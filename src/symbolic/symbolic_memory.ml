(* SPDX-License-Identifier: AGPL-3.0-or-later *)
(* Copyright © 2021-2024 OCamlPro *)
(* Written by the Owi programmers *)

module Value = Symbolic_value
module Expr = Smtml.Expr
open Expr

let page_size = Symbolic_value.const_i32 65_536l

type t =
  { data : (Int32.t, Value.int32) Hashtbl.t
  ; parent : t option
  ; mutable size : Value.int32
  ; chunks : (Int32.t, Value.int32) Hashtbl.t
  }

let create size =
  { data = Hashtbl.create 128
  ; parent = None
  ; size = Value.const_i32 size
  ; chunks = Hashtbl.create 16
  }

let i32 v = match view v with Val (Num (I32 i)) -> i | _ -> assert false

let grow m delta =
  let old_size = Value.I32.mul m.size page_size in
  let new_size = Value.I32.(div (add old_size delta) page_size) in
  m.size <-
    Value.Bool.select_expr
      (Value.I32.gt new_size m.size)
      ~if_true:new_size ~if_false:m.size

let size { size; _ } = Value.I32.mul size page_size

let size_in_pages { size; _ } = size

let fill _ = assert false

let blit _ = assert false

let blit_string m str ~src ~dst ~len =
  (* This function is only used in memory init so everything will be concrete *)
  let str_len = String.length str in
  let mem_len = Int32.(to_int (i32 m.size) * to_int (i32 page_size)) in
  let src = Int32.to_int @@ i32 src in
  let dst = Int32.to_int @@ i32 dst in
  let len = Int32.to_int @@ i32 len in
  if src < 0 || dst < 0 || len < 0 || src + len > str_len || dst + len > mem_len
  then Value.Bool.const true
  else begin
    for i = 0 to len - 1 do
      let byte = Char.code @@ String.get str (src + i) in
      let dst = Int32.of_int (dst + i) in
      Hashtbl.replace m.data dst (make (Val (Num (I8 byte))))
    done;
    Value.Bool.const false
  end

let clone m =
  { data = Hashtbl.create 16
  ; parent = Some m
  ; size = m.size
  ; chunks = Hashtbl.copy m.chunks (* TODO: we can make this lazy as well *)
  }

let rec load_byte { parent; data; _ } a =
  match Hashtbl.find_opt data a with
  | None -> begin
    match parent with
    | None -> make (Val (Num (I8 0)))
    | Some parent -> load_byte parent a
  end
  | Some v -> v

let loadn m a n =
  let rec loop addr size i acc =
    if i = size then acc
    else
      let addr' = Int32.(add addr (of_int i)) in
      let byte = load_byte m addr' in
      loop addr size (i + 1) (Smtml.Expr.concat3 i ~msb:byte ~lsb:acc)
  in
  let v0 = load_byte m a in
  loop a n 1 v0

let load_8_s m a =
  let v = loadn m (i32 a) 1 in
  match view v with
  | Val (Num (I8 i8)) -> Value.const_i32 (Int32.extend_s 8 (Int32.of_int i8))
  | _ -> cvtop (Ty_bitv 32) (Sign_extend 24) v

let load_8_u m a =
  let v = loadn m (i32 a) 1 in
  match view v with
  | Val (Num (I8 i)) -> Value.const_i32 (Int32.of_int i)
  | _ -> cvtop (Ty_bitv 32) (Zero_extend 24) v

let load_16_s m a =
  let v = loadn m (i32 a) 2 in
  match view v with
  | Val (Num (I32 i16)) -> Value.const_i32 (Int32.extend_s 16 i16)
  | _ -> cvtop (Ty_bitv 32) (Sign_extend 16) v

let load_16_u m a =
  let v = loadn m (i32 a) 2 in
  match view v with
  | Val (Num (I32 _)) -> v
  | _ -> cvtop (Ty_bitv 32) (Zero_extend 16) v

let load_32 m a = loadn m (i32 a) 4

let load_64 m a = loadn m (i32 a) 8

let storen m ~addr v n =
  let a0 = i32 addr in
  for i = 0 to n - 1 do
    let addr' = Int32.add a0 (Int32.of_int i) in
    let v' = Smtml.Expr.extract2 v i in
    Hashtbl.replace m.data addr' v'
  done

let store_8 m ~addr v = storen m ~addr v 1

let store_16 m ~addr v = storen m ~addr v 2

let store_32 m ~addr v = storen m ~addr v 4

let store_64 m ~addr v = storen m ~addr v 8

let get_limit_max _m = None (* TODO *)

let check_within_bounds m a =
  match view a with
  | Val (Num (I32 _)) -> Ok (Value.Bool.const false, a)
  | Ptr { base; offset } -> (
    match Hashtbl.find_opt m.chunks base with
    | None -> Error Trap.Memory_leak_use_after_free
    | Some size ->
      let ptr = Int32.add base (i32 offset) in
      let upper_bound =
        Value.(I32.ge (const_i32 ptr) (I32.add (const_i32 base) size))
      in
      Ok
        ( Value.Bool.(or_ (const (Int32.lt ptr base)) upper_bound)
        , Value.const_i32 ptr ) )
  | _ -> assert false

let free m base =
  if not @@ Hashtbl.mem m.chunks base then
    Fmt.failwith "Memory leak double free";
  Hashtbl.remove m.chunks base

let realloc m base size = Hashtbl.replace m.chunks base size

module ITbl = Hashtbl.Make (struct
  include Int

  let hash x = x
end)

type collection = t ITbl.t Env_id.Tbl.t

let init () = Env_id.Tbl.create 0

let iter f collection = Env_id.Tbl.iter (fun _ tbl -> f tbl) collection

let clone collection =
  (* TODO: this is ugly and should be rewritten *)
  let s = Env_id.Tbl.to_seq collection in
  Env_id.Tbl.of_seq
  @@ Seq.map
       (fun (i, t) ->
         let s = ITbl.to_seq t in
         (i, ITbl.of_seq @@ Seq.map (fun (i, a) -> (i, clone a)) s) )
       s

let convert (orig_mem : Concrete_memory.t) : t =
  let s = Concrete_memory.size_in_pages orig_mem in
  create s

let get_env env_id memories =
  match Env_id.Tbl.find_opt memories env_id with
  | Some env -> env
  | None ->
    let t = ITbl.create 0 in
    Env_id.Tbl.add memories env_id t;
    t

let get_memory env_id (orig_memory : Concrete_memory.t) collection g_id =
  let env = get_env env_id collection in
  match ITbl.find_opt env g_id with
  | Some t -> t
  | None ->
    let t = convert orig_memory in
    ITbl.add env g_id t;
    t
