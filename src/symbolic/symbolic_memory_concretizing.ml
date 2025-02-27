module Backend = struct
  type address = Int32.t

  type t =
    { data : (address, Symbolic_value.int32) Hashtbl.t
    ; parent : t option
    ; chunks : (address, Symbolic_value.int32) Hashtbl.t
    }

  let make () =
    { data = Hashtbl.create 16; parent = None; chunks = Hashtbl.create 16 }

  let clone m =
    (* TODO: Make chunk copying lazy *)
    { data = Hashtbl.create 16
    ; parent = Some m
    ; chunks = Hashtbl.copy m.chunks
    }

  let address a =
    let open Symbolic_choice_without_memory in
    match Smtml.Expr.view a with
    | Val (Num (I32 i)) -> return i
    | Ptr { base; offset } ->
      select_i32 Symbolic_value.(I32.add (const_i32 base) offset)
    | _ -> select_i32 a

  let address_i32 a = a

  let rec load_byte { parent; data; _ } a =
    match Hashtbl.find_opt data a with
    | Some v -> v
    | None -> (
      match parent with
      | None -> Smtml.Expr.value (Num (I8 0))
      | Some parent -> load_byte parent a )

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

  let storen m a v n =
    for i = 0 to n - 1 do
      let a' = Int32.add a (Int32.of_int i) in
      let v' = Smtml.Expr.extract2 v i in
      Hashtbl.replace m.data a' v'
    done

  let validate_address m a range =
    let open Symbolic_choice_without_memory in
    match Smtml.Expr.view a with
    | Val (Num (I32 _)) ->
      (* An i32 is not a pointer to a heap chunk, so its valid *)
      return (Ok a)
    | Ptr { base; offset = start_offset } -> (
      let open Symbolic_value in
      match Hashtbl.find_opt m.chunks base with
      | None -> return (Error Trap.Memory_leak_use_after_free)
      | Some chunk_size ->
        let+ is_out_of_bounds =
          let range = const_i32 (Int32.of_int (range - 1)) in
          (* end_offset: last byte we will read/write *)
          let end_offset = I32.add start_offset range in
          select
            (Bool.or_
               (I32.ge_u start_offset chunk_size)
               (I32.ge_u end_offset chunk_size) )
        in
        if is_out_of_bounds then Error Trap.Memory_heap_buffer_overflow
        else Ok a )
    | _ ->
      (* A symbolic expression is valid, but we print to check if Ptr's are passing through here  *)
      Log.debug2 "Saw a symbolic address: %a@." Smtml.Expr.pp a;
      return (Ok a)

  let ptr v =
    let open Symbolic_choice_without_memory in
    match Smtml.Expr.view v with
    | Ptr { base; _ } -> return base
    | _ ->
      Log.debug2 {|free: cannot fetch pointer base of "%a"|} Smtml.Expr.pp v;
      let* () = add_pc @@ Smtml.Expr.value False in
      assert false

  let free m p =
    let open Symbolic_choice_without_memory in
    let+ base = ptr p in
    if not @@ Hashtbl.mem m.chunks base then
      Fmt.failwith "Memory leak double free";
    Hashtbl.remove m.chunks base;
    Symbolic_value.const_i32 base

  let realloc m ~ptr ~size =
    let open Symbolic_choice_without_memory in
    let+ base = address ptr in
    Hashtbl.replace m.chunks base size;
    Smtml.Expr.ptr base (Symbolic_value.const_i32 0l)
end

include Symbolic_memory_make.Make (Backend)
