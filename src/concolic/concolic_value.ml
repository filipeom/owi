(* SPDX-License-Identifier: AGPL-3.0-or-later *)
(* Copyright © 2021-2024 OCamlPro *)
(* Written by the Owi programmers *)

module C = Concrete_value
module S = Symbolic_value

type bool = C.bool * S.bool

type int32 = C.int32 * S.int32

let pp_int32 fmt (c, s) =
  Fmt.pf fmt "{ c = %a ; s = %a }" C.pp_int32 c S.pp_int32 s

type int64 = C.int64 * S.int64

let pp_int64 fmt (c, s) =
  Fmt.pf fmt "{ c = %a ; s = %a }" C.pp_int64 c S.pp_int64 s

type float32 = C.float32 * S.float32

let pp_float32 fmt (c, s) =
  Fmt.pf fmt "{ c = %a ; s = %a }" C.pp_float32 c S.pp_float32 s

type float64 = C.float64 * S.float64

let pp_float64 fmt (c, s) =
  Fmt.pf fmt "{ c = %a ; s = %a }" C.pp_float64 c S.pp_float64 s

(* TODO: Probably beter not to have a different value for both,
     there are no good reason for that right now *)
type ref_value = C.ref_value * S.ref_value

let pp_ref_value fmt (c, s) =
  Fmt.pf fmt "{ c = %a ; s = %a }" C.pp_ref_value c S.pp_ref_value s

type t =
  | I32 of int32
  | I64 of int64
  | F32 of float32
  | F64 of float64
  | Ref of ref_value

(* Bof... *)
let pair_value (c : C.t) (s : S.t) =
  match (c, s) with
  | I32 c, I32 s -> I32 (c, s)
  | I64 c, I64 s -> I64 (c, s)
  | F32 c, F32 s -> F32 (c, s)
  | F64 c, F64 s -> F64 (c, s)
  | Ref c, Ref s -> Ref (c, s)
  | _, _ -> assert false

let concrete_value (cs : t) : C.t =
  match cs with
  | I32 (c, _s) -> I32 c
  | I64 (c, _s) -> I64 c
  | F32 (c, _s) -> F32 c
  | F64 (c, _s) -> F64 c
  | Ref (c, _s) -> Ref c

let symbolic_value (cs : t) : S.t =
  match cs with
  | I32 (_c, s) -> I32 s
  | I64 (_c, s) -> I64 s
  | F32 (_c, s) -> F32 s
  | F64 (_c, s) -> F64 s
  | Ref (_c, s) -> Ref s

let f_pair_1 fc fs (c, s) = (fc c, fs s) [@@inline always]

let f_pair_1' fc fs (c, s) =
  match fc c with
  | Error _ as e -> e
  | Ok c -> ( match fs s with Error _ as e -> e | Ok s -> Ok (c, s) )
[@@inline always]

let f_pair_2 fc fs (c1, s1) (c2, s2) = (fc c1 c2, fs s1 s2) [@@inline always]

let f_pair_1_cst fc fs v = (fc v, fs v) [@@inline always]

let f_pair_2_cst' fc fs (c, s) v2 = (fc c v2, fs s v2) [@@inline always]

let const_i32 v = f_pair_1_cst C.const_i32 S.const_i32 v

let const_i64 v = f_pair_1_cst C.const_i64 S.const_i64 v

let const_f32 v = f_pair_1_cst C.const_f32 S.const_f32 v

let const_f64 v = f_pair_1_cst C.const_f64 S.const_f64 v

let assert_ref_c = function C.Ref r -> r | _ -> assert false

let assert_ref_s = function S.Ref r -> r | _ -> assert false

let ref_pair rc rs = Ref (assert_ref_c rc, assert_ref_s rs)

let ref_null v = ref_pair (C.ref_null v) (S.ref_null v)

let ref_func v = ref_pair (C.ref_func v) (S.ref_func v)

let ref_externref v1 v2 =
  ref_pair (C.ref_externref v1 v2) (S.ref_externref v1 v2)

let ref_is_null v = f_pair_1 C.ref_is_null S.ref_is_null v

let mk_pp ppc pps ppf (c, s) =
  Fmt.pf ppf "@[<hov 2>{c: %a@, s: %a}@]" ppc c pps s

let pp fmt = function
  | I32 i -> pp_int32 fmt i
  | I64 i -> pp_int64 fmt i
  | F32 f -> pp_float32 fmt f
  | F64 f -> pp_float64 fmt f
  | Ref r -> pp_ref_value fmt r

module Ref = struct
  let _equal_func_intf (_ : Func_intf.t) (_ : Func_intf.t) : Bool.t =
    Fmt.failwith "TODO equal_func_intf"

  let get_func (c, s) : Func_intf.t Value_intf.get_ref =
    match (C.Ref.get_func c, S.Ref.get_func s) with
    | Null, Null -> Null
    | Type_mismatch, Type_mismatch -> Type_mismatch
    | Ref_value c, Ref_value _s -> Ref_value c
    | _ -> assert false

  let get_externref (c, s) ty_id : _ Value_intf.get_ref =
    match (C.Ref.get_externref c ty_id, S.Ref.get_externref s ty_id) with
    | Null, Null -> Null
    | Type_mismatch, Type_mismatch -> Type_mismatch
    | Ref_value c, Ref_value _s ->
      (* We could ask for equality from the externref but this would require to add
         an equality to Type.Id.t *)
      Ref_value c
    | _ -> assert false
end

module Bool = struct
  let const = f_pair_1_cst C.Bool.const S.Bool.const

  let not = f_pair_1 C.Bool.not S.Bool.not

  let or_ = f_pair_2 C.Bool.or_ S.Bool.or_

  let and_ = f_pair_2 C.Bool.and_ S.Bool.and_

  let int32 = f_pair_1 C.Bool.int32 S.Bool.int32

  let pp = mk_pp C.Bool.pp S.Bool.pp
end

module type CFop = sig
  type num

  type same_size_int

  include
    Value_intf.Fop
      with type num := num
       and type bool := C.bool
       and type int32 := C.int32
       and type int64 := C.int64
       and type same_size_int := same_size_int
end

module type SFop = sig
  type num

  type same_size_int

  include
    Value_intf.Fop
      with type num := num
       and type bool := S.bool
       and type int32 := S.int32
       and type int64 := S.int64
       and type same_size_int := same_size_int
end

module type T = sig
  type t
end

module MK_Fop
    (CT : T)
    (CIT : T)
    (ST : T)
    (SIT : T)
    (CFop : CFop with type num := CT.t and type same_size_int := CIT.t)
    (SFop : SFop with type num := ST.t and type same_size_int := SIT.t) :
  Value_intf.Fop
    with type num := CT.t * ST.t
     and type bool := bool
     and type int32 := int32
     and type int64 := int64
     and type same_size_int := CIT.t * SIT.t = struct
  let zero = (CFop.zero, SFop.zero)

  let abs = f_pair_1 CFop.abs SFop.abs

  let neg = f_pair_1 CFop.neg SFop.neg

  let sqrt = f_pair_1 CFop.sqrt SFop.sqrt

  let ceil = f_pair_1 CFop.ceil SFop.ceil

  let floor = f_pair_1 CFop.floor SFop.floor

  let trunc = f_pair_1 CFop.trunc SFop.trunc

  let nearest = f_pair_1 CFop.nearest SFop.nearest

  let add = f_pair_2 CFop.add SFop.add

  let sub = f_pair_2 CFop.sub SFop.sub

  let mul = f_pair_2 CFop.mul SFop.mul

  let div = f_pair_2 CFop.div SFop.div

  let min = f_pair_2 CFop.min SFop.min

  let max = f_pair_2 CFop.max SFop.max

  let copy_sign = f_pair_2 CFop.copy_sign SFop.copy_sign

  let eq = f_pair_2 CFop.eq SFop.eq

  let ne = f_pair_2 CFop.ne SFop.ne

  let lt = f_pair_2 CFop.lt SFop.lt

  let gt = f_pair_2 CFop.gt SFop.gt

  let le = f_pair_2 CFop.le SFop.le

  let ge = f_pair_2 CFop.ge SFop.ge

  let convert_i32_s = f_pair_1 CFop.convert_i32_s SFop.convert_i32_s

  let convert_i32_u = f_pair_1 CFop.convert_i32_u SFop.convert_i32_u

  let convert_i64_s = f_pair_1 CFop.convert_i64_s SFop.convert_i64_s

  let convert_i64_u = f_pair_1 CFop.convert_i64_u SFop.convert_i64_u

  let of_bits = f_pair_1 CFop.of_bits SFop.of_bits

  let to_bits = f_pair_1 CFop.to_bits SFop.to_bits
end

module type CIop = sig
  type num

  type const

  include
    Value_intf.Iop
      with type num := num
       and type const := const
       and type bool := C.bool
       and type float32 := C.float32
       and type float64 := C.float64
end

module type SIop = sig
  type num

  type const

  include
    Value_intf.Iop
      with type num := num
       and type const := const
       and type bool := S.bool
       and type float32 := S.float32
       and type float64 := S.float64
end

module MK_Iop
    (Const : T)
    (CT : T)
    (ST : T)
    (CIop : CIop with type num := CT.t and type const := Const.t)
    (SIop : SIop with type num := ST.t and type const := Const.t) :
  Value_intf.Iop
    with type num := CT.t * ST.t
     and type const := Const.t
     and type bool := bool
     and type float32 := float32
     and type float64 := float64 = struct
  let zero = (CIop.zero, SIop.zero)

  let clz = f_pair_1 CIop.clz SIop.clz

  let ctz = f_pair_1 CIop.ctz SIop.ctz

  let popcnt = f_pair_1 CIop.popcnt SIop.popcnt

  let add = f_pair_2 CIop.add SIop.add

  let sub = f_pair_2 CIop.sub SIop.sub

  let mul = f_pair_2 CIop.mul SIop.mul

  let div = f_pair_2 CIop.div SIop.div

  let unsigned_div = f_pair_2 CIop.unsigned_div SIop.unsigned_div

  let rem = f_pair_2 CIop.rem SIop.rem

  let unsigned_rem = f_pair_2 CIop.unsigned_rem SIop.unsigned_rem

  let logand = f_pair_2 CIop.logand SIop.logand

  let logor = f_pair_2 CIop.logor SIop.logor

  let logxor = f_pair_2 CIop.logxor SIop.logxor

  let shl = f_pair_2 CIop.shl SIop.shl

  let shr_s = f_pair_2 CIop.shr_s SIop.shr_s

  let shr_u = f_pair_2 CIop.shr_u SIop.shr_u

  let rotl = f_pair_2 CIop.rotl SIop.rotl

  let rotr = f_pair_2 CIop.rotr SIop.rotr

  let eq_const = f_pair_2_cst' CIop.eq_const SIop.eq_const

  let eq = f_pair_2 CIop.eq SIop.eq

  let ne = f_pair_2 CIop.ne SIop.ne

  let lt = f_pair_2 CIop.lt SIop.lt

  let gt = f_pair_2 CIop.gt SIop.gt

  let lt_u = f_pair_2 CIop.lt_u SIop.lt_u

  let gt_u = f_pair_2 CIop.gt_u SIop.gt_u

  let le = f_pair_2 CIop.le SIop.le

  let ge = f_pair_2 CIop.ge SIop.ge

  let le_u = f_pair_2 CIop.le_u SIop.le_u

  let ge_u = f_pair_2 CIop.ge_u SIop.ge_u

  let trunc_f32_s = f_pair_1' CIop.trunc_f32_s SIop.trunc_f32_s

  let trunc_f32_u = f_pair_1' CIop.trunc_f32_u SIop.trunc_f32_u

  let trunc_f64_s = f_pair_1' CIop.trunc_f64_s SIop.trunc_f64_s

  let trunc_f64_u = f_pair_1' CIop.trunc_f64_u SIop.trunc_f64_u

  let trunc_sat_f32_s = f_pair_1 CIop.trunc_sat_f32_s SIop.trunc_sat_f32_s

  let trunc_sat_f32_u = f_pair_1 CIop.trunc_sat_f32_u SIop.trunc_sat_f32_u

  let trunc_sat_f64_s = f_pair_1 CIop.trunc_sat_f64_s SIop.trunc_sat_f64_s

  let trunc_sat_f64_u = f_pair_1 CIop.trunc_sat_f64_u SIop.trunc_sat_f64_u

  let extend_s symbolic (c, s) =
    (CIop.extend_s symbolic c, SIop.extend_s symbolic s)
end

module F32 = struct
  include
    MK_Fop
      (struct
        type t = C.float32
      end)
      (struct
        type t = C.int32
      end)
      (struct
        type t = S.float32
      end)
      (struct
        type t = S.int32
      end)
      (C.F32)
      (S.F32)

  let demote_f64 = f_pair_1 C.F32.demote_f64 S.F32.demote_f64

  let reinterpret_i32 = f_pair_1 C.F32.reinterpret_i32 S.F32.reinterpret_i32
end

module F64 = struct
  include
    MK_Fop
      (struct
        type t = C.float64
      end)
      (struct
        type t = C.int64
      end)
      (struct
        type t = S.float64
      end)
      (struct
        type t = S.int64
      end)
      (C.F64)
      (S.F64)

  let promote_f32 = f_pair_1 C.F64.promote_f32 S.F64.promote_f32

  let reinterpret_i64 = f_pair_1 C.F64.reinterpret_i64 S.F64.reinterpret_i64
end

module I32 = struct
  include
    MK_Iop
      (struct
        type t = Int32.t
      end)
      (struct
        type t = C.int32
      end)
      (struct
        type t = S.int32
      end)
      (C.I32)
      (S.I32)

  let to_bool = f_pair_1 C.I32.to_bool S.I32.to_bool

  let reinterpret_f32 = f_pair_1 C.I32.reinterpret_f32 S.I32.reinterpret_f32

  let wrap_i64 = f_pair_1 C.I32.wrap_i64 S.I32.wrap_i64
end

module I64 = struct
  include
    MK_Iop
      (struct
        type t = Int64.t
      end)
      (struct
        type t = C.int64
      end)
      (struct
        type t = S.int64
      end)
      (C.I64)
      (S.I64)

  let of_int32 = f_pair_1 C.I64.of_int32 S.I64.of_int32

  let to_int32 = f_pair_1 C.I64.to_int32 S.I64.to_int32

  let reinterpret_f64 = f_pair_1 C.I64.reinterpret_f64 S.I64.reinterpret_f64

  let extend_i32_s = f_pair_1 C.I64.extend_i32_s S.I64.extend_i32_s

  let extend_i32_u = f_pair_1 C.I64.extend_i32_u S.I64.extend_i32_u
end
