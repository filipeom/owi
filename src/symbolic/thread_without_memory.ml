(* SPDX-License-Identifier: AGPL-3.0-or-later *)
(* Copyright © 2021-2024 OCamlPro *)
(* Written by the Owi programmers *)

include Thread.Make (struct
  type collection = bool

  let init () = false

  let clone _ = true
end)
