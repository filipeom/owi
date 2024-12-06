type t =
  | Nothing of Rusage.t
  | Signaled of Rusage.t * int
  | Stopped of Rusage.t * int
  | Reached of Rusage.t
  | Timeout of Rusage.t
  | Other of Rusage.t * int

let is_nothing = function Nothing _ -> true | _ -> false

let is_killed = function Signaled _ | Stopped _ -> true | _ -> false

let is_reached = function Reached _ -> true | _ -> false

let is_timeout = function Timeout _ -> true | _ -> false

let is_other = function Other _ -> true | _ -> false

let pp_ruse fmt { Rusage.clock; utime; stime; maxrss } =
  Fmt.pf fmt "%g %g %g using %Ld" clock utime stime maxrss

let pp fmt = function
  | Timeout t -> Fmt.pf fmt "Timeout in %a" pp_ruse t
  | Nothing t -> Fmt.pf fmt "Nothing in %a" pp_ruse t
  | Reached t -> Fmt.pf fmt "Reached in %a" pp_ruse t
  | Other (t, code) -> Fmt.pf fmt "Other %i in %a" code pp_ruse t
  | Signaled (t, code) -> Fmt.pf fmt "Signaled %i in %a" code pp_ruse t
  | Stopped (t, code) -> Fmt.pf fmt "Stopped %i in %a" code pp_ruse t
