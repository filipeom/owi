(module
  (import "owi" "f64_symbol" (func $f64_symbol (result f64)))

  (func $start
    (local $f64 f64)
    (local.set $f64 (call $f64_symbol))

    (i32.ge_s (i32.const 1) (i32.trunc_f64_s (local.get $f64)))
    (if (then unreachable))
  )

  (start $start)
)
