# Symbolic interpreter

## Basic example

The symbolic interpreter allows to define *symbolic variables* whose values is considered to be any possible value. Then, we collect informations during the execution and when an error is reached, we try to see if there's a possible value for all the symbolic variables by taking all our informations into account.

In the following file, we define `x` as a symbolic variable. Then if `5 < x`, we fail.

<!-- $MDX file=mini.wat -->
```wat
(module
  (import "symbolic" "i32" (func $gen_i32 (param i32) (result i32)))

  (func $start (local $x i32)
    (local.set $x (call $gen_i32 (i32.const 42)))
    (if (i32.lt_s (i32.const 5) (local.get $x)) (then
      unreachable
    )))

  (start $start)
)
```

Let's see if owi is able to find a value for `x` that lead to an error:

```sh
$ dune exec owi -- sym ./mini.wat
Trap: unreachable
Model:
  (model
    (x_0 i32 (i32 6)))
Reached problem!
```

Indeed, if `x` is equal to `6` then, the `unreachable` instruction will be reached.

## Complicated example

TODO

## Man page

```sh
$ dune exec owi -- sym --help=plain
OWI-SYM(1)                        Owi Manual                        OWI-SYM(1)

NAME
       owi-sym - Run the symbolic interpreter

SYNOPSIS
       owi sym [OPTION]… [ARG]…

OPTIONS
       -d, --debug
           debug mode

       --no-stop-at-failure
           do not stop when a program failure is encountered

       --optimize
           optimize mode

       -p, --profiling
           profiling mode

       -u, --unsafe
           skip typechecking pass

       -w VAL, --workers=VAL (absent=4)
           number of workers for symbolic execution

       --workspace=VAL (absent=owi-out)
           path to the workspace directory

COMMON OPTIONS
       --help[=FMT] (default=auto)
           Show  this  help  in format FMT. The value FMT must be one of auto,
           pager, groff or plain. With auto, the  format  is  pager  or  plain
           whenever the TERM env var is dumb or undefined.

       --version
           Show version information.

EXIT STATUS
       owi sym exits with:

       0   on success.

       123 on indiscriminate errors reported on standard error.

       124 on command line parsing errors.

       125 on unexpected internal errors (bugs).

BUGS
       Email them to <contact@ndrs.fr>.

SEE ALSO
       owi(1)

Owi 11VERSION11                                                     OWI-SYM(1)
```