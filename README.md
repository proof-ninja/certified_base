# certified_base

[![CI](https://github.com/proof-ninja/certified_base/actions/workflows/ci.yml/badge.svg)](https://github.com/proof-ninja/certified_base/actions/workflows/ci.yml)

A project aiming to define and prove, in [Rocq](https://rocq-prover.org/) (formerly Coq),
functionality equivalent to Jane Street's OCaml library [`base`](https://github.com/janestreet/base),
and [extract](https://rocq-prover.org/doc/master/refman/addendum/extraction.html) it into a real,
usable OCaml library.

* Jane Street base: https://github.com/janestreet/base
* base API doc: https://ocaml.janestreet.com/ocaml-core/v0.12/doc/base/index.html

## Module status

| Module | theories/ | Extracted | Status |
|---|---|---|---|
| `Fn`     | ✅ | ✅ | Fully proved |
| `Unit`   | ✅ | ✅ | Fully proved |
| `Result` | ✅ | ✅ | Fully proved (including Functor/Monad laws) |
| `Sign`   | ✅ | ✅ | Fully proved |
| `Option` | ✅ | ✅ | Fully proved (including Functor/Monad laws) |
| `List`   | ✅ | ✅ | Fully proved (including Functor/Monad laws) |
| `Nativeint` | ✅ (partial) | ❌ | Stub with `t`/`zero`/`compare` left as `Parameter`s (unimplemented axioms). Not extracted yet |

No `Admitted` is used anywhere. Anything not (yet) proved is stated explicitly as a `Parameter` (axiom).

## Usage

The extracted OCaml library is provided as a wrapped module `Certified_base`.
Add `certified_base` to your `dune` project's `libraries`, and instead of `open Base`,
write `open Certified_base` — you can then use submodules unqualified, e.g. `Sign.mult`.

```dune
(executable
 (name main)
 (libraries certified_base))
```

```ocaml
open Certified_base

let () = print_endline (if Sign.equal (Sign.flip Sign.Neg) Sign.Pos then "ok" else "ng")
```
