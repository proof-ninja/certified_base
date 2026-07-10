(lang dune 3.23)
(using rocq 0.13)
(name certified_base)
(generate_opam_files true)

(package
 (name certified_base)
 (synopsis "Rocq-proved, OCaml-extracted reimplementation of Jane Street's Base library")
 (license MIT)
 (depends
  ocaml
  ; rocq-runtime caps dune at < 3.24; declare it ourselves so opam picks a
  ; compatible dune from the start instead of installing the newest dune
  ; first and then having to downgrade once rocq-runtime's constraint is
  ; taken into account.
  (dune (< "3.24"))
  (rocq-prover (>= "9.0.0"))
  (base :with-test)))
