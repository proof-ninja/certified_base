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
  (rocq-prover (>= "9.0.0"))
  (base :with-test)))
