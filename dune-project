(lang dune 3.11)
(using coq 0.3)
(warnings (deprecated_coq_lang_lt_08 disabled))
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
