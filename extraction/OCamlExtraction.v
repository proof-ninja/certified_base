From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.
From Stdlib Require Import ExtrOCamlFloats.

From Base Require Import Fn Unit Result.

Extraction Language OCaml.

(** [Result.t] already has the exact shape of OCaml's built-in [result]. *)
Extract Inductive Result.t => "result" ["Ok" "Error"].

(** Inline so extracted files never reference an un-extracted [Datatypes]
    module. *)
Extraction Inline negb.
Extract Inductive comparison => "int" ["0" "-1" "1"].


Extraction Library Fn.
Extraction Library Unit.
Extraction Library Result.
