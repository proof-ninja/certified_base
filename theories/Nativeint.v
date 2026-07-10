From Base Require Import Sign.

Parameter t : Set.
Parameter zero : t.
Parameter compare : t -> t -> comparison.

Definition sign (i : t) : Sign.t :=
  match compare i zero with
  | Eq => Sign.Zero
  | Lt => Sign.Neg
  | Gt => Sign.Pos
  end.
