From Stdlib Require Import List.
Import List.ListNotations.

Inductive t : Type :=
| Neg
| Zero
| Pos.

Definition all := [Neg; Zero; Pos].

Definition equal (x y : t) : bool :=
  match x, y with
  | Neg, Neg | Zero, Zero | Pos, Pos => true
  | _, _ => false
  end.

Definition flip (s : t) : t :=
  match s with
  | Neg => Pos
  | Zero => Zero
  | Pos => Neg
  end.

Definition mult (x y : t) : t :=
  match x, y with
  | Zero, _ | _, Zero => Zero
  | Neg, Neg | Pos, Pos => Pos
  | Neg, Pos | Pos, Neg => Neg
  end.
Infix "x * y" := (mult x y) (at level 40).

Lemma flip_flip : forall s, flip (flip s) = s.
Proof. intros []; reflexivity. Qed.

Lemma mult_comm : forall x y, mult x y = mult y x.
Proof. intros [] []; reflexivity. Qed.

Lemma mult_assoc : forall x y z, mult (mult x y) z = mult x (mult y z).
Proof. intros [] [] []; reflexivity. Qed.

Lemma equal_reflects : forall x y, equal x y = true <-> x = y.
Proof. intros [] []; simpl; split; try reflexivity; try discriminate; congruence. Qed.
