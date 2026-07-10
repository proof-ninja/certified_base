Require Import List.
Import ListNotations.

Definition t : Type := unit.

Definition equal (_ _ : t) : bool := true.
Definition compare (_ _ : t) : comparison := Eq.

Definition all := [tt].

Lemma all_equal : forall x y : t, x = y.
Proof. intros [] []; reflexivity. Qed.

Lemma equal_reflects : forall x y : t, equal x y = true <-> x = y.
Proof. intros x y; split; intros _; [apply all_equal | reflexivity]. Qed.

Lemma compare_eq_iff : forall x y : t, compare x y = Eq <-> x = y.
Proof. intros x y; split; intros _; [apply all_equal | reflexivity]. Qed.
