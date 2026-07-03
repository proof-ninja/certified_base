From Stdlib Require Import Bool.

Definition pipe {A B : Type} (x : A) (f : A -> B) : B := f x.
Definition const {A B : Type} (x : A) (_ : B) : A := x.
Definition ignore {A : Type} (_ : A) : unit := tt.
Definition non {A: Type} (f : A -> bool) : A -> bool := fun x => negb (f x).

Fixpoint apply_n_times {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | O => x
  | S n' => apply_n_times n' f (f x)
  end.
Definition id {A : Type} (x : A) : A := x.
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).
Definition flip {A B C : Type} (f : A -> B -> C) : B -> A -> C :=
  fun y x => f x y.


Lemma id_left : forall {A B} (f : A -> B), compose id f = f.
Proof. intros A B f; reflexivity. Qed.

Lemma id_right : forall {A B} (f : A -> B), compose f id = f.
Proof. intros A B f; reflexivity. Qed.

Lemma compose_assoc :
  forall {A B C D} (h : C -> D) (g : B -> C) (f : A -> B),
    compose (compose h g) f = compose h (compose g f).
Proof. intros; reflexivity. Qed.

Lemma flip_flip : forall {A B C} (f : A -> B -> C), flip (flip f) = f.
Proof. intros A B C f; reflexivity. Qed.

Lemma non_involutive : forall (f : bool -> bool) x, non (non f) x = f x.
Proof. intros f x; unfold non; rewrite Bool.negb_involutive; reflexivity. Qed.

Lemma apply_n_times_add :
  forall {A} n m (f : A -> A) x,
    apply_n_times (n + m) f x = apply_n_times m f (apply_n_times n f x).
Proof.
  intros A n; induction n as [| n IH]; intros m f x; simpl.
  - reflexivity.
  - apply IH.
Qed.
