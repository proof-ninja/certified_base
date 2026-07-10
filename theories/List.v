From Stdlib Require Import List Bool Lia.
Import List.ListNotations.

(** This file's own compiled module name is [Base.List], which collides
    with the stdlib [List] module we import for the [In] predicate and the
    [[...]] notation. Everything computational below is written from
    scratch (never delegated to [List.foo]) rather than aliased from the
    stdlib, both to avoid self-qualification ambiguity (see [Base.String]'s
    note in the project history) and because aliasing stdlib [List]
    functions makes extraction pull in internal stdlib helper lemmas that
    don't extract cleanly. *)

Definition t (A : Type) := list A.

Definition is_empty {A : Type} (l : t A) : bool :=
  match l with [] => true | _ => false end.

Fixpoint length {A : Type} (l : t A) : nat :=
  match l with [] => O | _ :: l' => S (length l') end.

Fixpoint append {A : Type} (l1 l2 : t A) : t A :=
  match l1 with
  | [] => l2
  | x :: l1' => x :: append l1' l2
  end.

Fixpoint rev {A : Type} (l : t A) : t A :=
  match l with
  | [] => []
  | x :: l' => append (rev l') [x]
  end.

Fixpoint concat {A : Type} (ls : t (t A)) : t A :=
  match ls with
  | [] => []
  | l :: ls' => append l (concat ls')
  end.

Fixpoint map {A B : Type} (f : A -> B) (l : t A) : t B :=
  match l with
  | [] => []
  | x :: l' => f x :: map f l'
  end.

Fixpoint filter {A : Type} (f : A -> bool) (l : t A) : t A :=
  match l with
  | [] => []
  | x :: l' => if f x then x :: filter f l' else filter f l'
  end.

Fixpoint exists_ {A : Type} (f : A -> bool) (l : t A) : bool :=
  match l with
  | [] => false
  | x :: l' => f x || exists_ f l'
  end.

Fixpoint for_all {A : Type} (f : A -> bool) (l : t A) : bool :=
  match l with
  | [] => true
  | x :: l' => f x && for_all f l'
  end.

Fixpoint fold {A Acc : Type} (l : t A) (init : Acc) (f : Acc -> A -> Acc) : Acc :=
  match l with
  | [] => init
  | x :: l' => fold l' (f init x) f
  end.

Fixpoint mem {A : Type} (eq : A -> A -> bool) (x : A) (l : t A) : bool :=
  match l with
  | [] => false
  | y :: l' => eq x y || mem eq x l'
  end.

Fixpoint find {A : Type} (f : A -> bool) (l : t A) : option A :=
  match l with
  | [] => None
  | x :: l' => if f x then Some x else find f l'
  end.

Definition hd {A : Type} (l : t A) : option A :=
  match l with [] => None | x :: _ => Some x end.

Definition tl {A : Type} (l : t A) : option (t A) :=
  match l with [] => None | _ :: l' => Some l' end.

Fixpoint nth {A : Type} (l : t A) (n : nat) : option A :=
  match l, n with
  | [], _ => None
  | x :: _, O => Some x
  | _ :: l', S n' => nth l' n'
  end.

Fixpoint init {A : Type} (n : nat) (f : nat -> A) : t A :=
  match n with
  | O => []
  | S n' => append (init n' f) [f n']
  end.

Definition return_ {A : Type} (x : A) : t A := [x].

Definition bind {A B : Type} (l : t A) (f : A -> t B) : t B := concat (map f l).

Definition count {A : Type} (f : A -> bool) (l : t A) : nat := length (filter f l).

Fixpoint rev_append {A : Type} (l1 l2 : t A) : t A :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition equal {A : Type} (eq : A -> A -> bool) (l1 l2 : t A) : bool :=
  (fix go l1 l2 :=
     match l1, l2 with
     | [], [] => true
     | x :: l1', y :: l2' => eq x y && go l1' l2'
     | _, _ => false
     end) l1 l2.

(** Lexicographic order, matching Base's [List.compare]. *)
Fixpoint compare {A : Type} (cmp : A -> A -> comparison) (l1 l2 : t A) : comparison :=
  match l1, l2 with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: l1', y :: l2' =>
      match cmp x y with
      | Eq => compare cmp l1' l2'
      | c => c
      end
  end.

Definition iter {A : Type} (f : A -> unit) (l : t A) : unit := fold l tt (fun _ x => f x).

Local Fixpoint mapi_aux {A B : Type} (f : nat -> A -> B) (n : nat) (l : t A) : t B :=
  match l with
  | [] => []
  | x :: l' => f n x :: mapi_aux f (S n) l'
  end.
Definition mapi {A B : Type} (f : nat -> A -> B) (l : t A) : t B := mapi_aux f O l.

(** [f n x]'s result is threaded through as the accumulator (mirroring
    [fold]/[iter]'s recursion) rather than discarded via [let _ := ... in],
    since extraction treats a discarded binding as dead code and drops the
    call entirely -- even though [f]'s [unit] result stands in for a
    side effect once extracted to OCaml. *)
Local Fixpoint iteri_aux {A : Type} (f : nat -> A -> unit) (n : nat) (l : t A) (acc : unit) : unit :=
  match l with
  | [] => acc
  | x :: l' => iteri_aux f (S n) l' (f n x)
  end.
Definition iteri {A : Type} (f : nat -> A -> unit) (l : t A) : unit := iteri_aux f O l tt.

Local Fixpoint existsi_aux {A : Type} (f : nat -> A -> bool) (n : nat) (l : t A) : bool :=
  match l with
  | [] => false
  | x :: l' => f n x || existsi_aux f (S n) l'
  end.
Definition existsi {A : Type} (f : nat -> A -> bool) (l : t A) : bool := existsi_aux f O l.

Local Fixpoint for_alli_aux {A : Type} (f : nat -> A -> bool) (n : nat) (l : t A) : bool :=
  match l with
  | [] => true
  | x :: l' => f n x && for_alli_aux f (S n) l'
  end.
Definition for_alli {A : Type} (f : nat -> A -> bool) (l : t A) : bool := for_alli_aux f O l.

Local Fixpoint findi_aux {A : Type} (f : nat -> A -> bool) (n : nat) (l : t A) : option (nat * A) :=
  match l with
  | [] => None
  | x :: l' => if f n x then Some (n, x) else findi_aux f (S n) l'
  end.
Definition findi {A : Type} (f : nat -> A -> bool) (l : t A) : option (nat * A) := findi_aux f O l.

Fixpoint take {A : Type} (l : t A) (n : nat) : t A :=
  match l, n with
  | [], _ => []
  | _, O => []
  | x :: l', S n' => x :: take l' n'
  end.

Fixpoint drop {A : Type} (l : t A) (n : nat) : t A :=
  match l, n with
  | [], _ => []
  | _, O => l
  | _ :: l', S n' => drop l' n'
  end.

Fixpoint take_while {A : Type} (f : A -> bool) (l : t A) : t A :=
  match l with
  | [] => []
  | x :: l' => if f x then x :: take_while f l' else []
  end.

Fixpoint drop_while {A : Type} (f : A -> bool) (l : t A) : t A :=
  match l with
  | [] => []
  | x :: l' => if f x then drop_while f l' else l
  end.

Fixpoint last {A : Type} (l : t A) : option A :=
  match l with
  | [] => None
  | [x] => Some x
  | _ :: l' => last l'
  end.

Definition cons {A : Type} (x : A) (l : t A) : t A := x :: l.

Definition sub {A : Type} (l : t A) (pos len : nat) : t A := take (drop l pos) len.

Fixpoint unzip {A B : Type} (l : t (A * B)) : t A * t B :=
  match l with
  | [] => ([], [])
  | (x, y) :: l' => let (xs, ys) := unzip l' in (x :: xs, y :: ys)
  end.

Fixpoint zip {A B : Type} (l1 : t A) (l2 : t B) : option (t (A * B)) :=
  match l1, l2 with
  | [], [] => Some []
  | x :: l1', y :: l2' =>
      match zip l1' l2' with
      | Some l => Some ((x, y) :: l)
      | None => None
      end
  | _, _ => None
  end.

Definition partition_tf {A : Type} (f : A -> bool) (l : t A) : t A * t A :=
  (filter f l, filter (fun x => negb (f x)) l).

(** ** append *)

Lemma append_nil_r : forall {A} (l : t A), append l [] = l.
Proof. intros A l; induction l as [| x l' IH]; simpl; [| rewrite IH]; reflexivity. Qed.

Lemma append_assoc :
  forall {A} (l1 l2 l3 : t A), append (append l1 l2) l3 = append l1 (append l2 l3).
Proof.
  intros A l1; induction l1 as [| x l1' IH]; intros l2 l3; simpl; [| rewrite IH]; reflexivity.
Qed.

Lemma length_append : forall {A} (l1 l2 : t A), length (append l1 l2) = length l1 + length l2.
Proof.
  intros A l1; induction l1 as [| x l1' IH]; intros l2; simpl; [| rewrite IH]; reflexivity.
Qed.

(** ** rev *)

Lemma rev_append_distr :
  forall {A} (l1 l2 : t A), rev (append l1 l2) = append (rev l2) (rev l1).
Proof.
  intros A l1; induction l1 as [| x l1' IH]; intros l2; simpl.
  - rewrite append_nil_r; reflexivity.
  - rewrite IH, append_assoc; reflexivity.
Qed.

Lemma rev_involutive : forall {A} (l : t A), rev (rev l) = l.
Proof.
  intros A l; induction l as [| x l' IH]; simpl.
  - reflexivity.
  - rewrite rev_append_distr, IH; reflexivity.
Qed.

(** ** Functor laws *)

Lemma map_id : forall {A} (l : t A), map (fun x => x) l = l.
Proof. intros A l; induction l as [| x l' IH]; simpl; [| rewrite IH]; reflexivity. Qed.

Lemma map_map :
  forall {A B C} (f : A -> B) (g : B -> C) (l : t A),
    map g (map f l) = map (fun x => g (f x)) l.
Proof. intros A B C f g l; induction l as [| x l' IH]; simpl; [| rewrite IH]; reflexivity. Qed.

(** ** mem *)

Lemma mem_reflects :
  forall {A} (eq : A -> A -> bool),
    (forall x y, eq x y = true <-> x = y) ->
    forall x l, mem eq x l = true <-> In x l.
Proof.
  intros A eq Heq x l; induction l as [| y l' IH]; simpl.
  - split; [discriminate | intros []].
  - rewrite Bool.orb_true_iff, IH.
    split.
    + intros [H | H]; [left; apply Heq in H; congruence | right; assumption].
    + intros [H | H]; [left; apply Heq; congruence | right; assumption].
Qed.

(** ** find *)

Lemma find_some : forall {A} (f : A -> bool) (l : t A) (x : A), find f l = Some x -> f x = true.
Proof.
  intros A f l; induction l as [| y l' IH]; simpl; intros x H.
  - discriminate.
  - destruct (f y) eqn:Hfy.
    + injection H as ->; exact Hfy.
    + apply IH; exact H.
Qed.

(** ** init *)

Lemma init_length : forall {A} (n : nat) (f : nat -> A), length (init n f) = n.
Proof.
  intros A n; induction n as [| n' IH]; intros f; simpl.
  - reflexivity.
  - rewrite length_append, IH; simpl; lia.
Qed.

(** ** Monad laws *)

Lemma left_identity : forall {A B} (x : A) (f : A -> t B), bind (return_ x) f = f x.
Proof. intros A B x f; unfold bind, return_, concat, map; simpl; apply append_nil_r. Qed.

Lemma bind_append :
  forall {A B} (l1 l2 : t A) (f : A -> t B),
    bind (append l1 l2) f = append (bind l1 f) (bind l2 f).
Proof.
  intros A B l1 l2 f; unfold bind, concat, map.
  induction l1 as [| x l1' IH]; simpl.
  - reflexivity.
  - rewrite IH, append_assoc; reflexivity.
Qed.

Lemma right_identity : forall {A} (l : t A), bind l return_ = l.
Proof.
  intros A l; induction l as [| x l' IH]; simpl.
  - reflexivity.
  - unfold bind, concat, map in *; simpl; unfold return_; simpl.
    f_equal; exact IH.
Qed.

Lemma bind_cons :
  forall {A B} (x : A) (l : t A) (f : A -> t B), bind (x :: l) f = append (f x) (bind l f).
Proof. intros; unfold bind, concat, map; reflexivity. Qed.

Lemma assoc :
  forall {A B C} (l : t A) (f : A -> t B) (g : B -> t C),
    bind (bind l f) g = bind l (fun x => bind (f x) g).
Proof.
  intros A B C l f g; induction l as [| x l' IH].
  - reflexivity.
  - rewrite bind_cons, bind_append, IH, bind_cons; reflexivity.
Qed.

(** ** rev_append *)

Lemma rev_append_is_append_rev :
  forall {A} (l1 l2 : t A), rev_append l1 l2 = append (rev l1) l2.
Proof.
  intros A l1; induction l1 as [| x l1' IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH, append_assoc; reflexivity.
Qed.

(** ** equal *)

Lemma equal_reflects :
  forall {A} (eq : A -> A -> bool),
    (forall x y, eq x y = true <-> x = y) ->
    forall l1 l2, equal eq l1 l2 = true <-> l1 = l2.
Proof.
  intros A eq Heq l1; induction l1 as [| x l1' IH]; intros [| y l2']; simpl;
    split; intros H; try discriminate; try reflexivity.
  - apply Bool.andb_true_iff in H as [Hxy Hl].
    f_equal; [apply Heq; assumption | apply IH; assumption].
  - injection H as -> ->.
    apply Bool.andb_true_iff; split; [apply Heq; reflexivity | apply IH; reflexivity].
Qed.

(** ** compare *)

Lemma compare_nil_nil : forall {A} (cmp : A -> A -> comparison), compare cmp [] [] = Eq.
Proof. reflexivity. Qed.

Lemma compare_cons_cons :
  forall {A} (cmp : A -> A -> comparison) x l1 y l2,
    compare cmp (x :: l1) (y :: l2) =
      match cmp x y with Eq => compare cmp l1 l2 | c => c end.
Proof. reflexivity. Qed.

(** ** take / drop *)

Lemma take_drop_append : forall {A} (l : t A) (n : nat), append (take l n) (drop l n) = l.
Proof.
  intros A l; induction l as [| x l' IH]; intros [| n']; simpl; try reflexivity.
  f_equal; apply IH.
Qed.

(** ** take_while / drop_while *)

Lemma take_while_drop_while_append :
  forall {A} (f : A -> bool) (l : t A), append (take_while f l) (drop_while f l) = l.
Proof.
  intros A f l; induction l as [| x l' IH]; simpl.
  - reflexivity.
  - destruct (f x); simpl; [f_equal; apply IH | reflexivity].
Qed.

(** ** unzip / zip *)

Lemma unzip_spec : forall {A B} (l : t (A * B)), unzip l = (map fst l, map snd l).
Proof.
  intros A B l; induction l as [| [x y] l' IH]; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma zip_unzip_round_trip :
  forall {A B} (l : t (A * B)), zip (map fst l) (map snd l) = Some l.
Proof.
  intros A B l; induction l as [| [x y] l' IH]; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

(** ** partition_tf *)

Lemma partition_tf_spec :
  forall {A} (f : A -> bool) (l : t A),
    partition_tf f l = (filter f l, filter (fun x => negb (f x)) l).
Proof. reflexivity. Qed.
