From Stdlib Require Import Bool.

Definition t (A : Type) := option A.

Definition is_none {A : Type} (o : t A) : bool :=
  match o with None => true | Some _ => false end.

Definition is_some {A : Type} (o : t A) : bool :=
  match o with None => false | Some _ => true end.

Definition value {A : Type} (o : t A) (default : A) : A :=
  match o with None => default | Some x => x end.

Definition map {A B : Type} (f : A -> B) (o : t A) : t B :=
  match o with None => None | Some x => Some (f x) end.

Definition return_ {A : Type} (x : A) : t A := Some x.

Definition bind {A B : Type} (o : t A) (f : A -> t B) : t B :=
  match o with None => None | Some x => f x end.

Definition iter {A : Type} (o : t A) (f : A -> unit) : unit :=
  match o with None => tt | Some x => f x end.

Definition exists_ {A : Type} (f : A -> bool) (o : t A) : bool :=
  match o with None => false | Some x => f x end.

Definition for_all {A : Type} (f : A -> bool) (o : t A) : bool :=
  match o with None => true | Some x => f x end.

Definition find {A : Type} (f : A -> bool) (o : t A) : t A :=
  match o with
  | Some x => if f x then Some x else None
  | None => None
  end.

Definition filter {A : Type} (f : A -> bool) (o : t A) : t A := find f o.

Definition first_some {A : Type} (o1 o2 : t A) : t A :=
  match o1 with Some _ => o1 | None => o2 end.

Definition merge {A : Type} (o1 o2 : t A) (f : A -> A -> A) : t A :=
  match o1, o2 with
  | None, None => None
  | Some x, None => Some x
  | None, Some y => Some y
  | Some x, Some y => Some (f x y)
  end.

Definition equal {A : Type} (eq : A -> A -> bool) (o1 o2 : t A) : bool :=
  match o1, o2 with
  | None, None => true
  | Some x, Some y => eq x y
  | _, _ => false
  end.

(** [None] sorts before every [Some _], matching Base's [Option.compare]. *)
Definition compare {A : Type} (cmp : A -> A -> comparison) (o1 o2 : t A) : comparison :=
  match o1, o2 with
  | None, None => Eq
  | None, Some _ => Lt
  | Some _, None => Gt
  | Some x, Some y => cmp x y
  end.

Definition value_map {A B : Type} (o : t A) (default : B) (f : A -> B) : B :=
  match o with None => default | Some x => f x end.

Definition value_or_thunk {A : Type} (o : t A) (default : unit -> A) : A :=
  match o with None => default tt | Some x => x end.

Definition fold {A Acc : Type} (o : t A) (init : Acc) (f : Acc -> A -> Acc) : Acc :=
  match o with None => init | Some x => f init x end.

Definition mem {A : Type} (eq : A -> A -> bool) (x : A) (o : t A) : bool :=
  match o with None => false | Some y => eq x y end.

Definition length {A : Type} (o : t A) : nat :=
  match o with None => O | Some _ => 1 end.

Definition find_map {A B : Type} (f : A -> t B) (o : t A) : t B :=
  match o with None => None | Some x => f x end.

Definition to_list {A : Type} (o : t A) : list A :=
  match o with None => nil | Some x => cons x nil end.

(** [call x f] runs the optional function [f] on [x], doing nothing if [f] is [None]. *)
Definition call {A : Type} (x : A) (f : t (A -> unit)) : unit :=
  match f with None => tt | Some g => g x end.

Definition some {A : Type} (x : A) : t A := Some x.

Definition some_if {A : Type} (b : bool) (x : A) : t A := if b then Some x else None.

(** ** Applicative interface *)

Definition map2 {A B C : Type} (f : A -> B -> C) (o1 : t A) (o2 : t B) : t C :=
  match o1, o2 with
  | Some x, Some y => Some (f x y)
  | _, _ => None
  end.

Definition both {A B : Type} (o1 : t A) (o2 : t B) : t (A * B) :=
  match o1, o2 with
  | Some x, Some y => Some (x, y)
  | _, _ => None
  end.

Definition apply {A B : Type} (of_ : t (A -> B)) (o : t A) : t B :=
  match of_, o with
  | Some f, Some x => Some (f x)
  | _, _ => None
  end.

(** ** Basic predicates *)

Lemma is_none_is_some : forall {A} (o : t A), is_none o = negb (is_some o).
Proof. intros A []; reflexivity. Qed.

Lemma value_some : forall {A} (x default : A), value (Some x) default = x.
Proof. reflexivity. Qed.

Lemma value_none : forall {A} (default : A), value None default = default.
Proof. reflexivity. Qed.

Lemma first_some_some_l : forall {A} (x : A) o2, first_some (Some x) o2 = Some x.
Proof. reflexivity. Qed.

Lemma first_some_none_l : forall {A} (o2 : t A), first_some None o2 = o2.
Proof. reflexivity. Qed.

(** ** Functor laws *)

Lemma map_id : forall {A} (o : t A), map (fun x => x) o = o.
Proof. intros A []; reflexivity. Qed.

Lemma map_map :
  forall {A B C} (f : A -> B) (g : B -> C) (o : t A),
    map g (map f o) = map (fun x => g (f x)) o.
Proof. intros A B C f g []; reflexivity. Qed.

(** ** Monad laws *)

Lemma left_identity : forall {A B} (x : A) (f : A -> t B), bind (return_ x) f = f x.
Proof. reflexivity. Qed.

Lemma right_identity : forall {A} (o : t A), bind o return_ = o.
Proof. intros A []; reflexivity. Qed.

Lemma assoc :
  forall {A B C} (o : t A) (f : A -> t B) (g : B -> t C),
    bind (bind o f) g = bind o (fun x => bind (f x) g).
Proof. intros A B C [] f g; reflexivity. Qed.

(** ** equal *)

Lemma equal_reflects :
  forall {A} (eq : A -> A -> bool),
    (forall x y, eq x y = true <-> x = y) ->
    forall o1 o2, equal eq o1 o2 = true <-> o1 = o2.
Proof.
  intros A eq Heq [x |] [y |]; simpl; split; intros H;
    try discriminate; try reflexivity.
  - f_equal. apply Heq; assumption.
  - injection H as ->. apply Heq; reflexivity.
Qed.

(** ** compare *)

Lemma compare_some_some :
  forall {A} (cmp : A -> A -> comparison) x y, compare cmp (Some x) (Some y) = cmp x y.
Proof. reflexivity. Qed.

Lemma compare_none_none : forall {A} (cmp : A -> A -> comparison), compare cmp (@None A) None = Eq.
Proof. reflexivity. Qed.

Lemma compare_none_some :
  forall {A} (cmp : A -> A -> comparison) y, compare cmp (@None A) (Some y) = Lt.
Proof. reflexivity. Qed.

Lemma compare_some_none :
  forall {A} (cmp : A -> A -> comparison) x, compare cmp (Some x) (@None A) = Gt.
Proof. reflexivity. Qed.

(** ** mem *)

Lemma mem_reflects :
  forall {A} (eq : A -> A -> bool),
    (forall x y, eq x y = true <-> x = y) ->
    forall x o, mem eq x o = true <-> o = Some x.
Proof.
  intros A eq Heq x [y |]; simpl; split; intros H.
  - f_equal. symmetry. apply Heq; assumption.
  - injection H as <-. apply Heq; reflexivity.
  - discriminate.
  - discriminate.
Qed.

(** ** value_map / find_map *)

Lemma value_map_spec :
  forall {A B} (o : t A) (default : B) (f : A -> B), value_map o default f = value (map f o) default.
Proof. intros A B [] default f; reflexivity. Qed.

Lemma find_map_is_bind : forall {A B} (f : A -> t B) (o : t A), find_map f o = bind o f.
Proof. reflexivity. Qed.

(** ** Applicative interface *)

Lemma map2_some : forall {A B C} (f : A -> B -> C) x y, map2 f (Some x) (Some y) = Some (f x y).
Proof. reflexivity. Qed.

Lemma both_map2 : forall {A B} (o1 : t A) (o2 : t B), both o1 o2 = map2 (fun x y => (x, y)) o1 o2.
Proof. intros A B [] []; reflexivity. Qed.

Lemma apply_return : forall {A B} (f : A -> B) (x : A), apply (return_ f) (return_ x) = return_ (f x).
Proof. reflexivity. Qed.
