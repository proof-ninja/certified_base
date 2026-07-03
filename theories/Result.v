Inductive t (A E : Type) : Type :=
  | Ok : A -> t A E
  | Error : E -> t A E.

Arguments Ok {A E} _.
Arguments Error {A E} _.

Definition return_ {A E : Type} (x : A) : t A E := Ok x.

Definition bind {A B E : Type} (m : t A E) (f : A -> t B E) : t B E :=
  match m with
  | Ok x => f x
  | Error e => Error e
  end.

Definition map {A B E : Type} (f : A -> B) (m : t A E) : t B E :=
  bind m (fun x => return_ (f x)).

Definition map_error {A E F : Type} (f : E -> F) (m : t A E) : t A F :=
  match m with
  | Ok x => Ok x
  | Error e => Error (f e)
  end.

Definition is_ok {A E : Type} (m : t A E) : bool :=
  match m with Ok _ => true | Error _ => false end.

Definition is_error {A E : Type} (m : t A E) : bool :=
  match m with Ok _ => false | Error _ => true end.

Definition ok {A E : Type} (m : t A E) : option A :=
  match m with Ok x => Some x | Error _ => None end.

Definition error {A E : Type} (m : t A E) : option E :=
  match m with Ok _ => None | Error e => Some e end.

Definition value {A E : Type} (m : t A E) (default : A) : A :=
  match m with Ok x => x | Error _ => default end.

(** ** Functor laws *)

Lemma map_id : forall {A E} (m : t A E), map (fun x => x) m = m.
Proof. intros A E [x | e]; reflexivity. Qed.

Lemma map_map :
  forall {A B C E} (f : A -> B) (g : B -> C) (m : t A E),
    map g (map f m) = map (fun x => g (f x)) m.
Proof. intros A B C E f g [x | e]; reflexivity. Qed.

(** ** Monad laws *)

Lemma left_identity :
  forall {A B E} (x : A) (f : A -> t B E), bind (return_ x) f = f x.
Proof. intros; reflexivity. Qed.

Lemma right_identity : forall {A E} (m : t A E), bind m return_ = m.
Proof. intros A E [x | e]; reflexivity. Qed.

Lemma assoc :
  forall {A B C E} (m : t A E) (f : A -> t B E) (g : B -> t C E),
    bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof. intros A B C E [x | e] f g; reflexivity. Qed.

Lemma is_ok_is_error : forall {A E} (m : t A E), is_ok m = negb (is_error m).
Proof. intros A E [x | e]; reflexivity. Qed.
