From Stdlib Require Import List Arith Lia.
Import ListNotations.

(** * UndoList — Generic undo/redo wrapper for any pure reducer

    Given an inner reducer [inner : St -> E -> St], [UndoList] wraps it
    with a linear timeline: a current state, a stack of past states
    (for undo), and a stack of future states (for redo).

    [Do e]  applies the inner event [e], pushes current onto [past],
            and clears [future] (branching timeline discards the future).
    [Undo]  pops from [past] and pushes current onto [future].
            Returns [Failed] when [past] is empty.
    [Redo]  pops from [future] and pushes current onto [past].
            Returns [Failed] when [future] is empty.

    [Failed] is an absorbing element: all subsequent steps on it
    return [Failed], mirroring the [Failed] cursor of UndoTree. *)

Section UndoList.

Context {St E : Type}.
Variable inner : St -> E -> St.

(** * 1. Data structures *)

Inductive state : Type :=
  | Hist   : St -> list St -> list St -> state
  | Failed : state.

Inductive event : Type :=
  | Do   : E -> event
  | Undo : event
  | Redo : event.

Definition current (hs : state) : option St :=
  match hs with
  | Failed        => None
  | Hist curr _ _ => Some curr
  end.

Definition past (hs : state) : list St :=
  match hs with
  | Failed      => []
  | Hist _ p _  => p
  end.

Definition future (hs : state) : list St :=
  match hs with
  | Failed        => []
  | Hist _ _ fut  => fut
  end.

(** * 2. Definitions *)

(** [flat_map] is the sequencing primitive: it applies a step to a
    valid state and propagates [Failed] unchanged, mirroring
    [cursor_flat_map] in UndoTree. *)
Definition flat_map (hs : state)
    (f : St -> list St -> list St -> state) : state :=
  match hs with
  | Failed          => Failed
  | Hist curr p fut => f curr p fut
  end.

(** Initial state — no past, no future. *)
Definition init (s : St) : state := Hist s [] [].

(** The step function. *)
Definition step (hs : state) (e : event) : state :=
  flat_map hs (fun curr p fut =>
    match e with
    | Do ev   => Hist (inner curr ev) (curr :: p) []
    | Undo    => match p with
                 | []           => Failed
                 | prev :: rest => Hist prev rest (curr :: fut)
                 end
    | Redo    => match fut with
                 | []           => Failed
                 | next :: rest => Hist next (curr :: p) rest
                 end
    end).

(** Predicates exposed to the UI layer. *)
Definition is_failed (hs : state) : bool :=
  match hs with Failed => true | _ => false end.

Definition can_undo (hs : state) : bool :=
  match hs with
  | Failed       => false
  | Hist _ [] _  => false
  | Hist _ _ _   => true
  end.

Definition can_redo (hs : state) : bool :=
  match hs with
  | Failed       => false
  | Hist _ _ []  => false
  | Hist _ _ _   => true
  end.

(** Constructor helpers for extraction. *)
Definition mk_do   (e : E) : event := Do e.
Definition mk_undo : event := Undo.
Definition mk_redo : event := Redo.

(** * 3. Lemmas *)

(** [Failed] absorbs all steps. *)
Lemma failed_absorbs :
  forall e, step Failed e = Failed.
Proof.
  intros e. destruct e ; reflexivity.
Qed.

(** [flat_map] with the identity continuation is the identity. *)
Lemma flat_map_right_id :
  forall hs,
    flat_map hs (fun curr p fut => Hist curr p fut) = hs.
Proof.
  intros hs. destruct hs ; reflexivity.
Qed.

(** [flat_map] is associative. *)
Lemma flat_map_assoc :
  forall (hs : state) (f : St -> list St -> list St -> state)
         (g : St -> list St -> list St -> state),
    flat_map (flat_map hs f) g =
    flat_map hs (fun curr p fut => flat_map (f curr p fut) g).
Proof.
  intros hs f g. destruct hs ; reflexivity.
Qed.

(** After [Do], the current state is the image of [inner]. *)
Lemma do_current :
  forall curr p fut e,
    current (step (Hist curr p fut) (Do e)) = Some (inner curr e).
Proof.
  intros. simpl. reflexivity.
Qed.

(** After [Do], past grows by exactly one. *)
Lemma do_extends_past :
  forall curr p fut e,
    past (step (Hist curr p fut) (Do e)) = curr :: p.
Proof.
  intros. simpl. reflexivity.
Qed.

(** After [Do], future is cleared. *)
Lemma do_clears_future :
  forall curr p fut e,
    future (step (Hist curr p fut) (Do e)) = [].
Proof.
  intros. simpl. reflexivity.
Qed.

(** [Undo] on empty past yields [Failed]. *)
Lemma undo_failed_when_empty :
  forall curr fut,
    step (Hist curr [] fut) Undo = Failed.
Proof.
  intros. simpl. reflexivity.
Qed.

(** [Undo] on non-empty past restores the most-recent past state. *)
Lemma undo_restores :
  forall curr p fut prev rest,
    p = prev :: rest ->
    current (step (Hist curr p fut) Undo) = Some prev.
Proof.
  intros curr p fut prev rest Hp. subst. simpl. reflexivity.
Qed.

(** [Redo] on empty future yields [Failed]. *)
Lemma redo_failed_when_empty :
  forall curr p,
    step (Hist curr p []) Redo = Failed.
Proof.
  intros. simpl. reflexivity.
Qed.

(** [Redo] on non-empty future restores the most-recent future state. *)
Lemma redo_restores :
  forall curr p fut next rest,
    fut = next :: rest ->
    current (step (Hist curr p fut) Redo) = Some next.
Proof.
  intros curr p fut next rest Hf. subst. simpl. reflexivity.
Qed.

(** * 4. Theorems *)

(** [Do] then [Undo] reverts to the previous current state.
    Note: the future after undo is [[inner curr e]] (the state we just
    applied), not the original [fut], because [Do] discards the future. *)
Theorem undo_after_do :
  forall curr p fut e,
    current (step (step (Hist curr p fut) (Do e)) Undo) = Some curr.
Proof.
  intros curr p fut e. simpl. reflexivity.
Qed.

Theorem undo_after_do_state :
  forall curr p fut e,
    step (step (Hist curr p fut) (Do e)) Undo =
    Hist curr p [inner curr e].
Proof.
  intros curr p fut e. simpl. reflexivity.
Qed.

(** [Undo] then [Redo] reverts to the current state before undo,
    provided past was non-empty. *)
Theorem redo_after_undo :
  forall curr p fut prev rest,
    p = prev :: rest ->
    step (step (Hist curr p fut) Undo) Redo =
    Hist curr p fut.
Proof.
  intros curr p fut prev rest Hp. subst. simpl. reflexivity.
Qed.

(** [Undo] preserves |past| + |future| when past is non-empty.
    (When past is empty [Undo] yields [Failed] which has size 0.) *)
Theorem undo_preserves_size :
  forall curr p fut prev rest,
    p = prev :: rest ->
    length (past  (step (Hist curr p fut) Undo)) +
    length (future (step (Hist curr p fut) Undo)) =
    length p + length fut.
Proof.
  intros curr p fut prev rest Hp. subst. simpl. lia.
Qed.

(** [Redo] preserves |past| + |future| when future is non-empty.
    (When future is empty [Redo] yields [Failed] which has size 0.) *)
Theorem redo_preserves_size :
  forall curr p fut next rest,
    fut = next :: rest ->
    length (past  (step (Hist curr p fut) Redo)) +
    length (future (step (Hist curr p fut) Redo)) =
    length p + length fut.
Proof.
  intros curr p fut next rest Hf. subst. simpl. lia.
Qed.

(** [Do] increases |past| by one and clears future. *)
Theorem do_size_change :
  forall curr p fut e,
    length (past   (step (Hist curr p fut) (Do e))) = 1 + length p /\
    length (future (step (Hist curr p fut) (Do e))) = 0.
Proof.
  intros. simpl. lia.
Qed.

(** [can_undo] correctly reflects non-emptiness of past. *)
Theorem can_undo_correct :
  forall curr p fut,
    can_undo (Hist curr p fut) = true <-> p <> [].
Proof.
  intros curr p fut. destruct p ; simpl ; split ; congruence.
Qed.

(** [can_redo] correctly reflects non-emptiness of future. *)
Theorem can_redo_correct :
  forall curr p fut,
    can_redo (Hist curr p fut) = true <-> fut <> [].
Proof.
  intros curr p fut. destruct fut ; simpl ; split ; congruence.
Qed.

(** Applying [Do] after [init] gives exactly one element in past. *)
Theorem init_do_has_one_past :
  forall s e,
    past   (step (init s) (Do e)) = [s] /\
    future (step (init s) (Do e)) = [].
Proof.
  intros. simpl. split ; reflexivity.
Qed.

(** From [init], [Undo] yields [Failed]. *)
Theorem init_undo_failed :
  forall s,
    step (init s) Undo = Failed.
Proof.
  intros. simpl. reflexivity.
Qed.

(** From [init], [Redo] yields [Failed]. *)
Theorem init_redo_failed :
  forall s,
    step (init s) Redo = Failed.
Proof.
  intros. simpl. reflexivity.
Qed.

End UndoList.
