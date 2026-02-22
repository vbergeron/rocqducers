From Stdlib Require Import List Arith Lia.
Import ListNotations.

(** * StateHistory — Generic undo/redo wrapper for any pure reducer

    Given an inner reducer [inner : S -> E -> S], [StateHistory]
    wraps it with a timeline: a current state, a stack of past states
    (for undo), and a stack of future states (for redo).

    [Do e]  applies the inner event [e], pushes current onto [past],
            and clears [future] (branching timeline discards the future).
    [Undo]  pops from [past] and pushes current onto [future].
    [Redo]  pops from [future] and pushes current onto [past].
*)

(** * 1. Data structures *)

Record history_state (S : Type) := mk_history {
  current : S;
  past    : list S;   (** most-recent-first *)
  future  : list S;   (** most-recent-first *)
}.

Arguments mk_history {S}.
Arguments current  {S}.
Arguments past     {S}.
Arguments future   {S}.

Inductive history_event (E : Type) :=
  | Do   : E -> history_event E
  | Undo : history_event E
  | Redo : history_event E.

Arguments Do   {E}.
Arguments Undo {E}.
Arguments Redo {E}.

(** * 2. Definitions *)

(** Initial history state — no past, no future. *)
Definition history_init {S} (s : S) : history_state S :=
  mk_history s [] [].

(** Constructors for extraction *)
Definition mk_do   {E} (e : E) : history_event E := Do e.
Definition mk_undo {E}          : history_event E := Undo.
Definition mk_redo {E}          : history_event E := Redo.

(** The step function.  [inner] is the wrapped pure reducer. *)
Definition history_step {S E}
    (inner : S -> E -> S)
    (hs    : history_state S)
    (e     : history_event E)
    : history_state S :=
  match e with
  | Do ev =>
    mk_history (inner (current hs) ev)
               (current hs :: past hs)
               []
  | Undo =>
    match past hs with
    | []           => hs
    | prev :: rest =>
      mk_history prev rest (current hs :: future hs)
    end
  | Redo =>
    match future hs with
    | []           => hs
    | next :: rest =>
      mk_history next (current hs :: past hs) rest
    end
  end.

(** Predicates exposed to the JS layer. *)
Definition can_undo {S} (hs : history_state S) : bool :=
  match past hs with [] => false | _ => true end.

Definition can_redo {S} (hs : history_state S) : bool :=
  match future hs with [] => false | _ => true end.

(** * 3. Lemmas *)

(** After [Do], the current state is the image of the inner reducer. *)
Lemma do_current : forall S E (inner : S -> E -> S) hs e,
  current (history_step inner hs (Do e)) = inner (current hs) e.
Proof.
  intros. simpl. reflexivity.
Qed.

(** After [Do], the past grows by exactly one (the previous current). *)
Lemma do_extends_past : forall S E (inner : S -> E -> S) hs e,
  past (history_step inner hs (Do e)) = current hs :: past hs.
Proof.
  intros. simpl. reflexivity.
Qed.

(** After [Do], the future is always empty (branching discards it). *)
Lemma do_clears_future : forall S E (inner : S -> E -> S) hs e,
  future (history_step inner hs (Do e)) = [].
Proof.
  intros. simpl. reflexivity.
Qed.

(** [Undo] is a no-op when past is empty. *)
Lemma undo_noop_when_empty : forall S E (inner : S -> E -> S) hs,
  past hs = [] ->
  history_step inner hs Undo = hs.
Proof.
  intros S E inner hs Hp.
  simpl. rewrite Hp. reflexivity.
Qed.

(** When past is non-empty, [Undo] restores the most-recent past state. *)
Lemma undo_restores : forall S E (inner : S -> E -> S) hs prev rest,
  past hs = prev :: rest ->
  current (history_step inner hs Undo) = prev.
Proof.
  intros S E inner hs prev rest Hp.
  simpl. rewrite Hp. reflexivity.
Qed.

(** [Redo] is a no-op when future is empty. *)
Lemma redo_noop_when_empty : forall S E (inner : S -> E -> S) hs,
  future hs = [] ->
  history_step inner hs Redo = hs.
Proof.
  intros S E inner hs Hf.
  simpl. rewrite Hf. reflexivity.
Qed.

(** When future is non-empty, [Redo] restores the most-recent future state. *)
Lemma redo_restores : forall S E (inner : S -> E -> S) hs next rest,
  future hs = next :: rest ->
  current (history_step inner hs Redo) = next.
Proof.
  intros S E inner hs next rest Hf.
  simpl. rewrite Hf. reflexivity.
Qed.

(** * 4. Theorems *)

(** Theorem 1: [Do] then [Undo] reverts to the previous current state.
    Whatever event we apply, undoing it brings back the state we had
    before — regardless of what the inner reducer does. *)
Theorem undo_after_do : forall S E (inner : S -> E -> S) hs e,
  current (history_step inner (history_step inner hs (Do e)) Undo) = current hs.
Proof.
  intros S E inner hs e.
  (* After Do, past = current hs :: past hs, so Undo restores current hs *)
  simpl. reflexivity.
Qed.

(** Theorem 2: [Undo] then [Redo] reverts to the current state before undo,
    provided there was something to undo.
    i.e., the Undo/Redo pair is an identity on the current value. *)
Theorem redo_after_undo : forall S E (inner : S -> E -> S) hs prev rest,
  past hs = prev :: rest ->
  current (history_step inner (history_step inner hs Undo) Redo) = current hs.
Proof.
  intros S E inner hs prev rest Hp.
  simpl. rewrite Hp. reflexivity.
Qed.

(** Theorem 3: The timeline length (past + 1 + future) is preserved by
    [Undo] and [Redo], and increases by exactly 1 on [Do]
    (because Do drops the future and adds to past, increasing past by 1,
     but it also clears future, so net change = 1 + |past| + 0 vs
     0 + |past| + |future|  — actually, [Do] changes the total by
     - |future| + 1.   The simpler invariant below just tracks past+future.) *)

(** The "reachable" size (|past| + |future|) increases by 1 on [Do]
    when future is empty (the common case after a linear sequence of Dos),
    and by (1 - |future|) in general.  Rather than tracking that,
    we prove the useful monotone invariant:
    Undo and Redo preserve |past| + |future|. *)
Theorem undo_preserves_size : forall S E (inner : S -> E -> S) hs,
  length (past (history_step inner hs Undo)) +
  length (future (history_step inner hs Undo)) =
  length (past hs) + length (future hs).
Proof.
  intros S E inner hs.
  simpl.
  destruct (past hs) as [| prev rest].
  - (* past empty: no-op *) reflexivity.
  - (* past = prev :: rest *) simpl. lia.
Qed.

Theorem redo_preserves_size : forall S E (inner : S -> E -> S) hs,
  length (past (history_step inner hs Redo)) +
  length (future (history_step inner hs Redo)) =
  length (past hs) + length (future hs).
Proof.
  intros S E inner hs.
  simpl.
  destruct (future hs) as [| next rest].
  - (* future empty: no-op *) reflexivity.
  - (* future = next :: rest *) simpl. lia.
Qed.

(** Theorem 4: [Do] increases |past| by one and sets |future| to 0.
    Net change in |past| + |future| = 1 - |future_before|. *)
Theorem do_size_change : forall S E (inner : S -> E -> S) hs e,
  length (past (history_step inner hs (Do e))) = 1 + length (past hs) /\
  length (future (history_step inner hs (Do e))) = 0.
Proof.
  intros. simpl. lia.
Qed.

(** Theorem 5: [can_undo] correctly reflects non-emptiness of [past]. *)
Theorem can_undo_correct : forall S (hs : history_state S),
  can_undo hs = true <-> past hs <> [].
Proof.
  intros S hs.
  unfold can_undo.
  destruct (past hs) as [| h t].
  - split; intro H; [discriminate | contradiction].
  - split; intro _; discriminate.
Qed.

(** Theorem 6: [can_redo] correctly reflects non-emptiness of [future]. *)
Theorem can_redo_correct : forall S (hs : history_state S),
  can_redo hs = true <-> future hs <> [].
Proof.
  intros S hs.
  unfold can_redo.
  destruct (future hs) as [| h t].
  - split; intro H; [discriminate | contradiction].
  - split; intro _; discriminate.
Qed.

(** Theorem 7: Applying [Do] after [history_init] gives a state with
    exactly one element in past and an empty future. *)
Theorem init_do_has_one_past : forall S E (inner : S -> E -> S) s e,
  past (history_step inner (history_init s) (Do e)) = [s] /\
  future (history_step inner (history_init s) (Do e)) = [].
Proof.
  intros. simpl. split; reflexivity.
Qed.

(** Theorem 8: From [history_init], [Undo] and [Redo] are no-ops. *)
Theorem init_undo_noop : forall S E (inner : S -> E -> S) s,
  history_step inner (history_init s) Undo = history_init s.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem init_redo_noop : forall S E (inner : S -> E -> S) s,
  history_step inner (history_init s) Redo = history_init s.
Proof.
  intros. simpl. reflexivity.
Qed.
