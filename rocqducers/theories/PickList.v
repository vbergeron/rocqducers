From Stdlib Require Import List Arith Lia.
Import ListNotations.

(** * 1. Datastructures and arguments *)

Record state (A : Type) := mkState {
  picked : list A;
  suggestions : list A;
}.

Arguments mkState {A}.
Arguments picked {A}.
Arguments suggestions {A}.

Inductive event :=
  | DoPick : nat -> event
  | DoUnpick : nat -> event.

(** * 2. Definitions and Fixpoints *)

Fixpoint nth {A : Type} (l : list A) (n : nat) : option A :=
  match l, n with
  | [], _ => None
  | x :: _, O => Some x
  | _ :: t, S n' => nth t n'
  end.

Fixpoint remove_at {A : Type} (i : nat) (l : list A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: t, O => t
  | h :: t, S i' => h :: remove_at i' t
  end.

Definition mk_do_pick (i : nat) : event := DoPick i.
Definition mk_do_unpick (i : nat) : event := DoUnpick i.

Definition do_pick {A} (s : state A) (i : nat) : state A :=
  match nth (suggestions s) i with
  | None => s
  | Some x => mkState (x :: picked s) (remove_at i (suggestions s))
  end.

Definition do_unpick {A} (s : state A) (i : nat) : state A :=
  match picked s with
  | [] => s
  | [_] => s
  | _ =>
    match nth (picked s) i with
    | None => s
    | Some x => mkState (remove_at i (picked s)) (x :: suggestions s)
    end
  end.

Definition reducer {A} (s : state A) (e : event) : state A :=
  match e with
  | DoPick i => do_pick s i
  | DoUnpick i => do_unpick s i
  end.

Definition init_state {A} (default : A) (rest : list A) : state A :=
  mkState [default] rest.

(** * 3. Lemmas *)

(** Needed by [do_pick_total] and [do_unpick_total]: if [nth]
    succeeds, the index is within bounds. *)

Lemma nth_Some_lt : forall A (l : list A) i x,
  nth l i = Some x -> i < length l.
Proof.
  intros A l. induction l as [| h t IH]; intros i x H.
  - (* l = [] : nth returns None, contradicts H *)
    destruct i; discriminate.
  - (* l = h :: t *)
    destruct i as [| i']; simpl in *.
    + (* i = 0 : trivially 0 < S (length t) *) lia.
    + (* i = S i' : apply IH *) apply IH in H. lia.
Qed.

(** Needed by [do_pick_total] and [do_unpick_total]: removing an
    in-bounds element decreases length by exactly one. *)

Lemma remove_at_length : forall A (i : nat) (l : list A),
  i < length l -> length (remove_at i l) = length l - 1.
Proof.
  intros A i l. revert i.
  induction l as [| h t IH]; intros i Hi.
  - (* l = [] : contradicts i < 0 *) simpl in Hi. lia.
  - destruct i as [| i'].
    + (* i = 0 : remove head *) simpl. lia.
    + (* i = S i' : recurse into tail *)
      simpl. simpl in Hi. rewrite IH by lia. lia.
Qed.

(** Needed by [do_unpick_nonempty]: removing any element from a
    list with >= 2 elements still leaves a non-empty list. *)

Lemma remove_at_cons_nonempty : forall A (a b : A) (t : list A) i,
  remove_at i (a :: b :: t) <> [].
Proof.
  intros A a b t i.
  destruct i as [| i']; simpl.
  - (* i = 0 : result is b :: t *) discriminate.
  - (* i = S i' : result is a :: _ *) discriminate.
Qed.

(** [do_pick] preserves non-emptiness of picked.
    If suggestions[i] exists, picked grows by one (cons is non-empty).
    If suggestions[i] is out of bounds, state is unchanged. *)

Lemma do_pick_nonempty : forall A (s : state A) i,
  picked s <> [] -> picked (do_pick s i) <> [].
Proof.
  intros A s i Hne.
  unfold do_pick.
  destruct (nth (suggestions s) i); simpl.
  - (* Some x : picked becomes x :: picked s *) discriminate.
  - (* None : state unchanged *) exact Hne.
Qed.

(** [do_unpick] preserves non-emptiness of picked.
    When picked has 0 or 1 elements, do_unpick is a no-op.
    When picked has >= 2 elements, removing one still leaves >= 1
    (by [remove_at_cons_nonempty]). *)

Lemma do_unpick_nonempty : forall A (s : state A) i,
  picked s <> [] -> picked (do_unpick s i) <> [].
Proof.
  intros A s i Hne.
  unfold do_unpick.
  destruct (picked s) as [| a [| b t]] eqn:Hp.
  - (* picked s = [] : contradicts Hne *)
    contradiction.
  - (* picked s = [a] : do_unpick is a no-op, [a] <> [] *)
    simpl. rewrite Hp. discriminate.
  - (* picked s = a :: b :: t : at least 2 elements *)
    destruct (nth (a :: b :: t) i) eqn:Hn.
    + (* Some : remove_at on >= 2 elements is non-empty *)
      simpl. apply remove_at_cons_nonempty.
    + (* None : state unchanged, picked = a :: b :: t <> [] *)
      simpl. rewrite Hp. discriminate.
Qed.

(** [do_pick] preserves the total count.
    Moves one element from suggestions to picked: picked grows by 1,
    suggestions shrinks by 1 (via [remove_at_length]). *)

Lemma do_pick_total : forall A (s : state A) i,
  length (picked (do_pick s i)) + length (suggestions (do_pick s i)) =
  length (picked s) + length (suggestions s).
Proof.
  intros A s i.
  unfold do_pick.
  destruct (nth (suggestions s) i) eqn:Hn.
  - (* Some : one element moves from suggestions to picked *)
    simpl. apply nth_Some_lt in Hn.
    rewrite remove_at_length by exact Hn. lia.
  - (* None : state unchanged *)
    reflexivity.
Qed.

(** [do_unpick] preserves the total count.
    When picked has <= 1 elements, no-op. Otherwise moves one element
    from picked to suggestions (symmetric to [do_pick_total]). *)

Lemma do_unpick_total : forall A (s : state A) i,
  length (picked (do_unpick s i)) + length (suggestions (do_unpick s i)) =
  length (picked s) + length (suggestions s).
Proof.
  intros A s i.
  unfold do_unpick.
  destruct (picked s) as [| a [| b t]] eqn:Hp.
  - (* picked s = [] : no-op *)
    simpl. rewrite Hp. reflexivity.
  - (* picked s = [a] : no-op *)
    simpl. rewrite Hp. reflexivity.
  - (* picked s = a :: b :: t *)
    destruct (nth (a :: b :: t) i) eqn:Hn.
    + (* Some : one element moves from picked to suggestions *)
      apply nth_Some_lt in Hn.
      simpl picked. simpl suggestions.
      rewrite remove_at_length by exact Hn. simpl. lia.
    + (* None : state unchanged *)
      simpl. rewrite Hp. reflexivity.
Qed.

(** Base case: [init_state] produces a state where [picked = [default]],
    which is non-empty. *)

Lemma init_picked_nonempty : forall A (d : A) rest,
  picked (init_state d rest) <> [].
Proof.
  intros. simpl. discriminate.
Qed.

(** * 4. Theorems *)

(** Invariant 1: the picked list is never empty.
    If picked starts non-empty, no event can make it empty.
    [do_pick] prepends to picked (cons is non-empty),
    [do_unpick] refuses to act when only one element remains. *)

Theorem picked_nonempty : forall A (s : state A) e,
  picked s <> [] -> picked (reducer s e) <> [].
Proof.
  intros A s e Hne.
  destruct e; simpl.
  - apply do_pick_nonempty; exact Hne.
  - apply do_unpick_nonempty; exact Hne.
Qed.

(** Invariant 2: the total number of items never changes.
    Every [do_pick] moves one item from suggestions to picked,
    every [do_unpick] moves one item from picked to suggestions.
    Out-of-bounds indices leave the state unchanged. *)

Theorem total_preserved : forall A (s : state A) e,
  length (picked (reducer s e)) + length (suggestions (reducer s e)) =
  length (picked s) + length (suggestions s).
Proof.
  intros A s e.
  destruct e; simpl.
  - apply do_pick_total.
  - apply do_unpick_total.
Qed.

(** Full induction: for any sequence of events starting from
    [init_state], picked is always non-empty. Combines the base
    case [init_picked_nonempty] with the inductive step
    [picked_nonempty]. *)

Theorem picked_always_nonempty : forall A (d : A) rest events,
  picked (fold_left reducer events (init_state d rest)) <> [].
Proof.
  intros A d rest events.
  (* Generalize: any state with non-empty picked stays non-empty *)
  cut (picked (init_state d rest) <> [] ->
       picked (fold_left reducer events (init_state d rest)) <> []).
  { intro H. apply H. apply init_picked_nonempty. }
  generalize (init_state d rest) as s.
  induction events as [| e es IH]; intros s Hne; simpl.
  - (* Base: no events, picked unchanged *) exact Hne.
  - (* Step: apply IH to the next state *)
    apply IH. apply picked_nonempty. exact Hne.
Qed.

(** Full induction: for any sequence of events starting from
    [init_state], the total count equals [1 + length rest]. *)

Theorem total_always_preserved : forall A (d : A) rest events,
  let s := fold_left reducer events (init_state d rest) in
  length (picked s) + length (suggestions s) = 1 + length rest.
Proof.
  intros A d rest events. simpl.
  (* Generalize: total count is preserved from any starting state *)
  cut (length (picked (init_state d rest)) + length (suggestions (init_state d rest)) = 1 + length rest ->
       length (picked (fold_left reducer events (init_state d rest))) +
       length (suggestions (fold_left reducer events (init_state d rest))) = 1 + length rest).
  { intro H. apply H. reflexivity. }
  generalize (init_state d rest) as s.
  induction events as [| e es IH]; intros s Hs; simpl.
  - (* Base: no events *) exact Hs.
  - (* Step: rewrite with total_preserved *)
    apply IH. rewrite total_preserved. exact Hs.
Qed.
