From Stdlib Require Import List Arith Lia.
Import ListNotations.

(** * 1. Datastructures and arguments

    A navigation history is a "zipper" over a timeline:
    - [past]    : previously visited items, most-recent first
    - [present] : the currently active item
    - [future]  : items reachable via GoForward, closest first

    Three events drive the state machine:
    - [GoBack]     : step one position into the past
    - [GoForward]  : step one position into the future
    - [Navigate x] : jump to a new item, discarding the future *)

Record state (A : Type) := mkState {
  past    : list A;
  present : A;
  future  : list A;
}.

Arguments mkState  {A}.
Arguments past     {A}.
Arguments present  {A}.
Arguments future   {A}.

Inductive event (A : Type) :=
  | GoBack    : event A
  | GoForward : event A
  | Navigate  : A -> event A.

Arguments GoBack    {A}.
Arguments GoForward {A}.
Arguments Navigate  {A}.

(** * 2. Definitions *)

(** Constructor aliases for clean extraction. *)

Definition mk_go_back    {A} : event A         := GoBack.
Definition mk_go_forward {A} : event A         := GoForward.
Definition mk_navigate   {A} (x : A) : event A := Navigate x.

(** The initial state has an empty past and future. *)

Definition init {A} (x : A) : state A :=
  mkState [] x [].

(** The step function.

    - [GoBack]    : if past is empty, no-op.
                    Otherwise pop the head of past into present
                    and push the old present onto future.
    - [GoForward] : symmetric — pops from future, pushes to past.
    - [Navigate x]: push present onto past, set x as present,
                    and clear future (forward history is lost). *)

Definition step {A} (s : state A) (e : event A) : state A :=
  match e with
  | GoBack =>
    match past s with
    | []      => s
    | p :: ps => mkState ps p (present s :: future s)
    end
  | GoForward =>
    match future s with
    | []      => s
    | f :: fs => mkState (present s :: past s) f fs
    end
  | Navigate x =>
    mkState (present s :: past s) x []
  end.

(** Shorthand for the total item count across all three slots. *)

Definition total {A} (s : state A) : nat :=
  length (past s) + 1 + length (future s).

(** * 3. Lemmas *)

(** [GoBack] preserves [total].
    When past is empty, [GoBack] is a no-op (trivial).
    When past = p :: ps, one item moves: past shrinks by 1,
    future grows by 1 (present is pushed), so the sum is stable. *)

Lemma goback_total : forall A (s : state A),
  total (step s GoBack) = total s.
Proof.
  intros A [p pres fut].
  destruct p as [| h t]; unfold total; simpl; lia.
Qed.

(** [GoForward] preserves [total].
    Symmetric argument to [goback_total]. *)

Lemma goforward_total : forall A (s : state A),
  total (step s GoForward) = total s.
Proof.
  intros A [p pres fut].
  destruct fut as [| h t]; unfold total; simpl; lia.
Qed.

(** [GoBack] then [GoForward] is the identity when past is non-empty.

    Let past = p :: ps.
    - [step s GoBack] = mkState ps p (pres :: fut)
    - [step _ GoForward] picks up (pres :: fut), puts p back into
      past, and recovers mkState (p :: ps) pres fut = s. *)

Lemma back_forward_id : forall A (s : state A),
  past s <> [] ->
  step (step s GoBack) GoForward = s.
Proof.
  intros A [p pres fut] Hne.
  destruct p as [| h t].
  - simpl in Hne. contradiction.
  - simpl. reflexivity.
Qed.

(** [GoForward] then [GoBack] is the identity when future is non-empty.
    Symmetric to [back_forward_id]. *)

Lemma forward_back_id : forall A (s : state A),
  future s <> [] ->
  step (step s GoForward) GoBack = s.
Proof.
  intros A [p pres fut] Hne.
  destruct fut as [| h t].
  - simpl in Hne. contradiction.
  - simpl. reflexivity.
Qed.

(** * 4. Theorems *)

(** Theorem 1 (roundtrip — backward direction).
    Going back and then forward returns to the original state exactly.
    This is the fundamental correctness property of the history zipper:
    [GoBack] and [GoForward] are mutual inverses. *)

Theorem back_then_forward : forall A (s : state A),
  past s <> [] ->
  step (step s GoBack) GoForward = s.
Proof.
  exact back_forward_id.
Qed.

(** Theorem 2 (roundtrip — forward direction).
    Going forward and then back returns to the original state exactly.
    Symmetric to [back_then_forward]. *)

Theorem forward_then_back : forall A (s : state A),
  future s <> [] ->
  step (step s GoForward) GoBack = s.
Proof.
  exact forward_back_id.
Qed.

(** Theorem 3 (Navigate clears future).
    Navigating to any new item always empties the forward history.
    This models the standard browser contract: once you diverge from
    a saved forward path by choosing a new destination, that path is
    gone — only the new trajectory exists. *)

Theorem navigate_clears_future : forall A (s : state A) (x : A),
  future (step s (Navigate x)) = [].
Proof.
  intros. simpl. reflexivity.
Qed.

(** Theorem 4 (Navigate records present).
    The item that was active becomes the new head of past.
    Combined with [back_then_forward], this guarantees that a single
    [GoBack] after [Navigate x] recovers the previous present. *)

Theorem navigate_records_present : forall A (s : state A) (x : A),
  past (step s (Navigate x)) = present s :: past s.
Proof.
  intros. simpl. reflexivity.
Qed.

(** Theorem 5 (GoBack preserves total).
    The total number of items |past| + 1 + |future| never changes
    under [GoBack].  Items only move between the three slots; none
    is created or destroyed. *)

Theorem total_preserved_by_back : forall A (s : state A),
  total (step s GoBack) = total s.
Proof.
  exact goback_total.
Qed.

(** Theorem 6 (GoForward preserves total).
    Symmetric to [total_preserved_by_back]. *)

Theorem total_preserved_by_forward : forall A (s : state A),
  total (step s GoForward) = total s.
Proof.
  exact goforward_total.
Qed.

(** Theorem 7 (Navigate then GoBack recovers position).
    After navigating to [x], going back lands on the item that was
    active before the navigation.  The past list is also fully
    restored.  This makes [Navigate] + [GoBack] a verified undo
    step for navigation actions. *)

Theorem navigate_back_recovers : forall A (s : state A) (x : A),
  present (step (step s (Navigate x)) GoBack) = present s /\
  past    (step (step s (Navigate x)) GoBack) = past s.
Proof.
  intros. simpl. split; reflexivity.
Qed.

(** Full induction: any sequence of [GoBack] / [GoForward] events
    preserves [total] from any starting state.
    This follows by induction on the event list, applying
    [goback_total] or [goforward_total] at each step.

    Note: [s] is quantified after [events] so that the induction
    hypothesis is generalised over all starting states, allowing it
    to be applied to [step s e] in the inductive case. *)

Theorem total_preserved_by_seq : forall A (events : list (event A))
  (s : state A),
  (forall e, In e events -> e = GoBack \/ e = GoForward) ->
  total (fold_left step events s) = total s.
Proof.
  intros A events.
  induction events as [| e es IH]; intros s Hbf; simpl.
  - (* Base: no events, total unchanged *)
    reflexivity.
  - (* Step: route through total (step s e) *)
    transitivity (total (step s e)).
    + (* Remaining events preserve total from (step s e) *)
      apply IH.
      intros e' He'. apply Hbf. right. exact He'.
    + (* Single step e = GoBack or GoForward preserves total *)
      destruct (Hbf e (or_introl eq_refl)) as [-> | ->].
      * apply goback_total.
      * apply goforward_total.
Qed.
