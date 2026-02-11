From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations.

(** * 1. Datastructures and arguments *)

Inductive phase_t :=
  | Idle
  | Loading (rid : nat)
  | Loaded
  | Errored.

Record state (D : Type) := mkState {
  phase : phase_t;
  cache : option D;
  next_id : nat;
  retries : nat;
  max_retries : nat;
}.

Arguments mkState {D}.
Arguments phase {D}.
Arguments cache {D}.
Arguments next_id {D}.
Arguments retries {D}.
Arguments max_retries {D}.

Inductive event (D : Type) :=
  | Fetch
  | GotResponse (rid : nat) (data : D)
  | GotError (rid : nat)
  | TimedOut (rid : nat)
  | DoRetry.

Arguments Fetch {D}.
Arguments GotResponse {D}.
Arguments GotError {D}.
Arguments TimedOut {D}.
Arguments DoRetry {D}.

(** * 2. Definitions and Fixpoints *)

(** Constructors for extraction *)

Definition mk_fetch {D} : event D := Fetch.
Definition mk_got_response {D} (rid : nat) (d : D) : event D := GotResponse rid d.
Definition mk_got_error {D} (rid : nat) : event D := GotError rid.
Definition mk_timed_out {D} (rid : nat) : event D := TimedOut rid.
Definition mk_do_retry {D} : event D := DoRetry.

(** Initial state *)

Definition init_state {D} (max_r : nat) : state D :=
  mkState Idle None 0 0 max_r.

(** Step function

    Pure reducer: [step : state D -> event D -> state D].
    Side effects (HTTP requests, timers) are handled externally.

    - [Fetch]: starts a new load unless already loading.
    - [GotResponse rid d]: accepts response only if [rid] matches.
    - [GotError rid]: transitions to error only if [rid] matches.
    - [TimedOut rid]: same as error, triggered by timeout.
    - [DoRetry]: retries from error if under max retries. *)

Definition step {D} (s : state D) (e : event D) : state D :=
  match e with
  | Fetch =>
    match phase s with
    | Loading _ => s
    | _ =>
      let rid := next_id s in
      mkState (Loading rid) (cache s) (S rid) 0 (max_retries s)
    end
  | GotResponse rid data =>
    match phase s with
    | Loading current_rid =>
      if Nat.eqb rid current_rid then
        mkState Loaded (Some data) (next_id s) 0 (max_retries s)
      else s
    | _ => s
    end
  | GotError rid =>
    match phase s with
    | Loading current_rid =>
      if Nat.eqb rid current_rid then
        mkState Errored (cache s) (next_id s) (retries s) (max_retries s)
      else s
    | _ => s
    end
  | TimedOut rid =>
    match phase s with
    | Loading current_rid =>
      if Nat.eqb rid current_rid then
        mkState Errored (cache s) (next_id s) (retries s) (max_retries s)
      else s
    | _ => s
    end
  | DoRetry =>
    match phase s with
    | Errored =>
      if Nat.ltb (retries s) (max_retries s) then
        let rid := next_id s in
        mkState (Loading rid) (cache s) (S rid) (S (retries s)) (max_retries s)
      else s
    | _ => s
    end
  end.

(** Phase inspection helpers *)

Definition is_idle (p : phase_t) : bool :=
  match p with Idle => true | _ => false end.

Definition is_loading (p : phase_t) : bool :=
  match p with Loading _ => true | _ => false end.

Definition loading_rid (p : phase_t) : option nat :=
  match p with Loading rid => Some rid | _ => None end.

Definition is_loaded (p : phase_t) : bool :=
  match p with Loaded => true | _ => false end.

Definition is_errored (p : phase_t) : bool :=
  match p with Errored => true | _ => false end.

(** Loaded invariant: if the phase is [Loaded], then [cache] holds
    data. Used by [loaded_inv_step] and [loaded_inv_init]. *)

Definition loaded_inv {D} (s : state D) : Prop :=
  phase s = Loaded -> exists d, cache s = Some d.

(** * 3. Lemmas *)

(** Base case for [loaded_inv_always]: the initial state is [Idle],
    so [phase s = Loaded] is false and the invariant holds vacuously. *)

Lemma loaded_inv_init : forall D (max_r : nat),
  @loaded_inv D (init_state max_r).
Proof.
  unfold loaded_inv, init_state.
  (* phase = Idle, goal becomes Idle = Loaded -> ... *)
  simpl. discriminate.
Qed.

(** * 4. Theorems *)

(** Invariant 1: loaded implies data present.
    The only transition that produces [Loaded] is [GotResponse]
    with a matching request id, which sets [cache := Some data].
    All other transitions either keep the state unchanged (so the
    invariant carries over from [Hinv]) or move to a non-[Loaded]
    phase (vacuously true).

    Proof strategy: unfold [loaded_inv], then for each event
    constructor, case-split on the current phase. Most branches
    produce a phase that cannot equal [Loaded] (discharged by
    [discriminate]). The [GotResponse] + [Loading] + matching rid
    branch is the only one that produces [Loaded], and it sets
    [cache := Some data]. Branches where the phase is already
    [Loaded] propagate the invariant via [Hinv]. *)

Theorem loaded_inv_step : forall D (s : state D) e,
  loaded_inv s -> loaded_inv (step s e).
Proof.
  unfold loaded_inv; intros D s e Hinv.
  (* For each event, case-split on phase. When the result is a fresh
     [mkState], [discriminate] suffices. When the state is unchanged,
     [congruence] derives the contradiction from [Hp] and the
     introduced hypothesis. *)
  destruct e as [| rid d | rid | rid |]; simpl.
  - (* Fetch: produces Loading or unchanged — never Loaded *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl; intro H.
    + (* Idle: result is mkState (Loading ..) .. *) discriminate H.
    + (* Loading crid: state unchanged *) congruence.
    + (* Loaded: result is mkState (Loading ..) .. *) discriminate H.
    + (* Errored: result is mkState (Loading ..) .. *) discriminate H.
  - (* GotResponse *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl.
    + (* Idle: state unchanged *) intro H; congruence.
    + (* Loading crid: check if rid matches *)
      destruct (Nat.eqb rid crid) eqn:Heq; simpl.
      * (* rid = crid: transition to Loaded with Some data *)
        intro. exists d. reflexivity.
      * (* rid <> crid: state unchanged *) intro H; congruence.
    + (* Loaded: state unchanged, invariant carries over *)
      intro; apply Hinv; reflexivity.
    + (* Errored: state unchanged *) intro H; congruence.
  - (* GotError *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl.
    + (* Idle: state unchanged *) intro H; congruence.
    + (* Loading crid *)
      destruct (Nat.eqb rid crid); simpl; intro H.
      * (* rid = crid: result is mkState Errored .. *) discriminate H.
      * (* rid <> crid: state unchanged *) congruence.
    + (* Loaded: invariant carries over *) intro; apply Hinv; reflexivity.
    + (* Errored: state unchanged *) intro H; congruence.
  - (* TimedOut: symmetric with GotError *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl.
    + (* Idle: state unchanged *) intro H; congruence.
    + (* Loading crid *)
      destruct (Nat.eqb rid crid); simpl; intro H.
      * (* rid = crid: result is mkState Errored .. *) discriminate H.
      * (* rid <> crid: state unchanged *) congruence.
    + (* Loaded: invariant carries over *) intro; apply Hinv; reflexivity.
    + (* Errored: state unchanged *) intro H; congruence.
  - (* DoRetry *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl.
    + (* Idle: state unchanged *) intro H; congruence.
    + (* Loading: state unchanged *) intro H; congruence.
    + (* Loaded: invariant carries over *) intro; apply Hinv; reflexivity.
    + (* Errored: retry may start Loading or stay Errored *)
      destruct (Nat.ltb (retries s) (max_retries s)); simpl; intro H.
      * (* retries < max: result is mkState (Loading ..) .. *) discriminate H.
      * (* retries >= max: state unchanged *) congruence.
Qed.

(** Invariant 2: error transitions preserve cache.
    Transitioning to [Errored] never fabricates or erases cached
    data. A first-load error has no data ([cache = None] from init),
    while an error after a successful load keeps the previously
    cached response.

    Proof strategy: for each event constructor, case-split on the
    current phase. If the resulting phase is [Errored], the new
    [cache] field is always copied from the old state unchanged. *)

Theorem error_preserves_cache : forall D (s : state D) e,
  phase (step s e) = Errored -> cache (step s e) = cache s.
Proof.
  intros D s e H.
  destruct e as [| rid d | rid | rid |]; simpl in *.
  - (* Fetch: produces Loading or unchanged — never Errored *)
    destruct (phase s) eqn:Hp; simpl in H; congruence.
  - (* GotResponse *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl in *.
    + (* Idle: state unchanged *) congruence.
    + (* Loading crid *)
      destruct (Nat.eqb rid crid); simpl in H.
      * (* rid = crid: transition to Loaded, not Errored *) congruence.
      * (* rid <> crid: state unchanged *) congruence.
    + (* Loaded: state unchanged *) congruence.
    + (* Errored: state unchanged *) reflexivity.
  - (* GotError *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl in *.
    + (* Idle *) congruence.
    + (* Loading crid *)
      destruct (Nat.eqb rid crid); simpl in *.
      * (* rid = crid: transition to Errored, cache preserved *) reflexivity.
      * (* rid <> crid: state unchanged *) congruence.
    + (* Loaded *) congruence.
    + (* Errored: state unchanged *) reflexivity.
  - (* TimedOut: symmetric with GotError *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl in *.
    + (* Idle *) congruence.
    + destruct (Nat.eqb rid crid); simpl in *.
      * (* rid = crid: transition to Errored, cache preserved *) reflexivity.
      * (* rid <> crid: state unchanged *) congruence.
    + (* Loaded *) congruence.
    + reflexivity.
  - (* DoRetry *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl in *.
    + (* Idle *) congruence.
    + (* Loading *) congruence.
    + (* Loaded *) congruence.
    + (* Errored *)
      destruct (Nat.ltb (retries s) (max_retries s)); simpl in H.
      * (* retries < max: transition to Loading, not Errored *) congruence.
      * (* retries >= max: state unchanged *) reflexivity.
Qed.

(** Invariant 3: stale events are ignored (race condition safety).
    When the state is [Loading crid], any response, error, or timeout
    carrying a different [rid] is silently dropped. This prevents
    out-of-order responses from corrupting the state.

    Proved by rewriting the phase, then showing that [Nat.eqb rid crid]
    is false (from [rid <> crid]), which takes the identity branch. *)

Theorem stale_response_ignored : forall D (s : state D) rid (d : D) crid,
  phase s = Loading crid ->
  rid <> crid ->
  step s (GotResponse rid d) = s.
Proof.
  intros D s rid d crid Hph Hne.
  simpl. rewrite Hph.
  destruct (Nat.eqb rid crid) eqn:Heq.
  - (* rid = crid: contradicts Hne *)
    apply Nat.eqb_eq in Heq. contradiction.
  - (* rid <> crid: state unchanged *)
    reflexivity.
Qed.

Theorem stale_error_ignored : forall D (s : state D) rid crid,
  phase s = Loading crid ->
  rid <> crid ->
  step s (GotError rid) = s.
Proof.
  intros D s rid crid Hph Hne.
  simpl. rewrite Hph.
  destruct (Nat.eqb rid crid) eqn:Heq.
  - (* rid = crid: contradicts Hne *)
    apply Nat.eqb_eq in Heq. contradiction.
  - (* rid <> crid: state unchanged *)
    reflexivity.
Qed.

Theorem stale_timeout_ignored : forall D (s : state D) rid crid,
  phase s = Loading crid ->
  rid <> crid ->
  step s (TimedOut rid) = s.
Proof.
  intros D s rid crid Hph Hne.
  simpl. rewrite Hph.
  destruct (Nat.eqb rid crid) eqn:Heq.
  - (* rid = crid: contradicts Hne *)
    apply Nat.eqb_eq in Heq. contradiction.
  - (* rid <> crid: state unchanged *)
    reflexivity.
Qed.

(** Invariant 4: retry preserves cache.
    [DoRetry] only changes [phase], [next_id], and [retries].
    The [cache] field is always copied unchanged regardless of
    the current phase or whether retries are exhausted. *)

Theorem retry_preserves_cache : forall D (s : state D),
  cache (step s DoRetry) = cache s.
Proof.
  intros D s. simpl.
  destruct (phase s).
  - (* Idle *) reflexivity.
  - (* Loading *) reflexivity.
  - (* Loaded *) reflexivity.
  - (* Errored *)
    destruct (Nat.ltb (retries s) (max_retries s)).
    + (* retries < max: starts Loading, cache unchanged *) reflexivity.
    + (* retries >= max: no-op *) reflexivity.
Qed.

(** Invariant 5: bounded retries (prevents infinite retry).
    Once the retry counter reaches [max_retries], [DoRetry] is a
    no-op. This guarantees termination of retry loops.

    Key step: [Nat.ltb (retries s) (max_retries s)] is false when
    [retries s >= max_retries s], taking the identity branch. *)

Theorem bounded_retries : forall D (s : state D),
  retries s >= max_retries s -> step s DoRetry = s.
Proof.
  intros D s Hge. simpl.
  destruct (phase s).
  - (* Idle *) reflexivity.
  - (* Loading *) reflexivity.
  - (* Loaded *) reflexivity.
  - (* Errored *)
    destruct (Nat.ltb (retries s) (max_retries s)) eqn:Hlt.
    + (* retries < max: contradicts Hge *)
      apply Nat.ltb_lt in Hlt. lia.
    + (* retries >= max: no-op *)
      reflexivity.
Qed.

(** Invariant 6: timeout resolves loading (prevents stuck spinner).
    A timeout event with the correct request id always transitions
    from [Loading] to [Errored], ensuring the UI is never stuck in
    a loading state indefinitely.

    Key step: [Nat.eqb rid rid] is always true ([Nat.eqb_refl]),
    so the matching branch is always taken. *)

Theorem timeout_resolves_loading : forall D (s : state D) rid,
  phase s = Loading rid -> phase (step s (TimedOut rid)) = Errored.
Proof.
  intros D s rid Hph.
  simpl. rewrite Hph.
  (* Nat.eqb rid rid = true by reflexivity *)
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** Full induction: for any sequence of events starting from
    [init_state], the loaded invariant holds. Combines the base
    case [loaded_inv_init] with the inductive step
    [loaded_inv_step]. *)

Theorem loaded_inv_always : forall D (max_r : nat) (events : list (event D)),
  loaded_inv (fold_left step events (init_state max_r)).
Proof.
  intros D max_r events.
  (* Generalize: any state satisfying loaded_inv preserves it *)
  cut (@loaded_inv D (init_state max_r) ->
       loaded_inv (fold_left step events (init_state max_r))).
  { intro H. apply H. apply loaded_inv_init. }
  generalize (@init_state D max_r) as s.
  induction events as [| e es IH]; intros s Hinv; simpl.
  - (* Base case: no events, invariant unchanged *)
    exact Hinv.
  - (* Inductive step: step preserves, then IH carries through *)
    apply IH. apply loaded_inv_step. exact Hinv.
Qed.
