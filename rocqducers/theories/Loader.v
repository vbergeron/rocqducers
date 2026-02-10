From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations.

(** * Types *)

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

(** Constructors for extraction *)

Definition mk_fetch {D} : event D := Fetch.
Definition mk_got_response {D} (rid : nat) (d : D) : event D := GotResponse rid d.
Definition mk_got_error {D} (rid : nat) : event D := GotError rid.
Definition mk_timed_out {D} (rid : nat) : event D := TimedOut rid.
Definition mk_do_retry {D} : event D := DoRetry.

(** * Initial state *)

Definition init_state {D} (max_r : nat) : state D :=
  mkState Idle None 0 0 max_r.

(** * Step function

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

(** * Phase inspection helpers *)

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

(* ================================================================= *)
(** * Property 1: Loaded state always has data in cache               *)
(*                                                                     *)
(*  Invariant: if the phase is [Loaded], then [cache] holds data.     *)
(*  Proved inductively: init satisfies it, and step preserves it.     *)
(* ================================================================= *)

Definition loaded_inv {D} (s : state D) : Prop :=
  phase s = Loaded -> exists d, cache s = Some d.

(** The initial state is [Idle], so the invariant holds vacuously. *)

Lemma loaded_inv_init : forall D (max_r : nat),
  @loaded_inv D (init_state max_r).
Proof.
  unfold loaded_inv, init_state. simpl. discriminate.
Qed.

(** Each step preserves the invariant.

    The only transition that produces [Loaded] is [GotResponse]
    with a matching request id, which sets [cache := Some data].
    All other transitions either keep the state unchanged (so the
    invariant carries over from [Hinv]) or move to a non-[Loaded]
    phase (vacuously true). *)

Theorem loaded_inv_step : forall D (s : state D) e,
  loaded_inv s -> loaded_inv (step s e).
Proof.
  unfold loaded_inv; intros D s e Hinv.
  destruct e as [| rid d | rid | rid |]; simpl;
    destruct (phase s); simpl;
    try (intro; congruence);
    try (destruct (Nat.eqb _ _); simpl; try (intro; congruence));
    try (destruct (Nat.ltb _ _); simpl; try (intro; congruence));
    try exact Hinv.
  (* GotResponse with matching rid: cache = Some d *)
  intro. exists d. reflexivity.
Qed.

(* ================================================================= *)
(** * Property 2: Error transitions preserve cache                    *)
(*                                                                     *)
(*  Transitioning to [Errored] never fabricates or erases cached      *)
(*  data. Combined with [init_state] having [cache = None], this      *)
(*  ensures a first-load error has no data, while an error after a    *)
(*  successful load keeps the previously cached response.             *)
(* ================================================================= *)

Theorem error_preserves_cache : forall D (s : state D) e,
  phase (step s e) = Errored -> cache (step s e) = cache s.
Proof.
  intros D s e H.
  destruct e as [| rid d | rid | rid |]; simpl in *;
    destruct (phase s); simpl in *; try congruence;
    try (destruct (Nat.eqb _ _); simpl in *; congruence);
    try (destruct (Nat.ltb _ _); simpl in *; congruence).
Qed.

(* ================================================================= *)
(** * Property 3: Stale events are ignored (race condition safety)    *)
(*                                                                     *)
(*  When the state is [Loading crid], any response, error, or timeout *)
(*  carrying a different [rid] is silently dropped. This prevents     *)
(*  out-of-order responses from corrupting the state.                 *)
(* ================================================================= *)

Theorem stale_response_ignored : forall D (s : state D) rid (d : D) crid,
  phase s = Loading crid ->
  rid <> crid ->
  step s (GotResponse rid d) = s.
Proof.
  intros D s rid d crid Hph Hne.
  simpl. rewrite Hph.
  destruct (Nat.eqb rid crid) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Theorem stale_error_ignored : forall D (s : state D) rid crid,
  phase s = Loading crid ->
  rid <> crid ->
  step s (GotError rid) = s.
Proof.
  intros D s rid crid Hph Hne.
  simpl. rewrite Hph.
  destruct (Nat.eqb rid crid) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Theorem stale_timeout_ignored : forall D (s : state D) rid crid,
  phase s = Loading crid ->
  rid <> crid ->
  step s (TimedOut rid) = s.
Proof.
  intros D s rid crid Hph Hne.
  simpl. rewrite Hph.
  destruct (Nat.eqb rid crid) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

(* ================================================================= *)
(** * Property 4: Retry preserves cache                               *)
(*                                                                     *)
(*  Retrying never erases a previously cached valid response.         *)
(* ================================================================= *)

Theorem retry_preserves_cache : forall D (s : state D),
  cache (step s DoRetry) = cache s.
Proof.
  intros D s. simpl.
  destruct (phase s); try reflexivity.
  destruct (Nat.ltb (retries s) (max_retries s)); reflexivity.
Qed.

(* ================================================================= *)
(** * Property 5: Bounded retries (prevents infinite retry)           *)
(*                                                                     *)
(*  Once the retry counter reaches [max_retries], [DoRetry] is a     *)
(*  no-op. This guarantees termination of retry loops.                *)
(* ================================================================= *)

Theorem bounded_retries : forall D (s : state D),
  retries s >= max_retries s -> step s DoRetry = s.
Proof.
  intros D s Hge. simpl.
  destruct (phase s); try reflexivity.
  destruct (Nat.ltb (retries s) (max_retries s)) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt. lia.
  - reflexivity.
Qed.

(* ================================================================= *)
(** * Property 6: Timeout resolves loading (prevents stuck spinner)   *)
(*                                                                     *)
(*  A timeout event with the correct request id always transitions    *)
(*  from [Loading] to [Errored], ensuring the UI is never stuck in   *)
(*  a loading state indefinitely.                                     *)
(* ================================================================= *)

Theorem timeout_resolves_loading : forall D (s : state D) rid,
  phase s = Loading rid -> phase (step s (TimedOut rid)) = Errored.
Proof.
  intros D s rid Hph. simpl. rewrite Hph.
  rewrite Nat.eqb_refl. reflexivity.
Qed.
