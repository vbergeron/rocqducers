From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations.

(** * 1. Data structures and arguments

    Token-based (cursor) pagination: the server returns an opaque
    [next_tok] with each page.  Navigation uses that token, not
    a page number.  The [back_stack] records which token to pass
    on each backward step, enabling full bidirectional navigation
    without knowing the total page count. *)

Inductive phase_t :=
  | Idle
  | Loading (rid : nat)
  | Loaded
  | Errored.

(** [cur_tok] tracks the token that was used to fetch the current
    page.  While [Loading], it holds the pending token (the one
    being passed to the API), so the React hook can read it to
    start the request.  When [Loaded], it is the token that was
    used, and it is pushed onto [back_stack] when [Next] fires. *)

Record state (D : Type) := mkState {
  phase      : phase_t;
  data       : option D;
  next_tok   : option nat;        (** None = last page (server said so) *)
  cur_tok    : option nat;        (** pending token (Loading) / current page token (Loaded) *)
  back_stack : list (option nat); (** tokens for backward navigation, most-recent first *)
  next_rid   : nat;               (** monotone request-id counter *)
}.

Arguments mkState    {D}.
Arguments phase      {D}.
Arguments data       {D}.
Arguments next_tok   {D}.
Arguments cur_tok    {D}.
Arguments back_stack {D}.
Arguments next_rid   {D}.

Inductive event (D : Type) :=
  | Fetch                                                    (** reload from page 1 *)
  | Next                                                     (** advance one page *)
  | Prev                                                     (** go back one page *)
  | GotResponse (rid : nat) (d : D) (nxt : option nat)      (** server reply *)
  | GotError    (rid : nat).                                 (** fetch failed *)

Arguments Fetch       {D}.
Arguments Next        {D}.
Arguments Prev        {D}.
Arguments GotResponse {D}.
Arguments GotError    {D}.

(** * 2. Definitions *)

(** Constructor helpers — exported for JS event dispatch *)
Definition mk_fetch        {D} : event D := Fetch.
Definition mk_next         {D} : event D := Next.
Definition mk_prev         {D} : event D := Prev.
Definition mk_got_response {D} (rid : nat) (d : D) (nxt : option nat) : event D :=
  GotResponse rid d nxt.
Definition mk_got_error    {D} (rid : nat) : event D := GotError rid.

(** Initial state: Idle, no data, empty navigation *)
Definition init_state {D} : state D :=
  mkState Idle None None None [] 0.

(** Step function — pure reducer.  Side effects (HTTP, timers) live
    in the React hook.

    Key invariant on [cur_tok]:
    - When [Fetch] or [Next] or [Prev] starts a load, [cur_tok] is
      set to the token being requested.  The hook reads it to start
      the fetch.
    - When [GotResponse] arrives, [cur_tok] is unchanged; it now
      records which token fetched the current page.
    - [back_stack] is extended by [Next] and popped by [Prev];
      [Fetch] resets it to [[]]. *)

Definition step {D} (s : state D) (e : event D) : state D :=
  match e with

  | Fetch =>
    (** Reload from page 1.  Resets navigation.  No-op while loading. *)
    match phase s with
    | Loading _ => s
    | _ =>
      let rid := next_rid s in
      mkState (Loading rid) (data s) None None [] (S rid)
    end

  | Next =>
    (** Advance one page.  No-op unless Loaded with a next token. *)
    match phase s with
    | Loaded =>
      match next_tok s with
      | None => s                          (* last page *)
      | Some _ =>
        let rid := next_rid s in
        mkState (Loading rid) (data s) (next_tok s) (next_tok s)
                (cur_tok s :: back_stack s) (S rid)
      end
    | _ => s
    end

  | Prev =>
    (** Go back one page.  No-op unless Loaded with history. *)
    match phase s with
    | Loaded =>
      match back_stack s with
      | [] => s                            (* already at first page *)
      | t :: rest =>
        let rid := next_rid s in
        mkState (Loading rid) (data s) (next_tok s) t rest (S rid)
      end
    | _ => s
    end

  | GotResponse rid d nxt =>
    (** Accept response only when rid matches the pending request. *)
    match phase s with
    | Loading crid =>
      if Nat.eqb rid crid then
        mkState Loaded (Some d) nxt (cur_tok s) (back_stack s) (next_rid s)
      else s
    | _ => s
    end

  | GotError rid =>
    (** Stale errors are silently ignored. *)
    match phase s with
    | Loading crid =>
      if Nat.eqb rid crid then
        mkState Errored (data s) (next_tok s) (cur_tok s) (back_stack s) (next_rid s)
      else s
    | _ => s
    end

  end.

(** Phase inspection helpers *)

Definition is_idle     (p : phase_t) : bool :=
  match p with Idle      => true | _ => false end.
Definition is_loading  (p : phase_t) : bool :=
  match p with Loading _ => true | _ => false end.
Definition loading_rid (p : phase_t) : option nat :=
  match p with Loading rid => Some rid | _ => None end.
Definition is_loaded   (p : phase_t) : bool :=
  match p with Loaded    => true | _ => false end.
Definition is_errored  (p : phase_t) : bool :=
  match p with Errored   => true | _ => false end.

(** Navigation guards: used by the view to enable/disable buttons *)

Definition has_next {D} (s : state D) : bool :=
  match phase s, next_tok s with
  | Loaded, Some _ => true
  | _,      _      => false
  end.

Definition can_go_back {D} (s : state D) : bool :=
  match phase s, back_stack s with
  | Loaded, _ :: _ => true
  | _,      _      => false
  end.

(** Loaded invariant: when phase is [Loaded], [data] is always [Some d].
    This is the core safety property — the UI can unconditionally
    dereference [data] when the phase is [Loaded]. *)

Definition loaded_inv {D} (s : state D) : Prop :=
  phase s = Loaded -> exists d, data s = Some d.

(** * 3. Lemmas *)

(** Base case: [init_state] is [Idle], so [loaded_inv] holds vacuously. *)

Lemma loaded_inv_init : forall D, @loaded_inv D init_state.
Proof.
  unfold loaded_inv, init_state. simpl. discriminate.
Qed.

(** * 4. Theorems *)

(** Invariant 1 (I1) — Loaded implies data present.

    The only transition that produces [Loaded] is [GotResponse] with
    a matching rid, which simultaneously sets [data := Some d].
    Every other event either leaves the phase non-[Loaded] (so the
    conclusion is vacuous) or leaves the state unchanged (so the
    existing [Hinv] carries over).

    Proof: unfold [loaded_inv], then for each event case-split on
    [phase s].  The [GotResponse]/[Loading]/matching-rid branch is
    the single path to [Loaded]; all others are discharged by
    [discriminate] or [congruence]. *)

Theorem loaded_inv_step : forall D (s : state D) (e : event D),
  loaded_inv s -> loaded_inv (step s e).
Proof.
  unfold loaded_inv; intros D s e Hinv.
  destruct e as [ | | | rid d nxt | rid]; simpl.

  - (* Fetch: never produces Loaded (always goes to Loading or stays unchanged) *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl; intro H.
    + discriminate H.
    + congruence.
    + discriminate H.
    + discriminate H.

  - (* Next: either no-op or transitions to Loading — never Loaded *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl; intro H.
    + congruence.
    + congruence.
    + (* Loaded: check next_tok *)
      destruct (next_tok s) as [| t] eqn:Hnt; simpl; intro Hl.
      * apply Hinv. exact Hl.
      * discriminate Hl.
    + congruence.

  - (* Prev: either no-op or transitions to Loading — never Loaded *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl; intro H.
    + congruence.
    + congruence.
    + (* Loaded: check back_stack *)
      destruct (back_stack s) as [| t rest] eqn:Hbs; simpl; intro Hl.
      * apply Hinv. exact Hl.
      * discriminate Hl.
    + congruence.

  - (* GotResponse *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl.
    + intro H; congruence.
    + (* Loading crid: check if rid matches *)
      destruct (Nat.eqb rid crid) eqn:Heq; simpl.
      * (* rid = crid: transitions to Loaded with Some d *)
        intro. exists d. reflexivity.
      * (* rid ≠ crid: state unchanged *)
        intro H; congruence.
    + (* Loaded: state unchanged, invariant carries over *)
      intro H; apply Hinv; exact H.
    + intro H; congruence.

  - (* GotError: never produces Loaded *)
    destruct (phase s) as [| crid | |] eqn:Hp; simpl.
    + intro H; congruence.
    + destruct (Nat.eqb rid crid) eqn:Heq; simpl; intro H.
      * discriminate H.
      * congruence.
    + intro H; apply Hinv; exact H.
    + intro H; congruence.
Qed.

(** Invariant 2 (I3) — [Next] is a no-op on the last page.
    When [next_tok = None], the server indicated there are no more
    pages.  The reducer must be structurally inert. *)

Theorem no_next_noop : forall D (s : state D),
  phase s = Loaded ->
  next_tok s = None ->
  step s Next = s.
Proof.
  intros D s Hp Hn.
  simpl. rewrite Hp. rewrite Hn. reflexivity.
Qed.

(** Invariant 3 (I4) — [Next] is a no-op while loading.
    Prevents stacking concurrent requests. *)

Theorem loading_next_noop : forall D (s : state D) rid,
  phase s = Loading rid ->
  step s Next = s.
Proof.
  intros D s rid Hp.
  simpl. rewrite Hp. reflexivity.
Qed.

(** Invariant 4 (I5) — [Prev] is a no-op when already at the first page.
    An empty [back_stack] means there is nowhere to go back to. *)

Theorem empty_stack_prev_noop : forall D (s : state D),
  phase s = Loaded ->
  back_stack s = [] ->
  step s Prev = s.
Proof.
  intros D s Hp Hbs.
  simpl. rewrite Hp. rewrite Hbs. reflexivity.
Qed.

(** Invariant 5 (I2) — Stale responses are ignored (race-condition safety).
    A [GotResponse] with [rid ≠ crid] is silently dropped.  This
    prevents out-of-order responses from corrupting the state after
    a [Fetch] or navigation event overtakes a slow request. *)

Theorem stale_response_ignored :
  forall D (s : state D) rid (d : D) (nxt : option nat) crid,
  phase s = Loading crid ->
  rid <> crid ->
  step s (GotResponse rid d nxt) = s.
Proof.
  intros D s rid d nxt crid Hph Hne.
  simpl. rewrite Hph.
  destruct (Nat.eqb rid crid) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

(** Invariant 6 (I2 variant) — Stale errors are ignored. *)

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

(** Invariant 7 — [GotError] preserves [back_stack].
    A failed fetch must not silently corrupt navigation history.
    Without this, a retry after an error could start from a wrong
    position in the page sequence. *)

Theorem error_preserves_back_stack : forall D (s : state D) rid,
  phase (step s (GotError rid)) = Errored ->
  back_stack (step s (GotError rid)) = back_stack s.
Proof.
  intros D s rid H.
  simpl in *.
  destruct (phase s) as [| crid | |] eqn:Hp; simpl in *.
  - congruence.
  - destruct (Nat.eqb rid crid) eqn:Heq; simpl in *.
    + (* rid = crid: mkState Errored ... (back_stack s) ... *)
      reflexivity.
    + (* rid ≠ crid: state unchanged, but then phase = Loading, not Errored *)
      congruence.
  - congruence.
  - (* Errored: state unchanged *)
    reflexivity.
Qed.

(** Invariant 8a (I8 local) — [Prev] pops exactly the top of the stack.
    The token at the head of [back_stack] is consumed and the rest
    becomes the new [back_stack]. *)

Theorem prev_pops_back_stack : forall D (s : state D) t rest,
  phase s = Loaded ->
  back_stack s = t :: rest ->
  back_stack (step s Prev) = rest.
Proof.
  intros D s t rest Hp Hbs.
  simpl. rewrite Hp. rewrite Hbs. reflexivity.
Qed.

(** Invariant 8b (I6 local) — [Next] extends the stack by one.
    Pressing Next pushes [cur_tok] (the current page's fetch token)
    onto [back_stack], so a subsequent [Prev] can undo the navigation. *)

Theorem next_grows_stack : forall D (s : state D) t,
  phase s = Loaded ->
  next_tok s = Some t ->
  length (back_stack (step s Next)) = S (length (back_stack s)).
Proof.
  intros D s t Hp Hnt.
  simpl. rewrite Hp. rewrite Hnt. simpl.
  reflexivity.
Qed.

(** Invariant 9 — [Fetch] is a hard reset of all navigation state.
    Calling [Fetch] from any non-loading phase clears [back_stack]
    and [next_tok], ensuring navigation starts from a clean slate. *)

Theorem fetch_clears_navigation : forall D (s : state D),
  (forall rid, phase s <> Loading rid) ->
  back_stack (step s Fetch) = [] /\ next_tok (step s Fetch) = None.
Proof.
  intros D s Hnl.
  simpl.
  destruct (phase s) as [| rid | |] eqn:Hp.
  - (* Idle *) split; reflexivity.
  - (* Loading rid: contradicts Hnl *)
    exfalso. exact (Hnl rid Hp).
  - (* Loaded *) split; reflexivity.
  - (* Errored *) split; reflexivity.
Qed.

(** Full induction — [loaded_inv] holds for any event sequence
    starting from [init_state].  Combines [loaded_inv_init] (base)
    with [loaded_inv_step] (inductive step) via [fold_left]. *)

Theorem loaded_inv_always : forall D (events : list (event D)),
  loaded_inv (fold_left step events (@init_state D)).
Proof.
  intros D events.
  cut (@loaded_inv D init_state ->
       loaded_inv (fold_left step events init_state)).
  { intro H. apply H. apply loaded_inv_init. }
  generalize (@init_state D) as s.
  induction events as [| e es IH]; intros s Hinv; simpl.
  - exact Hinv.
  - apply IH. apply loaded_inv_step. exact Hinv.
Qed.
