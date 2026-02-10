From Stdlib Require Import List Arith Lia.
Import ListNotations.

(** * Helpers *)

(** Local [nth] to avoid extracting Stdlib.List *)
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

Lemma nth_Some_lt : forall A (l : list A) i x,
  nth l i = Some x -> i < length l.
Proof.
  intros A l. induction l as [| h t IH]; intros i x H.
  - destruct i; discriminate.
  - destruct i as [| i']; simpl in *.
    + lia.
    + apply IH in H. lia.
Qed.

Lemma remove_at_length : forall A (i : nat) (l : list A),
  i < length l -> length (remove_at i l) = length l - 1.
Proof.
  intros A i l. revert i.
  induction l as [| h t IH]; intros i Hi.
  - simpl in Hi. lia.
  - destruct i as [| i'].
    + simpl. lia.
    + simpl. simpl in Hi.
      rewrite IH by lia. lia.
Qed.

(** * State and events *)

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

(** Constructors for extraction *)
Definition mk_do_pick (i : nat) : event := DoPick i.
Definition mk_do_unpick (i : nat) : event := DoUnpick i.

(** * Reducer operations *)

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

(** * Initial state *)

Definition init_state {A} (default : A) (rest : list A) : state A :=
  mkState [default] rest.

(* ================================================================= *)
(** * Invariant 1: picked list stays non-empty                        *)
(*                                                                     *)
(*  We prove:  picked s <> []  ->  picked (reducer s e) <> []          *)
(*                                                                     *)
(*  Strategy: split by event constructor, then prove each operation    *)
(*  (do_pick / do_unpick) preserves non-emptiness separately.          *)
(* ================================================================= *)

(** ** [do_pick] preserves non-emptiness

    Picking from suggestions either adds an element to [picked]
    (making it [x :: picked s], trivially non-empty) or is a no-op
    when the index is out of bounds (state unchanged). *)

Lemma do_pick_nonempty : forall A (s : state A) i,
  picked s <> [] -> picked (do_pick s i) <> [].
Proof.
  intros A s i Hne.
  (** Goal:
        Hne : picked s <> []
        ============================
        picked (do_pick s i) <> []                                    *)
  unfold do_pick.
  (** Unfolding exposes the [match nth ...] branch:
        ============================
        picked
          match nth (suggestions s) i with
          | Some x => {| picked := x :: picked s; ... |}
          | None   => s
          end
        <> []                                                         *)
  destruct (nth (suggestions s) i); simpl.
  (** Case [Some a]: the picked field becomes [a :: picked s].
        ============================
        a :: picked s <> []                                           *)
  - discriminate.  (* a cons is never nil *)
  (** Case [None]: state is unchanged, goal is [picked s <> []].
        ============================
        picked s <> []                                                *)
  - exact Hne.
Qed.

(** ** Helper: [remove_at] on a list of length >= 2 is never empty

    Used in the [do_unpick] proof when we know [picked s] has the
    shape [a :: b :: t] (at least two elements). *)

Lemma remove_at_cons_nonempty : forall A (a b : A) (t : list A) i,
  remove_at i (a :: b :: t) <> [].
Proof.
  intros A a b t i.
  (** Goal:
        ============================
        remove_at i (a :: b :: t) <> []                               *)
  destruct i as [| i']; simpl.
  (** Case [i = 0]: [remove_at 0 (a :: b :: t) = b :: t].
        ============================
        b :: t <> []                                                  *)
  - discriminate.
  (** Case [i = S i']: [remove_at (S i') (a :: b :: t) = a :: ...].
        ============================
        a :: remove_at i' (b :: t) <> []                              *)
  - discriminate.
Qed.

(** ** [do_unpick] preserves non-emptiness

    Three cases on the shape of [picked s]:
    - []        : impossible by hypothesis (contradiction)
    - [a]       : single element, unpick is blocked (no-op)
    - a::b::t   : >= 2 elements, unpick may proceed
      - valid index   : result is [remove_at i (a::b::t)], non-empty
                        by [remove_at_cons_nonempty]
      - invalid index : no-op, state unchanged                       *)

Lemma do_unpick_nonempty : forall A (s : state A) i,
  picked s <> [] -> picked (do_unpick s i) <> [].
Proof.
  intros A s i Hne.
  (** Goal:
        Hne : picked s <> []
        ============================
        picked (do_unpick s i) <> []                                  *)
  unfold do_unpick.
  (** Unfolding exposes a nested match on [picked s]:
        ============================
        picked
          match picked s with
          | _ :: _ :: _ =>
              match nth (picked s) i with
              | Some x => {| picked := remove_at ...; ... |}
              | None   => s
              end
          | _ => s
          end
        <> []                                                         *)
  destruct (picked s) as [| a [| b t]] eqn:Hp.

  (** ---- Case 1: [picked s = []] ---- *)
  (** Context:
        Hp  : picked s = []
        Hne : [] <> []          (after destruct rewrote Hne)
        ============================
        picked s <> []

      This case is contradictory: [Hne] states [[] <> []] which
      is absurd. [congruence] finds the contradiction.               *)
  - simpl. congruence.

  (** ---- Case 2: [picked s = [a]] ---- *)
  (** Context:
        Hp  : picked s = [a]
        Hne : [a] <> []
        ============================
        picked s <> []

      The outer match falls into the [_ => s] default branch
      (single element), so the state is unchanged. We must show
      [picked s <> []], which follows from [Hp] and [Hne].           *)
  - simpl. congruence.

  (** ---- Case 3: [picked s = a :: b :: t] ---- *)
  (** Context:
        Hp  : picked s = a :: b :: t
        Hne : a :: b :: t <> []
        ============================
        picked
          match nth (a :: b :: t) i with
          | Some x => {| picked := remove_at i (a :: b :: t); ... |}
          | None   => s
          end
        <> []

      The outer match entered the [_ :: _ :: _] branch. Now we
      case-split on the inner [nth] lookup.                          *)
  - destruct (nth (a :: b :: t) i) eqn:Hn.

    (** ---- Case 3a: [nth ... = Some a0] (valid index) ---- *)
    (** Context:
          Hn : nth (a :: b :: t) i = Some a0
          ============================
          remove_at i (a :: b :: t) <> []

        The picked field is [remove_at i (a :: b :: t)]. Since
        the input has >= 2 elements, the result is never empty.      *)
    + simpl. apply remove_at_cons_nonempty.

    (** ---- Case 3b: [nth ... = None] (invalid index) ---- *)
    (** Context:
          Hn : nth (a :: b :: t) i = None
          ============================
          picked s <> []

        Index out of bounds: state unchanged. Follows from [Hp].     *)
    + simpl. congruence.
Qed.

(** ** Main theorem: the reducer preserves picked non-emptiness

    Dispatches on the event constructor, delegating to the two
    operation-specific lemmas proved above.                           *)

Theorem picked_nonempty : forall A (s : state A) e,
  picked s <> [] -> picked (reducer s e) <> [].
Proof.
  intros A s e Hne.
  (** Goal:
        Hne : picked s <> []
        ============================
        picked (reducer s e) <> []                                    *)
  destruct e; simpl.
  (** Case [DoPick n]:
        ============================
        picked (do_pick s n) <> []                                    *)
  - apply do_pick_nonempty; exact Hne.
  (** Case [DoUnpick n]:
        ============================
        picked (do_unpick s n) <> []                                  *)
  - apply do_unpick_nonempty; exact Hne.
Qed.

(* ================================================================= *)
(** * Invariant 2: total count is preserved                            *)
(* ================================================================= *)

Lemma do_pick_total : forall A (s : state A) i,
  length (picked (do_pick s i)) + length (suggestions (do_pick s i)) =
  length (picked s) + length (suggestions s).
Proof.
  intros A s i.
  unfold do_pick.
  destruct (nth (suggestions s) i) eqn:Hn.
  - simpl.
    apply nth_Some_lt in Hn.
    rewrite remove_at_length by exact Hn.
    lia.
  - reflexivity.
Qed.

Lemma do_unpick_total : forall A (s : state A) i,
  length (picked (do_unpick s i)) + length (suggestions (do_unpick s i)) =
  length (picked s) + length (suggestions s).
Proof.
  intros A s i.
  unfold do_unpick.
  destruct (picked s) as [| a [| b t]] eqn:Hp.
  - simpl. rewrite Hp. reflexivity.
  - simpl. rewrite Hp. reflexivity.
  - destruct (nth (a :: b :: t) i) eqn:Hn.
    + apply nth_Some_lt in Hn.
      simpl picked. simpl suggestions.
      rewrite remove_at_length by exact Hn.
      simpl. lia.
    + simpl. rewrite Hp. reflexivity.
Qed.

Theorem total_preserved : forall A (s : state A) e,
  length (picked (reducer s e)) + length (suggestions (reducer s e)) =
  length (picked s) + length (suggestions s).
Proof.
  intros A s e.
  destruct e; simpl.
  - apply do_pick_total.
  - apply do_unpick_total.
Qed.

(** * Init state satisfies invariants *)

Lemma init_picked_nonempty : forall A (d : A) rest,
  picked (init_state d rest) <> [].
Proof.
  intros. simpl. discriminate.
Qed.
