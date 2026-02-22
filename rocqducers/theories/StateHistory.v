From Stdlib Require Import List Arith.
From Rocqducers Require Import UndoTree.

(** * StateHistory — linear undo/redo backed by UndoTree

    The history state is a [UndoTree.cursor S]. The cursor's focus holds the
    current inner state (readable via [focus_value]). Navigation maps to
    undo/redo via the zipper structure:

      go_up   → undo  (climb to the CLink breadcrumb holding the previous value)
      go_link → redo  (descend to the Leaf holding the next value)

    Commits are *linear*: [sh_commit] on a [Link a t] node DISCARDS [t],
    clearing forward history. This gives standard editor-style undo semantics
    (as opposed to the branching [UndoTree.commit] which preserves all branches).

    Proved invariants:
      sh_commit_focus_leaf / sh_commit_focus_link :
        The new state is immediately the current focus.
      sh_commit_can_undo_leaf / sh_commit_can_undo_link :
        Every commit creates a reachable undo point.
      sh_commit_clears_redo_leaf / sh_commit_clears_redo_link :
        Committing always clears the redo stack (linear semantics).
      sh_undo_after_commit_leaf / sh_undo_after_commit_link :
        Undo after commit recovers the previous state exactly.
      sh_undo_redo_leaf / sh_undo_redo_link :
        Undo followed by redo is the identity. *)

(** * 1. Future-depth

    Count how many consecutive [Link] levels are stacked at the current focus.
    This equals the number of redo steps available. *)

Fixpoint focus_link_depth {A} (t : tree A) : nat :=
  match t with
  | Link _ child => S (focus_link_depth child)
  | _            => 0
  end.

Definition sh_future_depth {S} (hs : cursor S) : nat :=
  match hs with
  | At t _ => focus_link_depth t
  | Failed => 0
  end.

(** * 2. Linear commit

    [sh_commit new_state c] archives the current value and advances the cursor
    to a fresh [Leaf new_state].

    - [Leaf a]:   identical to [UndoTree.commit] — extends a linear chain.
    - [Link a _]: DISCARDS the existing child (clears the redo stack), giving
                  linear history semantics. The CLink breadcrumb still records
                  [a] so undo remains possible.
    - Otherwise:  [Failed]. *)

Definition sh_commit {S} (new_state : S) (c : cursor S) : cursor S :=
  match c with
  | At (Leaf a)   ctx => At (Leaf new_state) (CLink a ctx)
  | At (Link a _) ctx => At (Leaf new_state) (CLink a ctx)   (* discard future *)
  | _                 => Failed
  end.

(** * 3. Convenience aliases

    Thin wrappers over UndoTree inspection functions, named for the history
    domain so call sites are self-documenting. *)

Definition sh_can_undo {S} (hs : cursor S) : bool := can_go_up hs.
Definition sh_can_redo {S} (hs : cursor S) : bool := can_go_link hs.
Definition sh_init     {S} (s : S)         : cursor S := root_cursor (Leaf s).

(** * 4. Theorems *)

(** After committing on a Leaf, the new state is the current focus value. *)

Theorem sh_commit_focus_leaf :
  forall S (s new_s : S) (ctx : ctx S),
    focus_value (sh_commit new_s (At (Leaf s) ctx)) = Some new_s.
Proof.
  intros S s new_s ctx. simpl. reflexivity.
Qed.

(** After committing on a Link, the new state is the current focus value. *)

Theorem sh_commit_focus_link :
  forall S (s new_s : S) (t : tree S) (ctx : ctx S),
    focus_value (sh_commit new_s (At (Link s t) ctx)) = Some new_s.
Proof.
  intros S s new_s t ctx. simpl. reflexivity.
Qed.

(** Committing on a Leaf always creates a reachable undo point. *)

Theorem sh_commit_can_undo_leaf :
  forall S (s new_s : S) (ctx : ctx S),
    sh_can_undo (sh_commit new_s (At (Leaf s) ctx)) = true.
Proof.
  intros S s new_s ctx. simpl. reflexivity.
Qed.

(** Committing on a Link always creates a reachable undo point. *)

Theorem sh_commit_can_undo_link :
  forall S (s new_s : S) (t : tree S) (ctx : ctx S),
    sh_can_undo (sh_commit new_s (At (Link s t) ctx)) = true.
Proof.
  intros S s new_s t ctx. simpl. reflexivity.
Qed.

(** Committing on a Leaf always disables redo (linear semantics). *)

Theorem sh_commit_clears_redo_leaf :
  forall S (s new_s : S) (ctx : ctx S),
    sh_can_redo (sh_commit new_s (At (Leaf s) ctx)) = false.
Proof.
  intros S s new_s ctx. simpl. reflexivity.
Qed.

(** Committing on a Link always disables redo (the existing child is discarded). *)

Theorem sh_commit_clears_redo_link :
  forall S (s new_s : S) (t : tree S) (ctx : ctx S),
    sh_can_redo (sh_commit new_s (At (Link s t) ctx)) = false.
Proof.
  intros S s new_s t ctx. simpl. reflexivity.
Qed.

(** Undo after commit on a Leaf recovers the previous state exactly. *)

Theorem sh_undo_after_commit_leaf :
  forall S (s new_s : S) (ctx : ctx S),
    focus_value (go_up (sh_commit new_s (At (Leaf s) ctx))) = Some s.
Proof.
  intros S s new_s ctx. simpl. reflexivity.
Qed.

(** Undo after commit on a Link recovers the previous state exactly. *)

Theorem sh_undo_after_commit_link :
  forall S (s new_s : S) (t : tree S) (ctx : ctx S),
    focus_value (go_up (sh_commit new_s (At (Link s t) ctx))) = Some s.
Proof.
  intros S s new_s t ctx. simpl. reflexivity.
Qed.

(** Undo followed by redo is the identity (Leaf case).

    Proof: sh_commit new_s (At (Leaf s) ctx)
             = At (Leaf new_s) (CLink s ctx)
           go_up _ = At (Link s (Leaf new_s)) ctx
           go_link _ = At (Leaf new_s) (CLink s ctx) = original. *)

Theorem sh_undo_redo_leaf :
  forall S (s new_s : S) (ctx : ctx S),
    go_link (go_up (sh_commit new_s (At (Leaf s) ctx))) =
    sh_commit new_s (At (Leaf s) ctx).
Proof.
  intros S s new_s ctx. simpl. reflexivity.
Qed.

(** Undo followed by redo is the identity (Link case).

    Proof: sh_commit new_s (At (Link s t) ctx)
             = At (Leaf new_s) (CLink s ctx)          (child t is discarded)
           go_up _ = At (Link s (Leaf new_s)) ctx
           go_link _ = At (Leaf new_s) (CLink s ctx)  (independent of t). *)

Theorem sh_undo_redo_link :
  forall S (s new_s : S) (t : tree S) (ctx : ctx S),
    go_link (go_up (sh_commit new_s (At (Link s t) ctx))) =
    sh_commit new_s (At (Link s t) ctx).
Proof.
  intros S s new_s t ctx. simpl. reflexivity.
Qed.
