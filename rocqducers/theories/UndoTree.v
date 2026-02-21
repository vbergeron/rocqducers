From Stdlib Require Import List Arith.

(** * 1. Data structures

    A tree with three constructors:
    - [Leaf a]: a terminal node holding value [a]
    - [Link a t]: a chain node with value [a] and single child [t]
    - [Node l r]: a binary node with left child [l] and right child [r] *)

Inductive tree (A : Type) : Type :=
  | Leaf : A -> tree A
  | Link : A -> tree A -> tree A
  | Node : tree A -> tree A -> tree A.

(** A zipper context records the path from the root to the current focus.
    Each constructor represents one step up the tree. *)

Inductive ctx (A : Type) : Type :=
  | Top    : ctx A
  | CLink  : A -> ctx A -> ctx A
  | CLeft  : ctx A -> tree A -> ctx A
  | CRight : tree A -> ctx A -> ctx A.

(** A cursor is either a valid position [At focus ctx] or a [Failed]
    navigation result. [Failed] acts as an absorbing element. *)

Inductive cursor (A : Type) : Type :=
  | At     : tree A -> ctx A -> cursor A
  | Failed : cursor A.

(** * 2. Navigation

    [cursor_flat_map] is the sequencing primitive: it applies a step
    function to a valid cursor and propagates [Failed] unchanged. *)

Definition cursor_flat_map {A} (c : cursor A) (f : tree A -> ctx A -> cursor A) : cursor A :=
  match c with
  | Failed       => Failed
  | At focus ctx => f focus ctx
  end.

Notation "c |> f" := (f c) (at level 51, left associativity).

Definition step_left {A} (focus : tree A) (ctx : ctx A) : cursor A :=
  match focus with
  | Node l r => At l (CLeft ctx r)
  | _        => Failed
  end.

Definition step_right {A} (focus : tree A) (ctx : ctx A) : cursor A :=
  match focus with
  | Node l r => At r (CRight l ctx)
  | _        => Failed
  end.

Definition step_link {A} (focus : tree A) (ctx : ctx A) : cursor A :=
  match focus with
  | Link a t => At t (CLink a ctx)
  | _        => Failed
  end.

Definition step_up {A} (focus : tree A) (ctx : ctx A) : cursor A :=
  match ctx with
  | Top           => Failed
  | CLink a ctx'  => At (Link a focus) ctx'
  | CLeft ctx' r  => At (Node focus r) ctx'
  | CRight l ctx' => At (Node l focus) ctx'
  end.

Definition go_left  {A} (c : cursor A) : cursor A := cursor_flat_map c step_left.
Definition go_right {A} (c : cursor A) : cursor A := cursor_flat_map c step_right.
Definition go_link  {A} (c : cursor A) : cursor A := cursor_flat_map c step_link.
Definition go_up    {A} (c : cursor A) : cursor A := cursor_flat_map c step_up.

(** * 3. Reconstruction

    [zip_up] rebuilds the full tree by folding the context over the focus.
    It is structurally recursive on [ctx], peeling off one crumb per step. *)

Fixpoint zip_up {A} (focus : tree A) (c : ctx A) : tree A :=
  match c with
  | Top           => focus
  | CLink a ctx'  => zip_up (Link a focus) ctx'
  | CLeft ctx' r  => zip_up (Node focus r) ctx'
  | CRight l ctx' => zip_up (Node l focus) ctx'
  end.

(** [reconstruct] returns the root of the tree the cursor is embedded in,
    or [None] if the cursor has [Failed]. *)

Definition reconstruct {A} (c : cursor A) : option (tree A) :=
  match c with
  | Failed        => None
  | At focus ctx  => Some (zip_up focus ctx)
  end.

Definition root_cursor {A} (t : tree A) : cursor A := At t Top.

(** * 4. Reducer

    Events drive cursor navigation. Each constructor corresponds to
    one of the four navigation primitives. *)

Inductive event : Type :=
  | EvGoLeft
  | EvGoRight
  | EvGoLink
  | EvGoUp.

Definition step {A} (c : cursor A) (e : event) : cursor A :=
  match e with
  | EvGoLeft  => go_left c
  | EvGoRight => go_right c
  | EvGoLink  => go_link c
  | EvGoUp    => go_up c
  end.

(** * 5. Inspection

    Boolean predicates and nat discriminants for cursor inspection,
    safe to call from the UI layer. *)

Definition is_failed {A} (c : cursor A) : bool :=
  match c with Failed => true | _ => false end.

Definition can_go_left {A} (c : cursor A) : bool :=
  match c with At (Node _ _) _ => true | _ => false end.

Definition can_go_right {A} (c : cursor A) : bool :=
  match c with At (Node _ _) _ => true | _ => false end.

Definition can_go_link {A} (c : cursor A) : bool :=
  match c with At (Link _ _) _ => true | _ => false end.

Definition can_go_up {A} (c : cursor A) : bool :=
  match c with
  | At _ Top => false
  | At _ _   => true
  | Failed   => false
  end.

(** Depth of a context = number of steps back to the root. *)

Fixpoint ctx_depth {A} (c : ctx A) : nat :=
  match c with
  | Top           => 0
  | CLink _ ctx'  => S (ctx_depth ctx')
  | CLeft ctx' _  => S (ctx_depth ctx')
  | CRight _ ctx' => S (ctx_depth ctx')
  end.

Definition cursor_depth {A} (c : cursor A) : nat :=
  match c with
  | Failed    => 0
  | At _ ctx  => ctx_depth ctx
  end.

(** Focus kind discriminant: 0 = Leaf, 1 = Link, 2 = Node, 3 = Failed. *)

Definition focus_kind {A} (c : cursor A) : nat :=
  match c with
  | At (Leaf _)   _ => 0
  | At (Link _ _) _ => 1
  | At (Node _ _) _ => 2
  | Failed          => 3
  end.

(** * 6. Theorems *)

(** Going left descends into the left subtree of a [Node];
    going up afterwards restores the original cursor exactly. *)

Theorem go_left_up :
  forall A (l r : tree A) (ctx : ctx A),
    go_up (go_left (At (Node l r) ctx)) = At (Node l r) ctx.
Proof.
  intros A l r ctx.
  unfold go_left, go_up.
  unfold cursor_flat_map.
  simpl step_left.
  simpl step_up.
  reflexivity.
Qed.

(** Going right descends into the right subtree of a [Node];
    going up afterwards restores the original cursor exactly. *)

Theorem go_right_up :
  forall A (l r : tree A) (ctx : ctx A),
    go_up (go_right (At (Node l r) ctx)) = At (Node l r) ctx.
Proof.
  intros A l r ctx.
  unfold go_right, go_up.
  unfold cursor_flat_map.
  simpl step_right.
  simpl step_up.
  reflexivity.
Qed.

(** Any navigation step on a [Failed] cursor stays [Failed]. *)

Theorem failed_absorbs :
  forall A (f : cursor A -> cursor A),
    f = go_left \/ f = go_right \/ f = go_link \/ f = go_up ->
    f (@Failed A) = @Failed A.
Proof.
  intros A f [Hl | [Hr | [Hk | Hu]]] ; subst ; reflexivity.
Qed.

(** [cursor_flat_map] with the identity continuation is the identity. *)

Theorem flat_map_right_id :
  forall A (c : cursor A),
    cursor_flat_map c (fun focus ctx => At focus ctx) = c.
Proof.
  intros A c. destruct c ; reflexivity.
Qed.

(** [cursor_flat_map] is associative. *)

Theorem flat_map_assoc :
  forall A (c : cursor A) (f g : tree A -> ctx A -> cursor A),
    cursor_flat_map (cursor_flat_map c f) g =
    cursor_flat_map c (fun focus ctx => cursor_flat_map (f focus ctx) g).
Proof.
  intros A c f g. destruct c ; reflexivity.
Qed.

(** The reconstructed tree is invariant under go_left + go_up round-trips:
    navigating into a [Node]'s left child and back does not change
    the underlying tree. *)

Theorem reconstruct_left_round_trip :
  forall A (l r : tree A) (ctx : ctx A),
    reconstruct (go_up (go_left (At (Node l r) ctx))) =
    reconstruct (At (Node l r) ctx).
Proof.
  intros A l r ctx.
  rewrite go_left_up.
  reflexivity.
Qed.

(** Same invariant for right child navigation. *)

Theorem reconstruct_right_round_trip :
  forall A (l r : tree A) (ctx : ctx A),
    reconstruct (go_up (go_right (At (Node l r) ctx))) =
    reconstruct (At (Node l r) ctx).
Proof.
  intros A l r ctx.
  rewrite go_right_up.
  reflexivity.
Qed.

(** Any step from a [Failed] cursor stays [Failed]. *)

Theorem failed_step :
  forall A (e : event),
    @step A Failed e = Failed.
Proof.
  intros A e. destruct e ; reflexivity.
Qed.
