From Stdlib Require Import List Arith.

Section UndoTree.

Context {St E : Type}.
Variable inner : St -> E -> St.

(** * 1. Data structures

    A tree with three constructors:
    - [Leaf s]: a terminal node holding state [s]
    - [Link s t]: a chain node with state [s] and single child [t]
    - [Node l r]: a binary node with left child [l] and right child [r] *)

Inductive tree : Type :=
  | Leaf : St -> tree
  | Link : St -> tree -> tree
  | Node : tree -> tree -> tree.

(** A zipper context records the path from the root to the current focus.
    Each constructor represents one step up the tree. *)

Inductive ctx : Type :=
  | Top    : ctx
  | CLink  : St -> ctx -> ctx
  | CLeft  : ctx -> tree -> ctx
  | CRight : tree -> ctx -> ctx.

(** A cursor is either a valid position [At focus k] or a [Failed]
    navigation result. [Failed] acts as an absorbing element. *)

Inductive cursor : Type :=
  | At     : tree -> ctx -> cursor
  | Failed : cursor.

(** * 2. Navigation

    [cursor_flat_map] is the sequencing primitive: it applies a step
    function to a valid cursor and propagates [Failed] unchanged. *)

Definition cursor_flat_map (c : cursor) (f : tree -> ctx -> cursor) : cursor :=
  match c with
  | Failed     => Failed
  | At focus k => f focus k
  end.

Notation "c |> f" := (f c) (at level 51, left associativity).

Definition step_left (focus : tree) (k : ctx) : cursor :=
  match focus with
  | Node l r => At l (CLeft k r)
  | _        => Failed
  end.

Definition step_right (focus : tree) (k : ctx) : cursor :=
  match focus with
  | Node l r => At r (CRight l k)
  | _        => Failed
  end.

Definition step_link (focus : tree) (k : ctx) : cursor :=
  match focus with
  | Link s t => At t (CLink s k)
  | _        => Failed
  end.

Definition step_up (focus : tree) (k : ctx) : cursor :=
  match k with
  | Top          => Failed
  | CLink s k'   => At (Link s focus) k'
  | CLeft k' r   => At (Node focus r) k'
  | CRight l k'  => At (Node l focus) k'
  end.

Definition go_left  (c : cursor) : cursor := cursor_flat_map c step_left.
Definition go_right (c : cursor) : cursor := cursor_flat_map c step_right.
Definition go_link  (c : cursor) : cursor := cursor_flat_map c step_link.
Definition go_up    (c : cursor) : cursor := cursor_flat_map c step_up.

(** * 3. Reconstruction

    [zip_up] rebuilds the full tree by folding the context over the focus.
    It is structurally recursive on [ctx], peeling off one crumb per step. *)

Fixpoint zip_up (focus : tree) (k : ctx) : tree :=
  match k with
  | Top          => focus
  | CLink s k'   => zip_up (Link s focus) k'
  | CLeft k' r   => zip_up (Node focus r) k'
  | CRight l k'  => zip_up (Node l focus) k'
  end.

(** [reconstruct] returns the root of the tree the cursor is embedded in,
    or [None] if the cursor has [Failed]. *)

Definition reconstruct (c : cursor) : option tree :=
  match c with
  | Failed     => None
  | At focus k => Some (zip_up focus k)
  end.

Definition init (t : tree) : cursor := At t Top.

(** * 4. Events

    [ut_event] extends the four navigation primitives with [Do e], which
    applies the inner reducer to advance the history. *)

Inductive ut_event : Type :=
  | Do      : E -> ut_event
  | GoLeft  : ut_event
  | GoRight : ut_event
  | GoLink  : ut_event
  | GoUp    : ut_event.

(** [do_step] commits a new state computed by [inner] from the current
    focus state and event [e].

    - On a [Leaf s]: converts the leaf to a [CLink s] crumb and moves
      to [Leaf (inner s e)], extending a linear chain.
    - On a [Link s t]: keeps the old child [t] as the right branch of a
      new [Node], and [Leaf (inner s e)] becomes the left branch,
      modelling branching (git-style) history.
    - On a [Node] or [Failed]: [Failed]. *)

Definition do_step (focus : tree) (k : ctx) (e : E) : cursor :=
  match focus with
  | Leaf s   => At (Leaf (inner s e)) (CLink s k)
  | Link s t => At (Leaf (inner s e)) (CRight t (CLink s k))
  | Node _ _ => Failed
  end.

Definition step (c : cursor) (e : ut_event) : cursor :=
  cursor_flat_map c (fun focus k =>
    match e with
    | Do ev   => do_step focus k ev
    | GoLeft  => step_left focus k
    | GoRight => step_right focus k
    | GoLink  => step_link focus k
    | GoUp    => step_up focus k
    end).

(** * 5. Inspection

    Boolean predicates and nat discriminants for cursor inspection,
    safe to call from the UI layer. *)

Definition is_failed (c : cursor) : bool :=
  match c with Failed => true | _ => false end.

Definition can_go_left (c : cursor) : bool :=
  match c with At (Node _ _) _ => true | _ => false end.

Definition can_go_right (c : cursor) : bool :=
  match c with At (Node _ _) _ => true | _ => false end.

Definition can_go_link (c : cursor) : bool :=
  match c with At (Link _ _) _ => true | _ => false end.

Definition can_go_up (c : cursor) : bool :=
  match c with
  | At _ Top => false
  | At _ _   => true
  | Failed   => false
  end.

(** Depth of a context = number of steps back to the root. *)

Fixpoint ctx_depth (k : ctx) : nat :=
  match k with
  | Top          => 0
  | CLink _ k'   => S (ctx_depth k')
  | CLeft k' _   => S (ctx_depth k')
  | CRight _ k'  => S (ctx_depth k')
  end.

Definition cursor_depth (c : cursor) : nat :=
  match c with
  | Failed    => 0
  | At _ k    => ctx_depth k
  end.

(** Focus kind discriminant: 0 = Leaf, 1 = Link, 2 = Node, 3 = Failed. *)

Definition focus_kind (c : cursor) : nat :=
  match c with
  | At (Leaf _)   _ => 0
  | At (Link _ _) _ => 1
  | At (Node _ _) _ => 2
  | Failed          => 3
  end.

(** [focus_value] reads the state value held at the cursor focus.
    It returns [Some s] for [Leaf s] and [Link s _], and [None] otherwise. *)

Definition focus_value (c : cursor) : option St :=
  match c with
  | At (Leaf s)   _ => Some s
  | At (Link s _) _ => Some s
  | _               => None
  end.

(** * 6. Theorems *)

(** Going left descends into the left subtree of a [Node];
    going up afterwards restores the original cursor exactly. *)

Theorem go_left_up :
  forall (l r : tree) (k : ctx),
    go_up (go_left (At (Node l r) k)) = At (Node l r) k.
Proof.
  intros l r k.
  unfold go_left, go_up.
  unfold cursor_flat_map.
  simpl step_left.
  simpl step_up.
  reflexivity.
Qed.

(** Going right descends into the right subtree of a [Node];
    going up afterwards restores the original cursor exactly. *)

Theorem go_right_up :
  forall (l r : tree) (k : ctx),
    go_up (go_right (At (Node l r) k)) = At (Node l r) k.
Proof.
  intros l r k.
  unfold go_right, go_up.
  unfold cursor_flat_map.
  simpl step_right.
  simpl step_up.
  reflexivity.
Qed.

(** Any navigation step on a [Failed] cursor stays [Failed]. *)

Theorem failed_absorbs :
  forall (f : cursor -> cursor),
    f = go_left \/ f = go_right \/ f = go_link \/ f = go_up ->
    f Failed = Failed.
Proof.
  intros f [Hl | [Hr | [Hk | Hu]]] ; subst ; reflexivity.
Qed.

(** [cursor_flat_map] with the identity continuation is the identity. *)

Theorem flat_map_right_id :
  forall (c : cursor),
    cursor_flat_map c (fun focus k => At focus k) = c.
Proof.
  intros c. destruct c ; reflexivity.
Qed.

(** [cursor_flat_map] is associative. *)

Theorem flat_map_assoc :
  forall (c : cursor) (f g : tree -> ctx -> cursor),
    cursor_flat_map (cursor_flat_map c f) g =
    cursor_flat_map c (fun focus k => cursor_flat_map (f focus k) g).
Proof.
  intros c f g. destruct c ; reflexivity.
Qed.

(** The reconstructed tree is invariant under go_left + go_up round-trips. *)

Theorem reconstruct_left_round_trip :
  forall (l r : tree) (k : ctx),
    reconstruct (go_up (go_left (At (Node l r) k))) =
    reconstruct (At (Node l r) k).
Proof.
  intros l r k.
  rewrite go_left_up.
  reflexivity.
Qed.

(** Same invariant for right child navigation. *)

Theorem reconstruct_right_round_trip :
  forall (l r : tree) (k : ctx),
    reconstruct (go_up (go_right (At (Node l r) k))) =
    reconstruct (At (Node l r) k).
Proof.
  intros l r k.
  rewrite go_right_up.
  reflexivity.
Qed.

(** Any step from a [Failed] cursor stays [Failed]. *)

Theorem failed_step :
  forall (e : ut_event),
    step Failed e = Failed.
Proof.
  intros e. destruct e ; reflexivity.
Qed.

(** * 7. History invariants for [do_step] *)

(** [do_step] on a [Leaf] makes the new state the current focus value. *)

Theorem do_step_focus_leaf :
  forall (s : St) (k : ctx) (e : E),
    focus_value (do_step (Leaf s) k e) = Some (inner s e).
Proof.
  intros s k e. simpl. reflexivity.
Qed.

(** After [do_step] on a [Leaf], the cursor can always go up. *)

Theorem do_step_can_go_up_leaf :
  forall (s : St) (k : ctx) (e : E),
    can_go_up (do_step (Leaf s) k e) = true.
Proof.
  intros s k e. simpl. reflexivity.
Qed.

(** After [do_step] on a [Leaf] and going up, the previous state is recovered. *)

Theorem do_step_undo_leaf :
  forall (s : St) (k : ctx) (e : E),
    focus_value (go_up (do_step (Leaf s) k e)) = Some s.
Proof.
  intros s k e.
  unfold do_step, go_up, cursor_flat_map, step_up, focus_value.
  reflexivity.
Qed.

(** Undo followed by redo (go_link) restores the cursor after [do_step]. *)

Theorem do_step_undo_redo_leaf :
  forall (s : St) (k : ctx) (e : E),
    go_link (go_up (do_step (Leaf s) k e)) = do_step (Leaf s) k e.
Proof.
  intros s k e.
  unfold do_step, go_up, go_link, cursor_flat_map, step_up, step_link.
  reflexivity.
Qed.

(** [do_step] on a [Node] yields [Failed]. *)

Theorem do_step_node_failed :
  forall (l r : tree) (k : ctx) (e : E),
    do_step (Node l r) k e = Failed.
Proof.
  intros l r k e. simpl. reflexivity.
Qed.

(** [step (Do e)] on [Failed] stays [Failed]. *)

Theorem step_do_failed :
  forall (e : E),
    step Failed (Do e) = Failed.
Proof.
  intros e. simpl. reflexivity.
Qed.

(** * 8. Correctness of inspection predicates *)

(** Going up from [init] always fails (there is no parent). *)

Theorem init_go_up_failed :
  forall (t : tree),
    go_up (init t) = Failed.
Proof.
  intros t. unfold init, go_up, cursor_flat_map, step_up. reflexivity.
Qed.

(** [can_go_up] correctly reflects whether the context is non-[Top]. *)

Theorem can_go_up_correct :
  forall (focus : tree) (k : ctx),
    can_go_up (At focus k) = true <-> k <> Top.
Proof.
  intros focus k. destruct k ; simpl ; split ; congruence.
Qed.

(** [can_go_left] correctly reflects whether the focus is a [Node]. *)

Theorem can_go_left_correct :
  forall (focus : tree) (k : ctx),
    can_go_left (At focus k) = true <-> exists l r, focus = Node l r.
Proof.
  intros focus k. destruct focus ; simpl ; split ;
    [ discriminate | intros [l [r H]] ; discriminate
    | discriminate | intros [l [r H]] ; discriminate
    | intros _ ; eauto | intros _ ; reflexivity ].
Qed.

(** [can_go_right] correctly reflects whether the focus is a [Node]. *)

Theorem can_go_right_correct :
  forall (focus : tree) (k : ctx),
    can_go_right (At focus k) = true <-> exists l r, focus = Node l r.
Proof.
  intros focus k. destruct focus ; simpl ; split ;
    [ discriminate | intros [l [r H]] ; discriminate
    | discriminate | intros [l [r H]] ; discriminate
    | intros _ ; eauto | intros _ ; reflexivity ].
Qed.

(** [can_go_link] correctly reflects whether the focus is a [Link]. *)

Theorem can_go_link_correct :
  forall (focus : tree) (k : ctx),
    can_go_link (At focus k) = true <-> exists a b, focus = Link a b.
Proof.
  intros focus k. destruct focus ; simpl ; split ;
    [ discriminate | intros [a [b H]] ; discriminate
    | intros _ ; eauto | intros _ ; reflexivity
    | discriminate | intros [a [b H]] ; discriminate ].
Qed.

End UndoTree.
