# UndoTree — Verified branching history tree

A navigable history tree backed by a formally verified zipper. State transitions are driven by a pluggable inner reducer (`inner : St -> E -> St`); navigation and history invariants are proved once in Rocq and enforced at compile time.

## Overview

UndoTree models history as a persistent tree rather than a linear stack. Branching is first-class: applying `Do e` on a `Link` node (a node that already has one child) creates a `Node` keeping the old branch alongside the new one — history is never discarded, git-style.

```
   s₀                       s₀
    │  Do e₁                 │
   s₁          →            s₁
    │  Do e₂                / \
   s₂                      s₂  s₃   (← Do e₃ from s₁)
```

## Data model

```
tree St =
  | Leaf  : St → tree St               -- terminal node, holds a state value
  | Link  : St → tree St → tree St     -- chain node (one child, linear history)
  | Node  : tree St → tree St → tree St -- binary node (two branches)

ctx St =
  | Top                                  -- at the root
  | CLink  : St → ctx St → ctx St       -- descended into a Link's child
  | CLeft  : ctx St → tree St → ctx St  -- descended left into a Node
  | CRight : tree St → ctx St → ctx St  -- descended right into a Node

cursor St =
  | At     : tree St → ctx St → cursor St  -- valid position
  | Failed : cursor St                     -- navigation error (absorbing)
```

A **cursor** is a zipper: it pairs the **focus** (the subtree under examination) with a **context** (the breadcrumb trail back to the root). Together they fully represent the tree.

### Reconstruction

`zip_up` reassembles the root tree by folding the context over the focus. It is structurally recursive on `ctx`:

```
zip_up (Leaf "x") (CLeft Top (Leaf "y"))
  = zip_up (Node (Leaf "x") (Leaf "y")) Top
  = Node (Leaf "x") (Leaf "y")
```

`reconstruct` wraps it in an `option`:

```
reconstruct (At focus k) = Some (zip_up focus k)
reconstruct  Failed      = None
```

## Inner reducer

`UndoTree` is parameterised by an inner reducer that computes the next state from the current focus state and an event:

```rocq
Section UndoTree.
Context {St E : Type}.
Variable inner : St -> E -> St.
```

After the section closes, every exported definition receives `inner` as an explicit argument, matching the `(state, action) => state` pattern used by React's `useReducer`.

## Events

```rocq
Inductive ut_event :=
  | Do      : E -> ut_event    -- apply inner reducer and commit new state
  | GoLeft  : ut_event         -- descend into left child of a Node
  | GoRight : ut_event         -- descend into right child of a Node
  | GoLink  : ut_event         -- descend into child of a Link (redo)
  | GoUp    : ut_event         -- ascend to parent (undo)
```

`step` dispatches to the corresponding operation and absorbs `Failed`:

```rocq
Definition step (c : cursor) (e : ut_event) : cursor :=
  cursor_flat_map c (fun focus k =>
    match e with
    | Do ev   => do_step focus k ev
    | GoLeft  => step_left focus k
    | GoRight => step_right focus k
    | GoLink  => step_link focus k
    | GoUp    => step_up focus k
    end).
```

## Committing new states with `Do`

`do_step` applies the inner reducer and archives the current state:

| Focus | Effect |
|---|---|
| `Leaf s` | Moves to `Leaf (inner s e)`, pushing `CLink s` crumb — extends a linear chain |
| `Link s t` | Moves to `Leaf (inner s e)`, keeping old child `t` as right branch — creates a `Node` |
| `Node _ _` | Returns `Failed` (ambiguous parent) |

## Navigation

| Function | Precondition | Effect |
|---|---|---|
| `GoLeft` | focus is `Node l r` | descend into `l`, push `CLeft` crumb |
| `GoRight` | focus is `Node l r` | descend into `r`, push `CRight` crumb |
| `GoLink` | focus is `Link s t` | descend into `t`, push `CLink` crumb (redo) |
| `GoUp` | context is not `Top` | ascend, rebuild parent from crumb (undo) |

Any navigation that does not satisfy its precondition returns `Failed`. `Failed` absorbs all subsequent steps.

## Proved invariants

### Navigation round-trips

| Theorem | Statement |
|---|---|
| `go_left_up` | `go_up (go_left (At (Node l r) k)) = At (Node l r) k` |
| `go_right_up` | `go_up (go_right (At (Node l r) k)) = At (Node l r) k` |
| `reconstruct_left_round_trip` | `reconstruct (go_up (go_left (At (Node l r) k))) = reconstruct (At (Node l r) k)` |
| `reconstruct_right_round_trip` | `reconstruct (go_up (go_right (At (Node l r) k))) = reconstruct (At (Node l r) k)` |

Round-trip theorems: navigating into a child and back up never changes the underlying tree.

### Sequencing laws

| Theorem | Statement |
|---|---|
| `flat_map_right_id` | `cursor_flat_map c (fun f k => At f k) = c` |
| `flat_map_assoc` | `cursor_flat_map (cursor_flat_map c f) g = cursor_flat_map c (fun f k => cursor_flat_map (f k) g)` |

### Failure absorption

| Theorem | Statement |
|---|---|
| `failed_absorbs` | `f Failed = Failed` for any navigation `f` |
| `failed_step` | `step Failed e = Failed` for any `e` |
| `step_do_failed` | `step Failed (Do e) = Failed` |

### History invariants (`Do` / undo / redo)

| Theorem | Statement |
|---|---|
| `do_step_focus_leaf` | `focus_value (do_step (Leaf s) k e) = Some (inner s e)` |
| `do_step_can_go_up_leaf` | `can_go_up (do_step (Leaf s) k e) = true` |
| `do_step_undo_leaf` | `focus_value (go_up (do_step (Leaf s) k e)) = Some s` |
| `do_step_undo_redo_leaf` | `go_link (go_up (do_step (Leaf s) k e)) = do_step (Leaf s) k e` |
| `do_step_node_failed` | `do_step (Node l r) k e = Failed` |
| `init_go_up_failed` | `go_up (init t) = Failed` |

### Inspection predicate correctness

| Theorem | Statement |
|---|---|
| `can_go_up_correct` | `can_go_up (At focus k) = true ↔ k ≠ Top` |
| `can_go_left_correct` | `can_go_left (At focus k) = true ↔ ∃ l r, focus = Node l r` |
| `can_go_right_correct` | `can_go_right (At focus k) = true ↔ ∃ l r, focus = Node l r` |
| `can_go_link_correct` | `can_go_link (At focus k) = true ↔ ∃ s t, focus = Link s t` |

## Inspection functions

The following are extracted from Rocq and safe to call from JavaScript:

| Function | Return type | Meaning |
|---|---|---|
| `is_failed` | `bool` | cursor is in the `Failed` state |
| `can_go_left` | `bool` | focus is a `Node` |
| `can_go_right` | `bool` | focus is a `Node` |
| `can_go_link` | `bool` | focus is a `Link` (redo available) |
| `can_go_up` | `bool` | context is not `Top` (undo available) |
| `focus_kind` | `nat` (0/1/2/3) | Leaf / Link / Node / Failed |
| `cursor_depth` | `nat` | number of crumbs back to root |
| `focus_value` | `option St` | current state value, `None` for Node or Failed |

## React usage

```jsx
import { UndoTree } from "@rocqducers/lib/Rocqducers.js";

// Define the inner reducer (pure function, any type)
const myInner = (state, event) => { /* ... */ return newState; };

// Build a tree of initial states once at module level
const TREE = UndoTree.node(
  UndoTree.link("A", UndoTree.node(UndoTree.leaf("B"), UndoTree.leaf("C"))),
  UndoTree.leaf("D"),
);

function MyComponent() {
  const [cursor, dispatch] = useReducer(
    (c, e) => UndoTree.step(myInner, c, e),
    UndoTree.init(TREE),
  );

  const canGoLeft  = UndoTree.can_go_left(cursor);
  const canGoRight = UndoTree.can_go_right(cursor);
  const canGoLink  = UndoTree.can_go_link(cursor);  // redo
  const canGoUp    = UndoTree.can_go_up(cursor);    // undo

  return (
    <>
      <button onClick={() => dispatch(UndoTree.ev_go_left)}  disabled={!canGoLeft}>← Left</button>
      <button onClick={() => dispatch(UndoTree.ev_go_right)} disabled={!canGoRight}>Right →</button>
      <button onClick={() => dispatch(UndoTree.ev_go_link)}  disabled={!canGoLink}>↓ Redo</button>
      <button onClick={() => dispatch(UndoTree.ev_go_up)}    disabled={!canGoUp}>↑ Undo</button>
      <button onClick={() => dispatch(UndoTree.do_(myEvent))}>Apply event</button>
      <p>Depth: {UndoTree.cursor_depth(cursor)}</p>
    </>
  );
}
```

## Source files

| File | Role |
|---|---|
| `rocqducers/theories/UndoTree.v` | Types, inner reducer integration, navigation, proofs |
| `rocqducers/extraction/Extract.v` | Extraction directives |
| `rocqducers/lib/Rocqducers.ml` | `UndoTree` OCaml/Melange wrapper |
| `src/hooks/useSafeUndoTree.js` | React hook |
| `src/components/UndoTreeView.jsx` | View component |
| `src/components/SafeUndoTree.jsx` | Demo container |
