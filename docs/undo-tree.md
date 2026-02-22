# UndoTree — Verified tree zipper

A navigable tree structure backed by a formally verified zipper. Navigation is driven by a pure Rocq reducer; invariants are proved once and enforced at compile time.

## Data model

```
tree A =
  | Leaf  : A → tree A               -- terminal node
  | Link  : A → tree A → tree A      -- chain node (one child)
  | Node  : tree A → tree A → tree A -- binary node

ctx A =
  | Top                              -- at the root
  | CLink  : A → ctx A → ctx A       -- descended into a Link's child
  | CLeft  : ctx A → tree A → ctx A  -- descended left into a Node
  | CRight : tree A → ctx A → ctx A  -- descended right into a Node

cursor A =
  | At     : tree A → ctx A → cursor A   -- valid position
  | Failed : cursor A                    -- navigation error (absorbing)
```

A **cursor** is a zipper: it pairs the **focus** (the subtree currently under examination) with a **context** (the breadcrumb trail back to the root). Together they represent the full tree.

### Reconstruction

`zip_up` reassembles the root tree by folding the context over the focus. It is structurally recursive on `ctx`, so Rocq's termination checker accepts it unconditionally:

```
zip_up (Leaf "x") (CLeft Top (Leaf "y"))
  = zip_up (Node (Leaf "x") (Leaf "y")) Top
  = Node (Leaf "x") (Leaf "y")
```

`reconstruct` wraps it in an `option`:

```
reconstruct (At focus ctx) = Some (zip_up focus ctx)
reconstruct  Failed        = None
```

## Reducer

Events are plain enum constructors; `step` dispatches to the corresponding navigation function:

```rocq
Inductive event :=
  | EvGoLeft | EvGoRight | EvGoLink | EvGoUp.

Definition step {A} (c : cursor A) (e : event) : cursor A :=
  match e with
  | EvGoLeft  => go_left c
  | EvGoRight => go_right c
  | EvGoLink  => go_link c
  | EvGoUp    => go_up c
  end.
```

`step` matches React's `(state, action) => state` reducer signature and is passed directly to `useReducer`.

## Navigation

| Function | Precondition | Effect |
|---|---|---|
| `go_left` | focus is `Node l r` | descend into `l`, push `CLeft` crumb |
| `go_right` | focus is `Node l r` | descend into `r`, push `CRight` crumb |
| `go_link` | focus is `Link a t` | descend into `t`, push `CLink` crumb |
| `go_up` | context is not `Top` | ascend, rebuild parent from crumb |

Any navigation that does not satisfy its precondition returns `Failed`. `Failed` then absorbs all subsequent navigation steps.

## Proved invariants

| Theorem | Statement |
|---|---|
| `go_left_up` | `go_up (go_left (At (Node l r) ctx)) = At (Node l r) ctx` |
| `go_right_up` | `go_up (go_right (At (Node l r) ctx)) = At (Node l r) ctx` |
| `failed_absorbs` | `f Failed = Failed` for any navigation `f` |
| `flat_map_right_id` | `cursor_flat_map c (fun f c => At f c) = c` |
| `flat_map_assoc` | `cursor_flat_map (cursor_flat_map c f) g = cursor_flat_map c (fun f c => cursor_flat_map (f c) g)` |
| `reconstruct_left_round_trip` | `reconstruct (go_up (go_left (At (Node l r) ctx))) = reconstruct (At (Node l r) ctx)` |
| `reconstruct_right_round_trip` | `reconstruct (go_up (go_right (At (Node l r) ctx))) = reconstruct (At (Node l r) ctx)` |
| `failed_step` | `step Failed e = Failed` for any event `e` |

The round-trip theorems express the core correctness property: navigating into a child and back up never changes the underlying tree.

## Inspection functions

The following predicates are extracted from Rocq and usable directly in JavaScript (they return native booleans/integers):

| Function | Return type | Meaning |
|---|---|---|
| `is_failed` | `bool` | cursor is in the Failed state |
| `can_go_left` | `bool` | focus is a `Node` |
| `can_go_right` | `bool` | focus is a `Node` |
| `can_go_link` | `bool` | focus is a `Link` |
| `can_go_up` | `bool` | context is not `Top` |
| `focus_kind` | `nat` (0/1/2/3) | Leaf / Link / Node / Failed |
| `cursor_depth` | `nat` | number of crumbs back to root |

## React usage

```jsx
import { UndoTree } from "@rocqducers/lib/Rocqducers.js";
import useSafeUndoTree from "./hooks/useSafeUndoTree";

// Build a tree once at module level
const TREE = UndoTree.node(
  UndoTree.link("A", UndoTree.node(UndoTree.leaf("B"), UndoTree.leaf("C"))),
  UndoTree.leaf("D"),
);

function MyComponent() {
  const {
    canGoLeft, canGoRight, canGoLink, canGoUp,
    focusKind, focusLabel, depth,
    goLeft, goRight, goLink, goUp,
  } = useSafeUndoTree(UndoTree.root_cursor(TREE));

  return (
    <>
      <button onClick={goLeft}  disabled={!canGoLeft}>← Left</button>
      <button onClick={goRight} disabled={!canGoRight}>Right →</button>
      <button onClick={goLink}  disabled={!canGoLink}>↓ Link</button>
      <button onClick={goUp}    disabled={!canGoUp}>↑ Up</button>
      <p>Focus: {["Leaf","Link","Node","Failed"][focusKind]} · depth {depth}</p>
    </>
  );
}
```

## Source files

| File | Role |
|---|---|
| `rocqducers/theories/UndoTree.v` | Types, navigation, proofs |
| `rocqducers/extraction/Extract.v` | Extraction directives |
| `rocqducers/lib/Rocqducers.ml` | `UndoTree` OCaml wrapper |
| `src/hooks/useSafeUndoTree.js` | React hook |
| `src/components/UndoTreeView.jsx` | View component |
| `src/components/SafeUndoTree.jsx` | Demo container |
