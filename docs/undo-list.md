# UndoList — Verified linear undo/redo wrapper

A generic higher-order wrapper that adds a proven-correct undo/redo timeline to **any** pure Rocq reducer. `UndoList` is the linear-history counterpart to `UndoTree`: it stores a current state flanked by two stacks (`past` and `future`) rather than a navigable tree.

## Overview

```
 Do e₁       Do e₂       Undo          Redo
s₀ ──────── s₁ ──────── s₂ ──────── s₁ ──────── s₂
              past=[s₀]   past=[s₁,s₀]  past=[s₀]   past=[s₁,s₀]
              future=[]   future=[]     future=[s₂]  future=[]
```

`Do` clears the future (a new action discards the redo stack). `Undo` and `Redo` on an empty stack return `Failed` rather than silently doing nothing — `Failed` then absorbs all subsequent steps.

## Inner reducer

`UndoList` is parameterised by an inner reducer that computes the next state:

```rocq
Section UndoList.
Context {St E : Type}.
Variable inner : St -> E -> St.
```

After the section closes, every exported definition receives `inner` as an explicit argument, matching the `(state, action) => state` pattern used by React's `useReducer`.

## Data model

```rocq
Inductive state : Type :=
  | Hist   : St -> list St -> list St -> state
  | Failed : state.
(*           ↑ current    past    future  *)
```

`Hist curr past future` holds the current state and the two history stacks. `Failed` is an absorbing element: once reached, all further steps return `Failed`.

```rocq
Inductive event : Type :=
  | Do   : E -> event    -- apply inner reducer, push current onto past, clear future
  | Undo : event         -- pop from past, push current onto future
  | Redo : event         -- pop from future, push current onto past
```

## Step function

```rocq
Definition step (hs : state) (e : event) : state :=
  flat_map hs (fun curr past fut =>
    match e with
    | Do ev   => Hist (inner curr ev) (curr :: past) []
    | Undo    => match past with
                 | []           => Failed
                 | prev :: rest => Hist prev rest (curr :: fut)
                 end
    | Redo    => match fut with
                 | []           => Failed
                 | next :: rest => Hist next (curr :: past) rest
                 end
    end).
```

`flat_map` is the sequencing primitive: it propagates `Failed` unchanged, mirroring `cursor_flat_map` in `UndoTree`.

## Proved invariants

### `Do` behaviour

| Theorem | Statement |
|---|---|
| `do_current` | `current (step (Hist curr p fut) (Do e)) = Some (inner curr e)` |
| `do_extends_past` | `past (step (Hist curr p fut) (Do e)) = curr :: p` |
| `do_clears_future` | `future (step (Hist curr p fut) (Do e)) = []` |
| `do_size_change` | `|past| increases by 1 and |future| = 0 after Do` |
| `init_do_has_one_past` | `past (step (init s) (Do e)) = [s]` and `future = []` |

### `Undo` / `Redo` behaviour

| Theorem | Statement |
|---|---|
| `undo_failed_when_empty` | `step (Hist curr [] fut) Undo = Failed` |
| `undo_restores` | `p = prev :: rest → current (step (Hist curr p fut) Undo) = Some prev` |
| `redo_failed_when_empty` | `step (Hist curr p []) Redo = Failed` |
| `redo_restores` | `fut = next :: rest → current (step (Hist curr p fut) Redo) = Some next` |
| `init_undo_failed` | `step (init s) Undo = Failed` |
| `init_redo_failed` | `step (init s) Redo = Failed` |

### Round-trip theorems

| Theorem | Statement |
|---|---|
| `undo_after_do` | `current (step (step (Hist curr p fut) (Do e)) Undo) = Some curr` |
| `undo_after_do_state` | `step (step (Hist curr p fut) (Do e)) Undo = Hist curr p [inner curr e]` |
| `redo_after_undo` | `p = prev :: rest → step (step (Hist curr p fut) Undo) Redo = Hist curr p fut` |

Note: `undo_after_do_state` shows that after Do→Undo, the future contains exactly `[inner curr e]` (the state we just discarded), not the original future — because `Do` cleared it.

### Size invariants

| Theorem | Statement |
|---|---|
| `undo_preserves_size` | `p ≠ [] → |past| + |future|` is preserved by `Undo` |
| `redo_preserves_size` | `fut ≠ [] → |past| + |future|` is preserved by `Redo` |

The non-empty precondition is required because `Undo`/`Redo` on empty stacks yield `Failed`, which has size 0.

### Failure absorption

| Theorem | Statement |
|---|---|
| `failed_absorbs` | `step Failed e = Failed` for any `e` |

### Sequencing laws

| Theorem | Statement |
|---|---|
| `flat_map_right_id` | `flat_map hs (fun curr p fut => Hist curr p fut) = hs` |
| `flat_map_assoc` | `flat_map (flat_map hs f) g = flat_map hs (fun curr p fut => flat_map (f curr p fut) g)` |

### Inspection predicate correctness

| Theorem | Statement |
|---|---|
| `can_undo_correct` | `can_undo (Hist curr p fut) = true ↔ p ≠ []` |
| `can_redo_correct` | `can_redo (Hist curr p fut) = true ↔ fut ≠ []` |

## Inspection functions

| Function | Return type | Meaning |
|---|---|---|
| `is_failed` | `bool` | state is `Failed` |
| `can_undo` | `bool` | `past` is non-empty |
| `can_redo` | `bool` | `future` is non-empty |
| `current` | `option St` | current state value; `None` when `Failed` |
| `past` | `list St` | stack of past states (most-recent first) |
| `future` | `list St` | stack of future states (most-recent first) |

## Comparison with UndoTree

| Aspect | UndoList | UndoTree |
|---|---|---|
| History topology | Linear (two stacks) | Branching tree (zipper) |
| Branching | `Do` discards the future | `Do` on a `Link` creates a `Node`, preserving both branches |
| Undo | Pop from `past` | `GoUp` crumb |
| Redo | Pop from `future` | `GoLink` crumb |
| On empty undo/redo | `Failed` (absorbing) | `Failed` (absorbing) |
| State param type | `St` | `St` |
| Sequencing primitive | `flat_map` | `cursor_flat_map` |

## React usage

```jsx
import { UndoList } from "@rocqducers/lib/Rocqducers.js";

// Define the inner reducer for the application state
const myInner = (state, event) => { /* ... */ return newState; };

function MyComponent() {
  const [hs, dispatch] = useReducer(
    (hs, e) => UndoList.step(myInner, hs, e),
    UndoList.init(initialState),
  );

  const canUndo = UndoList.can_undo(hs);
  const canRedo = UndoList.can_redo(hs);
  const isFailed = UndoList.is_failed(hs);

  return (
    <>
      <button onClick={() => dispatch(UndoList.undo)} disabled={!canUndo}>Undo</button>
      <button onClick={() => dispatch(UndoList.redo)} disabled={!canRedo}>Redo</button>
      <button onClick={() => dispatch(UndoList.do_(myEvent))}>Apply</button>
      {isFailed && <p>History navigation failed.</p>}
    </>
  );
}
```

## Source files

| File | Role |
|---|---|
| `rocqducers/theories/UndoList.v` | Types, step function, all proofs |
| `rocqducers/extraction/Extract.v` | Extraction directives |
| `rocqducers/lib/Rocqducers.ml` | `UndoList` OCaml/Melange wrapper |
