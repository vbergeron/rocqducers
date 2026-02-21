# PickList — Verified selection list

Items move between a **picked** list and a **suggestions** list. The reducer is defined in Rocq; the two core invariants are proved by structural induction on any sequence of events.

## Data model

```rocq
Record state (A : Type) := {
  picked      : list A;
  suggestions : list A;
}.

Inductive event :=
  | DoPick   : nat -> event   -- move suggestions[i] → picked
  | DoUnpick : nat -> event   -- move picked[i] → suggestions
```

`init default rest` builds the initial state with `picked = [default]` and `suggestions = rest`.

## Reducer

```rocq
Definition reduce {A} (s : state A) (e : event) : state A :=
  match e with
  | DoPick i   => do_pick s i      (* move suggestions[i] → picked *)
  | DoUnpick i => do_unpick s i    (* move picked[i] → suggestions, unless |picked| ≤ 1 *)
  end.
```

`do_unpick` is a no-op when `|picked| ≤ 1` to protect the non-empty invariant.

## Proved invariants

| Theorem | Statement |
|---|---|
| `picked_nonempty` | `picked s ≠ [] → picked (reduce s e) ≠ []` |
| `total_preserved` | `|picked (reduce s e)| + |suggestions (reduce s e)| = |picked s| + |suggestions s|` |
| `picked_always_nonempty` | For any event sequence from `init`, picked is always non-empty |
| `total_always_preserved` | For any event sequence from `init d rest`, total = `1 + |rest|` |

The inductive theorems close over `fold_left reduce events (init d rest)`, guaranteeing the properties hold for **any** sequence of events, not just one step.

## React usage

```jsx
import { PickList } from "@rocqducers/lib/Rocqducers.js";
import useSafePickList from "./hooks/useSafePickList";

const FRUITS = ["Banana", "Cherry", "Date", "Elderberry"];

function MyComponent() {
  const { picked, suggestions, pick, unpick } = useSafePickList(FRUITS, 0);

  return (
    <>
      <ul>{picked.map((f, i) => <li key={f} onClick={() => unpick(i)}>{f} ✕</li>)}</ul>
      <ul>{suggestions.map((f, i) => <li key={f} onClick={() => pick(i)}>{f} +</li>)}</ul>
    </>
  );
}
```

## Source files

| File | Role |
|---|---|
| `rocqducers/theories/PickList.v` | Types, reducer, proofs |
| `rocqducers/extraction/Extract.v` | Extraction directives |
| `rocqducers/lib/Rocqducers.ml` | `PickList` OCaml wrapper (list → array) |
| `src/hooks/useSafePickList.js` | React hook |
| `src/components/SafePickList.jsx` | Demo component |
