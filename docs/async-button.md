# AsyncButton — Verified async button

A button that tracks whether an async operation is in-flight. Clicks while loading are silently ignored — proved, not just guarded.

## State machine

```
         Click
  Idle ────────► Loading
    ▲              │
    │    Success   │
    └──────────────┘
    │    Failure   │
    └──────────────┘

  Any event in Idle (except Click) → Idle (no-op)
  Click in Loading                  → Loading (ignored, proved)
```

## Data model

```rocq
Inductive state := Idle | Loading.

Inductive event := Click | Success | Failure.

Definition reducer (s : state) (e : event) : state :=
  match s, e with
  | Idle,    Click   => Loading
  | Loading, Success => Idle
  | Loading, Failure => Idle
  | _,       _       => s       (* all other combinations are no-ops *)
  end.
```

## Proved invariant

```rocq
Theorem click_on_loading_is_ignored :
  reducer Loading Click = Loading.
```

The theorem is small but the point is architectural: the UI can freely call `dispatch(Click)` without defensive checks — the reducer is proved to handle it correctly.

## React usage

```jsx
import { AsyncButton } from "@rocqducers/lib/Rocqducers.js";
import useSafeAsyncButton from "./hooks/useSafeAsyncButton";

function MyComponent({ onSubmit }) {
  const { isIdle, isLoading, click, succeed, fail } = useSafeAsyncButton();

  const handleClick = async () => {
    click();
    try   { await onSubmit(); succeed(); }
    catch { fail(); }
  };

  return (
    <button onClick={handleClick} disabled={isLoading}>
      {isLoading ? "Loading…" : "Submit"}
    </button>
  );
}
```

The `disabled` attribute is a UX convenience; correctness does not depend on it — `click` dispatches `Click` which the reducer ignores when `Loading`.

## Source files

| File | Role |
|---|---|
| `rocqducers/theories/AsyncButton.v` | State machine and proof |
| `rocqducers/extraction/Extract.v` | Extraction directives |
| `rocqducers/lib/Rocqducers.ml` | `AsyncButton` OCaml wrapper |
| `src/hooks/useSafeAsyncButton.js` | React hook |
| `src/components/SafeAsyncButton.jsx` | Demo component |
