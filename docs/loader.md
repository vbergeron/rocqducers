# Loader — Verified network loader

A network data loader with caching, retries, and timeout. The pure reducer is defined in Rocq; side effects (HTTP requests, timers) are handled by the React hook. Race conditions and stuck spinners are ruled out by proof.

## State machine

```
     Fetch          GotResponse         Fetch
Idle ────── Loading ──────────── Loaded ─────── Loading
               │                                   │
               │ GotError / TimedOut               │
               ▼                                   ▼
           Errored ──── DoRetry ──────── Loading  Errored
           (retries < max_retries)
           Errored ─── stays Errored ─────────── Errored
           (retries ≥ max_retries)
```

## Data model

```rocq
Inductive phase_t :=
  | Idle | Loading (rid : nat) | Loaded | Errored.

Record state (D : Type) := {
  phase       : phase_t;
  cache       : option D;   -- data from last successful load
  next_id     : nat;        -- monotone request counter
  retries     : nat;        -- retry count for current error
  max_retries : nat;        -- ceiling set at init
}.
```

Each `Loading` phase carries a **request id** (`rid`). Responses are only accepted if their `rid` matches the current phase — all stale or duplicate responses are silently discarded.

## Reducer

```rocq
Definition step {D} (s : state D) (e : event D) : state D :=
  match e with
  | Fetch          => (* start loading unless already loading *)
  | GotResponse rid data => (* accept only if rid matches *)
  | GotError rid   => (* transition to Errored only if rid matches *)
  | TimedOut rid   => (* same as GotError *)
  | DoRetry        => (* retry from Errored if under max_retries *)
  end.
```

## Proved invariants

| Theorem | Statement | Addressed bug |
|---|---|---|
| Loaded implies data | `phase (step s e) = Loaded → ∃ d, cache (step s e) = Some d` | Missing data on load |
| Error preserves cache | `phase (step s e) = Errored → cache (step s e) = cache s` | Cache wipe on error |
| Stale events ignored | `phase s = Loading crid → rid ≠ crid → step s (GotResponse rid d) = s` | Race conditions |
| Retry preserves cache | `cache (step s DoRetry) = cache s` | Cache invalidation on retry |
| Bounded retries | `retries s ≥ max_retries s → step s DoRetry = s` | Infinite retry loop |
| Timeout resolves loading | `phase s = Loading rid → phase (step s (TimedOut rid)) = Errored` | Stuck spinner |

## React integration

The hook is responsible for scheduling the fetch and timeout. Only `dispatch` calls cross the boundary between pure and effectful code:

```js
useEffect(() => {
  if (!isLoading) return;
  const timer = setTimeout(() => dispatch(Loader.timed_out(rid)), timeoutMs);
  fetch(url)
    .then(data => dispatch(Loader.got_response(rid, data)))
    .catch(()  => dispatch(Loader.got_error(rid)));
  return () => clearTimeout(timer);
}, [isLoading, rid]);
```

## Source files

| File | Role |
|---|---|
| `rocqducers/theories/Loader.v` | State machine, reducer, proofs |
| `rocqducers/extraction/Extract.v` | Extraction directives |
| `rocqducers/lib/Rocqducers.ml` | `Loader` OCaml wrapper |
| `src/hooks/useSafeLoader.js` | React hook (fetch + timer side effects) |
| `src/components/SafeLoader.jsx` | Demo component |
