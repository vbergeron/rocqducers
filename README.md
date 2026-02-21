# Rocqducers

**React components powered by formally verified reducers.**

Rocqducers bridges the [Rocq proof assistant](https://rocq-prover.org/) (formerly Coq) and [React](https://react.dev/) by compiling verified state machines into JavaScript via [Melange](https://melange.re/). Invariants are proved once in Rocq and enforced at compile time — the generated code is guaranteed to uphold them at runtime.

## How it works

```
  Rocq            Extraction         Melange           Vite
┌───────────┐    ┌──────────────┐    ┌───────────┐    ┌──────────┐
│ theories/ │───▶│  OCaml       │───▶│  ES6 JS   │───▶│  React   │
│  proofs   │    │  extraction  │    │  modules  │    │  App     │
└───────────┘    └──────────────┘    └───────────┘    └──────────┘
    ▲                                      │
    │  Invariants proved once,             │  useReducer(reducer, ...)
    │  enforced forever                    │
    └──────────────────────────────────────┘
```

1. **Rocq** — Definitions, reducer logic, and invariant proofs live in `.v` files under `rocqducers/theories/`. The type system enforces that every code path preserves the stated properties.

2. **Extraction** — Rocq's extraction mechanism translates the verified definitions into OCaml. Inductive types like `list`, `nat`, and `option` are mapped to their OCaml counterparts for efficient runtime representation. Configuration lives in `rocqducers/extraction/Extract.v`.

3. **Melange** — The extracted OCaml is compiled to ES6 JavaScript modules by [Melange](https://melange.re/). A thin wrapper (`rocqducers/lib/Rocqducers.ml`) adds array conversion helpers so the JS consumer works with plain arrays instead of linked lists.

4. **Vite + React** — The generated JS is imported like any other module. React's `useReducer` hook accepts the verified reducer directly — the proof-carrying state machine drives the UI.

## Components

> Detailed documentation for each component lives in [`docs/`](./docs/).

### 1. SafePickList — Verified selection list

→ [`docs/pick-list.md`](./docs/pick-list.md)

A pick/unpick list where items move between "picked" and "suggestions". The reducer is defined in `PickList.v` and used via `useReducer`.

**State:** `{ picked : list A; suggestions : list A }`
**Events:** `DoPick i` | `DoUnpick i`

**Proved invariants:**

| Property | Statement |
|----------|-----------|
| Non-empty picked | `picked s <> [] -> picked (reducer s e) <> []` |
| Total preserved | `card(picked s) + card(suggestions s) = card(picked (reducer s e)) + card(suggestions (reducer s e))` |

### 2. SafeLoader — Verified network loader with cache, retry, and timeout

→ [`docs/loader.md`](./docs/loader.md)

A network data loader that handles loading, errors, retries, timeouts, and race conditions. The pure reducer is defined in `Loader.v`; side effects (fetch, timers) are handled by the React component.

**State:** `{ phase; cache; next_id; retries; max_retries }`
**Events:** `Fetch` | `GotResponse rid data` | `GotError rid` | `TimedOut rid` | `DoRetry`

```
     Fetch          GotResponse         Fetch
Idle ────── Loading ──────────── Loaded ─────── Loading
               │                                   │
               │ GotError / TimedOut               │
               ▼                                   ▼
           Errored ──────────────── Loading    Errored
               │      DoRetry                      │
               │   (retries < max)                 │
               └── stays Errored ──────────────────┘
                   (retries >= max)
```

**Proved invariants:**

| Property | Statement | Addresses |
|----------|-----------|-----------|
| Loaded implies data | `phase (step s e) = Loaded -> exists d, cache (step s e) = Some d` | — |
| Error preserves cache | `phase (step s e) = Errored -> cache (step s e) = cache s` | Inconsistent cache |
| Stale events ignored | `phase s = Loading crid -> rid <> crid -> step s (GotResponse rid d) = s` | Race conditions |
| Retry preserves cache | `cache (step s DoRetry) = cache s` | Cache invalidation |
| Bounded retries | `retries s >= max_retries s -> step s DoRetry = s` | Infinite retry |
| Timeout resolves loading | `phase s = Loading rid -> phase (step s (TimedOut rid)) = Errored` | Stuck spinner |

### 3. SafeAsyncButton — Verified async button

→ [`docs/async-button.md`](./docs/async-button.md)

A button that tracks whether an async operation is in-flight. Clicks while loading are silently ignored — proved, not just guarded.

**State:** `Idle | Loading`
**Events:** `Click | Success | Failure`

**Proved invariant:**

| Property | Statement |
|----------|-----------|
| Click ignored while loading | `reducer Loading Click = Loading` |

### 4. SafeUndoTree — Verified tree zipper

→ [`docs/undo-tree.md`](./docs/undo-tree.md)

A navigable tree with `Leaf`, `Link`, and `Node` constructors. Navigation is modelled as a zipper (focus + context breadcrumbs) and driven by a verified reducer. Round-trip theorems guarantee that navigating into a subtree and back never corrupts the tree.

**State:** `cursor A = At (tree A) (ctx A) | Failed`
**Events:** `EvGoLeft | EvGoRight | EvGoLink | EvGoUp`

**Proved invariants:**

| Property | Statement |
|----------|-----------|
| Left round-trip | `reconstruct (go_up (go_left (At (Node l r) ctx))) = reconstruct (At (Node l r) ctx)` |
| Right round-trip | `reconstruct (go_up (go_right (At (Node l r) ctx))) = reconstruct (At (Node l r) ctx)` |
| Failed absorbs | `f Failed = Failed` for any navigation `f` |
| Failed step | `step Failed e = Failed` for any event `e` |

## Project structure

```
rocqducers/
├── docs/                         # Per-component documentation
│   ├── pick-list.md
│   ├── loader.md
│   ├── async-button.md
│   └── undo-tree.md
├── src/                          # React frontend
│   ├── main.jsx                  #   Entry point
│   ├── App.jsx                   #   Application shell
│   ├── hooks/                    #   React hooks (one per component)
│   └── components/               #   View + container components
├── vite.config.js                # Vite config with Melange aliases
├── package.json                  # JS dependencies and scripts
└── rocqducers/                   # Dune project (Rocq + Melange)
    ├── dune-project
    ├── theories/
    │   ├── PickList.v            #   Pick list: state, events, reducer, proofs
    │   ├── Loader.v              #   Network loader: state, events, step, proofs
    │   ├── AsyncButton.v         #   Async button: state machine and proof
    │   ├── UndoTree.v            #   Tree zipper: navigation, reconstruction, proofs
    │   └── dune
    ├── extraction/
    │   ├── Extract.v             #   Extraction directives
    │   └── dune
    ├── lib/
    │   ├── Rocqducers.ml         #   Melange wrapper (array interop, constructors)
    │   └── dune
    └── emit/
        └── dune                  #   Melange JS emit target
```

## Tools

| Tool | Role |
|------|------|
| [Rocq](https://rocq-prover.org/) (>= 9.0) | Theorem prover — definitions and proofs |
| [Dune](https://dune.build/) (>= 3.21) | Build system — orchestrates Rocq, extraction, and Melange |
| [Melange](https://melange.re/) | OCaml-to-JavaScript compiler |
| [OCaml](https://ocaml.org/) (>= 5.2) | Intermediate language between Rocq and JS |
| [Vite](https://vite.dev/) | Frontend bundler and dev server |
| [React](https://react.dev/) | UI framework |

## Prerequisites

- **opam** — OCaml package manager ([install guide](https://opam.ocaml.org/doc/Install.html))
- **Node.js** (>= 20) and **npm**

## Setup

```bash
# 1. Create opam switch and install OCaml/Rocq dependencies
npm run setup
eval $(opam env)

# 2. Install JS dependencies
npm install

# 3. Build the Rocq proofs, extract, and compile to JS
npm run dune

# 4. Start the dev server
npm run dev
```

## Scripts

| Command | Description |
|---------|-------------|
| `npm run setup` | Create opam switch (OCaml 5.2.1) and install dune, melange, rocq-core, rocq-stdlib |
| `npm run dune` | Build Rocq theories, extract OCaml, compile to JS via Melange |
| `npm run dev` | Build + start Vite dev server |
| `npm run build` | Build + production Vite bundle |
| `npm run preview` | Preview the production build |
| `npm run clean` | Remove dune (`rocqducers/_build`) and Vite (`dist`) build artifacts |

## License

MIT
