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

### 2. SafeAsyncButton — Verified async button

→ [`docs/async-button.md`](./docs/async-button.md)

A button that tracks whether an async operation is in-flight. Clicks while loading are silently ignored — proved, not just guarded.

**State:** `Idle | Loading`
**Events:** `Click | Success | Failure`

**Proved invariant:**

| Property | Statement |
|----------|-----------|
| Click ignored while loading | `reducer Loading Click = Loading` |

### 3. TreeHistoryWrapper — Verified branching history tree

→ [`docs/undo-tree.md`](./docs/undo-tree.md)

A navigable history tree with `Leaf`, `Link`, and `Node` constructors, driven by a pluggable inner reducer (`inner : St -> E -> St`). Navigation is modelled as a zipper (focus + context breadcrumbs). Branching is first-class: `Do e` on a `Link` node archives the old branch in a `Node` rather than discarding it.

**State:** `cursor St = At (tree St) (ctx St) | Failed`
**Events:** `Do e` (apply inner reducer) `| GoLeft | GoRight | GoLink | GoUp`

**Proved invariants:**

| Property | Statement |
|----------|-----------|
| Left round-trip | `go_up (go_left (At (Node l r) k)) = At (Node l r) k` |
| Right round-trip | `go_up (go_right (At (Node l r) k)) = At (Node l r) k` |
| Do then undo | `focus_value (go_up (do_step (Leaf s) k e)) = Some s` |
| Do then undo/redo | `go_link (go_up (do_step (Leaf s) k e)) = do_step (Leaf s) k e` |
| Failed absorbs | `f Failed = Failed` for any navigation `f` |
| Failed step | `step Failed e = Failed` for any event `e` |
| Predicate correctness | `can_go_up (At f k) = true ↔ k ≠ Top` (and analogues for left/right/link) |

### 4. LinearHistoryWrapper — Verified linear undo/redo wrapper

→ [`docs/undo-list.md`](./docs/undo-list.md)

A generic higher-order wrapper that adds a proven-correct undo/redo timeline to **any** Rocq reducer. It is the linear-history counterpart to `UndoTree`. `Undo`/`Redo` on an empty stack return a `Failed` absorbing state rather than silently doing nothing.

**State:** `state St = Hist curr past future | Failed`
**Events:** `Do e` (inner event) `| Undo | Redo`

```
 Do e₁       Do e₂       Undo          Redo
s₀ ──────── s₁ ──────── s₂ ──────── s₁ ──────── s₂
              past=[s₀]   past=[s₁,s₀]  past=[s₀]   past=[s₁,s₀]
              future=[]   future=[]     future=[s₂]  future=[]
```

**Proved invariants:**

| Property | Statement |
|----------|-----------|
| Undo reverses Do | `current (step (step hs (Do e)) Undo) = current hs` |
| Redo reverses Undo | `p ≠ [] → step (step (Hist curr p fut) Undo) Redo = Hist curr p fut` |
| Do clears future | `future (step (Hist curr p fut) (Do e)) = []` |
| Do extends past | `past (step (Hist curr p fut) (Do e)) = curr :: p` |
| Undo/Redo at edges yield Failed | `step (init s) Undo = Failed` and `step (init s) Redo = Failed` |
| Undo/Redo preserve timeline length | `p ≠ [] → |past| + |future|` preserved by `Undo` (analogously for `Redo`) |
| `can_undo` is correct | `can_undo (Hist curr p fut) = true ↔ p ≠ []` |
| `can_redo` is correct | `can_redo (Hist curr p fut) = true ↔ fut ≠ []` |
| Failed absorbs | `step Failed e = Failed` for any `e` |

## Project structure

```
rocqducers/
├── docs/                         # Per-component documentation
│   ├── pick-list.md
│   ├── async-button.md
│   ├── undo-tree.md
│   └── undo-list.md
├── src/                          # React frontend
│   ├── main.jsx                  #   Entry point
│   ├── App.jsx                   #   Tab-based application shell
│   └── components/               #   View + wrapper components
│       ├── SafePickList.jsx
│       ├── PickListView.jsx
│       ├── SafeAsyncButton.jsx
│       ├── AsyncButtonView.jsx
│       ├── LinearHistoryWrapper.jsx
│       └── TreeHistoryWrapper.jsx
├── vite.config.js                # Vite config with Melange aliases
├── package.json                  # JS dependencies and scripts
└── rocqducers/                   # Dune project (Rocq + Melange)
    ├── dune-project
    ├── theories/
    │   ├── PickList.v            #   Pick list: state, events, reducer, proofs
    │   ├── AsyncButton.v         #   Async button: state machine and proof
    │   ├── UndoTree.v            #   Branching history tree: zipper, inner reducer, proofs
    │   ├── UndoList.v            #   Linear undo/redo wrapper: state, events, step, proofs
    │   └── dune
    ├── extraction/
    │   ├── Extract.v             #   Extraction directives
    │   └── dune
    ├── lib/
    │   ├── Rocqducers.ml         #   Melange wrapper (array interop, constructors)
    │   ├── Hooks.ml              #   React hooks (useReducer bindings, tree visualization)
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
