# Rocqducers

**React components powered by formally verified reducers.**

Rocqducers bridges the [Rocq proof assistant](https://rocq-prover.org/) (formerly Coq) and [React](https://react.dev/) by compiling verified state machines into JavaScript via [Melange](https://melange.re/). Invariants are proved once in Rocq and enforced at compile time — the generated code is guaranteed to uphold them at runtime.

## How it works

```
  Rocq            Extraction         Melange           Vite
┌───────────┐    ┌──────────────┐    ┌───────────┐    ┌──────────┐
│ PickList.v│───▶│  PickList.ml │───▶│PickList.js│───▶│  React   │
│  proofs   │    │  (OCaml)     │    │  (ES6)    │    │  App     │
└───────────┘    └──────────────┘    └───────────┘    └──────────┘
    ▲                                      │
    │  Invariants proved:                  │  useReducer(reducer, ...)
    │  • picked list always non-empty      │
    │  • total item count is constant      │
    └──────────────────────────────────────┘
```

1. **Rocq** — Definitions, reducer logic, and invariant proofs live in `.v` files under `rocqducers/theories/`. The type system enforces that every code path preserves the stated properties.

2. **Extraction** — Rocq's extraction mechanism translates the verified definitions into OCaml. Inductive types like `list`, `nat`, and `option` are mapped to their OCaml counterparts for efficient runtime representation. Configuration lives in `rocqducers/extraction/Extract.v`.

3. **Melange** — The extracted OCaml is compiled to ES6 JavaScript modules by [Melange](https://melange.re/). A thin wrapper (`rocqducers/lib/Rocqducers.ml`) adds array conversion helpers so the JS consumer works with plain arrays instead of linked lists.

4. **Vite + React** — The generated JS is imported like any other module. React's `useReducer` hook accepts the verified reducer directly — the proof-carrying state machine drives the UI.

## Project structure

```
rocqducers/
├── src/                          # React frontend
│   ├── main.jsx                  #   Entry point
│   ├── App.jsx                   #   Application shell
│   └── SafePickList.jsx          #   Component using the verified reducer
├── vite.config.js                # Vite config with Melange aliases
├── package.json                  # JS dependencies and scripts
└── rocqducers/                   # Dune project (Rocq + Melange)
    ├── dune-project
    ├── theories/
    │   ├── PickList.v            #   State, events, reducer, proofs
    │   └── dune
    ├── extraction/
    │   ├── Extract.v             #   Extraction directives
    │   └── dune
    ├── lib/
    │   ├── Rocqducers.ml         #   Melange wrapper (array interop)
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
# 1. Create and configure the opam switch
opam switch create rocqducers ocaml-base-compiler.5.2.1
eval $(opam env)

# 2. Install OCaml/Rocq dependencies
opam install dune melange rocq-core rocq-stdlib

# 3. Install JS dependencies
npm install

# 4. Build the Rocq proofs, extract, and compile to JS
npm run dune

# 5. Start the dev server
npm run dev
```

## Scripts

| Command | Description |
|---------|-------------|
| `npm run dune` | Build Rocq theories, extract OCaml, compile to JS via Melange |
| `npm run dev` | Build + start Vite dev server |
| `npm run build` | Build + production Vite bundle |
| `npm run preview` | Preview the production build |

## License

MIT
