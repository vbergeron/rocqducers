#!/usr/bin/env bash
set -euo pipefail

# 1. Create and configure the opam switch
if opam switch list --short | grep -qx rocqducers; then
  echo "Switch 'rocqducers' already exists, selecting it."
  opam switch rocqducers
else
  opam switch create rocqducers ocaml-base-compiler.5.2.1
fi
eval $(opam env)

# 2. Install OCaml/Rocq dependencies
opam install dune melange rocq-core rocq-stdlib
