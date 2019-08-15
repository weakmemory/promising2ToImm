## Installation of dependencies
You can either run `configure', or to execute the following commands:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-promising-local -k git https://github.com/snu-sf/promising-opam-coq-archive
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam pin add coq-promising2 git@github.com:snu-sf/promising-coq-private.git#v2
opam install coq-imm coq-promising2
```

## Building the project
Run `make -j -k`.

## The project structure
- `src/ext_traversal` contains definiitions related to IMM traversal with reservations.
  Reservations represent half-message in Promising2
- `src/promise_basics` contains definitions and lemmas about Promising2.