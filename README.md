This repository contains Coq code of Promising 2.0 to IMM compilation correctness proof
supplementing the paper *Promising 2.0: Global Optimizations and Relaxed Memory Concurrency*.

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
- `src/lib` contains definitions and lemmas about relations, IMM, and Promising2's memory.
- `src/promise_basics` contains definitions and lemmas about Promising2.
- `src/traversal` contains definitions related to the IMM traversal as it is presented in Podkopaev et al. POPL19.
- `src/ext_traversal` contains definitions related to the extended IMM traversal with reservations.
- `src/simulation` contains definitions and lemmas related to certification graph's construction and the simulation relation.
- `src/simulation_steps` contains definitions and lemmas related to the simulation step lemma (`SimulationPlainStep.v`) and
  the main theorem of compilation (`PromiseToimm_s.v`).
