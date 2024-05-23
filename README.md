# Promising 2.0: Global Optimizations in Relaxed Memory Concurrency

Sung-Hwan Lee, Minki Cho, Anton Podkopaev, Soham Chakraborty, Chung-Kil Hur, Ori Lahav, Viktor Vafeiadis.

Proceedings of the 41st annual ACM SIGPLAN conference on Programming Languages Design and Implementation ([PLDI 2020](https://conf.researchr.org/home/pldi-2020))

Please visit the [project website](https://sf.snu.ac.kr/promising2.0/) for more information.

This repository contains Coq code of Promising 2.0 to IMM compilation correctness proof
supplementing the paper *Promising 2.0: Global Optimizations and Relaxed Memory Concurrency*.

### Requirements
* [Coq](https://coq.inria.fr)
* [Our fork](https://github.com/weakmemory/hahn) of [the Hahn library](https://github.com/vafeiadis/hahn)
* [HahnExt library](https://github.com/weakmemory/hahnExt)
* [IMM library](https://github.com/weakmemory/imm)
* [The Coq supplementary library w/ basic data types](https://github.com/snu-sf/promising-lib)
To check precise requirements with version numbers, please, check [the Nix configuration file](.nix/config.nix).

### Building via Nix (preferred and mainly supported way)
First, you need to install Nix (see https://nixos.org/download.html) and set-up Nix as recommended by [Coq Nix Toolbox](https://github.com/coq-community/coq-nix-toolbox).
That is, run
```
nix-env -iA nixpkgs.cachix && cachix use coq && cachix use coq-community && cachix use math-comp
```
in order to use binary caches from recognized organizations.
Additionally, we recommend add our binary cache with IMM and related packages as well:
```
cachix use weakmemory
```
Then, you may just run `nix-build` in the root folder of the project to build it.
Alternatively, you may run `nix-shell` and then, in the Nix-configured environment, run `make -j`.

#### Working on the project in VS Code
You may use the [Nix Environment Selector](https://marketplace.visualstudio.com/items?itemName=arrterian.nix-env-selector) plugin in VS Code for it to use proper configuration.
Alternatively, 
you may run `nix-shell` in the root of the project and then `code .`--VSCoq or CoqLSP should be able to pick up the environment.

## (OUT-DATED) Build w/ opam

- Requirement: [Coq](https://coq.inria.fr/download), opam, Make, Rsync.

- Installing dependencies with opam

        opam repo add coq-released https://coq.inria.fr/opam/released
        opam remote add coq-promising -k git https://github.com/snu-sf/promising-opam-coq-archive
        opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
        opam install coq-paco.2.0.3 coq-sflib coq-promising-lib coq-promising2 coq-imm

- Building the project

        git clone https://github.com/weakmemory/promising2ToImm.git
        cd promising2ToImm 
        make -j build

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or [CoqIDE](https://coq.inria.fr/download).
  Note that `make` creates `_CoqProject`, which is then used by ProofGeneral and CoqIDE. To use it:
    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change `ignored` to `appended to arguments`.

## References
- `src/lib` contains definitions and lemmas about relations, IMM, and Promising 2.0's memory.
- `src/promise_basics` contains definitions and lemmas about Promising 2.0.
- `src/traversal` contains definitions related to the IMM traversal as it is presented in Podkopaev et al. POPL19.
- `src/ext_traversal` contains definitions related to the extended IMM traversal with reservations.
- `src/simulation` contains definitions and lemmas related to certification graph's construction and the simulation relation.
- `src/simulation_steps` contains definitions and lemmas related to the simulation step lemma (`SimulationPlainStep.v`).
- `src/compilation` contains the main theorem of compilation (`PromiseToimm_s.v`).
