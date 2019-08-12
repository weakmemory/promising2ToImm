### Installation of dependencies
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-promising-local -k git https://github.com/snu-sf/promising-opam-coq-archive
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-imm
```

One also needs to install [the `Promising2` package](https://github.com/snu-sf/promising-coq-private.git#v2).