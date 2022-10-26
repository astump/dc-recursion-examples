## Installing Coq via Docker

See README.md

## Installing Coq & Coq Version(s) manually
Our library has been developed and tested on **Coq 8.15.2** (the most recent
version as of this writing).  **However,** versions
[8.13.2](https://github.com/coq/coq/releases/tag/V8.13.2) or
[8.13.0](https://github.com/coq/coq/releases/tag/V8.13.0) are needed for MetaCoq
(See paper, Section 6, Functorializing Datatypes). We recommend you install **8.13.2**.

The easiest way to install a specific Coq version is via
[opam](http://coq.io/opam/get_started.html). You can specifically install
**Coq 8.13.2** by running:

```
opam pin coq 8.13.2
```

## Quick-and-Easy Install

```
# Installs Coq version 8.13.2
opam pin coq 8.13.2

# Installs coq-idt as well as dependencies Coq-Equations & MetaCoq
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-idt

# Builds all .v files
make all
```


## Dependencies 
We have as dependencies:

- [Coq-Equations](https://github.com/mattam82/Coq-Equations)
- [MetaCoq](https://github.com/MetaCoq/metacoq)
- [coq-idt](https://github.com/ccyip/coq-idt)

But **coq-idt** depends on both **Coq-Equations** and **MetaCoq**, so it is
easiest to simply run...

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-idt
```

### Coq-Equations

We use [Coq-Equations](https://github.com/mattam82/Coq-Equations) as an
example of well-founded recursion (See Sections 2 and 3 of paper). 
The following files rely on **Coq-Equations**.

- [Nat/NatWf.v](./Nat/NatWf.v)
- [Wordsby/WordsByWf.v](./Wordsby/WordsByWf.v)
- [Wordsby/WordsByEq.v](./Wordsby/WordsByEq.v)
- [Rle/MapThroughWf.v](./Rle/MapThroughWf.v)
- [Rle/RleWf.v](./Rle/RleWf.v)

### MetaCoq
We use [MetaCoq](https://github.com/MetaCoq/metacoq) and
[coq-idt](https://github.com/ccyip/coq-idt). The following files rely on these
packages.

- [FunctorGenerators/Functorializer.v](./FunctorGenerators/Functorializer.v)
- [List/List.v](./List/List.v)
- [FunctorGenerators/Example.v](./FunctorGenerators/Example.v)
