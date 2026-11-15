# Sumatra

[![Build](https://github.com/dzackon/sumatra/actions/workflows/build.yml/badge.svg)](https://github.com/dzackon/sumatra/actions/workflows/build.yml)
[![License](https://img.shields.io/github/license/dzackon/sumatra)](LICENSE)
[![CPP 2027 artifact](https://img.shields.io/badge/CPP_2027-artifact-blue)](https://doi.org/10.5281/zenodo.22696853)

Sumatra (**SU**bstructural **M**eta-theory with **A**djoin**T** **R**esource
**A**nnotations) is a Rocq library for mechanizing substructural logics and type
systems. It supplies infrastructure for contexts, resource splitting, renaming,
and substitutions, as well as proof tactics. The user supplies the object
language and its judgments.

This library is the subject of the paper "Sumatra: Mechanizing Substructural
Meta-theory in Rocq" (CPP 2027).

## Installation

Sumatra requires Rocq 9.0 or later together with Stdlib;
the sources have been checked with Rocq 9.3.0 and Stdlib 9.2.0. The
required Autosubst support files are included in [autosubst/](autosubst), so no
separate Autosubst installation is needed.

With your intended opam switch selected, run the following from the
repository root:

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
eval "$(opam env)"
opam install .
```

Opam installs the dependencies, generates a Makefile from
[_RocqProject](_RocqProject), builds the library and case studies, and installs
them in the active switch's `lib/coq/user-contrib`. Other developments using
that switch can then import Sumatra without adding local load paths.

### Building from source

To build in place, install just Sumatra's dependencies
and generate the Makefile.

```sh
opam install . --deps-only
rocq makefile -f _RocqProject -o Makefile
make # or make -j <number-of-cores>
```

To build a single module and its dependencies instead, run, for example,
`make src/Contexts.vo`.

Optional commands:

```sh
make install
make html
make clean
```

`make install` installs into the active Rocq installation's `user-contrib`.
`make html` produces browsable documentation in `html/`, and `make clean`
removes build products.

### Interactive use

Compiled files sit beside their sources. Open the repository root in an editor
with Rocq support and use `_RocqProject` for the load paths. Configure the editor
to use the same opam switch as the command-line build.

## Using the library

Everything installs under one logical namespace, `Sumatra`:

- `Sumatra` — the library itself
- `Sumatra.Autosubst` — the bundled Autosubst support files
- `Sumatra.CaseStudies.<Study>` — each case study

The complete public interface is available through `Sumatra.All`:

```coq
From Sumatra Require Import All.
```

It imports the whole library, including standard instances and tactics, and
re-exports `fin` and the other scoped-syntax definitions.
For most developments, it is enough to import only the modules one
uses. The principal modules are outlined in [src/README.md](src/README.md).

## License

Sumatra is distributed under the ISC license; see [LICENSE](LICENSE).
