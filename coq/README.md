# Coq mechanization (unbuilt copy)

These files are the Coq development that accompanies the paper: the product effect algebra with its
interaction axioms (`EffectAlgebra.v`), the core calculus (`Syntax.v`, `Typing.v`, `Semantics.v`) and
the metatheory (`Lemmas.v`, `Preservation.v`, `Progress.v`, `Safety.v`).

Status of this copy:

- **Not built here.** `coqc` is not installed on the machine that assembled this repository, so these
  files were not compiled for this demo. The paper states that the development was tested with Coq 8.18.
- **Not fully proved.** The files still contain `Admitted.` proofs (Lemmas.v: 2, Preservation.v: 1,
  Safety.v: 2 occurrences) and a few `Axiom`s for the abstract handler interface. The paper's mechanization
  appendix describes which obligations are open.
- The Python demo in `../runbookfx` does not depend on these files.

To try to build (Coq 8.18):

```sh
cd coq
coq_makefile -f _CoqProject -o Makefile
make
```
