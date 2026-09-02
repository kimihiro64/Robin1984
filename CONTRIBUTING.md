# Contributing to Robin1984

Contributions that improve mathematical clarity, source fidelity, proof
robustness, build performance, or documentation are welcome. Please keep the
repository's public purpose narrow: Robin's 1984 criterion, its reduction to
colossally abundant integers, the finite certificates, and the Nicolas--Landau
and explicit analytic results required by those theorems.

## Proof requirements

- Do not add project-local axioms, bodyless constants, `sorry`, `admit`, or
  `native_decide` to the proof development. The two statement holes in
  `Challenge.lean` are the only intentional `sorry`s.
- Keep `#print axioms`, `#print`, `#check`, `#eval`, and other temporary
  diagnostics outside committed Lean sources.
- Prefer ordinary kernel-checked decisions and small proved certificate
  formats to opaque computation.
- Preserve the exact quantifiers and hypotheses of cited results. Numerical
  work may discharge an explicitly bounded finite domain; it may not replace
  an arbitrary mathematical parameter.

Substantive declarations must lie in the transitive constant dependency graph
of an advertised `Solution` theorem. The documented exceptions are the public
facades, Palomar Challenge/Solution/configuration files, and certificate data
needed to elaborate those proofs. A reusable lemma is welcome when it is
actually used; unused Lean code is not retained as a future convenience.

## Documentation and provenance

Every project-specific Lean file must contain:

1. exactly one provenance header that agrees with
   `provenance/ledger.json`; and
2. a separate human-readable module description explaining the mathematical
   contents and proof role.

Files below `Robin1984/Mathlib/` instead carry an upstream-ready Mathlib
copyright, Apache-2.0 licence and authorship header plus ordinary Mathlib module
documentation. They still require a reviewed entry in
`provenance/ledger.json`; the separate project provenance block is deliberately
omitted so the source can move upstream without editing its contents.

Provenance classifications must be assigned by reading the declarations and
their use in the final proof. Do not infer them from filenames, paths, or
keyword searches. When adding or materially changing a file, update the ledger
with its source, content-level review basis, and dependency status, then run
both repository prose checks.

Generated finite data must document its exact range, certificate meaning, and
kernel verification. Include or update the generation method when changing
certificate values.

## Mathlib candidate layer

Project-independent declarations intended for upstreaming belong below
`Robin1984/Mathlib/`, mirroring their proposed path after the prefix is
removed. They must use their proposed Mathlib namespace and may import only
narrow Mathlib, Batteries, Init, Lean, Std, or other candidate modules. They
may not import Robin1984 definitions, proof branches, `Challenge`, `Solution`,
or third-party project libraries.

Record every real candidate exactly once in `MATHLIB_PORTING.md`. The
`mathlib-ready` state requires an identified destination, Mathlib-style source,
no project dependency or proof placeholder, a clean boundary audit, and a
focused build against the pinned Mathlib revision. Existing project names may
be preserved by thin compatibility declarations outside the candidate layer.

## Dependencies

The Lean toolchain and every Git dependency are pinned. Do not update a pin
without rebuilding the complete project and reviewing the effect on
Comparator, NanoDa and doc-gen4.

The required `PrimeNumberTheoremAnd` changes live in the public
`kimihiro64/PrimeNumberTheoremAnd` fork. The root Lakefile pins one exact fork
commit derived from the documented upstream base. Do not make an unrecorded
edit under `.lake/packages` or introduce a build-time patch hook. Any future
dependency change must first be committed publicly, replay-checked against its
recorded upstream base, pinned by full SHA, and verified from a fresh Lake
checkout.

The default `lake build` target follows `scripts/build-order.txt`: the exact
250-module dependency closure ending in `Solution`. If a source import or
dependency update changes that closure, update the file in topological order,
check for missing or duplicate modules, and verify that `Solution` remains the
last entry. Do not replace the Lake-native sequential target with an
uncommitted local runner; the submitted repository must impose its own safe
certificate build order.

## Local checks

On Windows PowerShell:

```powershell
./scripts/bootstrap.ps1
./scripts/check-imports.ps1
./scripts/check-provenance.ps1
lake exe cache get
lake build
ruby ./scripts/validate-formalization.rb
```

Before a release or Palomar submission, also run the Linux CI documentation
job and execute `./scripts/verify-comparator.sh` on a host that satisfies its
Git, Go, Rust/Cargo, Python, Ruby, and Landrun requirements.

The final change must leave the advertised `Solution` declarations dependent
only on `propext`, `Classical.choice`, and `Quot.sound`, as confirmed by a
temporary kernel axiom audit and the Comparator/NanoDa checks.

## Licence

Contributions to this repository are accepted under the repository's
Apache-2.0 licence unless explicitly agreed and marked otherwise. Preserve all
applicable third-party notices and submit only material you are authorized to
license. The paper's additional CC-BY-4.0 option and the precise treatment of
mathematical provenance, dependencies, and generated archives are documented
in [LICENSING.md](LICENSING.md).
