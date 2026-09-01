# Robin1984

[![CI](https://github.com/kimihiro64/Robin1984/actions/workflows/ci.yml/badge.svg)](https://github.com/kimihiro64/Robin1984/actions/workflows/ci.yml)

Robin1984 is a Lean 4 formalization of Guy Robin's 1984 criterion for the
Riemann hypothesis. It proves that

```text
RiemannHypothesis <->
  forall n > 5040, sigma(n) < exp(gamma) * n * log(log n),
```

and proves the equivalent restriction to colossally abundant integers. The
repository also reconstructs the Nicolas--Landau oscillation argument used in
the converse implication and discharges the finite ranges with exact,
kernel-checked certificates.

This is a formalization of an equivalence criterion. It does **not** prove the
Riemann hypothesis.

## Advertised results

The small statement surface is [Challenge.lean](Challenge.lean). Palomar
Comparator checks the corresponding proved declarations in
[Solution.lean](Solution.lean):

- `Robin1984.robin_inequality_iff_riemannHypothesis` formalizes Robin's
  equivalence between the Riemann hypothesis and the strict divisor-sum
  inequality for every integer `n > 5040`.
- `Robin1984.riemannHypothesis_iff_colossallyAbundant_robin` proves that it is
  equivalent to verify the same inequality on colossally abundant integers
  above `5040`.

The Challenge definitions use Mathlib's divisor sum, Euler--Mascheroni
constant, real logarithm and real power, and `RiemannHypothesis` predicate.
There are no hidden hypotheses in either compared theorem.

## Mathematical organization

The proof development is organized by mathematical role:

- `Robin1984/Arithmetic/` defines Robin's inequality and elementary divisor
  and logarithmic bounds.
- `Robin1984/ColossallyAbundant/` develops marginal prime-power events,
  colossally abundant threshold profiles, and the reduction to CA integers.
- `Robin1984/Finite/` contains the exact startup proof, rational tangent rows,
  and kernel-checked finite certificates.
- `Robin1984/Analytic/` proves the explicit Mertens, prime-power and
  large-height estimates used under RH.
- `Robin1984/NicolasLandau/` reconstructs Nicolas's oscillation argument and
  Landau's positive-transform principle, including the weighted explicit
  formula and multiplicity-aware xi-zero sums.
- `Robin1984/Equivalence/` assembles the finite and analytic implications into
  the public equivalence theorem.
- `Robin1984/Helpers/` contains reusable event, threshold, state and
  prime-tower lemmas.

The finite proof has three visible parts. Exact prime factorizations cover
`5041 <= n < 7560`; a common colossally abundant tangent covers
`7560 <= n < 720720`; and 36 rational log-height rows cover the remaining
finite range through `log n = 74500`. The final retained row uses 105 bounded
prime-product blocks, each recomputed with `decide +kernel`.

## Provenance

Every owned Lean file has two separate module headers:

1. a content-reviewed provenance designation identifying whether the file
   directly formalizes Robin, Nicolas, Landau or another published source;
   records a standard mathematical formalization; or is primarily original to
   this Lean development; and
2. a human-readable description of the module's definitions, theorems and role
   in the proof.

The review methodology and category counts are in
[docs/PROVENANCE.md](docs/PROVENANCE.md). The machine-readable, path-exact
review record is [provenance/ledger.json](provenance/ledger.json). Provenance
was assigned from the contents and dependency role of each file, not from
filename or keyword matching.

Primary mathematical references include:

- Guy Robin, *Grandes valeurs de la fonction somme des diviseurs et hypothese
  de Riemann*, Journal de Mathematiques Pures et Appliquees 63 (1984),
  187--213.
- Jean-Louis Nicolas, [*Petites valeurs de la fonction
  d'Euler*](https://doi.org/10.1016/0022-314X(83)90055-0), Journal of Number
  Theory 17 (1983), 375--388.
- Edmund Landau, [*Uber einen Satz von
  Tschebyschef*](https://eudml.org/doc/158244), Mathematische Annalen 61
  (1905), 527--550.
- N. Costa Pereira, [*Estimates for the Chebyshev function
  psi(x)-theta(x)*](https://doi.org/10.2307/2007805), Mathematics of
  Computation 44 (1985), 211--221, with the 1987 corrigendum.

The complete structured bibliography and source relationships are recorded in
[formalization.yaml](formalization.yaml). The accompanying
[research paper](paper/robin1984-formalization.tex) presents the mathematical
proof, theorem-by-theorem correspondence, and original references.

## Trust and proof surface

The completed kernel axiom audit of both proved `Solution` declarations
returned exactly Lean's standard principles `propext`, `Classical.choice`,
and `Quot.sound`. Project proof sources contain no custom axiom declarations,
`sorry`, `admit`, or `native_decide`. The two deliberate `sorry`s in
`Challenge.lean` are statement holes required by the Challenge/Solution
comparison and are excluded from proof-status counts.

Finite certificates use ordinary `decide +kernel`, exact natural and rational
arithmetic, and proved soundness theorems. Comparator statement checking and
an independent NanoDa replay are configured as release gates in Linux CI.

## Lean version and dependencies

The project is pinned to Lean `v4.33.1`; see [lean-toolchain](lean-toolchain)
and [lake-manifest.json](lake-manifest.json). The proof depends on Mathlib and
`leancert` at pinned Git revisions. The analytic dependency
`PrimeNumberTheoremAnd` is fetched from a
[public fork](https://github.com/kimihiro64/PrimeNumberTheoremAnd/tree/robin1984-lean-4.33.1)
at the exact commit recorded in the manifest. That commit is based on upstream
commit `47fa48680663df41146704d02a5b092d792bd5b9` and contains the eight source
changes required for Lean 4.33.1 compatibility and the xi-divisor interfaces
used here. The added xi-divisor source retains Matteo Cipollina's authorship
and Apache-2.0 notice. A fresh Lake build reconstructs the patched dependency
from public Git history and needs no local or build-time patch step.

## Building

Install Git and `elan`, then ensure the pinned toolchain can be installed. On
Windows PowerShell:

```powershell
./scripts/bootstrap.ps1
lake exe cache get
lake build
```

On Linux or macOS:

```sh
lake update
lake exe cache get
lake build
```

The bare `lake build` command is the complete submission build. Its Lake-native
default target reads the checked-in 245-module topological order from
[`scripts/build-order.txt`](scripts/build-order.txt), schedules one module job
at a time, and finishes with `Solution`. Each Lean process is additionally
bounded to one internal task thread (`-j1`). This avoids overlapping the
largest finite-certificate elaborations without relying on an external build
runner, bootstrap patch, or machine-local state.

The finite certificates are deliberately substantial, so a fully uncached
build is dominated by their kernel reductions and can take considerably longer
than an incremental replay. It needs several GiB of free disk space and
adequate memory; no machine-independent cold-build duration is claimed.

## Checks

The repository's local checks are:

```powershell
./scripts/check-imports.ps1
./scripts/check-provenance.ps1
ruby ./scripts/validate-formalization.rb
```

The import linter rejects package and Mathlib-category umbrella imports,
duplicate or unresolved imports, non-canonical header ordering, and local
imports already supplied transitively by another direct import. The subsequent
Lean build separately verifies that every retained narrow import provides the
notation, tactics, instances, and declarations its file actually needs.

On a Linux host with Git, Go, Ruby, Rust/Cargo, Python 3 and Landrun support,
run the pinned Comparator and NanoDa toolchain with:

```sh
./scripts/verify-comparator.sh
```

The verifier first runs the repository's sequential default build, then checks
the advertised Challenge/Solution interface and replays the exported proof in
NanoDa. Linux CI passes the completed root `.lake/build` tree from its build job
to the documentation and Comparator jobs, avoiding redundant concurrent cold
builds while retaining the same checks on fresh standalone verifiers.
It pins the upstream `leanprover/lean4export` v4.33.0 source commit and compiles
that source unmodified with this repository's exact Lean v4.33.1 toolchain via
`ELAN_TOOLCHAIN`. This keeps the exporter compatible with the project's
`.olean` format without a fork or a machine-local patch.
The build job also caches that tree across workflow runs under a key derived
from every Lean source and build-defining file. A source change therefore
forces a new kernel build, while documentation-only changes can reuse the exact
Linux `.olean`s.

API documentation is checked by the Linux CI job and can be built from the
nested `docbuild` project on a host with a compatible native C toolchain:

```sh
cd docbuild
lake build Robin1984:docs
```

doc-gen4 includes every transitive import so that declaration links resolve.
The project therefore avoids umbrella `import Mathlib` declarations and CI
caches `docbuild/.lake/build`, allowing later documentation runs to update the
existing database rather than regenerate every imported module.
After doc-gen4 finishes, CI replaces its server-oriented root page with the
committed [offline landing page](assets/api-documentation-index.html) and
checks every link before uploading the site. The resulting `index.html` works
when the documentation archive is opened directly after extraction, without a
web server, iframe, external script or CDN.

The same CI run publishes the compiled research paper as the
`robin1984-research-paper` artifact. Its cached PDF is keyed only by
[`paper/robin1984-formalization.tex`](paper/robin1984-formalization.tex), so an
unchanged paper source reuses the same PDF instead of rebuilding it. The build
uses the source file's last Git change time as `SOURCE_DATE_EPOCH` and checks
that the final PDF has resolved references and exactly 11 pages.

Successful `main` builds publish an official GitHub release only after every
job has passed, including Comparator statement matching, NanoDa replay and
Lean's default-kernel replay. The committed [RELEASE_VERSION](RELEASE_VERSION)
file supplies the semantic version and must be bumped before a new release;
CI checks tag collisions before starting the long Lean build. The release
contains exactly the paper PDF, a compressed Ubuntu `.lake/build` tree, and a
ZIP of the complete offline-safe API site. The build archive includes the
project's licensing statement, while the documentation ZIP also includes the
licence and notice files for Lean and every pinned dependency represented in
the generated pages. A rerun at an already published commit verifies the
existing release instead of creating a duplicate.

## Production and review disclosure

The maintainer selected the mathematical goals, source correspondences and
public theorem statements. OpenAI Codex agents assisted with Lean proof
development, dependency analysis, refactoring, certificate organization,
documentation and mechanical audits. Lean's kernel and the independent
Comparator/NanoDa pipeline are correctness gates; they are not substitutes for
independent expert mathematical review. No such expert review is claimed.

## Licence and submission

The repository's original material is licensed under the
[Apache License 2.0](LICENSE) by default. The research paper is additionally
available under CC-BY-4.0, at the recipient's option. Mathematical provenance,
cited papers, external dependencies, file-specific exceptions, and generated
release archives are explained in [LICENSING.md](LICENSING.md); the project
licence does not relicense third-party material or claim ownership of the
underlying mathematical results.

Machine-readable citation information for this formalization is provided in
[CITATION.cff](CITATION.cff). The canonical source repository is
[kimihiro64/Robin1984](https://github.com/kimihiro64/Robin1984).

Palomar reviews a fixed commit from a public GitHub repository, identified by
its full 40-character SHA. See the current
[submission instructions](https://palomar-registry.org/how-to-submit) and use
the [Palomar submission form](https://submit.palomar-registry.org/) only after
all checks pass and the exact commit has been pushed.
