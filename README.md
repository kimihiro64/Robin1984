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

It also formalizes Lagarias's 2001 elementary criterion, proving that the
Riemann hypothesis is equivalent to
`sigma(n) <= H_n + exp(H_n) * log(H_n)` for every positive integer `n`.

This is a formalization of an equivalence criterion. It does **not** prove the
Riemann hypothesis.

## Advertised results

[Challenge.lean](Challenge.lean) contains the Mathlib-only statements.
[Solution.lean](Solution.lean) proves the classical, Dirichlet GRH and
Dedekind ERH equivalences included in the Palomar Comparator configuration.

- `Robin1984.robin_inequality_iff_riemannHypothesis` formalizes Robin's
  equivalence between the Riemann hypothesis and the strict divisor-sum
  inequality for every integer `n > 5040`.
- `Robin1984.riemannHypothesis_iff_colossallyAbundant_robin` proves that it is
  equivalent to verify the same inequality on colossally abundant integers
  above `5040`.
- `Robin1984.riemann_hypothesis_iff_lagarias_elementary_criterion` formalizes
  Lagarias's elementary criterion in terms of harmonic numbers.

The Challenge definitions use Mathlib's divisor sum, Euler--Mascheroni
constant, harmonic numbers, real logarithm and real power, and
`RiemannHypothesis` predicate.

## Dirichlet GRH, Dedekind ERH, and Grand RH

### The corrected ideal Robin inequality

Let $K$ be a number field with ring of integers $\mathcal O_K$ and
discriminant $D_K$. Write $\kappa_K=\operatorname{Res}_{s=1}\zeta_K(s)$
for the residue of its Dedekind zeta function, and let $\gamma$ be the
Euler–Mascheroni constant. For a nonzero integral ideal $\mathfrak a$,
the absolute norm and the ideal divisor sum are

```math
N\mathfrak a=\#(\mathcal O_K/\mathfrak a),
\qquad
\sigma_K(\mathfrak a)=
  \sum_{\substack{\mathfrak d\mid\mathfrak a\\
                   \mathfrak d\ \mathrm{integral}}}N\mathfrak d.
```

The corrected inequality for $K$ asks for an integer cutoff $A_K$
such that every nonzero integral ideal $\mathfrak a$ with
$N\mathfrak a\ge A_K$ satisfies

```math
\frac{\sigma_K(\mathfrak a)}{N\mathfrak a}
\ \le\
e^\gamma\kappa_K
\left(
  \log\log N\mathfrak a+
  \frac{12+3\log|D_K|}{\sqrt{\log N\mathfrak a}}
\right).
```

All logarithms are natural. The cutoff can depend on $K$.

- **Dirichlet GRH.** For every integer $m\ge1$ and every Dirichlet character
  $\chi$ modulo $m$, every zero of $L(s,\chi)$ in $0<\Re s<1$ lies on
  $\Re s=1/2$ if and only if the corrected ideal Robin inequality holds
  in every cyclotomic field $K=\mathbb Q(\zeta_m)$, where $\zeta_m$ is a
  primitive $m$-th root of unity.
- **Dedekind ERH.** For every number field $K$, every zero of $\zeta_K(s)$
  in $0<\Re s<1$ lies on $\Re s=1/2$ if and only if the corrected ideal
  Robin inequality holds in every number field $K$.

### Grand RH and the triangular prime-power inequality

Grand RH is the assertion that every nontrivial zero of every standard
automorphic $L(s,\pi)$ has real part $1/2$. Here $\pi$ ranges over unitary
cuspidal representations of $\mathrm{GL}_n(\mathbb A_K)$ for all $n\ge1$
and all number fields $K$. The nontrivial zeros are the zeros of the
pole-cleared completed standard function.

For each $K$, include the test $Z=\zeta_K$. For every $\pi$ other than a
pure norm character $|\cdot|_{\mathbb A_K}^{it}$ of $\mathrm{GL}_1$,
include the paired test $Z=L(s,\pi)L(s,\widetilde\pi)$, where
$\widetilde\pi$ is the contragredient of $\pi$. The $Z=\zeta_K$ test
covers the pure norm characters because their standard functions are
$\zeta_K(s+it)$.

For a nonzero prime ideal $\mathfrak p$ write $q=N\mathfrak p$.
The real coefficients $b_{\mathfrak p,j}(Z)$ for integers $j\ge1$
are those of the logarithmic derivative

```math
-\frac{Z'(s)}{Z(s)}
 =\sum_{\mathfrak p}\sum_{j\ge1}b_{\mathfrak p,j}(Z)q^{-js},
\qquad \Re s>1.
```

For $Z=\zeta_K$, $b_{\mathfrak p,j}(Z)=\log q$. For a pair, write
$L_{\mathfrak p}(s,\pi)=\prod_{k=1}^n(1-\alpha_{\mathfrak p,k}q^{-s})^{-1}$,
using zero parameters as needed at ramified primes. Then

```math
b_{\mathfrak p,j}(Z)=2\log q\,
    \Re\!\left(\sum_{k=1}^n\alpha_{\mathfrak p,k}^{\,j}\right).
```

Let $m_Z$ be the pole order of $Z$ at $1$, equal to $1$ for the
Dedekind test and $0$ for a paired test. Grand RH is equivalent to
the following bound for every test $Z$.

```math
R_Z(x)
 =\frac{m_Z x}{2}
  -\sum_{\substack{\mathfrak p,\ j\ge1\\ q^j\le x}}
    b_{\mathfrak p,j}(Z)\left(1-\frac{q^j}{x}\right)
 \ \le\ C_Z\sqrt{x}
\qquad (x\ge X_Z).
```

Each $Z$ has its own constants $C_Z\in\mathbb R$ and $X_Z\ge1$, and
the bound holds for every real $x\ge X_Z$. For $Z=\zeta_K$, the triangular
bound and the corrected ideal Robin inequality are equivalent for that
field. Taking all fields gives Dedekind ERH. Taking all cyclotomic fields
gives Dirichlet GRH.

### Proofs and verification

The [research paper](paper/robin1984-formalization.tex) proves all three
equivalences in ordinary mathematics and gives the citations for the
automorphic analytic inputs. The classical Robin, colossally abundant,
and Lagarias arguments appear in its appendices.

Lean verifies both corrected ideal equivalences and the triangular
equivalence for a family supplied with `HasStandardAutomorphicAnalytics`.
It constructs the standard completed rank-one family over every number
field, including unitary norm twists. Its critical-line assertion is
equivalent to the Dedekind triangular bound for the field together with
the paired triangular bound for every unitary Hecke character nontrivial
on norm-one idele classes.

For higher ranks, Lean proves that the self-dual Fourier transform of a
Schwartz rectangle is a finite sum of Schwartz rectangles. The invertible
theta integrals for the original test and its Fourier transform both decay
as $O(e^{-\beta t})$ for every $\beta>0$ as $t\to+\infty$, given a measurable
fundamental domain, bi-invariant Haar measure, and square-integrable quotient
functions. [Fourier closure and dual decay](Robin1984/GRH/GodementJacquetThetaDualDecay.lean)

The full rational theta series, including singular matrices, has the
bound
$$
\sum_{P\in M_n(K)} |\Phi(A^{-1}z_tPB)|
\le C_\Phi(t) H_L(A)^m H_R(B)^m,\qquad
m>\dim_{\mathbb R} M_n(K_\infty).
$$
Here $H(U,V)=\max(1,\|X\mapsto U_\infty X V_\infty\|_{\rm op})$ on the
archimedean matrix coordinates. The weights are
$H_L(A)=H(\delta_A A,1)$ and $H_R(B)=H(1,B^{-1}\delta_B)$, where the
nonzero integers $\delta_A,\delta_B$ clear the finite entries of $A$
and $B^{-1}$. The factor $C_\Phi(t)$ depends on the test and $t$.
The same two weights apply to the Fourier dual.

Lean proves cancellation of the singular terms for both tests when
$c,f$ have zero mean and vanishing unipotent periods and both weighted
absolute values $|u|H_L^m,|u|H_R^m$ belong to $L^1(D,\mu)$ for
$u=c,f$. The resulting identities give entire Mellin continuation and
reflection under the square-integrability assumptions above. The
higher-rank instantiation needs the weighted bounds for actual
cuspidal data and the local and global Euler products.
[Weighted theta cancellation](Robin1984/GRH/GodementJacquetThetaWeightedCancellation.lean)
[Generalized criteria](docs/GRH.md)

## Critical-line zeros and multiplicity

For a carrier $F$, let $A_F(w,R,\eta)$ be the planar area of
$\{z : |z-w|<R,\ |F(z)|\le \eta\}$. The local test for a prescribed
maximum order $B\ge 0$ is

```math
\operatorname{ord}_w F\le B
\quad\Longleftrightarrow\quad
\exists R>0,\quad A_F(w,R,\varepsilon^{B+1})=o(\varepsilon^2)
\quad(\varepsilon\downarrow0).
```

Use $B=0$ off the critical line. On the line, for a holomorphic
factorization $F=U\prod_j F_j^{e_j}$ with $U$ nowhere zero, use
$B=\sum_j e_j b_j(w)$ for specified lower bounds $b_j(w)$ on the factor
orders. The basic choice counts one per factor vanishing at $w$, with its
exponent $e_j$. This tests for no excess order in the factors and counts
shared zeros with their weights. The Robin or triangular criterion can
supply the location condition instead, so the area test only needs points
on the line.

The arithmetic carriers are $L(s,\chi)/L(s+1,\chi)$,
$\zeta_K(s)/\zeta_K(s+1)$, and $Z_\pi(s)/L(s+1,\pi)$ with the individual
pole-cleared completion $Z_\pi$. The first two have the coefficients
$\chi(n)\varphi(n)/n$ and $\varphi_K(\mathfrak a)/N\mathfrak a$ in their
Dirichlet series, where $\varphi_K(\mathfrak a)=N\mathfrak a\prod_{\mathfrak p\mid\mathfrak a}(1-(N\mathfrak p)^{-1})$.
The [paper](paper/robin1984-formalization.tex) gives the automorphic local factors,
the holomorphy requirement for a full Artin factorization, and the treatment of
intrinsic central zeros. This extension is a mathematical criterion.

The same triangular remainder $R_Z$ also supplies an arithmetic
multiplicity test. Once the square-root bound holds, put
$w=\tfrac12+i\gamma$, $s=w+\delta$. The order of the pole-cleared
function in the triangular Mellin formula is the limit, as
$\delta\downarrow0$, of

```math
D_Z(w,\delta)=\delta\,s(s+1)\int_1^\infty R_Z(x)x^{-s-1}\,dx.
```

This order is at most $B$ exactly when $\Re D_Z(w,\delta)\le B+\tfrac12$
for every sufficiently small $\delta>0$. The paper gives the completion
factor correction when that factor has nonzero order at $w$.

### Global multiplicity test

There is also a test that combines all ordinates in one inequality.
Use $A(t)=e^{-t/2}R_Z(e^t)$ for $t\ge 0$ and $A(t)=0$ for $t<0$.
For $a=1,2$ convolve $A$ with the integrable kernel
$k_a=(\frac{d}{dt}+\frac12)(\frac{d}{dt}+\frac32)g_a$, where
$g_a(t)=e^{-t^2/(4a)}/\sqrt{4\pi a}$. Write $H_a=k_a*A$ and let
$\widetilde H_a$ remove the mean Fourier coefficients at any specified
exceptional ordinates. Under the square-root bound, the test is

```math
\lim_{T\to\infty}\frac1T\int_0^T|\widetilde H_1(t)|^2\,dt
\ \le\ \limsup_{t\to\infty}\Re\widetilde H_2(t).
```

The difference of the two sides is the sum of
$m_\gamma(m_\gamma-1)e^{-2\gamma^2}$ over the retained ordinates, where
$m_\gamma$ is the order in the function used by the Mellin formula.
This detects any repeated zero. Use the individual factors and sum
with their factorization weights for a criterion that allows repeated
zeros forced by the product. The [paper](paper/robin1984-formalization.tex)
proves the inequality criterion, including exact order constraints
at exceptional ordinates.

### Four conditional headline equivalences

Assume the corresponding location hypothesis in each statement.
Write $\mathcal E$ for the global mean-square limit and $\mathcal S$
for the limit superior defined above.

| Hypothesis | Multiplicity requirement equivalent to the global inequality |
| --- | --- |
| RH | All nontrivial zeros of $\zeta$ are simple iff $\mathcal E\le\mathcal S$ for $\zeta$. |
| Dirichlet GRH | Each Dirichlet $L$-function has simple nontrivial zeros iff $\mathcal E\le\mathcal S$ for each individual character. |
| Dedekind ERH | For the specified holomorphic factorization $\zeta_K=U_K\prod_jL_{K,j}^{e_{K,j}}$, the order at each zero is exactly $\sum_{j:L_{K,j}(w)=0}e_{K,j}$ iff $\sum_j e_{K,j}\mathcal E_j\le\sum_j e_{K,j}\mathcal S_j$ for each field in the test. |
| Grand RH | Every individual standard completion has simple zeros outside its prescribed exceptions and the stated exact orders at specified exceptions iff $\mathcal E+\mathcal P\le\mathcal S$ for each individual representation. The term $\mathcal P$ is the sum of squared errors in the prescribed orders, weighted by the Gaussian coefficients. |

The [research paper](paper/robin1984-formalization.tex) gives the proofs.
The [Challenge](Challenge.lean) and [Solution](Solution.lean) contain the
following multiplicity equivalences.

| Hypothesis | Lean declaration |
| --- | --- |
| RH | `riemannRH_iff_globalPrimePowerMultiplicityInequality` |
| Dirichlet GRH | `dirichletGRH_iff_globalPrimePowerMultiplicityInequality` |
| Dedekind ERH | `dedekindERH_iff_globalPrimePowerMultiplicityInequality` |
| Grand RH for a supplied standard family | `grandRH_iff_globalPrimePowerMultiplicityInequality` |

The Dedekind proof takes the positive holomorphic factorization and the
analytic data of its factors as inputs. The Grand RH proof takes the
individual standard Euler coefficients and Gamma completions through
`HasStandardMultiplicityAnalytics`. The paper supplies the standard
automorphic inputs from the cited theorems. Instantiating those inputs in
Lean over the full automorphic family remains in progress.

## Mathematical organization

The proof development is organized by mathematical role:

- `Robin1984/Arithmetic/` defines Robin's inequality and elementary divisor
  and logarithmic bounds.
- `Robin1984/ColossallyAbundant/` develops marginal prime-power events,
  colossally abundant threshold profiles, and the reduction to CA integers.
- `Robin1984/Finite/` contains the exact startup proof, rational tangent rows,
  and kernel-checked finite certificates.
- `Robin1984/Lagarias/` proves the harmonic comparison, finite range, and the
  forward and converse bridges for Lagarias's elementary criterion.
- `Robin1984/Analytic/` proves the explicit Mertens, prime-power and
  large-height estimates used under RH.
- `Robin1984/NicolasLandau/` reconstructs Nicolas's oscillation argument and
  Landau's positive-transform principle, including the weighted explicit
  formula and multiplicity-aware xi-zero sums.
- `Robin1984/Equivalence/` assembles the finite and analytic implications into
  the public equivalence theorem.
- `Robin1984/Helpers/` contains reusable event, threshold, state and
  prime-tower lemmas.
- `Robin1984/Mathlib/` contains project-independent modules maintained in their
  proposed upstream namespaces and source format.

The finite proof has three visible parts. Exact prime factorizations cover
`5041 <= n < 7560`; a common colossally abundant tangent covers
`7560 <= n < 720720`; and 36 rational log-height rows cover the remaining
finite range through `log n = 74500`. The final retained row uses 105 bounded
prime-product blocks, each recomputed with `decide +kernel`.

## Mathlib candidate layer

[`MATHLIB_PORTING.md`](MATHLIB_PORTING.md) inventories the reusable modules
maintained for possible upstreaming. The current candidate layer contains nine
modules covering Abel identities, `Nat.lcmUpto` support, finite Mertens
products, exact rational logarithm bounds, one-sided Omega transfer, absolute
tail reweighting, nonnegative-MGF continuation, and positive-real zeta
nonvanishing. Each uses its proposed upstream namespace at a path mirroring
its intended Mathlib destination. Existing project declarations and the
advertised downstream API retain their original names.

The import audit enforces a one-way boundary: candidates may depend only on
narrow Mathlib-family modules or other candidates, never on Robin1984 proof
code or third-party project libraries. It also checks Mathlib source headers,
absence of the project namespace from candidate bodies, one manifest row per
candidate, and a recognized readiness state. All nine candidates build
directly against the pinned Mathlib revision before the complete project.

## Provenance

Every project-specific Lean file has two separate module headers:

1. a content-reviewed provenance designation identifying whether the file
   directly formalizes Robin, Nicolas, Landau or another published source;
   records a standard mathematical formalization; or is primarily original to
   this Lean development; and
2. a human-readable description of the module's definitions, theorems and role
   in the proof.

Mathlib candidate source instead uses Mathlib's upstream-ready copyright,
licence, authorship and module-documentation header while retaining an exact
reviewed entry in the repository provenance ledger.

The review methodology and category counts are in
[docs/PROVENANCE.md](docs/PROVENANCE.md). The machine-readable, path-exact
review record is [provenance/ledger.json](provenance/ledger.json). Provenance
was assigned from the contents and dependency role of each file, not from
filename or keyword matching.

Primary mathematical references include:

- Jeffrey C. Lagarias, [*An Elementary Problem Equivalent to the Riemann
  Hypothesis*](https://doi.org/10.1080/00029890.2002.11919883), American
  Mathematical Monthly 109 (2002), 534--543; submitted in 2001.
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

The kernel axiom audit of the five Comparator `Solution` declarations
returned exactly Lean's standard principles `propext`, `Classical.choice`,
and `Quot.sound`. Project proof sources contain no custom axiom declarations,
`sorry`, `admit`, or `native_decide`. The deliberate `sorry`s in `Challenge.lean` mark statements and are excluded
from proof-status counts. The Comparator manifest lists the declarations
with audited proofs.

Finite certificates use ordinary `decide +kernel`, exact natural and rational
arithmetic, and proved soundness theorems. Comparator statement checking and
an independent NanoDa replay are configured as release gates in Linux CI.

## Lean version and dependencies

The project is pinned to Lean `v4.33.1`; see [lean-toolchain](lean-toolchain)
and [lake-manifest.json](lake-manifest.json). The proof depends on Mathlib and
`leancert` at pinned Git revisions. The analytic dependency
`PrimeNumberTheoremAnd` is fetched from a temporary
[public compatibility and extension fork](https://github.com/kimihiro64/PrimeNumberTheoremAnd/tree/robin1984-lean-4.33.1)
at the exact commit recorded in the manifest. That commit is based on upstream
commit `47fa48680663df41146704d02a5b092d792bd5b9` and contains the Lean 4.33.1
proof repairs plus the xi-divisor and Mertens interfaces used here. As of
September 2026, [upstream `main`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/lean-toolchain)
still declares Lean 4.32.2 and does not contain the required xi-divisor source.
The fork can be removed after a compatible upstream revision contains or
replaces those interfaces and the full build and Comparator/NanoDa checks pass.
The added xi-divisor source retains Matteo Cipollina's authorship and
Apache-2.0 notice. A fresh Lake build reconstructs the dependency from public
Git history and needs no local or build-time patch step.

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

The bare `lake build` command is the complete submission build. Its default
targets are `Challenge` and `Solution`; they use Lake's ordinary scheduler, so
unrelated modules can build concurrently. The memory-intensive Robin and
Lagarias certificate modules encode their order as import-dependency ladders,
keeping those
elaborations sequential in both repository and consumer builds. Each Lean
process is additionally bounded to one internal task thread (`-j1`).

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
imports already supplied transitively by another direct import. It also
enforces the Mathlib candidate boundary and inventory. The subsequent Lean
build separately verifies that every retained narrow import provides the
notation, tactics, instances, and declarations its file actually needs.

On a Linux host with Git, Lake, Go, Rust/Cargo, Python 3 and Landrun support,
run the pinned Comparator and NanoDa toolchain with:

```sh
./scripts/verify-comparator.sh
```

The verifier first runs the repository's sequential default build. Comparator
then exports the Challenge and Solution environments separately, compares each
advertised theorem statement and the declarations used by that statement,
audits the Solution proof bodies against the three permitted standard axioms,
and replays the export through Lean's default kernel. The configuration has no
definition holes and requires a second replay through the independent NanoDa
kernel. Linux CI passes the completed root `.lake/build` tree from its build job
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


The same CI run publishes the compiled research paper as the
`robin1984-research-paper` artifact. Its cached PDF is keyed only by
[`paper/robin1984-formalization.tex`](paper/robin1984-formalization.tex), so an
unchanged paper source reuses the same PDF instead of rebuilding it. The build
uses the source file's last Git change time as `SOURCE_DATE_EPOCH` and checks
that the final PDF is nonempty and has resolved references and a positive page
count.

Successful `main` builds publish an official GitHub release only after every
job has passed, including Comparator statement matching, NanoDa replay and
Lean's default-kernel replay. The committed [RELEASE_VERSION](RELEASE_VERSION)
file supplies the semantic version and must be bumped before a new release;
CI checks tag collisions before starting the long Lean build. The release
contains the paper PDF and a compressed Ubuntu `.lake/build` tree with the
project's licensing information. A rerun at an already published commit
verifies the existing release.

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
