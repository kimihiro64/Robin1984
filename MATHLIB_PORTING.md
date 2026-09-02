# Mathlib candidate layer

Reusable mathematics intended for upstreaming lives under
`Robin1984/Mathlib/` and is exported by `Robin1984/Mathlib.lean`. Removing the
leading `Robin1984/Mathlib/` path component yields each proposed Mathlib path.

## Hard boundary

Candidate modules may import only narrow `Mathlib.*`, `Batteries.*`, `Init.*`,
`Lean.*`, or `Std.*` modules and other modules in this candidate layer. Their
declarations use the proposed upstream namespace and may not refer to
Robin1984 definitions, proof modules, theorem surfaces, or third-party project
libraries.

Each candidate carries Mathlib's copyright, Apache-2.0 licence, authorship,
module documentation, declaration documentation, naming, and formatting
conventions. A `mathlib-ready` row has an identified destination, no project
dependency, no proof placeholders, and a clean focused build against the
pinned Mathlib revision.

## Candidate inventory

| Project module | Proposed Mathlib path | Readiness | Upstream reference |
| --- | --- | --- | --- |
| `Robin1984.Mathlib.Analysis.Asymptotics.Omega` | `Mathlib/Analysis/Asymptotics/Omega.lean` | mathlib-ready | Not submitted |
| `Robin1984.Mathlib.Analysis.SpecialFunctions.Log.RatBounds` | `Mathlib/Analysis/SpecialFunctions/Log/RatBounds.lean` | mathlib-ready | Not submitted |
| `Robin1984.Mathlib.MeasureTheory.Integral.IntervalIntegral.TailReweight` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/TailReweight.lean` | mathlib-ready | Not submitted |
| `Robin1984.Mathlib.NumberTheory.Chebyshev.LcmSupport` | `Mathlib/NumberTheory/Chebyshev/LcmSupport.lean` | mathlib-ready | Not submitted |
| `Robin1984.Mathlib.NumberTheory.Chebyshev.MertensProduct` | `Mathlib/NumberTheory/Chebyshev/MertensProduct.lean` | mathlib-ready | Not submitted |
| `Robin1984.Mathlib.NumberTheory.Chebyshev.PrimeLogAbel` | `Mathlib/NumberTheory/Chebyshev/PrimeLogAbel.lean` | mathlib-ready | Not submitted |
| `Robin1984.Mathlib.NumberTheory.Chebyshev.PrimeSquareAbel` | `Mathlib/NumberTheory/Chebyshev/PrimeSquareAbel.lean` | mathlib-ready | Not submitted |
| `Robin1984.Mathlib.NumberTheory.LSeries.RiemannZetaReal` | `Mathlib/NumberTheory/LSeries/RiemannZetaReal.lean` | mathlib-ready | Not submitted |
| `Robin1984.Mathlib.Probability.Moments.MGFAnalyticContinuation` | `Mathlib/Probability/Moments/MGFAnalyticContinuation.lean` | mathlib-ready | Not submitted |

Compatibility modules outside this layer preserve the project's existing
declaration names. New reusable work belongs in the candidate layer;
project-specific wrappers may depend on it, but candidate modules may never
depend back on the project.

## Reviewed extraction backlog

No reviewed project-independent extraction remains. The candidate layer now
contains every reusable unit identified by the repository-wide audit.

The audit intentionally leaves source-specific combinations in the project:
Nicolas's named oscillation functions, Robin's dyadic certificate constants,
and the filled Nicolas--Landau tail-continuation machinery. Their reusable
constituents—the finite Mertens product, rational logarithm bounds, zeta pole
factor and positive-real nonvanishing theorem, MGF continuation lemmas, and
complete-tail reweighting identity—are maintained in the candidate layer.
