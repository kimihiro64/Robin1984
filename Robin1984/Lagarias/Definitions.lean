import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jeffrey C. Lagarias, An Elementary Problem Equivalent
  to the Riemann Hypothesis (2001).
- Formalization note: The criterion is stated with Mathlib's harmonic numbers,
  divisor sum, and Riemann-hypothesis predicate.
- PROVENANCE-END
-/

/-!
# Lagarias' elementary criterion

This is the project-local statement corresponding to Problem E in Lagarias
(2001).
-/

namespace Robin1984

open scoped ArithmeticFunction.sigma

/-- Lagarias' elementary divisor-sum criterion. -/
def LagariasElementaryCriterion : Prop :=
  forall n : Nat,
    0 < n ->
      ((ArithmeticFunction.sigma 1 n : Nat) : Real) <=
        (harmonic n : Real) +
          Real.exp (harmonic n : Real) * Real.log (harmonic n : Real)

end Robin1984
