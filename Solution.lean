import Mathlib.NumberTheory.LSeries.RiemannZeta
import Robin1984.Equivalence.Theorem
import Robin1984.Lagarias.Theorem
import Robin1984.Public

set_option autoImplicit false

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984) and Jeffrey C. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis (2001).
- Formalization note: The retained statements are Robin's and Lagarias's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Proved solution

Comparator checks that these declarations have exactly the same statements as
their counterparts in `Challenge.lean` and use only the permitted axioms.
-/

namespace Robin1984

theorem robin_inequality_iff_riemannHypothesis :
    (forall n : Nat, 5040 < n -> robinInequality n) <->
      RiemannHypothesis := by
  exact riemannHypothesis_iff_nativeRobinInequalityAll.symm

theorem riemannHypothesis_iff_colossallyAbundant_robin :
    RiemannHypothesis <->
      (forall n : Nat, forall eps : Real, 5040 < n ->
        IsColossallyAbundantWith n eps -> robinInequality n) := by
  exact riemannHypothesis_iff_colossallyAbundantRobin

theorem riemann_hypothesis_iff_lagarias_elementary_criterion :
    RiemannHypothesis <-> LagariasElementaryCriterion := by
  exact riemannHypothesis_iff_lagariasElementaryCriterion

end Robin1984
