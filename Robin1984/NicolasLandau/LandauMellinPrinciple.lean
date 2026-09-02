import Robin1984.Mathlib.Probability.Moments.MGFAnalyticContinuation

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# Landau's positive-transform principle

Compatibility declarations for the project-independent Landau transform
lemmas maintained in the Mathlib candidate layer.
-/

namespace Robin1984

/-- Compatibility alias for the upstream-ready moment-series criterion. -/
alias mem_integrableExpSet_add_of_summable_moments :=
  ProbabilityTheory.mem_integrableExpSet_add_of_summable_moments

/-- Compatibility alias for analytic continuation on a ball. -/
alias mem_integrableExpSet_add_of_analyticContinuationOnBall :=
  ProbabilityTheory.mem_integrableExpSet_add_of_analyticContinuationOnBall

/-- Compatibility alias for strict crossing of the convergence frontier. -/
alias integrableExpSet_strict_crossing_of_analyticContinuationOnBall :=
  ProbabilityTheory.integrableExpSet_strict_crossing_of_analyticContinuationOnBall

/-- Compatibility alias for Landau's strict local frontier conclusion. -/
alias exists_integrableExpSet_gt_of_analyticContinuationAt :=
  ProbabilityTheory.exists_integrableExpSet_gt_of_analyticContinuationAt

end Robin1984
