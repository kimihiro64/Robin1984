import Robin1984.Equivalence.Equivalence
import Robin1984.Lagarias.Elementary

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jeffrey C. Lagarias, An Elementary Problem Equivalent
  to the Riemann Hypothesis (2001), forward implication.
- Formalization note: Robin's established theorem supplies the large range;
  Lagarias' Lemma 3.1 supplies the harmonic comparison.
- PROVENANCE-END
-/

/-! # The forward Lagarias implication outside the finite certificate -/

namespace Robin1984

/-- Lagarias' criterion at its equality case `n = 1`. -/
theorem lagariasElementaryCriterion_one :
    ((ArithmeticFunction.sigma 1 1 : Nat) : Real) <=
      (harmonic 1 : Real) +
        Real.exp (harmonic 1 : Real) * Real.log (harmonic 1 : Real) := by
  norm_num [ArithmeticFunction.sigma, harmonic]

/-- Under RH, Lagarias' criterion holds above Robin's exceptional cutoff. -/
theorem lagariasElementaryCriterion_of_riemannHypothesis_of_5040_lt
    (hRH : RiemannHypothesis) {n : Nat} (hn : 5040 < n) :
    ((ArithmeticFunction.sigma 1 n : Nat) : Real) <=
      (harmonic n : Real) +
        Real.exp (harmonic n : Real) * Real.log (harmonic n : Real) := by
  have hRobin : Core.NativeRobinInequality n :=
    nativeRobinInequalityAll_of_riemannHypothesis hRH n hn
  have hLagarias :
      Real.exp Real.eulerMascheroniConstant * (n : Real) *
          Real.log (Real.log (n : Real)) <=
        Real.exp (harmonic n : Real) * Real.log (harmonic n : Real) :=
    robinBound_le_exp_harmonic_mul_log_harmonic (by omega)
  have hnRealPos : (0 : Real) < (n : Real) := by
    exact_mod_cast (by omega : 0 < n)
  have hCast : (n : Real) <= ((n + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ n
  have hLogNLeH : Real.log (n : Real) <= (harmonic n : Real) :=
    (Real.log_le_log hnRealPos hCast).trans (log_add_one_le_harmonic n)
  have hHarmonicNonneg : (0 : Real) <= harmonic n :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).le.trans hLogNLeH
  unfold Core.NativeRobinInequality Core.sigmaOneNat at hRobin
  linarith

end Robin1984
