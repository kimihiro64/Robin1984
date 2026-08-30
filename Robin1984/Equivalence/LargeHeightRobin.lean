import Robin1984.Analytic.MertensExplicitCoefficient
import Robin1984.Analytic.PrimeCostExplicitCoefficient
import Robin1984.Arithmetic.Definitions
import Robin1984.Arithmetic.RobinBounds
import Robin1984.Equivalence.AbundancyExponentBound
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann (1984).
- Formalization note: The retained statement or source-level argument is Robin's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# The RH implication above the explicit logarithmic height

Under the classical Riemann hypothesis, the analytic estimates force the
logarithmic Robin margin below the required negative error scale whenever
`log n >= 100000`. The final theorem converts that margin estimate into
Robin's inequality for every integer in the large-height range.
-/

namespace Robin1984

noncomputable section

theorem robin_log_margin_lt_negative_scale_of_RH
    (hRH : RiemannHypothesis) {n : Nat} (hn : Not (n = 0))
    (hH : 100000 <= Real.log (n : Real)) :
    Real.log (abundancy n) - Real.eulerMascheroniConstant -
        Real.log (Real.log (Real.log (n : Real))) <
      -(1 / 100 : Real) * ((Real.log (n : Real))^(-(1 / 2 : Real)) *
        Inv.inv (Real.log (Real.log (n : Real)))) := by
  have hArithmetic := robin_log_abundancy_le_complete_prime_cost hRH hn (by linarith : 20000 <= Real.log (n : Real))
  have hMertens := robinMertensWeightedScalar_lt_nine_quarters hH
  have hCost := robin_minimum_prime_cost_ge_large_scalar hRH hH
  linarith

/-- The explicit analytic cutoff. The finite range below this height is not
assumed or hidden in this theorem. -/
theorem nativeRobinInequality_of_RH_large_log
    (hRH : RiemannHypothesis) {n : Nat} (hH : 100000 <= Real.log (n : Real)) :
    Robin1984.Core.NativeRobinInequality n := by
  have hn : Not (n = 0) := by
    intro hZero
    subst n
    norm_num at hH
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  have hHeightOne : 1 < Real.log (n : Real) := by linarith
  have hLogHeightPos := Real.log_pos hHeightOne
  have hScale : 0 < (Real.log (n : Real))^(-(1 / 2 : Real)) *
      Inv.inv (Real.log (Real.log (n : Real))) := by positivity
  have hMargin := robin_log_margin_lt_negative_scale_of_RH hRH hn hH
  have hLog : Real.log (abundancy n) < Real.eulerMascheroniConstant +
      Real.log (Real.log (Real.log (n : Real))) := by nlinarith
  have hBoundPos : 0 < robinBoundRatio n := by
    unfold robinBoundRatio
    exact mul_pos (Real.exp_pos _) hLogHeightPos
  have hBoundLog : Real.log (robinBoundRatio n) = Real.eulerMascheroniConstant +
      Real.log (Real.log (Real.log (n : Real))) := by
    unfold robinBoundRatio
    rw [Real.log_mul (Real.exp_pos _).ne' hLogHeightPos.ne', Real.log_exp]
  apply (nativeRobinInequality_iff_abundancy_lt_bound hnPos).mpr
  apply (Real.log_lt_log_iff (abundancy_pos hnPos) hBoundPos).mp
  rwa [hBoundLog]

end

end Robin1984
