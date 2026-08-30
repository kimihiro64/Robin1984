import Robin1984.Arithmetic.Definitions
import Robin1984.Arithmetic.RobinBounds
import Robin1984.ColossallyAbundant.CAProfile
import Robin1984.Helpers.Lyapunov
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Robin's inequality as positivity of a logarithmic margin

The logarithmic margin of the actual exponent state is positive exactly when
the integer satisfies Robin's inequality.
-/

namespace Robin1984

noncomputable section

theorem actualExponentState_lyapunov_pos_iff_nativeRobinInequality
    {n : Nat} (hnCut : 5040 < n) :
    0 < Robin1984.lyapunov (actualExponentState n) <->
      Robin1984.Core.NativeRobinInequality n := by
  have hnPos : 0 < n := Nat.zero_lt_of_lt hnCut
  have hnNe : Not (n = 0) := Nat.ne_of_gt hnPos
  have hAbundancyPos : 0 < abundancy n := abundancy_pos hnPos
  have hBoundPos : 0 < robinBoundRatio n :=
    robinBoundRatio_pos_of_cutoff hnCut
  rw [nativeRobinInequality_iff_abundancy_lt_bound hnPos]
  unfold Robin1984.lyapunov
  rw [actualExponentState_logN_eq_log hnNe,
    actualExponentState_logSigmaOverN_eq_log_abundancy hnNe]
  constructor
  case mp =>
    intro hMargin
    have hLog :
        Real.log (abundancy n) < Real.log (robinBoundRatio n) := by
      rw [log_robinBoundRatio_eq_of_cutoff hnCut]
      linarith
    calc
      abundancy n = Real.exp (Real.log (abundancy n)) :=
        (Real.exp_log hAbundancyPos).symm
      _ < Real.exp (Real.log (robinBoundRatio n)) :=
        Real.exp_lt_exp.mpr hLog
      _ = robinBoundRatio n := Real.exp_log hBoundPos
  case mpr =>
    intro hRobin
    have hLog :
        Real.log (abundancy n) < Real.log (robinBoundRatio n) :=
      Real.log_lt_log hAbundancyPos hRobin
    rw [log_robinBoundRatio_eq_of_cutoff hnCut] at hLog
    linarith


end

end Robin1984
