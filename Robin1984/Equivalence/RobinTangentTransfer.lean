import Robin1984.ColossallyAbundant.RobinLogMargin
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Transferring Robin's inequality through tangent CA maximizers

These statements quantify over arbitrary actual exponent states at actual
first-layer frontiers.  A maximizer for the tangent colossally abundant
objective transfers Robin's inequality back to the original integer.
-/

namespace Robin1984

noncomputable section


/-- Constructive tangent-support transfer: if `q` has at least the fixed
Robin-tangent CA objective of `n`, then Robin at `q` implies Robin at `n`. -/
theorem nativeRobinInequality_of_tangentCAObjective_ge
    {n q : Nat}
    (hnCut : 5040 < n)
    (hqCut : 5040 < q)
    (hObj :
      caLogObjective (robinFrontierCutoff n) n <=
        caLogObjective (robinFrontierCutoff n) q)
    (hqRobin : Robin1984.Core.NativeRobinInequality q) :
    Robin1984.Core.NativeRobinInequality n := by
  have hnPos : 0 < n := Nat.zero_lt_of_lt hnCut
  have hqPos : 0 < q := Nat.zero_lt_of_lt hqCut
  have hnNe : Not (n = 0) := Nat.ne_of_gt hnPos
  have hqNe : Not (q = 0) := Nat.ne_of_gt hqPos
  have hnLogOne : 1 < Real.log (n : Real) := by
    have hnRealPos : (0 : Real) < (n : Real) := by
      exact_mod_cast hnPos
    rw [Real.lt_log_iff_exp_lt hnRealPos]
    exact lt_trans Real.exp_one_lt_three
      (by exact_mod_cast (by omega : 3 < n))
  have hqLogOne : 1 < Real.log (q : Real) := by
    have hqRealPos : (0 : Real) < (q : Real) := by
      exact_mod_cast hqPos
    rw [Real.lt_log_iff_exp_lt hqRealPos]
    exact lt_trans Real.exp_one_lt_three
      (by exact_mod_cast (by omega : 3 < q))
  have hObjLog := hObj
  rw [caLogObjective_eq_log_abundancy_sub
        (eps := robinFrontierCutoff n) hnPos,
      caLogObjective_eq_log_abundancy_sub
        (eps := robinFrontierCutoff n) hqPos] at hObjLog
  unfold robinFrontierCutoff at hObjLog
  have hTangent :=
    log_log_sub_le_frontier_tangent_global hnLogOne hqLogOne
  have hqMargin : 0 < Robin1984.lyapunov (actualExponentState q) :=
    (actualExponentState_lyapunov_pos_iff_nativeRobinInequality hqCut).2
      hqRobin
  have hnMargin : 0 < Robin1984.lyapunov (actualExponentState n) := by
    unfold Robin1984.lyapunov at hqMargin
    unfold Robin1984.lyapunov
    rw [actualExponentState_logN_eq_log hqNe,
      actualExponentState_logSigmaOverN_eq_log_abundancy hqNe] at hqMargin
    rw [actualExponentState_logN_eq_log hnNe,
      actualExponentState_logSigmaOverN_eq_log_abundancy hnNe]
    linarith
  exact
    (actualExponentState_lyapunov_pos_iff_nativeRobinInequality hnCut).1
      hnMargin

/-- A Robin-good colossally abundant maximizer at `n`'s own tangent cutoff
constructively covers `n`. -/
theorem nativeRobinInequality_of_tangent_colossallyAbundant
    {n q : Nat}
    (hnCut : 5040 < n)
    (hqCut : 5040 < q)
    (hCA : IsColossallyAbundantWith q (robinFrontierCutoff n))
    (hqRobin : Robin1984.Core.NativeRobinInequality q) :
    Robin1984.Core.NativeRobinInequality n := by
  apply nativeRobinInequality_of_tangentCAObjective_ge hnCut hqCut
  case hObj =>
    exact hCA.logObjective_max (by omega : 1 < n)
  case hqRobin =>
    exact hqRobin

/-- If `5040` and `55440` are CA maximizers at a shared transition parameter,
then every maximizer at a smaller positive parameter lies above `5040`. -/
theorem tangentCAMaximizer_above_5040_of_shared_5040_55440
    {n q : Nat} {eps0 : Real}
    (hnCut : 5040 < n)
    (hEps : robinFrontierCutoff n < eps0)
    (h5040 : IsColossallyAbundantWith 5040 eps0)
    (h55440 : IsColossallyAbundantWith 55440 eps0)
    (hqCA : IsColossallyAbundantWith q (robinFrontierCutoff n)) :
    5040 < q := by
  by_contra hNot
  have hqLe : q <= 5040 := Nat.le_of_not_gt hNot
  have hqPos : 0 < q := Nat.zero_lt_of_lt hqCA.one_lt
  have hLambdaPos : 0 < robinFrontierCutoff n :=
    robinFrontierCutoff_pos_of_cutoff hnCut
  have hEq :
      caLogObjective eps0 5040 = caLogObjective eps0 55440 :=
    le_antisymm
      (h55440.logObjective_max (by norm_num : 1 < 5040))
      (h5040.logObjective_max (by norm_num : 1 < 55440))
  have hSmall :
      caLogObjective eps0 q <= caLogObjective eps0 5040 :=
    h5040.logObjective_max hqCA.one_lt
  have hMax :
      caLogObjective (robinFrontierCutoff n) 55440 <=
        caLogObjective (robinFrontierCutoff n) q :=
    hqCA.logObjective_max (by norm_num : 1 < 55440)
  rw [caLogObjective_eq_log_abundancy_sub (by norm_num : 0 < 5040),
      caLogObjective_eq_log_abundancy_sub (by norm_num : 0 < 55440)] at hEq
  rw [caLogObjective_eq_log_abundancy_sub hqPos,
      caLogObjective_eq_log_abundancy_sub (by norm_num : 0 < 5040)] at hSmall
  rw [caLogObjective_eq_log_abundancy_sub (by norm_num : 0 < 55440),
      caLogObjective_eq_log_abundancy_sub hqPos] at hMax
  have hqCastLe : (q : Real) <= (5040 : Real) := by
    exact_mod_cast hqLe
  have hLogqLe : Real.log (q : Real) <= Real.log (5040 : Real) :=
    Real.log_le_log (by exact_mod_cast hqPos) hqCastLe
  have hLogStep : Real.log (5040 : Real) < Real.log (55440 : Real) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hPenaltyNonneg :
      0 <= (eps0 - robinFrontierCutoff n) *
        (Real.log (5040 : Real) - Real.log (q : Real)) :=
    mul_nonneg (sub_nonneg.mpr hEps.le) (sub_nonneg.mpr hLogqLe)
  have hStepPositive :
      0 < (eps0 - robinFrontierCutoff n) *
        (Real.log (55440 : Real) - Real.log (5040 : Real)) :=
    mul_pos (sub_pos.mpr hEps) (sub_pos.mpr hLogStep)
  have hSmallTransport :
      (Real.log (abundancy q) -
          robinFrontierCutoff n * Real.log (q : Real)) -
        (Real.log (abundancy 5040) -
          robinFrontierCutoff n * Real.log (5040 : Real)) =
      ((Real.log (abundancy q) - eps0 * Real.log (q : Real)) -
        (Real.log (abundancy 5040) - eps0 * Real.log (5040 : Real))) -
      (eps0 - robinFrontierCutoff n) *
        (Real.log (5040 : Real) - Real.log (q : Real)) := by
    ring
  have hSmallAtLambda :
      Real.log (abundancy q) -
          robinFrontierCutoff n * Real.log (q : Real) <=
        Real.log (abundancy 5040) -
          robinFrontierCutoff n * Real.log (5040 : Real) := by
    apply sub_nonpos.mp
    rw [hSmallTransport]
    apply sub_nonpos.mpr
    exact (sub_nonpos.mpr hSmall).trans hPenaltyNonneg
  have hStepTransport :
      (Real.log (abundancy 55440) -
          robinFrontierCutoff n * Real.log (55440 : Real)) -
        (Real.log (abundancy 5040) -
          robinFrontierCutoff n * Real.log (5040 : Real)) =
      ((Real.log (abundancy 55440) - eps0 * Real.log (55440 : Real)) -
        (Real.log (abundancy 5040) - eps0 * Real.log (5040 : Real))) +
      (eps0 - robinFrontierCutoff n) *
        (Real.log (55440 : Real) - Real.log (5040 : Real)) := by
    ring
  have hStepAtLambda :
      Real.log (abundancy 5040) -
          robinFrontierCutoff n * Real.log (5040 : Real) <
        Real.log (abundancy 55440) -
          robinFrontierCutoff n * Real.log (55440 : Real) := by
    apply sub_pos.mp
    rw [hStepTransport]
    have hBaseZero :
        (Real.log (abundancy 55440) -
            eps0 * Real.log (55440 : Real)) -
          (Real.log (abundancy 5040) -
            eps0 * Real.log (5040 : Real)) = 0 :=
      sub_eq_zero.mpr hEq.symm
    exact add_pos_of_nonneg_of_pos hBaseZero.ge hStepPositive
  exact (not_lt_of_ge (hMax.trans hSmallAtLambda)) hStepAtLambda

end

end Robin1984
