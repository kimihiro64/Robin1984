import Robin1984.NicolasLandau.RobinWeightedIntegral
import Robin1984.NicolasLandau.WeightedMellin
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# Exact paired zero atoms in Robin's weighted explicit formula

The regularizing constant in the Hadamard atom is retained until it cancels
the lower cutoff endpoint.  No sum/integral interchange is asserted here.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set

theorem integrableOn_robinCutoffMellinTest_power_tail
    {n : Nat} {x : Real} (hx : 1 < x) {rho : Complex} (hRho : rho.re < n) :
    IntegrableOn (fun u : Real =>
      (u : Complex) ^ (rho - 1) * robinCutoffMellinTest n x u) (Ioi 1) := by
  have hInterval : Not (Membership.mem (uIcc (1 : Real) x) 0) := by
    rw [uIcc_of_le hx.le]
    simp
  have hLowBase : IntegrableOn (fun u : Real => (u : Complex) ^ (rho - 1))
      (Ioc 1 x) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mp
      (intervalIntegral.intervalIntegrable_cpow (Or.inr hInterval))
  have hLowScaled : IntegrableOn (fun u : Real =>
      (u : Complex) ^ (rho - 1) *
        ((x : Complex)^(-(n : Complex)) * (((Inv.inv (Real.log x) : Real) : Complex))))
      (Ioc 1 x) := hLowBase.mul_const _
  have hLow : IntegrableOn (fun u : Real =>
      (u : Complex) ^ (rho - 1) * robinCutoffMellinTest n x u) (Ioc 1 x) :=
    hLowScaled.congr_fun
      (fun u hu => (robinCutoffMellinIntegrand_eq_lower n rho hu.2).symm)
      measurableSet_Ioc
  have hHighBase : IntegrableOn (fun u : Real =>
      (u : Complex) ^ (rho - (n : Complex) - 1) *
        (((Inv.inv (Real.log u) : Real) : Complex))) (Ioi x) := by
    simpa using integrableOn_cpow_div_log_pow hx (by
      simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re]
      linarith : (rho - (n : Complex) - 1).re < -1) 1
  have hHigh : IntegrableOn (fun u : Real =>
      (u : Complex) ^ (rho - 1) * robinCutoffMellinTest n x u) (Ioi x) :=
    hHighBase.congr_fun
      (fun u hu => (robinCutoffMellinIntegrand_eq_upper n rho hx hu).symm)
      measurableSet_Ioi
  rw [<- Ioc_union_Ioi_eq_Ioi hx.le]
  exact hLow.union hHigh

/-- The lower cutoff endpoint, kept explicitly before pairing the Hadamard
regularizer. -/
theorem robinCutoffMellinTest_power_tail_eq
    {n : Nat} {x : Real} (hx : 1 < x) {rho : Complex}
    (hRhoZero : Not (rho = 0)) (hRho : rho.re < n) :
    integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
      (u : Complex) ^ (rho - 1) * robinCutoffMellinTest n x u) =
      robinZeroKernel n rho x / rho - robinCutoffMellinTest n x 1 / rho := by
  have hxZero : Not ((x : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans Real.zero_lt_one hx))
  have hInterval : Not (Membership.mem (uIcc (1 : Real) x) 0) := by
    rw [uIcc_of_le hx.le]
    simp
  have hExpZero : Not (rho - 1 = -1) := by
    intro h
    apply hRhoZero
    linear_combination h
  have hInt := integrableOn_robinCutoffMellinTest_power_tail hx hRho
  have hLow := hInt.mono_set (Ioc_subset_Ioi_self : Ioc 1 x <= Ioi 1)
  have hHigh := hInt.mono_set (Ioi_subset_Ioi hx.le)
  rw [<- Ioc_union_Ioi_eq_Ioi hx.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hLow hHigh]
  have hLowValue : integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
      (u : Complex) ^ (rho - 1) * robinCutoffMellinTest n x u) =
      ((x : Complex)^rho - 1) / rho * robinCutoffMellinTest n x 1 := by
    calc
      integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
          (u : Complex) ^ (rho - 1) * robinCutoffMellinTest n x u) =
        integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
          (u : Complex) ^ (rho - 1) * robinCutoffMellinTest n x 1) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro u hu
        simp only [robinCutoffMellinTest, if_pos hu.2, if_pos hx.le]
      _ = _ := by
        rw [integral_mul_const, <- intervalIntegral.integral_of_le hx.le,
          integral_cpow (Or.inr (And.intro hExpZero hInterval))]
        simp
  have hHighValue : integral (volume.restrict (Ioi x)) (fun u : Real =>
      (u : Complex) ^ (rho - 1) * robinCutoffMellinTest n x u) =
      robinCpowLogTail (rho - (n : Complex)) 1 x := by
    unfold robinCpowLogTail
    simp only [pow_one]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact robinCutoffMellinIntegrand_eq_upper n rho hx hu
  rw [hLowValue, hHighValue,
    robinZeroKernel_div_rho_eq_boundary_div_add_tail_one hRhoZero hx hRho]
  have hCpow : (x : Complex)^rho * (x : Complex)^(-(n : Complex)) =
      (x : Complex)^(rho - (n : Complex)) := by
    rw [<- Complex.cpow_add _ _ hxZero]
    congr 1
  simp only [robinCutoffMellinTest, if_pos hx.le, Complex.ofReal_inv]
  have hLog : Not (((Real.log x : Real) : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos hx))
  field_simp [hRhoZero, hLog]
  linear_combination hCpow

theorem integrable_vertical_resolvent
    {H : Real -> Complex} (hH : Integrable H) {c : Real} {rho : Complex}
    (hRho : rho.re < c) :
    Integrable (fun t : Real =>
      H t / ((c : Complex) + (t : Complex) * Complex.I - rho)) := by
  have hPos : 0 < c - rho.re := sub_pos.mpr hRho
  have hCoeffMeas : Measurable (fun t : Real =>
      Inv.inv ((c : Complex) + (t : Complex) * Complex.I - rho)) := by
    fun_prop
  have hMeas : AEStronglyMeasurable (fun t : Real =>
      H t / ((c : Complex) + (t : Complex) * Complex.I - rho)) volume := by
    simpa only [div_eq_mul_inv] using!
      hH.aestronglyMeasurable.mul hCoeffMeas.aestronglyMeasurable
  apply (hH.norm.div_const (c - rho.re)).mono' hMeas
  filter_upwards with t
  have hDen : c - rho.re <= norm ((c : Complex) + (t : Complex) * Complex.I - rho) := by
    calc
      c - rho.re <= abs (c - rho.re) := le_abs_self _
      _ <= norm ((c : Complex) + (t : Complex) * Complex.I - rho) := by
        simpa using Complex.abs_re_le_norm
          ((c : Complex) + (t : Complex) * Complex.I - rho)
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg (H t)) hPos hDen

/-- Exact zero-atom matching: the lower endpoint cancels the Hadamard
regularizing constant, leaving precisely Robin's weighted zero kernel. -/
theorem robinCutoffMellin_paired_zero_atom
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    {c : Real} (hcPos : 0 < c) (hcLt : c < n)
    {rho : Complex} (hRhoZero : Not (rho = 0)) (hRho : rho.re < c) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (robinCutoffMellinTest n x) ((c : Complex) + (t : Complex) * Complex.I) *
            (1 / ((c : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho)) =
      robinZeroKernel n rho x / rho := by
  let H : Real -> Complex := fun t =>
    mellin (robinCutoffMellinTest n x) ((c : Complex) + (t : Complex) * Complex.I)
  have hLine : Integrable H :=
    verticalIntegrable_mellin_robinCutoffMellinTest hn hx hcPos hcLt
  have hResolvent := integrable_vertical_resolvent hLine hRho
  have hConst := hLine.div_const rho
  have hAtOne : (((1 / (2 * Real.pi) : Real) : Complex)) *
      integral volume H = robinCutoffMellinTest n x 1 := by
    have h := mellinInv_mellin_robinCutoffMellinTest hn hx hcPos hcLt Real.zero_lt_one
    simpa only [mellinInv, Complex.ofReal_one, Complex.one_cpow,
      RCLike.real_smul_eq_coe_mul, smul_eq_mul, one_mul, H] using! h
  have hFunction : (fun t : Real => H t *
      (1 / ((c : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho)) =
      (fun t : Real => H t / ((c : Complex) + (t : Complex) * Complex.I - rho) +
        H t / rho) := by
    funext t
    ring
  change (((1 / (2 * Real.pi) : Real) : Complex)) *
    integral volume (fun t : Real => H t *
      (1 / ((c : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho)) = _
  rw [hFunction, integral_add hResolvent hConst, mul_add]
  have hPair : (((1 / (2 * Real.pi) : Real) : Complex)) *
      integral volume (fun t : Real =>
        H t / ((c : Complex) + (t : Complex) * Complex.I - rho)) =
      robinZeroKernel n rho x / rho - robinCutoffMellinTest n x 1 / rho := by
    rw [robinCutoffMellin_resolvent_pairing hn hx hcPos hcLt hRho,
      robinCutoffMellinTest_power_tail_eq hx hRhoZero (lt_trans hRho hcLt)]
  rw [hPair, integral_div, <- mul_div_assoc, hAtOne]
  ring

end

end Robin1984
