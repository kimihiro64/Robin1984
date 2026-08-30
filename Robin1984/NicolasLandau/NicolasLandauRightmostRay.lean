import Robin1984.Equivalence.OmegaScaleTransfer
import Robin1984.NicolasLandau.NicolasLandau
import Robin1984.NicolasLandau.NicolasLandauCompactBlock
import Robin1984.NicolasLandau.NicolasLandauComplexFrontier
import Robin1984.NicolasLandau.NicolasLandauPositiveStrip
import Robin1984.NicolasLandau.NicolasLandauPositiveTail
import Robin1984.NicolasLandau.NicolasOscillation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# Nicolas-Landau continuation along a rightmost-zero ray

This file identifies the analytic positive-tail moment-generating function
with the complete filled Nicolas continuation and isolates the endpoint pole.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem norm_intervalIntegral_inv_smul_sub_le_of_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [CompleteSpace E]
    {f : Real -> E} {a b delta : Real} {V : E}
    (hf : IntervalIntegrable f volume a b) (ha : 0 < a) (hb : 0 < b)
    (hDelta : 0 <= delta)
    (hBound : forall x : Real, Membership.mem (uIoc a b) x ->
      norm (f x - V) <= delta) :
    norm (intervalIntegral
        (fun x : Real => HSMul.hSMul (Inv.inv x) (f x)) a b volume -
      HSMul.hSMul (Real.log (b / a)) V) <=
      delta * abs (Real.log (b / a)) := by
  have hSubset : uIcc a b <= Ioi (0 : Real) := by
    simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hInv : ContinuousOn (fun x : Real => Inv.inv x) (uIcc a b) := by
    intro x hx
    exact (NormedField.continuousAt_inv.mpr
      (ne_of_gt (hSubset hx))).continuousWithinAt
  have hWeighted : IntervalIntegrable
      (fun x : Real => HSMul.hSMul (Inv.inv x) (f x)) volume a b :=
    hf.continuousOn_smul hInv
  have hConst : IntervalIntegrable
      (fun x : Real => HSMul.hSMul (Inv.inv x) V) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact hInv.smul continuousOn_const
  have hReal : IntervalIntegrable
      (fun x : Real => Inv.inv x * delta) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact hInv.mul continuousOn_const
  calc
    norm (intervalIntegral
          (fun x : Real => HSMul.hSMul (Inv.inv x) (f x)) a b volume -
        HSMul.hSMul (Real.log (b / a)) V) =
        norm (intervalIntegral
          (fun x : Real => HSMul.hSMul (Inv.inv x) (f x - V))
          a b volume) := by
      congr 1
      have hConstIntegral : HSMul.hSMul (Real.log (b / a)) V =
          intervalIntegral
            (fun x : Real => HSMul.hSMul (Inv.inv x) V) a b volume := by
        rw [intervalIntegral.integral_smul_const,
          integral_inv_of_pos ha hb]
      rw [hConstIntegral, <- intervalIntegral.integral_sub hWeighted hConst]
      congr 1
      funext x
      exact (smul_sub _ _ _).symm
    _ <= abs (intervalIntegral
        (fun x : Real => Inv.inv x * delta) a b volume) := by
      apply intervalIntegral.norm_integral_le_abs_of_norm_le
      . filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
        have hxPos : 0 < x :=
          lt_of_lt_of_le (lt_min ha hb) (uIoc_subset_uIcc hx).1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxPos)]
        exact mul_le_mul_of_nonneg_left (hBound x hx)
          (inv_nonneg.mpr hxPos.le)
      . exact hReal
    _ = delta * abs (Real.log (b / a)) := by
      simp_rw [mul_comm]
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
      rw [abs_mul, abs_of_nonneg hDelta]

def nicolasLandauRpowComplexContinuation
    (X b : Real) (z : Complex) : Complex :=
  (X : Complex) ^ (z - (b : Complex)) / ((b : Complex) - z)

def nicolasLandauPositiveComplexContinuationFilled
    (X b : Real) (z : Complex) : Complex :=
  nicolasJShiftedComplexContinuationFilled z -
    nicolasJComplexMellinStartup X z +
      nicolasLandauRpowComplexContinuation X b z

def nicolasLandauPositiveComplexMellin
    (X b : Real) (z : Complex) : Complex :=
  integral (volume.restrict (Ioi X)) (fun x : Real =>
    (x : Complex) ^ (z - 1) *
      (nicolasLandauPositiveTail b x : Complex))

theorem complexMGF_log_nicolasLandauPositiveMeasure_eq_complexMellin
    {X b : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x) {z : Complex} :
    complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b) z =
      nicolasLandauPositiveComplexMellin X b z := by
  have hDensity := nicolasLandauPositiveDensity_aemeasurable
    (X := X) (b := b) hX
  let measurableDensity : Real -> ENNReal :=
    hDensity.mk (nicolasLandauPositiveDensity b)
  have hDensityEq : Filter.Eventually
      (fun x : Real => nicolasLandauPositiveDensity b x =
        measurableDensity x)
      (ae (volume.restrict (Ioi X))) := hDensity.ae_eq_mk
  have hDensityTop : Filter.Eventually
      (fun x : Real => measurableDensity x < Top.top)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [hDensityEq] with x hx
    rw [<- hx]
    exact ENNReal.ofReal_lt_top
  have hMeasureEq :
      (volume.restrict (Ioi X)).withDensity
          (nicolasLandauPositiveDensity b) =
        (volume.restrict (Ioi X)).withDensity measurableDensity :=
    withDensity_congr_ae hDensityEq
  unfold complexMGF nicolasLandauPositiveMeasure
  rw [hMeasureEq, integral_withDensity_eq_integral_toReal_smul
    hDensity.measurable_mk hDensityTop]
  unfold nicolasLandauPositiveComplexMellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hxNe : Not ((x : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hxPos.ne'
  have hTail : 0 <= nicolasLandauPositiveTail b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      nicolasLandauPositiveTail b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  have hExp : Complex.exp (z * (Real.log x : Complex)) =
      (x : Complex) ^ z := by
    rw [Complex.cpow_def_of_ne_zero hxNe, <- Complex.ofReal_log hxPos.le]
    congr 1
    ring
  change SMul.smul (measurableDensity x).toReal
      (Complex.exp (z * (Real.log x : Complex))) =
    (x : Complex) ^ (z - 1) *
      (nicolasLandauPositiveTail b x : Complex)
  rw [<- hdx]
  unfold nicolasLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  change ((x ^ (-1 : Real) * nicolasLandauPositiveTail b x : Real) : Complex) *
      Complex.exp (z * (Real.log x : Complex)) =
    (x : Complex) ^ (z - 1) *
      (nicolasLandauPositiveTail b x : Complex)
  rw [hExp]
  push_cast
  calc
    ((x ^ (-1 : Real) : Real) : Complex) *
          (nicolasLandauPositiveTail b x : Complex) * (x : Complex) ^ z =
        (((x ^ (-1 : Real) : Real) : Complex) * (x : Complex) ^ z) *
          (nicolasLandauPositiveTail b x : Complex) := by ring
    _ = ((x : Complex) ^ ((-1 : Real) : Complex) *
          (x : Complex) ^ z) *
          (nicolasLandauPositiveTail b x : Complex) := by
      rw [Complex.ofReal_cpow hxPos.le]
    _ = (x : Complex) ^ (((-1 : Real) : Complex) + z) *
          (nicolasLandauPositiveTail b x : Complex) := by
      rw [Complex.cpow_add _ _ hxNe]
    _ = (x : Complex) ^ (z - 1) *
          (nicolasLandauPositiveTail b x : Complex) := by
      congr 2
      norm_num [sub_eq_add_neg, add_comm]

theorem nicolasLandauRpowComplexTailMellin_eq_continuation
    {X b : Real} (hX : 0 < X) {z : Complex} (hz : z.re < b) :
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) =
      nicolasLandauRpowComplexContinuation X b z := by
  have hExponent : (z - (b : Complex) - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith
  calc
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) =
        integral (volume.restrict (Ioi X)) (fun x : Real =>
          (x : Complex) ^ (z - (b : Complex) - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxPos : 0 < x := hX.trans hx
      have hxNe : Not ((x : Complex) = 0) :=
        Complex.ofReal_ne_zero.mpr hxPos.ne'
      change (x : Complex) ^ (z - 1) *
          ((x ^ (-b) : Real) : Complex) =
        (x : Complex) ^ (z - (b : Complex) - 1)
      rw [Complex.ofReal_cpow hxPos.le]
      rw [<- Complex.cpow_add _ _ hxNe]
      congr 1
      push_cast
      ring
    _ = -(X : Complex) ^ (z - (b : Complex) - 1 + 1) /
          (z - (b : Complex) - 1 + 1) :=
      integral_Ioi_cpow_of_lt hExponent hX
    _ = nicolasLandauRpowComplexContinuation X b z := by
      unfold nicolasLandauRpowComplexContinuation
      have hDen : Not (z - (b : Complex) = 0) := by
        intro hEq
        have hRe := congrArg Complex.re hEq
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hRe
        linarith
      have hDen' : Not ((b : Complex) - z = 0) := by
        exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hDen))
      field_simp [hDen, hDen']
      ring

theorem nicolasLandauRpowComplexContinuation_analyticAt
    {X b : Real} (hX : 0 < X) {z : Complex}
    (hz : Not (z = (b : Complex))) :
    AnalyticAt Complex (nicolasLandauRpowComplexContinuation X b) z := by
  have hXNe : Not ((X : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hX.ne'
  have hNumerator : AnalyticAt Complex (fun w : Complex =>
      (X : Complex) ^ (w - (b : Complex))) z := by
    have hDiff : Differentiable Complex (fun w : Complex =>
        (X : Complex) ^ (w - (b : Complex))) := by
      intro w
      exact (differentiableAt_id.sub_const (b : Complex)).const_cpow
        (Or.inl hXNe)
    exact hDiff.analyticAt z
  have hDenominator : AnalyticAt Complex
      (fun w : Complex => (b : Complex) - w) z := by
    fun_prop
  unfold nicolasLandauRpowComplexContinuation
  exact hNumerator.div hDenominator (sub_ne_zero.mpr (Ne.symm hz))

theorem nicolasJ_complexMellin_integrableOn_Ioi_three
    {z : Complex} (hz : z.re < 0) :
    IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex))
      (Ioi (3 : Real)) := by
  have hTriple := nicolasJMellinTriple_integrable hz
  have hOuter := hTriple.integral_prod_left
  apply hOuter.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact nicolasJMellinTriple_inner_eq hx.le

theorem nicolasJShiftedComplexContinuationFilled_eq_mellin_of_re_neg
    {z : Complex} (hz : z.re < 0) :
    nicolasJShiftedComplexContinuationFilled z = nicolasJMellin z := by
  unfold nicolasJShiftedComplexContinuationFilled
  calc
    integral (volume.restrict (Ioi (0 : Real)))
        (nicolasJMellinShiftIntegrandFilled z) =
        integral (volume.restrict (Ioi (0 : Real)))
          (nicolasJMellinShiftIntegrand z) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact nicolasJMellinShiftIntegrandFilled_eq_raw hz hu
    _ = nicolasJMellin z :=
      (nicolasJMellin_eq_integral_shift hz).symm

theorem nicolasJMellin_eq_startup_add_tail_of_re_neg
    {X : Real} (hX : 3 <= X) {z : Complex} (hz : z.re < 0) :
    nicolasJMellin z = nicolasJComplexMellinStartup X z +
      integral (volume.restrict (Ioi X)) (fun x : Real =>
        (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) := by
  have hJThree := nicolasJ_complexMellin_integrableOn_Ioi_three hz
  have hJX : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hJStartup : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) (Ioc 3 X) :=
    hJThree.mono_set Ioc_subset_Ioi_self
  unfold nicolasJMellin nicolasJComplexMellinStartup
  rw [<- Ioc_union_Ioi_eq_Ioi hX,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hJStartup
  . exact hJX

theorem nicolasLandauRpowComplexTailMellin_integrableOn
    {X b : Real} (hX : 0 < X) {z : Complex} (hz : z.re < b) :
    IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex))
      (Ioi X) := by
  have hExponent : (z - (b : Complex) - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hBase := integrableOn_Ioi_cpow_of_lt hExponent hX
  apply hBase.congr_fun
  . intro x hx
    have hxPos : 0 < x := hX.trans hx
    have hxNe : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr hxPos.ne'
    change (x : Complex) ^ (z - (b : Complex) - 1) =
      (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)
    rw [Complex.ofReal_cpow hxPos.le]
    rw [<- Complex.cpow_add _ _ hxNe]
    congr 1
    push_cast
    ring
  . exact measurableSet_Ioi

theorem nicolasLandauPositiveComplexMellin_eq_continuation_of_re_neg
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    {z : Complex} (hz : z.re < 0) :
    nicolasLandauPositiveComplexMellin X b z =
      nicolasLandauPositiveComplexContinuationFilled X b z := by
  have hJThree := nicolasJ_complexMellin_integrableOn_Ioi_three hz
  have hJX : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hzB : z.re < b := lt_trans hz hb
  have hRpow := nicolasLandauRpowComplexTailMellin_integrableOn
    hXPos hzB
  have hDecomp : (fun x : Real =>
      (x : Complex) ^ (z - 1) *
        (nicolasLandauPositiveTail b x : Complex)) =
      (fun x : Real =>
        (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) +
      (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) := by
    funext x
    unfold nicolasLandauPositiveTail
    push_cast
    simp only [Pi.add_apply]
    ring
  unfold nicolasLandauPositiveComplexMellin
    nicolasLandauPositiveComplexContinuationFilled
  rw [hDecomp]
  change integral (volume.restrict (Ioi X)) (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex) +
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) = _
  rw [integral_add hJX hRpow]
  rw [nicolasLandauRpowComplexTailMellin_eq_continuation hXPos hzB]
  have hSplit := nicolasJMellin_eq_startup_add_tail_of_re_neg hX hz
  rw [<- nicolasJShiftedComplexContinuationFilled_eq_mellin_of_re_neg hz] at hSplit
  rw [hSplit]
  ring

theorem nicolasLandauComplexMGF_eq_continuationFilled_of_re_neg
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    {z : Complex} (hz : z.re < 0) :
    complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b) z =
      nicolasLandauPositiveComplexContinuationFilled X b z := by
  rw [complexMGF_log_nicolasLandauPositiveMeasure_eq_complexMellin hX hPos]
  exact nicolasLandauPositiveComplexMellin_eq_continuation_of_re_neg
    hX hb hz

def nicolasRightmostRayPoint (rho : Complex) (eps : Real) : Complex :=
  (1 - rho) - (eps : Complex)

theorem nicolasLandauPositiveComplexContinuationFilled_analyticAt_rightmostRay
    {X b : Real} (hX : 3 <= X) {rho : Complex}
    (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex
      (nicolasLandauPositiveComplexContinuationFilled X b)
      (nicolasRightmostRayPoint rho eps) := by
  have hJ := nicolasJShiftedComplexContinuationFilled_analyticAt_rightmostRay
    hZero hHalf hOne hRay hEps
  have hStartup := nicolasJComplexMellinStartup_analyticAt hX
    (nicolasRightmostRayPoint rho eps)
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOne
  have hPointIm : (nicolasRightmostRayPoint rho eps).im = -rho.im := by
    unfold nicolasRightmostRayPoint
    simp
  have hPointNeB : Not (nicolasRightmostRayPoint rho eps = (b : Complex)) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hPointIm, Complex.ofReal_im] at hEqIm
    exact hIm (neg_eq_zero.mp hEqIm)
  have hRpow := nicolasLandauRpowComplexContinuation_analyticAt
    (lt_of_lt_of_le (by norm_num) hX) hPointNeB
  unfold nicolasLandauPositiveComplexContinuationFilled
  exact (hJ.sub hStartup).add hRpow

theorem nicolasLandauComplexMGF_analyticAt_rightmostRay
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    {rho : Complex} (hHalf : (1 / 2 : Real) < rho.re)
    (hLower : 1 - rho.re < b)
    {eps : Real} (hEps : 0 <= eps) :
    AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b))
      (nicolasRightmostRayPoint rho eps) := by
  apply nicolasLandauComplexMGF_analyticAt_of_positive
    hX hb hbHalf hPos
  unfold nicolasRightmostRayPoint
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  linarith [hLower]

theorem nicolasLandauComplexMGF_rightmostRay_analyticAt_real
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    {rho : Complex} (hHalf : (1 / 2 : Real) < rho.re)
    (hLower : 1 - rho.re < b)
    {eps : Real} (hEps : 0 <= eps) :
    AnalyticAt Real (fun e : Real =>
      complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b)
        (nicolasRightmostRayPoint rho e)) eps := by
  have hOuterComplex := nicolasLandauComplexMGF_analyticAt_rightmostRay
    hX hb hbHalf hPos hHalf hLower hEps
  have hOuterReal : AnalyticAt Real
      (complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b))
      (nicolasRightmostRayPoint rho eps) := hOuterComplex.restrictScalars
  have hInner : AnalyticAt Real (nicolasRightmostRayPoint rho) eps := by
    unfold nicolasRightmostRayPoint
    exact analyticAt_const.sub (Complex.ofRealCLM.analyticAt eps)
  exact hOuterReal.comp_of_eq hInner rfl

theorem nicolasLandauPositiveComplexContinuationFilled_rightmostRay_analyticAt_real
    {X b : Real} (hX : 3 <= X) {rho : Complex}
    (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Real (fun e : Real =>
      nicolasLandauPositiveComplexContinuationFilled X b
        (nicolasRightmostRayPoint rho e)) eps := by
  have hOuterComplex :=
    nicolasLandauPositiveComplexContinuationFilled_analyticAt_rightmostRay
      (b := b) hX hZero hHalf hOne hRay hEps
  have hOuterReal : AnalyticAt Real
      (nicolasLandauPositiveComplexContinuationFilled X b)
      (nicolasRightmostRayPoint rho eps) := hOuterComplex.restrictScalars
  have hInner : AnalyticAt Real (nicolasRightmostRayPoint rho) eps := by
    unfold nicolasRightmostRayPoint
    exact analyticAt_const.sub (Complex.ofRealCLM.analyticAt eps)
  exact hOuterReal.comp_of_eq hInner rfl

theorem nicolasLandauComplexMGF_eq_continuationFilled_rightmostRay
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hLower : 1 - rho.re < b)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b)
        (nicolasRightmostRayPoint rho eps) =
      nicolasLandauPositiveComplexContinuationFilled X b
        (nicolasRightmostRayPoint rho eps) := by
  let F : Real -> Complex := fun e : Real =>
    complexMGF (fun x : Real => Real.log x)
      (nicolasLandauPositiveMeasure X b)
      (nicolasRightmostRayPoint rho e)
  let G : Real -> Complex := fun e : Real =>
    nicolasLandauPositiveComplexContinuationFilled X b
      (nicolasRightmostRayPoint rho e)
  have hF : AnalyticOnNhd Real F (Ioi (0 : Real)) := by
    intro e he
    dsimp [F]
    exact nicolasLandauComplexMGF_rightmostRay_analyticAt_real
      hX hb hbHalf hPos hHalf hLower (mem_Ioi.mp he).le
  have hG : AnalyticOnNhd Real G (Ioi (0 : Real)) := by
    intro e he
    dsimp [G]
    exact
      nicolasLandauPositiveComplexContinuationFilled_rightmostRay_analyticAt_real
        hX hZero hHalf hOne hRay (mem_Ioi.mp he)
  have hEqNhd : Filter.EventuallyEq (nhds (2 : Real)) F G := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 : Real) < 2)] with e he
    dsimp [F, G]
    apply nicolasLandauComplexMGF_eq_continuationFilled_of_re_neg
      hX hb hPos
    unfold nicolasRightmostRayPoint
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith [mem_Ioi.mp he]
  have hEqOn : EqOn F G (Ioi (0 : Real)) :=
    hF.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_Ioi (0 : Real)).isPreconnected (by norm_num) hEqNhd
  exact hEqOn hEps

def nicolasJRightmostRayTranslatedScaledKernel
    (rho : Complex) (eps v : Real) : Complex :=
  (v : Complex) * nicolasJMellinShiftIntegrand
    (nicolasRightmostRayPoint rho eps) (v - eps)

theorem nicolasJMellinShiftIntegrandFilled_eq_raw_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps u : Real} (hEps : 0 < eps) (hU : 0 < u) :
    nicolasJMellinShiftIntegrandFilled
        (nicolasRightmostRayPoint rho eps) u =
      nicolasJMellinShiftIntegrand
        (nicolasRightmostRayPoint rho eps) u := by
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hzZero : Not (nicolasRightmostRayPoint rho eps = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold nicolasRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.zero_im] at hEqIm
    apply hIm
    linarith
  let s : Complex := rho + ((eps + u : Real) : Complex)
  have hShift :
      (((u + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps) = s := by
    dsimp [s, nicolasRightmostRayPoint]
    push_cast
    ring
  have hsIm : s.im = rho.im := by
    dsimp [s]
    simp
  have hsZero : Not (s = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.zero_im] at hEqIm
    exact hIm hEqIm
  have hsOne : Not (s = 1) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.one_im] at hEqIm
    exact hIm hEqIm
  have hZeta : Not (riemannZeta s = 0) := by
    dsimp [s]
    exact hRay (eps + u) (by linarith)
  have hBaseRe : 1 < (((u + 1 : Real) : Complex)).re := by
    simp
    linarith
  have hBaseEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hBaseRe
  have hShiftEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw hsZero hsOne hZeta
  unfold nicolasJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzZero]
  unfold slope
  rw [nicolasJShiftNumeratorFilled_zero]
  unfold nicolasJShiftNumeratorFilled nicolasJMellinShiftIntegrand
  rw [hBaseEq, hShift, hShiftEq]
  simp only [sub_zero, smul_eq_mul, vsub_eq_sub]
  field_simp [hzZero]

def nicolasJRightmostRayTranslatedScaledKernelFilled
    (rho : Complex) (eps v : Real) : Complex :=
  (v : Complex) * nicolasJMellinShiftIntegrandFilled
    (nicolasRightmostRayPoint rho eps) (v - eps)

theorem nicolasJRightmostRayTranslatedScaledKernelFilled_eq_raw
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps v : Real} (hEps : 0 < eps) (hEpsV : eps < v) :
    nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v =
      nicolasJRightmostRayTranslatedScaledKernel rho eps v := by
  unfold nicolasJRightmostRayTranslatedScaledKernelFilled
    nicolasJRightmostRayTranslatedScaledKernel
  rw [nicolasJMellinShiftIntegrandFilled_eq_raw_rightmostRay
    hZero hHalf hOneRe hRay hEps (by linarith)]

theorem nicolasJRightmostRayTranslatedScaledKernel_tendsto
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Exists fun d : Complex => And (Not (d = 0))
      (Tendsto (fun p : Prod Real Real =>
          nicolasJRightmostRayTranslatedScaledKernel rho p.1 p.2)
        (nhdsWithin ((0 : Real), (0 : Real))
          {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)})
        (nhds d)) := by
  have hRhoZero : Not (rho = 0) := by
    intro hEq
    rw [hEq] at hHalf
    norm_num at hHalf
  have hRhoOne : Not (rho = 1) := by
    intro hEq
    rw [hEq] at hOneRe
    norm_num at hOneRe
  choose c hc hPole using
    nicolasPsiMellinTailContinuation_three_simplePoleLimit_Ioi
      hZero hRhoZero hRhoOne
  let D : Set (Prod Real Real) :=
    {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)}
  let l : Filter (Prod Real Real) :=
    nhdsWithin ((0 : Real), (0 : Real)) D
  let u : Prod Real Real -> Real := fun p => p.2 - p.1
  let z : Prod Real Real -> Complex := fun p =>
    nicolasRightmostRayPoint rho p.1
  let z0 : Complex := 1 - rho
  have hFst : Tendsto (fun p : Prod Real Real => p.1) l (nhds 0) := by
    exact continuousAt_fst.tendsto.mono_left nhdsWithin_le_nhds
  have hSnd : Tendsto (fun p : Prod Real Real => p.2) l (nhds 0) := by
    exact continuousAt_snd.tendsto.mono_left nhdsWithin_le_nhds
  have hU : Tendsto u l (nhds 0) := by
    dsimp [u]
    simpa using hSnd.sub hFst
  have hSndPos : Filter.Eventually
      (fun p : Prod Real Real => 0 < p.2) l := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.1.trans hp.2
  have hUPos : Filter.Eventually (fun p : Prod Real Real => 0 < u p) l := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    dsimp [u]
    linarith [hp.2]
  have hSndWithin : Tendsto (fun p : Prod Real Real => p.2) l
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro hSnd hSndPos
  have hUWithin : Tendsto u l (nhdsWithin 0 (Ioi (0 : Real))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro hU hUPos
  have hPoleComp : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) *
        nicolasPsiMellinTailContinuation 3 (rho + (p.2 : Complex)))
      l (nhds c) := hPole.comp hSndWithin
  have hBaseArg : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex))) l
      (nhdsWithin 1 (Set.compl {(1 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    . have hCast : Tendsto (fun p : Prod Real Real => (u p : Complex))
          l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hU
      simpa using hCast.add tendsto_const_nhds
    . filter_upwards [hUPos] with p hp
      apply Set.mem_compl_singleton_iff.mpr
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp only [Complex.ofReal_re, Complex.one_re] at hRe
      linarith
  have hBaseTail : Tendsto (fun p : Prod Real Real =>
      nicolasPsiMellinTailContinuation 3
        (((u p + 1 : Real) : Complex))) l
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1) -
        nicolasPsiMellinStartup 3 1)) :=
    nicolasPsiMellinTailContinuation_three_tendsto_one.comp hBaseArg
  have hSndCast : Tendsto (fun p : Prod Real Real => (p.2 : Complex))
      l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hSnd
  have hScaledBase : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) * nicolasPsiMellinTailContinuation 3
        (((u p + 1 : Real) : Complex))) l (nhds 0) := by
    simpa using hSndCast.mul hBaseTail
  have hZ : Tendsto z l (nhds z0) := by
    have hFstCast : Tendsto (fun p : Prod Real Real => (p.1 : Complex))
        l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hFst
    dsimp [z, z0, nicolasRightmostRayPoint]
    simpa using (tendsto_const_nhds.sub hFstCast)
  have hz0Ne : Not (z0 = 0) := by
    dsimp [z0]
    exact sub_ne_zero.mpr (Ne.symm hRhoOne)
  have hNumerator : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex))) l (nhds 1) := by
    have hCast : Tendsto (fun p : Prod Real Real => (u p : Complex))
        l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hU
    simpa using hCast.add tendsto_const_nhds
  have hPrefactor : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex)) / z p) l (nhds (1 / z0)) :=
    hNumerator.div hZ hz0Ne
  have hPowerAt : Tendsto (fun p : Prod Real Real =>
      (3 : Complex) ^ (z p)) l (nhds ((3 : Complex) ^ z0)) := by
    have hContinuous : ContinuousAt (fun w : Complex =>
        (3 : Complex) ^ w) z0 := by
      fun_prop
    exact hContinuous.tendsto.comp hZ
  have hDifference : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) *
          nicolasPsiMellinTailContinuation 3 (rho + (p.2 : Complex)) -
        (3 : Complex) ^ (z p) *
          ((p.2 : Complex) * nicolasPsiMellinTailContinuation 3
            (((u p + 1 : Real) : Complex)))) l (nhds c) := by
    simpa using hPoleComp.sub (hPowerAt.mul hScaledBase)
  let d : Complex := c / z0
  have hd : Not (d = 0) := div_ne_zero hc hz0Ne
  refine Exists.intro d (And.intro hd ?_)
  have hProduct := hPrefactor.mul hDifference
  convert hProduct using 1
  . funext p
    have hShift :
        ((((p.2 - p.1 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1)) =
          rho + (p.2 : Complex) := by
      unfold nicolasRightmostRayPoint
      push_cast
      ring
    unfold nicolasJRightmostRayTranslatedScaledKernel
      nicolasJMellinShiftIntegrand
    rw [hShift]
    dsimp [u, z, nicolasRightmostRayPoint]
    ring
  . dsimp [d]
    ring

theorem exists_nicolasRightmostRayScaledKernel_uniform
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps v : Real, 0 < eps -> eps < v -> v <= r ->
            norm (nicolasJRightmostRayTranslatedScaledKernel rho eps v - d) <=
              norm d / 4))) := by
  choose d hd hLimit using
    nicolasJRightmostRayTranslatedScaledKernel_tendsto hZero hHalf hOneRe
  have hdNorm : 0 < norm d := norm_pos_iff.mpr hd
  have hClose : Filter.Eventually
      (fun p : Prod Real Real =>
        norm (nicolasJRightmostRayTranslatedScaledKernel rho p.1 p.2 - d) <
          norm d / 4)
      (nhdsWithin ((0 : Real), (0 : Real))
        {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)}) := by
    have hBall := hLimit.eventually
      (Metric.ball_mem_nhds d (by positivity : 0 < norm d / 4))
    simpa [Metric.mem_ball, dist_eq_norm] using hBall
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hClose
  choose eta hEta hCloseEta using hClose
  let r : Real := min (eta / 2) (1 / 4)
  have hrPos : 0 < r := by
    dsimp [r]
    exact lt_min (by positivity) (by norm_num)
  have hrHalf : r < 1 / 2 := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrEta : r < eta := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps v hEps hEpsV hVr
  have hVPos : 0 < v := hEps.trans hEpsV
  have hDist : dist (eps, v) ((0 : Real), (0 : Real)) < eta := by
    change max (dist eps 0) (dist v 0) < eta
    rw [max_lt_iff]
    constructor
    . rw [Real.dist_eq, sub_zero, abs_of_pos hEps]
      exact hEpsV.trans_le hVr |>.trans hrEta
    . rw [Real.dist_eq, sub_zero, abs_of_pos hVPos]
      exact hVr.trans_lt hrEta
  exact (hCloseEta hDist (And.intro hEps hEpsV)).le

theorem nicolasJRightmostRayTranslatedScaledKernelFilled_intervalIntegrable
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps r : Real} (hEps : 0 < eps) (hEpsR : eps < r)
    (hWidth : r - eps <= 1) :
    IntervalIntegrable
      (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps)
      volume eps r := by
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hzZero : Not (nicolasRightmostRayPoint rho eps = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold nicolasRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.zero_im] at hEqIm
    apply hIm
    linarith
  apply ContinuousOn.intervalIntegrable
  intro v hv
  have hvIcc : Membership.mem (Icc eps r) v := by
    simpa [uIcc, min_eq_left hEpsR.le, max_eq_right hEpsR.le] using hv
  have hU : 0 <= v - eps := by linarith [hvIcc.1]
  have hULe : v - eps <= 1 := by linarith [hvIcc.2]
  let s : Complex := rho + (v : Complex)
  have hsIm : s.im = rho.im := by
    dsimp [s]
    simp
  have hsZero : Not (s = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.zero_im] at hEqIm
    exact hIm hEqIm
  have hsOne : Not (s = 1) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.one_im] at hEqIm
    exact hIm hEqIm
  have hVPos : 0 < v := hEps.trans_le hvIcc.1
  have hZeta : Not (riemannZeta s = 0) := by
    dsimp [s]
    exact hRay v hVPos
  have hFactor : Not (nicolasZetaPoleFactor s = 0) :=
    nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
  have hShift :
      ((((v - eps + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps)) = s := by
    dsimp [s, nicolasRightmostRayPoint]
    push_cast
    ring
  have hShiftZero : Not
      ((((v - eps + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps) = 0) := by
    rw [hShift]
    exact hsZero
  have hShiftFactor : Not
      (nicolasZetaPoleFactor
        (((v - eps + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps) = 0) := by
    rw [hShift]
    exact hFactor
  have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
    (u := v - eps) (z := nicolasRightmostRayPoint rho eps)
    hU hzZero hShiftZero hShiftFactor
  have hEmbed : ContinuousAt (fun w : Real =>
      (w - eps, nicolasRightmostRayPoint rho eps)) v := by
    fun_prop
  have hTail : ContinuousAt (fun w : Real =>
      nicolasJMellinShiftIntegrandFilled
        (nicolasRightmostRayPoint rho eps) (w - eps)) v := by
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    simpa [Function.comp_def] using hComp
  have hCast : ContinuousAt (fun w : Real => (w : Complex)) v := by
    fun_prop
  unfold nicolasJRightmostRayTranslatedScaledKernelFilled
  exact (hCast.mul hTail).continuousWithinAt

theorem exists_nicolasRightmostRayScaledKernelFilled_uniform
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps v : Real, 0 < eps -> eps < v -> v <= r ->
            norm
              (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v - d) <=
              norm d / 4))) := by
  choose d r hd hrPos hrHalf hUniform using
    exists_nicolasRightmostRayScaledKernel_uniform hZero hHalf hOneRe
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps v hEps hEpsV hVr
  rw [nicolasJRightmostRayTranslatedScaledKernelFilled_eq_raw
    hZero hHalf hOneRe hRay hEps hEpsV]
  exact hUniform eps v hEps hEpsV hVr

theorem exists_nicolasRightmostRayScaledKernel_log_interval_estimate
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps : Real, 0 < eps -> eps < r ->
            norm (intervalIntegral (fun v : Real =>
                HSMul.hSMul (Inv.inv v)
                  (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
                eps r volume -
              HSMul.hSMul (Real.log (r / eps)) d) <=
              (norm d / 4) * abs (Real.log (r / eps))))) := by
  choose d r hd hrPos hrHalf hUniform using
    exists_nicolasRightmostRayScaledKernelFilled_uniform
      hZero hHalf hOneRe hRay
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps hEps hEpsR
  have hInt :=
    nicolasJRightmostRayTranslatedScaledKernelFilled_intervalIntegrable
      hZero hHalf hOneRe hRay hEps hEpsR (by linarith)
  apply norm_intervalIntegral_inv_smul_sub_le_of_intervalIntegrable
    hInt hEps hrPos (by positivity)
  intro v hv
  have hvIoc : Membership.mem (Ioc eps r) v := by
    simpa [uIoc, min_eq_left hEpsR.le, max_eq_right hEpsR.le] using hv
  exact hUniform eps v hEps hvIoc.1 hvIoc.2

theorem nicolasRightmostRay_weighted_scaledKernelFilled_interval_eq
    {rho : Complex} {eps r : Real} (hEps : 0 < eps) (hEpsR : eps < r) :
    intervalIntegral (fun v : Real =>
        HSMul.hSMul (Inv.inv v)
          (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
        eps r volume =
      intervalIntegral
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps))
        0 (r - eps) volume := by
  calc
    intervalIntegral (fun v : Real =>
        HSMul.hSMul (Inv.inv v)
          (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
        eps r volume =
        intervalIntegral (fun v : Real =>
          nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps) (v - eps))
          eps r volume := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hvIcc : Membership.mem (Icc eps r) v := by
        simpa [uIcc, min_eq_left hEpsR.le,
          max_eq_right hEpsR.le] using hv
      have hvPos : 0 < v := hEps.trans_le hvIcc.1
      unfold nicolasJRightmostRayTranslatedScaledKernelFilled
      change ((Inv.inv v : Real) : Complex) *
          ((v : Complex) *
            nicolasJMellinShiftIntegrandFilled
              (nicolasRightmostRayPoint rho eps) (v - eps)) =
        nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps) (v - eps)
      rw [Complex.ofReal_inv]
      field_simp [Complex.ofReal_ne_zero.mpr hvPos.ne']
    _ = intervalIntegral
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps))
        (eps - eps) (r - eps) volume := by
      exact intervalIntegral.integral_comp_sub_right
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps)) eps
    _ = intervalIntegral
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps))
        0 (r - eps) volume := by ring_nf

theorem exists_nicolasRightmostRayCompactSingularIntegral_lowerBound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps : Real, 0 < eps -> eps < r ->
            (3 / 4 : Real) * norm d * Real.log (r / eps) <=
              norm (intervalIntegral
                (nicolasJMellinShiftIntegrandFilled
                  (nicolasRightmostRayPoint rho eps))
                0 (r - eps) volume)))) := by
  choose d r hd hrPos hrHalf hEstimate using
    exists_nicolasRightmostRayScaledKernel_log_interval_estimate
      hZero hHalf hOneRe hRay
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps hEps hEpsR
  let I : Complex := intervalIntegral (fun v : Real =>
      HSMul.hSMul (Inv.inv v)
        (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
      eps r volume
  let A : Complex := HSMul.hSMul (Real.log (r / eps)) d
  have hRatio : 1 < r / eps := (one_lt_div hEps).mpr hEpsR
  have hLogPos : 0 < Real.log (r / eps) := Real.log_pos hRatio
  have hErr : norm (I - A) <=
      (norm d / 4) * Real.log (r / eps) := by
    dsimp [I, A]
    simpa [abs_of_pos hLogPos] using hEstimate eps hEps hEpsR
  have hReverse : norm A - norm I <= norm (I - A) := by
    have hBasic := (le_abs_self (norm A - norm I)).trans
      (abs_norm_sub_norm_le A I)
    simpa [norm_sub_rev] using hBasic
  have hANorm : norm A = Real.log (r / eps) * norm d := by
    dsimp [A]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hLogPos]
  have hLowerI : (3 / 4 : Real) * norm d * Real.log (r / eps) <=
      norm I := by
    rw [hANorm] at hReverse
    have hdNorm : 0 <= norm d := norm_nonneg d
    nlinarith [hReverse.trans hErr]
  dsimp [I] at hLowerI
  have hIntegralEq :
      intervalIntegral (fun v : Real =>
          ((Inv.inv v : Real) : Complex) *
            nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v)
          eps r volume =
        intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          0 (r - eps) volume := by
    simpa [smul_eq_mul] using
      (nicolasRightmostRay_weighted_scaledKernelFilled_interval_eq
        (rho := rho) hEps hEpsR)
  rw [hIntegralEq] at hLowerI
  exact hLowerI

theorem exists_nicolasRightmostRayCompactAwayKernel_bound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {r : Real} (hrPos : 0 < r) (hrHalf : r < 1 / 2) :
    Exists fun M : Real => And (0 <= M)
      (forall eps u : Real,
        Membership.mem (Icc (0 : Real) (r / 2)) eps ->
        Membership.mem (Icc (r / 2) (1 : Real)) u ->
        norm (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps) u) <= M) := by
  let K : Set (Prod Real Real) := fun p =>
    And (Membership.mem (Icc (0 : Real) (r / 2)) p.1)
      (Membership.mem (Icc (r / 2) (1 : Real)) p.2)
  let F : Prod Real Real -> Complex := fun p =>
    nicolasJMellinShiftIntegrandFilled
      (nicolasRightmostRayPoint rho p.1) p.2
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) (r / 2))).prod
      (isCompact_Icc : IsCompact (Icc (r / 2) (1 : Real)))
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), r / 2) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl (by positivity))
      (And.intro le_rfl (by linarith))
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hContinuous : ContinuousOn F K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    change And (Membership.mem (Icc (0 : Real) (r / 2)) p.1)
      (Membership.mem (Icc (r / 2) (1 : Real)) p.2) at hp
    have hzZero : Not (nicolasRightmostRayPoint rho p.1 = 0) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      unfold nicolasRightmostRayPoint at hEqIm
      simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
        Complex.zero_im] at hEqIm
      apply hIm
      linarith
    let s : Complex := rho + ((p.1 + p.2 : Real) : Complex)
    have hsIm : s.im = rho.im := by
      dsimp [s]
      simp
    have hsZero : Not (s = 0) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      rw [hsIm, Complex.zero_im] at hEqIm
      exact hIm hEqIm
    have hsOne : Not (s = 1) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      rw [hsIm, Complex.one_im] at hEqIm
      exact hIm hEqIm
    have hSumPos : 0 < p.1 + p.2 := by
      linarith [hp.1.1, hp.2.1, hrPos]
    have hZeta : Not (riemannZeta s = 0) := by
      dsimp [s]
      exact hRay (p.1 + p.2) hSumPos
    have hFactor : Not (nicolasZetaPoleFactor s = 0) :=
      nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
    have hShift :
        ((((p.2 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1)) = s := by
      dsimp [s, nicolasRightmostRayPoint]
      push_cast
      ring
    have hShiftZero : Not
        ((((p.2 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1) = 0) := by
      rw [hShift]
      exact hsZero
    have hShiftFactor : Not
        (nicolasZetaPoleFactor
          (((p.2 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1) = 0) := by
      rw [hShift]
      exact hFactor
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      (u := p.2) (z := nicolasRightmostRayPoint rho p.1)
      (by linarith [hp.2.1, hrPos]) hzZero hShiftZero hShiftFactor
    have hEmbed : ContinuousAt (fun q : Prod Real Real =>
        (q.2, nicolasRightmostRayPoint rho q.1)) p := by
      unfold nicolasRightmostRayPoint
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    simpa [F, Function.comp_def] using hComp
  choose p hpK hpMax using
    hKCompact.exists_isMaxOn hKNonempty hContinuous.norm
  let M : Real := norm (F p)
  refine Exists.intro M (And.intro (norm_nonneg _) ?_)
  intro eps u hEps hU
  have hPair : K (eps, u) := by
    dsimp [K]
    exact And.intro hEps hU
  simpa [M, F] using hpMax hPair

theorem exists_nicolasRightmostRayCompactAwayIntegral_bound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {r : Real} (hrPos : 0 < r) (hrHalf : r < 1 / 2) :
    Exists fun M : Real => And (0 <= M)
      (forall eps : Real, 0 <= eps -> eps <= r / 2 ->
        norm (intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          (r - eps) 1 volume) <= M) := by
  choose M hMNonneg hKernel using
    exists_nicolasRightmostRayCompactAwayKernel_bound
      hZero hHalf hOneRe hRay hrPos hrHalf
  refine Exists.intro M (And.intro hMNonneg ?_)
  intro eps hEps hEpsLe
  have hLowerNonneg : 0 <= r - eps := by linarith
  have hLowerOne : r - eps <= 1 := by linarith
  have hPointwise : forall u : Real,
      Membership.mem (uIoc (r - eps) (1 : Real)) u ->
      norm (nicolasJMellinShiftIntegrandFilled
        (nicolasRightmostRayPoint rho eps) u) <= M := by
    intro u hu
    have huIoc : Membership.mem (Ioc (r - eps) (1 : Real)) u := by
      simpa [uIoc, min_eq_left hLowerOne,
        max_eq_right hLowerOne] using hu
    apply hKernel eps u
    . exact And.intro hEps hEpsLe
    . exact And.intro (by linarith [huIoc.1]) huIoc.2
  have hNorm := intervalIntegral.norm_integral_le_of_norm_le_const hPointwise
  rw [abs_of_nonneg (by linarith : 0 <= (1 : Real) - (r - eps))] at hNorm
  nlinarith

theorem exists_nicolasRightmostRayCompactIntegral_log_lowerBound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real => Exists fun M : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2) (And (0 <= M)
          (forall eps : Real, 0 < eps -> eps <= r / 2 ->
            (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
              norm (intervalIntegral
                (nicolasJMellinShiftIntegrandFilled
                  (nicolasRightmostRayPoint rho eps))
                0 1 volume))))) := by
  choose d r hd hrPos hrHalf hSingular using
    exists_nicolasRightmostRayCompactSingularIntegral_lowerBound
      hZero hHalf hOneRe hRay
  choose M hMNonneg hAway using
    exists_nicolasRightmostRayCompactAwayIntegral_bound
      hZero hHalf hOneRe hRay hrPos hrHalf
  refine Exists.intro d (Exists.intro r (Exists.intro M
    (And.intro hd (And.intro hrPos (And.intro hrHalf
      (And.intro hMNonneg ?_))))))
  intro eps hEps hEpsLe
  have hEpsR : eps < r := by linarith [hrPos]
  have hLowerNonneg : 0 <= r - eps := by linarith [hEpsLe, hrPos]
  have hLowerOne : r - eps <= 1 := by linarith [hrHalf]
  let f : Real -> Complex :=
    nicolasJMellinShiftIntegrandFilled
      (nicolasRightmostRayPoint rho eps)
  have hIntegrableOn : IntegrableOn f (Ioc (0 : Real) 1) := by
    have hEventually :=
      eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
        hZero hHalf hOneRe hRay hEps
    have hAt := hEventually.self_of_nhds
    simpa [f, nicolasRightmostRayPoint] using hAt
  have hFullIntegrable : IntervalIntegrable f volume 0 1 := by
    rw [intervalIntegrable_iff]
    simpa [uIoc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using hIntegrableOn
  have hLeftIntegrable : IntervalIntegrable f volume 0 (r - eps) := by
    apply hFullIntegrable.mono_set
    intro u hu
    have huSmall : Membership.mem (Icc (0 : Real) (r - eps)) u := by
      simpa [uIcc, min_eq_left hLowerNonneg,
        max_eq_right hLowerNonneg] using hu
    have huFull : Membership.mem (Icc (0 : Real) 1) u :=
      And.intro huSmall.1 (huSmall.2.trans hLowerOne)
    simpa [uIcc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using huFull
  have hRightIntegrable : IntervalIntegrable f volume (r - eps) 1 := by
    apply hFullIntegrable.mono_set
    intro u hu
    have huSmall : Membership.mem (Icc (r - eps) (1 : Real)) u := by
      simpa [uIcc, min_eq_left hLowerOne,
        max_eq_right hLowerOne] using hu
    have huFull : Membership.mem (Icc (0 : Real) 1) u :=
      And.intro (hLowerNonneg.trans huSmall.1) huSmall.2
    simpa [uIcc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using huFull
  let L : Complex := intervalIntegral f 0 (r - eps) volume
  let R : Complex := intervalIntegral f (r - eps) 1 volume
  let T : Complex := intervalIntegral f 0 1 volume
  have hDecomp : L + R = T := by
    dsimp [L, R, T]
    exact intervalIntegral.integral_add_adjacent_intervals
      hLeftIntegrable hRightIntegrable
  have hTriangle : norm L <= norm T + norm R := by
    calc
      norm L = norm ((L + R) - R) := by ring_nf
      _ <= norm (L + R) + norm R := norm_sub_le _ _
      _ = norm T + norm R := by rw [hDecomp]
  have hSing : (3 / 4 : Real) * norm d * Real.log (r / eps) <=
      norm L := by
    dsimp [L, f]
    exact hSingular eps hEps hEpsR
  have hAwayBound : norm R <= M := by
    dsimp [R, f]
    exact hAway eps hEps.le hEpsLe
  have hFinal : (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
      norm T := by
    linarith
  simpa [T, f] using hFinal

theorem nicolasRightmostRayCompactIntegral_norm_tendsto_atTop
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          0 1 volume))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  choose d r M hd hrPos hrHalf hMNonneg hLower using
    exists_nicolasRightmostRayCompactIntegral_log_lowerBound
      hZero hHalf hOneRe hRay
  have hInv : Tendsto (fun eps : Real => Inv.inv eps)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    simpa using (tendsto_inv_nhdsGT_zero :
      Tendsto (fun eps : Real => Inv.inv eps)
        (nhdsWithin 0 (Ioi (0 : Real))) atTop)
  have hRatio : Tendsto (fun eps : Real => r / eps)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    have hMul := Tendsto.const_mul_atTop hrPos hInv
    simpa [div_eq_mul_inv] using hMul
  have hLog : Tendsto (fun eps : Real => Real.log (r / eps))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop :=
    Real.tendsto_log_atTop.comp hRatio
  have hCoefficient : 0 < (3 / 4 : Real) * norm d :=
    mul_pos (by norm_num) (norm_pos_iff.mpr hd)
  have hScaled : Tendsto (fun eps : Real =>
      ((3 / 4 : Real) * norm d) * Real.log (r / eps))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop :=
    Tendsto.const_mul_atTop hCoefficient hLog
  have hLowerTendsto : Tendsto (fun eps : Real =>
      (3 / 4 : Real) * norm d * Real.log (r / eps) - M)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    simpa [mul_assoc, sub_eq_add_neg] using
      (tendsto_atTop_add_const_right
        (nhdsWithin 0 (Ioi (0 : Real))) (-M) hScaled)
  have hSmall : Filter.Eventually (fun eps : Real => eps <= r / 2)
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    have hNhd : Membership.mem (nhds (0 : Real)) (Iio (r / 2)) :=
      Iio_mem_nhds (by positivity)
    have hNhdWithin : Filter.Eventually (fun eps : Real => eps < r / 2)
        (nhdsWithin 0 (Ioi (0 : Real))) :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hNhd
    filter_upwards [hNhdWithin] with eps hEps
    exact hEps.le
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
        norm (intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          0 1 volume))
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    filter_upwards [self_mem_nhdsWithin, hSmall] with eps hEps hEpsLe
    exact hLower eps (mem_Ioi.mp hEps) hEpsLe
  exact tendsto_atTop_mono'
    (nhdsWithin 0 (Ioi (0 : Real))) hEventualLower hLowerTendsto

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRayEndpoint
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      (nicolasRightmostRayPoint rho 0) := by
  let center : Complex := nicolasRightmostRayPoint rho 0
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hCenterIm : center.im = -rho.im := by
    dsimp [center, nicolasRightmostRayPoint]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    apply hIm
    linarith [hCenterIm, hZeroIm]
  have hCenterNorm : 0 < norm center := norm_pos_iff.mpr hCenterNe
  have hCenterRe : center.re = 1 - rho.re := by
    dsimp [center, nicolasRightmostRayPoint]
    simp
  have hReMargin : 0 < (3 / 4 : Real) - center.re := by
    rw [hCenterRe]
    linarith
  let d : Real := norm center / 2
  let R : Real := min (norm center / 2)
    (((3 / 4 : Real) - center.re) / 2)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hRPos : 0 < R := by
    dsimp [R]
    exact lt_min (by positivity) (by positivity)
  have hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z) := by
    intro z hz
    have hzDist : dist z center < R := by
      simpa [Metric.mem_ball] using hz
    have hDistNorm : dist z center < norm center / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_left _ _)
    have hDistRe : dist z center <
        ((3 / 4 : Real) - center.re) / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_right _ _)
    have hReDiff : z.re - center.re <= dist z center := by
      calc
        z.re - center.re <= abs (z.re - center.re) := le_abs_self _
        _ = abs ((z - center).re) :=
          congrArg abs (Complex.sub_re z center).symm
        _ <= norm (z - center) := Complex.abs_re_le_norm _
        _ = dist z center := by rw [dist_eq_norm]
    have hTriangle : norm center <= dist center z + norm z := by
      have h := dist_triangle center z 0
      simpa [dist_zero_right] using h
    have hNorm : d <= norm z := by
      dsimp [d]
      rw [dist_comm center z] at hTriangle
      linarith
    exact And.intro (by linarith) hNorm
  apply nicolasJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    hRPos hd
  intro z hz
  exact hGeometry z (by simpa [center] using hz)

theorem nicolasJShiftedComplexContinuationFilledLarge_rightmostRay_tendsto
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Tendsto (fun eps : Real =>
        nicolasJShiftedComplexContinuationFilledLarge
          (nicolasRightmostRayPoint rho eps))
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds (nicolasJShiftedComplexContinuationFilledLarge
        (nicolasRightmostRayPoint rho 0))) := by
  have hOuter :=
    (nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRayEndpoint
      hZero hHalf hOneRe).continuousAt.tendsto
  have hInner : Tendsto (nicolasRightmostRayPoint rho)
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds (nicolasRightmostRayPoint rho 0)) := by
    have hContinuous : ContinuousAt (nicolasRightmostRayPoint rho) 0 := by
      unfold nicolasRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  exact hOuter.comp hInner

theorem nicolasJShiftedComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (nicolasJShiftedComplexContinuationFilled
          (nicolasRightmostRayPoint rho eps)))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let C : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilledCompact
      (nicolasRightmostRayPoint rho eps)
  let G : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilledLarge
      (nicolasRightmostRayPoint rho eps)
  let H : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilled
      (nicolasRightmostRayPoint rho eps)
  have hCompact : Tendsto (fun eps : Real => norm (C eps)) l atTop := by
    have hBase := nicolasRightmostRayCompactIntegral_norm_tendsto_atTop
      hZero hHalf hOneRe hRay
    simpa [l, C, nicolasJShiftedComplexContinuationFilledCompact,
      intervalIntegral.integral_of_le zero_le_one] using hBase
  let G0 : Complex := nicolasJShiftedComplexContinuationFilledLarge
    (nicolasRightmostRayPoint rho 0)
  have hLarge : Tendsto G l (nhds G0) := by
    simpa [l, G, G0] using
      nicolasJShiftedComplexContinuationFilledLarge_rightmostRay_tendsto
        hZero hHalf hOneRe
  have hLargeBound : Filter.Eventually (fun eps : Real =>
      norm (G eps) <= norm G0 + 1) l := by
    have hBall := hLarge.eventually
      (Metric.ball_mem_nhds G0 (by norm_num : (0 : Real) < 1))
    filter_upwards [hBall] with eps hEps
    have hDist : norm (G eps - G0) < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hEps
    calc
      norm (G eps) = norm ((G eps - G0) + G0) := by ring_nf
      _ <= norm (G eps - G0) + norm G0 := norm_add_le _ _
      _ <= norm G0 + 1 := by linarith
  have hEq : Filter.Eventually (fun eps : Real => H eps = C eps + G eps) l := by
    filter_upwards [self_mem_nhdsWithin] with eps hEps
    have hAt :=
      (eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
        hZero hHalf hOneRe hRay (mem_Ioi.mp hEps)).self_of_nhds
    simpa [H, C, G, nicolasRightmostRayPoint] using hAt
  have hLowerTendsto : Tendsto (fun eps : Real =>
      norm (C eps) - (norm G0 + 1)) l atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right l (-(norm G0 + 1)) hCompact)
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      norm (C eps) - (norm G0 + 1) <= norm (H eps)) l := by
    filter_upwards [hLargeBound, hEq] with eps hGBound hAt
    have hTriangle : norm (C eps) <= norm (H eps) + norm (G eps) := by
      calc
        norm (C eps) = norm ((C eps + G eps) - G eps) := by ring_nf
        _ = norm (H eps - G eps) := by rw [hAt]
        _ <= norm (H eps) + norm (G eps) := norm_sub_le _ _
    linarith
  exact tendsto_atTop_mono' l hEventualLower hLowerTendsto

theorem nicolasLandauPositiveComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
    {X b : Real} (hX : 3 <= X)
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (nicolasLandauPositiveComplexContinuationFilled X b
          (nicolasRightmostRayPoint rho eps)))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let J : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilled
      (nicolasRightmostRayPoint rho eps)
  let D : Real -> Complex := fun eps =>
    -nicolasJComplexMellinStartup X (nicolasRightmostRayPoint rho eps) +
      nicolasLandauRpowComplexContinuation X b
        (nicolasRightmostRayPoint rho eps)
  let P : Real -> Complex := fun eps =>
    nicolasLandauPositiveComplexContinuationFilled X b
      (nicolasRightmostRayPoint rho eps)
  have hJ : Tendsto (fun eps : Real => norm (J eps)) l atTop := by
    simpa [l, J] using
      nicolasJShiftedComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
        hZero hHalf hOneRe hRay
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hPointNeB : Not (nicolasRightmostRayPoint rho 0 = (b : Complex)) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold nicolasRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im] at hEqIm
    apply hIm
    linarith
  have hCorrectionAnalytic : AnalyticAt Complex (fun z : Complex =>
      -nicolasJComplexMellinStartup X z +
        nicolasLandauRpowComplexContinuation X b z)
      (nicolasRightmostRayPoint rho 0) := by
    exact (nicolasJComplexMellinStartup_analyticAt hX _).neg.add
      (nicolasLandauRpowComplexContinuation_analyticAt
        (lt_of_lt_of_le (by norm_num) hX) hPointNeB)
  let D0 : Complex :=
    -nicolasJComplexMellinStartup X (nicolasRightmostRayPoint rho 0) +
      nicolasLandauRpowComplexContinuation X b
        (nicolasRightmostRayPoint rho 0)
  have hInner : Tendsto (nicolasRightmostRayPoint rho) l
      (nhds (nicolasRightmostRayPoint rho 0)) := by
    have hContinuous : ContinuousAt (nicolasRightmostRayPoint rho) 0 := by
      unfold nicolasRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hD : Tendsto D l (nhds D0) := by
    have hComp := hCorrectionAnalytic.continuousAt.tendsto.comp hInner
    simpa [D, D0, Function.comp_def] using hComp
  have hDBound : Filter.Eventually (fun eps : Real =>
      norm (D eps) <= norm D0 + 1) l := by
    have hBall := hD.eventually
      (Metric.ball_mem_nhds D0 (by norm_num : (0 : Real) < 1))
    filter_upwards [hBall] with eps hEps
    have hDist : norm (D eps - D0) < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hEps
    calc
      norm (D eps) = norm ((D eps - D0) + D0) := by ring_nf
      _ <= norm (D eps - D0) + norm D0 := norm_add_le _ _
      _ <= norm D0 + 1 := by linarith
  have hEq : forall eps : Real, P eps = J eps + D eps := by
    intro eps
    unfold P J D nicolasLandauPositiveComplexContinuationFilled
    ring
  have hLowerTendsto : Tendsto (fun eps : Real =>
      norm (J eps) - (norm D0 + 1)) l atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right l (-(norm D0 + 1)) hJ)
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      norm (J eps) - (norm D0 + 1) <= norm (P eps)) l := by
    filter_upwards [hDBound] with eps hBound
    have hTriangle : norm (J eps) <= norm (P eps) + norm (D eps) := by
      calc
        norm (J eps) = norm ((J eps + D eps) - D eps) := by ring_nf
        _ = norm (P eps - D eps) := by rw [hEq]
        _ <= norm (P eps) + norm (D eps) := norm_sub_le _ _
    linarith
  exact tendsto_atTop_mono' l hEventualLower hLowerTendsto

theorem exists_nicolasJ_omegaMinus_of_riemannZeta_zero_re_gt_half
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Exists fun b : Real => And (0 < b) (And (b < 1 / 2)
      (AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)))) := by
  choose rhoMax hMaxZero hMaxHalf hMaxOne hMaxIm hRay using
    exists_rightmost_horizontal_riemannZeta_zero
      hZero hHalf hOneRe
  let b : Real := ((1 - rhoMax.re) + 1 / 2) / 2
  have hbPos : 0 < b := by
    dsimp [b]
    linarith
  have hbLower : 1 - rhoMax.re < b := by
    dsimp [b]
    linarith
  have hbHalf : b < 1 / 2 := by
    dsimp [b]
    linarith
  refine Exists.intro b (And.intro hbPos (And.intro hbHalf ?_))
  by_contra hNot
  choose X hX hPos hAnalytic using
    exists_nicolasLandauComplexMGF_analytic_halfPlane_of_not_omegaMinus
      hbPos hbHalf.le hNot
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let MGF : Real -> Complex := fun eps =>
    complexMGF (fun x : Real => Real.log x)
      (nicolasLandauPositiveMeasure X b)
      (nicolasRightmostRayPoint rhoMax eps)
  let P : Real -> Complex := fun eps =>
    nicolasLandauPositiveComplexContinuationFilled X b
      (nicolasRightmostRayPoint rhoMax eps)
  have hPointRe : (nicolasRightmostRayPoint rhoMax 0).re =
      1 - rhoMax.re := by
    unfold nicolasRightmostRayPoint
    simp
  have hMGFAnalytic : AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b))
      (nicolasRightmostRayPoint rhoMax 0) := by
    apply hAnalytic
    rw [hPointRe]
    exact hbLower
  let MGF0 : Complex := complexMGF (fun x : Real => Real.log x)
    (nicolasLandauPositiveMeasure X b)
    (nicolasRightmostRayPoint rhoMax 0)
  have hInner : Tendsto (nicolasRightmostRayPoint rhoMax) l
      (nhds (nicolasRightmostRayPoint rhoMax 0)) := by
    have hContinuous : ContinuousAt (nicolasRightmostRayPoint rhoMax) 0 := by
      unfold nicolasRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hMGF : Tendsto MGF l (nhds MGF0) := by
    have hComp := hMGFAnalytic.continuousAt.tendsto.comp hInner
    simpa [MGF, MGF0, Function.comp_def] using hComp
  have hEq : Filter.Eventually (fun eps : Real => MGF eps = P eps) l := by
    filter_upwards [self_mem_nhdsWithin] with eps hEps
    dsimp [MGF, P]
    exact nicolasLandauComplexMGF_eq_continuationFilled_rightmostRay
      hX hbPos hbHalf.le hPos hMaxZero hMaxHalf hMaxOne hbLower hRay
      (mem_Ioi.mp hEps)
  have hPNormFinite : Tendsto (fun eps : Real => norm (P eps)) l
      (nhds (norm MGF0)) := by
    have hMGFNorm := hMGF.norm
    apply hMGFNorm.congr'
    filter_upwards [hEq] with eps hAt
    rw [hAt]
  have hPNormTop : Tendsto (fun eps : Real => norm (P eps)) l atTop := by
    simpa [l, P] using
      nicolasLandauPositiveComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
        hX hMaxZero hMaxHalf hMaxOne hRay
  exact not_tendsto_nhds_of_tendsto_atTop hPNormTop (norm MGF0) hPNormFinite

theorem exists_nicolasJ_omegaMinus_of_not_riemannHypothesis
    (hNotRH : Not RiemannHypothesis) :
    Exists fun b : Real => And (0 < b) (And (b < 1 / 2)
      (AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)))) := by
  choose rho hZero hHalf hOneRe using
    exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  exact exists_nicolasJ_omegaMinus_of_riemannZeta_zero_re_gt_half
    hZero hHalf hOneRe

end

end Robin1984
