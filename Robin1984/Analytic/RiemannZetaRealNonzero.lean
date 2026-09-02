import Robin1984.NicolasLandau.NicolasLandauPositiveTail

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# The Riemann zeta function on the positive real axis

Compatibility declarations expose the upstream-ready real-zeta nonvanishing
argument under the project's historical names. The remaining declarations are
specific to the Nicolas--Landau continuation developed by this project.
-/

namespace Robin1984

open Filter MeasureTheory Set

noncomputable section

abbrev nicolasEulerSaw : Real -> Real := RiemannZeta.eulerSaw
alias nicolasEulerSaw_pos := RiemannZeta.eulerSaw_pos
alias nicolasEulerSaw_le_one := RiemannZeta.eulerSaw_le_one
alias nicolasEulerSaw_eq_sub_nat_on_cell :=
  RiemannZeta.eulerSaw_eq_sub_nat_on_cell
alias iUnion_nicolasEulerCells := RiemannZeta.iUnion_eulerCells
alias pairwise_disjoint_nicolasEulerCells :=
  RiemannZeta.pairwise_disjoint_eulerCells

noncomputable abbrev nicolasEulerRemainderIntegrand : Real -> Real -> Real :=
  RiemannZeta.eulerRemainderIntegrand
noncomputable abbrev nicolasEulerRemainder : Real -> Real :=
  RiemannZeta.eulerRemainder
alias nicolasEulerRemainderIntegrable := RiemannZeta.eulerRemainderIntegrable
alias integral_nicolasEulerCell_eq_term :=
  RiemannZeta.integral_eulerCell_eq_term
alias nicolasEulerRemainder_eq_termTSum :=
  RiemannZeta.eulerRemainder_eq_termTSum

noncomputable abbrev nicolasEulerDensity : Real -> NNReal :=
  RiemannZeta.eulerDensity
alias measurable_nicolasEulerDensity := RiemannZeta.measurable_eulerDensity
noncomputable abbrev nicolasEulerMeasure : Measure Real :=
  RiemannZeta.eulerMeasure
alias nicolasEulerDensity_coe := RiemannZeta.eulerDensity_coe
alias nicolasEulerDensity_mul_exp_eq_integrand :=
  RiemannZeta.eulerDensity_mul_exp_eq_integrand
alias mgf_nicolasEulerMeasure_neg_eq_remainder :=
  RiemannZeta.mgf_eulerMeasure_neg_eq_remainder
alias integrable_exp_log_nicolasEulerMeasure_of_neg :=
  RiemannZeta.integrable_exp_log_eulerMeasure_of_neg
alias neg_mem_nicolasEulerIntegrableExpSet :=
  RiemannZeta.neg_mem_eulerIntegrableExpSet
alias zetaAsymptoticsTermTSum_analyticAt_of_pos :=
  RiemannZeta.termTSum_analyticAt_of_pos
alias zetaAsymptoticsTermTSum_nonneg := RiemannZeta.termTSum_nonneg

alias nicolasZetaPoleFactor_eq_termTSum_of_one_lt :=
  RiemannZeta.poleFactor_eq_termTSum_of_one_lt
alias nicolasZetaPoleFactor_re_eq_termTSum_of_pos :=
  RiemannZeta.poleFactor_re_eq_termTSum_of_pos
alias nicolasZetaPoleFactor_ne_zero_of_mem_Ioo_zero_one :=
  RiemannZeta.poleFactor_ne_zero_of_mem_Ioo_zero_one
alias riemannZeta_real_ne_zero_of_mem_Ioo_zero_one :=
  RiemannZeta.real_ne_zero_of_mem_Ioo_zero_one
alias nicolasZetaPoleFactor_ne_zero_of_pos_real :=
  RiemannZeta.poleFactor_ne_zero_of_pos_real
alias riemannZeta_real_ne_zero_of_pos := RiemannZeta.real_ne_zero_of_pos

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_pos_real
    {s : Real} (hs : 0 < s) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled (s : Complex) := by
  by_cases hsOne : s = 1
  case pos =>
    subst s
    exact nicolasPsiMellinTailContinuationFilled_analyticAt_one
  case neg =>
    have hsZero : Not ((s : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr hs.ne'
    have hFactor := nicolasZetaPoleFactor_ne_zero_of_pos_real hs
    unfold nicolasPsiMellinTailContinuationFilled
    exact (nicolasPsiMellinContinuationFilled_analyticAt hsZero hFactor).sub
      (nicolasPsiMellinStartup_three_analyticAt (s : Complex))


theorem norm_nicolasJShiftNumeratorFilled_le_threeQuarter
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.closedBall (0 : Complex) (3 / 4 : Real)) z) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
  have hzNorm : norm z <= (3 / 4 : Real) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hzRe : z.re <= (3 / 4 : Real) :=
    (Complex.re_le_norm z).trans hzNorm
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hDen1 : (1 / 4 : Real) < s1.re - 1 := by
    dsimp [s1, s0]
    linarith
  have hShiftRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs1
  have hShiftNumerator : (3 : Real) ^ (1 - s1.re) <=
      (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [s1, s0]
    linarith
  have hShiftPowerNonneg : 0 <= (3 : Real) ^ (1 - s1.re) :=
    Real.rpow_nonneg (by norm_num) _
  have hShiftFraction : (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
      4 * (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
          (3 : Real) ^ (1 - s1.re) / (1 / 4 : Real) :=
        div_le_div_of_nonneg_left hShiftPowerNonneg (by norm_num) hDen1.le
      _ = 4 * (3 : Real) ^ (1 - s1.re) := by ring
      _ <= 4 * (3 : Real) ^ (-u + (3 / 4 : Real)) :=
        mul_le_mul_of_nonneg_left hShiftNumerator (by norm_num)
  have hShift : norm (nicolasPsiMellinTailContinuationFilled s1) <=
      4 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      norm (nicolasPsiMellinTailContinuationFilled s1) <=
          (Real.log 4 + 5) *
            ((3 : Real) ^ (1 - s1.re) / (s1.re - 1)) := hShiftRaw
      _ <= (Real.log 4 + 5) *
          (4 * (3 : Real) ^ (-u + (3 / 4 : Real))) :=
        mul_le_mul_of_nonneg_left hShiftFraction (by positivity)
      _ = 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring
  have hBaseRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs0
  have hBase : norm (nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) * (3 : Real) ^ (-u) := by
    have huPos : 0 < u := lt_trans zero_lt_one hu
    have hPowNonneg : 0 <= (3 : Real) ^ (-u) :=
      Real.rpow_nonneg (by norm_num) _
    have hS0Exponent : 1 - s0.re = -u := by
      dsimp [s0]
      ring
    have hS0Denominator : s0.re - 1 = u := by
      dsimp [s0]
      ring
    rw [hS0Exponent, hS0Denominator] at hBaseRaw
    calc
      norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (Real.log 4 + 5) * ((3 : Real) ^ (-u) / u) := hBaseRaw
      _ <= (Real.log 4 + 5) * ((3 : Real) ^ (-u) / 1) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hPowNonneg zero_lt_one hu.le)
          (by positivity)
      _ = (Real.log 4 + 5) * (3 : Real) ^ (-u) := by ring
  have hPowerNorm : norm ((3 : Complex) ^ z) =
      (3 : Real) ^ z.re := by
    change norm (((3 : Real) : Complex) ^ z) =
      (3 : Real) ^ z.re
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hPowerProduct : norm ((3 : Complex) ^ z *
      nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    rw [norm_mul, hPowerNorm]
    calc
      (3 : Real) ^ z.re *
          norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (3 : Real) ^ z.re *
            ((Real.log 4 + 5) * (3 : Real) ^ (-u)) :=
        mul_le_mul_of_nonneg_left hBase
          (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.log 4 + 5) *
          ((3 : Real) ^ z.re * (3 : Real) ^ (-u)) := by ring
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re + (-u)) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 3)]
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re - u) := by
        congr 2
      _ <= (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
  unfold nicolasJShiftNumeratorFilled
  change norm (nicolasPsiMellinTailContinuationFilled s1 -
      (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <= _
  calc
    norm (nicolasPsiMellinTailContinuationFilled s1 -
        (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <=
        norm (nicolasPsiMellinTailContinuationFilled s1) +
          norm ((3 : Complex) ^ z *
            nicolasPsiMellinTailContinuationFilled s0) := norm_sub_le _ _
    _ <= 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) +
        (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) :=
      add_le_add hShift hPowerProduct
    _ = 5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring

theorem nicolasJShiftNumeratorFilled_differentiableOn_threeQuarter
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) (3 / 4 : Real)) := by
  intro z hz
  have hzNorm : norm z < (3 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (3 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hTail : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s1 :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs1
  have hAffine : AnalyticAt Complex (fun w : Complex => s0 - w) z :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s0 - w)) z := by
    have hComp := hTail.comp_of_eq hAffine (by dsimp [s1])
    apply hComp.congr
    exact Eventually.of_forall (fun _ => rfl)
  have hPowerDifferentiable : Differentiable Complex
      (fun w : Complex => (3 : Complex) ^ w) := by
    intro w
    exact DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (by norm_num))
  have hPower : AnalyticAt Complex
      (fun w : Complex => (3 : Complex) ^ w) z :=
    hPowerDifferentiable.analyticAt z
  have hTailConst : AnalyticAt Complex (fun _ : Complex =>
      nicolasPsiMellinTailContinuationFilled s0) z := analyticAt_const
  unfold nicolasJShiftNumeratorFilled
  change DifferentiableWithinAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s0 - w) -
        (3 : Complex) ^ w *
          nicolasPsiMellinTailContinuationFilled s0)
    (Metric.ball (0 : Complex) (3 / 4 : Real)) z
  exact (hShift.sub (hPower.mul hTailConst)).differentiableAt.differentiableWithinAt

theorem norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (3 / 4 : Real)) z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      (20 / 3 : Real) * (Real.log 4 + 5) * (u + 1) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
  let R : Real := 3 / 4
  let M : Real := 5 * (Real.log 4 + 5) *
    (3 : Real) ^ (-u + (3 / 4 : Real))
  have hMaps : MapsTo (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) R)
      (Metric.closedBall (nicolasJShiftNumeratorFilled u 0) M) := by
    intro w hw
    rw [nicolasJShiftNumeratorFilled_zero]
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_nicolasJShiftNumeratorFilled_le_threeQuarter hu
      (Metric.ball_subset_closedBall hw)
  have hDslope := Complex.norm_dslope_le_div_of_mapsTo_ball
    (nicolasJShiftNumeratorFilled_differentiableOn_threeQuarter hu)
    hMaps hz
  have huOnePos : 0 < u + 1 := by linarith
  unfold nicolasJMellinShiftIntegrandFilled
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huOnePos]
  calc
    (u + 1) * norm (dslope (nicolasJShiftNumeratorFilled u) 0 z) <=
        (u + 1) * (M / R) :=
      mul_le_mul_of_nonneg_left hDslope huOnePos.le
    _ = (20 / 3 : Real) * (Real.log 4 + 5) * (u + 1) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
      dsimp [M, R]
      ring

def nicolasJLargeMajorantHalf (u : Real) : Real :=
  (20 / 3 : Real) * (Real.log 4 + 5) * (u + 1) *
    (3 : Real) ^ (-u + (3 / 4 : Real))

theorem nicolasJLargeMajorantHalf_integrableOn :
    IntegrableOn nicolasJLargeMajorantHalf (Ioi (1 : Real)) := by
  have hLog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hExp : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : Real)) (s := (0 : Real)) (b := Real.log 3)
      (by norm_num) (by norm_num) hLog
    have hSubset : Ioi (1 : Real) <= Ioi (0 : Real) := by
      intro u hu
      exact zero_lt_one.trans (mem_Ioi.mp hu)
    apply (h.mono_set hSubset).congr_fun _ measurableSet_Ioi
    intro u hu
    simp
  have hUExp : IntegrableOn
      (fun u : Real => u * Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : Real)) (s := (1 : Real)) (b := Real.log 3)
      (by norm_num) (by norm_num) hLog
    have hSubset : Ioi (1 : Real) <= Ioi (0 : Real) := by
      intro u hu
      exact zero_lt_one.trans (mem_Ioi.mp hu)
    apply (h.mono_set hSubset).congr_fun _ measurableSet_Ioi
    intro u hu
    simp
  have hLinear : IntegrableOn
      (fun u : Real => (u + 1) * Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    apply (hUExp.add hExp).congr_fun _ measurableSet_Ioi
    intro u hu
    change u * Real.exp (-(Real.log 3) * u) +
      Real.exp (-(Real.log 3) * u) =
        (u + 1) * Real.exp (-(Real.log 3) * u)
    ring
  have hScaled : IntegrableOn
      (fun u : Real =>
        ((20 / 3 : Real) * (Real.log 4 + 5) *
            Real.exp (3 * Real.log 3 / 4)) *
          ((u + 1) * Real.exp (-(Real.log 3) * u)))
      (Ioi (1 : Real)) :=
    hLinear.const_mul
      ((20 / 3 : Real) * (Real.log 4 + 5) *
        Real.exp (3 * Real.log 3 / 4))
  apply hScaled.congr_fun _ measurableSet_Ioi
  intro u hu
  unfold nicolasJLargeMajorantHalf
  rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 3)]
  rw [show Real.log 3 * (-u + (3 / 4 : Real)) =
      3 * Real.log 3 / 4 + (-(Real.log 3) * u) by ring]
  rw [Real.exp_add]
  ring

theorem nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex
      (fun z : Complex => nicolasJMellinShiftIntegrandFilled z u)
      (Metric.ball (0 : Complex) (3 / 4 : Real)) := by
  intro z hz
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      (by linarith)).differentiableAt.differentiableWithinAt
  case neg =>
    have hNumeratorAt : DifferentiableAt Complex
        (nicolasJShiftNumeratorFilled u) z :=
      (nicolasJShiftNumeratorFilled_differentiableOn_threeQuarter
        hu z hz).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz)
    have hDslopeAt : DifferentiableAt Complex
        (dslope (nicolasJShiftNumeratorFilled u) 0) z :=
      (differentiableAt_dslope_of_ne hzZero).2 hNumeratorAt
    unfold nicolasJMellinShiftIntegrandFilled
    exact (analyticAt_const.differentiableAt.mul hDslopeAt).differentiableWithinAt

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le_half
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <=
      8 * nicolasJLargeMajorantHalf u := by
  let f : Complex -> Complex := fun w : Complex =>
    nicolasJMellinShiftIntegrandFilled w u
  let R : Real := 1 / 4
  let M : Real := nicolasJLargeMajorantHalf u
  have hSmallSubset : Metric.ball z R <=
      Metric.ball (0 : Complex) (3 / 4 : Real) := by
    intro w hw
    rw [Metric.mem_ball] at hw hz
    rw [Metric.mem_ball]
    calc
      dist w 0 <= dist w z + dist z 0 := dist_triangle w z 0
      _ < (1 / 4 : Real) + (1 / 2 : Real) := add_lt_add hw hz
      _ = (3 / 4 : Real) := by norm_num
  have hzOuter : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self (by norm_num)
  have hDiff : DifferentiableOn Complex f (Metric.ball z R) :=
    (nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter hu).mono
      hSmallSubset
  have hMaps : MapsTo f (Metric.ball z R)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwOuter := hSmallSubset hw
    have hwBound : norm (f w) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorantHalf] using
        norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter hu hwOuter
    have hzBound : norm (f z) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorantHalf] using
        norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter hu hzOuter
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps (by norm_num : 0 < R)
  change norm (deriv f z) <= 8 * M
  calc
    norm (deriv f z) <= (2 * M) / R := hCauchy
    _ = 8 * M := by
      dsimp [R]
      ring

def nicolasJLargeDerivativeMajorantHalf (u : Real) : Real :=
  8 * nicolasJLargeMajorantHalf u

theorem nicolasJLargeDerivativeMajorantHalf_integrableOn :
    IntegrableOn nicolasJLargeDerivativeMajorantHalf (Ioi (1 : Real)) := by
  unfold nicolasJLargeDerivativeMajorantHalf
  exact nicolasJLargeMajorantHalf_integrableOn.const_mul 8

theorem nicolasJShiftNumeratorFilled_continuousOn_u_threeQuarter
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z) :
    ContinuousOn (fun u : Real => nicolasJShiftNumeratorFilled u z)
      (Ioi (1 : Real)) := by
  let s0 : Real -> Complex := fun u : Real => ((u + 1 : Real) : Complex)
  let s1 : Real -> Complex := fun u : Real => s0 u - z
  have hS0 : Continuous s0 := by
    dsimp [s0]
    fun_prop
  have hS1 : Continuous s1 := by
    dsimp [s1]
    exact hS0.sub continuous_const
  intro u hu
  have huOne : 1 < u := mem_Ioi.mp hu
  have hzNorm : norm z < (3 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (3 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  have hs0 : 1 < (s0 u).re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < (s1 u).re := by
    dsimp [s1, s0]
    linarith
  have hTail0 : ContinuousAt (fun v : Real =>
      nicolasPsiMellinTailContinuationFilled (s0 v)) u :=
    (nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs0).continuousAt.comp
      hS0.continuousAt
  have hTail1 : ContinuousAt (fun v : Real =>
      nicolasPsiMellinTailContinuationFilled (s1 v)) u :=
    (nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs1).continuousAt.comp
      hS1.continuousAt
  unfold nicolasJShiftNumeratorFilled
  change ContinuousWithinAt (fun v : Real =>
    nicolasPsiMellinTailContinuationFilled (s1 v) -
      (3 : Complex) ^ z *
        nicolasPsiMellinTailContinuationFilled (s0 v))
    (Ioi (1 : Real)) u
  exact (hTail1.sub (continuousAt_const.mul hTail0)).continuousWithinAt

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_u_threeQuarter_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hNumeratorZ :=
    nicolasJShiftNumeratorFilled_continuousOn_u_threeQuarter hz
  have hZeroMem : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) (0 : Complex) :=
    Metric.mem_ball_self (by norm_num)
  have hNumeratorZero :=
    nicolasJShiftNumeratorFilled_continuousOn_u_threeQuarter hZeroMem
  have hU : Continuous (fun u : Real => ((u + 1 : Real) : Complex)) := by
    fun_prop
  have hInv : Continuous (fun _ : Real => Inv.inv (z - 0)) :=
    continuous_const
  have hEq : (fun u : Real => nicolasJMellinShiftIntegrandFilled z u) =
      (fun u : Real => ((u + 1 : Real) : Complex) *
        Inv.inv (z - 0) *
          (nicolasJShiftNumeratorFilled u z -
            nicolasJShiftNumeratorFilled u 0)) := by
    funext u
    unfold nicolasJMellinShiftIntegrandFilled
    rw [dslope_of_ne _ hzZero]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    ring
  rw [hEq]
  exact (hU.continuousOn.mul hInv.continuousOn).mul
    (hNumeratorZ.sub hNumeratorZero)

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero
  case neg =>
    have hzOuter : Membership.mem
        (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
      rw [Metric.mem_ball, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact
      (nicolasJMellinShiftIntegrandFilled_continuousOn_u_threeQuarter_of_ne
        hzOuter hzZero).aestronglyMeasurable measurableSet_Ioi

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_threeQuarter
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero
  case neg =>
    exact
      (nicolasJMellinShiftIntegrandFilled_continuousOn_u_threeQuarter_of_ne
        hz hzZero).aestronglyMeasurable measurableSet_Ioi

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_large_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hzOuter : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  apply Integrable.mono' nicolasJLargeMajorantHalf_integrableOn
    (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half hz)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa [nicolasJLargeMajorantHalf] using
    norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter
      (mem_Ioi.mp hu) hzOuter

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioi (1 : Real))) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasJDerivativeStep n)
  have hzNorm : norm z < (1 / 2 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzOuter : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hShiftOuter : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real))
      (z + nicolasJDerivativeStep n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    calc
      norm (z + nicolasJDerivativeStep n) <=
          norm z + norm (nicolasJDerivativeStep n) := norm_add_le _ _
      _ < (1 / 2 : Real) + (1 / 8 : Real) :=
        add_lt_add_of_lt_of_le hzNorm (norm_nicolasJDerivativeStep_lt n)
      _ < (3 / 4 : Real) := by norm_num
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    have hShift :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_threeQuarter
        (hShiftOuter n)
    have hBase :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_threeQuarter
        hzOuter
    have hEq : slopeSeq n = fun u : Real =>
        Inv.inv ((z + nicolasJDerivativeStep n) - z) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasJDerivativeStep n) u -
            nicolasJMellinShiftIntegrandFilled z u) := by
      funext u
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub]
    rw [hEq]
    exact ((hShift.sub hBase).const_mul
      (Inv.inv ((z + nicolasJDerivativeStep n) - z))).aemeasurable
  have hStepWithin : Tendsto nicolasJDerivativeStep atTop
      (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro nicolasJDerivativeStep_tendsto_zero
      (Eventually.of_forall (fun n : Nat =>
        Set.mem_compl_singleton_iff.mpr
          (nicolasJDerivativeStep_ne_zero n)))
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
        (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)))
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huOne : 1 < u := mem_Ioi.mp hu
    have hDiffAt : DifferentiableAt Complex
        (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) z :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter
        huOne z hzOuter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hzOuter)
    have hSlope := hDiffAt.hasDerivAt.tendsto_slope_zero.comp hStepWithin
    change Tendsto (fun n : Nat =>
      Inv.inv (nicolasJDerivativeStep n) *
        (nicolasJMellinShiftIntegrandFilled
            (z + nicolasJDerivativeStep n) u -
          nicolasJMellinShiftIntegrandFilled z u))
      atTop (nhds (deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
    dsimp [slopeSeq]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
    exact hSlope
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    HasDerivAt nicolasJShiftedComplexContinuationFilledLarge
      (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) z := by
  let s : Set Complex := Metric.ball (0 : Complex) (1 / 2 : Real)
  let F : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    nicolasJMellinShiftIntegrandFilled w u
  let F' : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
  have hsNhd : Membership.mem (nhds z) s := by
    dsimp [s]
    exact Metric.isOpen_ball.mem_nhds hz
  have hFMeas : Filter.Eventually
      (fun w : Complex => AEStronglyMeasurable (F w)
        (volume.restrict (Ioi (1 : Real)))) (nhds z) := by
    filter_upwards [hsNhd] with w hw
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half hw
  have hFInt : Integrable (F z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact nicolasJMellinShiftIntegrandFilled_integrableOn_large_half hz
  have hF'Meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half hz
  have hBound : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        norm (F' w u) <= nicolasJLargeDerivativeMajorantHalf u)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    dsimp [F', s]
    unfold nicolasJLargeDerivativeMajorantHalf
    exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le_half
      (mem_Ioi.mp hu) hw
  have hDiff : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        HasDerivAt (fun v : Complex => F v u) (F' w u) w)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hwOuter : Membership.mem
        (Metric.ball (0 : Complex) (3 / 4 : Real)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hAt : DifferentiableAt Complex
        (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter
        (mem_Ioi.mp hu) w hwOuter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hwOuter)
    dsimp [F, F']
    exact hAt.hasDerivAt
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F')
    (bound := nicolasJLargeDerivativeMajorantHalf)
    hsNhd hFMeas hFInt hF'Meas hBound
    nicolasJLargeDerivativeMajorantHalf_integrableOn hDiff
  unfold nicolasJShiftedComplexContinuationFilledLarge
  simpa [F, F'] using hMain.2

theorem nicolasJShiftedComplexContinuationFilledLarge_differentiableOn_half :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilledLarge
      (Metric.ball (0 : Complex) (1 / 2 : Real)) := by
  intro z hz
  exact (nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt_half
    hz).differentiableAt.differentiableWithinAt

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      (sigma : Complex) := by
  apply
    nicolasJShiftedComplexContinuationFilledLarge_differentiableOn_half.analyticAt
  apply Metric.isOpen_ball.mem_nhds
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hSigmaPos]
  exact hSigma

end

end Robin1984
