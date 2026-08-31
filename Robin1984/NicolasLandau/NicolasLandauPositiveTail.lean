import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import Robin1984.NicolasLandau.NicolasLandau

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# Nicolas-Landau positive tail measure

This file specializes the strict positive-transform principle to the exact
tail `nicolasJ x + x ^ (-b)`.  The logarithmic coordinate turns its Mellin
transform into an ordinary moment-generating function.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

def nicolasLandauPositiveTail (b x : Real) : Real :=
  nicolasJ x + x ^ (-b)

def nicolasLandauPositiveDensity (b x : Real) : ENNReal :=
  ENNReal.ofReal (x ^ (-1 : Real) * nicolasLandauPositiveTail b x)

def nicolasLandauPositiveMeasure (X b : Real) : Measure Real :=
  (volume.restrict (Ioi X)).withDensity
    (nicolasLandauPositiveDensity b)

def nicolasLandauPositiveMellin (X b a : Real) : Real :=
  integral (volume.restrict (Ioi X)) (fun x : Real =>
    x ^ (a - 1) * nicolasLandauPositiveTail b x)

def nicolasLandauRpowMellinContinuation (X b a : Real) : Real :=
  X ^ (a - b) / (b - a)

def nicolasJShiftedRealContinuation (a : Real) : Real :=
  Complex.re (integral (volume.restrict (Ioi (0 : Real)))
    (nicolasJMellinShiftIntegrand (a : Complex)))

def nicolasJRealMellinStartup (X a : Real) : Real :=
  integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
    x ^ (a - 1) * nicolasJ x)

def nicolasLandauPositiveMellinContinuation (X b a : Real) : Real :=
  nicolasJShiftedRealContinuation a - nicolasJRealMellinStartup X a +
    nicolasLandauRpowMellinContinuation X b a

def nicolasPsiMellinContinuationFilled (s : Complex) : Complex :=
  -(logDeriv nicolasZetaPoleFactor s + 1) / s

theorem nicolasPsiMellinContinuationFilled_analyticAt_one :
    AnalyticAt Complex nicolasPsiMellinContinuationFilled 1 := by
  have hFactor : AnalyticAt Complex nicolasZetaPoleFactor 1 :=
    nicolasZetaPoleFactor_differentiable.analyticAt 1
  have hFactorDeriv : AnalyticAt Complex
      (deriv nicolasZetaPoleFactor) 1 :=
    nicolasZetaPoleFactor_differentiable.deriv.analyticAt 1
  have hLogDeriv : AnalyticAt Complex
      (logDeriv nicolasZetaPoleFactor) 1 := by
    unfold logDeriv
    exact hFactorDeriv.div hFactor (by simp)
  unfold nicolasPsiMellinContinuationFilled
  have hOne : AnalyticAt Complex (fun _ : Complex => (1 : Complex)) 1 :=
    analyticAt_const
  have hNumerator : AnalyticAt Complex
      (fun s : Complex => -(logDeriv nicolasZetaPoleFactor s + 1)) 1 :=
    (hLogDeriv.add hOne).neg
  exact hNumerator.div analyticAt_id (by norm_num)

theorem nicolasPsiMellinContinuationFilled_eq_raw
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    nicolasPsiMellinContinuationFilled s =
      nicolasPsiMellinContinuation s := by
  exact (nicolasPsiMellinContinuation_eq_poleFactor
    hsZero hsOne hZeta).symm

theorem nicolasPsiMellinStartup_three_differentiableAt (s0 : Complex) :
    DifferentiableAt Complex (nicolasPsiMellinStartup 3) s0 := by
  letI : AddCommGroup Complex := Complex.addCommGroup
  letI : Module Complex Complex := Semiring.toModule
  let F : Complex -> Real -> Complex := fun s t =>
    (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1))
  let F' : Complex -> Real -> Complex := fun s t =>
    -((Real.log t : Real) : Complex) * F s t
  let base : Real -> Complex := fun t =>
    (nicolasPsiError t : Complex) * (t : Complex) ^ (-3 : Complex)
  let ratio : Complex -> Real -> Complex := fun s t =>
    (t : Complex) ^ ((2 : Complex) - s)
  let majorant : Real -> Real := fun t =>
    norm (base t) * (3 : Real) ^ (abs s0.re + 4)
  have hBaseIntegrable : Integrable base
      (volume.restrict (Ioc (1 : Real) 3)) := by
    dsimp [base]
    change IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-3 : Complex)) (Ioc (1 : Real) 3)
    have h :=
      (nicolasPsiErrorMellin_integrable (s := (2 : Complex))
        (by norm_num)).mono_set
        (show Ioc (1 : Real) 3 <= Ioi 1 from Ioc_subset_Ioi_self)
    apply h.congr_fun
    . intro t ht
      congr 2
      norm_num
    . exact measurableSet_Ioc
  have hMajorantIntegrable : Integrable majorant
      (volume.restrict (Ioc (1 : Real) 3)) := by
    have h := hBaseIntegrable.norm.const_mul
      ((3 : Real) ^ (abs s0.re + 4))
    simpa [majorant, mul_comm] using h
  have hMeasurable : forall s : Complex, AEStronglyMeasurable (F s)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    intro s
    have hRatioContinuous : ContinuousOn (ratio s) (Ioc (1 : Real) 3) := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      dsimp [ratio]
      have htPos : 0 < t := lt_trans zero_lt_one ht.1
      exact (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 htPos)).comp
          Complex.continuous_ofReal.continuousAt
    have hProduct := hBaseIntegrable.aestronglyMeasurable.mul
      (hRatioContinuous.aestronglyMeasurable measurableSet_Ioc)
    apply hProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one ht.1))
    dsimp [F, base, ratio]
    rw [mul_assoc, <- Complex.cpow_add _ _ htZero]
    congr 2
    ring
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall t : Real, 1 < t -> t <= 3 ->
        norm (F s t) <= majorant t := by
    intro s hs t htOneStrict htThree
    have hDist : norm (s - s0) < 1 := by
      simpa [dist_eq_norm] using hs
    have hReAbs : abs (s.re - s0.re) <= norm (s - s0) := by
      simpa using Complex.abs_re_le_norm (s - s0)
    have hReLower : s0.re - 1 < s.re := by
      have hAbsLt : abs (s.re - s0.re) < 1 := lt_of_le_of_lt hReAbs hDist
      linarith [(abs_lt.mp hAbsLt).1]
    have htPos : 0 < t := lt_trans zero_lt_one htOneStrict
    have htOne : 1 <= t := le_of_lt htOneStrict
    have hExponent : 2 - s.re <= abs s0.re + 4 := by
      have hNeg : -s0.re <= abs s0.re := neg_le_abs s0.re
      linarith
    have hExponentNonneg : 0 <= abs s0.re + 4 := by positivity
    have hRatioBound : norm (ratio s t) <=
        (3 : Real) ^ (abs s0.re + 4) := by
      dsimp [ratio]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htPos]
      calc
        t ^ (2 - s.re) <= t ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow_of_exponent_le htOne hExponent
        _ <= (3 : Real) ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow (le_of_lt htPos) htThree hExponentNonneg
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt htPos)
    dsimp [F]
    rw [show -(s + 1) = (-3 : Complex) + ((2 : Complex) - s) by ring,
      Complex.cpow_add _ _ htZero, norm_mul]
    dsimp [majorant, base]
    simp only [norm_mul]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hRatioBound
        (mul_nonneg (norm_nonneg ((nicolasPsiError t : Complex)))
          (norm_nonneg ((t : Complex) ^ (-3 : Complex)))))
  have hFIntegrable : Integrable (F s0)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    apply Integrable.mono hMajorantIntegrable (hMeasurable s0)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hMajorantNonneg : 0 <= majorant t := by
      dsimp [majorant]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hMajorantNonneg]
    exact hBound s0 (by simp [dist_self]) t ht.1 ht.2
  have hDerivativeMeasurable : AEStronglyMeasurable (F' s0)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    have hRealLogOn : ContinuousOn (fun t : Real => Real.log t)
        (Ioc (1 : Real) 3) := by
      apply Real.continuousOn_log.mono
      intro t ht
      exact Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (lt_trans zero_lt_one ht.1))
    have hRealLog : AEStronglyMeasurable (fun t : Real => Real.log t)
        (volume.restrict (Ioc (1 : Real) 3)) :=
      hRealLogOn.aestronglyMeasurable measurableSet_Ioc
    have hLog : AEStronglyMeasurable
        (fun t : Real => ((Real.log t : Real) : Complex))
        (volume.restrict (Ioc (1 : Real) 3)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hRealLog
    exact hLog.neg.mul (hMeasurable s0)
  have hDerivativeBound : Filter.Eventually
      (fun t : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        norm (F' s t) <= 3 * majorant t)
      (ae (volume.restrict (Ioc (1 : Real) 3))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    have htPos : 0 < t := lt_trans zero_lt_one ht.1
    have hLogNonneg : 0 <= Real.log t := Real.log_nonneg ht.1.le
    have hLogBound : Real.log t <= 3 := by
      have hLogSub := Real.log_le_sub_one_of_pos htPos
      linarith [ht.2]
    have hFBound : norm (F s t) <= majorant t :=
      hBound s (by simpa [Metric.mem_ball] using hs) t ht.1 ht.2
    dsimp [F']
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hLogNonneg]
    exact mul_le_mul hLogBound hFBound (norm_nonneg _) (by norm_num)
  have hDerivativeIntegrable : Integrable (fun t : Real => 3 * majorant t)
      (volume.restrict (Ioc (1 : Real) 3)) :=
    hMajorantIntegrable.const_mul 3
  have hDerivative : Filter.Eventually
      (fun t : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        HasDerivAt (fun z : Complex => F z t) (F' s t) s)
      (ae (volume.restrict (Ioc (1 : Real) 3))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    have htPos : 0 < t := lt_trans zero_lt_one ht.1
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt htPos)
    have hExponent : HasDerivAt (fun z : Complex => -(z + 1)) (-1) s := by
      have hRaw := ((hasDerivAt_id' s).add_const 1).neg
      exact hRaw.congr_of_eventuallyEq
        (Eventually.of_forall (fun _ => rfl))
    have hPower := hExponent.const_cpow (Or.inl htZero)
    have hProduct := hPower.const_smul (nicolasPsiError t : Complex)
    have hProduct' : HasDerivAt
        (fun z : Complex => (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(z + 1)))
        ((nicolasPsiError t : Complex) *
          ((t : Complex) ^ (-(s + 1)) * Complex.log (t : Complex) * -1)) s := by
      convert hProduct using 1 <;> try rfl
    dsimp [F, F']
    apply hProduct'.congr_deriv
    rw [Complex.ofReal_log htPos.le]
    ring
  unfold nicolasPsiMellinStartup
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s0 zero_lt_one)
    (Eventually.of_forall hMeasurable) hFIntegrable
    hDerivativeMeasurable hDerivativeBound hDerivativeIntegrable hDerivative
  exact hMain.2.differentiableAt

theorem nicolasPsiMellinStartup_three_differentiable :
    Differentiable Complex (nicolasPsiMellinStartup 3) :=
  nicolasPsiMellinStartup_three_differentiableAt

theorem nicolasPsiMellinStartup_three_analyticAt (s0 : Complex) :
    AnalyticAt Complex (nicolasPsiMellinStartup 3) s0 :=
  nicolasPsiMellinStartup_three_differentiable.analyticAt s0

def nicolasPsiMellinTailContinuationFilled (s : Complex) : Complex :=
  nicolasPsiMellinContinuationFilled s - nicolasPsiMellinStartup 3 s

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_one :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled 1 := by
  unfold nicolasPsiMellinTailContinuationFilled
  exact nicolasPsiMellinContinuationFilled_analyticAt_one.sub
    (nicolasPsiMellinStartup_three_analyticAt 1)

theorem nicolasPsiMellinTailContinuationFilled_eq_raw
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    nicolasPsiMellinTailContinuationFilled s =
      nicolasPsiMellinTailContinuation 3 s := by
  unfold nicolasPsiMellinTailContinuationFilled
    nicolasPsiMellinTailContinuation
  rw [nicolasPsiMellinContinuationFilled_eq_raw hsZero hsOne hZeta]

theorem nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero
    {s : Complex} (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    Not (nicolasZetaPoleFactor s = 0) := by
  intro hFactor
  have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hsOne
  rw [hFactor, zero_div] at hIdentity
  exact hZeta hIdentity

theorem nicolasPsiMellinContinuationFilled_analyticAt
    {s : Complex} (hsZero : Not (s = 0))
    (hFactor : Not (nicolasZetaPoleFactor s = 0)) :
    AnalyticAt Complex nicolasPsiMellinContinuationFilled s := by
  have hPoleFactor : AnalyticAt Complex nicolasZetaPoleFactor s :=
    nicolasZetaPoleFactor_differentiable.analyticAt s
  have hPoleFactorDeriv : AnalyticAt Complex
      (deriv nicolasZetaPoleFactor) s :=
    nicolasZetaPoleFactor_differentiable.deriv.analyticAt s
  have hLogDeriv : AnalyticAt Complex
      (logDeriv nicolasZetaPoleFactor) s := by
    unfold logDeriv
    exact hPoleFactorDeriv.div hPoleFactor hFactor
  have hOne : AnalyticAt Complex (fun _ : Complex => (1 : Complex)) s :=
    analyticAt_const
  have hNumerator : AnalyticAt Complex
      (fun w : Complex => -(logDeriv nicolasZetaPoleFactor w + 1)) s :=
    (hLogDeriv.add hOne).neg
  unfold nicolasPsiMellinContinuationFilled
  exact hNumerator.div analyticAt_id hsZero

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s := by
  have hsZero : Not (s = 0) := by
    intro hZero
    rw [hZero] at hs
    norm_num at hs
  have hsOne : Not (s = 1) := by
    intro hOne
    rw [hOne] at hs
    norm_num at hs
  have hZeta : Not (riemannZeta s = 0) :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have hFactor := nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
  unfold nicolasPsiMellinTailContinuationFilled
  exact (nicolasPsiMellinContinuationFilled_analyticAt hsZero hFactor).sub
    (nicolasPsiMellinStartup_three_analyticAt s)

theorem nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    nicolasPsiMellinTailContinuationFilled s =
      nicolasPsiMellinTailContinuation 3 s := by
  have hsZero : Not (s = 0) := by
    intro hZero
    rw [hZero] at hs
    norm_num at hs
  have hsOne : Not (s = 1) := by
    intro hOne
    rw [hOne] at hs
    norm_num at hs
  exact nicolasPsiMellinTailContinuationFilled_eq_raw
    hsZero hsOne (riemannZeta_ne_zero_of_one_lt_re hs)

theorem abs_nicolasPsiError_le_linear
    {t : Real} (ht : 0 <= t) :
    abs (nicolasPsiError t) <= (Real.log 4 + 5) * t := by
  have hPsiNonneg : 0 <= Chebyshev.psi t := Chebyshev.psi_nonneg t
  have hPsi := Chebyshev.psi_le_const_mul_self ht
  unfold nicolasPsiError
  calc
    abs (Chebyshev.psi t - t) <=
        abs (Chebyshev.psi t) + abs t := abs_sub _ _
    _ = Chebyshev.psi t + t := by
      rw [abs_of_nonneg hPsiNonneg, abs_of_nonneg ht]
    _ <= (Real.log 4 + 4) * t + t := by
      simpa [add_comm] using add_le_add_right hPsi t
    _ = (Real.log 4 + 5) * t := by ring

theorem norm_nicolasPsiMellinTailContinuationFilled_le
    {s : Complex} (hs : 1 < s.re) :
    norm (nicolasPsiMellinTailContinuationFilled s) <=
      (Real.log 4 + 5) * (3 ^ (1 - s.re) / (s.re - 1)) := by
  let c : Real := Real.log 4 + 5
  have hcPos : 0 < c := by
    dsimp [c]
    positivity
  have hPowerIntegrable : IntegrableOn
      (fun t : Real => t ^ (-s.re)) (Ioi (3 : Real)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hMajorantIntegrable : IntegrableOn
      (fun t : Real => c * t ^ (-s.re)) (Ioi (3 : Real)) :=
    hPowerIntegrable.const_mul c
  have hIntegralEq :
      integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          (nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1))) =
        nicolasPsiMellinTailContinuationFilled s := by
    calc
      integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          (nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1))) =
          nicolasPsiMellinTailContinuation 3 s :=
        nicolasPsiErrorTailMellin_eq_continuation (by norm_num) hs
      _ = nicolasPsiMellinTailContinuationFilled s :=
        (nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hs).symm
  have hNormIntegral :
      norm (integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          (nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1)))) <=
        integral (volume.restrict (Ioi (3 : Real)))
          (fun t : Real => c * t ^ (-s.re)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hMajorantIntegrable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := lt_trans (by norm_num) ht
    have hError := abs_nicolasPsiError_le_linear htPos.le
    have hPowNonneg : 0 <= t ^ (-(s + 1)).re :=
      Real.rpow_nonneg htPos.le _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos htPos]
    calc
      abs (nicolasPsiError t) * t ^ (-(s + 1)).re <=
          (c * t) * t ^ (-(s + 1)).re :=
        mul_le_mul_of_nonneg_right (by simpa [c] using hError) hPowNonneg
      _ = c * t ^ (-s.re) := by
        calc
          (c * t) * t ^ (-(s + 1)).re =
              c * (t ^ (1 : Real) * t ^ (-(s + 1)).re) := by
            rw [Real.rpow_one]
            ring
          _ = c * t ^ ((1 : Real) + (-(s + 1)).re) := by
            rw [Real.rpow_add htPos]
          _ = c * t ^ (-s.re) := by
            congr 2
            simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
            ring
  rw [<- hIntegralEq]
  calc
    norm (integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1)))) <=
        integral (volume.restrict (Ioi (3 : Real)))
          (fun t : Real => c * t ^ (-s.re)) := hNormIntegral
    _ = c * (-3 ^ (-s.re + 1) / (-s.re + 1)) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
    _ = (Real.log 4 + 5) * (3 ^ (1 - s.re) / (s.re - 1)) := by
      dsimp [c]
      have hDen : Not (s.re - 1 = 0) := ne_of_gt (sub_pos.mpr hs)
      have hDenLeft : Not (-s.re + 1 = 0) := by linarith
      field_simp [hDen, hDenLeft]
      ring


def nicolasJShiftNumeratorFilled (u : Real) (z : Complex) : Complex :=
  nicolasPsiMellinTailContinuationFilled
      (((u + 1 : Real) : Complex) - z) -
    (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled
      ((u + 1 : Real) : Complex)

theorem nicolasJShiftNumeratorFilled_zero (u : Real) :
    nicolasJShiftNumeratorFilled u 0 = 0 := by
  unfold nicolasJShiftNumeratorFilled
  simp

theorem norm_nicolasJShiftNumeratorFilled_le
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.closedBall (0 : Complex) (1 / 4 : Real)) z) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      3 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by
  have hzNorm : norm z <= (1 / 4 : Real) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hzRe : z.re <= (1 / 4 : Real) :=
    (Complex.re_le_norm z).trans hzNorm
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hDen1 : (3 / 4 : Real) < s1.re - 1 := by
    dsimp [s1, s0]
    linarith
  have hShiftRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs1
  have hShiftNumerator : (3 : Real) ^ (1 - s1.re) <=
      (3 : Real) ^ (-u + (1 / 4 : Real)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [s1, s0]
    linarith
  have hShiftPowerNonneg : 0 <= (3 : Real) ^ (1 - s1.re) :=
    Real.rpow_nonneg (by norm_num) _
  have hShiftFraction : (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
      2 * (3 : Real) ^ (-u + (1 / 4 : Real)) := by
    calc
      (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
          (3 : Real) ^ (1 - s1.re) / (3 / 4 : Real) :=
        div_le_div_of_nonneg_left hShiftPowerNonneg (by norm_num) hDen1.le
      _ <= 2 * (3 : Real) ^ (1 - s1.re) := by
        nlinarith
      _ <= 2 * (3 : Real) ^ (-u + (1 / 4 : Real)) :=
        mul_le_mul_of_nonneg_left hShiftNumerator (by norm_num)
  have hShift : norm (nicolasPsiMellinTailContinuationFilled s1) <=
      2 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by
    calc
      norm (nicolasPsiMellinTailContinuationFilled s1) <=
          (Real.log 4 + 5) *
            ((3 : Real) ^ (1 - s1.re) / (s1.re - 1)) := hShiftRaw
      _ <= (Real.log 4 + 5) *
          (2 * (3 : Real) ^ (-u + (1 / 4 : Real))) :=
        mul_le_mul_of_nonneg_left hShiftFraction (by positivity)
      _ = 2 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (1 / 4 : Real)) := by ring
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
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by
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
          (3 : Real) ^ (-u + (1 / 4 : Real)) := by
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
    _ <= 2 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (1 / 4 : Real)) +
        (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (1 / 4 : Real)) :=
      add_le_add hShift hPowerProduct
    _ = 3 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by ring

theorem nicolasJShiftNumeratorFilled_differentiableOn_quarter
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) (1 / 4 : Real)) := by
  intro z hz
  have hzNorm : norm z < (1 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (1 / 4 : Real) :=
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
    (Metric.ball (0 : Complex) (1 / 4 : Real)) z
  exact (hShift.sub (hPower.mul hTailConst)).differentiableAt.differentiableWithinAt

theorem nicolasJShiftNumeratorFilled_analyticAt_zero
    {u : Real} (hu : 0 < u) :
    AnalyticAt Complex (nicolasJShiftNumeratorFilled u) 0 := by
  let s : Complex := ((u + 1 : Real) : Complex)
  have hs : 1 < s.re := by
    dsimp [s]
    simp
    linarith
  have hTail : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs
  have hAffine : AnalyticAt Complex (fun z : Complex => s - z) 0 :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex
      (fun z : Complex =>
        nicolasPsiMellinTailContinuationFilled (s - z)) 0 :=
    by
      have hComp := hTail.comp_of_eq hAffine (by simp)
      apply hComp.congr
      exact Eventually.of_forall (fun _ => rfl)
  have hPowerDifferentiable : Differentiable Complex
      (fun z : Complex => (3 : Complex) ^ z) := by
    intro z
    exact DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (by norm_num))
  have hPower : AnalyticAt Complex
      (fun z : Complex => (3 : Complex) ^ z) 0 :=
    hPowerDifferentiable.analyticAt 0
  have hTailConst : AnalyticAt Complex
      (fun _ : Complex => nicolasPsiMellinTailContinuationFilled s) 0 :=
    analyticAt_const
  unfold nicolasJShiftNumeratorFilled
  change AnalyticAt Complex (fun z : Complex =>
    nicolasPsiMellinTailContinuationFilled (s - z) -
      (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s) 0
  exact hShift.sub (hPower.mul hTailConst)

def nicolasJMellinShiftIntegrandFilled (z : Complex) (u : Real) : Complex :=
  ((u + 1 : Real) : Complex) *
    dslope (nicolasJShiftNumeratorFilled u) 0 z

theorem norm_nicolasJMellinShiftIntegrandFilled_le
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      12 * (Real.log 4 + 5) * (u + 1) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by
  let R : Real := 1 / 4
  let M : Real := 3 * (Real.log 4 + 5) *
    (3 : Real) ^ (-u + (1 / 4 : Real))
  have hMNonneg : 0 <= M := by
    dsimp [M]
    positivity
  have hMaps : MapsTo (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) R)
      (Metric.closedBall (nicolasJShiftNumeratorFilled u 0) M) := by
    intro w hw
    rw [nicolasJShiftNumeratorFilled_zero]
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_nicolasJShiftNumeratorFilled_le hu
      (Metric.ball_subset_closedBall hw)
  have hDslope := Complex.norm_dslope_le_div_of_mapsTo_ball
    (nicolasJShiftNumeratorFilled_differentiableOn_quarter hu)
    hMaps hz
  have huOnePos : 0 < u + 1 := by linarith
  unfold nicolasJMellinShiftIntegrandFilled
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huOnePos]
  calc
    (u + 1) * norm (dslope (nicolasJShiftNumeratorFilled u) 0 z) <=
        (u + 1) * (M / R) :=
      mul_le_mul_of_nonneg_left hDslope huOnePos.le
    _ = 12 * (Real.log 4 + 5) * (u + 1) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by
      dsimp [M, R]
      ring

def nicolasJLargeMajorant (u : Real) : Real :=
  12 * (Real.log 4 + 5) * (u + 1) *
    (3 : Real) ^ (-u + (1 / 4 : Real))

theorem nicolasJLargeMajorant_integrableOn :
    IntegrableOn nicolasJLargeMajorant (Ioi (1 : Real)) := by
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
        (12 * (Real.log 4 + 5) * Real.exp (Real.log 3 / 4)) *
          ((u + 1) * Real.exp (-(Real.log 3) * u)))
      (Ioi (1 : Real)) :=
    hLinear.const_mul
      (12 * (Real.log 4 + 5) * Real.exp (Real.log 3 / 4))
  apply hScaled.congr_fun _ measurableSet_Ioi
  intro u hu
  unfold nicolasJLargeMajorant
  rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 3)]
  rw [show Real.log 3 * (-u + (1 / 4 : Real)) =
      Real.log 3 / 4 + (-(Real.log 3) * u) by ring]
  rw [Real.exp_add]
  ring

theorem nicolasJMellinShiftIntegrandFilled_analyticAt_zero
    {u : Real} (hu : 0 < u) :
    AnalyticAt Complex (fun z : Complex =>
      nicolasJMellinShiftIntegrandFilled z u) 0 := by
  have hNumerator := nicolasJShiftNumeratorFilled_analyticAt_zero hu
  have hPunctured : Filter.Eventually
      (fun z : Complex => DifferentiableAt Complex
        (dslope (nicolasJShiftNumeratorFilled u) 0) z)
      (nhdsWithin 0 (Set.compl {(0 : Complex)})) := by
    filter_upwards
        [hNumerator.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with z hzAnalytic hzNe
    exact (differentiableAt_dslope_of_ne
      (Set.mem_compl_singleton_iff.mp hzNe)).2 hzAnalytic.differentiableAt
  have hDslopeContinuous : ContinuousAt
      (dslope (nicolasJShiftNumeratorFilled u) 0) 0 :=
    continuousAt_dslope_same.2 hNumerator.differentiableAt
  have hDslope : AnalyticAt Complex
      (dslope (nicolasJShiftNumeratorFilled u) 0) 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      hPunctured hDslopeContinuous
  unfold nicolasJMellinShiftIntegrandFilled
  exact analyticAt_const.mul hDslope

theorem nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex
      (fun z : Complex => nicolasJMellinShiftIntegrandFilled z u)
      (Metric.ball (0 : Complex) (1 / 4 : Real)) := by
  intro z hz
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      (by linarith)).differentiableAt.differentiableWithinAt
  case neg =>
    have hNumeratorAt : DifferentiableAt Complex
        (nicolasJShiftNumeratorFilled u) z :=
      (nicolasJShiftNumeratorFilled_differentiableOn_quarter hu z hz).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz)
    have hDslopeAt : DifferentiableAt Complex
        (dslope (nicolasJShiftNumeratorFilled u) 0) z :=
      (differentiableAt_dslope_of_ne hzZero).2 hNumeratorAt
    unfold nicolasJMellinShiftIntegrandFilled
    exact (analyticAt_const.differentiableAt.mul hDslopeAt).differentiableWithinAt

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <=
      16 * nicolasJLargeMajorant u := by
  let f : Complex -> Complex := fun w : Complex =>
    nicolasJMellinShiftIntegrandFilled w u
  let R : Real := 1 / 8
  let M : Real := nicolasJLargeMajorant u
  have hSmallSubset : Metric.ball z R <=
      Metric.ball (0 : Complex) (1 / 4 : Real) := by
    intro w hw
    rw [Metric.mem_ball] at hw hz
    rw [Metric.mem_ball]
    calc
      dist w 0 <= dist w z + dist z 0 := dist_triangle w z 0
      _ < (1 / 8 : Real) + (1 / 8 : Real) := add_lt_add hw hz
      _ = (1 / 4 : Real) := by norm_num
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self (by norm_num)
  have hDiff : DifferentiableOn Complex f (Metric.ball z R) :=
    (nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter hu).mono
      hSmallSubset
  have hMaps : MapsTo f (Metric.ball z R)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwQuarter := hSmallSubset hw
    have hwBound : norm (f w) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorant] using
        norm_nicolasJMellinShiftIntegrandFilled_le hu hwQuarter
    have hzBound : norm (f z) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorant] using
        norm_nicolasJMellinShiftIntegrandFilled_le hu hzQuarter
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps (by norm_num : 0 < R)
  change norm (deriv f z) <= 16 * M
  calc
    norm (deriv f z) <= (2 * M) / R := hCauchy
    _ = 16 * M := by
      dsimp [R]
      ring

theorem nicolasJShiftNumeratorFilled_continuousOn_u
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
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
  have hzNorm : norm z < (1 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (1 / 4 : Real) :=
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

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hNumeratorZ := nicolasJShiftNumeratorFilled_continuousOn_u hz
  have hZeroMem : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) (0 : Complex) :=
    Metric.mem_ball_self (by norm_num)
  have hNumeratorZero :=
    nicolasJShiftNumeratorFilled_continuousOn_u hZeroMem
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

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) :=
  (nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_ne
    hz hzZero).aestronglyMeasurable measurableSet_Ioi

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled 0 u)
      (volume.restrict (Ioi (1 : Real))) := by
  let zseq : Nat -> Complex := fun n : Nat =>
    (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex)
  have hZPos : forall n : Nat,
      0 < (1 : Real) / (8 * ((n : Real) + 1)) := by
    intro n
    positivity
  have hZMem : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) (zseq n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [zseq]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hZPos n)]
    have hn : 0 <= (n : Real) := by positivity
    apply one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 4)
    nlinarith
  have hZNe : forall n : Nat, Not (zseq n = 0) := by
    intro n
    dsimp [zseq]
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero (by norm_num) (by positivity))
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (1 / 8 : Real) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((1 / 8 : Real) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hReal : Tendsto
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1)))
      atTop (nhds 0) := by
    have hFunctions :
        (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1))) =
          (fun n : Nat => (1 / 8 : Real) *
            ((1 : Real) / ((n : Real) + 1))) := by
      funext n
      field_simp
    rw [hFunctions]
    simpa using hScaled
  have hZ : Tendsto zseq atTop (nhds (0 : Complex)) := by
    have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
    change Tendsto
      (fun n : Nat =>
        (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex))
      atTop (nhds (0 : Complex)) at hCast
    change Tendsto
      (fun n : Nat =>
        (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex))
      atTop (nhds (0 : Complex))
    exact hCast
  have hMeas : forall n : Nat, AEMeasurable
      (fun u : Real => nicolasJMellinShiftIntegrandFilled (zseq n) u)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    exact (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne
      (hZMem n) (hZNe n)).aemeasurable
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto
        (fun n : Nat => nicolasJMellinShiftIntegrandFilled (zseq n) u)
        atTop (nhds (nicolasJMellinShiftIntegrandFilled 0 u)))
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huPos : 0 < u := zero_lt_one.trans hu
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      huPos).continuousAt.tendsto.comp hZ
  exact (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero
  case neg =>
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne
      hz hzZero

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_large
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  apply Integrable.mono' nicolasJLargeMajorant_integrableOn
    (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable hzQuarter)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa [nicolasJLargeMajorant] using
    norm_nicolasJMellinShiftIntegrandFilled_le (mem_Ioi.mp hu) hzQuarter

def nicolasJLargeDerivativeMajorant (u : Real) : Real :=
  16 * nicolasJLargeMajorant u

theorem nicolasJLargeDerivativeMajorant_integrableOn :
    IntegrableOn nicolasJLargeDerivativeMajorant (Ioi (1 : Real)) := by
  unfold nicolasJLargeDerivativeMajorant
  exact nicolasJLargeMajorant_integrableOn.const_mul 16

def nicolasJDerivativeStep (n : Nat) : Complex :=
  (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex)

theorem nicolasJDerivativeStep_ne_zero (n : Nat) :
    Not (nicolasJDerivativeStep n = 0) := by
  unfold nicolasJDerivativeStep
  exact Complex.ofReal_ne_zero.mpr
    (div_ne_zero (by norm_num) (by positivity))

theorem norm_nicolasJDerivativeStep_lt (n : Nat) :
    norm (nicolasJDerivativeStep n) <= (1 / 8 : Real) := by
  unfold nicolasJDerivativeStep
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity :
      0 < (1 : Real) / (8 * ((n : Real) + 1)))]
  apply one_div_le_one_div_of_le (by norm_num : (0 : Real) < 8)
  have hn : 0 <= (n : Real) := by positivity
  nlinarith

theorem nicolasJDerivativeStep_tendsto_zero :
    Tendsto nicolasJDerivativeStep atTop (nhds (0 : Complex)) := by
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (1 / 8 : Real) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((1 / 8 : Real) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hFunctions :
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1))) =
        (fun n : Nat => (1 / 8 : Real) *
          ((1 : Real) / ((n : Real) + 1))) := by
    funext n
    field_simp
  have hReal : Tendsto
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1)))
      atTop (nhds 0) := by
    rw [hFunctions]
    simpa using hScaled
  have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
  change Tendsto nicolasJDerivativeStep atTop (nhds (0 : Complex)) at hCast
  exact hCast

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioi (1 : Real))) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasJDerivativeStep n)
  have hzNorm : norm z < (1 / 8 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hShiftQuarter : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real))
      (z + nicolasJDerivativeStep n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    calc
      norm (z + nicolasJDerivativeStep n) <=
          norm z + norm (nicolasJDerivativeStep n) := norm_add_le _ _
      _ < (1 / 8 : Real) + (1 / 8 : Real) :=
        add_lt_add_of_lt_of_le hzNorm (norm_nicolasJDerivativeStep_lt n)
      _ = (1 / 4 : Real) := by norm_num
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    have hShift :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
        (hShiftQuarter n)
    have hBase :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable hzQuarter
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
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter
        huOne z hzQuarter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hzQuarter)
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
  exact (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

def nicolasJShiftedComplexContinuationFilledLarge (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (1 : Real)))
    (nicolasJMellinShiftIntegrandFilled z)

theorem nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    HasDerivAt nicolasJShiftedComplexContinuationFilledLarge
      (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) z := by
  let s : Set Complex := Metric.ball (0 : Complex) (1 / 8 : Real)
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
    have hwQuarter : Membership.mem
        (Metric.ball (0 : Complex) (1 / 4 : Real)) w := by
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
      hwQuarter
  have hFInt : Integrable (F z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact nicolasJMellinShiftIntegrandFilled_integrableOn_large hz
  have hF'Meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable hz
  have hBound : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        norm (F' w u) <= nicolasJLargeDerivativeMajorant u)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    dsimp [F', s]
    unfold nicolasJLargeDerivativeMajorant
    exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le
      (mem_Ioi.mp hu) hw
  have hDiff : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        HasDerivAt (fun v : Complex => F v u) (F' w u) w)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hwQuarter : Membership.mem
        (Metric.ball (0 : Complex) (1 / 4 : Real)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hAt : DifferentiableAt Complex
        (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter
        (mem_Ioi.mp hu) w hwQuarter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hwQuarter)
    dsimp [F, F']
    exact hAt.hasDerivAt
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := nicolasJLargeDerivativeMajorant)
    hsNhd hFMeas hFInt hF'Meas hBound
    nicolasJLargeDerivativeMajorant_integrableOn hDiff
  unfold nicolasJShiftedComplexContinuationFilledLarge
  simpa [F, F'] using hMain.2

theorem nicolasJShiftedComplexContinuationFilledLarge_differentiableOn :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilledLarge
      (Metric.ball (0 : Complex) (1 / 8 : Real)) := by
  intro z hz
  exact (nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt
    hz).differentiableAt.differentiableWithinAt


theorem exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one :
    Exists fun r : Real => And (0 < r)
      (forall s : Complex, Membership.mem
        (Metric.ball (1 : Complex) r) s ->
          AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s) := by
  have hEventually :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_one.eventually_analyticAt
  choose r hrPos hrSubset using Metric.mem_nhds_iff.1 hEventually
  refine Exists.intro r (And.intro hrPos ?_)
  intro s hs
  exact hrSubset hs

theorem nicolasJMellinShiftIntegrandFilled_eq_raw
    {z : Complex} (hzRe : z.re < 0) {u : Real} (hu : 0 < u) :
    nicolasJMellinShiftIntegrandFilled z u =
      nicolasJMellinShiftIntegrand z u := by
  have hzZero : Not (z = 0) := by
    intro hZero
    rw [hZero] at hzRe
    norm_num at hzRe
  have hBaseRe : 1 < (((u + 1 : Real) : Complex)).re := by
    simp
    linarith
  have hShiftRe : 1 <
      ((((u + 1 : Real) : Complex) - z)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hBaseEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hBaseRe
  have hShiftEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hShiftRe
  unfold nicolasJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzZero]
  unfold slope
  rw [nicolasJShiftNumeratorFilled_zero]
  unfold nicolasJShiftNumeratorFilled nicolasJMellinShiftIntegrand
  rw [hBaseEq, hShiftEq]
  simp only [sub_zero, smul_eq_mul, vsub_eq_sub]
  field_simp [hzZero]

def nicolasJShiftedComplexContinuationFilled (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (0 : Real)))
    (nicolasJMellinShiftIntegrandFilled z)

def nicolasJShiftedRealContinuationFilled (a : Real) : Real :=
  Complex.re (nicolasJShiftedComplexContinuationFilled (a : Complex))

theorem nicolasJShiftedRealContinuationFilled_eq_raw
    {a : Real} (ha : a < 0) :
    nicolasJShiftedRealContinuationFilled a =
      nicolasJShiftedRealContinuation a := by
  unfold nicolasJShiftedRealContinuationFilled
    nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedRealContinuation
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  exact nicolasJMellinShiftIntegrandFilled_eq_raw
    (by simpa using ha) hu

theorem nicolasLandauRpowTailMellin_eq_continuation
    {X b a : Real} (hX : 0 < X) (ha : a < b) :
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        x ^ (a - 1) * x ^ (-b)) =
      nicolasLandauRpowMellinContinuation X b a := by
  calc
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        x ^ (a - 1) * x ^ (-b)) =
        integral (volume.restrict (Ioi X)) (fun x : Real =>
          x ^ (a - b - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxPos : 0 < x := hX.trans hx
      change x ^ (a - 1) * x ^ (-b) = x ^ (a - b - 1)
      rw [<- Real.rpow_add hxPos]
      congr 1
      ring
    _ = -X ^ (a - b - 1 + 1) / (a - b - 1 + 1) := by
      exact integral_Ioi_rpow_of_lt (by linarith) hX
    _ = nicolasLandauRpowMellinContinuation X b a := by
      unfold nicolasLandauRpowMellinContinuation
      have hab : Not (a - b = 0) := sub_ne_zero.mpr (ne_of_lt ha)
      have hba : Not (b - a = 0) := sub_ne_zero.mpr (Ne.symm (ne_of_lt ha))
      rw [show a - b - 1 + 1 = a - b by ring]
      field_simp [hab, hba]
      ring

theorem nicolasLandauRpowMellinContinuation_analyticAt
    {X b sigma : Real} (hX : 0 < X) (hSigma : sigma < b) :
    AnalyticAt Real (nicolasLandauRpowMellinContinuation X b) sigma := by
  have hFunction : nicolasLandauRpowMellinContinuation X b =
      fun a : Real => Real.exp (Real.log X * (a - b)) / (b - a) := by
    funext a
    unfold nicolasLandauRpowMellinContinuation
    rw [Real.rpow_def_of_pos hX]
  rw [hFunction]
  have hNumerator : AnalyticAt Real
      (fun a : Real => Real.exp (Real.log X * (a - b))) sigma := by
    fun_prop
  have hDenominator : AnalyticAt Real (fun a : Real => b - a) sigma := by
    fun_prop
  exact hNumerator.div hDenominator (sub_ne_zero.mpr (ne_of_gt hSigma))

theorem nicolasJKernel_integrableOn_Ioi_three :
    IntegrableOn
      (fun t : Real => nicolasPsiError t * nicolasTailKernel t)
      (Ioi (3 : Real)) := by
  have hDouble := nicolasFrullaniDouble_integrable
    (x := (3 : Real)) (by norm_num)
  have hSlice := hDouble.integral_prod_left
  apply hSlice.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htOne : 1 < t := lt_trans (by norm_num) ht
  change
    integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
      nicolasPsiError t * (u + 1) * t ^ (-(u + 2))) =
        nicolasPsiError t * nicolasTailKernel t
  rw [nicolasTailKernel_eq_frullani htOne, <- integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  ring

theorem nicolasJ_realMellin_integrableOn_Ioi_three
    {a : Real} (ha : a < 0) :
    IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasJ x) (Ioi (3 : Real)) := by
  have hTriple := nicolasJMellinTriple_integrable
    (z := (a : Complex)) (by simpa using ha)
  have hOuter := hTriple.integral_prod_left
  have hComplex : Integrable
      (fun x : Real =>
        (x : Complex) ^ ((a : Complex) - 1) * (nicolasJ x : Complex))
      (volume.restrict (Ioi (3 : Real))) := by
    apply hOuter.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact nicolasJMellinTriple_inner_eq hx.le
  have hRealPart := Complex.reCLM.integrable_comp hComplex
  apply hRealPart.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  have hPower : (x : Complex) ^ ((a : Complex) - 1) =
      ((x ^ (a - 1) : Real) : Complex) := by
    rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
      push_cast
      rfl]
    rw [<- Complex.ofReal_cpow hxPos.le]
  rw [hPower]
  simp

theorem nicolasJ_realMellin_eq_shiftedRealContinuation
    {a : Real} (ha : a < 0) :
    integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        x ^ (a - 1) * nicolasJ x) =
      nicolasJShiftedRealContinuation a := by
  have hCast :
      ((integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        x ^ (a - 1) * nicolasJ x) : Real) : Complex) =
        nicolasJMellin (a : Complex) := by
    unfold nicolasJMellin
    calc
      ((integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          x ^ (a - 1) * nicolasJ x) : Real) : Complex) =
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            ((x ^ (a - 1) * nicolasJ x : Real) : Complex)) :=
        integral_ofReal.symm
      _ = integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          (x : Complex) ^ ((a : Complex) - 1) *
            (nicolasJ x : Complex)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxPos : 0 < x := lt_trans (by norm_num) hx
        have hPower : (x : Complex) ^ ((a : Complex) - 1) =
            ((x ^ (a - 1) : Real) : Complex) := by
          rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
            push_cast
            rfl]
          rw [<- Complex.ofReal_cpow hxPos.le]
        rw [hPower]
        push_cast
        rfl
  have hShift := nicolasJMellin_eq_integral_shift
    (z := (a : Complex)) (by simpa using ha)
  unfold nicolasJShiftedRealContinuation
  have hValue :
      ((integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        x ^ (a - 1) * nicolasJ x) : Real) : Complex) =
        integral (volume.restrict (Ioi (0 : Real)))
          (nicolasJMellinShiftIntegrand (a : Complex)) := by
    rw [hCast, hShift]
    rfl
  exact Complex.ofReal_injective (by
    simpa using congrArg Complex.re hValue)

theorem nicolasLandauPositiveMellin_eq_continuation_of_neg
    {X b a : Real} (hX : 3 <= X) (hb : 0 < b) (ha : a < 0) :
    nicolasLandauPositiveMellin X b a =
      nicolasLandauPositiveMellinContinuation X b a := by
  have hJThree := nicolasJ_realMellin_integrableOn_Ioi_three ha
  have hJX : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasJ x) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hJStartup : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasJ x) (Ioc 3 X) :=
    hJThree.mono_set Ioc_subset_Ioi_self
  have hJSplit :
      integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          x ^ (a - 1) * nicolasJ x) =
        nicolasJRealMellinStartup X a +
          integral (volume.restrict (Ioi X)) (fun x : Real =>
            x ^ (a - 1) * nicolasJ x) := by
    unfold nicolasJRealMellinStartup
    rw [<- Ioc_union_Ioi_eq_Ioi hX,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
    . exact hJStartup
    . exact hJX
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have haB : a < b := lt_trans ha hb
  have hRpowBase : IntegrableOn (fun x : Real =>
      x ^ (a - b - 1)) (Ioi X) := by
    rw [integrableOn_Ioi_rpow_iff hXPos]
    linarith
  have hRpow : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * x ^ (-b)) (Ioi X) := by
    apply hRpowBase.congr_fun
    . intro x hx
      have hxPos : 0 < x := hXPos.trans hx
      change x ^ (a - b - 1) = x ^ (a - 1) * x ^ (-b)
      rw [<- Real.rpow_add hxPos]
      congr 1
      ring
    . exact measurableSet_Ioi
  unfold nicolasLandauPositiveMellin nicolasLandauPositiveTail
    nicolasLandauPositiveMellinContinuation
  have hDecomp :
      (fun x : Real => x ^ (a - 1) * (nicolasJ x + x ^ (-b))) =
        (fun x : Real => x ^ (a - 1) * nicolasJ x) +
          (fun x : Real => x ^ (a - 1) * x ^ (-b)) := by
    funext x
    dsimp
    ring
  rw [hDecomp]
  change integral (volume.restrict (Ioi X)) (fun x : Real =>
      x ^ (a - 1) * nicolasJ x + x ^ (a - 1) * x ^ (-b)) =
    nicolasJShiftedRealContinuation a - nicolasJRealMellinStartup X a +
      nicolasLandauRpowMellinContinuation X b a
  rw [integral_add hJX hRpow]
  rw [nicolasLandauRpowTailMellin_eq_continuation hXPos haB]
  rw [nicolasJ_realMellin_eq_shiftedRealContinuation ha] at hJSplit
  linarith

theorem nicolasLandauPositiveTail_integrableOn_of_neg
    {X b a : Real} (hX : 3 <= X) (hb : 0 < b) (ha : a < 0) :
    IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasLandauPositiveTail b x) (Ioi X) := by
  have hJ : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasJ x) (Ioi X) :=
    nicolasJ_realMellin_integrableOn_Ioi_three ha |>.mono_set
      (Ioi_subset_Ioi hX)
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hPowerBase : IntegrableOn (fun x : Real =>
      x ^ (a - b - 1)) (Ioi X) := by
    rw [integrableOn_Ioi_rpow_iff hXPos]
    linarith
  have hRpow : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * x ^ (-b)) (Ioi X) := by
    apply hPowerBase.congr_fun
    . intro x hx
      have hxPos : 0 < x := hXPos.trans hx
      change x ^ (a - b - 1) = x ^ (a - 1) * x ^ (-b)
      rw [<- Real.rpow_add hxPos]
      congr 1
      ring
    . exact measurableSet_Ioi
  apply (hJ.add hRpow).congr_fun
  . intro x hx
    unfold nicolasLandauPositiveTail
    change x ^ (a - 1) * nicolasJ x + x ^ (a - 1) * x ^ (-b) =
      x ^ (a - 1) * (nicolasJ x + x ^ (-b))
    ring
  . exact measurableSet_Ioi

theorem nicolasJ_aemeasurable_restrict_Ioi
    {X : Real} (hX : 3 <= X) :
    AEMeasurable nicolasJ (volume.restrict (Ioi X)) := by
  let q : Real -> Real := fun t : Real =>
    nicolasPsiError t * nicolasTailKernel t
  have hq : IntegrableOn q (Ioi (3 : Real)) := by
    simpa [q] using nicolasJKernel_integrableOn_Ioi_three
  let q0 : Real -> Real := (Ioi (3 : Real)).indicator q
  have hq0 : Integrable q0 volume := by
    dsimp [q0]
    exact hq.integrable_indicator measurableSet_Ioi
  let tailPrimitive : Real -> Real := fun x : Real =>
    integral (volume.restrict (Ioi (3 : Real))) q -
      intervalIntegral q0 3 x volume
  have hContinuous : Continuous tailPrimitive := by
    dsimp [tailPrimitive]
    exact continuous_const.sub (hq0.continuous_primitive 3)
  have hEq : Filter.Eventually
      (fun x : Real => nicolasJ x = tailPrimitive x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxThree : 3 <= x := hX.trans hx.le
    have hqx : IntegrableOn q (Ioi x) :=
      hq.mono_set (Ioi_subset_Ioi hxThree)
    have hSplit := intervalIntegral.integral_interval_add_Ioi hq hqx
    have hInterval : intervalIntegral q0 3 x volume =
        intervalIntegral q 3 x volume := by
      apply intervalIntegral.integral_congr_Ioo_of_le hxThree
      intro t ht
      simpa [q, ht.1]
    unfold nicolasJ
    dsimp [tailPrimitive, q]
    rw [hInterval]
    linarith
  have hEqSymm : Filter.Eventually
      (fun x : Real => tailPrimitive x = nicolasJ x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [hEq] with x hx
    exact hx.symm
  exact hContinuous.aemeasurable.congr hEqSymm

theorem nicolasLandauPositiveDensity_aemeasurable
    {X b : Real} (hX : 3 <= X) :
    AEMeasurable (nicolasLandauPositiveDensity b)
      (volume.restrict (Ioi X)) := by
  have hJ := nicolasJ_aemeasurable_restrict_Ioi hX
  have hInv : AEMeasurable (fun x : Real => x ^ (-1 : Real))
      (volume.restrict (Ioi X)) :=
    measurable_id.aemeasurable.pow aemeasurable_const
  have hPower : AEMeasurable (fun x : Real => x ^ (-b))
      (volume.restrict (Ioi X)) :=
    measurable_id.aemeasurable.pow aemeasurable_const
  exact (hInv.mul (hJ.add hPower)).ennreal_ofReal

theorem ae_log_nonneg_nicolasLandauPositiveMeasure
    {X b : Real} (hX : 3 <= X) :
    Filter.Eventually (fun x : Real => 0 <= Real.log x)
      (ae (nicolasLandauPositiveMeasure X b)) := by
  have hBase : Filter.Eventually (fun x : Real => 0 <= Real.log x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.log_nonneg (le_trans (by norm_num) (hX.trans hx.le))
  exact (withDensity_absolutelyContinuous
    (volume.restrict (Ioi X)) (nicolasLandauPositiveDensity b)).ae_le hBase

theorem mgf_log_nicolasLandauPositiveMeasure_eq_mellin
    {X b a : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x) :
    mgf (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b) a =
      nicolasLandauPositiveMellin X b a := by
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
  unfold mgf nicolasLandauPositiveMeasure
  rw [hMeasureEq, integral_withDensity_eq_integral_toReal_smul
    hDensity.measurable_mk hDensityTop]
  unfold nicolasLandauPositiveMellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hTail : 0 <= nicolasLandauPositiveTail b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      nicolasLandauPositiveTail b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  change (measurableDensity x).toReal * Real.exp (a * Real.log x) =
    x ^ (a - 1) * nicolasLandauPositiveTail b x
  rw [<- hdx]
  unfold nicolasLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  rw [Real.rpow_def_of_pos hxPos, Real.rpow_def_of_pos hxPos]
  calc
    Real.exp (Real.log x * -1) * nicolasLandauPositiveTail b x *
        Real.exp (a * Real.log x) =
        (Real.exp (Real.log x * -1) *
          Real.exp (a * Real.log x)) *
            nicolasLandauPositiveTail b x := by ring
    _ = Real.exp (Real.log x * -1 + a * Real.log x) *
        nicolasLandauPositiveTail b x := by rw [Real.exp_add]
    _ = Real.exp (Real.log x * (a - 1)) *
        nicolasLandauPositiveTail b x := by
      congr 2
      ring

theorem mem_integrableExpSet_log_nicolasLandau_iff
    {X b a : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x) :
    Membership.mem
        (integrableExpSet (fun x : Real => Real.log x)
          (nicolasLandauPositiveMeasure X b)) a <->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * nicolasLandauPositiveTail b x) (Ioi X) := by
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
  change Integrable (fun x : Real => Real.exp (a * Real.log x))
      (nicolasLandauPositiveMeasure X b) <->
    Integrable (fun x : Real =>
      x ^ (a - 1) * nicolasLandauPositiveTail b x)
      (volume.restrict (Ioi X))
  unfold nicolasLandauPositiveMeasure
  rw [hMeasureEq, integrable_withDensity_iff
    hDensity.measurable_mk hDensityTop]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hTail : 0 <= nicolasLandauPositiveTail b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      nicolasLandauPositiveTail b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  change Real.exp (a * Real.log x) * (measurableDensity x).toReal =
    x ^ (a - 1) * nicolasLandauPositiveTail b x
  rw [<- hdx]
  unfold nicolasLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  rw [Real.rpow_def_of_pos hxPos, Real.rpow_def_of_pos hxPos]
  calc
    Real.exp (a * Real.log x) *
        (Real.exp (Real.log x * -1) *
          nicolasLandauPositiveTail b x) =
        (Real.exp (a * Real.log x) *
          Real.exp (Real.log x * -1)) *
            nicolasLandauPositiveTail b x := by ring
    _ = Real.exp (a * Real.log x + Real.log x * -1) *
        nicolasLandauPositiveTail b x := by rw [Real.exp_add]
    _ = Real.exp (Real.log x * (a - 1)) *
        nicolasLandauPositiveTail b x := by
      congr 2
      ring

theorem interior_integrableExpSet_log_nicolasLandau_of_below
    {X b sigma : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    (hBelow : forall a : Real, a < sigma ->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * nicolasLandauPositiveTail b x) (Ioi X)) :
    forall a : Real, a < sigma ->
      Membership.mem
        (interior (integrableExpSet (fun x : Real => Real.log x)
          (nicolasLandauPositiveMeasure X b))) a := by
  intro a ha
  rw [mem_interior_iff_mem_nhds]
  let eps : Real := (sigma - a) / 2
  have hEps : 0 < eps := by
    dsimp [eps]
    linarith
  apply mem_of_superset (Metric.ball_mem_nhds a hEps)
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hySigma : y < sigma := by
    have hAbs := (abs_lt.mp hy).2
    dsimp [eps] at hAbs
    linarith
  exact (mem_integrableExpSet_log_nicolasLandau_iff hX hPos).2
    (hBelow y hySigma)


end

end Robin1984
