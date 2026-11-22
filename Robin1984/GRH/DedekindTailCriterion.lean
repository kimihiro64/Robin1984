import Robin1984.GRH.DedekindTailConverse
import Robin1984.GRH.PositiveMellinMeasure
import Robin1984.GRH.TailMellin

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The integrated prime-ideal error in a Dedekind Robin-type converse.
- Formalization note: A global nonnegative comparison is obtained by increasing the eventual bound's constant on a bounded interval, and its transform is obtained by Fubini.
- PROVENANCE-END
-/

/-!
# Excluding zeros using an upper bound for the integrated error

For the arithmetic application the real density is the prime-ideal
Chebyshev error divided by the square of the integration variable.
The hypotheses state its absolute integrability and its logarithmic
derivative on the initial half-plane.
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace Robin1984.GRH

/-- The integral of a real error density to the right of the argument. -/
noncomputable def integratedTail (g : Real -> Real) (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) g

private theorem measurable_integratedTail {g : Real -> Real} (hg : Measurable g) :
    Measurable (integratedTail g) := by
  let D : Set (Prod Real Real) := {p | p.1 < p.2}
  have hD : MeasurableSet D := (isOpen_lt continuous_fst continuous_snd).measurableSet
  let K : Prod Real Real -> Real := D.indicator (fun p => g p.2)
  have hK : Measurable K := (hg.comp measurable_snd).indicator hD
  have hCurriedStrong : StronglyMeasurable (fun x : Real =>
      integral volume (fun t : Real => K (x, t))) := hK.stronglyMeasurable.integral_prod_right'
  have hCurriedEq : (fun x : Real => integral volume (fun t : Real => K (x, t))) = integratedTail g := by
    funext x
    have hFun : (fun t => K (x, t)) = (Ioi x).indicator g := by
      funext t
      by_cases ht : x < t
      case pos =>
        change D.indicator _ (x, t) = (Ioi x).indicator _ t
        rw [indicator_of_mem (show Membership.mem D (x, t) from ht),
          indicator_of_mem (show Membership.mem (Ioi x) t from ht)]
      case neg =>
        change D.indicator _ (x, t) = (Ioi x).indicator _ t
        rw [indicator_of_notMem (show Not (Membership.mem D (x, t)) from ht),
          indicator_of_notMem (show Not (Membership.mem (Ioi x) t) from ht)]
    rw [hFun, integral_indicator measurableSet_Ioi, integratedTail]
  rw [<- hCurriedEq]
  exact hCurriedStrong.measurable

private theorem norm_integratedTail_le {g : Real -> Real}
    (hg : IntegrableOn g (Ioi (1 : Real))) {x : Real} (hx : 1 < x) :
    norm (integratedTail g x) <= integral (volume.restrict (Ioi (1 : Real))) (fun t => norm (g t)) := by
  have hSub : Set.Subset (Ioi x) (Ioi (1 : Real)) := fun _ ht => hx.trans ht
  exact (norm_integral_le_integral_norm g).trans
    (setIntegral_mono_set hg.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (Filter.Eventually.of_forall (fun _ h => hSub h)))

private theorem tailComparison_mellin {g : Real -> Real} (hMeas : Measurable g)
    (hg : IntegrableOn g (Ioi (1 : Real))) (C : Real) (s : Complex) (hs : 1 < s.re) :
    let mu := volume.restrict (Ioi (1 : Real))
    let F := fun x : Real => C * Real.sqrt x + x * integratedTail g x
    let K := fun x : Real => (F x : Complex) * (x : Complex) ^ (-s - 1)
    And (Integrable K mu)
      (integral mu K = (C : Complex) / (s - 1 / 2) +
        (integral mu (fun x : Real => (x : Complex) ^ (1 - s) * (g x : Complex)) -
          integral mu (fun x : Real => (g x : Complex))) / (1 - s)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let F := fun x : Real => C * Real.sqrt x + x * integratedTail g x
  let P := fun x : Real => (C : Complex) * (x : Complex) ^ (((1 / 2 : Real) : Complex) - s - 1)
  let T := fun x : Real => (x : Complex) ^ (-s) * (integratedTail g x : Complex)
  let K := fun x : Real => (F x : Complex) * (x : Complex) ^ (-s - 1)
  let M := integral mu (fun t => norm (g t))
  have hPExp : (((1 / 2 : Real) : Complex) - s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith only [hs]
  have hPInt : Integrable P mu :=
    (integrableOn_Ioi_cpow_of_lt hPExp zero_lt_one).const_mul _
  have hPVal : integral mu P = (C : Complex) / (s - 1 / 2) := by
    unfold P
    rw [integral_const_mul, integral_Ioi_cpow_of_lt hPExp zero_lt_one]
    have hHalf : ((1 / 2 : Real) : Complex) = (1 / 2 : Complex) := by norm_num
    have hExp : ((1 / 2 : Real) : Complex) - s - 1 + 1 = -(s - 1 / 2) := by
      rw [hHalf]
      ring
    rw [hExp, Complex.ofReal_one, Complex.one_cpow, neg_div_neg_eq, mul_one_div]
  have hTExp : (-s).re < -1 := by rw [Complex.neg_re]; linarith only [hs]
  have hTWeight : IntegrableOn (fun x : Real => (x : Complex) ^ (-s)) (Ioi (1 : Real)) :=
    integrableOn_Ioi_cpow_of_lt hTExp zero_lt_one
  have hTInt : Integrable T mu := by
    refine Integrable.mono' (hTWeight.norm.const_mul M)
      (hTWeight.aestronglyMeasurable.mul
        ((Complex.continuous_ofReal.measurable.comp
          (measurable_integratedTail hMeas)).aestronglyMeasurable)) ?_
    have hTail : Filter.Eventually (fun x : Real => 1 < x) (ae mu) :=
      ae_restrict_mem measurableSet_Ioi
    filter_upwards [hTail] with x hx
    change norm ((x : Complex) ^ (-s) * (integratedTail g x : Complex)) <=
      M * norm ((x : Complex) ^ (-s))
    rw [norm_mul, Complex.norm_real, mul_comm M]
    exact mul_le_mul_of_nonneg_left (norm_integratedTail_le hg hx) (norm_nonneg _)
  have hTVal : integral mu T =
      (integral mu (fun x : Real => (x : Complex) ^ (1 - s) * (g x : Complex)) -
        integral mu (fun x : Real => (g x : Complex))) / (1 - s) := by
    have hCast : T = fun x : Real => (x : Complex) ^ (-s) *
        integral (volume.restrict (Ioi x)) (fun t : Real => (g t : Complex)) := by
      funext x
      unfold T
      rw [integral_complex_ofReal, integratedTail]
    rw [hCast]
    have hgCast : IntegrableOn (fun t : Real => (g t : Complex)) (Ioi (1 : Real)) :=
      Integrable.ofReal hg
    exact integral_tail_cpow_dividedDifference hgCast s hs
  have hK : Filter.EventuallyEq (ae mu) K (P + T) := by
    have hTail : Filter.Eventually (fun x : Real => 1 < x) (ae mu) :=
      ae_restrict_mem measurableSet_Ioi
    filter_upwards [hTail] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hNe := Complex.ofReal_ne_zero.mpr hx0.ne'
    have hSqrt : (Real.sqrt x : Complex) = (x : Complex) ^ ((1 / 2 : Real) : Complex) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx0.le]
    have hP : (x : Complex) ^ (((1 / 2 : Real) : Complex) - s - 1) =
        (x : Complex) ^ ((1 / 2 : Real) : Complex) * (x : Complex) ^ (-s - 1) := by
      rw [<- Complex.cpow_add _ _ hNe]
      congr 1
      ring
    have hT : (x : Complex) ^ (-s) =
        (x : Complex) * (x : Complex) ^ (-s - 1) := by
      calc
        _ = (x : Complex) ^ (1 + (-s - 1)) := by
          congr 1
          ring
        _ = _ := by rw [Complex.cpow_add _ _ hNe, Complex.cpow_one]
    simp only [K, F, Pi.add_apply, P, T, Complex.ofReal_add, Complex.ofReal_mul, hSqrt,
      add_mul, hP, hT]
    ring
  refine And.intro ((hPInt.add hTInt).congr hK.symm) ?_
  rw [integral_congr_ae hK]
  change integral mu (fun x => P x + T x) = _
  rw [integral_add hPInt hTInt, hPVal, hTVal]

private theorem logDeriv_one_add_integral_eq_zero {g : Real -> Real} {f : Complex -> Complex}
    (hg : IntegrableOn g (Ioi (1 : Real))) (hf : AnalyticAt Complex f 1)
    (hf1 : Not (f 1 = 0))
    (hSeries : forall s : Complex, 1 < s.re ->
      integral (volume.restrict (Ioi (1 : Real)))
        (fun x : Real => (x : Complex) ^ (1 - s) * (g x : Complex)) = -(logDeriv f s + 1) / s) :
    logDeriv f 1 + 1 +
      integral (volume.restrict (Ioi (1 : Real))) (fun x : Real => (g x : Complex)) = 0 := by
  let mu := volume.restrict (Ioi (1 : Real))
  let l := nhdsWithin (1 : Real) (Ioi 1)
  let G := fun s x : Real => (x : Complex) ^ (1 - (s : Complex)) * (g x : Complex)
  have hFilter : l <= nhds (1 : Real) := nhdsWithin_le_nhds
  have hgCast : Integrable (fun x : Real => (g x : Complex)) mu := Integrable.ofReal hg
  have hRight : Filter.Eventually (fun s : Real => 1 < s) l := self_mem_nhdsWithin
  have hTail : Filter.Eventually (fun x : Real => 1 < x) (ae mu) :=
    ae_restrict_mem measurableSet_Ioi
  have hMeas (s : Real) : AEStronglyMeasurable (G s) mu := by
    have hWeight : AEStronglyMeasurable (fun x : Real => (x : Complex) ^ (1 - (s : Complex))) mu := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')).continuousWithinAt
    exact hWeight.mul hgCast.aestronglyMeasurable
  have hBounds : Filter.Eventually (fun s : Real =>
      Filter.Eventually (fun x => norm (G s x) <= norm (g x)) (ae mu)) l := by
    refine hRight.mono (fun s hs => hTail.mono (fun x hx => ?_))
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hExp : (1 - (s : Complex)).re <= 0 := by
      rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      exact sub_nonpos.mpr hs.le
    change norm ((x : Complex) ^ (1 - (s : Complex)) * (g x : Complex)) <= norm (g x)
    rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    apply mul_le_of_le_one_left (norm_nonneg _)
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hx.le hExp
  have hLimit : Filter.Eventually (fun x : Real =>
      Tendsto (fun s : Real => G s x) l (nhds (g x : Complex))) (ae mu) := by
    refine hTail.mono (fun x hx => ?_)
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hFun : (fun s : Real => G s x) =
        fun s : Real => Complex.exp (Complex.log (x : Complex) * (1 - (s : Complex))) *
          (g x : Complex) := by
      funext s
      change (x : Complex) ^ (1 - (s : Complex)) * _ = _
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx0.ne')]
    rw [hFun]
    have hCont : Continuous (fun s : Real =>
        Complex.exp (Complex.log (x : Complex) * (1 - (s : Complex))) * (g x : Complex)) :=
      (Complex.continuous_exp.comp
        (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal))).mul continuous_const
    simpa only [Complex.ofReal_one, sub_self, mul_zero, Complex.exp_zero, one_mul] using
      (hCont.continuousAt (x := (1 : Real))).tendsto.mono_left hFilter
  have hIntegral : Tendsto (fun s : Real => integral mu (G s)) l
      (nhds (integral mu (fun x : Real => (g x : Complex)))) :=
    tendsto_integral_filter_of_dominated_convergence (fun x => norm (g x))
      (Filter.Eventually.of_forall hMeas) hBounds hg.norm hLimit
  have hLog : AnalyticAt Complex (logDeriv f) 1 := hf.deriv.div hf hf1
  have hFormula : ContinuousAt (fun s : Complex => -(logDeriv f s + 1) / s) 1 :=
    ((hLog.continuousAt.add continuousAt_const).neg).div continuousAt_id one_ne_zero
  have hComplexCast : ContinuousAt (fun s : Real => (s : Complex)) 1 :=
    Complex.continuous_ofReal.continuousAt
  have hFormulaReal : ContinuousAt (fun s : Real => -(logDeriv f (s : Complex) + 1) / (s : Complex)) 1 := by
    have hFormulaCast : ContinuousAt (fun s : Complex => -(logDeriv f s + 1) / s)
        ((1 : Real) : Complex) := by simpa only [Complex.ofReal_one] using hFormula
    exact hFormulaCast.comp hComplexCast
  have hFormulaLimit : Tendsto (fun s : Real => -(logDeriv f (s : Complex) + 1) / (s : Complex)) l
      (nhds (-(logDeriv f 1 + 1))) := by
    simpa only [Complex.ofReal_one, div_one] using hFormulaReal.tendsto.mono_left hFilter
  have hAgreement : Filter.EventuallyEq l (fun s : Real => integral mu (G s))
      (fun s : Real => -(logDeriv f (s : Complex) + 1) / (s : Complex)) :=
    hRight.mono (fun s hs => hSeries s (by simpa only [Complex.ofReal_re] using hs))
  have hMass := tendsto_nhds_unique hIntegral (hFormulaLimit.congr' hAgreement.symm)
  change logDeriv f 1 + 1 + integral mu (fun x : Real => (g x : Complex)) = 0
  rw [hMass, add_neg_cancel]

/-- An eventual upper bound for minus the integrated error excludes
right-half-plane zeros, given the absolute-integrability and
logarithmic-derivative data of the number-field application. -/
theorem ne_zero_of_eventual_integratedTailBound {g : Real -> Real} {f : Complex -> Complex}
    (hMeas : Measurable g) (hg : IntegrableOn g (Ioi (1 : Real)))
    (hf : AnalyticOnNhd Complex f {z : Complex | (1 / 2 : Real) < z.re})
    (hNoRealHigh : forall b : Real, 1 <= b -> Not (f (b : Complex) = 0))
    (hSeries : forall s : Complex, 1 < s.re ->
      integral (volume.restrict (Ioi (1 : Real)))
        (fun x : Real => (x : Complex) ^ (1 - s) * (g x : Complex)) = -(logDeriv f s + 1) / s)
    (hBound : exists C t : Real, forall x : Real, t < x ->
      -x * integratedTail g x <= C * Real.sqrt x)
    {z : Complex} (hz : (1 / 2 : Real) < z.re) :
    Not (f z = 0) := by
  choose c t hct using hBound
  let mu := volume.restrict (Ioi (1 : Real))
  let M := integral mu (fun x => norm (g x))
  let C := max c (max 1 t * M)
  let F := fun x : Real => C * Real.sqrt x + x * integratedTail g x
  let Fone : Complex := integral mu (fun x : Real => (g x : Complex))
  let nu := positiveMellinMeasure F 1 0
  have hM : 0 <= M := integral_nonneg (fun _ => norm_nonneg _)
  have hF (x : Real) (hx : 1 < x) : 0 <= F x := by
    have hSqrt : 1 <= Real.sqrt x := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx.le
    have hC : -x * integratedTail g x <= C * Real.sqrt x := by
      by_cases ht : t < x
      case pos =>
        exact (hct x ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.sqrt_nonneg _))
      case neg =>
        have hTail : -integratedTail g x <= M := by
          have hNorm := norm_integratedTail_le hg hx
          rw [Real.norm_eq_abs] at hNorm
          exact (neg_le_abs _).trans hNorm
        have hTop : x <= max 1 t := (le_of_not_gt ht).trans (le_max_right _ _)
        calc
          _ = x * (-integratedTail g x) := by ring
          _ <= x * M := mul_le_mul_of_nonneg_left hTail (zero_lt_one.trans hx).le
          _ <= max 1 t * M := mul_le_mul_of_nonneg_right hTop hM
          _ <= C * Real.sqrt x :=
            (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hM) hSqrt).trans
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
    change 0 <= C * Real.sqrt x + x * integratedTail g x
    linarith only [hC]
  have hFMeas : Measurable F :=
    (measurable_const.mul Real.continuous_sqrt.measurable).add
      (measurable_id.mul (measurable_integratedTail hMeas))
  have hSupport := ae_nonneg_log_positiveMellinMeasure F (le_refl (1 : Real)) 0
  have hMoment (t : Real) (ht : t < -1) : Membership.mem (integrableExpSet Real.log nu) t := by
    apply (mem_integrableExpSet_positiveMellinMeasure_iff hFMeas (le_refl (1 : Real)) hF 0 t).mpr
    have htRe : 1 < (-(t : Complex)).re := by
      rw [Complex.neg_re, Complex.ofReal_re]
      exact lt_neg_of_lt_neg ht
    have hI : IntegrableOn (fun x : Real =>
        ((F x : Complex) * (x : Complex) ^ (-(-(t : Complex)) - 1)).re) (Ioi (1 : Real)) :=
      (tailComparison_mellin hMeas hg C (-(t : Complex)) htRe).1.re
    refine hI.congr_fun (fun x hx => ?_) measurableSet_Ioi
    change ((F x : Complex) * (x : Complex) ^ (-(-(t : Complex)) - 1)).re =
      F x * x ^ (t - 0 - 1)
    have hExp : -(-(t : Complex)) - 1 = ((t - 0 - 1 : Real) : Complex) := by
      simp only [neg_neg, sub_zero, Complex.ofReal_sub, Complex.ofReal_one]
    rw [hExp, <- Complex.ofReal_cpow (zero_le_one.trans hx.le),
      <- Complex.ofReal_mul, Complex.ofReal_re]
  have hBaseExp : Membership.mem (interior (integrableExpSet Real.log nu)) (-(2 : Complex)).re :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
      (Iio_mem_nhds (by norm_num : (-(2 : Complex)).re < -1)) hMoment)
  have hOne : AnalyticAt Complex f 1 := hf _ (by norm_num)
  have hOneNonzero : Not (f 1 = 0) := by
    simpa only [Complex.ofReal_one] using hNoRealHigh 1 (le_refl (1 : Real))
  have hAtOne := logDeriv_one_add_integral_eq_zero hg hOne hOneNonzero hSeries
  refine ne_zero_of_dedekindTailComparison (C := (C : Complex)) (Fone := Fone)
    Real.measurable_log hSupport hf hNoRealHigh hAtOne hBaseExp ?_ hz
  have hTwo : Membership.mem {z : Complex | (1 / 2 : Real) < z.re} (2 : Complex) := by norm_num
  have hTwoNonzero : Not (f (2 : Complex) = 0) := by
    simpa only [Complex.ofReal_ofNat] using hNoRealHigh 2 (by norm_num)
  have hNear : Filter.Eventually (fun s : Complex => 1 < s.re) (nhds (2 : Complex)) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hNearNonzero : Filter.Eventually (fun s => Not (f s = 0)) (nhds (2 : Complex)) :=
    (hf _ hTwo).continuousAt.tendsto.eventually (isOpen_ne.mem_nhds hTwoNonzero)
  filter_upwards [hNear, hNearNonzero] with s hs hsNonzero
  have hMellin : complexMGF Real.log nu (-s) =
      (C : Complex) / (s - 1 / 2) + (-(logDeriv f s + 1) / s - Fone) / (1 - s) := by
    change complexMGF Real.log (positiveMellinMeasure F 1 0) (-s) = _
    rw [complexMGF_log_positiveMellinMeasure hFMeas (le_refl (1 : Real)) hF]
    simpa only [Complex.ofReal_zero, sub_zero, hSeries s hs] using
      (tailComparison_mellin hMeas hg C s hs).2
  have hs0 : Not (s = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs1 : Not (s - 1 = 0) := Complex.ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]
    exact sub_pos.mpr hs)
  have hOneS : Not (1 - s = 0) := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hs1))
  have hsHalf : Not (s - 1 / 2 = 0) := Complex.ne_zero_of_re_pos (by
    norm_num [Complex.sub_re]
    linarith only [hs])
  have hLog : logDeriv f s = -1 - s * Fone - s * (s - 1) * ((C : Complex) / (s - 1 / 2)) +
      s * (s - 1) * complexMGF Real.log nu (-s) := by
    rw [hMellin]
    field_simp [hs0, hOneS, hsHalf]
    ring
  have hD := (div_eq_iff hsNonzero).mp (show deriv f s / f s = _ from hLog)
  exact hD.trans (mul_comm _ _)

end Robin1984.GRH
