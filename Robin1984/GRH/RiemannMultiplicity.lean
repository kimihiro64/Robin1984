import Mathlib.Tactic.FunProp
import Robin1984.GRH.MultiplicityDivisor
import Robin1984.GRH.MultiplicityGaussian
import Robin1984.GRH.RiemannMultiplicityArithmetic

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The Gaussian-smoothed global multiplicity test for the classical von Mangoldt remainder.
- Formalization note: Under RH the arithmetic remainder has the critical-line occurrence spectrum, and the mean-square inequality detects simple zeta zeros.
- PROVENANCE-END
-/

/-!
# A global criterion for simple Riemann zeta zeros

Under RH the Gaussian-smoothed signed von Mangoldt remainder satisfies
the global mean-square inequality exactly when the nontrivial zeros of
the Riemann zeta function are simple.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Complex.Hadamard Filter MeasureTheory Set
open scoped Topology

private theorem continuous_logScaled_grandElementaryTerm (beta : Complex) (m m0 mNeg : Real) :
    Continuous (fun t : Real => (Real.exp (-t / 2) : Complex) *
      grandElementaryTerm beta m m0 mNeg (Real.exp t)) := by
  let X (t : Real) : Complex := (Real.exp (-t / 2) : Complex)
  let Y (t : Real) : Complex := (Real.exp (-t) : Complex)
  have hX : Continuous X := Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_id.neg.div_const 2))
  have hY : Continuous Y := Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp continuous_id.neg)
  have hC : Continuous (fun t : Real => (t : Complex)) := Complex.continuous_ofReal
  have h : (fun t : Real => X t * grandElementaryTerm beta m m0 mNeg (Real.exp t)) =
      (fun t : Real => X t * ((beta + m - m0) +
        ((m0 : Complex) - beta - (m : Complex) / 2) * Y t +
        (m0 : Complex) * (t : Complex) -
        (mNeg : Complex) * (Y t * (t : Complex)))) := by
    funext t
    simp only [grandElementaryTerm, Real.log_exp, Y, Complex.cpow_neg, Complex.cpow_one,
      <- Complex.ofReal_inv, <- Real.exp_neg]
  change Continuous (fun t : Real => X t * grandElementaryTerm beta m m0 mNeg (Real.exp t))
  rw [h]
  exact hX.mul (((continuous_const.add (continuous_const.mul hY)).add
    (continuous_const.mul hC)).sub (continuous_const.mul (hY.mul hC)))

private theorem exists_bound_logScaled_grandElementaryTerm (beta : Complex) (m m0 mNeg : Real) :
    exists B : Real, forall t : Real, 0 <= t ->
      norm ((Real.exp (-t / 2) : Complex) * grandElementaryTerm beta m m0 mNeg (Real.exp t)) <= B := by
  let E (t : Real) : Complex := (Real.exp (-t / 2) : Complex) *
    grandElementaryTerm beta m m0 mNeg (Real.exp t)
  have hLim : Tendsto E atTop (nhds 0) :=
    tendsto_logScaled_grandElementaryTerm beta m m0 mNeg
  have hNorm := (Metric.tendsto_nhds.1 hLim) 1 zero_lt_one
  choose T hT using eventually_atTop.1 hNorm
  let U := max T 0
  have hCont : Continuous (fun t => norm (E t)) :=
    (continuous_logScaled_grandElementaryTerm beta m m0 mNeg).norm
  have hCompact : IsCompact ((fun t => norm (E t)) '' Icc 0 U) :=
    isCompact_Icc.image hCont
  choose C hC using hCompact.bddAbove
  refine Exists.intro (max C 1) (fun t h0 => ?_)
  by_cases ht : t <= U
  case pos =>
    exact (hC (mem_image_of_mem (fun t => norm (E t)) (And.intro h0 ht))).trans (le_max_left _ _)
  case neg =>
    have hDist := hT t ((le_max_left T 0).trans (le_of_lt (lt_of_not_ge ht)))
    have ht' : norm (E t) < 1 := by simpa only [dist_zero_right] using hDist
    exact ht'.le.trans (le_max_right _ _)

/-- The normalized prime-power signal in the classical criterion. -/
def riemannArithmeticLogSignal (t : Real) : Complex :=
  triangularLogSignal (fun x => (riemannArithmeticRemainder x : Complex)) t

theorem measurable_riemannArithmeticLogSignal : Measurable riemannArithmeticLogSignal := by
  have hR : Measurable riemannArithmeticRemainder :=
    measurable_triangularRemainder riemannPrimePowerNorm ArithmeticFunction.vonMangoldt 1
  unfold riemannArithmeticLogSignal triangularLogSignal
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
  exact (Complex.continuous_ofReal.measurable.comp
    (Real.continuous_exp.measurable.comp (measurable_id.neg.div_const 2))).mul
      (Complex.continuous_ofReal.measurable.comp (hR.comp Real.continuous_exp.measurable))

theorem riemannPoleClearedFactor_nontrivial : exists z, Not (riemannPoleClearedFactor z = 0) :=
  Exists.intro 1 riemannPoleClearedFactor_ne_zero_at_one

theorem countable_riemannCriticalHadamardOccurrences :
    Countable (criticalHadamardOccurrence riemannPoleClearedFactor) := by
  let _ : Countable (entireNonzeroZeroIndex riemannPoleClearedFactor) :=
    countable_entireNonzeroZeroIndex riemannPoleClearedFactor_entireOrderOne
      riemannPoleClearedFactor_nontrivial
  infer_instance

/-- Under RH the classical prime-power signal is bounded and has the
critical-line Fourier expansion with the exact von Mangoldt remainder. -/
theorem riemannArithmeticLogSignal_has_criticalSpectrum (hRH : RiemannHypothesis) :
    (exists C : Real, forall t, norm (riemannArithmeticLogSignal t) <= C) /\
    Tendsto (fun t : Real => riemannArithmeticLogSignal t -
      tsum (fun i : criticalHadamardOccurrence riemannPoleClearedFactor =>
        Inv.inv (((1 / 2 : Complex) + (criticalHadamardOrdinate i : Complex) * Complex.I) *
          ((3 / 2 : Complex) + (criticalHadamardOrdinate i : Complex) * Complex.I)) *
          Complex.exp ((criticalHadamardOrdinate i : Complex) * Complex.I * (t : Complex))))
      atTop (nhds 0) := by
  let F := riemannPoleClearedFactor
  let rho : regularHadamardZeroIndex F -> Complex := regularHadamardZero
  let R (x : Real) : Complex := (riemannArithmeticRemainder x : Complex)
  let _ : Countable (entireNonzeroZeroIndex F) :=
    countable_entireNonzeroZeroIndex riemannPoleClearedFactor_entireOrderOne
      riemannPoleClearedFactor_nontrivial
  have hF : Differentiable Complex F := riemannPoleClearedFactor_entireOrderOne.differentiable
  have hRho (i : regularHadamardZeroIndex F) : (rho i).re <= 1 / 2 :=
    riemannPoleClearedFactor_zero_re_le_half hRH (entireNonzeroZero_is_zero hF i.val)
  have hWeight := summable_regularHadamardZeroWeight riemannPoleClearedFactor_entireOrderOne
    riemannPoleClearedFactor_nontrivial
  have hWeightInv : Summable (fun i => Inv.inv (norm (rho i * (rho i + 1)))) := by
    simpa only [zpow_neg_one] using hWeight
  have hEuler (s : Complex) (hs : 1 < s.re) :
      logDeriv F s = (1 : Complex) / (s - 1) -
        tsum (fun n => (ArithmeticFunction.vonMangoldt n : Complex) *
          (riemannPrimePowerNorm n : Complex) ^ (-s)) := by
    rw [<- LSeries_vonMangoldt_eq_tsum_primePowerNorm,
      riemannPoleClearedFactor_logDeriv hs]
  choose beta m0 mNeg hHad using entireOfOrderAtMost_one_logDeriv_regular
    riemannPoleClearedFactor_entireOrderOne riemannPoleClearedFactor_nontrivial
  let E := grandElementaryTerm beta 1 (m0 : Real) (mNeg : Real)
  have hHadRight (s : Complex) (hs : 1 < s.re) :
      logDeriv F s = beta + ((m0 : Real) : Complex) / s +
        ((mNeg : Real) : Complex) * (1 / (s + 1) - 1) +
        tsum (fun i : regularHadamardZeroIndex F => 1 / (s - rho i) + 1 / rho i) := by
    have hs0 : Not (s = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
    have hs1 : Not (s = 1) := by
      intro he
      rw [he, Complex.one_re] at hs
      exact (lt_irrefl _ hs)
    have hFs : Not (F s = 0) := by
      unfold F
      rw [riemannPoleClearedFactor_eq (zero_lt_one.trans hs) hs1]
      exact mul_ne_zero
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (sub_ne_zero.mpr hs1))
        (riemannZeta_ne_zero_of_one_lt_re hs)
    simpa only [Complex.ofReal_natCast] using hHad s hs0 hFs
  have hAE : Filter.EventuallyEq (ae (volume.restrict (Ioi (1 : Real)))) R
      (fun x => E x + tsum (fun i => triangularZeroTerm (rho i) x)) :=
    ae_triangularRemainder_eq_complex_expansion riemannPrimePowerNorm ArithmeticFunction.vonMangoldt
      1 F rho beta m0 mNeg one_le_riemannPrimePowerNorm
      (fun r hr => summable_norm_vonMangoldt_primePowerNorm hr) (by simpa only [Complex.ofReal_one] using hEuler)
      hRho (fun i => i.val.property) (fun i => i.property) hWeight hHadRight
  have hRCont : ContinuousOn R (Ioi 1) :=
    Complex.continuous_ofReal.comp_continuousOn continuousOn_riemannArithmeticRemainder
  have hECont := continuousOn_grandElementaryTerm beta 1 (m0 : Real) (mNeg : Real)
  have hELim := tendsto_logScaled_grandElementaryTerm beta 1 (m0 : Real) (mNeg : Real)
  have hAsym := tendsto_triangularLogSignal_sub_criticalSpectrum
    rho hRho hWeightInv hRCont hECont hAE hELim
  constructor
  case right =>
    refine hAsym.congr' (Filter.Eventually.of_forall (fun t => ?_))
    exact congrArg (fun z : Complex => triangularLogSignal R t - z)
      (tsum_triangularCriticalSpectrumTerm_eq_occurrenceSeries (F := F) t)
  case left =>
    let B := tsum (fun i : regularHadamardZeroIndex F => (norm (rho i * (rho i + 1))) ^ (-1 : Int))
    choose C hC using exists_bound_logScaled_grandElementaryTerm beta 1 (m0 : Real) (mNeg : Real)
    let D := max (norm (riemannArithmeticLogSignal 0)) (C + 2 * B)
    have hD0 : 0 <= D := (norm_nonneg _).trans (le_max_left _ _)
    refine Exists.intro D (fun t => ?_)
    by_cases hP : 0 < t
    case pos =>
      have hx : 1 < Real.exp t := Real.one_lt_exp_iff.mpr hP
      have hPoint := eqOn_triangularZeroSeries_of_ae rho hRho hWeightInv hRCont hECont hAE hx
      let q : Complex := (Real.exp (-t / 2) : Complex)
      let S : Complex := tsum (fun i => triangularZeroTerm (rho i) (Real.exp t))
      have hS : norm S <= (2 * Real.sqrt (Real.exp t)) * B :=
        norm_tsum_triangularZeroTerm_le rho hRho hWeight hx.le
      have hExp : Real.exp (-t / 2) * Real.sqrt (Real.exp t) = 1 := by
        rw [Real.sqrt_eq_rpow, <- Real.exp_mul, <- Real.exp_add]
        rw [show -t / 2 + t * (1 / 2) = 0 by ring, Real.exp_zero]
      have hQS : norm (q * S) <= 2 * B := by
        rw [norm_mul, show norm q = Real.exp (-t / 2) by
          simp only [q, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]]
        calc
          _ <= Real.exp (-t / 2) * (2 * Real.sqrt (Real.exp t) * B) :=
            mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
          _ = (Real.exp (-t / 2) * Real.sqrt (Real.exp t)) * (2 * B) := by ring
          _ = _ := by rw [hExp, one_mul]
      unfold riemannArithmeticLogSignal triangularLogSignal
      rw [if_neg hP.not_gt]
      change norm (q * R (Real.exp t)) <= D
      rw [hPoint, mul_add]
      exact ((norm_add_le _ _).trans (add_le_add (hC t hP.le) hQS)).trans (le_max_right _ _)
    case neg =>
      by_cases hN : t < 0
      case pos =>
        simpa only [riemannArithmeticLogSignal, triangularLogSignal, if_pos hN, norm_zero] using hD0
      case neg =>
        have ht : t = 0 := le_antisymm (le_of_not_gt hP) (le_of_not_gt hN)
        rw [ht]
        exact le_max_left _ _

private theorem fourierOccurrenceSeries_measurable_and_bounded {i : Type*} [Countable i]
    (gamma w : i -> Real) (hW : forall i, 0 <= w i) (hSum : Summable w) :
    let S := fun t : Real => tsum (fun i => (w i : Complex) *
      Complex.exp ((gamma i : Complex) * Complex.I * (t : Complex)))
    Measurable S /\ forall t, norm (S t) <= tsum w := by
  let f (j : i) (t : Real) : Complex := (w j : Complex) *
    Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex))
  have hf (j : i) : Continuous (f j) :=
    continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))
  have hn (j : i) (t : Real) : norm (f j t) = w j := by
    unfold f
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW j)]
    simp [Complex.mul_re, Complex.mul_im]
  change Measurable (fun t => tsum (fun j => f j t)) /\
    forall t, norm (tsum (fun j => f j t)) <= tsum w
  constructor
  case left =>
    exact Measurable.tsum (fun j => (hf j).measurable)
  case right =>
    intro t
    have hs : Summable (fun j => norm (f j t)) := by simpa only [hn] using hSum
    simpa only [hn] using norm_tsum_le_tsum_norm hs

/-- The two Gaussian smoothings of the normalized classical prime-power signal. -/
def riemannMultiplicitySignal (a t : Real) : Complex :=
  spectralConvolution (fun v => (multiplicityGaussianKernel a v : Complex)) riemannArithmeticLogSignal t

/-- The global inequality for simplicity of the nontrivial zeros of zeta. -/
def RiemannMultiplicityInequality : Prop :=
  spectralSquareEnergy (riemannMultiplicitySignal 1) <=
    Filter.limsup (fun t : Real => (riemannMultiplicitySignal 2 t).re) atTop

private theorem measurable_riemannMultiplicitySignal (a : Real) :
    Measurable (riemannMultiplicitySignal a) := by
  have h := measurable_riemannArithmeticLogSignal
  have hK : Continuous (fun v : Real => (multiplicityGaussianKernel a v : Complex)) := by
    unfold multiplicityGaussianKernel multiplicityGaussian
    fun_prop
  exact measurable_spectralConvolution hK.measurable h

private theorem riemannPoleClearedFactor_order_pos {z : Complex}
    (hZero : riemannPoleClearedFactor z = 0) :
    0 < analyticOrderNatAt riemannPoleClearedFactor z := by
  have hF := riemannPoleClearedFactor_entireOrderOne.differentiable
  have h0 : Not (analyticOrderAt riemannPoleClearedFactor z = 0) := fun h =>
    ((hF.analyticAt z).analyticOrderAt_eq_zero.mp h) hZero
  have ht : Not (analyticOrderAt riemannPoleClearedFactor z = Top.top) := by
    intro he
    have hD := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (fun w => hF.analyticAt w)).mp he
    exact riemannPoleClearedFactor_ne_zero_at_one (congrFun hD 1)
  exact ENat.toNat_pos h0 ht

private theorem zeta_orderOne_in_strip_iff_criticalOccurrences_injective
    (hRH : RiemannHypothesis) :
    (forall z : Complex, 0 < z.re -> z.re < 1 -> riemannZeta z = 0 ->
      analyticOrderNatAt riemannZeta z = 1) <->
    Function.Injective (criticalHadamardOrdinate (F := riemannPoleClearedFactor)) := by
  rw [injective_criticalHadamardOrdinate_iff riemannPoleClearedFactor_entireOrderOne.differentiable]
  constructor
  case mp =>
    intro h z hz hFZero
    have hz0 : 0 < z.re := by rw [hz]; norm_num
    have hz1 : z.re < 1 := by rw [hz]; norm_num
    have hs1 : Not (z = 1) := by
      intro he
      rw [he, Complex.one_re] at hz1
      exact (lt_irrefl _ hz1)
    have hPi : Not ((Real.pi : Complex) = 0) := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [riemannPoleClearedFactor_eq hz0 hs1] at hFZero
    have hZ := (mul_eq_zero.mp hFZero).resolve_left (mul_ne_zero hPi (sub_ne_zero.mpr hs1))
    rw [analyticOrderNatAt_riemannPoleClearedFactor_eq hz0 hz1, h z hz0 hz1 hZ]
  case mpr =>
    intro h z hz0 hz1 hZ
    have hs1 : Not (z = 1) := by
      intro he
      rw [he, Complex.one_re] at hz1
      exact (lt_irrefl _ hz1)
    have hNontriv : Not (exists n : Nat, z = -2 * (n + 1)) := by
      intro hneg
      choose n hn using hneg
      rw [hn] at hz0
      have hn0 : (0 : Real) <= n := Nat.cast_nonneg n
      norm_num [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re] at hz0
      linarith only [hz0, hn0]
    have hRe := hRH z hZ hNontriv hs1
    have hF0 : riemannPoleClearedFactor z = 0 := by
      rw [riemannPoleClearedFactor_eq hz0 hs1, hZ, mul_zero]
    have hOne := le_antisymm (h z hRe hF0)
      (Nat.succ_le_of_lt (riemannPoleClearedFactor_order_pos hF0))
    rwa [analyticOrderNatAt_riemannPoleClearedFactor_eq hz0 hz1] at hOne

/-- **Classical RH multiplicity.** Under RH, the Gaussian-smoothed
prime-power inequality is equivalent to simplicity of every nontrivial
zero of the Riemann zeta function. -/
theorem riemannRH_simpleZeros_iff_globalMultiplicityInequality
    (hRH : RiemannHypothesis) :
    (forall z : Complex, 0 < z.re -> z.re < 1 -> riemannZeta z = 0 ->
      analyticOrderNatAt riemannZeta z = 1) <-> RiemannMultiplicityInequality := by
  let i := criticalHadamardOccurrence riemannPoleClearedFactor
  let gamma (j : i) : Real := criticalHadamardOrdinate j
  let w (j : i) : Real := Real.exp (-(gamma j ^ 2))
  let S1 (t : Real) : Complex := tsum (fun j => (w j : Complex) *
    Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))
  let S2 (t : Real) : Complex := tsum (fun j => ((w j ^ 2 : Real) : Complex) *
    Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))
  let _ : Countable i := countable_riemannCriticalHadamardOccurrences
  have hWeights := summable_criticalHadamardOccurrence_denominator
    riemannPoleClearedFactor_entireOrderOne riemannPoleClearedFactor_nontrivial
  have hw : Summable w := summable_gaussian_criticalWeights gamma hWeights
  have hp (j : i) : 0 < w j := Real.exp_pos _
  have hOne (j : i) : w j <= 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have hw2 : Summable (fun i => w i ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg (w i))
      (fun j => by
        rw [pow_two]
        exact mul_le_of_le_one_right (hp j).le (hOne j)) hw
  have hS1 := fourierOccurrenceSeries_measurable_and_bounded gamma w (fun j => (hp j).le) hw
  have hS2 := fourierOccurrenceSeries_measurable_and_bounded gamma (fun j => w j ^ 2)
    (fun j => sq_nonneg (w j)) hw2
  have hR := riemannArithmeticLogSignal_has_criticalSpectrum hRH
  choose C hBound using hR.1
  have hSq (j : i) : w j ^ 2 = Real.exp (-(2 : Real) * gamma j ^ 2) := by
    unfold w
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  have hH1 : Tendsto (fun t => riemannMultiplicitySignal 1 t - S1 t) atTop (nhds 0) := by
    simpa only [riemannMultiplicitySignal, S1, w, neg_mul, one_mul] using
      tendsto_gaussianConvolution_sub_weightedSpectrum gamma measurable_riemannArithmeticLogSignal
        hBound hWeights hR.2 (a := 1) zero_lt_one
  have hH2 : Tendsto (fun t => riemannMultiplicitySignal 2 t - S2 t) atTop (nhds 0) := by
    simpa only [riemannMultiplicitySignal, S2, hSq] using
      tendsto_gaussianConvolution_sub_weightedSpectrum gamma measurable_riemannArithmeticLogSignal
        hBound hWeights hR.2 (a := 2) (by norm_num)
  have hK1 := integrable_multiplicityGaussianKernel (a := 1) zero_lt_one
  have hNorm1 (t : Real) : norm (riemannMultiplicitySignal 1 t) <=
      (integral volume (fun v => norm (multiplicityGaussianKernel 1 v : Complex))) * C :=
    norm_spectralConvolution_le hK1 hBound t
  have hEnergy := spectralSquareEnergy_eq_of_tendsto_sub_zero
    (measurable_riemannMultiplicitySignal 1) hS1.1 hNorm1 hS1.2 hH1
  have hMass := limsup_re_eq_of_tendsto_sub_zero hS2.2 hH2
  have hCriterion : (spectralSquareEnergy S1 <=
      Filter.limsup (fun t : Real => (S2 t).re) atTop) <->
      Function.Injective gamma := fourierOccurrenceMultiplicityCriterion w gamma hp hw hw2
  unfold RiemannMultiplicityInequality
  rw [hEnergy, hMass, hCriterion]
  exact zeta_orderOne_in_strip_iff_criticalOccurrences_injective hRH

end Robin1984.GRH
