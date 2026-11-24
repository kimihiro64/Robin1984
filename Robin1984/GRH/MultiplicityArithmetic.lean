import Mathlib.Tactic.FunProp
import Robin1984.GRH.MultiplicityDivisor
import Robin1984.GRH.MultiplicityGaussian

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Gaussian smoothing of the triangular explicit formula and positive Fourier spectra.
- Formalization note: The exact complex prime-power remainder has the repeated critical-line spectrum and the global Gaussian inequality detects its repetitions.
- PROVENANCE-END
-/

/-!
# The global multiplicity criterion for complex arithmetic signals

The repeated critical-line zero spectrum is obtained from the actual
signed prime-power remainder. Its two Gaussian smoothings give the
global mean-square test.
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

theorem measurable_complexTriangularLogSignal {i : Type*} [Countable i]
    (a : i -> Real) (b : i -> Complex) (m : Real) :
    Measurable (triangularLogSignal (complexTriangularRemainder a b m)) := by
  have hR := measurable_complexTriangularRemainder a b m
  unfold triangularLogSignal
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
  exact (Complex.continuous_ofReal.measurable.comp
    (Real.continuous_exp.measurable.comp (measurable_id.neg.div_const 2))).mul
      (hR.comp Real.continuous_exp.measurable)

/-- The actual signed complex prime-power signal has a bounded continuous-tail
representative and the repeated critical-line spectrum of its entire factor. -/
theorem complexTriangularLogSignal_has_criticalSpectrum {iota : Type*} [Countable iota]
    (a : iota -> Real) (b : iota -> Complex) (m : Real) (F : Complex -> Complex)
    (ha : forall i, 1 <= a i)
    (hFinite : forall T : Real, Set.Finite {i : iota | a i < T})
    (hSum : forall r : Real, 1 < r -> Summable (fun n => norm (b n) * (a n) ^ (-r)))
    (hOrder : EntireOfOrderAtMost 1 F)
    (hNonzero : exists z, Not (F z = 0))
    (hZero : forall z, F z = 0 -> z.re <= 1 / 2)
    (hEuler : forall s : Complex, 1 < s.re ->
      logDeriv F s = (m : Complex) / (s - 1) -
        tsum (fun n => b n * (a n : Complex) ^ (-s))) :
    (exists C : Real, forall t, norm ((triangularLogSignal (complexTriangularRemainder a b m)) t) <= C) /\
    Tendsto (fun t : Real => (triangularLogSignal (complexTriangularRemainder a b m)) t -
      tsum (fun i : criticalHadamardOccurrence F =>
        Inv.inv (((1 / 2 : Complex) + (criticalHadamardOrdinate i : Complex) * Complex.I) *
          ((3 / 2 : Complex) + (criticalHadamardOrdinate i : Complex) * Complex.I)) *
          Complex.exp ((criticalHadamardOrdinate i : Complex) * Complex.I * (t : Complex))))
      atTop (nhds 0) := by
  let rho : regularHadamardZeroIndex F -> Complex := regularHadamardZero
  let R := complexTriangularRemainder a b m
  let _ : Countable (entireNonzeroZeroIndex F) :=
    countable_entireNonzeroZeroIndex hOrder hNonzero
  have hF : Differentiable Complex F := hOrder.differentiable
  have hRho (i : regularHadamardZeroIndex F) : (rho i).re <= 1 / 2 :=
    hZero _ (entireNonzeroZero_is_zero hF i.val)
  have hWeight := summable_regularHadamardZeroWeight hOrder hNonzero
  have hWeightInv : Summable (fun i => Inv.inv (norm (rho i * (rho i + 1)))) := by
    simpa only [zpow_neg_one] using hWeight
  choose beta m0 mNeg hHad using entireOfOrderAtMost_one_logDeriv_regular hOrder hNonzero
  let E := grandElementaryTerm beta m (m0 : Real) (mNeg : Real)
  have hHadRight (s : Complex) (hs : 1 < s.re) :
      logDeriv F s = beta + ((m0 : Real) : Complex) / s +
        ((mNeg : Real) : Complex) * (1 / (s + 1) - 1) +
        tsum (fun i : regularHadamardZeroIndex F => 1 / (s - rho i) + 1 / rho i) := by
    have hs0 : Not (s = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
    have hFs : Not (F s = 0) := by
      intro he
      have h := hZero s he
      linarith only [h, hs]
    simpa only [Complex.ofReal_natCast] using hHad s hs0 hFs
  have hAE : Filter.EventuallyEq (ae (volume.restrict (Ioi (1 : Real)))) R
      (fun x => E x + tsum (fun i => triangularZeroTerm (rho i) x)) :=
    ae_complexTriangularRemainder_eq_expansion a b m F rho beta m0 mNeg ha hSum hEuler
      hRho (fun i => i.val.property) (fun i => i.property) hWeight hHadRight
  have hRCont : ContinuousOn R (Ioi 1) :=
    continuousOn_complexTriangularRemainder a b m hFinite
  have hECont := continuousOn_grandElementaryTerm beta m (m0 : Real) (mNeg : Real)
  have hELim := tendsto_logScaled_grandElementaryTerm beta m (m0 : Real) (mNeg : Real)
  have hAsym := tendsto_triangularLogSignal_sub_criticalSpectrum
    rho hRho hWeightInv hRCont hECont hAE hELim
  constructor
  case right =>
    refine hAsym.congr' (Filter.Eventually.of_forall (fun t => ?_))
    exact congrArg (fun z : Complex => triangularLogSignal R t - z)
      (tsum_triangularCriticalSpectrumTerm_eq_occurrenceSeries (F := F) t)
  case left =>
    let B := tsum (fun i : regularHadamardZeroIndex F => (norm (rho i * (rho i + 1))) ^ (-1 : Int))
    choose C hC using exists_bound_logScaled_grandElementaryTerm beta m (m0 : Real) (mNeg : Real)
    let D := max (norm ((triangularLogSignal (complexTriangularRemainder a b m)) 0)) (C + 2 * B)
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
      unfold triangularLogSignal
      rw [if_neg hP.not_gt]
      change norm (q * R (Real.exp t)) <= D
      rw [hPoint, mul_add]
      exact ((norm_add_le _ _).trans (add_le_add (hC t hP.le) hQS)).trans (le_max_right _ _)
    case neg =>
      by_cases hN : t < 0
      case pos =>
        simpa only [triangularLogSignal, if_pos hN, norm_zero] using hD0
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

/-- Gaussian smoothing of a normalized prime-power input. -/
def gaussianMultiplicitySignal (A : Real -> Complex) (a t : Real) : Complex :=
  spectralConvolution (fun v => (multiplicityGaussianKernel a v : Complex)) A t

/-- The mean-square inequality for an uncorrected prime-power input. -/
def GaussianMultiplicityInequality (A : Real -> Complex) : Prop :=
  spectralSquareEnergy (gaussianMultiplicitySignal A 1) <=
    Filter.limsup (fun t : Real => (gaussianMultiplicitySignal A 2 t).re) atTop

private theorem measurable_gaussianMultiplicitySignal {A : Real -> Complex}
    (hA : Measurable A) (a : Real) :
    Measurable (gaussianMultiplicitySignal A a) := by
  have hK : Continuous (fun v : Real => (multiplicityGaussianKernel a v : Complex)) := by
    unfold multiplicityGaussianKernel multiplicityGaussian
    fun_prop
  exact measurable_spectralConvolution hK.measurable hA

/-- The Gaussian inequality detects repeated frequencies of an arithmetic
signal with the repeated triangular Hadamard expansion. -/
theorem gaussianMultiplicityInequality_iff_injective {i : Type*} [Countable i]
    (A : Real -> Complex) (gamma : i -> Real) (hA : Measurable A)
    {C : Real} (hBound : forall t, norm (A t) <= C)
    (hWeights : Summable (fun j => Inv.inv (norm
      (((1 / 2 : Complex) + (gamma j : Complex) * Complex.I) *
        ((3 / 2 : Complex) + (gamma j : Complex) * Complex.I)))))
    (hAsym : Tendsto (fun t : Real => A t -
      tsum (fun j => Inv.inv
        (((1 / 2 : Complex) + (gamma j : Complex) * Complex.I) *
          ((3 / 2 : Complex) + (gamma j : Complex) * Complex.I)) *
        Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex))))
      atTop (nhds 0)) :
    GaussianMultiplicityInequality A <-> Function.Injective gamma := by
  let w (j : i) : Real := Real.exp (-(gamma j ^ 2))
  let S1 (t : Real) : Complex := tsum (fun j => (w j : Complex) *
    Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))
  let S2 (t : Real) : Complex := tsum (fun j => ((w j ^ 2 : Real) : Complex) *
    Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))
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
  have hSq (j : i) : w j ^ 2 = Real.exp (-(2 : Real) * gamma j ^ 2) := by
    unfold w
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  have hH1 : Tendsto (fun t => gaussianMultiplicitySignal A 1 t - S1 t) atTop (nhds 0) := by
    simpa only [gaussianMultiplicitySignal, S1, w, neg_mul, one_mul] using
      tendsto_gaussianConvolution_sub_weightedSpectrum gamma hA
        hBound hWeights hAsym (a := 1) zero_lt_one
  have hH2 : Tendsto (fun t => gaussianMultiplicitySignal A 2 t - S2 t) atTop (nhds 0) := by
    simpa only [gaussianMultiplicitySignal, S2, hSq] using
      tendsto_gaussianConvolution_sub_weightedSpectrum gamma hA
        hBound hWeights hAsym (a := 2) (by norm_num)
  have hK1 := integrable_multiplicityGaussianKernel (a := 1) zero_lt_one
  have hNorm1 (t : Real) : norm (gaussianMultiplicitySignal A 1 t) <=
      (integral volume (fun v => norm (multiplicityGaussianKernel 1 v : Complex))) * C :=
    norm_spectralConvolution_le hK1 hBound t
  have hEnergy := spectralSquareEnergy_eq_of_tendsto_sub_zero
    (measurable_gaussianMultiplicitySignal hA 1) hS1.1 hNorm1 hS1.2 hH1
  have hMass := limsup_re_eq_of_tendsto_sub_zero hS2.2 hH2
  have hCriterion : (spectralSquareEnergy S1 <=
      Filter.limsup (fun t : Real => (S2 t).re) atTop) <->
      Function.Injective gamma := fourierOccurrenceMultiplicityCriterion w gamma hp hw hw2
  unfold GaussianMultiplicityInequality
  rw [hEnergy, hMass, hCriterion]

end Robin1984.GRH
