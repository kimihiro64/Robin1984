import Mathlib.Tactic.FunProp
import Robin1984.GRH.MultiplicityArithmetic

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Gaussian filtering of the repeated prime-power spectrum and finite-frequency subtraction.
- Formalization note: An arithmetic mean extracts the order at each prescribed ordinate and the energy inequality detects simple zeros outside the exceptions.
- PROVENANCE-END
-/

/-!
# The prime-power inequality with prescribed zero orders

Deleting finitely many measured Fourier coefficients leaves the frequencies
whose zeros should be simple. The penalty at a designated ordinate forces
the exact prescribed order.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Complex.Hadamard Filter MeasureTheory Set
open scoped Topology Classical

/-- The mean Fourier coefficient extracted from the arithmetic signal. -/
def arithmeticMultiplicityCoefficient (H : Real -> Complex) (delta : Real) : Complex :=
  Filter.limUnder atTop (multiplicityFrequencyMean H delta)

/-- Delete the measured contribution of each exceptional ordinate. -/
def removeMultiplicityFrequencies (E : Finset Real) (H : Real -> Complex) (t : Real) :
    Complex :=
  H t - E.sum (fun delta => arithmeticMultiplicityCoefficient H delta *
    Complex.exp ((delta : Complex) * Complex.I * (t : Complex)))

private theorem measurable_bounded_removeMultiplicityFrequencies
    (E : Finset Real) (H : Real -> Complex) (hH : Measurable H) {C : Real}
    (hC : forall t, norm (H t) <= C) :
    Measurable (removeMultiplicityFrequencies E H) /\
      forall t, norm (removeMultiplicityFrequencies E H t) <=
        C + E.sum (fun delta => norm (arithmeticMultiplicityCoefficient H delta)) := by
  have hContinuous : Continuous (fun t : Real => E.sum (fun delta =>
      arithmeticMultiplicityCoefficient H delta *
        Complex.exp ((delta : Complex) * Complex.I * (t : Complex)))) := by
    apply continuous_finsetSum
    intro delta _
    fun_prop
  refine And.intro (hH.sub hContinuous.measurable) ?_
  intro t
  unfold removeMultiplicityFrequencies
  refine (norm_sub_le _ _).trans (add_le_add (hC t) ?_)
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro delta _
  rw [norm_mul, Complex.norm_exp]
  have hRe : (((delta : Complex) * Complex.I * (t : Complex)) : Complex).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hRe, Real.exp_zero, mul_one]

private def multiplicityOccurrenceSeries {i : Type*} (gamma : i -> Real)
    (a : i -> Complex) (t : Real) : Complex :=
  tsum (fun j => a j * Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))

private theorem measurable_bounded_multiplicityOccurrenceSeries {i : Type*} [Countable i]
    (gamma : i -> Real) (a : i -> Complex) (ha : Summable (fun j => norm (a j))) :
    Measurable (multiplicityOccurrenceSeries gamma a) /\
      forall t, norm (multiplicityOccurrenceSeries gamma a t) <=
        tsum (fun j => norm (a j)) := by
  let f (j : i) (t : Real) := a j * Complex.exp ((gamma j : Complex) *
    Complex.I * (t : Complex))
  have hf (j : i) : Continuous (f j) := by
    unfold f
    fun_prop
  have hn (j : i) (t : Real) : norm (f j t) = norm (a j) := by
    unfold f
    rw [norm_mul, Complex.norm_exp]
    have hRe : (((gamma j : Complex) * Complex.I * (t : Complex)) : Complex).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hRe, Real.exp_zero, mul_one]
  refine And.intro (Measurable.tsum (fun j => (hf j).measurable)) ?_
  intro t
  have hSum : Summable (fun j => norm (f j t)) := by simpa only [hn] using ha
  simpa only [multiplicityOccurrenceSeries, f, hn] using norm_tsum_le_tsum_norm hSum

private theorem arithmeticMultiplicityCoefficient_eq_fiber {i : Type*} [Countable i]
    (gamma : i -> Real) (a : i -> Complex) (H : Real -> Complex)
    (ha : Summable (fun j => norm (a j))) (hH : Measurable H) {C : Real}
    (hC : forall t, norm (H t) <= C)
    (hAsym : Tendsto (fun t => H t - multiplicityOccurrenceSeries gamma a t) atTop (nhds 0))
    (delta : Real) :
    arithmeticMultiplicityCoefficient H delta =
      tsum (fun j => if gamma j = delta then a j else 0) := by
  have hS := measurable_bounded_multiplicityOccurrenceSeries gamma a ha
  unfold arithmeticMultiplicityCoefficient
  exact (tendsto_multiplicityFrequencyMean H gamma a delta ha hH hC
    (And.intro hS.1 (And.intro hS.2 hAsym))).limUnder_eq

private theorem removeMultiplicityFrequencies_has_restrictedSpectrum {i : Type*} [Countable i]
    (E : Finset Real) (gamma : i -> Real) (a : i -> Complex) (H : Real -> Complex)
    (ha : Summable (fun j => norm (a j))) (hH : Measurable H) {C : Real}
    (hC : forall t, norm (H t) <= C)
    (hAsym : Tendsto (fun t => H t - multiplicityOccurrenceSeries gamma a t) atTop (nhds 0)) :
    let i' := {j : i // Not (Membership.mem E (gamma j))}
    Tendsto (fun t => removeMultiplicityFrequencies E H t -
      multiplicityOccurrenceSeries (fun j : i' => gamma j.val) (fun j => a j.val) t)
      atTop (nhds 0) := by
  dsimp only
  have hPoint (t : Real) :
      removeMultiplicityFrequencies E H t -
        multiplicityOccurrenceSeries
          (fun j : {j : i // Not (Membership.mem E (gamma j))} => gamma j.val)
          (fun j => a j.val) t =
        H t - multiplicityOccurrenceSeries gamma a t := by
    have h := subtract_finiteFrequencies_eq_occurrences_outside E gamma a ha t
    unfold removeMultiplicityFrequencies multiplicityOccurrenceSeries
    simp_rw [arithmeticMultiplicityCoefficient_eq_fiber gamma a H ha hH hC hAsym]
    dsimp only at h
    rw [<- h]
    abel
  simpa only [hPoint] using hAsym

/-- The global energy and mass comparison with omitted frequencies and
prescribed Fourier coefficients at a finite set of ordinates. -/
theorem arithmeticMultiplicityWithPrescribedFrequencies {i : Type*} [Countable i]
    (gamma w : i -> Real) (H1 H2 : Real -> Complex) (E J : Finset Real) (target : Real -> Complex)
    (hw : forall j, 0 < w j)
    (hSum : Summable w) (hSum2 : Summable (fun j => w j ^ 2))
    (hH1 : Measurable H1) (hH2 : Measurable H2) {C1 C2 : Real}
    (hC1 : forall t, norm (H1 t) <= C1) (hC2 : forall t, norm (H2 t) <= C2)
    (hAsym1 : Tendsto (fun t => H1 t -
      multiplicityOccurrenceSeries gamma (fun j => (w j : Complex)) t) atTop (nhds 0))
    (hAsym2 : Tendsto (fun t => H2 t -
      multiplicityOccurrenceSeries gamma (fun j => ((w j ^ 2 : Real) : Complex)) t)
      atTop (nhds 0)) :
    let i' := {j : i // Not (Membership.mem E (gamma j))}
    (spectralSquareEnergy (removeMultiplicityFrequencies E H1) +
      J.sum (fun delta => norm (arithmeticMultiplicityCoefficient H1 delta - target delta) ^ 2) <=
      Filter.limsup (fun t => (removeMultiplicityFrequencies E H2 t).re) atTop) <->
    (Function.Injective (fun j : i' => gamma j.val) /\
      forall delta, Membership.mem J delta ->
        tsum (fun j => if gamma j = delta then (w j : Complex) else 0) = target delta) := by
  dsimp only
  let i' := {j : i // Not (Membership.mem E (gamma j))}
  let gamma' (j : i') := gamma j.val
  let w' (j : i') := w j.val
  let H1' := removeMultiplicityFrequencies E H1
  let H2' := removeMultiplicityFrequencies E H2
  have hSumNorm1 : Summable (fun j => norm (w j : Complex)) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw _)] using hSum
  have hSumNorm2 : Summable (fun j => norm ((w j ^ 2 : Real) : Complex)) := by
    convert hSum2 using 1
    funext j
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (w j))]
  have hSum1' : Summable w' := hSum.subtype _
  have hSum2' : Summable (fun j : i' => w' j ^ 2) := hSum2.subtype _
  have hS1 := measurable_bounded_multiplicityOccurrenceSeries gamma'
    (fun j => (w' j : Complex)) (hSumNorm1.subtype _)
  have hS2 := measurable_bounded_multiplicityOccurrenceSeries gamma'
    (fun j => ((w' j ^ 2 : Real) : Complex)) (hSumNorm2.subtype _)
  have hRestrict1 := removeMultiplicityFrequencies_has_restrictedSpectrum
    E gamma (fun j => (w j : Complex)) H1 hSumNorm1 hH1 hC1 hAsym1
  have hRestrict2 := removeMultiplicityFrequencies_has_restrictedSpectrum
    E gamma (fun j => ((w j ^ 2 : Real) : Complex)) H2 hSumNorm2 hH2 hC2 hAsym2
  have hH1' := measurable_bounded_removeMultiplicityFrequencies E H1 hH1 hC1
  have hEnergy := spectralSquareEnergy_eq_of_tendsto_sub_zero hH1'.1 hS1.1 hH1'.2 hS1.2 hRestrict1
  have hMass := limsup_re_eq_of_tendsto_sub_zero hS2.2 hRestrict2
  have hCompare := fourierOccurrenceMultiplicityComparison w' gamma'
    (fun j => hw j.val) hSum1' hSum2'
  have hLower : Filter.limsup (fun t => (H2' t).re) atTop <= spectralSquareEnergy H1' := by
    exact hMass.le.trans (hCompare.1.trans hEnergy.symm.le)
  have hEquality : spectralSquareEnergy H1' <= Filter.limsup (fun t => (H2' t).re) atTop <->
      Function.Injective gamma' := by
    rw [hEnergy, hMass]
    exact hCompare.2
  simp_rw [arithmeticMultiplicityCoefficient_eq_fiber gamma (fun j => (w j : Complex))
    H1 hSumNorm1 hH1 hC1 hAsym1]
  let d (delta : Real) := norm ((tsum (fun j => if gamma j = delta then (w j : Complex) else 0))
    - target delta) ^ 2
  have hd (delta : Real) : 0 <= d delta := sq_nonneg _
  have hJ : 0 <= J.sum d := Finset.sum_nonneg (fun delta _ => hd delta)
  change (spectralSquareEnergy H1' + J.sum d <= Filter.limsup (fun t => (H2' t).re) atTop) <->
    (Function.Injective gamma' /\ forall delta, Membership.mem J delta ->
      tsum (fun j => if gamma j = delta then (w j : Complex) else 0) = target delta)
  constructor
  case mp =>
    intro h
    have hLE := (le_add_of_nonneg_right hJ).trans h
    have hJ0 : J.sum d = 0 := le_antisymm
      (nonpos_of_add_le_right (h.trans hLower)) hJ
    refine And.intro (hEquality.mp hLE) ?_
    intro delta hDelta
    have hZero := (Finset.sum_eq_zero_iff_of_nonneg (fun delta _ => hd delta)).mp hJ0 delta hDelta
    have hNorm : norm ((tsum (fun j => if gamma j = delta then (w j : Complex) else 0)) -
        target delta) = 0 := by
      have hMul := mul_eq_zero.mp (by simpa only [d, pow_two] using hZero :
        norm ((tsum (fun j => if gamma j = delta then (w j : Complex) else 0)) - target delta) *
            norm ((tsum (fun j => if gamma j = delta then (w j : Complex) else 0)) - target delta) = 0)
      exact hMul.elim id id
    exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)
  case mpr =>
    intro h
    have hJ0 : J.sum d = 0 := Finset.sum_eq_zero_iff_of_nonneg (fun delta _ => hd delta) |>.mpr
      (fun delta hDelta => by simp [d, h.2 delta hDelta])
    rw [hJ0, add_zero]
    exact hEquality.mpr h.1

/-- The Gaussian multiplicity inequality with finite exceptions and prescribed orders. -/
def ExceptionalPrimePowerMultiplicityInequality (A : Real -> Complex)
    (E J : Finset Real) (order : Real -> Nat) : Prop :=
  let H1 := gaussianMultiplicitySignal A 1
  let H2 := gaussianMultiplicitySignal A 2
  spectralSquareEnergy (removeMultiplicityFrequencies E H1) +
    J.sum (fun delta => norm (arithmeticMultiplicityCoefficient H1 delta -
      (order delta : Complex) * (Real.exp (-(delta ^ 2)) : Complex)) ^ 2) <=
    Filter.limsup (fun t => (removeMultiplicityFrequencies E H2 t).re) atTop

/-- Simple zeros outside the omitted ordinates and exact orders at the prescribed ones. -/
def HasPrescribedZeroOrders (F : Complex -> Complex)
    (E J : Finset Real) (order : Real -> Nat) : Prop :=
  (forall delta, Not (Membership.mem E delta) ->
    analyticOrderNatAt F (multiplicityCriticalPoint delta) <= 1) /\
  (forall delta, Membership.mem J delta ->
    analyticOrderNatAt F (multiplicityCriticalPoint delta) = order delta)

/-- If the ordinary Euler factor has no zeros to the right of the critical line,
the arithmetic inequality detects simple zeros and exact prescribed orders. -/
theorem complexArithmeticMultiplicityWithExceptions {iota : Type*} [Countable iota]
    (a : iota -> Real) (b : iota -> Complex) (m : Real) (F : Complex -> Complex)
    (E J : Finset Real) (order : Real -> Nat)
    (ha : forall i, 1 <= a i)
    (hFinite : forall T : Real, Set.Finite {i : iota | a i < T})
    (hSum : forall r : Real, 1 < r -> Summable (fun n => norm (b n) * (a n) ^ (-r)))
    (hOrder : EntireOfOrderAtMost 1 F)
    (hNonzero : exists z, Not (F z = 0))
    (hZero : forall z, F z = 0 -> z.re <= 1 / 2)
    (hEuler : forall s : Complex, 1 < s.re ->
      logDeriv F s = (m : Complex) / (s - 1) -
        tsum (fun n => b n * (a n : Complex) ^ (-s))) :
    HasPrescribedZeroOrders F E J order <->
      ExceptionalPrimePowerMultiplicityInequality
        (triangularLogSignal (complexTriangularRemainder a b m)) E J order := by
  let A := triangularLogSignal (complexTriangularRemainder a b m)
  let _ : Countable (entireNonzeroZeroIndex F) :=
    countable_entireNonzeroZeroIndex hOrder hNonzero
  let i := criticalHadamardOccurrence F
  let gamma : i -> Real := criticalHadamardOrdinate
  let w (j : i) : Real := Real.exp (-(gamma j ^ 2))
  let H1 := gaussianMultiplicitySignal A 1
  let H2 := gaussianMultiplicitySignal A 2
  have hTrace := complexTriangularLogSignal_has_criticalSpectrum a b m F ha hFinite
    hSum hOrder hNonzero hZero hEuler
  choose C hC using hTrace.1
  have hA : Measurable A := measurable_complexTriangularLogSignal a b m
  have hWeights := summable_criticalHadamardOccurrence_denominator hOrder hNonzero
  have hw : Summable w := summable_gaussian_criticalWeights gamma hWeights
  have hp (j : i) : 0 < w j := Real.exp_pos _
  have hOne (j : i) : w j <= 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have hw2 : Summable (fun i => w i ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg (w i))
      (fun j => by
        rw [pow_two]
        exact mul_le_of_le_one_right (hp j).le (hOne j)) hw
  have hSq (j : i) : w j ^ 2 = Real.exp (-(2 : Real) * gamma j ^ 2) := by
    unfold w
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  have hH1 : Tendsto (fun t => H1 t -
      multiplicityOccurrenceSeries gamma (fun j => (w j : Complex)) t) atTop (nhds 0) := by
    simpa only [H1, gaussianMultiplicitySignal, multiplicityOccurrenceSeries, w, neg_mul, one_mul]
      using tendsto_gaussianConvolution_sub_weightedSpectrum gamma hA
        hC hWeights hTrace.2 (a := 1) zero_lt_one
  have hH2 : Tendsto (fun t => H2 t -
      multiplicityOccurrenceSeries gamma (fun j => ((w j ^ 2 : Real) : Complex)) t)
      atTop (nhds 0) := by
    simpa only [H2, gaussianMultiplicitySignal, multiplicityOccurrenceSeries, hSq] using
      tendsto_gaussianConvolution_sub_weightedSpectrum gamma hA
        hC hWeights hTrace.2 (a := 2) (by norm_num)
  let M (v : Real) :=
    (integral volume (fun t => norm (multiplicityGaussianKernel v t : Complex))) * C
  have hNorm (v : Real) (hv : 0 < v) (t : Real) :
      norm (gaussianMultiplicitySignal A v t) <= M v :=
    norm_spectralConvolution_le (integrable_multiplicityGaussianKernel hv) hC t
  let target (delta : Real) : Complex :=
    (order delta : Complex) * (Real.exp (-(delta ^ 2)) : Complex)
  have hCompare := arithmeticMultiplicityWithPrescribedFrequencies gamma w H1 H2 E J target
    hp hw hw2 (measurable_gaussianMultiplicitySignal hA 1)
    (measurable_gaussianMultiplicitySignal hA 2) (hNorm 1 zero_lt_one)
    (hNorm 2 (by norm_num)) hH1 hH2
  have hOutside : Function.Injective
      (fun j : {p : i // Not (Membership.mem E (gamma p))} => gamma j.val) <->
      (forall delta, Not (Membership.mem E delta) ->
        analyticOrderNatAt F (multiplicityCriticalPoint delta) <= 1) :=
    injective_criticalHadamardOrdinate_outside_iff hOrder.differentiable E
  have hTotal (delta : Real) :
      tsum (fun j : i => if gamma j = delta then (w j : Complex) else 0) = target delta <->
        analyticOrderNatAt F (multiplicityCriticalPoint delta) = order delta := by
    have hFiber := criticalOccurrenceFiberSum_eq_order hOrder.differentiable delta
      (fun u => (Real.exp (-(u ^ 2)) : Complex))
    change (tsum (fun j : i => if gamma j = delta then (w j : Complex) else 0)) =
      (analyticOrderNatAt F (multiplicityCriticalPoint delta) : Complex) *
      (Real.exp (-(delta ^ 2)) : Complex) at hFiber
    rw [hFiber]
    unfold target
    constructor
    case mp =>
      intro h
      have hW : Not ((Real.exp (-(delta ^ 2)) : Complex) = 0) :=
        Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
      have hMul :
          ((analyticOrderNatAt F (multiplicityCriticalPoint delta) : Complex) -
             (order delta : Complex)) * (Real.exp (-(delta ^ 2)) : Complex) = 0 := by
        rw [sub_mul, h, sub_self]
      have hc := sub_eq_zero.mp ((mul_eq_zero.mp hMul).resolve_right hW)
      exact_mod_cast hc
    case mpr =>
      intro h
      rw [h]
  unfold HasPrescribedZeroOrders
  change _ <-> ExceptionalPrimePowerMultiplicityInequality A E J order
  refine Iff.trans ?_ hCompare.symm
  simp only [hOutside, hTotal]

end Robin1984.GRH
