import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order
import Robin1984.GRH.DedekindSpectralMellin

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Mellin inversion of the triangular kernel applied to the genus-one logarithmic derivative.
- Formalization note: The zeros at zero and minus one are integrated separately, with a complex Mellin uniqueness argument for the remaining expansion.
- PROVENANCE-END
-/

/-!
# The triangular remainder from a Hadamard expansion

The Mellin transforms match the signed prime-power remainder with a zero
series and elementary terms. The right-half-plane zero condition bounds
this series even when it includes trivial zeros to the left of the line.
-/

open Complex.Hadamard Filter MeasureTheory Set

set_option autoImplicit false

namespace Robin1984.GRH

/-- The elementary contribution from the pole and the zeros at zero and minus one. -/
noncomputable def grandElementaryTerm (b : Complex) (m m0 mNeg : Real)
    (x : Real) : Complex :=
  (b + m - m0) + ((m0 : Complex) - b - (m : Complex) / 2) * (x : Complex) ^ (-(1 : Complex)) +
    (m0 : Complex) * (Real.log x : Complex) -
    (mNeg : Complex) * ((x : Complex) ^ (-(1 : Complex)) * (Real.log x : Complex))

private theorem grandMonomial_mellin (s r : Complex) (h : r.re < s.re) :
    let mu := volume.restrict (Ioi (1 : Real))
    let k := fun x : Real => (x : Complex) ^ (-s - 1) * (x : Complex) ^ r
    And (Integrable k mu) (integral mu k = 1 / (s - r)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let k := fun x : Real => (x : Complex) ^ (-s - 1) * (x : Complex) ^ r
  let p := fun x : Real => (x : Complex) ^ (-(s - r) - 1)
  have hExp : (-(s - r) - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith only [h]
  have hP : IntegrableOn p (Ioi (1 : Real)) := integrableOn_Ioi_cpow_of_lt hExp zero_lt_one
  have hEq : EqOn p k (Ioi 1) := by
    intro x hx
    have hxn := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
    dsimp only [p, k]
    rw [<- Complex.cpow_add _ _ hxn]
    congr 1
    ring
  refine And.intro (hP.congr_fun hEq measurableSet_Ioi) ?_
  rw [<- setIntegral_congr_fun measurableSet_Ioi hEq]
  change integral mu (fun x : Real => (x : Complex) ^ (-(s - r) - 1)) = _
  rw [integral_Ioi_cpow_of_lt hExp zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
  rw [sub_add_cancel, neg_div_neg_eq]

private theorem grandLogMonomial_mellin (s r : Complex) (h : 1 < (s - r).re) :
    let mu := volume.restrict (Ioi (1 : Real))
    let k := fun x : Real => (x : Complex) ^ (-s - 1) * ((x : Complex) ^ r * (Real.log x : Complex))
    And (Integrable k mu) (integral mu k = 1 / (s - r) ^ (2 : Nat)) := by
  let p := fun x : Real => (x : Complex) ^ (-(s - r) - 1) * (Real.log x : Complex)
  let k := fun x : Real => (x : Complex) ^ (-s - 1) * ((x : Complex) ^ r * (Real.log x : Complex))
  have hEq : EqOn p k (Ioi 1) := by
    intro x hx
    have hxn := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
    dsimp only [p, k]
    rw [<- mul_assoc, <- Complex.cpow_add _ _ hxn]
    congr 2
    ring
  have hP := integral_cpow_log_from_one h
  have hpInt : IntegrableOn p (Ioi (1 : Real)) := hP.1
  exact And.intro (hpInt.congr_fun hEq measurableSet_Ioi)
    ((setIntegral_congr_fun measurableSet_Ioi hEq).symm.trans hP.2)

private theorem grandElementaryTerm_mellin (b : Complex) (m m0 mNeg : Real)
    (s : Complex) (hs : 1 < s.re) :
    let mu := volume.restrict (Ioi (1 : Real))
    let k := fun x : Real => grandElementaryTerm b m m0 mNeg x * (x : Complex) ^ (-s - 1)
    And (Integrable k mu)
      (integral mu k =
        (b + (m : Complex) / 2 * (s + 2) + (m0 : Complex) / s) / (s * (s + 1)) -
          (mNeg : Complex) / (s + 1) ^ (2 : Nat)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let a0 := b + (m : Complex) - (m0 : Complex)
  let a1 := (m0 : Complex) - b - (m : Complex) / 2
  let p0 := fun x : Real => (x : Complex) ^ (-s - 1)
  let p1 := fun x : Real => (x : Complex) ^ (-s - 1) * (x : Complex) ^ (-(1 : Complex))
  let l0 := fun x : Real => (x : Complex) ^ (-s - 1) * (Real.log x : Complex)
  let l1 := fun x : Real => (x : Complex) ^ (-s - 1) *
    ((x : Complex) ^ (-(1 : Complex)) * (Real.log x : Complex))
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hs1 : 1 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith only [hs0]
  have hP0 : And (Integrable p0 mu) (integral mu p0 = 1 / s) := by
    simpa only [p0, sub_zero, Complex.cpow_zero, mul_one] using
      (grandMonomial_mellin s 0 (by simpa only [Complex.zero_re] using hs0))
  have hP1 : And (Integrable p1 mu) (integral mu p1 = 1 / (s + 1)) := by
    simpa only [p1, sub_neg_eq_add] using
      (grandMonomial_mellin s (-1) (by rw [Complex.neg_re, Complex.one_re]; linarith only [hs]))
  have hL0 : And (Integrable l0 mu) (integral mu l0 = 1 / s ^ (2 : Nat)) := by
    simpa only [l0, sub_zero, Complex.cpow_zero, one_mul] using
      (grandLogMonomial_mellin s 0 (by simpa only [sub_zero] using hs))
  have hL1 : And (Integrable l1 mu) (integral mu l1 = 1 / (s + 1) ^ (2 : Nat)) := by
    simpa only [l1, sub_neg_eq_add] using
      (grandLogMonomial_mellin s (-1) (by simpa only [sub_neg_eq_add] using hs1))
  have hA0 := hP0.1.const_mul a0
  have hA1 := hP1.1.const_mul a1
  have hM0 := hL0.1.const_mul (m0 : Complex)
  have hMNeg := hL1.1.const_mul (mNeg : Complex)
  have hAdd : Integrable (fun x => a0 * p0 x + a1 * p1 x) mu := hA0.add hA1
  have hAdds : Integrable (fun x => a0 * p0 x + a1 * p1 x + (m0 : Complex) * l0 x) mu :=
    hAdd.add hM0
  have hEq : (fun x : Real => grandElementaryTerm b m m0 mNeg x * (x : Complex) ^ (-s - 1)) =
      fun x => a0 * p0 x + a1 * p1 x + (m0 : Complex) * l0 x - (mNeg : Complex) * l1 x := by
    funext x
    dsimp [grandElementaryTerm, a0, a1, p0, p1, l0, l1]
    ring
  dsimp only
  rw [hEq]
  refine And.intro (hAdds.sub hMNeg) ?_
  rw [integral_sub hAdds hMNeg, integral_add hAdd hM0,
    integral_add hA0 hA1, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, hP0.2, hP1.2, hL0.2, hL1.2]
  have hsne := Complex.ne_zero_of_re_pos hs0
  have hsone := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs1)
  dsimp [a0, a1]
  field_simp [hsne, hsone]
  ring


private theorem norm_grandElementaryTerm_le (b : Complex) (m m0 mNeg : Real)
    {x : Real} (hx : 1 < x) :
    norm (grandElementaryTerm b m m0 mNeg x) <=
      (norm (b + (m : Complex) - (m0 : Complex)) + norm ((m0 : Complex) - b - (m : Complex) / 2) +
        2 * norm (m0 : Complex) + 2 * norm (mNeg : Complex)) * Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hSqrt : 1 <= Real.sqrt x := Real.one_le_sqrt.mpr hx.le
  have hLog0 : 0 <= Real.log x := Real.log_nonneg hx.le
  have hLog : Real.log x <= 2 * Real.sqrt x := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    rw [Real.log_sqrt hx0.le] at h
    linarith only [h]
  have hInv : norm ((x : Complex) ^ (-(1 : Complex))) <= 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.neg_re, Complex.one_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  let a0 := b + (m : Complex) - (m0 : Complex)
  let a1 := (m0 : Complex) - b - (m : Complex) / 2
  let invX := (x : Complex) ^ (-(1 : Complex))
  let L := (Real.log x : Complex)
  have hL : norm L <= 2 * Real.sqrt x := by
    dsimp only [L]
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLog0]
  have hLInv : norm (invX * L) <= 2 * Real.sqrt x := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg L) hInv).trans hL
  change norm (a0 + a1 * invX + (m0 : Complex) * L - (mNeg : Complex) * (invX * L)) <=
    (norm a0 + norm a1 + 2 * norm (m0 : Complex) + 2 * norm (mNeg : Complex)) * Real.sqrt x
  calc
    _ <= norm a0 + norm (a1 * invX) + norm ((m0 : Complex) * L) +
        norm ((mNeg : Complex) * (invX * L)) := by
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ <= (norm a0 + norm a1 + 2 * norm (m0 : Complex) + 2 * norm (mNeg : Complex)) *
        Real.sqrt x := by
      have ha0 : norm a0 <= norm a0 * Real.sqrt x := le_mul_of_one_le_right (norm_nonneg _) hSqrt
      have ha1 : norm a1 * norm invX <= norm a1 * Real.sqrt x :=
        mul_le_mul_of_nonneg_left (hInv.trans hSqrt) (norm_nonneg _)
      have hm0 := mul_le_mul_of_nonneg_left hL (norm_nonneg (m0 : Complex))
      have hmNeg := mul_le_mul_of_nonneg_left hLInv (norm_nonneg (mNeg : Complex))
      rw [norm_mul a1, norm_mul (m0 : Complex), norm_mul (mNeg : Complex)]
      calc
        _ <= norm a0 * Real.sqrt x + norm a1 * Real.sqrt x +
            norm (m0 : Complex) * (2 * Real.sqrt x) +
            norm (mNeg : Complex) * (2 * Real.sqrt x) :=
          add_le_add (add_le_add (add_le_add ha0 ha1) hm0) hmNeg
        _ = _ := by ring

private theorem triangularRemainder_mellin_of_logDeriv {iota : Type*} [Countable iota]
    (a b : iota -> Real) (m : Real) (F : Complex -> Complex)
    (ha : forall i, 1 <= a i) (s : Complex) (hs : 1 < s.re)
    (hSum : Summable (fun i => norm (b i) * (a i) ^ (-s.re)))
    (hLogDeriv : logDeriv F s = (m : Complex) / (s - 1) -
      tsum (fun i => (b i : Complex) * (a i : Complex) ^ (-s))) :
    let mu := volume.restrict (Ioi (1 : Real))
    let k := fun x : Real => (triangularRemainder a b m x : Complex) * (x : Complex) ^ (-s - 1)
    And (Integrable k mu)
      (integral mu k =
        (logDeriv F s + (m : Complex) / 2 * (s + 2)) / (s * (s + 1))) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let k := fun x : Real => (triangularRemainder a b m x : Complex) * (x : Complex) ^ (-s - 1)
  have h := triangularComparison_mellin a b m 0 s hs ha hSum
  have he :
      (fun x : Real => ((0 * Real.sqrt x - triangularRemainder a b m x : Real) : Complex) *
        (x : Complex) ^ (-s - 1)) = fun x => -k x := by
    funext x
    simp only [k, zero_mul, zero_sub, Complex.ofReal_neg, neg_mul]
  rw [he] at h
  have hn : Integrable (fun x => -k x) mu := h.1
  have hnn : Integrable (fun x => -(-k x)) mu := hn.neg
  have hk : Integrable k mu := by simpa only [neg_neg] using hnn
  refine And.intro hk ?_
  have hIntegral := h.2
  rw [integral_neg] at hIntegral
  have hA : Not (s - 1 = 0) := Complex.ne_zero_of_re_pos (by rwa [Complex.sub_re, Complex.one_re, sub_pos])
  have hS : Not (s = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hB : Not (s + 1 = 0) := Complex.ne_zero_of_re_pos (by
    rw [Complex.add_re, Complex.one_re]
    linarith only [hs])
  change integral mu k = _
  rw [show integral mu k = -(-integral mu k) by rw [neg_neg], hIntegral, hLogDeriv]
  push_cast
  simp only [zero_div, zero_sub]
  field_simp [hA, hS, hB]
  ring

private theorem ae_eq_hadamard_expansion {zeros : Type*} [Countable zeros]
    (R : Real -> Complex) (m : Real) (F : Complex -> Complex) (rho : zeros -> Complex)
    (beta : Complex) (m0 mNeg : Real)
    (hTransform : forall s : Complex, 1 < s.re ->
      let mu := volume.restrict (Ioi (1 : Real))
      let k := fun x : Real => R x * (x : Complex) ^ (-s - 1)
      And (Integrable k mu)
        (integral mu k =
          (logDeriv F s + (m : Complex) / 2 * (s + 2)) / (s * (s + 1))))
    (hRho : forall i, (rho i).re <= 1 / 2)
    (hRho0 : forall i, Not (rho i = 0)) (hRho1 : forall i, Not (rho i + 1 = 0))
    (hRhoSum : Summable (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)))
    (hHadamard : forall s : Complex, 1 < s.re -> logDeriv F s =
      beta + (m0 : Complex) / s + (mNeg : Complex) * (1 / (s + 1) - 1) +
        tsum (fun i => 1 / (s - rho i) + 1 / rho i)) :
    Filter.EventuallyEq (ae (volume.restrict (Ioi (1 : Real))))
      R
      (fun x => grandElementaryTerm beta m m0 mNeg x +
        tsum (fun i => triangularZeroTerm (rho i) x)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let E := grandElementaryTerm beta m m0 mNeg
  let Z := fun x => tsum (fun i => triangularZeroTerm (rho i) x)
  let d := fun x => R x - (E x + Z x)
  let W (t x : Real) := (x : Complex) ^ (-((2 : Real) : Complex) - 1 + (t : Complex) * Complex.I)
  have hLine (t : Real) :
      And (Integrable (fun x => W t x * d x) mu) (integral mu (fun x => W t x * d x) = 0) := by
    let s : Complex := 2 - (t : Complex) * Complex.I
    have hs : 1 < s.re := by simp [s, Complex.sub_re, Complex.mul_re]
    have hR := hTransform s hs
    have hE := grandElementaryTerm_mellin beta m m0 mNeg s hs
    have hZ := triangularZeroSeries_mellin rho hRho hRho0 hRho1 hRhoSum s hs
    let fR := fun x : Real => R x * (x : Complex) ^ (-s - 1)
    let fE := fun x : Real => E x * (x : Complex) ^ (-s - 1)
    let fZ := fun x : Real => Z x * (x : Complex) ^ (-s - 1)
    have hEq : (fun x => W t x * d x) = fun x => fR x - (fE x + fZ x) := by
      funext x
      have he : -((2 : Real) : Complex) - 1 + (t : Complex) * Complex.I = -s - 1 := by
        dsimp [s]
        norm_num
        ring
      dsimp only [d, W, fR, fE, fZ]
      rw [he]
      ring
    have hEInt : Integrable fE mu := hE.1
    have hZInt : Integrable fZ mu := hZ.1
    have hRInt : Integrable fR mu := hR.1
    have hEZInt : Integrable (fun x => fE x + fZ x) mu := hEInt.add hZInt
    rw [hEq]
    refine And.intro (hRInt.sub hEZInt) ?_
    rw [integral_sub hRInt hEZInt, integral_add hEInt hZInt]
    change integral mu fR - (integral mu fE + integral mu fZ) = 0
    rw [hR.2, hE.2, hZ.2, hHadamard s hs]
    have hs0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
    have hs1 : Not (s + 1 = 0) := Complex.ne_zero_of_re_pos (by
      rw [Complex.add_re, Complex.one_re]
      linarith only [hs])
    field_simp [hs0, hs1]
    ring
  have hd : AEMeasurable d mu := by
    let g := fun x : Real => (x : Complex) ^ (3 : Nat) * (W 0 x * d x)
    have hg : AEMeasurable g mu :=
      (Complex.continuous_ofReal.pow (3 : Nat)).measurable.aemeasurable.mul
        (hLine 0).1.aemeasurable
    refine hg.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hne := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
    have hW : W 0 x = Inv.inv ((x : Complex) ^ (3 : Nat)) := by
      simp only [W, Complex.ofReal_zero, zero_mul, add_zero,
        show -((2 : Real) : Complex) - 1 = -((3 : Nat) : Complex) by norm_num,
        Complex.cpow_neg, Complex.cpow_natCast]
    change (x : Complex) ^ (3 : Nat) * (W 0 x * d x) = d x
    rw [hW, <- mul_assoc, <- div_eq_mul_inv, div_self (pow_ne_zero _ hne), one_mul]
  let d0 := hd.mk d
  have h0 : Filter.EventuallyEq (ae mu) d d0 := hd.ae_eq_mk
  have hRep (t : Real) :
      And (Integrable (fun x => W t x * d0 x) mu) (integral mu (fun x => W t x * d0 x) = 0) := by
    have ht := h0.mono (fun x hx => congrArg (fun z : Complex => W t x * z) hx)
    exact And.intro ((hLine t).1.congr ht) ((integral_congr_ae ht).symm.trans (hLine t).2)
  have hZero := ae_zero_of_complex_verticalMellin_eq_zero_at hd.measurable_mk 2 hRep
  filter_upwards [hZero, h0] with x hR hx
  have hh : d x = 0 := hx.trans hR
  exact sub_eq_zero.mp hh

/-- The full complex triangular expansion under a Hadamard logarithmic derivative. -/
theorem ae_triangularRemainder_eq_complex_expansion
    {iota zeros : Type*} [Countable iota] [Countable zeros]
    (a b : iota -> Real) (m : Real) (F : Complex -> Complex) (rho : zeros -> Complex)
    (beta : Complex) (m0 mNeg : Real)
    (ha : forall i, 1 <= a i)
    (hSum : forall r : Real, 1 < r -> Summable (fun i => norm (b i) * (a i) ^ (-r)))
    (hEuler : forall s : Complex, 1 < s.re ->
      logDeriv F s = (m : Complex) / (s - 1) -
        tsum (fun i => (b i : Complex) * (a i : Complex) ^ (-s)))
    (hRho : forall i, (rho i).re <= 1 / 2)
    (hRho0 : forall i, Not (rho i = 0)) (hRho1 : forall i, Not (rho i + 1 = 0))
    (hRhoSum : Summable (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)))
    (hHadamard : forall s : Complex, 1 < s.re -> logDeriv F s =
      beta + (m0 : Complex) / s + (mNeg : Complex) * (1 / (s + 1) - 1) +
        tsum (fun i => 1 / (s - rho i) + 1 / rho i)) :
    Filter.EventuallyEq (ae (volume.restrict (Ioi (1 : Real))))
      (fun x => (triangularRemainder a b m x : Complex))
      (fun x => grandElementaryTerm beta m m0 mNeg x +
        tsum (fun i => triangularZeroTerm (rho i) x)) := by
  apply ae_eq_hadamard_expansion (fun x => (triangularRemainder a b m x : Complex)) m F
    rho beta m0 mNeg ?_
    hRho hRho0 hRho1 hRhoSum hHadamard
  intro s hs
  exact triangularRemainder_mellin_of_logDeriv a b m F ha s hs (hSum s.re hs) (hEuler s hs)

/-- The Hadamard expansion of a signed prime-power remainder with complex coefficients. -/
theorem ae_complexTriangularRemainder_eq_expansion
    {iota zeros : Type*} [Countable iota] [Countable zeros]
    (a : iota -> Real) (b : iota -> Complex) (m : Real) (F : Complex -> Complex) (rho : zeros -> Complex)
    (beta : Complex) (m0 mNeg : Real)
    (ha : forall i, 1 <= a i)
    (hSum : forall r : Real, 1 < r -> Summable (fun i => norm (b i) * (a i) ^ (-r)))
    (hEuler : forall s : Complex, 1 < s.re ->
      logDeriv F s = (m : Complex) / (s - 1) -
        tsum (fun i => b i * (a i : Complex) ^ (-s)))
    (hRho : forall i, (rho i).re <= 1 / 2)
    (hRho0 : forall i, Not (rho i = 0)) (hRho1 : forall i, Not (rho i + 1 = 0))
    (hRhoSum : Summable (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)))
    (hHadamard : forall s : Complex, 1 < s.re -> logDeriv F s =
      beta + (m0 : Complex) / s + (mNeg : Complex) * (1 / (s + 1) - 1) +
        tsum (fun i => 1 / (s - rho i) + 1 / rho i)) :
    Filter.EventuallyEq (ae (volume.restrict (Ioi (1 : Real))))
      (complexTriangularRemainder a b m)
      (fun x => grandElementaryTerm beta m m0 mNeg x +
        tsum (fun i => triangularZeroTerm (rho i) x)) := by
  apply ae_eq_hadamard_expansion (complexTriangularRemainder a b m) m F
    rho beta m0 mNeg ?_
    hRho hRho0 hRho1 hRhoSum hHadamard
  intro s hs
  exact complexTriangularRemainder_mellin_of_logDeriv a b m F ha s hs
    (hSum s.re hs) (hEuler s hs)

/-- The elementary remainder is continuous on the open positive tail. -/
theorem continuousOn_grandElementaryTerm (beta : Complex) (m m0 mNeg : Real) :
    ContinuousOn (grandElementaryTerm beta m m0 mNeg) (Ioi (1 : Real)) := by
  have hi : ContinuousOn (fun x : Real => (x : Complex) ^ (-(1 : Complex)))
      (Ioi (1 : Real)) := by
    simp only [Complex.cpow_neg, Complex.cpow_one, <- one_div]
    exact continuousOn_const.div Complex.continuous_ofReal.continuousOn
      (fun x hx => Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne')
  have hl : ContinuousOn (fun x : Real => (Real.log x : Complex)) (Ioi (1 : Real)) := by
    intro x hx
    exact (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_log (zero_lt_one.trans hx).ne')).continuousWithinAt
  unfold grandElementaryTerm
  exact (((continuousOn_const.add (continuousOn_const.mul hi)).add
    (continuousOn_const.mul hl)).sub (continuousOn_const.mul (hi.mul hl)))

/-- The elementary Hadamard remainder disappears under the square-root
normalization on logarithmic time. -/
theorem tendsto_logScaled_grandElementaryTerm (beta : Complex) (m m0 mNeg : Real) :
    Tendsto (fun t : Real => (Real.exp (-t / 2) : Complex) *
      grandElementaryTerm beta m m0 mNeg (Real.exp t)) atTop (nhds 0) := by
  let X (t : Real) : Complex := (Real.exp (-t / 2) : Complex)
  let Y (t : Real) : Complex := (Real.exp (-t) : Complex)
  let Z (t : Real) : Complex := (t : Complex) * X t
  have hXR : Tendsto (fun t : Real => Real.exp (-t / 2)) atTop (nhds 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show (-(1 / 2) : Real) < 0 by norm_num))
    convert h using 1
    funext t
    change Real.exp (-t / 2) = Real.exp (-(1 / 2) * t)
    congr 1
    ring
  have hYR : Tendsto (fun t : Real => Real.exp (-t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hZR : Tendsto (fun t : Real => t * Real.exp (-t / 2)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num)
    convert h using 1
    funext t
    rw [Real.rpow_one]
    congr 2
    ring
  have hX : Tendsto X atTop (nhds 0) := by
    simpa only [X, Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hXR
  have hY : Tendsto Y atTop (nhds 0) := by
    simpa only [Y, Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hYR
  have hZ : Tendsto Z atTop (nhds 0) := by
    simpa only [Z, X, Function.comp_def, Complex.ofReal_mul, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hZR
  have hSum := (((hX.mul_const (beta + m - m0)).add
    ((hX.mul hY).mul_const ((m0 : Complex) - beta - (m : Complex) / 2))).add
    (hZ.mul_const (m0 : Complex))).sub ((hZ.mul hY).mul_const (mNeg : Complex))
  simp only [zero_mul, add_zero, sub_zero] at hSum
  refine hSum.congr' (Filter.Eventually.of_forall (fun t => ?_))
  have hInv : (Real.exp t : Complex) ^ (-(1 : Complex)) = Y t := by
    simp only [Y, Complex.cpow_neg, Complex.cpow_one, <- Complex.ofReal_inv, <- Real.exp_neg]
  simp only [grandElementaryTerm, Real.log_exp, hInv]
  change _ = X t * ((beta + m - m0) +
    ((m0 : Complex) - beta - (m : Complex) / 2) * Y t + (m0 : Complex) * (t : Complex) -
    (mNeg : Complex) * (Y t * (t : Complex)))
  unfold Z
  ring

private theorem ae_triangularRemainder_eq_re_expansion
    {iota zeros : Type*} [Countable iota] [Countable zeros]
    (a b : iota -> Real) (m : Real) (F : Complex -> Complex) (rho : zeros -> Complex)
    (beta : Complex) (m0 mNeg : Real)
    (ha : forall i, 1 <= a i)
    (hSum : forall r : Real, 1 < r -> Summable (fun i => norm (b i) * (a i) ^ (-r)))
    (hEuler : forall s : Complex, 1 < s.re ->
      logDeriv F s = (m : Complex) / (s - 1) -
        tsum (fun i => (b i : Complex) * (a i : Complex) ^ (-s)))
    (hRho : forall i, (rho i).re <= 1 / 2)
    (hRho0 : forall i, Not (rho i = 0)) (hRho1 : forall i, Not (rho i + 1 = 0))
    (hRhoSum : Summable (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)))
    (hHadamard : forall s : Complex, 1 < s.re -> logDeriv F s =
      beta + (m0 : Complex) / s + (mNeg : Complex) * (1 / (s + 1) - 1) +
        tsum (fun i => 1 / (s - rho i) + 1 / rho i)) :
    Filter.EventuallyEq (ae (volume.restrict (Ioi (1 : Real))))
      (triangularRemainder a b m)
      (fun x => (grandElementaryTerm beta m m0 mNeg x +
        tsum (fun i => triangularZeroTerm (rho i) x)).re) := by
  filter_upwards [ae_triangularRemainder_eq_complex_expansion a b m F rho beta m0 mNeg
    ha hSum hEuler hRho hRho0 hRho1 hRhoSum hHadamard] with x hx
  exact congrArg Complex.re hx

/-- A Hadamard log-derivative expansion supported in the closed left half
of the critical line bounds the signed triangular prime-power remainder. -/
theorem triangularSquareRootBound_of_hadamard
    {iota zeros : Type*} [Countable iota] [Countable zeros]
    (a b : iota -> Real) (m : Real) (F : Complex -> Complex) (rho : zeros -> Complex)
    (beta : Complex) (m0 mNeg : Real)
    (ha : forall i, 1 <= a i)
    (hSum : forall r : Real, 1 < r -> Summable (fun i => norm (b i) * (a i) ^ (-r)))
    (hEuler : forall s : Complex, 1 < s.re ->
      logDeriv F s = (m : Complex) / (s - 1) -
        tsum (fun i => (b i : Complex) * (a i : Complex) ^ (-s)))
    (hRho : forall i, (rho i).re <= 1 / 2)
    (hRho0 : forall i, Not (rho i = 0)) (hRho1 : forall i, Not (rho i + 1 = 0))
    (hRhoSum : Summable (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)))
    (hHadamard : forall s : Complex, 1 < s.re -> logDeriv F s =
      beta + (m0 : Complex) / s + (mNeg : Complex) * (1 / (s + 1) - 1) +
        tsum (fun i => 1 / (s - rho i) + 1 / rho i))
    (hCont : ContinuousOn (triangularRemainder a b m) (Ioi (1 : Real))) :
    exists C : Real, forall x : Real, 1 < x -> triangularRemainder a b m x <= C * Real.sqrt x := by
  let A := norm (beta + (m : Complex) - (m0 : Complex)) +
    norm ((m0 : Complex) - beta - (m : Complex) / 2) +
    2 * norm (m0 : Complex) + 2 * norm (mNeg : Complex)
  let B := tsum (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int))
  refine Exists.intro (A + 2 * B) (fun x hx => pointwise_sqrtBound_of_ae hCont ?_ hx)
  have hModel := ae_triangularRemainder_eq_re_expansion a b m F rho beta m0 mNeg
    ha hSum hEuler hRho hRho0 hRho1 hRhoSum hHadamard
  filter_upwards [hModel, ae_restrict_mem measurableSet_Ioi] with y hy hyTail
  have hE := norm_grandElementaryTerm_le beta m m0 mNeg hyTail
  have hZ := norm_tsum_triangularZeroTerm_le rho hRho hRhoSum hyTail.le
  rw [hy]
  calc
    _ <= norm (grandElementaryTerm beta m m0 mNeg y +
        tsum (fun i => triangularZeroTerm (rho i) y)) := Complex.re_le_norm _
    _ <= norm (grandElementaryTerm beta m m0 mNeg y) +
        norm (tsum (fun i => triangularZeroTerm (rho i) y)) := norm_add_le _ _
    _ <= A * Real.sqrt y + 2 * Real.sqrt y * B := add_le_add hE hZ
    _ = (A + 2 * B) * Real.sqrt y := by ring

/-! ## Canonical data from entire order at most one -/

/-- Nonzero complex zeros with their divisor multiplicities. -/
abbrev entireNonzeroZeroIndex (F : Complex -> Complex) :=
  Subtype (fun i : divisorZeroIndex F (univ : Set Complex) => Not (i.1 = 0))

/-- The zero corresponding to a nonzero divisor index. -/
def entireNonzeroZero {F : Complex -> Complex} (i : entireNonzeroZeroIndex F) : Complex :=
  i.val.1

/-- Each divisor index gives an actual zero. -/
theorem entireNonzeroZero_is_zero {F : Complex -> Complex} (hF : Differentiable Complex F)
    (i : entireNonzeroZeroIndex F) : F (entireNonzeroZero i) = 0 := by
  by_contra h
  let z := entireNonzeroZero i
  have ha : AnalyticOnNhd Complex F univ := fun s _ => hF.analyticAt s
  have ho : analyticOrderAt F z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr h)
  have hd : MeromorphicOn.divisor F univ z = 0 := by
    rw [MeromorphicOn.divisor_apply ha.meromorphicOn (mem_univ z),
      (ha z (mem_univ z)).meromorphicOrderAt_eq, ho]
    simp
  have hi : Fin (Int.toNat (MeromorphicOn.divisor F univ z)) := i.val.2
  rw [hd, Int.toNat_zero] at hi
  exact Fin.elim0 hi

/-- Every nonzero entire function of order at most one has summable
reciprocal-square zero norms, with multiplicities. -/
theorem summable_entireNonzeroZero_inv_sq {F : Complex -> Complex}
    (hOrder : EntireOfOrderAtMost 1 F) (hNontrivial : exists z, Not (F z = 0)) :
    Summable (fun i : entireNonzeroZeroIndex F =>
      (Inv.inv (norm (entireNonzeroZero i))) ^ (2 : Nat)) := by
  run_tac do
    let provider := Lean.mkIdent (Lean.Name.str `Complex.Hadamard.EntireOfOrderAtMost
      ("summable_norm_inv_pow_divisorZeroIndex".push (Char.ofNat 8320)))
    let hOrder := Lean.mkIdent `hOrder
    let hNontrivial := Lean.mkIdent `hNontrivial
    let hProvider := Lean.mkIdent `hProvider
    Lean.Elab.Tactic.evalTactic
      ( <- `(tactic| have $hProvider := $provider $hOrder zero_le_one $hNontrivial))
  rw [Nat.floor_one] at hProvider
  exact hProvider

/-- The genus-one logarithmic derivative of an entire function of order
at most one, including the multiplicity at the origin. -/
theorem entireOfOrderAtMost_one_logDeriv {F : Complex -> Complex}
    (hOrder : EntireOfOrderAtMost 1 F) (hNontrivial : exists z, Not (F z = 0)) :
    exists beta : Complex, forall s : Complex, Not (s = 0) -> Not (F s = 0) ->
      logDeriv F s = beta + (analyticOrderNatAt F 0 : Complex) / s +
        tsum (fun i : entireNonzeroZeroIndex F =>
          1 / (s - entireNonzeroZero i) + 1 / entireNonzeroZero i) := by
  choose P hp using hadamard_factorization_of_order zero_le_one hNontrivial hOrder
  have hD : P.natDegree <= 1 := Polynomial.natDegree_le_iff_degree_le.mpr
    (by simpa only [Nat.floor_one, Nat.cast_one] using hp.1)
  have hC : P.derivative = Polynomial.C (P.coeff 1) := by
    apply Polynomial.ext
    intro n
    cases n with
    | zero => simp [Polynomial.coeff_derivative]
    | succ n =>
      have hN : P.natDegree < n + 1 + 1 := hD.trans_lt (by omega)
      have h0 : P.coeff (n + 1 + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hN
      simp [Polynomial.coeff_derivative, h0]
  refine Exists.intro (P.coeff 1) ?_
  intro s hs hFs
  let G := divisorCanonicalProduct 1 F (univ : Set Complex)
  let E := fun z : Complex => Complex.exp (P.eval z)
  let N := fun z : Complex => z ^ analyticOrderNatAt F 0
  have hFunctions : F = fun z => (E z * N z) * G z := by
    funext z
    simpa only [E, N, G, Nat.floor_one] using hp.2 z
  have hAway (i : entireNonzeroZeroIndex F) : Not (s = entireNonzeroZero i) := by
    intro he
    apply hFs
    rw [he]
    exact entireNonzeroZero_is_zero hOrder.differentiable i
  have hSum := summable_entireNonzeroZero_inv_sq hOrder hNontrivial
  have hExp : HasDerivAt E (Complex.exp (P.eval s) * P.derivative.eval s) s :=
    (Complex.hasDerivAt_exp (P.eval s)).comp s (P.hasDerivAt s)
  have hExpLog : logDeriv E s = P.derivative.eval s := by
    rw [logDeriv_apply, hExp.deriv]
    dsimp only [E]
    field_simp [Complex.exp_ne_zero]
  have hG : Not (G s = 0) := divisorCanonicalProduct_ne_zero_of_forall_ne 1 F hSum hAway
  have hGD : DifferentiableAt Complex G s := differentiableAt_divisorCanonicalProduct_univ 1 F hSum s
  have hN : Not (N s = 0) := pow_ne_zero _ hs
  have hND : DifferentiableAt Complex N s := differentiableAt_id.pow _
  have hE : Not (E s = 0) := Complex.exp_ne_zero _
  have hEN : Not (E s * N s = 0) := mul_ne_zero hE hN
  have hEND : DifferentiableAt Complex (fun z => E z * N z) s := hExp.differentiableAt.mul hND
  have hGL : logDeriv G s = tsum (fun i : entireNonzeroZeroIndex F =>
      1 / (s - entireNonzeroZero i) + 1 / entireNonzeroZero i) :=
    logDeriv_divisorCanonicalProduct_one_eq_tsum hSum hAway hG
  calc
    logDeriv F s = logDeriv (fun z => (E z * N z) * G z) s :=
      congrArg (fun f : Complex -> Complex => logDeriv f s) hFunctions
    _ = _ := by
      rw [logDeriv_mul s hEN hG hEND hGD,
        logDeriv_mul s hE hN hExp.differentiableAt hND, hExpLog, hC, Polynomial.eval_C, hGL]
      rw [show logDeriv N s = (analyticOrderNatAt F 0 : Complex) / s from logDeriv_pow s _]

/-- Nonzero divisor indices with the exceptional point minus one removed. -/
abbrev regularHadamardZeroIndex (F : Complex -> Complex) :=
  Subtype (fun i : entireNonzeroZeroIndex F => Not (entireNonzeroZero i + 1 = 0))

/-- The indexed zero at a regular index. -/
def regularHadamardZero {F : Complex -> Complex} (i : regularHadamardZeroIndex F) : Complex :=
  entireNonzeroZero i.val

private theorem finite_boundedEntireNonzeroZeroIndex (F : Complex -> Complex) :
    Finite {i : entireNonzeroZeroIndex F // norm (entireNonzeroZero i) <= 2} := by
  have hBall : Metric.closedBall (0 : Complex) (2 : Real) <= (univ : Set Complex) :=
    subset_univ _
  run_tac do
    let p := Lean.mkIdent (Lean.Name.str `Complex.Hadamard
      (("finite_divisorZeroIndex".push (Char.ofNat 8320)) ++ "_subtype_norm_le"))
    let f := Lean.mkIdent `F
    let h := Lean.mkIdent `hBall
    Lean.Elab.Tactic.evalTactic (<- `(tactic| exact $p (f := $f) (B := (2 : Real)) $h))

/-- The zero weights of the triangular kernel are summable for an entire
function of order at most one. -/
theorem summable_regularHadamardZeroWeight {F : Complex -> Complex}
    (hOrder : EntireOfOrderAtMost 1 F) (hNontrivial : exists z, Not (F z = 0)) :
    Summable (fun i : regularHadamardZeroIndex F =>
      (norm (regularHadamardZero i * (regularHadamardZero i + 1))) ^ (-1 : Int)) := by
  let S : Set (regularHadamardZeroIndex F) := {i | norm (regularHadamardZero i) <= 2}
  let w := fun i : regularHadamardZeroIndex F =>
    (norm (regularHadamardZero i * (regularHadamardZero i + 1))) ^ (-1 : Int)
  let v := fun i : regularHadamardZeroIndex F =>
    (Inv.inv (norm (regularHadamardZero i))) ^ (2 : Nat)
  have : Finite {i : entireNonzeroZeroIndex F // norm (entireNonzeroZero i) <= 2} :=
    finite_boundedEntireNonzeroZeroIndex F
  have : Finite S := by
    apply Finite.of_injective
      (fun i : S => (Subtype.mk i.val.val i.property :
        {j : entireNonzeroZeroIndex F // norm (entireNonzeroZero j) <= 2}))
    intro i j hij
    have hVal : i.val.val = j.val.val := congrArg
      (fun t : {k : entireNonzeroZeroIndex F // norm (entireNonzeroZero k) <= 2} => t.val) hij
    exact Subtype.ext (Subtype.ext hVal)
  have hv : Summable v :=
    (summable_entireNonzeroZero_inv_sq hOrder hNontrivial).subtype _
  apply (summable_subtype_and_compl (f := w) (s := S)).mp
  refine And.intro (Set.Finite.summable (toFinite S) w) ?_
  refine Summable.of_nonneg_of_le (g := fun i : (S : Set (regularHadamardZeroIndex F)).compl => w i.val)
    (f := fun i : S.compl => 2 * v i.val) (fun i => by dsimp [w]; positivity) ?_
    ((hv.subtype (fun i => Membership.mem S.compl i)).mul_left 2)
  intro i
  let z := regularHadamardZero i.val
  have hz2 : 2 < norm z := lt_of_not_ge i.property
  have hz0 : 0 < norm z := (by norm_num : (0 : Real) < 2).trans hz2
  have hshift : norm z <= norm (z + 1) + 1 := by
    simpa only [add_sub_cancel_right, norm_one] using norm_sub_le (z + 1) (1 : Complex)
  have hhalf : norm z / 2 <= norm (z + 1) := by linarith only [hz2, hshift]
  have hproduct : norm z ^ (2 : Nat) / 2 <= norm (z * (z + 1)) := by
    rw [norm_mul]
    nlinarith only [mul_le_mul_of_nonneg_left hhalf hz0.le]
  have hpos : 0 < norm z ^ (2 : Nat) / 2 := by positivity
  have hrecip := one_div_le_one_div_of_le hpos hproduct
  change (norm (z * (z + 1))) ^ (-1 : Int) <= 2 * (Inv.inv (norm z)) ^ (2 : Nat)
  rw [zpow_neg_one, <- one_div]
  exact hrecip.trans_eq (by
    field_simp [hz0.ne'])

/-- The zeros counted with multiplicity form a countable index type. -/
theorem countable_entireNonzeroZeroIndex {F : Complex -> Complex}
    (hOrder : EntireOfOrderAtMost 1 F) (hNontrivial : exists z, Not (F z = 0)) :
    Countable (entireNonzeroZeroIndex F) := by
  let v (i : entireNonzeroZeroIndex F) : NNReal :=
    Real.toNNReal ((Inv.inv (norm (entireNonzeroZero i))) ^ (2 : Nat))
  have hv : Summable v := by
    apply NNReal.summable_coe.mp
    refine (summable_entireNonzeroZero_inv_sq hOrder hNontrivial).congr ?_
    intro i
    exact (Real.coe_toNNReal _ (sq_nonneg _)).symm
  have hs : Function.support v = univ := by
    refine Set.eq_univ_of_forall ?_
    intro i
    have hn : 0 < norm (entireNonzeroZero i) := norm_pos_iff.mpr i.property
    have hp : 0 < (Inv.inv (norm (entireNonzeroZero i))) ^ (2 : Nat) := by positivity
    exact ne_of_gt (Real.toNNReal_pos.mpr hp)
  have h := Summable.countable_support_nnreal v hv
  rw [hs] at h
  exact Set.countable_univ_iff.mp h

/-- The genus-one expansion splits off the zero at minus one in addition
to the origin. Both terms use their divisor multiplicities. -/
theorem entireOfOrderAtMost_one_logDeriv_regular {F : Complex -> Complex}
    (hOrder : EntireOfOrderAtMost 1 F) (hNontrivial : exists z, Not (F z = 0)) :
    exists (beta : Complex) (m0 mNeg : Nat),
      forall s : Complex, Not (s = 0) -> Not (F s = 0) ->
        logDeriv F s = beta + (m0 : Complex) / s +
          (mNeg : Complex) * (1 / (s + 1) - 1) +
          tsum (fun i : regularHadamardZeroIndex F =>
            1 / (s - regularHadamardZero i) + 1 / regularHadamardZero i) := by
  let A : Set (entireNonzeroZeroIndex F) := {i | entireNonzeroZero i + 1 = 0}
  have hx (i : A) : entireNonzeroZero i.val = -1 := by
    have hei : entireNonzeroZero i.val + 1 = 0 := i.property
    calc
      _ = entireNonzeroZero i.val + 1 - 1 := (add_sub_cancel_right _ _).symm
      _ = -1 := by rw [hei, zero_sub]
  have : Finite {i : entireNonzeroZeroIndex F // norm (entireNonzeroZero i) <= 2} :=
    finite_boundedEntireNonzeroZeroIndex F
  have : Finite A := by
    refine Finite.of_injective (fun i : A => (Subtype.mk i.val (by
      rw [hx i, norm_neg, norm_one]
      norm_num) : {j : entireNonzeroZeroIndex F // norm (entireNonzeroZero j) <= 2})) ?_
    intro i j hij
    have hv : i.val = j.val := congrArg
      (fun t : {k : entireNonzeroZeroIndex F // norm (entireNonzeroZero k) <= 2} => t.val) hij
    exact Subtype.ext hv
  choose beta hBeta using entireOfOrderAtMost_one_logDeriv hOrder hNontrivial
  refine Exists.intro beta (Exists.intro (analyticOrderNatAt F 0)
    (Exists.intro (Nat.card A) ?_))
  intro s hs hf
  let f := fun i : entireNonzeroZeroIndex F =>
    1 / (s - entireNonzeroZero i) + 1 / entireNonzeroZero i
  have hAway (i : entireNonzeroZeroIndex F) : Not (s = entireNonzeroZero i) := by
    intro he
    apply hf
    rw [he]
    exact entireNonzeroZero_is_zero hOrder.differentiable i
  have hSqSum := summable_entireNonzeroZero_inv_sq hOrder hNontrivial
  have hSum : Summable f := by
    run_tac do
      let p := Lean.mkIdent (Lean.Name.str `Complex.Hadamard
        (("summable_logDerivTerms_divisorZeroIndex".push (Char.ofNat 8320)) ++
          "_of_summable_inv_sq"))
      let hh := Lean.mkIdent `hSqSum
      let ha := Lean.mkIdent `hAway
      Lean.Elab.Tactic.evalTactic (<- `(tactic| exact $p $hh $ha))
  have hA : tsum (fun i : A => f i.val) = (Nat.card A : Complex) * (1 / (s + 1) - 1) := by
    calc
      _ = tsum (fun _ : A => 1 / (s + 1) - 1) := by
        apply tsum_congr
        intro i
        dsimp only [f]
        rw [hx i, sub_neg_eq_add]
        norm_num [sub_eq_add_neg]
      _ = _ := by rw [tsum_const, nsmul_eq_mul]
  calc
    logDeriv F s = beta + (analyticOrderNatAt F 0 : Complex) / s + tsum f := hBeta s hs hf
    _ = beta + (analyticOrderNatAt F 0 : Complex) / s +
          (tsum (fun i : A => f i.val) + tsum (fun i : regularHadamardZeroIndex F => f i.val)) :=
      congrArg (fun z : Complex => beta + (analyticOrderNatAt F 0 : Complex) / s + z)
        (hSum.tsum_subtype_add_tsum_subtype_compl A).symm
    _ = _ := by rw [hA, <- add_assoc]; rfl

end Robin1984.GRH
