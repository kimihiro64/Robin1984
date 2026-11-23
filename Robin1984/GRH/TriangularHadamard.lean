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

open Filter MeasureTheory Set

set_option autoImplicit false

namespace Robin1984.GRH

private noncomputable def grandElementaryTerm (b : Complex) (m m0 mNeg : Real)
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
  let mu := volume.restrict (Ioi (1 : Real))
  let E := grandElementaryTerm beta m m0 mNeg
  let Z := fun x => tsum (fun i => triangularZeroTerm (rho i) x)
  let R := triangularRemainder a b m
  let d := fun x => (R x : Complex) - (E x + Z x)
  let W (t x : Real) := (x : Complex) ^ (-((2 : Real) : Complex) - 1 + (t : Complex) * Complex.I)
  have hLine (t : Real) :
      And (Integrable (fun x => W t x * d x) mu) (integral mu (fun x => W t x * d x) = 0) := by
    let s : Complex := 2 - (t : Complex) * Complex.I
    have hs : 1 < s.re := by simp [s, Complex.sub_re, Complex.mul_re]
    have hR := triangularRemainder_mellin_of_logDeriv a b m F ha s hs
      (hSum s.re hs) (hEuler s hs)
    have hE := grandElementaryTerm_mellin beta m m0 mNeg s hs
    have hZ := triangularZeroSeries_mellin rho hRho hRho0 hRho1 hRhoSum s hs
    let fR := fun x : Real => (R x : Complex) * (x : Complex) ^ (-s - 1)
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
  have hRe := ae_zero_re_of_verticalMellin_eq_zero_at hd.measurable_mk 2 hRep
  filter_upwards [hRe, h0] with x hR hx
  change (d0 x).re = 0 at hR
  rw [<- hx, show (d x).re = R x - (E x + Z x).re by simp only [d, Complex.sub_re, Complex.ofReal_re]]
    at hR
  exact sub_eq_zero.mp hR

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

end Robin1984.GRH
