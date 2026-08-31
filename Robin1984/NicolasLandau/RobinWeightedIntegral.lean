import Robin1984.NicolasLandau.XiZeroConstant

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# Robin's weighted Chebyshev integral

This module formalizes the zero kernel used in Lemmas 1 and 2 of Robin 1984.
The exponent is initially allowed to be complex; the critical-line estimate is
then summable over the multiplicity-carrying xi divisor index.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators

/-- The complex zero kernel in Robin 1984, Lemma 1. -/
def robinZeroKernel (n : Nat) (rho : Complex) (x : Real) : Complex :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    (t : Complex) ^ (rho - (n : Complex) - 1) *
      (((n : Real) * Real.log t + 1) /
        (Real.log t) ^ (2 : Nat) : Real))

/-- A negative complex power remains integrable after division by a fixed
positive power of `log` on a tail beginning above one. -/
theorem integrableOn_cpow_div_log_pow
    {a : Complex} {x : Real} (hx : 1 < x) (ha : a.re < -1)
    (k : Nat) :
    IntegrableOn (fun t : Real =>
      (t : Complex) ^ a *
        (((Inv.inv ((Real.log t) ^ k) : Real) : Complex))) (Ioi x) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hBase :
      IntegrableOn (fun t : Real => (t : Complex) ^ a) (Ioi x) :=
    integrableOn_Ioi_cpow_of_lt ha hxPos
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  apply hBase.mul_bdd (c := Inv.inv ((Real.log x) ^ k))
  . have hMeasReal :
        Measurable (fun t : Real => Inv.inv ((Real.log t) ^ k)) :=
      (Measurable.pow_const Real.measurable_log k).inv
    exact
      (Complex.continuous_ofReal.measurable.comp hMeasReal).aestronglyMeasurable
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hxt : x <= t := ht.le
    have hLog : Real.log x <= Real.log t := Real.log_le_log hxPos hxt
    have hLogTPos : 0 < Real.log t := lt_of_lt_of_le hLogPos hLog
    have hPow : (Real.log x) ^ k <= (Real.log t) ^ k := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, pow_succ]
          exact mul_le_mul ih hLog hLogPos.le
            (pow_nonneg hLogTPos.le k)
    have hPowPos : 0 < (Real.log t) ^ k := pow_pos hLogTPos k
    have hPowXPos : 0 < (Real.log x) ^ k := pow_pos hLogPos k
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hPowPos)]
    simpa [one_div] using one_div_le_one_div_of_le hPowXPos hPow

/-- The logarithmically weighted complex-power tail. -/
def robinCpowLogTail (a : Complex) (k : Nat) (x : Real) : Complex :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    (t : Complex) ^ (a - 1) *
      (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)))

/-- The twice-integrated remainder in Robin 1984, Lemma 1. -/
def robinZeroKernelRemainder
    (n : Nat) (rho : Complex) (x : Real) : Complex :=
  rho / (rho - (n : Complex)) ^ (2 : Nat) *
    (-((x : Complex) ^ (rho - (n : Complex))) /
        ((Real.log x : Real) : Complex) ^ (2 : Nat) +
      2 * robinCpowLogTail (rho - (n : Complex)) 3 x)

/-- Dividing Robin's remainder by the zero removes its numerator exactly. -/
theorem robinZeroKernelRemainder_div_rho
    {n : Nat} {rho : Complex} {x : Real} (hRho : Not (rho = 0)) :
    robinZeroKernelRemainder n rho x / rho =
      Inv.inv ((rho - (n : Complex)) ^ (2 : Nat)) *
        (-((x : Complex) ^ (rho - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat) +
          2 * robinCpowLogTail (rho - (n : Complex)) 3 x) := by
  unfold robinZeroKernelRemainder
  simp only [div_eq_mul_inv]
  calc
    rho * Inv.inv ((rho - (n : Complex)) ^ (2 : Nat)) *
          (-((x : Complex) ^ (rho - (n : Complex))) *
              Inv.inv (((Real.log x : Real) : Complex) ^ (2 : Nat)) +
            2 * robinCpowLogTail (rho - (n : Complex)) 3 x) *
        Inv.inv rho =
        (rho * Inv.inv rho) *
          (Inv.inv ((rho - (n : Complex)) ^ (2 : Nat)) *
            (-((x : Complex) ^ (rho - (n : Complex))) *
                Inv.inv (((Real.log x : Real) : Complex) ^ (2 : Nat)) +
              2 * robinCpowLogTail (rho - (n : Complex)) 3 x)) := by
      ring
    _ = _ := by
      simp [hRho]

/-- On the critical line, translating a zero left by a positive integer does
not decrease its norm. -/
theorem norm_le_norm_sub_nat_of_re_eq_half
    {n : Nat} (hn : 1 <= n) {rho : Complex}
    (hRe : rho.re = (1 / 2 : Real)) :
    norm rho <= norm (rho - (n : Complex)) := by
  apply le_of_sq_le_sq
  case h =>
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.natCast_re, Complex.natCast_im, sub_zero, hRe]
    have hnReal : (1 : Real) <= (n : Real) := by
      exact_mod_cast hn
    nlinarith
  case hb => exact norm_nonneg _

/-- The leading critical-line coefficient has the same inverse-square zero
majorant as the remainder. -/
theorem norm_nat_div_sub_div_le_robinXiZeroWeight
    {n : Nat} (hn : 1 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re = (1 / 2 : Real)) :
    norm (((n : Complex) / ((n : Complex) - rho)) / rho) <=
      (n : Real) * (Inv.inv (norm rho)) ^ (2 : Nat) := by
  have hNormLe : norm rho <= norm (rho - (n : Complex)) :=
    norm_le_norm_sub_nat_of_re_eq_half hn hRe
  have hOppNorm :
      norm ((n : Complex) - rho) = norm (rho - (n : Complex)) := by
    rw [show (n : Complex) - rho = -(rho - (n : Complex)) by ring,
      norm_neg]
  have hNormPos : 0 < norm rho := norm_pos_iff.mpr hRho
  have hInvLe :
      Inv.inv (norm ((n : Complex) - rho)) <= Inv.inv (norm rho) := by
    rw [hOppNorm]
    simpa [one_div] using one_div_le_one_div_of_le hNormPos hNormLe
  rw [norm_div, norm_div, Complex.norm_natCast]
  calc
    (n : Real) / norm ((n : Complex) - rho) / norm rho =
        (n : Real) * Inv.inv (norm ((n : Complex) - rho)) *
          Inv.inv (norm rho) := by ring
    _ <= (n : Real) * Inv.inv (norm rho) * Inv.inv (norm rho) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hInvLe (Nat.cast_nonneg n))
        (inv_nonneg.mpr (norm_nonneg rho))
    _ = (n : Real) * (Inv.inv (norm rho)) ^ (2 : Nat) := by
      ring

/-- A primitive used in the integration-by-parts recurrence for
`robinCpowLogTail`. -/
def robinCpowLogPrimitive (a : Complex) (k : Nat) (t : Real) : Complex :=
  Inv.inv a * (t : Complex) ^ a *
    (((Inv.inv ((Real.log t) ^ k) : Real) : Complex))

theorem hasDerivAt_robinCpowLogPrimitive
    {a : Complex} (ha : Not (a = 0)) (k : Nat)
    {t : Real} (ht : 1 < t) :
    HasDerivAt (robinCpowLogPrimitive a k)
      ((t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)) -
        ((k : Complex) * Inv.inv a) *
          (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex))) t := by
  have htZero : Not (t = 0) := ne_of_gt (lt_trans Real.zero_lt_one ht)
  have htOne : Not (t = 1) := ne_of_gt ht
  have hLogZero : Not (Real.log t = 0) :=
    Real.log_ne_zero_of_pos_of_ne_one
      (lt_trans Real.zero_lt_one ht) htOne
  have hPower := hasDerivAt_ofReal_cpow_const htZero ha
  cases k with
  | zero =>
      have hFunction :
          robinCpowLogPrimitive a 0 =
            (fun y : Real => Inv.inv a * (y : Complex) ^ a) := by
        funext y
        simp [robinCpowLogPrimitive]
      rw [hFunction]
      simpa [ha] using hPower.const_mul (Inv.inv a)
  | succ k =>
      have hLogPower := (Real.hasDerivAt_log htZero).pow (k + 1)
      have hLogPowerZero :
          Not ((Real.log t) ^ (k + 1) = 0) :=
        pow_ne_zero (k + 1) hLogZero
      have hInverse := (hLogPower.inv hLogPowerZero).ofReal_comp
      have hRaw := (hPower.mul hInverse).const_mul (Inv.inv a)
      have hFunction :
          robinCpowLogPrimitive a (k + 1) =
            (fun y : Real => Inv.inv a *
              ((fun z : Real => (z : Complex) ^ a) y *
                (fun z : Real =>
                  (((Inv.inv ((Real.log z) ^ (k + 1)) : Real) : Complex))) y)) := by
        funext y
        simp [robinCpowLogPrimitive, mul_assoc]
      have hCoefficient :
          Inv.inv a *
              (a * (t : Complex) ^ (a - 1) *
                  (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex)) +
                (t : Complex) ^ a *
                  (((-( (k + 1 : Real) * (Real.log t) ^ k * Inv.inv t) /
                    ((Real.log t) ^ (k + 1)) ^ (2 : Nat) : Real) : Complex))) =
            (t : Complex) ^ (a - 1) *
                (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex)) -
              (((k + 1 : Nat) : Complex) * Inv.inv a) *
                (t : Complex) ^ (a - 1) *
                (((Inv.inv ((Real.log t) ^ (k + 2)) : Real) : Complex)) := by
        rw [Complex.cpow_sub a 1 (Complex.ofReal_ne_zero.mpr htZero),
          Complex.cpow_one]
        push_cast
        field_simp [ha, hLogZero, htZero]
        ring
      rw [hFunction]
      have hNormalized := hRaw
      simp only [Pi.pow_apply, Pi.inv_apply, Nat.cast_add, Nat.cast_one,
        add_tsub_cancel_right] at hNormalized
      rw [hCoefficient] at hNormalized
      simpa [Nat.add_assoc] using hNormalized

theorem tendsto_robinCpowLogPrimitive_atTop
    {a : Complex} (ha : a.re < 0) (k : Nat) :
    Filter.Tendsto (robinCpowLogPrimitive a k) Filter.atTop (nhds 0) := by
  have haZero : Not (a = 0) := by
    intro h
    rw [h] at ha
    norm_num at ha
  have hRpow :
      Filter.Tendsto (fun t : Real => t ^ a.re) Filter.atTop (nhds 0) := by
    have hNeg : 0 < -a.re := neg_pos.mpr ha
    simpa [neg_neg] using tendsto_rpow_neg_atTop hNeg
  have hCpowNorm :
      Filter.Tendsto (fun t : Real => norm ((t : Complex) ^ a))
        Filter.atTop (nhds 0) :=
    (Filter.tendsto_congr' (norm_ofReal_cpow_eventually_eq_atTop a)).mpr hRpow
  have hMajor :
      Filter.Tendsto
        (fun t : Real => norm (Inv.inv a) * norm ((t : Complex) ^ a))
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hCpowNorm)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hMajor
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with t ht
  have htPos : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  have hLogOne : 1 <= Real.log t := by
    rw [<- Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) ht
  have hPowOne : 1 <= (Real.log t) ^ k := by
    induction k with
    | zero => simp
      | succ k ih =>
        rw [pow_succ]
        simpa using mul_le_mul ih hLogOne zero_le_one
          (pow_nonneg (le_trans zero_le_one hLogOne) k)
  have hPowPos : 0 < (Real.log t) ^ k := lt_of_lt_of_le zero_lt_one hPowOne
  have hInvLe : Inv.inv ((Real.log t) ^ k) <= 1 := by
    simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hPowOne
  rw [robinCpowLogPrimitive, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hPowPos)]
  simpa using mul_le_mul_of_nonneg_left hInvLe
    (mul_nonneg (norm_nonneg (Inv.inv a))
      (norm_nonneg ((t : Complex) ^ a)))

/-- Exact integration-by-parts recurrence for the logarithmically weighted
complex-power tail. -/
theorem robinCpowLogTail_recurrence
    {a : Complex} {x : Real} (hx : 1 < x) (ha : a.re < 0)
    (k : Nat) :
    robinCpowLogTail a k x =
      -Inv.inv a * (x : Complex) ^ a *
          (((Inv.inv ((Real.log x) ^ k) : Real) : Complex)) +
        ((k : Complex) * Inv.inv a) * robinCpowLogTail a (k + 1) x := by
  have haZero : Not (a = 0) := by
    intro h
    rw [h] at ha
    norm_num at ha
  have hExponent : (a - 1).re < -1 := by
    simp
    linarith
  have hFirst :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ k) : Real) : Complex))) (Ioi x) :=
    integrableOn_cpow_div_log_pow hx hExponent k
  have hNext :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex))) (Ioi x) :=
    integrableOn_cpow_div_log_pow hx hExponent (k + 1)
  have hScaledNext :
      IntegrableOn (fun t : Real =>
        ((k : Complex) * Inv.inv a) *
          ((t : Complex) ^ (a - 1) *
            (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex))))
        (Ioi x) :=
    hNext.const_mul ((k : Complex) * Inv.inv a)
  have hDifference :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
            (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)) -
          ((k : Complex) * Inv.inv a) *
            ((t : Complex) ^ (a - 1) *
              (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex))))
        (Ioi x) :=
    hFirst.sub hScaledNext
  have hIntegral :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := robinCpowLogPrimitive a k)
      (f' := fun t : Real =>
        (t : Complex) ^ (a - 1) *
            (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)) -
          ((k : Complex) * Inv.inv a) *
            ((t : Complex) ^ (a - 1) *
              (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex))))
      (fun t ht => by
        simpa [mul_assoc] using
          hasDerivAt_robinCpowLogPrimitive haZero k
            (lt_of_lt_of_le hx ht))
      hDifference (tendsto_robinCpowLogPrimitive_atTop ha k)
  have hSplit :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          (t : Complex) ^ (a - 1) *
              (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)) -
            ((k : Complex) * Inv.inv a) *
              ((t : Complex) ^ (a - 1) *
                (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex)))) =
        robinCpowLogTail a k x -
          ((k : Complex) * Inv.inv a) * robinCpowLogTail a (k + 1) x := by
    rw [integral_sub hFirst hScaledNext, integral_const_mul]
    rfl
  rw [hSplit] at hIntegral
  unfold robinCpowLogPrimitive at hIntegral
  linear_combination hIntegral

/-- The logarithmic denominator can be frozen at the left endpoint of the
tail.  This is the quantitative estimate used in Robin 1984, Lemma 1. -/
theorem norm_robinCpowLogTail_le
    {a : Complex} {x : Real} (hx : 1 < x) (ha : a.re < 0)
    (k : Nat) :
    norm (robinCpowLogTail a k x) <=
      (-x ^ a.re / a.re) * Inv.inv ((Real.log x) ^ k) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogXPos : 0 < Real.log x := Real.log_pos hx
  have hExponent : a.re - 1 < -1 := by
    linarith
  have hBase :
      IntegrableOn (fun t : Real => t ^ (a.re - 1)) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt hExponent hxPos
  have hMajor :
      IntegrableOn (fun t : Real =>
        t ^ (a.re - 1) * Inv.inv ((Real.log x) ^ k)) (Ioi x) :=
    hBase.mul_const _
  unfold robinCpowLogTail
  calc
    norm (integral (volume.restrict (Ioi x)) (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)))) <=
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          t ^ (a.re - 1) * Inv.inv ((Real.log x) ^ k)) := by
      apply norm_integral_le_of_norm_le hMajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hxt : x <= t := ht.le
      have htPos : 0 < t := lt_of_lt_of_le hxPos hxt
      have hLogLe : Real.log x <= Real.log t :=
        Real.log_le_log hxPos hxt
      have hLogTPos : 0 < Real.log t :=
        lt_of_lt_of_le hLogXPos hLogLe
      have hPowLe : (Real.log x) ^ k <= (Real.log t) ^ k := by
        clear hMajor
        induction k with
        | zero => simp
        | succ k ih =>
            rw [pow_succ, pow_succ]
            exact mul_le_mul ih hLogLe hLogXPos.le
              (pow_nonneg hLogTPos.le k)
      have hPowXPos : 0 < (Real.log x) ^ k := pow_pos hLogXPos k
      have hPowTPos : 0 < (Real.log t) ^ k := pow_pos hLogTPos k
      have hInvLe :
          Inv.inv ((Real.log t) ^ k) <=
            Inv.inv ((Real.log x) ^ k) := by
        simpa [one_div] using one_div_le_one_div_of_le hPowXPos hPowLe
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htPos,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hPowTPos)]
      simp only [Complex.sub_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_left hInvLe
        (Real.rpow_nonneg htPos.le _)
    _ = (-x ^ a.re / a.re) * Inv.inv ((Real.log x) ^ k) := by
      rw [integral_mul_const,
        integral_Ioi_rpow_of_lt hExponent hxPos]
      ring_nf

/-- Critical-line bound for the bracket in Robin's zero-kernel remainder. -/
theorem norm_robinZeroKernelRemainder_bracket_le
    {n : Nat} (hn : 1 <= n) {rho : Complex}
    (hRe : rho.re = (1 / 2 : Real)) {x : Real} (hx : 1 < x) :
    norm
        (-((x : Complex) ^ (rho - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat) +
          2 * robinCpowLogTail (rho - (n : Complex)) 3 x) <=
      x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  have haRe : (rho - (n : Complex)).re < 0 := by
    rw [Complex.sub_re, Complex.natCast_re, hRe]
    have hnReal : (1 : Real) <= (n : Real) := by
      exact_mod_cast hn
    linarith
  have hMainNorm :
      norm
          (-((x : Complex) ^ (rho - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat)) =
        x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) := by
    rw [norm_div, norm_neg,
      Complex.norm_cpow_eq_rpow_re_of_pos hxPos, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLogPos]
    simp only [Complex.sub_re, Complex.natCast_re, hRe]
    rw [div_eq_mul_inv]
  have hTail := norm_robinCpowLogTail_le hx haRe 3
  have hTailExact :
      norm (robinCpowLogTail (rho - (n : Complex)) 3 x) <=
        (-x ^ ((1 / 2 : Real) - (n : Real)) /
            ((1 / 2 : Real) - (n : Real))) *
          Inv.inv ((Real.log x) ^ (3 : Nat)) := by
    simpa only [Complex.sub_re, Complex.natCast_re, hRe] using hTail
  calc
    norm
        (-((x : Complex) ^ (rho - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat) +
          2 * robinCpowLogTail (rho - (n : Complex)) 3 x) <=
        norm
            (-((x : Complex) ^ (rho - (n : Complex))) /
              ((Real.log x : Real) : Complex) ^ (2 : Nat)) +
          norm (2 * robinCpowLogTail (rho - (n : Complex)) 3 x) :=
      norm_add_le _ _
    _ = x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 * norm (robinCpowLogTail (rho - (n : Complex)) 3 x) := by
      rw [hMainNorm, norm_mul]
      norm_num
    _ <= x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hTailExact zero_le_two)

/-- Robin 1984, Lemma 1 remainder bound in the form needed for summing over
the multiplicity-carrying xi divisor. -/
theorem norm_robinZeroKernelRemainder_div_rho_le
    {n : Nat} (hn : 1 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re = (1 / 2 : Real))
    {x : Real} (hx : 1 < x) :
    norm (robinZeroKernelRemainder n rho x / rho) <=
      (Inv.inv (norm rho)) ^ (2 : Nat) *
        (x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv ((Real.log x) ^ (2 : Nat)) +
          2 *
            ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                  ((1 / 2 : Real) - (n : Real))) *
              Inv.inv ((Real.log x) ^ (3 : Nat)))) := by
  have hNormLe : norm rho <= norm (rho - (n : Complex)) :=
    norm_le_norm_sub_nat_of_re_eq_half hn hRe
  have hNormPos : 0 < norm rho := norm_pos_iff.mpr hRho
  have hNormSqPos : 0 < (norm rho) ^ (2 : Nat) :=
    pow_pos hNormPos 2
  have hNormSqLe :
      (norm rho) ^ (2 : Nat) <=
        (norm (rho - (n : Complex))) ^ (2 : Nat) := by
    nlinarith [norm_nonneg (rho - (n : Complex))]
  have hInvNormLe :
      norm (Inv.inv ((rho - (n : Complex)) ^ (2 : Nat))) <=
        (Inv.inv (norm rho)) ^ (2 : Nat) := by
    rw [norm_inv, norm_pow]
    simpa [one_div, inv_pow] using
      one_div_le_one_div_of_le hNormSqPos hNormSqLe
  have hBracket :=
    norm_robinZeroKernelRemainder_bracket_le hn hRe hx
  rw [robinZeroKernelRemainder_div_rho hRho, norm_mul]
  exact mul_le_mul hInvNormLe hBracket (norm_nonneg _)
    (pow_nonneg (inv_nonneg.mpr (norm_nonneg rho)) 2)


/-- Split Robin's kernel into its two logarithmic complex-power tails. -/
theorem robinZeroKernel_eq_nat_mul_tail_one_add_tail_two
    {n : Nat} {rho : Complex} {x : Real} (hx : 1 < x)
    (hRe : rho.re < n) :
    robinZeroKernel n rho x =
      (n : Complex) * robinCpowLogTail (rho - (n : Complex)) 1 x +
        robinCpowLogTail (rho - (n : Complex)) 2 x := by
  let a : Complex := rho - (n : Complex)
  have hExponent : (a - 1).re < -1 := by
    dsimp [a]
    linarith
  have hOne :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv (Real.log t) : Real) : Complex))) (Ioi x) := by
    simpa using integrableOn_cpow_div_log_pow hx hExponent 1
  have hTwo :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ (2 : Nat)) : Real) : Complex)))
        (Ioi x) :=
    integrableOn_cpow_div_log_pow hx hExponent 2
  change robinZeroKernel n rho x =
    (n : Complex) * robinCpowLogTail a 1 x +
      robinCpowLogTail a 2 x
  unfold robinZeroKernel robinCpowLogTail
  have hFunctions :
      (fun t : Real =>
        (t : Complex) ^ (rho - (n : Complex) - 1) *
          (((n : Real) * Real.log t + 1) /
            (Real.log t) ^ (2 : Nat) : Real)) =
        (fun t : Real =>
          (n : Complex) *
              ((t : Complex) ^ (a - 1) *
                (((Inv.inv (Real.log t) : Real) : Complex))) +
            (t : Complex) ^ (a - 1) *
              (((Inv.inv ((Real.log t) ^ (2 : Nat)) : Real) : Complex))) := by
    funext t
    dsimp [a]
    rw [show rho - (n : Complex) - 1 =
        (rho - (n : Complex)) - 1 by ring]
    push_cast
    by_cases hLog : Real.log t = 0
    case pos => simp [hLog]
    case neg => field_simp [hLog]
  rw [hFunctions, integral_add (hOne.const_mul (n : Complex)) hTwo,
    integral_const_mul]
  simp only [pow_one]

/-- One integration by parts exposes the exact atom-matching form: the
boundary atom plus `rho` times the first logarithmic tail. -/
theorem robinZeroKernel_eq_boundary_add_rho_mul_tail_one
    {n : Nat} {rho : Complex} {x : Real} (hx : 1 < x)
    (hRe : rho.re < n) :
    robinZeroKernel n rho x =
      (x : Complex) ^ (rho - (n : Complex)) *
          (((Inv.inv (Real.log x) : Real) : Complex)) +
        rho * robinCpowLogTail (rho - (n : Complex)) 1 x := by
  let a : Complex := rho - (n : Complex)
  have haRe : a.re < 0 := by
    dsimp [a]
    simp
    exact hRe
  have haZero : Not (a = 0) := by
    intro h
    have hReal := congrArg Complex.re h
    rw [Complex.zero_re] at hReal
    linarith
  rw [robinZeroKernel_eq_nat_mul_tail_one_add_tail_two hx hRe]
  have hRecOne := robinCpowLogTail_recurrence hx haRe 1
  have hRecScaled :
      a * robinCpowLogTail a 1 x =
        -(x : Complex) ^ a *
            (((Inv.inv (Real.log x) : Real) : Complex)) +
          robinCpowLogTail a 2 x := by
    rw [hRecOne]
    push_cast
    field_simp [haZero]
  have hRho : rho = (n : Complex) + a := by
    dsimp [a]
    ring
  have hTailTwo :
      robinCpowLogTail a 2 x =
        a * robinCpowLogTail a 1 x +
          (x : Complex) ^ a *
            (((Inv.inv (Real.log x) : Real) : Complex)) := by
    clear hRho
    linear_combination -hRecScaled
  change (n : Complex) * robinCpowLogTail a 1 x +
      robinCpowLogTail a 2 x =
    (x : Complex) ^ a *
        (((Inv.inv (Real.log x) : Real) : Complex)) +
      rho * robinCpowLogTail a 1 x
  rw [hTailTwo, hRho]
  ring

/-- Dividing the atom-matching identity by `rho` gives exactly the Mellin
transform split into the lower constant block and the upper logarithmic tail. -/
theorem robinZeroKernel_div_rho_eq_boundary_div_add_tail_one
    {n : Nat} {rho : Complex} (hRho : Not (rho = 0))
    {x : Real} (hx : 1 < x) (hRe : rho.re < n) :
    robinZeroKernel n rho x / rho =
      (x : Complex) ^ (rho - (n : Complex)) /
          (rho * ((Real.log x : Real) : Complex)) +
        robinCpowLogTail (rho - (n : Complex)) 1 x := by
  rw [robinZeroKernel_eq_boundary_add_rho_mul_tail_one hx hRe]
  push_cast
  field_simp [hRho]

/-- Robin 1984, Lemma 1: the zero kernel is its leading term plus the
twice-integrated remainder. -/
theorem robinZeroKernel_eq_main_add_remainder
    {n : Nat} (hn : 1 <= n) {rho : Complex} {x : Real}
    (hx : 1 < x) (hRe : rho.re < n) :
    robinZeroKernel n rho x =
      ((n : Complex) / ((n : Complex) - rho)) *
          (x : Complex) ^ (rho - (n : Complex)) *
          (((Inv.inv (Real.log x) : Real) : Complex)) +
        robinZeroKernelRemainder n rho x := by
  let a : Complex := rho - (n : Complex)
  have haRe : a.re < 0 := by
    dsimp [a]
    simp
    exact hRe
  have haZero : Not (a = 0) := by
    intro h
    have hReal := congrArg Complex.re h
    rw [Complex.zero_re] at hReal
    linarith
  have hExponent : (a - 1).re < -1 := by
    simp
    linarith
  have hOne :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv (Real.log t) : Real) : Complex))) (Ioi x) := by
    simpa using integrableOn_cpow_div_log_pow hx hExponent 1
  have hTwo :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ (2 : Nat)) : Real) : Complex)))
        (Ioi x) :=
    integrableOn_cpow_div_log_pow hx hExponent 2
  have hKernelSplit :
      robinZeroKernel n rho x =
        (n : Complex) * robinCpowLogTail a 1 x +
          robinCpowLogTail a 2 x := by
    unfold robinZeroKernel robinCpowLogTail
    have hFunctions :
        (fun t : Real =>
          (t : Complex) ^ (rho - (n : Complex) - 1) *
            (((n : Real) * Real.log t + 1) /
              (Real.log t) ^ (2 : Nat) : Real)) =
          (fun t : Real =>
            (n : Complex) *
                ((t : Complex) ^ (a - 1) *
                  (((Inv.inv (Real.log t) : Real) : Complex))) +
              (t : Complex) ^ (a - 1) *
                (((Inv.inv ((Real.log t) ^ (2 : Nat)) : Real) : Complex))) := by
      funext t
      dsimp [a]
      rw [show rho - (n : Complex) - 1 =
          (rho - (n : Complex)) - 1 by ring]
      push_cast
      by_cases hLog : Real.log t = 0
      case pos => simp [hLog]
      case neg =>
        field_simp [hLog]
    rw [hFunctions, integral_add (hOne.const_mul (n : Complex)) hTwo,
      integral_const_mul]
    simp only [pow_one]
  have hRecOne := robinCpowLogTail_recurrence hx haRe 1
  have hRecTwo := robinCpowLogTail_recurrence hx haRe 2
  rw [hKernelSplit, hRecOne, hRecTwo]
  unfold robinZeroKernelRemainder
  have hLog : Not (Real.log x = 0) := ne_of_gt (Real.log_pos hx)
  have hOpp : (n : Complex) - rho = -a := by
    dsimp [a]
    ring
  have hDiff : rho - (n : Complex) = a := by
    rfl
  rw [hOpp, hDiff]
  push_cast
  field_simp [haZero, hLog]
  ring

/-- Complete critical-line majorant for one multiplicity-carrying zero atom. -/
theorem norm_robinZeroKernel_div_rho_le_robinXiZeroWeight
    {n : Nat} (hn : 1 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re = (1 / 2 : Real))
    {x : Real} (hx : 1 < x) :
    norm (robinZeroKernel n rho x / rho) <=
      (Inv.inv (norm rho)) ^ (2 : Nat) *
        ((n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv (Real.log x) +
          (x ^ ((1 / 2 : Real) - (n : Real)) *
              Inv.inv ((Real.log x) ^ (2 : Nat)) +
            2 *
              ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                    ((1 / 2 : Real) - (n : Real))) *
                Inv.inv ((Real.log x) ^ (3 : Nat))))) := by
  have hReLt : rho.re < (n : Real) := by
    have hnReal : (1 : Real) <= (n : Real) := by
      exact_mod_cast hn
    rw [hRe]
    linarith
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  have hCoefficient :=
    norm_nat_div_sub_div_le_robinXiZeroWeight hn hRho hRe
  have hFactorNorm :
      norm
          ((x : Complex) ^ (rho - (n : Complex)) *
            (((Inv.inv (Real.log x) : Real) : Complex))) =
        x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_trans Real.zero_lt_one hx), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hLogPos)]
    simp only [Complex.sub_re, Complex.natCast_re, hRe]
  have hMain :
      norm
          ((((n : Complex) / ((n : Complex) - rho)) *
              (x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) / rho) <=
        (Inv.inv (norm rho)) ^ (2 : Nat) *
          ((n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv (Real.log x)) := by
    have hRewrite :
        (((n : Complex) / ((n : Complex) - rho)) *
              (x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) / rho =
          (((n : Complex) / ((n : Complex) - rho)) / rho) *
            ((x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) := by
      ring
    rw [hRewrite, norm_mul, hFactorNorm]
    have hFactorNonneg :
        0 <= x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans Real.zero_lt_one hx)) _)
        (inv_nonneg.mpr hLogPos.le)
    calc
      norm (((n : Complex) / ((n : Complex) - rho)) / rho) *
          (x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x)) <=
        ((n : Real) * (Inv.inv (norm rho)) ^ (2 : Nat)) *
          (x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x)) :=
        mul_le_mul_of_nonneg_right hCoefficient hFactorNonneg
      _ = (Inv.inv (norm rho)) ^ (2 : Nat) *
          ((n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv (Real.log x)) := by ring
  have hRemainder :=
    norm_robinZeroKernelRemainder_div_rho_le hn hRho hRe hx
  rw [robinZeroKernel_eq_main_add_remainder hn hx hReLt, add_div]
  calc
    norm
        ((((n : Complex) / ((n : Complex) - rho)) *
              (x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) / rho +
          robinZeroKernelRemainder n rho x / rho) <=
        norm
            ((((n : Complex) / ((n : Complex) - rho)) *
                (x : Complex) ^ (rho - (n : Complex)) *
                (((Inv.inv (Real.log x) : Real) : Complex))) / rho) +
          norm (robinZeroKernelRemainder n rho x / rho) :=
      norm_add_le _ _
    _ <= (Inv.inv (norm rho)) ^ (2 : Nat) *
          ((n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv (Real.log x)) +
        (Inv.inv (norm rho)) ^ (2 : Nat) *
          (x ^ ((1 / 2 : Real) - (n : Real)) *
              Inv.inv ((Real.log x) ^ (2 : Nat)) +
            2 *
              ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                    ((1 / 2 : Real) - (n : Real))) *
                Inv.inv ((Real.log x) ^ (3 : Nat)))) :=
      add_le_add hMain hRemainder
    _ = _ := by ring

/-- The complete multiplicity-counted Robin zero-kernel series is absolutely
summable under RH. -/
theorem summable_robinZeroKernel_div_rho
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n)
    {x : Real} (hx : 1 < x) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      robinZeroKernel n (riemannXiDivisorZeroValue p) x /
        riemannXiDivisorZeroValue p) := by
  let C : Real :=
    (n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
        Inv.inv (Real.log x) +
      (x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))))
  have hMajor :
      Summable (fun p : RiemannXiDivisorZeroIndex =>
        (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat) * C) :=
    summable_robinXiZeroWeight.mul_right C
  apply hMajor.of_norm_bounded
  intro p
  dsimp [C]
  exact norm_robinZeroKernel_div_rho_le_robinXiZeroWeight hn
    (riemannXiDivisorZeroValue_ne_zero p)
    (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p) hx

/-- Robin's exact xi zero constant controls the complete zero-kernel sum. -/
theorem norm_tsum_robinZeroKernel_div_rho_le
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n)
    {x : Real} (hx : 1 < x) :
    norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        ((n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv (Real.log x) +
          (x ^ ((1 / 2 : Real) - (n : Real)) *
              Inv.inv ((Real.log x) ^ (2 : Nat)) +
            2 *
              ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                    ((1 / 2 : Real) - (n : Real))) *
                Inv.inv ((Real.log x) ^ (3 : Nat))))) := by
  let C : Real :=
    (n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
        Inv.inv (Real.log x) +
      (x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))))
  have hSeries := summable_robinZeroKernel_div_rho hRH hn hx
  have hNormSeries := hSeries.norm
  have hMajor :
      Summable (fun p : RiemannXiDivisorZeroIndex =>
        (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat) * C) :=
    summable_robinXiZeroWeight.mul_right C
  have hPointwise : forall p : RiemannXiDivisorZeroIndex,
      norm (robinZeroKernel n (riemannXiDivisorZeroValue p) x /
        riemannXiDivisorZeroValue p) <=
      (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat) * C := by
    intro p
    dsimp [C]
    exact norm_robinZeroKernel_div_rho_le_robinXiZeroWeight hn
      (riemannXiDivisorZeroValue_ne_zero p)
      (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p) hx
  calc
    norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) <=
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          norm (robinZeroKernel n (riemannXiDivisorZeroValue p) x /
            riemannXiDivisorZeroValue p)) :=
      norm_tsum_le_tsum_norm hNormSeries
    _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
        (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat) * C) :=
      hNormSeries.tsum_le_tsum hPointwise hMajor
    _ = (tsum (fun p : RiemannXiDivisorZeroIndex =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat))) * C := by
      rw [tsum_mul_right]
    _ = (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) * C := by
      rw [robinXiZeroConstant_eq_of_riemannHypothesis hRH]
    _ = _ := by rfl

/-- The scalar obtained from the leading zero atom and the twice-integrated
remainder is exactly Robin's printed Lemma 2 scalar. -/
theorem robinCriticalLineKernelScalar_eq_paper
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    (n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv (Real.log x) +
        (x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv ((Real.log x) ^ (2 : Nat)) +
          2 *
            ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                  ((1 / 2 : Real) - (n : Real))) *
              Inv.inv ((Real.log x) ^ (3 : Nat)))) =
      x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) *
        ((n : Real) + Inv.inv (Real.log x) +
          4 * Inv.inv (((2 * n - 1 : Nat) : Real) *
            (Real.log x) ^ (2 : Nat))) := by
  have hLog : Not (Real.log x = 0) := ne_of_gt (Real.log_pos hx)
  have hOddNat : Not (2 * n - 1 = 0) := by
    omega
  have hOddReal : Not ((((2 * n - 1 : Nat) : Real)) = 0) := by
    exact_mod_cast hOddNat
  have hOneLeTwoN : 1 <= 2 * n := by
    omega
  have hOddCast :
      (((2 * n - 1 : Nat) : Real)) = 2 * (n : Real) - 1 := by
    rw [Nat.cast_sub hOneLeTwoN]
    push_cast
    rfl
  have hExponentEq :
      (1 / 2 : Real) - (n : Real) =
        -(((2 * n - 1 : Nat) : Real)) / 2 := by
    rw [hOddCast]
    ring
  have hInvSq :
      Inv.inv ((Real.log x) ^ (2 : Nat)) =
        Inv.inv (Real.log x) * Inv.inv (Real.log x) := by
    rw [<- inv_pow]
    ring
  have hThird :
      2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))) =
        x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) *
          (4 * Inv.inv ((((2 * n - 1 : Nat) : Real)) *
            (Real.log x) ^ (2 : Nat))) := by
    rw [hExponentEq]
    field_simp [hLog, hOddReal]
    ring
  rw [hThird, hInvSq]
  ring

/-- Robin 1984, Lemma 2: the complete nontrivial-zero contribution in the
printed scalar normalization. -/
theorem norm_tsum_robinZeroKernel_div_rho_le_paper
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n)
    {x : Real} (hx : 1 < x) :
    norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        (x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) *
          ((n : Real) + Inv.inv (Real.log x) +
            4 * Inv.inv (((2 * n - 1 : Nat) : Real) *
              (Real.log x) ^ (2 : Nat)))) := by
  have hBound := norm_tsum_robinZeroKernel_div_rho_le hRH hn hx
  rw [robinCriticalLineKernelScalar_eq_paper hn hx] at hBound
  exact hBound

/-- The positive real weight in Robin 1984, Lemma 2. -/
def robinRealWeight (n : Nat) (t : Real) : Real :=
  t ^ (-(n : Real) - 1) *
    (((n : Real) * Real.log t + 1) /
      (Real.log t) ^ (2 : Nat))

/-- A primitive whose derivative is Robin's positive real weight. -/
def robinRealWeightPrimitive (n : Nat) (t : Real) : Real :=
  -(t ^ (-(n : Real)) * Inv.inv (Real.log t))

theorem hasDerivAt_robinRealWeightPrimitive
    (n : Nat) {t : Real} (ht : 1 < t) :
    HasDerivAt (robinRealWeightPrimitive n)
      (robinRealWeight n t) t := by
  have htZero : Not (t = 0) :=
    ne_of_gt (lt_trans Real.zero_lt_one ht)
  have hLogZero : Not (Real.log t = 0) :=
    ne_of_gt (Real.log_pos ht)
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have hRpow :
      t ^ (-(n : Real)) = t ^ (-(n : Real) - 1) * t := by
    calc
      t ^ (-(n : Real)) = t ^ ((-(n : Real) - 1) + 1) := by
        congr 1
        ring
      _ = t ^ (-(n : Real) - 1) * t ^ (1 : Real) :=
        Real.rpow_add htPos _ _
      _ = t ^ (-(n : Real) - 1) * t := by
        rw [Real.rpow_one]
  have hPow :=
    Real.hasDerivAt_rpow_const (p := -(n : Real)) (Or.inl htZero)
  have hLogInv := (Real.hasDerivAt_log htZero).inv hLogZero
  have hRaw := (hPow.mul hLogInv).neg
  refine hRaw.congr_deriv ?_
  simp only [Pi.inv_apply]
  unfold robinRealWeight
  rw [hRpow]
  field_simp [htZero, hLogZero] <;> ring

theorem robinRealWeight_nonneg
    {n : Nat} {t : Real} (ht : 1 < t) :
    0 <= robinRealWeight n t := by
  unfold robinRealWeight
  have hLogPos : 0 < Real.log t := Real.log_pos ht
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans Real.zero_lt_one ht)) _)
    (div_nonneg
      (add_nonneg
        (mul_nonneg (Nat.cast_nonneg n) hLogPos.le) zero_le_one)
      (sq_nonneg (Real.log t)))

theorem tendsto_robinRealWeightPrimitive_atTop
    {n : Nat} (hn : 1 <= n) :
    Filter.Tendsto (robinRealWeightPrimitive n) Filter.atTop (nhds 0) := by
  have hnReal : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hPow :
      Filter.Tendsto (fun t : Real => t ^ (-(n : Real)))
        Filter.atTop (nhds 0) := by
    simpa using tendsto_rpow_neg_atTop hnReal
  have hLogInv :
      Filter.Tendsto (fun t : Real => Inv.inv (Real.log t))
        Filter.atTop (nhds 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  change Filter.Tendsto
    (fun t : Real => -(t ^ (-(n : Real)) * Inv.inv (Real.log t)))
    Filter.atTop (nhds 0)
  simpa only [zero_mul, neg_zero] using (hPow.mul hLogInv).neg

/-- The total mass of Robin's weight is the exact cutoff boundary atom. -/
theorem integral_robinRealWeight
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (robinRealWeight n) =
      x ^ (-(n : Real)) * Inv.inv (Real.log x) := by
  have hDeriv : forall t : Real, Membership.mem (Ici x) t ->
      HasDerivAt (robinRealWeightPrimitive n)
        (robinRealWeight n t) t := by
    intro t ht
    exact hasDerivAt_robinRealWeightPrimitive n (lt_of_lt_of_le hx ht)
  have hNonneg : forall t : Real, Membership.mem (Ioi x) t ->
      0 <= robinRealWeight n t := by
    intro t ht
    exact robinRealWeight_nonneg (lt_trans hx ht)
  have hIntegral := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    hDeriv hNonneg (tendsto_robinRealWeightPrimitive_atTop hn)
  rw [hIntegral]
  simp [robinRealWeightPrimitive]

theorem integrableOn_robinRealWeight
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (robinRealWeight n) (Ioi x) := by
  apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (g := robinRealWeightPrimitive n)
  . intro t ht
    exact hasDerivAt_robinRealWeightPrimitive n (lt_of_lt_of_le hx ht)
  . intro t ht
    exact robinRealWeight_nonneg (lt_trans hx ht)
  . exact tendsto_robinRealWeightPrimitive_atTop hn

/-- The pole/trivial-zero correction factor in Robin's weighted explicit
formula. -/
def robinTrivialZeroCorrectionFactor (t : Real) : Real :=
  Real.log (2 * Real.pi) +
    (1 / 2 : Real) * Real.log (1 - 1 / t ^ (2 : Nat))

theorem robinTrivialZeroCorrectionFactor_bounds
    {t : Real} (ht : 2 <= t) :
    And (0 <= robinTrivialZeroCorrectionFactor t)
      (robinTrivialZeroCorrectionFactor t <= Real.log (2 * Real.pi)) := by
  have htSq : (4 : Real) <= t ^ (2 : Nat) := by
    nlinarith
  have hInvLe : (1 : Real) / t ^ (2 : Nat) <= 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) htSq
  have hInvNonneg : 0 <= (1 : Real) / t ^ (2 : Nat) := by
    positivity
  have hInnerHalf : (1 / 2 : Real) <= 1 - 1 / t ^ (2 : Nat) := by
    linarith
  have hInnerPos : 0 < 1 - 1 / t ^ (2 : Nat) := by
    linarith
  have hInnerLeOne : 1 - 1 / t ^ (2 : Nat) <= 1 := by
    linarith
  have hLogNonpos : Real.log (1 - 1 / t ^ (2 : Nat)) <= 0 :=
    Real.log_nonpos hInnerPos.le hInnerLeOne
  have hLogLower :
      Real.log (1 / 2 : Real) <= Real.log (1 - 1 / t ^ (2 : Nat)) :=
    Real.log_le_log (by norm_num) hInnerHalf
  have hLogHalf : Real.log (1 / 2 : Real) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hLogTwoPos : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num)
  have hTwoPi : (2 : Real) <= 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hLogTwoPi : Real.log (2 : Real) <= Real.log (2 * Real.pi) :=
    Real.log_le_log (by norm_num) hTwoPi
  rw [hLogHalf] at hLogLower
  unfold robinTrivialZeroCorrectionFactor
  exact And.intro (by nlinarith) (by linarith)

/-- The complete pole/trivial-zero correction in Robin's weighted explicit
formula. -/
def robinTrivialZeroCorrection (n : Nat) (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    robinRealWeight n t * robinTrivialZeroCorrectionFactor t)

theorem integrableOn_robinTrivialZeroCorrection_integrand
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    IntegrableOn (fun t : Real =>
      robinRealWeight n t * robinTrivialZeroCorrectionFactor t) (Ioi x) := by
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hWeight := integrableOn_robinRealWeight hn hxOne
  apply hWeight.mul_bdd (c := Real.log (2 * Real.pi))
  . have hMeas : Measurable robinTrivialZeroCorrectionFactor := by
      unfold robinTrivialZeroCorrectionFactor
      fun_prop
    exact hMeas.aestronglyMeasurable
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hBounds :=
      robinTrivialZeroCorrectionFactor_bounds (le_trans hx ht.le)
    rw [Real.norm_eq_abs, abs_of_nonneg hBounds.1]
    exact hBounds.2

/-- The correction is nonnegative and at most its constant `log(2*pi)` part
times the exact total weight. -/
theorem robinTrivialZeroCorrection_bounds
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    And (0 <= robinTrivialZeroCorrection n x)
      (robinTrivialZeroCorrection n x <=
        Real.log (2 * Real.pi) * x ^ (-(n : Real)) *
          Inv.inv (Real.log x)) := by
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hWeight := integrableOn_robinRealWeight hn hxOne
  have hCorrection := integrableOn_robinTrivialZeroCorrection_integrand hn hx
  refine And.intro ?_ ?_
  . unfold robinTrivialZeroCorrection
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg
      (robinRealWeight_nonneg (lt_trans hxOne ht))
      (robinTrivialZeroCorrectionFactor_bounds (le_trans hx ht.le)).1
  . unfold robinTrivialZeroCorrection
    have hCompare :
        integral (volume.restrict (Ioi x)) (fun t : Real =>
            robinRealWeight n t * robinTrivialZeroCorrectionFactor t) <=
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            robinRealWeight n t * Real.log (2 * Real.pi)) := by
      apply integral_mono_ae hCorrection (hWeight.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_le_mul_of_nonneg_left
        (robinTrivialZeroCorrectionFactor_bounds (le_trans hx ht.le)).2
        (robinRealWeight_nonneg (lt_trans hxOne ht))
    calc
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          robinRealWeight n t * robinTrivialZeroCorrectionFactor t) <=
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            robinRealWeight n t * Real.log (2 * Real.pi)) := hCompare
      _ = Real.log (2 * Real.pi) * x ^ (-(n : Real)) *
          Inv.inv (Real.log x) := by
        rw [integral_mul_const, integral_robinRealWeight hn hxOne]
        ring

end

end Robin1984
