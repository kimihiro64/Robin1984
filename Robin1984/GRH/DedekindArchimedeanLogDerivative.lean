import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Robin1984.GRH.DedekindCompletedHadamard
import Robin1984.GRH.DedekindIntegratedTailBridge

/-!
# The Dedekind archimedean logarithmic derivative

Differentiate the gamma factors on the positive half-plane. The digamma series supplies the negative gamma lattice, and the values at two give the real-part estimate for the completed logarithmic derivative.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The standard gamma factors and the partial-fraction expansion of the digamma function.
- Formalization note: Differentiate the normalized factors and use nonnegative Dirichlet coefficients at two.
- Content basis: Canonical Dedekind completion, Gamma logarithmic derivative, and the pinned PrimeNumberTheoremAnd digamma series.
- Dependency status: Optional GRH extension and PrimeNumberTheoremAnd.
-/

open DedekindZeta NumberField NumberField.InfinitePlace

namespace Robin1984.GRH

/-- The negative lattice of gamma-factor poles, with spacing q. -/
def gammaZero (q : Real) (n : Nat) : Complex :=
  -((q * ((n : Real) + 1) : Real) : Complex)

private theorem gammaZero_re {q : Real} (hq : 0 < q) (n : Nat) :
    (gammaZero q n).re < 0 := by
  unfold gammaZero
  rw [Complex.neg_re, Complex.ofReal_re, neg_lt_zero]
  positivity

private theorem complex_ne_neg_nat_of_re_pos {z : Complex} (hz : 0 < z.re) (n : Nat) :
    Not (z = -(n : Complex)) := by
  intro h
  rw [h, Complex.neg_re, Complex.natCast_re] at hz
  exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg n))) hz

/-- The digamma contribution divided by its argument has a convergent sum over the negative gamma lattice. -/
theorem hasSum_gammaZeroLogDeriv_div {q : Real} (hq : 0 < q) {s : Complex}
    (hs : 0 < s.re) :
    HasSum (fun n : Nat => 1 / (gammaZero q n * (s - gammaZero q n)))
      ((-Complex.digamma (s / (q : Complex)) / (q : Complex) -
        (Real.eulerMascheroniConstant : Complex) / (q : Complex) - 1 / s) / s) := by
  let z := s / (q : Complex)
  have hz : 0 < z.re := by
    dsimp [z]
    rw [div_eq_mul_inv, <- Complex.ofReal_inv, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    positivity
  have hs0 := Complex.ne_zero_of_re_pos hs
  have hz0 := Complex.ne_zero_of_re_pos hz
  have hq0 : Not ((q : Complex) = 0) := Complex.ofReal_ne_zero.mpr hq.ne'
  have hz1 : 0 < (z + 1).re := by rw [Complex.add_re, Complex.one_re]; positivity
  have hSum := Complex.hasSum_digamma_of_re_pos hz1
  have h := hSum.neg.div_const ((q : Complex) * s)
  have eqTerm (n : Nat) :
      -(Inv.inv ((n : Complex) + 1) - Inv.inv (z + 1 + n)) / ((q : Complex) * s) =
        1 / (gammaZero q n * (s - gammaZero q n)) := by
    have hn : Not ((n : Complex) + 1 = 0) := Complex.ne_zero_of_re_pos (by
      rw [Complex.add_re, Complex.natCast_re, Complex.one_re]
      positivity)
    have hn1 : Not (z + 1 + (n : Complex) = 0) := Complex.ne_zero_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
      positivity)
    have hw0 : Not (gammaZero q n = 0) := by
      intro e
      have h := gammaZero_re hq n
      rw [e, Complex.zero_re] at h
      exact (lt_irrefl _) h
    have hw1 : Not (s - gammaZero q n = 0) := Complex.ne_zero_of_re_pos (by
      rw [Complex.sub_re]
      exact sub_pos.mpr ((gammaZero_re hq n).trans hs))
    have hw : gammaZero q n = -(q : Complex) * ((n : Complex) + 1) := by
      unfold gammaZero
      push_cast
      ring
    rw [hw] at hw0 hw1
    rw [hw]
    dsimp [z] at hn1
    dsimp [z]
    have htotal : Not (((n : Complex) * (q : Complex) + (q : Complex) + s) = 0) :=
      Complex.ne_zero_of_re_pos (by
        simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
          Complex.ofReal_re, zero_mul, sub_zero]
        positivity)
    field_simp [hq0, hs0, hn, hn1, hw0, hw1]
    ring_nf
    have cancel : ((n : Complex) * (q : Complex) + (q : Complex) + s) *
        Inv.inv ((n : Complex) * (q : Complex) + (q : Complex) + s) = 1 := by
      rw [<- div_eq_mul_inv, div_self htotal]
    linear_combination cancel
  change HasSum (fun n : Nat => -(Inv.inv ((n : Complex) + 1) - Inv.inv (z + 1 + n)) /
    ((q : Complex) * s)) _ at h
  simp_rw [eqTerm] at h
  rw [Complex.digamma_apply_add_one z (complex_ne_neg_nat_of_re_pos hz)] at h
  convert h using 1
  change (-Complex.digamma z / (q : Complex) - (Real.eulerMascheroniConstant : Complex) /
    (q : Complex) - 1 / s) / s = -(Complex.digamma z + Inv.inv z + Real.eulerMascheroniConstant) /
    ((q : Complex) * s)
  dsimp [z]
  field_simp [hs0, hq0]
  ring

private theorem logDeriv_const_cpow {f : Complex -> Complex} {a c s : Complex}
    (hf : HasDerivAt f a s) (hc : Not (c = 0)) :
    logDeriv (fun z => c ^ f z) s = Complex.log c * a := by
  rw [logDeriv_apply, (hf.const_cpow (Or.inl hc)).deriv]
  have h : Not (c ^ f s = 0) := Complex.cpow_ne_zero_iff.mpr (Or.inl hc)
  field_simp [h]

private theorem gamma_ne_zero_of_re_pos {s : Complex} (hs : 0 < s.re) :
    Not (Complex.Gamma s = 0) := by
  apply Complex.Gamma_ne_zero
  intro n h
  have hh := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at hh
  rw [hh] at hs
  exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg n))) hs

private theorem differentiableAt_gamma_of_re_pos {s : Complex} (hs : 0 < s.re) :
    DifferentiableAt Complex Complex.Gamma s := by
  apply Complex.differentiableAt_Gamma
  intro n h
  have hh := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at hh
  rw [hh] at hs
  exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg n))) hs

private theorem logDeriv_LReal {s : Complex} (hs : 0 < s.re) :
    logDeriv LReal s = (Complex.digamma (s / 2) - Complex.log Real.pi) / 2 := by
  have hPi : Not ((Real.pi : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hS : 0 < (s / 2).re := by
    rw [show (s / 2).re = s.re / 2 by
      simp [div_eq_mul_inv, Complex.mul_re, Complex.inv_re]]
    positivity
  have hNeg : HasDerivAt (fun z : Complex => -z / 2) (-(1 : Complex) / 2) s :=
    (hasDerivAt_id s).neg.div_const 2
  have hHalf : HasDerivAt (fun z : Complex => z / 2) (1 / 2) s :=
    (hasDerivAt_id s).div_const 2
  unfold LReal
  rw [logDeriv_mul (f := fun z => (Real.pi : Complex) ^ (-z / 2))
    (g := fun z => Complex.Gamma (z / 2)) s
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hPi)) (gamma_ne_zero_of_re_pos hS)
    (hNeg.const_cpow (Or.inl hPi)).differentiableAt
    ((differentiableAt_gamma_of_re_pos hS).comp s hHalf.differentiableAt)]
  rw [logDeriv_const_cpow hNeg hPi]
  change _ + logDeriv (Complex.Gamma.comp (fun z => z / 2)) s = _
  rw [logDeriv_comp (g := fun z : Complex => z / 2) (x := s)
    (differentiableAt_gamma_of_re_pos hS) hHalf.differentiableAt, hHalf.deriv]
  rw [Complex.digamma_def]
  ring

private theorem logDeriv_LComplex {s : Complex} (hs : 0 < s.re) :
    logDeriv LComplex s = Complex.digamma s - Complex.log (2 * (Real.pi : Complex)) := by
  have hPi : Not ((2 : Complex) * (Real.pi : Complex) = 0) :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hNeg : HasDerivAt (fun z : Complex => -z) (-1) s :=
    (hasDerivAt_id s).neg
  unfold LComplex
  have hF : (fun z : Complex => 2 * (2 * (Real.pi : Complex)) ^ (-z) * Complex.Gamma z) =
      fun z => 2 * ((2 * (Real.pi : Complex)) ^ (-z) * Complex.Gamma z) := by
    funext z
    rw [mul_assoc]
  rw [hF, logDeriv_const_mul s 2 (by norm_num)]
  rw [logDeriv_mul (f := fun z => (2 * (Real.pi : Complex)) ^ (-z)) (g := Complex.Gamma)
    s (Complex.cpow_ne_zero_iff.mpr (Or.inl hPi)) (gamma_ne_zero_of_re_pos hs)
    (hNeg.const_cpow (Or.inl hPi)).differentiableAt (differentiableAt_gamma_of_re_pos hs)]
  rw [logDeriv_const_cpow hNeg hPi, Complex.digamma_def]
  ring

variable (K : Type*) [Field K] [NumberField K]

private theorem re_div_two (s : Complex) : (s / 2).re = s.re / 2 := by
  simp [div_eq_mul_inv, Complex.mul_re, Complex.inv_re]

/-- The logarithmic derivative of the discriminant and gamma factors on the positive half-plane. -/
theorem logDeriv_dedekindArchimedean {s : Complex} (hs : 0 < s.re) :
    logDeriv (ZInfty K) s = Complex.log (Int.natAbs (discr K) : Complex) / 2 +
      (nrRealPlaces K : Complex) * ((Complex.digamma (s / 2) - Complex.log Real.pi) / 2) +
      (nrComplexPlaces K : Complex) * (Complex.digamma s - Complex.log (2 * (Real.pi : Complex))) := by
  let D := ((Int.natAbs (discr K)) : Complex)
  have hD : Not (D = 0) := by
    dsimp [D]
    exact_mod_cast Int.natAbs_ne_zero.mpr (discr_ne_zero K)
  have hPi : Not ((Real.pi : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hPi2 : Not ((2 : Complex) * (Real.pi : Complex) = 0) :=
    mul_ne_zero (by norm_num) hPi
  have hS : 0 < (s / 2).re := by
    rw [re_div_two]
    positivity
  have hHalf : HasDerivAt (fun z : Complex => z / 2) (1 / 2) s :=
    (hasDerivAt_id s).div_const 2
  have hNegHalf : HasDerivAt (fun z : Complex => -z / 2) (-(1 : Complex) / 2) s :=
    (hasDerivAt_id s).neg.div_const 2
  have hNeg : HasDerivAt (fun z : Complex => -z) (-1) s := (hasDerivAt_id s).neg
  have hd : DifferentiableAt Complex (fun z : Complex => D ^ (z / 2)) s :=
    (hHalf.const_cpow (Or.inl hD)).differentiableAt
  have hreal : DifferentiableAt Complex LReal s :=
    (hNegHalf.const_cpow (Or.inl hPi)).differentiableAt.mul
      ((differentiableAt_gamma_of_re_pos hS).comp s hHalf.differentiableAt)
  have hcomplex : DifferentiableAt Complex LComplex s :=
    ((hNeg.const_cpow (Or.inl hPi2)).differentiableAt.const_mul 2).mul
      (differentiableAt_gamma_of_re_pos hs)
  have hr : Not (LReal s = 0) := mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hPi)) (gamma_ne_zero_of_re_pos hS)
  have hc : Not (LComplex s = 0) := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl hPi2)))
    (gamma_ne_zero_of_re_pos hs)
  unfold ZInfty
  rw [Int.abs_eq_natAbs, Int.cast_natCast]
  change logDeriv (fun z : Complex => D ^ (z / 2) *
    LReal z ^ nrRealPlaces K * LComplex z ^ nrComplexPlaces K) s = _
  rw [logDeriv_mul (f := fun z : Complex => D ^ (z / 2) * LReal z ^ nrRealPlaces K)
    (g := fun z => LComplex z ^ nrComplexPlaces K) s
    (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hD)) (pow_ne_zero _ hr))
    (pow_ne_zero _ hc) (hd.mul (hreal.pow _)) (hcomplex.pow _)]
  rw [logDeriv_mul (f := fun z : Complex => D ^ (z / 2))
    (g := fun z => LReal z ^ nrRealPlaces K) s (Complex.cpow_ne_zero_iff.mpr (Or.inl hD))
    (pow_ne_zero _ hr) hd (hreal.pow _)]
  rw [logDeriv_fun_pow hreal, logDeriv_fun_pow hcomplex, logDeriv_const_cpow hHalf hD,
    logDeriv_LReal hs, logDeriv_LComplex hs]
  ring

/-- At a nonzero value of the completion, remove the explicitly differentiated archimedean factors. -/
theorem logDeriv_entirePoleFreeDedekindZeta {s : Complex} (hs : 0 < s.re)
    (hn : Not (completedDedekindPoleCleared K s = 0)) :
    logDeriv (entirePoleFreeDedekindZeta K) s =
      logDeriv (completedDedekindPoleCleared K) s - 1 / s - logDeriv (ZInfty K) s := by
  let F := entirePoleFreeDedekindZeta K
  let A := ZInfty K
  have hNear : Filter.EventuallyEq (nhds s) (completedDedekindPoleCleared K)
      (fun z : Complex => z * A z * F z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact completedDedekindPoleCleared_eq_archimedean K hz
  have hF : Not (F s = 0) := by
    intro h
    apply hn
    rw [completedDedekindPoleCleared_eq_archimedean K hs]
    change s * A s * F s = 0
    rw [h, mul_zero]
  have hA := ZInfty_ne_zero_of_re_pos K hs
  have hDA := (analyticAt_ZInfty_of_re_pos K hs).differentiableAt
  have hD := (analyticAt_entirePoleFreeDedekindZeta K s).differentiableAt
  have hs0 := Complex.ne_zero_of_re_pos hs
  have h := (logDeriv_congr_nhds hNear).eq_of_nhds
  rw [logDeriv_mul (f := fun z : Complex => z * A z) (g := F)
    s (mul_ne_zero hs0 hA) hF (differentiableAt_id.mul hDA) hD] at h
  rw [logDeriv_mul (f := fun z : Complex => z) (g := A)
    s hs0 hA differentiableAt_id hDA, logDeriv_id'] at h
  change logDeriv F s = logDeriv (completedDedekindPoleCleared K) s - 1 / s - logDeriv A s
  rw [h]
  ring

private theorem dedekind_logDeriv_two_nonpos :
    (logDeriv (NumberField.dedekindZeta K) 2).re <= 0 := by
  have hTwo : 1 < (2 : Complex).re := by norm_num
  have h := hasSum_dedekindNormCoeff K hTwo
  change HasSum (LSeries.term (fun n => (dedekindNormCoeff K n : Complex)) 2)
    (-(deriv (NumberField.dedekindZeta K) 2) / NumberField.dedekindZeta K 2) at h
  rw [neg_div, <- logDeriv_apply] at h
  have hRe := Complex.reCLM.hasSum h
  change HasSum (fun n => (LSeries.term (fun n => (dedekindNormCoeff K n : Complex)) 2 n).re)
    (-(logDeriv (NumberField.dedekindZeta K) 2).re) at hRe
  rw [<- neg_nonneg, <- hRe.tsum_eq]
  refine tsum_nonneg ?_
  intro n
  by_cases hn : n = 0
  case pos => subst n; simp only [LSeries.term_zero, Complex.zero_re, le_refl]
  case neg =>
    rw [LSeries.term_of_ne_zero hn, show (n : Complex) ^ (2 : Complex) = (n : Complex) ^ (2 : Nat)
      from Complex.cpow_natCast _ 2, <- Complex.ofReal_natCast, <- Complex.ofReal_pow,
      <- Complex.ofReal_div, Complex.ofReal_re]
    positivity [dedekindNormCoeff_nonneg K n]

private theorem poleFree_logDeriv_two_le_one :
    (logDeriv (entirePoleFreeDedekindZeta K) 2).re <= 1 := by
  have hTwo : 1 < (2 : Complex).re := by norm_num
  have h := actualDedekindError_logDeriv_identity K hTwo
  rw [neg_div, <- logDeriv_apply] at h
  have he : logDeriv (entirePoleFreeDedekindZeta K) 2 =
      1 + logDeriv (NumberField.dedekindZeta K) 2 := by
    norm_num at h
    linear_combination 2 * h
  rw [he, Complex.add_re, Complex.one_re]
  have hb := dedekind_logDeriv_two_nonpos K
  linarith

/-- At two the real part of the logarithmic derivative is bounded by the discriminant and pole factors. -/
theorem completedDedekind_logDeriv_two_le :
    (logDeriv (completedDedekindPoleCleared K) 2).re <=
      3 / 2 + Real.log ((discr K).natAbs : Real) / 2 := by
  have h2 : 0 < (2 : Complex).re := by norm_num
  have hn := completedDedekindPoleCleared_ne_zero_of_one_le_re K (s := (2 : Complex)) (by norm_num)
  have h := logDeriv_entirePoleFreeDedekindZeta K h2 hn
  have he := congrArg Complex.re h
  rw [Complex.sub_re, Complex.sub_re] at he
  have hArch := logDeriv_dedekindArchimedean K h2
  have he0 : (1 / (2 : Complex)).re = 1 / 2 := by norm_num
  rw [he0, hArch] at he
  have hF := poleFree_logDeriv_two_le_one K
  have hEuler : 0 <= Real.eulerMascheroniConstant :=
    le_of_lt (by linarith [Real.one_half_lt_eulerMascheroniConstant])
  have hPi : 0 <= Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hPi2 : 1 <= Real.log (2 * Real.pi) := by
    have hp : 0 < 2 * Real.pi := by positivity [Real.pi_pos]
    have hh : Real.exp 1 <= 2 * Real.pi := by linarith [Real.exp_one_lt_three, Real.pi_gt_three]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hh
  have hDg := Complex.digamma_apply_add_one (1 : Complex) (fun n h => by
    have hh := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hh
    linarith [(Nat.cast_nonneg n : 0 <= (n : Real))])
  rw [Complex.digamma_one] at hDg
  have hDg2 : Complex.digamma (2 : Complex) = -(Real.eulerMascheroniConstant : Complex) + 1 := by
    rw [show (2 : Complex) = 1 + 1 by norm_num, hDg, inv_one]
  have hReal : ((Complex.digamma ((2 : Complex) / 2) - Complex.log (Real.pi : Complex)) / 2).re <= 0 := by
    rw [re_div_two, div_self (by norm_num : Not ((2 : Complex) = 0)), Complex.digamma_one,
      Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.log_ofReal_re]
    linarith
  have hComplex : (Complex.digamma (2 : Complex) - Complex.log (2 * (Real.pi : Complex))).re <= 0 := by
    rw [hDg2, Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re,
      show (2 : Complex) * (Real.pi : Complex) = ((2 * Real.pi : Real) : Complex) by norm_cast,
      Complex.log_ofReal_re]
    linarith
  have hD : (Complex.log ((discr K).natAbs : Complex) / 2).re =
      Real.log ((discr K).natAbs : Real) / 2 := by
    rw [re_div_two, <- Complex.ofReal_natCast, Complex.log_ofReal_re]
  rw [Complex.add_re, Complex.add_re, hD] at he
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at he
  have hR := mul_nonpos_of_nonneg_of_nonpos
    (Nat.cast_nonneg (n := nrRealPlaces K)) hReal
  have hC := mul_nonpos_of_nonneg_of_nonpos
    (Nat.cast_nonneg (n := nrComplexPlaces K)) hComplex
  linarith

end Robin1984.GRH
