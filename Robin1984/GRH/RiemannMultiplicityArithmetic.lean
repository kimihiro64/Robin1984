import Robin1984.GRH.AutomorphicCompletion
import Robin1984.NicolasLandau.XiLogDerivative

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The completed Riemann xi function, Gamma recurrence, and the logarithmic derivative of the zeta Euler product.
- Formalization note: The pole-cleared ordinary factor is entire of order at most one, preserves the orders of zeta in the strip, and supplies the von Mangoldt coefficients.
- PROVENANCE-END
-/

/-!
# The ordinary zeta factor and the classical prime-power remainder

The pole-cleared ordinary factor is entire of order at most one, preserves the orders of zeta in the strip, and supplies the von Mangoldt coefficients.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Complex Complex.Hadamard DedekindZeta Filter Set

/-- A pole-cleared ordinary zeta factor expressed using xi and the
reciprocal shifted real Gamma factor. -/
def riemannPoleClearedFactor (s : Complex) : Complex :=
  riemannXi s * (Real.pi : Complex) ^ (s / 2 + 1) * Inv.inv (Complex.Gamma (s / 2 + 1))

/-- The actual ordinary zeta factor is entire of order at most one. -/
theorem riemannPoleClearedFactor_entireOrderOne :
    EntireOfOrderAtMost 1 riemannPoleClearedFactor := by
  have hPi : Not ((Real.pi : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hAffine : Differentiable Complex (fun s : Complex => s / 2 + 1) :=
    (differentiable_id.div_const (2 : Complex)).add_const (1 : Complex)
  have hPiPower : Differentiable Complex (fun s : Complex => (Real.pi : Complex) ^ (s / 2 + 1)) := by
    simp only [Complex.cpow_def_of_ne_zero hPi]
    exact Complex.differentiable_exp.comp (hAffine.const_mul (Complex.log (Real.pi : Complex)))
  have hGamma : Differentiable Complex (fun s : Complex => Inv.inv (Complex.Gamma (s / 2 + 1))) :=
    reciprocalGamma_entireOfOrderAtMost_one.differentiable.comp hAffine
  have hF : Differentiable Complex riemannPoleClearedFactor :=
    (riemannXi_entireOfOrderAtMost_one.differentiable.mul hPiPower).mul hGamma
  refine entireOrderOne_of_standardCompletion (conductor := (1 : Real)) (by norm_num)
    0 (fun _ : Unit => (2 : Complex)) (fun _ : Empty => (0 : Complex))
    (fun _ => by norm_num) (fun j => Empty.elim j)
    hF riemannXi_entireOfOrderAtMost_one ?_
  intro s hs
  have hStandard : standardCompletionFactor (1 : Real) 0
      (fun _ : Unit => (2 : Complex)) (fun _ : Empty => (0 : Complex)) s = LReal (s + 2) := by
    simp [standardCompletionFactor]
  rw [hStandard, LReal, riemannPoleClearedFactor]
  have ha : (s + 2) / 2 = s / 2 + 1 := by ring
  have hb : -(s + 2) / 2 = -(s / 2 + 1) := by ring
  rw [ha, hb, Complex.cpow_neg]
  have hRe : 0 < (s / 2 + 1).re := by
    have hHalf : (s / 2).re = s.re / 2 := by simp
    rw [Complex.add_re, Complex.one_re, hHalf]
    linarith only [hs]
  have hG : Not (Complex.Gamma (s / 2 + 1) = 0) := Complex.Gamma_ne_zero_of_re_pos hRe
  have hP : Not ((Real.pi : Complex) ^ (s / 2 + 1) = 0) :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hPi)
  calc
    riemannXi s = riemannXi s *
        ((Real.pi : Complex) ^ (s / 2 + 1) / (Real.pi : Complex) ^ (s / 2 + 1)) *
        (Complex.Gamma (s / 2 + 1) / Complex.Gamma (s / 2 + 1)) := by
      rw [div_self hG, div_self hP, mul_one, mul_one]
    _ = _ := by ring

/-- In the positive half-plane away from the pole, this factor is zeta
multiplied by the pole factor and by pi. -/
theorem riemannPoleClearedFactor_eq {s : Complex} (hs : 0 < s.re) (hs1 : Not (s = 1)) :
    riemannPoleClearedFactor s = (Real.pi : Complex) * (s - 1) * riemannZeta s := by
  have hPi : Not ((Real.pi : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs0 : Not (s = 0) := Complex.ne_zero_of_re_pos hs
  have hHalf : 0 < (s / 2).re := by simp; linarith only [hs]
  have hG : Not (Gamma (s / 2) = 0) := Complex.Gamma_ne_zero_of_re_pos hHalf
  have hP : Not ((Real.pi : Complex) ^ (s / 2) = 0) :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hPi)
  have hn : -s / 2 = -(s / 2) := by ring
  rw [riemannPoleClearedFactor, riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    completedRiemannZeta_eq_cpow_mul_Gamma_mul_riemannZeta hs0 hG,
    Complex.cpow_add (s / 2) 1 hPi, Complex.cpow_one,
    Gamma_add_one (s / 2) (div_ne_zero hs0 two_ne_zero), hn, Complex.cpow_neg]
  field_simp [hG, hP, hs0]

theorem riemannPoleClearedFactor_ne_zero_at_one : Not (riemannPoleClearedFactor 1 = 0) := by
  unfold riemannPoleClearedFactor
  rw [riemannXi_one_eq_half]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
    (inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by norm_num [Complex.div_re])))

/-- The pole-cleared factor has the von Mangoldt Euler logarithmic derivative. -/
theorem riemannPoleClearedFactor_logDeriv {s : Complex} (hs : 1 < s.re) :
    logDeriv riemannPoleClearedFactor s = 1 / (s - 1) -
      LSeries (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s := by
  let P (z : Complex) : Complex := (Real.pi : Complex) * (z - 1)
  have hPos : 0 < s.re := zero_lt_one.trans hs
  have hs1 : Not (s = 1) := by
    intro he
    rw [he, Complex.one_re] at hs
    exact (lt_irrefl _ hs)
  have hZeta : Not (riemannZeta s = 0) := riemannZeta_ne_zero_of_one_lt_re hs
  have hPi : Not ((Real.pi : Complex) = 0) := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hP0 : Not (P s = 0) := mul_ne_zero hPi (sub_ne_zero.mpr hs1)
  have hP : HasDerivAt P (Real.pi : Complex) s := by
    have hId : HasDerivAt (fun z : Complex => z) 1 s := hasDerivAt_id s
    simpa only [P, mul_one] using (hId.sub_const (1 : Complex)).const_mul (Real.pi : Complex)
  have hEq : Filter.EventuallyEq (nhds s) riemannPoleClearedFactor (fun z => P z * riemannZeta z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    have hz1 : Not (z = 1) := by
      intro he
      rw [he, Complex.one_re] at hz
      exact (lt_irrefl _ hz)
    exact riemannPoleClearedFactor_eq (zero_lt_one.trans hz) hz1
  rw [(logDeriv_congr_nhds hEq).self_of_nhds,
    logDeriv_mul s hP0 hZeta hP.differentiableAt (differentiableAt_riemannZeta hs1),
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    logDeriv_apply, hP.deriv]
  change (Real.pi : Complex) / ((Real.pi : Complex) * (s - 1)) +
    deriv riemannZeta s / riemannZeta s =
    1 / (s - 1) - -deriv riemannZeta s / riemannZeta s
  field_simp [hPi, hZeta, sub_ne_zero.mpr hs1]
  ring

/-- Under RH the pole-cleared ordinary zeta factor has no zero to the
right of the critical line. The factor is nonzero at the removed pole. -/
theorem riemannPoleClearedFactor_zero_re_le_half (hRH : RiemannHypothesis)
    {z : Complex} (hZero : riemannPoleClearedFactor z = 0) : z.re <= 1 / 2 := by
  by_contra h
  have hr : 1 / 2 < z.re := lt_of_not_ge h
  have hPos : 0 < z.re := (by norm_num : (0 : Real) < 1 / 2).trans hr
  have hz1 : Not (z = 1) := by
    intro he
    rw [he] at hZero
    exact riemannPoleClearedFactor_ne_zero_at_one hZero
  have hPi : Not ((Real.pi : Complex) = 0) := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [riemannPoleClearedFactor_eq hPos hz1] at hZero
  have hZeta : riemannZeta z = 0 :=
    (mul_eq_zero.mp hZero).resolve_left (mul_ne_zero hPi (sub_ne_zero.mpr hz1))
  have hNontrivial : Not (exists n : Nat, z = -2 * (n + 1)) := by
    intro hz
    choose n hn using hz
    rw [hn] at hPos
    have hn0 : (0 : Real) <= n := Nat.cast_nonneg n
    norm_num [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re] at hPos
    linarith only [hPos, hn0]
  exact (ne_of_gt hr) (hRH z hZeta hNontrivial hz1)

/-- The pole factor is an analytic unit at every point in the open critical
strip, so it preserves the analytic order there. -/
theorem analyticOrderNatAt_riemannPoleClearedFactor_eq {w : Complex}
    (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderNatAt riemannPoleClearedFactor w = analyticOrderNatAt riemannZeta w := by
  let P (z : Complex) : Complex := (Real.pi : Complex) * (z - 1)
  have hw1 : Not (w = 1) := by
    intro h
    rw [h, Complex.one_re] at h1
    exact (lt_irrefl _ h1)
  have hOpen : IsOpen {z : Complex | Not (z = 1)} := isOpen_compl_singleton
  have hEq : Filter.EventuallyEq (nhds w) riemannPoleClearedFactor (P * riemannZeta) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h0,
      hOpen.mem_nhds hw1] with z hz hz1
    exact riemannPoleClearedFactor_eq hz hz1
  have hP : AnalyticAt Complex P w :=
    ((differentiable_id.sub_const (1 : Complex)).const_mul (Real.pi : Complex)).analyticAt w
  have hZ : AnalyticAt Complex riemannZeta w := analyticOn_riemannZeta w hw1
  have hP0 : Not (P w = 0) := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (sub_ne_zero.mpr hw1)
  have hOrd : analyticOrderAt P w = 0 := hP.analyticOrderAt_eq_zero.mpr hP0
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hEq, analyticOrderAt_mul hP hZ, hOrd, zero_add]

/-- Use the positive integer norm for every nonzero index. The index zero
carries zero von Mangoldt coefficient. -/
def riemannPrimePowerNorm (n : Nat) : Real := ((max 1 n : Nat) : Real)

theorem one_le_riemannPrimePowerNorm (n : Nat) : 1 <= riemannPrimePowerNorm n := by
  unfold riemannPrimePowerNorm
  exact_mod_cast le_max_left 1 n

theorem riemannPrimePowerNorm_locallyFinite (T : Real) :
    Set.Finite {n : Nat | riemannPrimePowerNorm n < T} := by
  refine (Set.finite_Iic (Nat.ceil T)).subset ?_
  intro n hn
  have ha : (n : Real) <= riemannPrimePowerNorm n := by
    unfold riemannPrimePowerNorm
    exact_mod_cast le_max_right 1 n
  have hT : T <= (Nat.ceil T : Real) := Nat.le_ceil T
  have h := ha.trans ((show riemannPrimePowerNorm n < T from hn).le.trans hT)
  exact_mod_cast h

private theorem riemannPrimePowerNorm_of_ne_zero {n : Nat} (hn : Not (n = 0)) :
    riemannPrimePowerNorm n = (n : Real) := by
  unfold riemannPrimePowerNorm
  rw [max_eq_right (Nat.pos_of_ne_zero hn)]

/-- The von Mangoldt Dirichlet series is the prime-power series required by
the triangular Mellin transform. -/
theorem LSeries_vonMangoldt_eq_tsum_primePowerNorm (s : Complex) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) s =
      tsum (fun n => (ArithmeticFunction.vonMangoldt n : Complex) *
        (riemannPrimePowerNorm n : Complex) ^ (-s)) := by
  unfold LSeries
  refine tsum_congr ?_
  intro n
  by_cases hn : n = 0
  case pos => simp [hn, LSeries.term_zero]
  case neg =>
    rw [LSeries.term_of_ne_zero hn, riemannPrimePowerNorm_of_ne_zero hn,
      Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]

theorem summable_norm_vonMangoldt_primePowerNorm {r : Real} (hr : 1 < r) :
    Summable (fun n => norm (ArithmeticFunction.vonMangoldt n) * (riemannPrimePowerNorm n) ^ (-r)) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (r : Complex)) (by simpa only [Complex.ofReal_re] using hr)).norm
  refine h.congr ?_
  intro n
  by_cases hn : n = 0
  case pos => simp [hn, LSeries.term_zero]
  case neg =>
    rw [LSeries.norm_term_eq, if_neg hn, riemannPrimePowerNorm_of_ne_zero hn,
      Real.rpow_neg (Nat.cast_nonneg n)]
    simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]

/-- This is the signed triangular prime-power remainder for classical RH. -/
def riemannArithmeticRemainder (x : Real) : Real :=
  triangularRemainder riemannPrimePowerNorm ArithmeticFunction.vonMangoldt 1 x

theorem continuousOn_riemannArithmeticRemainder :
    ContinuousOn riemannArithmeticRemainder (Ioi (1 : Real)) :=
  continuousOn_triangularRemainder riemannPrimePowerNorm ArithmeticFunction.vonMangoldt 1
    riemannPrimePowerNorm_locallyFinite

end Robin1984.GRH
