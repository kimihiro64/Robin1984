import DedekindZeta.Statements
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The gamma factors of the classical Dedekind functional equation.
- Formalization note: The archimedean factor on the positive half-plane.
- PROVENANCE-END
-/

/-!
# The archimedean factor on the positive half-plane

The completion factor is analytic and nonzero for positive real part.
This lets the theta continuation be converted to an analytic continuation
of the uncompleted series in the same half-plane.
-/

open Filter Set

namespace DedekindZeta

private theorem analyticAt_Gamma_of_re_pos {s : Complex} (hs : 0 < s.re) :
    AnalyticAt Complex Complex.Gamma s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hNear : Filter.Eventually (fun z : Complex => 0 < z.re) (nhds s) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  refine hNear.mono (fun z hz => Complex.differentiableAt_Gamma z (fun n h => ?_))
  have hRe := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at hRe
  exact (not_le_of_gt hz) (hRe.trans_le (neg_nonpos.mpr (Nat.cast_nonneg n)))

private theorem analyticAt_const_base_cpow {b s : Complex} {g : Complex -> Complex}
    (hb : Not (b = 0)) (hg : AnalyticAt Complex g s) :
    AnalyticAt Complex (fun z => b ^ (g z)) s := by
  have hLog : AnalyticAt Complex (fun z => Complex.log b * g z) s :=
    analyticAt_const.mul hg
  have hExp : AnalyticAt Complex (fun z => Complex.exp (Complex.log b * g z)) s :=
    analyticAt_cexp.comp (f := fun z => Complex.log b * g z) hLog
  exact hExp.congr (Filter.Eventually.of_forall (fun z =>
    (Complex.cpow_def_of_ne_zero hb (g z)).symm))

private theorem cpow_ne_zero_of_base {b : Complex} (hb : Not (b = 0)) (s : Complex) :
    Not (b ^ s = 0) := by
  rw [Complex.cpow_def_of_ne_zero hb]
  exact Complex.exp_ne_zero _

private theorem ofReal_pi_ne_zero : Not ((Real.pi : Complex) = 0) :=
  Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

private theorem ofReal_two_pi_ne_zero : Not (2 * (Real.pi : Complex) = 0) :=
  mul_ne_zero (by norm_num) ofReal_pi_ne_zero

private theorem discrBase_ne_zero (K : Type*) [Field K] [NumberField K] :
    Not (((abs (NumberField.discr K) : Int) : Complex) = 0) := by
  exact_mod_cast abs_ne_zero.mpr (NumberField.discr_ne_zero K)

private theorem re_div_two_pos {s : Complex} (hs : 0 < s.re) : 0 < (s / 2).re := by
  rw [show s / 2 = s * ((1 / 2 : Real) : Complex) by push_cast; ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_pos hs (by norm_num)

/-- The completion factor is analytic wherever the real part is positive. -/
theorem analyticAt_ZInfty_of_re_pos (K : Type*) [Field K] [NumberField K]
    {s : Complex} (hs : 0 < s.re) : AnalyticAt Complex (ZInfty K) s := by
  have hTwo : Not ((2 : Complex) = 0) := by norm_num
  have hHalf : AnalyticAt Complex (fun z : Complex => z / 2) s :=
    analyticAt_id.div analyticAt_const hTwo
  have hNegHalf : AnalyticAt Complex (fun z : Complex => -z / 2) s :=
    analyticAt_id.neg.div analyticAt_const hTwo
  have hDisc : AnalyticAt Complex (fun z : Complex =>
      ((abs (NumberField.discr K) : Int) : Complex) ^ (z / 2)) s :=
    analyticAt_const_base_cpow (discrBase_ne_zero K) hHalf
  have hGammaHalf : AnalyticAt Complex (fun z : Complex => Complex.Gamma (z / 2)) s :=
    (analyticAt_Gamma_of_re_pos (re_div_two_pos hs)).comp (f := fun z : Complex => z / 2) hHalf
  have hReal : AnalyticAt Complex LReal s :=
    (analyticAt_const_base_cpow ofReal_pi_ne_zero hNegHalf).mul hGammaHalf
  have hCplx : AnalyticAt Complex LComplex s :=
    (analyticAt_const.mul (analyticAt_const_base_cpow ofReal_two_pi_ne_zero
      analyticAt_id.neg)).mul (analyticAt_Gamma_of_re_pos hs)
  exact (hDisc.mul (hReal.pow _)).mul (hCplx.pow _)

/-- The archimedean factor never vanishes in the same half-plane. -/
theorem ZInfty_ne_zero_of_re_pos (K : Type*) [Field K] [NumberField K]
    {s : Complex} (hs : 0 < s.re) : Not (ZInfty K s = 0) := by
  have hR : Not (LReal s = 0) := mul_ne_zero
    (cpow_ne_zero_of_base ofReal_pi_ne_zero _)
    (Complex.Gamma_ne_zero_of_re_pos (re_div_two_pos hs))
  have hC : Not (LComplex s = 0) := mul_ne_zero
    (mul_ne_zero (by norm_num) (cpow_ne_zero_of_base ofReal_two_pi_ne_zero _))
    (Complex.Gamma_ne_zero_of_re_pos hs)
  exact mul_ne_zero
    (mul_ne_zero (cpow_ne_zero_of_base (discrBase_ne_zero K) _) (pow_ne_zero _ hR))
    (pow_ne_zero _ hC)

open NumberField.InfinitePlace

private theorem analyticAt_invGamma (s : Complex) :
    AnalyticAt Complex (fun z : Complex => Inv.inv (Complex.Gamma z)) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Filter.Eventually.of_forall Complex.differentiable_one_div_Gamma

/-- The reciprocal of the archimedean factor is entire. -/
theorem analyticAt_invZInfty (K : Type*) [Field K] [NumberField K] (s : Complex) :
    AnalyticAt Complex (fun z : Complex => Inv.inv (ZInfty K z)) s := by
  let inversion : MonoidWithZeroHom Complex Complex := invMonoidWithZeroHom
  have hTwo : Not ((2 : Complex) = 0) := by norm_num
  have hHalf : AnalyticAt Complex (fun z : Complex => z / 2) s :=
    analyticAt_id.div analyticAt_const hTwo
  have hNegHalf : AnalyticAt Complex (fun z : Complex => -z / 2) s :=
    analyticAt_id.neg.div analyticAt_const hTwo
  have hDiscInv : AnalyticAt Complex (fun z : Complex =>
      Inv.inv (((abs (NumberField.discr K) : Int) : Complex) ^ (z / 2))) s :=
    (analyticAt_const_base_cpow (discrBase_ne_zero K) hHalf).inv
      (cpow_ne_zero_of_base (discrBase_ne_zero K) _)
  have hRealScaleInv : AnalyticAt Complex (fun z : Complex =>
      Inv.inv ((Real.pi : Complex) ^ (-z / 2))) s :=
    (analyticAt_const_base_cpow ofReal_pi_ne_zero hNegHalf).inv
      (cpow_ne_zero_of_base ofReal_pi_ne_zero _)
  have hGammaHalfInv : AnalyticAt Complex (fun z : Complex =>
      Inv.inv (Complex.Gamma (z / 2))) s :=
    (analyticAt_invGamma (s / 2)).comp (f := fun z : Complex => z / 2) hHalf
  have hCplxScale : AnalyticAt Complex (fun z : Complex =>
      (2 : Complex) * (2 * (Real.pi : Complex)) ^ (-z)) s :=
    analyticAt_const.mul (analyticAt_const_base_cpow ofReal_two_pi_ne_zero analyticAt_id.neg)
  have hCplxScaleInv := hCplxScale.inv (mul_ne_zero hTwo
    (cpow_ne_zero_of_base ofReal_two_pi_ne_zero (-s)))
  have hProduct := (hDiscInv.mul ((hRealScaleInv.mul hGammaHalfInv).pow (nrRealPlaces K))).mul
    ((hCplxScaleInv.mul (analyticAt_invGamma s)).pow (nrComplexPlaces K))
  refine hProduct.congr (Filter.Eventually.of_forall (fun z => ?_))
  change inversion (((abs (NumberField.discr K) : Int) : Complex) ^ (z / 2)) *
      (inversion ((Real.pi : Complex) ^ (-z / 2)) * inversion (Complex.Gamma (z / 2))) ^
        nrRealPlaces K *
      (inversion (2 * (2 * (Real.pi : Complex)) ^ (-z)) * inversion (Complex.Gamma z)) ^
        nrComplexPlaces K = inversion (ZInfty K z)
  simp only [ZInfty, LReal, LComplex, map_mul, map_pow]

/-- At zero at least one reciprocal gamma factor vanishes. -/
theorem invZInfty_zero (K : Type*) [Field K] [NumberField K] :
    Inv.inv (ZInfty K 0) = 0 := by
  have hPositive : 0 < nrRealPlaces K + nrComplexPlaces K := by
    rw [<- card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hReal : LReal 0 = 0 := by
    simp only [LReal, zero_div, Complex.Gamma_zero, mul_zero]
  have hCplx : LComplex 0 = 0 := by
    simp only [LComplex, Complex.Gamma_zero, mul_zero]
  rw [ZInfty, hReal, hCplx]
  by_cases hR : nrRealPlaces K = 0
  case pos =>
    have hC : Not (nrComplexPlaces K = 0) := by omega
    simp only [zero_pow hC, mul_zero, inv_zero]
  case neg =>
    simp only [zero_pow hR, mul_zero, zero_mul, inv_zero]

end DedekindZeta
