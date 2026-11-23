import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Robin1984.GRH.DedekindIntegratedTailBridge

/-!
# Mellin formulas for the Dedekind primitive tail

Compute the actual tail transform from Chebyshev partial summation. Absolute convergence also gives the transform of a weighted series of complex powers.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Mellin transform of the Chebyshev primitive and absolutely summable power series.
- Formalization note: Reuse the initial Dedekind transform and interchange the spectral sum with integration using summable integral norms.
- Content basis: Mellin partial summation and the countable series integrability estimate.
- Dependency status: Optional GRH extension and existing Dedekind analytic providers.
-/

open Filter MeasureTheory NumberField Set
open Filter MeasureTheory Set

namespace Robin1984.GRH

open DedekindZeta

/-- The weighted actual primitive tail has the divided-difference Mellin transform. -/
theorem integral_dedekindPrimitiveTail_cpow (K : Type*) [Field K] [NumberField K]
    {a : Real} (ha : (a : Complex) = -(logDeriv (entirePoleFreeDedekindZeta K) 1 + 1))
    {s : Complex} (hs : 1 < s.re) :
    let mu := volume.restrict (Ioi (1 : Real))
    let T := fun x : Real => (x : Complex) ^ (-s) *
      (primitiveTail (dedekindChebyshevErrorRatio K) a x : Complex)
    And (Integrable T mu)
      (integral mu T = -(((logDeriv (entirePoleFreeDedekindZeta K) s + 1) / s) -
        (logDeriv (entirePoleFreeDedekindZeta K) 1 + 1)) / (1 - s)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let g := dedekindChebyshevErrorRatio K
  let G := fun x : Real => (g x : Complex)
  let W := fun x : Real => (x : Complex) ^ (-s) * ((a : Complex) - primitiveFromOne G x)
  have hG : Measurable G :=
    Complex.continuous_ofReal.measurable.comp (measurable_dedekindChebyshevErrorRatio K)
  have h := dedekindChebyshevErrorRatio_mellin_and_integrable K hs
  have hMellin := integral_primitiveTail_cpow hG (a : Complex) s hs h.1
  have hEq (x : Real) :
      (primitiveTail g a x : Complex) = (a : Complex) - primitiveFromOne G x := by
    rw [primitiveTail, Complex.ofReal_sub, primitiveFromOne, integral_complex_ofReal, realPrimitiveFromOne]
  have hW : (fun x : Real => (x : Complex) ^ (-s) * (primitiveTail g a x : Complex)) = W := by
    funext x
    rw [hEq]
  change And (Integrable (fun x : Real => (x : Complex) ^ (-s) *
    (primitiveTail g a x : Complex)) mu) (integral mu (fun x : Real => (x : Complex) ^ (-s) *
    (primitiveTail g a x : Complex)) = _)
  rw [hW]
  refine And.intro hMellin.1 ?_
  rw [hMellin.2, h.2, actualDedekindError_logDeriv_identity K hs, ha]
  ring

/-- Summable weights and the common real-part bound justify the Mellin transform term by term. -/
theorem integrable_integral_tsum_spectralMellin {I : Type*} [Countable I]
    (rho : I -> Complex) (b : I -> Complex) {s : Complex}
    (hs : 1 < s.re) (hRho : forall i, (rho i).re <= 1 / 2)
    (hSum : Summable fun i => norm (b i)) :
    let mu := volume.restrict (Ioi (1 : Real))
    let Z := fun x : Real => (x : Complex) ^ (-s) *
      tsum (fun i => b i * (x : Complex) ^ (rho i - 1))
    And (Integrable Z mu)
      (integral mu Z = tsum (fun i => b i / (s - rho i))) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let a : Real := 1 / 2 - s.re - 1
  let W := fun x : Real => x ^ a
  let F (i : I) (x : Real) := b i * (x : Complex) ^ (rho i - s - 1)
  have ha : a < -1 := by dsimp [a]; linarith
  have hW : Integrable W mu := integrableOn_Ioi_rpow_of_lt ha zero_lt_one
  have hE (i : I) : (rho i - s - 1).re <= a := by
    simp only [a, Complex.sub_re, Complex.one_re]
    linarith [hRho i]
  have hF (i : I) : Integrable (F i) mu :=
    (integrableOn_Ioi_cpow_of_lt ((hE i).trans_lt ha) zero_lt_one).const_mul (b i)
  have hNorm (i : I) : Filter.EventuallyLE (ae mu) (fun x => norm (F i x))
      (fun x => norm (b i) * W x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    change norm (b i * (x : Complex) ^ (rho i - s - 1)) <= norm (b i) * x ^ a
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx.le (hE i)) (norm_nonneg _)
  have hInt : Summable (fun i => integral mu (fun x => norm (F i x))) := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg (F i x)))
      (fun i => ?_) (hSum.mul_right (integral mu W))
    rw [<- integral_const_mul]
    exact integral_mono_ae (hF i).norm (hW.const_mul (norm (b i))) (hNorm i)
  have hEq : Filter.EventuallyEq (ae mu) (fun x : Real => tsum (fun i => F i x))
      (fun x => (x : Complex) ^ (-s) * tsum (fun i => b i * (x : Complex) ^ (rho i - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : Not ((x : Complex) = 0) := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
    rw [<- tsum_mul_left]
    apply tsum_congr
    intro i
    change b i * (x : Complex) ^ (rho i - s - 1) =
      (x : Complex) ^ (-s) * (b i * (x : Complex) ^ (rho i - 1))
    rw [show rho i - s - 1 = -s + (rho i - 1) by ring, Complex.cpow_add _ _ hx0]
    ring
  refine And.intro ((integrable_tsum_complex_of_norm_integrals hF hInt).congr hEq) ?_
  change integral mu
    (fun x : Real => (x : Complex) ^ (-s) * tsum (fun i => b i * (x : Complex) ^ (rho i - 1))) = _
  rw [<- integral_congr_ae hEq, <- integral_tsum_of_summable_integral_norm hF hInt]
  apply tsum_congr
  intro i
  change integral mu (fun x : Real => b i * (x : Complex) ^ (rho i - s - 1)) = _
  rw [integral_const_mul, integral_Ioi_cpow_of_lt ((hE i).trans_lt ha) zero_lt_one,
    Complex.ofReal_one, Complex.one_cpow,
    show rho i - s - 1 + 1 = -(s - rho i) by ring, neg_div_neg_eq]
  ring

private theorem primitive_inv_eq_log {x : Real} (hx : 1 < x) :
    primitiveFromOne (fun t : Real => Inv.inv (t : Complex)) x = (Real.log x : Complex) := by
  rw [primitiveFromOne, <- integral_Ioc_eq_integral_Ioo, <- intervalIntegral.integral_of_le hx.le]
  simp_rw [<- Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal, integral_inv_of_pos zero_lt_one (zero_lt_one.trans hx), div_one]

/-- The Mellin transform of the logarithm on the tail, obtained from the primitive of the reciprocal. -/
theorem integral_cpow_log_from_one {s : Complex} (hs : 1 < s.re) :
    let mu := volume.restrict (Ioi (1 : Real))
    let f := fun x : Real => (x : Complex) ^ (-s - 1) * (Real.log x : Complex)
    And (Integrable f mu) (integral mu f = 1 / s ^ (2 : Nat)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let f := fun x : Real => Inv.inv (x : Complex)
  have hMeas : Measurable f := Complex.continuous_ofReal.measurable.inv
  have hsA : 1 < (s + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hRe : (-s - 1).re < -1 := by
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hPow : IntegrableOn (fun x : Real => (x : Complex) ^ (-s - 1)) (Ioi (1 : Real)) :=
    integrableOn_Ioi_cpow_of_lt hRe zero_lt_one
  have hEq : Filter.EventuallyEq (ae mu)
      (fun x : Real => (x : Complex) ^ (-s - 1))
      (fun x => (x : Complex) ^ (1 - (s + 1)) * f x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
    dsimp [f]
    rw [show Inv.inv (x : Complex) = (x : Complex) ^ (-(1 : Complex)) by
      rw [Complex.cpow_neg, Complex.cpow_one], <- Complex.cpow_add _ _ hx0]
    congr 2
    ring
  have hi := integral_primitive_cpow hMeas (s + 1) hsA (hPow.congr hEq)
  have hModel : Filter.EventuallyEq (ae mu)
      (fun x : Real => (x : Complex) ^ (-(s + 1)) * primitiveFromOne f x)
      (fun x => (x : Complex) ^ (-s - 1) * (Real.log x : Complex)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [primitive_inv_eq_log hx, show -(s + 1) = -s - 1 by ring]
  refine And.intro (hi.1.congr hModel) ?_
  change integral mu (fun x : Real => (x : Complex) ^ (-s - 1) * (Real.log x : Complex)) = _
  rw [<- integral_congr_ae hModel, hi.2, <- integral_congr_ae hEq,
    integral_Ioi_cpow_of_lt hRe zero_lt_one, Complex.ofReal_one, Complex.one_cpow,
    show -s - 1 + 1 = -s by ring, neg_div_neg_eq, add_sub_cancel_right]
  rw [pow_two, div_div]

end Robin1984.GRH
