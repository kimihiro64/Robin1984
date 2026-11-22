import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic.Ring

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Change of measure by a nonnegative density in the Mellin transform.
- Formalization note: The observable is the real logarithm on a restricted measure, so the Mellin exponent is expressed as the moment generating parameter.
- PROVENANCE-END
-/

/-!
# A positive measure for a tail Mellin transform

Multiplying the restricted Lebesgue measure by a nonnegative tail density
realizes the real Mellin transform as a moment generating function of log.
-/

open MeasureTheory ProbabilityTheory Set

namespace Robin1984.GRH

private noncomputable def tailDensity (F : Real -> Real) (centre x : Real) : NNReal :=
  (F x * Real.exp ((-centre - 1) * Real.log x)).toNNReal

private theorem measurable_tailDensity {F : Real -> Real} (hF : Measurable F)
    (centre : Real) : Measurable (tailDensity F centre) :=
  (hF.mul (Real.continuous_exp.measurable.comp
    (measurable_const.mul Real.measurable_log))).real_toNNReal

/-- A measure whose density agrees with the weighted tail on its
nonnegative domain. -/
noncomputable def positiveMellinMeasure (F : Real -> Real) (cutoff centre : Real) :
    Measure Real :=
  (volume.restrict (Ioi cutoff)).withDensity (fun x => (tailDensity F centre x : ENNReal))

private theorem ae_cutoff_lt (cutoff : Real) :
    Filter.Eventually (fun x : Real => cutoff < x) (ae (volume.restrict (Ioi cutoff))) :=
  ae_restrict_mem measurableSet_Ioi

/-- The logarithm is nonnegative on the tail starting at a cutoff at least one. -/
theorem ae_nonneg_log_positiveMellinMeasure (F : Real -> Real) {cutoff : Real}
    (hCutoff : 1 <= cutoff) (centre : Real) :
    Filter.Eventually (fun x => 0 <= Real.log x) (ae (positiveMellinMeasure F cutoff centre)) := by
  apply (withDensity_absolutelyContinuous (volume.restrict (Ioi cutoff))
    (fun x => (tailDensity F centre x : ENNReal))).ae_le
  filter_upwards [ae_cutoff_lt cutoff] with x hx
  exact Real.log_nonneg (hCutoff.trans hx.le)

private theorem ae_density_mul_exp {F : Real -> Real} {cutoff : Real} (hCutoff : 1 <= cutoff)
    (hF : forall x, cutoff < x -> 0 <= F x) (centre t : Real) :
    Filter.EventuallyEq (ae (volume.restrict (Ioi cutoff)))
      (fun x => (tailDensity F centre x : Real) * Real.exp (t * Real.log x))
      (fun x => F x * x ^ (t - centre - 1)) := by
  filter_upwards [ae_cutoff_lt cutoff] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one (hCutoff.trans_lt hx)
  rw [tailDensity, Real.coe_toNNReal _ (mul_nonneg (hF x hx) (Real.exp_pos _).le),
    Real.rpow_def_of_pos hx0, mul_assoc, <- Real.exp_add]
  congr 2
  ring

/-- The real exponential moment is integrable exactly where the Mellin
integrand is integrable on the tail. -/
theorem mem_integrableExpSet_positiveMellinMeasure_iff {F : Real -> Real}
    (hMeas : Measurable F) {cutoff : Real} (hCutoff : 1 <= cutoff)
    (hF : forall x, cutoff < x -> 0 <= F x) (centre t : Real) :
    Membership.mem (integrableExpSet Real.log (positiveMellinMeasure F cutoff centre)) t <->
      Integrable (fun x => F x * x ^ (t - centre - 1)) (volume.restrict (Ioi cutoff)) := by
  change Integrable (fun x => Real.exp (t * Real.log x))
      ((volume.restrict (Ioi cutoff)).withDensity (fun x => (tailDensity F centre x : ENNReal))) <-> _
  rw [integrable_withDensity_iff_integrable_coe_smul (measurable_tailDensity hMeas centre)]
  simpa only [smul_eq_mul] using integrable_congr (ae_density_mul_exp hCutoff hF centre t)

/-- The value of the moment generating function is the real tail Mellin integral. -/
theorem mgf_log_positiveMellinMeasure {F : Real -> Real} (hMeas : Measurable F)
    {cutoff : Real} (hCutoff : 1 <= cutoff) (hF : forall x, cutoff < x -> 0 <= F x)
    (centre t : Real) :
    mgf Real.log (positiveMellinMeasure F cutoff centre) t =
      integral (volume.restrict (Ioi cutoff)) (fun x => F x * x ^ (t - centre - 1)) := by
  rw [mgf, positiveMellinMeasure,
    integral_withDensity_eq_integral_smul (measurable_tailDensity hMeas centre)]
  simpa only [NNReal.smul_def, smul_eq_mul] using
    integral_congr_ae (ae_density_mul_exp hCutoff hF centre t)

/-- The complex moment generating function is the complex tail Mellin integral. -/
theorem complexMGF_log_positiveMellinMeasure {F : Real -> Real} (hMeas : Measurable F)
    {cutoff : Real} (hCutoff : 1 <= cutoff) (hF : forall x, cutoff < x -> 0 <= F x)
    (centre : Real) (z : Complex) :
    complexMGF Real.log (positiveMellinMeasure F cutoff centre) z =
      integral (volume.restrict (Ioi cutoff))
        (fun x : Real => (F x : Complex) * (x : Complex) ^ (z - (centre : Complex) - 1)) := by
  rw [complexMGF, positiveMellinMeasure,
    integral_withDensity_eq_integral_smul (measurable_tailDensity hMeas centre)]
  apply integral_congr_ae
  filter_upwards [ae_cutoff_lt cutoff] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one (hCutoff.trans_lt hx)
  change ((tailDensity F centre x : Real) : Complex) *
    Complex.exp (z * (Real.log x : Complex)) =
      (F x : Complex) * (x : Complex) ^ (z - (centre : Complex) - 1)
  rw [tailDensity, Real.coe_toNNReal _ (mul_nonneg (hF x hx) (Real.exp_pos _).le),
    Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx0.ne'),
    <- Complex.ofReal_log hx0.le, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_one, mul_assoc, <- Complex.exp_add]
  congr 2
  ring

end Robin1984.GRH
