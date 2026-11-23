import Mathlib.MeasureTheory.Function.JacobianOneDim
import Robin1984.GRH.DedekindIntegratedTailBridge
import Robin1984.GRH.DedekindLineBridge

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The exponential change of variables in the Mellin transform of the Dedekind Chebyshev error.
- Formalization note: The logarithmic chart for the Dedekind Chebyshev error.
- PROVENANCE-END
-/

/-!
# The logarithmic chart for the Dedekind Chebyshev error

The weighted Mellin transform becomes a Laplace transform on the
positive real axis. Finite intervals in that chart give the exact
primitive needed by the signed improper-tail criterion.
-/

open Filter MeasureTheory NumberField Robin1984.GRH Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

/-- The Dedekind error density multiplied by the Jacobian of the
exponential chart. -/
noncomputable def dedekindLogErrorProfile (t : Real) : Complex :=
  (Real.exp t : Complex) * (dedekindChebyshevErrorRatio K (Real.exp t) : Complex)

theorem measurable_dedekindLogErrorProfile : Measurable (dedekindLogErrorProfile K) :=
  (Complex.continuous_ofReal.measurable.comp Real.continuous_exp.measurable).mul
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_dedekindChebyshevErrorRatio K).comp Real.continuous_exp.measurable))

private theorem integral_exp_chart (D : Set Real) (hD : MeasurableSet D)
    (g : Real -> Complex) :
    integral (volume.restrict (Real.exp '' D)) g =
      integral (volume.restrict D) (fun t : Real => (Real.exp t : Complex) * g (Real.exp t)) := by
  rw [integral_image_eq_integral_abs_deriv_smul hD
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    change SMul.smul (abs (Real.exp t)) (g (Real.exp t)) = (Real.exp t : Complex) * g (Real.exp t)
    rw [abs_of_pos (Real.exp_pos t)]
    exact Complex.real_smul)

private theorem exp_image_positive : Real.exp '' Ioi (0 : Real) = Ioi (1 : Real) := by
  ext x
  constructor
  case mp =>
    intro hx
    choose t ht using hx
    rw [<- ht.2]
    change 1 < Real.exp t
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr ht.1
  case mpr =>
    intro hx
    exact Exists.intro (Real.log x)
      (And.intro (Real.log_pos hx) (Real.exp_log (zero_lt_one.trans hx)))

private theorem exp_image_interval (T : Real) :
    Real.exp '' Ioo (0 : Real) T = Ioo 1 (Real.exp T) := by
  ext x
  constructor
  case mp =>
    intro hx
    choose t ht using hx
    rw [<- ht.2]
    exact And.intro
      (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr ht.1.1)
      (Real.exp_lt_exp.mpr ht.1.2)
  case mpr =>
    intro hx
    have hL : Real.exp (Real.log x) = x := Real.exp_log (zero_lt_one.trans hx.1)
    exact Exists.intro (Real.log x) (And.intro
      (And.intro (Real.log_pos hx.1) (Real.exp_lt_exp.mp (hL.trans_lt hx.2))) hL)

private theorem exp_cpow_neg (t : Real) (z : Complex) :
    ((Real.exp t : Real) : Complex) ^ (-z) = Complex.exp (-z * (t : Complex)) := by
  have hPos : 0 < Real.exp t := Real.exp_pos t
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hPos.ne') (-z),
    <- Complex.ofReal_log hPos.le, Real.log_exp, mul_comm (t : Complex)]

/-- The real-logarithm coordinate identifies the actual Chebyshev
Mellin transform with the Laplace transform required by Newman. -/
theorem dedekindLogErrorProfile_laplace {z : Complex} (hz : 0 < z.re) :
    -(logDeriv (entirePoleFreeDedekindZeta K) (z + 1) + 1) / (z + 1) =
      integral (volume.restrict (Ici (0 : Real)))
        (fun t : Real => dedekindLogErrorProfile K t * Complex.exp (-z * (t : Complex))) := by
  have hs : 1 < (z + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith only [hz]
  have hInitial := (dedekindChebyshevErrorRatio_mellin K hs).trans
    (actualDedekindError_logDeriv_identity K hs)
  rw [show 1 - (z + 1) = -z by ring] at hInitial
  rw [<- hInitial, integral_Ici_eq_integral_Ioi, <- exp_image_positive,
    integral_exp_chart (Ioi 0) measurableSet_Ioi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    change (Real.exp t : Complex) *
        ((Real.exp t : Complex) ^ (-z) * (dedekindChebyshevErrorRatio K (Real.exp t) : Complex)) =
      dedekindLogErrorProfile K t * Complex.exp (-z * (t : Complex))
    rw [exp_cpow_neg, dedekindLogErrorProfile]
    ring)

/-- Integrate the logarithmic profile on a finite interval to obtain the
actual Chebyshev primitive at the exponential endpoint. -/
theorem intervalIntegral_dedekindLogErrorProfile {T : Real} (hT : 0 <= T) :
    intervalIntegral (dedekindLogErrorProfile K) 0 T volume =
      (realPrimitiveFromOne (dedekindChebyshevErrorRatio K) (Real.exp T) : Complex) := by
  rw [intervalIntegral.integral_of_le hT, integral_Ioc_eq_integral_Ioo, realPrimitiveFromOne,
    <- integral_complex_ofReal, <- exp_image_interval T, integral_exp_chart (Ioo 0 T) measurableSet_Ioo]
  rfl

end DedekindZeta
