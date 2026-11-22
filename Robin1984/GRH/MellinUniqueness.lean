import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic.Ring

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Uniqueness of the Fourier transform of a finite measure after taking the logarithm.
- Formalization note: The signed integrable Mellin density is split into positive and negative measures, and the logarithmic pushforward is inverted on the positive tail.
- PROVENANCE-END
-/

/-!
# Uniqueness on a vertical Mellin line

After the Mellin weight is absorbed into an integrable signed density,
its vertical-line transform is the Fourier transform of the logarithmic
pushforward.
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace Robin1984.GRH

private noncomputable def logFourierKernel (t x : Real) : Complex :=
  Complex.exp ((t : Complex) * Complex.I * (Real.log x : Complex))

private theorem measurable_logFourierKernel (t : Real) : Measurable (logFourierKernel t) :=
  Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp Real.measurable_log))

private theorem norm_logFourierKernel (t x : Real) : norm (logFourierKernel t x) = 1 := by
  simp only [logFourierKernel, Complex.norm_exp, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, Real.exp_zero]

private theorem toNNReal_sub_neg_toNNReal (x : Real) :
    (x.toNNReal : Real) - ((-x).toNNReal : Real) = x := by
  rcases le_total 0 x with h | h
  case inl =>
    rw [Real.coe_toNNReal _ h, Real.toNNReal_of_nonpos (neg_nonpos.mpr h)]
    simp
  case inr =>
    rw [Real.toNNReal_of_nonpos h, Real.coe_toNNReal _ (neg_nonneg.mpr h)]
    simp

private theorem integrable_density_mul_logFourierKernel {d : Real -> NNReal}
    (hMeas : Measurable d) {mu : Measure Real}
    (hInt : Integrable (fun x => (d x : Real)) mu) (t : Real) :
    Integrable (fun x => ((d x : Real) : Complex) * logFourierKernel t x) mu := by
  have hCast : Measurable (fun x => ((d x : Real) : Complex)) :=
    Complex.continuous_ofReal.measurable.comp (NNReal.continuous_coe.measurable.comp hMeas)
  apply hInt.mono' ((hCast.mul (measurable_logFourierKernel t)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change norm (((d x : Real) : Complex) * logFourierKernel t x) <= (d x : Real)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (d x).coe_nonneg,
      norm_logFourierKernel, mul_one])

/-- A real integrable density whose logarithmic Fourier transform is zero
vanishes almost everywhere on the positive tail. -/
private theorem ae_zero_of_logFourierIntegral_zero {u : Real -> Real} (hMeas : Measurable u)
    (hInt : Integrable u (volume.restrict (Ioi (1 : Real))))
    (hZero : forall t : Real,
      integral (volume.restrict (Ioi (1 : Real)))
        (fun x => (u x : Complex) * logFourierKernel t x) = 0) :
    Filter.EventuallyEq (ae (volume.restrict (Ioi (1 : Real)))) u (fun _ => 0) := by
  let nu := volume.restrict (Ioi (1 : Real))
  let pos := fun x : Real => (u x).toNNReal
  let neg := fun x : Real => (-u x).toNNReal
  let dens := fun d : Real -> NNReal => nu.withDensity (fun x => (d x : ENNReal))
  have hPosMeas : Measurable pos := hMeas.real_toNNReal
  have hNegMeas : Measurable neg := hMeas.neg.real_toNNReal
  have hPosInt : Integrable (fun x => (pos x : Real)) nu := hInt.real_toNNReal
  have hNegInt : Integrable (fun x => (neg x : Real)) nu := hInt.neg.real_toNNReal
  have hFinite {d : Real -> NNReal} (hd : Integrable (fun x => (d x : Real)) nu) :
      IsFiniteMeasure (dens d) := by
    apply isFiniteMeasure_withDensity
    rw [lintegral_coe_eq_integral _ hd]
    exact ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure (dens pos) := hFinite hPosInt
  let _ : IsFiniteMeasure (dens neg) := hFinite hNegInt
  have hChar (d : Real -> NNReal) (hd : Measurable d) (t : Real) :
      charFun ((dens d).map Real.log) t =
        integral nu (fun x => ((d x : Real) : Complex) * logFourierKernel t x) := by
    rw [<- complexMGF_id_mul_I, complexMGF_id_map Real.measurable_log.aemeasurable, complexMGF]
    change integral (nu.withDensity (fun x => (d x : ENNReal)))
      (fun x => logFourierKernel t x) = _
    rw [integral_withDensity_eq_integral_smul hd]
    rfl
  have hMap : (dens pos).map Real.log = (dens neg).map Real.log := by
    apply Measure.ext_of_charFun
    funext t
    rw [hChar pos hPosMeas, hChar neg hNegMeas]
    apply sub_eq_zero.mp
    rw [<- integral_sub (integrable_density_mul_logFourierKernel hPosMeas hPosInt t)
      (integrable_density_mul_logFourierKernel hNegMeas hNegInt t)]
    refine (integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))).trans (hZero t)
    rw [<- sub_mul, <- Complex.ofReal_sub, toNNReal_sub_neg_toNNReal]
  have hBack (d : Real -> NNReal) : ((dens d).map Real.log).map Real.exp = dens d := by
    rw [Measure.map_map Real.continuous_exp.measurable Real.measurable_log]
    have hSupport : Filter.Eventually (fun x : Real => 1 < x) (ae nu) :=
      ae_restrict_mem measurableSet_Ioi
    have hLogExp : Filter.EventuallyEq (ae (dens d)) (Real.exp.comp Real.log) id :=
      (withDensity_absolutelyContinuous nu (fun x => (d x : ENNReal))).ae_le
        (hSupport.mono (fun x hx => Real.exp_log (zero_lt_one.trans hx)))
    rw [Measure.map_congr hLogExp, Measure.map_id]
  have hDens : dens pos = dens neg := by
    rw [<- hBack pos, hMap, hBack neg]
  have hValues : Filter.EventuallyEq (ae nu) (fun x => (pos x : ENNReal))
      (fun x => (neg x : ENNReal)) :=
    (withDensity_eq_iff_of_sigmaFinite hPosMeas.coe_nnreal_ennreal.aemeasurable
      hNegMeas.coe_nnreal_ennreal.aemeasurable).mp hDens
  filter_upwards [hValues] with x hx
  have hPN : pos x = neg x := ENNReal.coe_injective hx
  calc
    u x = (pos x : Real) - (neg x : Real) := (toNNReal_sub_neg_toNNReal (u x)).symm
    _ = 0 := by rw [hPN, sub_self]

/-- The Mellin transform on one vertical line determines an integrable
real density almost everywhere on the tail. -/
theorem ae_zero_of_verticalMellin_eq_zero {u : Real -> Real} (hMeas : Measurable u) (c : Real)
    (hInt : Integrable (fun x : Real => u x * x ^ (-c - 1))
      (volume.restrict (Ioi (1 : Real))))
    (hZero : forall t : Real, integral (volume.restrict (Ioi (1 : Real)))
      (fun x : Real => (u x : Complex) *
        (x : Complex) ^ (-(c : Complex) - 1 + (t : Complex) * Complex.I)) = 0) :
    Filter.EventuallyEq (ae (volume.restrict (Ioi (1 : Real)))) u (fun _ => 0) := by
  let v : Real -> Real := fun x => u x * Real.exp ((-c - 1) * Real.log x)
  have hvMeas : Measurable v := hMeas.mul
    (Real.continuous_exp.measurable.comp (measurable_const.mul Real.measurable_log))
  have hIntOn : IntegrableOn (fun x : Real => u x * x ^ (-c - 1)) (Ioi (1 : Real)) := hInt
  have hvInt : Integrable v (volume.restrict (Ioi (1 : Real))) := by
    refine hIntOn.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := zero_lt_one.trans hx
    change u x * x ^ (-c - 1) = u x * Real.exp ((-c - 1) * Real.log x)
    rw [Real.rpow_def_of_pos hx0]
    congr 2
    ring
  have hvZero (t : Real) : integral (volume.restrict (Ioi (1 : Real)))
      (fun x : Real => (v x : Complex) * logFourierKernel t x) = 0 := by
    refine (setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)).trans (hZero t)
    have hx0 : 0 < x := zero_lt_one.trans hx
    change ((u x * Real.exp ((-c - 1) * Real.log x) : Real) : Complex) *
      Complex.exp ((t : Complex) * Complex.I * (Real.log x : Complex)) =
      (u x : Complex) * (x : Complex) ^ (-(c : Complex) - 1 + (t : Complex) * Complex.I)
    rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, <- Complex.exp_add,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx0.ne'),
      <- Complex.ofReal_log hx0.le, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_neg, Complex.ofReal_one]
    congr 2
    ring
  exact (ae_zero_of_logFourierIntegral_zero hvMeas hvInt hvZero).mono (fun x hx =>
    (mul_eq_zero.mp hx).resolve_right (Real.exp_pos _).ne')

end Robin1984.GRH
