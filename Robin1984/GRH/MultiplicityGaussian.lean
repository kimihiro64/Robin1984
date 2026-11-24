import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Robin1984.GRH.MultiplicityFourierSeries

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Fourier transform of a Gaussian and its derivatives.
- Formalization note: The explicit kernel is integrable, its multiplier cancels the triangular denominator, and convolution preserves the vanishing error.
- PROVENANCE-END
-/

/-!
# Gaussian smoothing of the triangular spectrum

The explicit kernel is integrable, its multiplier cancels the triangular denominator, and convolution preserves the vanishing error.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Filter MeasureTheory
open scoped Topology

/-- The normalized Gaussian with Fourier weight exp(-a * gamma^2). -/
def multiplicityGaussian (a v : Real) : Real :=
  Real.exp (-(v ^ 2) / (4 * a)) / Real.sqrt (4 * Real.pi * a)

/-- The Gaussian kernel whose multiplier includes the triangular denominator. -/
def multiplicityGaussianKernel (a v : Real) : Real :=
  (v ^ 2 / (4 * a ^ 2) - v / a + 3 / 4 - 1 / (2 * a)) * multiplicityGaussian a v

def gaussianAtFrequency (gamma : Real) : Real -> Complex := fun v =>
  Complex.exp ((-(gamma * v) : Real) * Complex.I)

private theorem fourier_gaussian_at_frequency {a : Real} (ha : 0 < a) (gamma : Real) :
    FourierTransform.fourier (fun v : Real => (multiplicityGaussian a v : Complex))
      (gamma / (2 * Real.pi)) = Complex.exp ((-a * gamma ^ 2 : Real) : Complex) := by
  let b : Real := 1 / (4 * a)
  let d : Real := Real.sqrt (4 * Real.pi * a)
  have hb : 0 < b := by dsimp [b]; positivity
  have hD : 0 < d := by dsimp [d]; positivity
  have hA : Not (a = 0) := ha.ne'
  have hPi : Not (Real.pi = 0) := Real.pi_pos.ne'
  have hC : Not ((a : Complex) = 0) := Complex.ofReal_ne_zero.mpr hA
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = (integral volume (fun v : Real =>
      Complex.exp (Complex.I * (-gamma : Real) * (v : Complex)) *
        Complex.exp (-(b : Complex) * (v : Complex) ^ 2))) / (d : Complex) := by
      rw [<- integral_div]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
      have hv : -2 * Real.pi * v * (gamma / (2 * Real.pi)) = -(gamma * v) := by
        field_simp [hPi]
      dsimp only
      rw [hv]
      unfold multiplicityGaussian
      simp only [smul_eq_mul, Complex.ofReal_div, Complex.ofReal_exp,
        Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
      have h1 : -((gamma : Complex) * (v : Complex)) * Complex.I =
          Complex.I * -(gamma : Complex) * (v : Complex) := by ring
      have h2 : -(v : Complex) ^ 2 / (4 * (a : Complex)) =
          -(b : Complex) * (v : Complex) ^ 2 := by
        simp only [b, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul,
          Complex.ofReal_ofNat]
        ring
      rw [h1, h2, mul_div_assoc]
    _ = Complex.exp ((-a * gamma ^ 2 : Real) : Complex) := by
      rw [fourierIntegral_gaussian (b := (b : Complex))
        (by simpa only [Complex.ofReal_re] using hb)]
      have hdReal : Real.pi / b = 4 * Real.pi * a := by
        dsimp only [b]
        field_simp [hA]
      have hd : ((Real.pi : Complex) / (b : Complex)) ^ (1 / 2 : Complex) = (d : Complex) := by
        unfold d
        rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity), <- hdReal]
        simp
      have hExp : -(((-gamma : Real) : Complex) ^ 2) / (4 * (b : Complex)) =
          ((-a * gamma ^ 2 : Real) : Complex) := by
        simp only [b, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul,
          Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_pow]
        field_simp [hC]
      rw [hd, hExp, mul_comm, mul_div_assoc, div_self (Complex.ofReal_ne_zero.mpr hD.ne'), mul_one]

private theorem hasDerivAt_multiplicityGaussian (a v : Real) :
    HasDerivAt (multiplicityGaussian a) (-(v / (2 * a)) * multiplicityGaussian a v) v := by
  let b : Real := 1 / (4 * a)
  let d : Real := Real.sqrt (4 * Real.pi * a)
  have hId : HasDerivAt (fun t : Real => t) 1 v := hasDerivAt_id v
  have hSq : HasDerivAt (fun t : Real => t ^ 2) (2 * v) v := by
    have h := hId.pow 2
    change HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * v ^ (2 - 1) * 1) v at h
    simpa only [Nat.reduceSub, pow_one, mul_one] using h
  have hf := ((hSq.const_mul (-b)).exp).div_const d
  change HasDerivAt (fun t : Real => Real.exp (-b * t ^ 2) / d)
    (Real.exp (-b * v ^ 2) * (-b * (2 * v)) / d) v at hf
  have hFun : (fun t : Real => Real.exp (-b * t ^ 2) / d) =
      multiplicityGaussian a := by
    funext t
    unfold multiplicityGaussian
    have hExp : -b * t ^ 2 = -(t ^ 2) / (4 * a) := by
      simp only [b, div_eq_mul_inv, one_mul]
      ring
    rw [hExp]
  have hCoeff : -b * (2 * v) = -(v / (2 * a)) := by
    by_cases ha : a = 0
    case pos => simp [ha, b]
    case neg =>
      unfold b
      field_simp [ha]
      ring
  rw [hCoeff, mul_comm (Real.exp _) _, mul_div_assoc] at hf
  change HasDerivAt (fun t : Real => Real.exp (-b * t ^ 2) / d)
    (-(v / (2 * a)) * ((fun t : Real => Real.exp (-b * t ^ 2) / d) v)) v at hf
  rwa [hFun] at hf

private def gaussianFirst (a v : Real) : Real :=
  -(v / (2 * a)) * multiplicityGaussian a v

private def gaussianSecond (a v : Real) : Real :=
  (v ^ 2 / (4 * a ^ 2) - 1 / (2 * a)) * multiplicityGaussian a v

private theorem hasDerivAt_gaussianFirst {a : Real} (ha : 0 < a) (v : Real) :
    HasDerivAt (gaussianFirst a) (gaussianSecond a v) v := by
  have hf := (((hasDerivAt_id v).div_const (2 * a)).neg).mul
    (hasDerivAt_multiplicityGaussian a v)
  change HasDerivAt (gaussianFirst a)
    (-(1 / (2 * a)) * multiplicityGaussian a v +
      -(v / (2 * a)) * (-(v / (2 * a)) * multiplicityGaussian a v)) v at hf
  convert hf using 1
  unfold gaussianSecond
  field_simp [ha.ne']
  ring

private theorem integrable_gaussianMoments {a : Real} (ha : 0 < a) :
    Integrable (multiplicityGaussian a) /\ Integrable (gaussianFirst a) /\
      Integrable (gaussianSecond a) := by
  let b : Real := 1 / (4 * a)
  let d : Real := Real.sqrt (4 * Real.pi * a)
  let E (v : Real) := Real.exp (-b * v ^ 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have h0 : Integrable E := integrable_exp_neg_mul_sq hb
  have h1 : Integrable (fun v : Real => v * E v) := integrable_mul_exp_neg_mul_sq hb
  have h2 : Integrable (fun v : Real => v ^ 2 * E v) := by
    simpa only [E, Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (show (-1 : Real) < 2 by norm_num))
  have hGauss (v : Real) : multiplicityGaussian a v = E v / d := by
    unfold multiplicityGaussian E b d
    simp only [div_eq_mul_inv, one_mul]
    ring_nf
  have hFirst (v : Real) :
      gaussianFirst a v = -(1 / (2 * a) / d) * (v * E v) := by
    unfold gaussianFirst
    rw [hGauss]
    simp only [div_eq_mul_inv, one_mul]
    ring
  have hSecond (v : Real) : gaussianSecond a v =
      (1 / (4 * a ^ 2) / d) * (v ^ 2 * E v) - (1 / (2 * a) / d) * E v := by
    unfold gaussianSecond
    rw [hGauss]
    simp only [div_eq_mul_inv, one_mul]
    ring
  refine And.intro ?_ (And.intro ?_ ?_)
  case refine_1 =>
    rw [funext hGauss]
    exact h0.div_const d
  case refine_2 =>
    rw [funext hFirst]
    exact h1.const_mul _
  case refine_3 =>
    rw [funext hSecond]
    exact (h2.const_mul _).sub (h0.const_mul _)

/-- The angular-frequency multiplier of the kernel used in the arithmetic
multiplicity test. -/
theorem multiplicityGaussianKernel_fourier {a : Real} (ha : 0 < a) (gamma : Real) :
    integral volume (fun v : Real => (multiplicityGaussianKernel a v : Complex) *
      gaussianAtFrequency gamma v) =
      (((gamma : Complex) * Complex.I + 1 / 2) *
        ((gamma : Complex) * Complex.I + 3 / 2)) *
        Complex.exp ((-a * gamma ^ 2 : Real) : Complex) := by
  let z : Complex := (gamma : Complex) * Complex.I
  let x : Real := gamma / (2 * Real.pi)
  let e : Real -> Complex := gaussianAtFrequency gamma
  let G (v : Real) : Complex := (multiplicityGaussian a v : Complex)
  let D (v : Real) : Complex := (gaussianFirst a v : Complex)
  let Q (v : Real) : Complex := (gaussianSecond a v : Complex)
  have hD (v : Real) : HasDerivAt G (D v) v :=
    (hasDerivAt_multiplicityGaussian a v).ofReal_comp
  have hQ (v : Real) : HasDerivAt D (Q v) v :=
    (hasDerivAt_gaussianFirst ha v).ofReal_comp
  have hD' : deriv G = D := funext (fun v => (hD v).deriv)
  have hQ' : deriv D = Q := funext (fun v => (hQ v).deriv)
  have hGI : Integrable G :=
    Complex.ofRealCLM.integrable_comp (integrable_gaussianMoments ha).1
  have hDI : Integrable D :=
    Complex.ofRealCLM.integrable_comp (integrable_gaussianMoments ha).2.1
  have hQI : Integrable Q :=
    Complex.ofRealCLM.integrable_comp (integrable_gaussianMoments ha).2.2
  have hfD := Real.fourier_deriv hGI (fun v => (hD v).differentiableAt) (Eq.mpr (congrArg (fun f : Real -> Complex => Integrable f) hD') hDI)
  have hfQ := Real.fourier_deriv hDI (fun v => (hQ v).differentiableAt) (Eq.mpr (congrArg (fun f : Real -> Complex => Integrable f) hQ') hQI)
  have hPi : Not (Real.pi = 0) := Real.pi_pos.ne'
  have hFactor : 2 * (Real.pi : Complex) * Complex.I * (x : Complex) = z := by
    unfold x z
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
    field_simp [Complex.ofReal_ne_zero.mpr hPi]
  have hx (v : Real) : -2 * Real.pi * v * x = -(gamma * v) := by
    unfold x
    field_simp [hPi]
  have hFourier (f : Real -> Complex) :
      FourierTransform.fourier f x = integral volume (fun v => e v * f v) := by
    simp only [Real.fourier_real_eq_integral_exp_smul, hx, e, gaussianAtFrequency, smul_eq_mul]
  have hPhase : Continuous e :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_id).neg).mul continuous_const)
  have hNorm (v : Real) : norm (e v) = 1 := Complex.norm_exp_ofReal_mul_I _
  have hWeighted (f : Real -> Complex) (hf : Integrable f) :
      Integrable (fun v => e v * f v) := by
    apply hf.mono (hPhase.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun v => by
      change norm (e v * f v) <= norm (f v)
      rw [norm_mul, hNorm, one_mul])
  have hDval : FourierTransform.fourier D x = z * FourierTransform.fourier G x := by
    rw [hD'] at hfD
    have h := congrFun hfD x
    simpa only [hFactor, smul_eq_mul] using h
  have hQval : FourierTransform.fourier Q x = z * FourierTransform.fourier D x := by
    rw [hQ'] at hfQ
    have h := congrFun hfQ x
    simpa only [hFactor, smul_eq_mul] using h
  have hSplit (v : Real) : multiplicityGaussianKernel a v =
      gaussianSecond a v + 2 * gaussianFirst a v + (3 / 4) * multiplicityGaussian a v := by
    unfold multiplicityGaussianKernel gaussianSecond gaussianFirst
    field_simp [ha.ne']
    ring
  let QF (v : Real) : Complex := e v * Q v
  let DF (v : Real) : Complex := 2 * (e v * D v)
  let GF (v : Real) : Complex := (3 / 4) * (e v * G v)
  have h2 : Integrable QF := hWeighted Q hQI
  have h1 : Integrable DF := (hWeighted D hDI).const_mul _
  have h0 : Integrable GF := (hWeighted G hGI).const_mul _
  calc
    _ = integral volume ((QF + DF) + GF) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
      change (multiplicityGaussianKernel a v : Complex) * e v =
        e v * Q v + 2 * (e v * D v) + (3 / 4) * (e v * G v)
      rw [hSplit]
      simp only [G, D, Q, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_ofNat]
      ring
    _ = integral volume (fun v => e v * Q v) +
        2 * integral volume (fun v => e v * D v) +
          (3 / 4) * integral volume (fun v => e v * G v) := by
      have hFull : integral volume ((QF + DF) + GF) =
          integral volume (QF + DF) + integral volume GF :=
        integral_add (h2.add h1) h0
      have hPartial : integral volume (QF + DF) = integral volume QF + integral volume DF :=
        integral_add h2 h1
      rw [hFull, hPartial]
      simp only [QF, DF, GF, integral_const_mul]
    _ = _ := by
      rw [<- hFourier Q, <- hFourier D, <- hFourier G, hQval, hDval,
        fourier_gaussian_at_frequency ha gamma]
      change z * (z * _) + 2 * (z * _) + (3 / 4) * _ =
        (z + 1 / 2) * (z + 3 / 2) * _
      ring

/-- The kernel used by the global multiplicity test is integrable. -/
theorem integrable_multiplicityGaussianKernel {a : Real} (ha : 0 < a) :
    Integrable (fun v : Real => (multiplicityGaussianKernel a v : Complex)) := by
  have h := integrable_gaussianMoments ha
  have hEq : multiplicityGaussianKernel a =
      (gaussianSecond a + (fun v => 2 * gaussianFirst a v)) +
        (fun v => (3 / 4) * multiplicityGaussian a v) := by
    funext v
    change multiplicityGaussianKernel a v =
      gaussianSecond a v + 2 * gaussianFirst a v + (3 / 4) * multiplicityGaussian a v
    unfold multiplicityGaussianKernel gaussianSecond gaussianFirst
    field_simp [ha.ne']
    ring
  have hR : Integrable (multiplicityGaussianKernel a) := by
    rw [hEq]
    exact (h.2.2.add (h.2.1.const_mul 2)).add (h.1.const_mul (3 / 4))
  exact Complex.ofRealCLM.integrable_comp hR

/-- Gaussian smoothing cancels each triangular denominator on the critical
line and leaves a Gaussian weight for each zero occurrence. -/
theorem tendsto_gaussianConvolution_sub_weightedSpectrum
    {i : Type*} [Countable i] (gamma : i -> Real) {A : Real -> Complex}
    (hMeas : Measurable A) {M : Real} (hBound : forall t, norm (A t) <= M)
    (hWeight : Summable (fun j => Inv.inv (norm
      (((1 / 2 : Complex) + (gamma j : Complex) * Complex.I) *
        ((3 / 2 : Complex) + (gamma j : Complex) * Complex.I)))))
    (hAsym : Tendsto (fun t : Real => A t - tsum (fun j =>
      Inv.inv (((1 / 2 : Complex) + (gamma j : Complex) * Complex.I) *
        ((3 / 2 : Complex) + (gamma j : Complex) * Complex.I)) *
        Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))) atTop (nhds 0))
    {a : Real} (ha : 0 < a) :
    Tendsto (fun t : Real =>
      spectralConvolution (fun v => (multiplicityGaussianKernel a v : Complex)) A t -
        tsum (fun j => (Real.exp (-a * gamma j ^ 2) : Complex) *
          Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))) atTop (nhds 0) := by
  let c (j : i) : Complex := (gamma j : Complex) * Complex.I
  let Q (j : i) : Complex := ((1 / 2 : Complex) + c j) * ((3 / 2 : Complex) + c j)
  let b (j : i) : Complex := Inv.inv (Q j)
  let k (v : Real) : Complex := (multiplicityGaussianKernel a v : Complex)
  let p (t : Real) (j : i) : Complex := b j * Complex.exp (c j * (t : Complex))
  let P (t : Real) : Complex := tsum (p t)
  have hc (j : i) : (c j).re = 0 := by simp [c, Complex.mul_re]
  have hb : Summable (fun j => norm (b j)) := by simpa only [b, norm_inv] using hWeight
  have hk : Integrable k := integrable_multiplicityGaussianKernel ha
  have hp (j : i) : Continuous (fun t : Real => p t j) :=
    continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))
  have hPMeas : Measurable P := Measurable.tsum (fun j => (hp j).measurable)
  have hNorm (j : i) (t : Real) : norm (p t j) = norm (b j) := by
    unfold p
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re, hc j]
  have hPBound (t : Real) : norm (P t) <= tsum (fun j => norm (b j)) := by
    have hs : Summable (fun j => norm (p t j)) := by simpa only [hNorm] using hb
    simpa only [hNorm] using norm_tsum_le_tsum_norm hs
  have hE : Tendsto (spectralConvolution k (fun t => A t - P t)) atTop (nhds 0) :=
    tendsto_spectralConvolution_of_tendsto_zero hk (hMeas.sub hPMeas)
      (fun t => (norm_sub_le (A t) (P t)).trans (add_le_add (hBound t) (hPBound t))) hAsym
  have hI (f : Real -> Complex) (hf : Measurable f) (C : Real) (hC : forall t, norm (f t) <= C)
      (t : Real) : Integrable (fun v : Real => k v * f (t - v)) := by
    have hFMeas : Measurable (fun v : Real => f (t - v)) :=
      hf.comp (measurable_const.sub measurable_id)
    apply (hk.norm.mul_const C).mono' (hk.aestronglyMeasurable.mul hFMeas.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun v => by
      change norm (k v * f (t - v)) <= norm (k v) * C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  have hConvolution (t : Real) : spectralConvolution k (fun v => A v - P v) t =
      spectralConvolution k A t - spectralConvolution k P t := by
    simp only [spectralConvolution, mul_sub]
    exact integral_sub (hI A hMeas M hBound t) (hI P hPMeas _ hPBound t)
  have hKMode (j : i) : angularFourierTransform k (c j) =
      Q j * (Real.exp (-a * gamma j ^ 2) : Complex) := by
    have hPhase (v : Real) : Complex.exp (-c j * (v : Complex)) = gaussianAtFrequency (gamma j) v := by
      unfold c gaussianAtFrequency
      simp only [Complex.ofReal_neg, Complex.ofReal_mul]
      congr 1
      ring
    unfold angularFourierTransform
    simp only [hPhase, k]
    simpa only [Q, c, Complex.ofReal_exp, add_comm] using
      multiplicityGaussianKernel_fourier ha (gamma j)
  have hQ0 (j : i) : Not (Q j = 0) := by
    unfold Q
    exact mul_ne_zero
      (Complex.ne_zero_of_re_pos (by norm_num [Complex.add_re, Complex.div_re, hc j]))
      (Complex.ne_zero_of_re_pos (by norm_num [Complex.add_re, Complex.div_re, hc j]))
  have hPexact (t : Real) : spectralConvolution k P t =
      tsum (fun j => (Real.exp (-a * gamma j ^ 2) : Complex) *
        Complex.exp (c j * (t : Complex))) := by
    change spectralConvolution k (fun u => tsum (fun j => b j * Complex.exp (c j * (u : Complex)))) t = _
    rw [spectralConvolution_fourierSeries b c hb hc k hk t]
    refine tsum_congr ?_
    intro j
    simp only [hKMode, b]
    rw [<- mul_assoc, mul_comm (Inv.inv (Q j)) (Q j), <- div_eq_mul_inv, div_self (hQ0 j), one_mul]
  exact hE.congr' (Filter.Eventually.of_forall (fun t => by rw [hConvolution t, hPexact t]))

end Robin1984.GRH
