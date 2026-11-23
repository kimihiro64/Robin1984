/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.Statements
import DedekindZeta.Theta
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# The higher-dimensional Gamma-integral (multiplicative Mellin over `K_ℝ`)

This module builds the higher-dimensional Gamma-integral machinery from
Neukirch, *Algebraic Number Theory*, Chapter VII §4: the *multiplicative* Mellin
transform over the Minkowski space `K_ℝ`.

The point is that the *scalar* single-variable Mellin transform of the theta series
`DedekindZeta.Theta.theta` only produces an Epstein-type zeta in the quadratic
form `⟨a,a⟩`, **not** the Dedekind zeta in `𝔑(𝔞)^{-s}`. Recovering the norm
requires integrating over the multiplicative group `K_ℝ^* = (ℝ^*)^{r₁} × (ℂ^*)^{r₂}`
against the *multiplicative* Haar measure `d^*x`, extracting `|N(x)|^s`. This is
the integral computed in the standard treatment, whose value factorises into the
archimedean L-factors `L_ℝ`, `L_ℂ` already pinned in `DedekindZeta.Statements`.

## Normalisations

We use `K_ℝ = NumberField.mixedEmbedding.mixedSpace K` and the norm map
`NumberField.mixedEmbedding.norm`, with `|N(x)| = ∏_w |x_w|^{mult w}`
(`mult = 1` at a real place, `2` at a complex place). The multiplicative Haar
measure is taken with the standard normalisation
`d^*x = ∏_{w real} dx_w/|x_w| · ∏_{w cplx} (2/π) dλ_w/|z_w|²` so that the
per-place integrals against the Gaussian evaluate to exactly `L_ℝ(s)` and
`L_ℂ(s)`:

* real place : `∫_{ℝ^*} e^{-π x²} |x|^s dx/|x| = π^{-s/2} Γ(s/2) = L_ℝ(s)`;
* complex place : `∫_{ℂ^*} e^{-2π|z|²} |z|^{2s} (2/π) dλ/|z|² = 2(2π)^{-s} Γ(s) = L_ℂ(s)`.
-/

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal

namespace DedekindZeta.GammaIntegral

open Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

/-! ## The multiplicative Minkowski space and its norm -/



open Classical in
/-- The standard multiplicative Haar measure `d^*x` on `K_ℝ^*`, written as a
density against the additive Lebesgue measure `volume` on `K_ℝ`:
`d^*x = (2/π)^{r₂} · |N(x)|^{-1} · dx`. The factor `|N(x)|^{-1} = ∏_w
|x_w|^{-mult w}` turns `dx_w` into the one-dimensional multiplicative Haar
`dx_w/|x_w|` (real) and `dλ_w/|z_w|²` (complex); the constant `(2/π)^{r₂}` is the
the standard treatment per-complex-place normalisation that pins the complex factor to `L_ℂ`.
The density vanishes on the measure-zero locus `N(x) = 0`, so the measure lives
on `K_ℝ^*`. -/
def mulHaar :=
  volume.withDensity fun x : mixedEmbedding.mixedSpace K =>
    ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹)

/-! ## The Gaussian on `K_ℝ` -/

/-- The standard Gaussian on `K_ℝ` (the standard treatment):
`g₀(x) = exp(-π ⟨x,x⟩)` with the Minkowski quadratic form
`⟨x,x⟩ = ∑_w mult w · |x_w|²` (so a complex place contributes `2|z_w|²`). This is
the `t = 1` instance of the Gaussian whose lattice sum is
`DedekindZeta.Theta.theta`. -/
def gaussian (x : mixedEmbedding.mixedSpace K) : ℝ :=
  Real.exp (-Real.pi * ∑ w : InfinitePlace K, (mult w : ℝ) * normAtPlace w x ^ 2)

/-! ## The higher-dimensional Gamma-integral (multiplicative Mellin) -/

/-- The **higher-dimensional Gamma-integral** of the standard treatment: the multiplicative
Mellin transform `∫_{K_ℝ^*} f(x) |N(x)|^s d^*x` of `f : K_ℝ → ℂ`. -/
def gammaIntegral (f : mixedEmbedding.mixedSpace K → ℂ) (s : ℂ) : ℂ :=
  ∫ x, f x * (mixedEmbedding.norm x : ℂ) ^ s ∂(mulHaar K)

/-! ## The one-dimensional (per-place) Gamma-integrals -/

/-- The one-dimensional real-place Gamma-integral
`∫_{ℝ^*} e^{-π x²} |x|^s dx/|x|`. By the standard treatment it equals `L_ℝ(s)`. -/
def gammaReal (s : ℂ) : ℂ :=
  ∫ x : ℝ, Real.exp (-Real.pi * x ^ 2) * (((|x| : ℝ) : ℂ)) ^ s
    ∂(volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹)

/-- The one-dimensional complex-place Gamma-integral
`∫_{ℂ^*} e^{-2π|z|²} |z|^{2s} (2/π) dλ/|z|²`. By the standard treatment it equals
`L_ℂ(s)`. -/
def gammaComplex (s : ℂ) : ℂ :=
  ∫ z : ℂ, Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * (‖z‖ : ℂ) ^ (2 * s)
    ∂(volume.withDensity fun z : ℂ => ENNReal.ofReal (2 / Real.pi * (‖z‖ ^ 2)⁻¹))

/-! ## Evaluation of the per-place integrals (the standard treatment) -/

open scoped Real in
/-- Complex-valued analogue of `MeasureTheory.integral_comp_abs`: the Lebesgue
integral over `ℝ` of an even-by-construction integrand `f |x|` is twice the
half-line integral.  (Mathlib's `integral_comp_abs` is stated only for
`f : ℝ → ℝ`; we need the `ℂ`-valued version for the Gaussian Mellin integrand.) -/
private theorem integral_comp_abs_complex {f : ℝ → ℂ} :
    ∫ x, f |x| = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
  have eq : ∫ x : ℝ in Set.Ioi 0, f |x| = ∫ x : ℝ in Set.Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_of_pos hx]
  by_cases hf : IntegrableOn (fun x => f |x|) (Set.Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Set.Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Set.Iic 0, f |x|) + ∫ x in Set.Ioi 0, f |x| := by
        rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Set.Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ x in Set.Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_of_nonpos hx]
  · have hni : ¬ Integrable (fun x => f |x|) := by
      exact fun h => hf h.integrableOn
    rw [← eq, integral_undef hf, integral_undef hni, mul_zero]

/-- **Real-place evaluation** (the standard treatment): the real Gamma-integral is the real
L-factor `L_ℝ(s) = π^{-s/2} Γ(s/2)`, for `0 < s.re`. -/
theorem gammaReal_eq {s : ℂ} (hs : 0 < s.re) :
    gammaReal s = DedekindZeta.LReal s := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Step 1: replace the multiplicative-density integral by a plain Lebesgue integral.
  have hmeas : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal |x|⁻¹) volume := by
    apply Measurable.aemeasurable
    exact ENNReal.measurable_ofReal.comp ((measurable_id.norm).inv)
  rw [gammaReal,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  -- Step 2: rewrite the integrand as `H |x|` for `H t = t⁻¹ • (e^{-πt²} (↑t)^s)`.
  set H : ℝ → ℂ := fun t : ℝ =>
    (t⁻¹ : ℝ) • ((Real.exp (-Real.pi * t ^ 2) : ℂ) * (t : ℂ) ^ s) with hH
  have hrw : (∫ x : ℝ, (ENNReal.ofReal |x|⁻¹).toReal •
        ((Real.exp (-Real.pi * x ^ 2) : ℂ) * ((|x| : ℝ) : ℂ) ^ s))
      = ∫ x : ℝ, H |x| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hH, ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x))]
    rw [← sq_abs x]
  rw [hrw, integral_comp_abs_complex]
  -- Step 3: identify the half-line integral with the Mellin transform of the Gaussian.
  have hHalf : (∫ t in Set.Ioi (0 : ℝ), H t)
      = mellin (fun t => (Real.exp (-Real.pi * t ^ 2) : ℂ)) s := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Set.mem_Ioi] at ht
    simp only [hH]
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    rw [Complex.real_smul, Complex.ofReal_inv, smul_eq_mul,
      Complex.cpow_sub _ _ ht0, Complex.cpow_one]
    field_simp
  rw [hHalf]
  -- Step 4: evaluate the Mellin transform of the Gaussian via `mellin_comp_rpow`.
  have hgauss : mellin (fun t => (Real.exp (-Real.pi * t ^ 2) : ℂ)) s
      = mellin (fun t => (Real.exp (-Real.pi * t ^ (2 : ℝ)) : ℂ)) s := by
    rw [mellin, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Set.mem_Ioi] at ht
    congr 2
    rw [← Real.rpow_natCast t 2]
    norm_num
  rw [hgauss]
  have hcomp := mellin_comp_rpow (fun u => (Real.exp (-Real.pi * u) : ℂ)) s 2
  rw [hcomp, show (s / ((2 : ℝ) : ℂ)) = s / 2 by push_cast; ring]
  -- Step 5: the one-variable Gaussian Mellin transform is `(1/π)^{s/2} Γ(s/2)`.
  have hmf : mellin (fun u => (Real.exp (-Real.pi * u) : ℂ)) (s / 2)
      = (1 / Real.pi) ^ (s / 2) * Complex.Gamma (s / 2) := by
    rw [mellin]
    rw [show (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s / 2 - 1) •
          (Real.exp (-Real.pi * t) : ℂ))
        = ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s / 2 - 1) *
          Complex.exp (-(Real.pi * t)) from ?_]
    · rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi (by simpa using hs) hπ]
    · refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [smul_eq_mul]
      congr 1
      rw [Complex.ofReal_exp]
      congr 1
      push_cast; ring
  rw [hmf]
  -- Step 6: bookkeep the constants and match `LReal`.
  rw [DedekindZeta.LReal, Complex.real_smul]
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hπ.le]; exact hπ.ne
  rw [show ((|(2 : ℝ)|⁻¹ : ℝ) : ℂ) = 1 / 2 by norm_num]
  rw [one_div (Real.pi : ℂ), Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  rw [show (-s / 2 : ℂ) = -(s / 2) by ring]
  ring

/-- **Complex-place evaluation** (the standard treatment): the complex Gamma-integral is the
complex L-factor `L_ℂ(s) = 2 (2π)^{-s} Γ(s)`, for `0 < s.re`. -/
theorem gammaComplex_eq {s : ℂ} (hs : 0 < s.re) :
    gammaComplex s = DedekindZeta.LComplex s := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  -- Polar/cpow bookkeeping lemma: `x · (x²)^{s-1} = x^{2s-1}` for `x > 0`.
  have hkey : ∀ x : ℝ, 0 < x →
      (x : ℂ) * ((x ^ 2 : ℝ) : ℂ) ^ (s - 1) = (x : ℂ) ^ (2 * s - 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [show ((x ^ 2 : ℝ) : ℂ) = (x : ℂ) * (x : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg hx.le hx.le, ← Complex.cpow_add _ _ hx0]
    nth_rewrite 1 [← Complex.cpow_one (x : ℂ)]
    rw [← Complex.cpow_add _ _ hx0]; congr 1; ring
  -- `x⁻¹ · x^{2s} = x^{2s-1}` for `x > 0`.
  have hkey2 : ∀ x : ℝ, 0 < x →
      ((x⁻¹ : ℝ) : ℂ) * (x : ℂ) ^ (2 * s) = (x : ℂ) ^ (2 * s - 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [Complex.ofReal_inv, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hx0]
    congr 1; ring
  -- `(1/(2π))^s = (2π)^{-s}`.
  have hpow : (1 / (2 * (Real.pi : ℂ))) ^ s = (2 * (Real.pi : ℂ)) ^ (-s) := by
    have harg : (2 * (Real.pi : ℂ)).arg ≠ Real.pi := by
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
          Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_pos.ne
    rw [one_div, Complex.inv_cpow _ _ harg, Complex.cpow_neg]
  -- The radial Mellin integral (substitution `u = x²` then `Complex.Gamma`).
  have hrad : (∫ x in Set.Ioi (0 : ℝ),
        (x : ℂ) ^ (2 * s - 1) * ((Real.exp (-2 * Real.pi * x ^ 2) : ℝ) : ℂ))
      = (1 / 2) * ((1 / ((2 * Real.pi : ℝ) : ℂ)) ^ s * Complex.Gamma s) := by
    have h2 := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := s) (r := 2 * Real.pi) hs
      (by positivity)
    have h3 := integral_comp_rpow_Ioi
      (fun u : ℝ => (u : ℂ) ^ (s - 1) * Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * (u : ℂ))))
      (p := 2) two_ne_zero
    rw [h2] at h3
    rw [← h3, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    rw [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.rpow_one, Real.rpow_two,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul]
    rw [← hkey x hx']
    rw [show ((Real.exp (-2 * Real.pi * x ^ 2) : ℝ) : ℂ)
          = Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ))) by
        rw [Complex.ofReal_exp]; congr 1; push_cast; ring]
    push_cast; ring
  -- The angular integral contributes `2π`.
  have hang : (∫ _ in Set.Ioo (-Real.pi) Real.pi, (1 : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
    rw [setIntegral_const, Real.volume_real_Ioo,
      max_eq_left (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi - -Real.pi),
      Complex.real_smul, mul_one]
    push_cast; ring
  -- Measurability/finiteness of the multiplicative-Haar density.
  have hd : Measurable (fun z : ℂ => ENNReal.ofReal (2 / Real.pi * (‖z‖ ^ 2)⁻¹)) :=
    (((continuous_norm.pow 2).measurable.inv).const_mul (2 / Real.pi)).ennreal_ofReal
  -- Unfold and pass to a plain Lebesgue integral, then to polar coordinates.
  unfold gammaComplex
  rw [integral_withDensity_eq_integral_toReal_smul₀ hd.aemeasurable
      (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
  have hfun : (fun z : ℂ => (ENNReal.ofReal (2 / Real.pi * (‖z‖ ^ 2)⁻¹)).toReal •
        ((Real.exp (-2 * Real.pi * ‖z‖ ^ 2) : ℝ) * (‖z‖ : ℂ) ^ (2 * s)))
      = fun z : ℂ => ((2 / Real.pi * (‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        (((Real.exp (-2 * Real.pi * ‖z‖ ^ 2) : ℝ) : ℂ) * (‖z‖ : ℂ) ^ (2 * s)) := by
    funext z
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  rw [hfun, ← Complex.integral_comp_polarCoord_symm,
    show _root_.polarCoord.target
      = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl]
  simp only [Complex.norm_polarCoord_symm]
  -- Rewrite the integrand on the polar target as a pure radial function.
  trans (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      2 / (Real.pi : ℂ) * ((p.1 : ℂ) ^ (2 * s - 1) *
        ((Real.exp (-2 * Real.pi * p.1 ^ 2) : ℝ) : ℂ)))
  · refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
    have h1 : (0 : ℝ) < p.1 := hp.1
    rw [abs_of_pos h1, Complex.real_smul]
    have hco : (p.1 : ℂ) * ((2 / Real.pi * (p.1 ^ 2)⁻¹ : ℝ) : ℂ)
        = (2 / (Real.pi : ℂ)) * ((p.1⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul,
        show p.1 * (2 / Real.pi * (p.1 ^ 2)⁻¹) = 2 / Real.pi * p.1⁻¹ by
          field_simp]
      push_cast; ring
    rw [← mul_assoc, hco, mul_assoc,
      show ((p.1⁻¹ : ℝ) : ℂ) * (((Real.exp (-2 * Real.pi * p.1 ^ 2) : ℝ) : ℂ)
            * (p.1 : ℂ) ^ (2 * s))
          = ((Real.exp (-2 * Real.pi * p.1 ^ 2) : ℝ) : ℂ)
            * (((p.1⁻¹ : ℝ) : ℂ) * (p.1 : ℂ) ^ (2 * s)) by ring,
      hkey2 p.1 h1]
    ring
  -- Fubini: factor into radial × angular.
  trans ((∫ x in Set.Ioi (0 : ℝ),
      2 / (Real.pi : ℂ) * ((x : ℂ) ^ (2 * s - 1) *
        ((Real.exp (-2 * Real.pi * x ^ 2) : ℝ) : ℂ)))
      * (∫ _ in Set.Ioo (-Real.pi) Real.pi, (1 : ℂ)))
  · rw [← setIntegral_prod_mul, Measure.volume_eq_prod]; simp_rw [mul_one]
  rw [hang, integral_const_mul, hrad, DedekindZeta.LComplex,
    show ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) by push_cast; ring, hpow]
  field_simp

/-! ## Factorisation and evaluation of the higher-dimensional integral -/

/-- **Convergence** (the standard treatment): for `0 < s.re` the Gaussian Mellin integrand
is integrable for the multiplicative Haar measure on `K_ℝ^*`. -/
theorem integrable_gaussian_mellin {s : ℂ} (hs : 0 < s.re) :
    Integrable
      (fun x : mixedEmbedding.mixedSpace K => gaussian K x * (mixedEmbedding.norm x : ℂ) ^ s)
      (mulHaar K) :=
  -- Single source of truth: the whole-space Gaussian-Mellin convergence and its
  -- `withDensity`/product-measure reduction live upstream in `DedekindZeta`
  -- (Statements.lean), stated against the canonical `Theta.mixedGaussian` /
  -- `mixedMulHaar`. The legacy `gaussian` (GammaIntegral:83) and `mulHaar`
  -- (GammaIntegral:72) defs are *definitionally equal* to `Theta.mixedGaussian`
  -- (Theta.lean) and `mixedMulHaar` (Statements.lean) respectively, so the
  -- upstream lemma typechecks here through defeq; we consume it rather than
  -- redoing the ~110-line per-place reduction.
  DedekindZeta.integrable_mixedGaussian_mellin K hs

/-! ### Per-place integrands for the factorisation

The higher-dimensional Gaussian Mellin integrand, written against the additive
`volume` (after pushing the `mulHaar` density inside), is a product over the
places of the one-dimensional integrands defining `gammaReal`/`gammaComplex`.
We record those per-place integrands (the `volume`-density form of the
defining `withDensity` integrals) so the factorisation is a clean product. -/

/-- The real-place integrand (the standard treatment): the `volume`-density form of the
`gammaReal` integrand, `|t|⁻¹ • (e^{-π t²} · |t|^s)`. -/
def realFactor (s : ℂ) (t : ℝ) : ℂ :=
  (|t|⁻¹ : ℝ) • (Real.exp (-Real.pi * t ^ 2) * (((|t| : ℝ) : ℂ)) ^ s)

/-- The complex-place integrand (the standard treatment): the `volume`-density form of the
`gammaComplex` integrand, `(2/π)·‖z‖⁻² • (e^{-2π‖z‖²} · ‖z‖^{2s})`. -/
def complexFactor (s : ℂ) (z : ℂ) : ℂ :=
  (2 / Real.pi * (‖z‖ ^ 2)⁻¹ : ℝ) •
    (Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * (‖z‖ : ℂ) ^ (2 * s))

/-- `gammaReal` is the additive-`volume` integral of `realFactor` (unfolding the
`withDensity` defining `gammaReal` via `integral_withDensity_eq_integral_toReal_smul`). -/
theorem gammaReal_eq_integral (s : ℂ) :
    gammaReal s = ∫ t : ℝ, realFactor s t := by
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal |x|⁻¹) volume := by
    apply Measurable.aemeasurable
    exact ENNReal.measurable_ofReal.comp ((measurable_id.norm).inv)
  rw [gammaReal,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [realFactor, ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x))]

/-- `gammaComplex` is the additive-`volume` integral of `complexFactor`. -/
theorem gammaComplex_eq_integral (s : ℂ) :
    gammaComplex s = ∫ z : ℂ, complexFactor s z := by
  -- Unfold the `withDensity` and push the density into the integrand.
  have hmeas : AEMeasurable
      (fun z : ℂ => ENNReal.ofReal (2 / Real.pi * (‖z‖ ^ 2)⁻¹)) volume := by
    apply Measurable.aemeasurable
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((measurable_id.norm.pow_const 2).inv))
  rw [gammaComplex,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have hnn : 0 ≤ 2 / Real.pi * (‖z‖ ^ 2)⁻¹ :=
    mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) (inv_nonneg.2 (sq_nonneg _))
  simp only [complexFactor, ENNReal.toReal_ofReal hnn]

/-- Distributing a complex power over a finite product of nonnegative reals:
`(↑(∏ gᵢ))^s = ∏ (↑gᵢ)^s`. (Repeated `Complex.mul_cpow_ofReal_nonneg`.) -/
private theorem ofReal_prod_cpow {ι : Type*} (t : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ t, 0 ≤ g i) (s : ℂ) :
    (((∏ i ∈ t, g i : ℝ)) : ℂ) ^ s = ∏ i ∈ t, ((g i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (hg a (Finset.mem_insert_self a t))
          (Finset.prod_nonneg fun i hi => hg i (Finset.mem_insert_of_mem hi)),
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

/-- For a positive real `r`, `(↑(r²))^s = (↑r)^(2s)` (the complex cpow of the
square). Used to match the complex per-place factor `(‖z‖)^{2s}`. -/
private theorem ofReal_sq_cpow {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (((r ^ 2 : ℝ)) : ℂ) ^ s = (r : ℂ) ^ (2 * s) := by
  have him : (Complex.log (r : ℂ) * 2).im = 0 := by
    simp [Complex.mul_im, Complex.log_im, Complex.arg_ofReal_of_nonneg hr.le]
  rw [Complex.cpow_mul (x := (r : ℂ)) (y := 2) s
      (by rw [him]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [him]; exact Real.pi_pos.le), Complex.cpow_two, ← Complex.ofReal_pow]

/-- **Product form of the Gaussian Gamma-integral** (the standard treatment): pushing the
`mulHaar` density into the integrand, factoring the Gaussian and the norm over
the infinite places, and applying Fubini (`integral_prod_mul`) over the
product space `K_ℝ = (real → ℝ) × (complex → ℂ)`, the higher-dimensional
integral becomes the product of the per-place `volume`-integrals. -/
theorem gammaIntegral_gaussian_prod (s : ℂ) :
    gammaIntegral K (fun x => (gaussian K x : ℂ)) s =
      (∫ y : {w : InfinitePlace K // IsReal w} → ℝ, ∏ w, realFactor s (y w)) *
        (∫ y : {w : InfinitePlace K // IsComplex w} → ℂ, ∏ w, complexFactor s (y w)) := by
  classical
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Measurability of the `mulHaar` density, for pushing it into the integrand.
  have hmeas : AEMeasurable (fun x : mixedEmbedding.mixedSpace K =>
      ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹)) volume :=
    (ENNReal.measurable_ofReal.comp
      (measurable_const.mul
        (Measurable.inv (mixedEmbedding.continuous_norm (K := K)).measurable))).aemeasurable
  -- The two product integrands, separated.
  set F : ({w : InfinitePlace K // IsReal w} → ℝ) → ℂ :=
    fun y => ∏ w, realFactor s (y w) with hF
  set G : ({w : InfinitePlace K // IsComplex w} → ℂ) → ℂ :=
    fun y => ∏ w, complexFactor s (y w) with hG
  -- The pointwise identity for the pushed-density integrand.
  have key : ∀ x : mixedEmbedding.mixedSpace K,
      (ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K *
          (mixedEmbedding.norm x)⁻¹)).toReal •
        ((gaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
        = F x.1 * G x.2 := by
    intro x
    by_cases hx0 : mixedEmbedding.norm x = 0
    · -- On the zero locus both sides vanish.
      have hLHS : (ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K *
          (mixedEmbedding.norm x)⁻¹)).toReal •
          ((gaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s) = 0 := by
        rw [hx0, inv_zero, mul_zero, ENNReal.ofReal_zero, ENNReal.toReal_zero, zero_smul]
      rw [hLHS]
      obtain ⟨w, hw⟩ := mixedEmbedding.norm_eq_zero_iff.mp hx0
      symm
      obtain hwr | hwc := isReal_or_isComplex w
      · have : F x.1 = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ (⟨w, hwr⟩ :
            {w : InfinitePlace K // IsReal w})) ?_
          have hzero : x.1 ⟨w, hwr⟩ = 0 := by
            have := normAtPlace_apply_of_isReal hwr x
            rw [hw] at this
            simpa using (norm_eq_zero.mp this.symm)
          simp [realFactor, hzero]
        rw [this, zero_mul]
      · have : G x.2 = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ (⟨w, hwc⟩ :
            {w : InfinitePlace K // IsComplex w})) ?_
          have hzero : x.2 ⟨w, hwc⟩ = 0 := by
            have := normAtPlace_apply_of_isComplex hwc x
            rw [hw] at this
            simpa using (norm_eq_zero.mp this.symm)
          simp [complexFactor, hzero]
        rw [this, mul_zero]
    · -- Away from the zero locus: every place-norm is positive.
      have hpos : ∀ w : InfinitePlace K, normAtPlace w x ≠ 0 := fun w hw =>
        hx0 (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, hw⟩)
      have hnn : (0 : ℝ) ≤ (2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹ :=
        mul_nonneg (by positivity) (inv_nonneg.mpr (mixedEmbedding.norm_nonneg x))
      -- Split each place-product into its three constituent factors.
      have hF_split : F x.1 =
          (∏ w : {w : InfinitePlace K // IsReal w}, ((|x.1 w|⁻¹ : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsReal w},
            ((Real.exp (-Real.pi * (x.1 w) ^ 2) : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsReal w}, ((|x.1 w| : ℝ) : ℂ) ^ s) := by
        rw [hF, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [realFactor, Complex.real_smul]; push_cast; ring
      have hG_split : G x.2 =
          (∏ w : {w : InfinitePlace K // IsComplex w},
            ((2 / Real.pi * (‖x.2 w‖ ^ 2)⁻¹ : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsComplex w},
            ((Real.exp (-2 * Real.pi * ‖x.2 w‖ ^ 2) : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsComplex w}, ((‖x.2 w‖ : ℝ) : ℂ) ^ (2 * s)) := by
        rw [hG, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [complexFactor, Complex.real_smul]; push_cast; ring
      -- Bracket 1: the density factor.
      have hB1 :
          (∏ w : {w : InfinitePlace K // IsReal w}, ((|x.1 w|⁻¹ : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsComplex w},
            ((2 / Real.pi * (‖x.2 w‖ ^ 2)⁻¹ : ℝ) : ℂ))
          = (((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
          Complex.ofReal_inj]
        have hnorm : mixedEmbedding.norm x =
            (∏ w : {w : InfinitePlace K // IsReal w}, |x.1 w|) *
            (∏ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2) := by
          rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod]
          congr 1
          · refine Finset.prod_congr rfl fun w _ => ?_
            rw [mult_isReal, normAtPlace_apply_of_isReal w.2, pow_one, Real.norm_eq_abs]
          · refine Finset.prod_congr rfl fun w _ => ?_
            rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2]
        have hconst : (∏ _w : {w : InfinitePlace K // IsComplex w}, (2 / Real.pi : ℝ))
            = (2 / Real.pi) ^ nrComplexPlaces K := by
          rw [Finset.prod_const, Finset.card_univ]
        rw [hnorm]
        simp only [Finset.prod_inv_distrib, Finset.prod_mul_distrib, hconst, mul_inv]
        ring
      -- Bracket 2: the Gaussian.
      have hB2 :
          (∏ w : {w : InfinitePlace K // IsReal w},
            ((Real.exp (-Real.pi * (x.1 w) ^ 2) : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsComplex w},
            ((Real.exp (-2 * Real.pi * ‖x.2 w‖ ^ 2) : ℝ) : ℂ))
          = (gaussian K x : ℂ) := by
        rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
          Complex.ofReal_inj]
        rw [gaussian, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
        congr 1
        rw [sum_eq_sum_add_sum, mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun w _ => ?_
          rw [mult_isReal, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs, sq_abs]
          push_cast; ring
        · refine Finset.sum_congr rfl fun w _ => ?_
          rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2]
          push_cast; ring
      -- Bracket 3: the norm power.
      have hB3 :
          (∏ w : {w : InfinitePlace K // IsReal w}, ((|x.1 w| : ℝ) : ℂ) ^ s) *
          (∏ w : {w : InfinitePlace K // IsComplex w}, ((‖x.2 w‖ : ℝ) : ℂ) ^ (2 * s))
          = (mixedEmbedding.norm x : ℂ) ^ s := by
        rw [mixedEmbedding.norm_apply,
          ofReal_prod_cpow Finset.univ (fun w => normAtPlace w x ^ mult w)
            (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _) s,
          prod_eq_prod_mul_prod]
        congr 1
        · refine Finset.prod_congr rfl fun w _ => ?_
          rw [mult_isReal, normAtPlace_apply_of_isReal w.2, pow_one, Real.norm_eq_abs]
        · refine Finset.prod_congr rfl fun w _ => ?_
          have hposc : ‖x.2 ⟨w.1, w.2⟩‖ ≠ 0 := by
            have := hpos w.1; rwa [normAtPlace_apply_of_isComplex w.2] at this
          rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2,
            ofReal_sq_cpow ((norm_nonneg _).lt_of_ne hposc.symm) s]
      -- Assemble.
      rw [ENNReal.toReal_ofReal hnn, Complex.real_smul, hF_split, hG_split,
        show ((((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹ : ℝ) : ℂ)) *
            ((gaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
          = ((((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹ : ℝ) : ℂ)) *
            ((gaussian K x : ℂ)) * ((mixedEmbedding.norm x : ℂ) ^ s) from by ring,
        ← hB1, ← hB2, ← hB3]
      ring
  -- Now compute the integral.
  rw [gammaIntegral, mulHaar, integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _,
    integral_congr_ae (Filter.Eventually.of_forall key), Measure.volume_eq_prod,
    integral_prod_mul F G]

/-- **Factorisation into per-place integrals** (the standard treatment): the
higher-dimensional Gamma-integral of the Gaussian factors as the product of the
one-dimensional integrals over the real and complex places. -/
theorem gammaIntegral_gaussian_factor (s : ℂ) :
    gammaIntegral K (fun x => (gaussian K x : ℂ)) s =
      gammaReal s ^ nrRealPlaces K * gammaComplex s ^ nrComplexPlaces K := by
  rw [gammaIntegral_gaussian_prod,
    integral_fintype_prod_volume_eq_pow (realFactor s),
    integral_fintype_prod_volume_eq_pow (complexFactor s),
    gammaReal_eq_integral, gammaComplex_eq_integral]

/-- **Evaluation of the higher-dimensional Gamma-integral** (the standard treatment):
for `0 < s.re` the multiplicative Mellin transform of the Gaussian over `K_ℝ^*`
is `L_ℝ(s)^{r₁} · L_ℂ(s)^{r₂}` — the archimedean L-factors with
`r₁ = nrRealPlaces K`, `r₂ = nrComplexPlaces K`. -/
theorem gammaIntegral_gaussian_eq {s : ℂ} (hs : 0 < s.re) :
    gammaIntegral K (fun x => (gaussian K x : ℂ)) s =
      DedekindZeta.LReal s ^ nrRealPlaces K *
        DedekindZeta.LComplex s ^ nrComplexPlaces K := by
  rw [gammaIntegral_gaussian_factor, gammaReal_eq hs, gammaComplex_eq hs]

/-! ## The archimedean Gamma factor `I(s)` and the identity `|d_K|^{s/2}·I(s) = Z_∞` -/

-- the standard treatment: the archimedean Gamma-integral is the **whole-space**
-- multiplicative Mellin transform of the single Minkowski Gaussian over
-- `K_ℝ^* = mixedSpace K` (NOT over the fundamental cone — the cone is
-- closed under all nonzero real scalings and
-- yields only a single radial Γ-factor, not the per-place product
-- `L_ℝ^{r₁}·L_ℂ^{r₂}`).
/-- The **archimedean Gamma factor** `I(s)` of the standard treatment: the
multiplicative Mellin transform `∫_{K_ℝ^*} g(x) |N(x)|^s d^*x` of the single
Minkowski Gaussian `g = gaussian K` over the whole multiplicative Minkowski
space. Defined as an alias of `gammaIntegral K (g·) s`. -/
def I (s : ℂ) : ℂ := gammaIntegral K (fun x => (gaussian K x : ℂ)) s

/-- **The archimedean Gamma-factor identity** (the standard treatment):
for `0 < s.re`, the discriminant-weighted archimedean Gamma-integral equals the
archimedean completion `Z_∞(s) = |d_K|^{s/2} L_ℝ(s)^{r₁} L_ℂ(s)^{r₂}`:

    ((|d_K| : ℝ) : ℂ)^(s/2) · I(s) = Z_∞(s).

Proof: `I(s) = L_ℝ^{r₁}·L_ℂ^{r₂}` by `gammaIntegral_gaussian_eq`, and
`Z_∞` is exactly `|d_K|^{s/2}` times that product. -/
theorem absdisc_rpow_mul_I_eq_ZInfty {s : ℂ} (hs : 0 < s.re) :
    ((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) * I K s = DedekindZeta.ZInfty K s := by
  rw [I, gammaIntegral_gaussian_eq K hs, DedekindZeta.ZInfty, mul_assoc]

end

end DedekindZeta.GammaIntegral

/-! ## The Mellin principle: inversion `x ↦ x⁻¹` of the `K_ℝ^*` Mellin integral

This section formalises the substitution underlying the standard treatment's *Mellin principle*
(the theorem) for the multiplicative Mellin integral `∫_{K_ℝ^*} f(x) |N(x)|^s d^*x`:
the change of variables `x ↦ x⁻¹` sends `|N(x)|^s ↦ |N(x)|^{-s}` and leaves the
multiplicative Haar measure `d^*x = DedekindZeta.mixedMulHaar` invariant, which is
exactly what produces the `s ↔ 1 − s` symmetry of the gamma-integral once the
theta-kernel inversion law is fed in.

The cone/dual-ideal bookkeeping (mapping `fundamentalCone K` to itself up to the
quotiented `𝓞ˣ`-action, and replacing the `𝔞`-kernel by the `𝔞'`-kernel) is the
remaining assembly step; here we provide the measure-theoretic
substitution principle that step consumes. -/

namespace DedekindZeta

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory

variable {K : Type*} [Field K] [NumberField K]

noncomputable section

/-- The componentwise inversion of `K_ℝ` negates each place-norm exponent:
`normAtPlace w (x⁻¹) = (normAtPlace w x)⁻¹`. (The `Inv` on the mixed space is the
componentwise inverse of the real/complex coordinates.) -/
theorem normAtPlace_inv (w : InfinitePlace K) (x : mixedEmbedding.mixedSpace K) :
    normAtPlace w x⁻¹ = (normAtPlace w x)⁻¹ := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, normAtPlace_apply_of_isReal hw,
      show x⁻¹.1 ⟨w, hw⟩ = (x.1 ⟨w, hw⟩)⁻¹ from rfl, norm_inv]
  · rw [normAtPlace_apply_of_isComplex hw, normAtPlace_apply_of_isComplex hw,
      show x⁻¹.2 ⟨w, hw⟩ = (x.2 ⟨w, hw⟩)⁻¹ from rfl, norm_inv]

/-- **Inversion sends `|N(x)| ↦ |N(x)|⁻¹`** (the standard treatment: the kernel of the Mellin
principle). The absolute norm `N : K_ℝ → ℝ` of the standard treatment inverts under the
componentwise inversion `x ↦ x⁻¹` of `K_ℝ^*`. -/
theorem mixedEmbedding_norm_inv (x : mixedEmbedding.mixedSpace K) :
    mixedEmbedding.norm x⁻¹ = (mixedEmbedding.norm x)⁻¹ := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_inv, inv_pow,
    ← Finset.prod_inv_distrib]

/-! ### Product Fubini for `lintegral` and `withDensity` on `Measure.pi`

Two measure-theoretic helpers used to push a one-dimensional inversion
Jacobian through a finite product of coordinates: a Tonelli/Fubini identity
for a product of per-coordinate densities, and the resulting identification of
`Measure.pi (fun _ => μ.withDensity g)` with a single `withDensity` of the
product density on `Measure.pi (fun _ => μ)`. -/

/-- **Tonelli for a finite (`Fin n`) product of densities.** The `lintegral` of
a product `∏ i, f i (x i)` against `Measure.pi μ` factors as the product of the
per-coordinate `lintegral`s.  `lintegral` analogue of
`MeasureTheory.integral_fin_nat_prod_eq_prod`. -/
private theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
        (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero]
      simp only [Fin.zero_succAbove, Function.comp_def]
      rw [← ih (fun i ↦ f (Fin.succ i)) (fun i ↦ hf _)]
      haveI : ∀ j : Fin n, SigmaFinite (μ j.succ) := fun j ↦ inferInstance
      have hpm := lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun i : Fin n ↦ μ i.succ)
        (f := fun a ↦ f 0 a)
        (g := fun y : (i : Fin n) → E (Fin.succ i) ↦ ∏ i, f (Fin.succ i) (y i))
        ((hf 0).aemeasurable)
        ((Finset.measurable_prod _ fun i _ ↦ (hf _).comp (measurable_pi_apply i)).aemeasurable)
      exact hpm

/-- **Tonelli for a finite product of densities**, indexed by a general
`Fintype`. `lintegral` analogue of
`MeasureTheory.integral_fintype_prod_eq_prod`. -/
private theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  haveI : ∀ j : Fin (Fintype.card ι), SigmaFinite (μ (e j)) := fun j ↦ inferInstance
  have hpm := lintegral_fin_nat_prod_eq_prod (E := fun j ↦ E (e j)) (mE := fun j ↦ mE (e j))
    (μ := fun j ↦ μ (e j)) (fun j ↦ f (e j)) (fun j ↦ hf _)
  exact hpm

/-- **`Measure.pi` of `withDensity` is `withDensity` of the product density.**
The finite product of the per-coordinate measures `μ.withDensity g` equals the
product measure `Measure.pi (fun _ => μ)` carrying the product density
`x ↦ ∏ i, g (x i)`. -/
private theorem pi_withDensity_const_eq {ι : Type*} [Fintype ι] {E : Type*}
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] {g : E → ℝ≥0∞} (hg : Measurable g)
    [SigmaFinite (μ.withDensity g)] :
    Measure.pi (fun _ : ι ↦ μ.withDensity g)
      = (Measure.pi (fun _ : ι ↦ μ)).withDensity (fun x ↦ ∏ i, g (x i)) := by
  refine Measure.pi_eq (μ := fun _ : ι ↦ μ.withDensity g) fun s hs ↦ ?_
  haveI : ∀ i : ι, SigmaFinite (μ.restrict (s i)) := fun i ↦ inferInstance
  have hLI : ∫⁻ x : ι → E, ∏ i, g (x i) ∂(Measure.pi fun _ : ι ↦ μ.restrict (s _))
      = ∏ i, ∫⁻ x, g x ∂(μ.restrict (s i)) :=
    lintegral_fintype_prod_eq_prod (μ := fun _ : ι ↦ μ.restrict (s _)) (fun _ ↦ g) (fun _ ↦ hg)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi, hLI]
  exact Finset.prod_congr rfl fun i _ ↦ (withDensity_apply g (hs i)).symm

/-! ## Complex-factor inversion Jacobian

The additive Lebesgue measure on the complex coordinate factor
`({w : InfinitePlace K // IsComplex w} → ℂ)` of the mixed space transforms
under componentwise field inversion `z ↦ z⁻¹` with one Jacobian factor
`|z_w|⁻⁴` per complex place: the real derivative of `z ↦ z⁻¹` on `ℂ ≅ ℝ²` is
multiplication by `-z⁻²`, a `ℂ`-linear (hence conformal) map whose real
determinant is `|−z⁻²|² = |z|⁻⁴`. -/

/-- **One-dimensional complex inversion Jacobian.** Pushing the additive
Lebesgue measure on `ℂ` forward along `z ↦ z⁻¹` gives `|z|⁻⁴ dλ`. The fixed
point `0` is volume-null; off it, `z ↦ z⁻¹` is a diffeomorphism whose real
Fréchet derivative `-z⁻²·(·)` is `ℂ`-linear with `|det_ℝ| = |z|⁻⁴`
(`integral_image_eq_integral_abs_det_fderiv_smul`). -/
theorem volume_complex_map_inv :
    Measure.map (fun z : ℂ => z⁻¹) volume
      = volume.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ 4)⁻¹) := by
  set f : ℂ → ℂ := fun z => z⁻¹ with hf_def
  set s : Set ℂ := {(0 : ℂ)}ᶜ with hs_def
  have hs : MeasurableSet s := (measurableSet_singleton 0).compl
  -- the real Fréchet derivative of `z ↦ z⁻¹` at `z` is multiplication by `-z⁻²`,
  -- viewed as the `ℝ`-restriction of a `ℂ`-linear (conformal) map.
  set f' : ℂ → (ℂ →L[ℝ] ℂ) :=
    fun z => (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z ^ 2)⁻¹)).restrictScalars ℝ
      with hf'_def
  have hmeas : Measurable f := by rw [hf_def]; fun_prop
  -- `|det_ℝ (-z⁻²·)| = ‖-z⁻²‖² = (‖z‖⁴)⁻¹`, valid for every `z` (incl. the null point `0`).
  have hdet : (fun z => ENNReal.ofReal |(f' z).det|)
      = (fun z => ENNReal.ofReal (‖z‖ ^ 4)⁻¹) := by
    funext z
    have hd : (f' z).det = ‖(-(z ^ 2)⁻¹)‖ ^ 2 := by
      rw [hf'_def]
      simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
        Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]
    rw [hd, abs_of_nonneg (by positivity)]
    congr 1
    rw [norm_neg, norm_inv, norm_pow, inv_pow, ← pow_mul]
  -- differentiability of `f` on the conull set `s = {0}ᶜ`
  have hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x := by
    intro x hx
    have hx0 : x ≠ 0 := hx
    exact ((hasDerivAt_inv hx0).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : Set.InjOn f s := by
    intro a _ b _ hab
    simpa [hf_def] using inv_injective hab
  have himg : f '' s = s := by
    rw [hf_def, hs_def]
    ext w
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro hw; exact ⟨w⁻¹, by simpa using hw, inv_inv w⟩
  -- change of variables on `s`: push `volume.restrict s` with the Jacobian density
  -- back to `volume` on the image `s`.
  have key := map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure ℂ) hs.nullMeasurableSet hf' hinj
  rw [himg, hdet] at key
  -- `{0}` is `volume`-null, so `volume.restrict s = volume`.
  have hconull : (volume : Measure ℂ).restrict s = volume := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [hs_def]
    exact compl_mem_ae_iff.mpr (measure_singleton 0)
  rw [hconull] at key
  -- `f` is an involution, so applying `map f` to `key` inverts it.
  have hinvol : f ∘ f = id := by funext z; simp [hf_def, inv_inv]
  have hres := congrArg (Measure.map f) key
  rw [Measure.map_map hmeas hmeas, hinvol, Measure.map_id] at hres
  exact hres.symm

open Classical in
/-- **Complex-factor inversion Jacobian** on the complex coordinate factor of
the mixed space. Componentwise inversion `x ↦ (x_w)⁻¹` pushes the additive
Lebesgue measure forward to the density `∏_w |x_w|⁻⁴`, the product over complex
places of the one-dimensional Jacobian `volume_complex_map_inv`, obtained via
`MeasureTheory.Measure.pi_map_pi` / `volume_pi`. -/
theorem volume_pi_complex_map_inv :
    Measure.map (fun x : {w : InfinitePlace K // IsComplex w} → ℂ => fun w => (x w)⁻¹) volume
      = volume.withDensity
          (fun x : {w : InfinitePlace K // IsComplex w} → ℂ => ∏ w, ENNReal.ofReal (‖x w‖ ^ 4)⁻¹) := by
  classical
  -- the per-coordinate inversion Jacobian density.
  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ 4)⁻¹ with hg
  have hgmeas : Measurable g := by
    rw [hg]; exact ((measurable_norm.pow_const 4).inv).ennreal_ofReal
  -- σ-finiteness of the per-coordinate push-forward `map (·⁻¹) volume = volume.withDensity g`.
  have hsf : SigmaFinite ((volume : Measure ℂ).map (fun z : ℂ => z⁻¹)) := by
    rw [volume_complex_map_inv]; infer_instance
  haveI hsf' : ∀ _i : {w : InfinitePlace K // IsComplex w},
      SigmaFinite ((volume : Measure ℂ).map (fun z : ℂ => z⁻¹)) := fun _ => hsf
  -- identify `volume` on the product with `Measure.pi (fun _ => volume)` and push forward
  -- componentwise (`pi_map_pi`).
  rw [volume_pi]
  have hmap := Measure.pi_map_pi (μ := fun _ : {w : InfinitePlace K // IsComplex w} => (volume : Measure ℂ))
    (f := fun _ : {w : InfinitePlace K // IsComplex w} => fun z : ℂ => z⁻¹)
    (fun _ => measurable_inv.aemeasurable)
  rw [hmap]
  -- replace each per-coordinate map by its `withDensity` form, then collapse the product.
  simp_rw [volume_complex_map_inv]
  rw [pi_withDensity_const_eq (volume : Measure ℂ) hgmeas]

/-- **One-dimensional real inversion Jacobian.** The push-forward of the additive
Lebesgue measure on `ℝ` under the field inversion `t ↦ t⁻¹` (with `0⁻¹ = 0`) has
density `|t|⁻²` (the absolute value of the Jacobian determinant of `t ↦ t⁻¹`,
whose derivative is `-t⁻²`):

    map (·⁻¹) (volume : Measure ℝ) = volume.withDensity (t ↦ |t|⁻²).

The fixed point `0` is volume-null, so on `ℝ \ {0}` this is the diffeomorphism
change of variables `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`.
This is the analytic core of the real-factor inversion Jacobian. -/
theorem map_inv_volume_real_one :
    Measure.map (fun t : ℝ => t⁻¹) volume
      = volume.withDensity (fun t : ℝ => ENNReal.ofReal (‖t‖ ^ 2)⁻¹) := by
  -- Density measurability.
  have hdens : Measurable (fun t : ℝ => ENNReal.ofReal (‖t‖ ^ 2)⁻¹) :=
    ((measurable_norm.pow_const 2).inv).ennreal_ofReal
  -- We test both measures against an arbitrary measurable `g`.
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg measurable_inv,
    lintegral_withDensity_eq_lintegral_mul volume hdens hg]
  simp only [Pi.mul_apply]
  -- Now: `∫⁻ a, g a⁻¹ = ∫⁻ a, ofReal (‖a‖²)⁻¹ * g a`.
  -- Splitting principle: the fixed point `0` is volume-null.
  have hdisj : Disjoint (Set.Iio (0 : ℝ)) (Set.Ioi 0) := by
    rw [Set.disjoint_left]; intro x hx hx'
    exact absurd ((Set.mem_Ioi.1 hx').trans (Set.mem_Iio.1 hx)) (lt_irrefl 0)
  have hset : Set.Iio (0 : ℝ) ∪ Set.Ioi 0 = ({(0 : ℝ)}ᶜ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_compl_iff,
      Set.mem_singleton_iff, lt_or_lt_iff_ne, ne_eq]
  have hae : ((Set.Iio (0 : ℝ) ∪ Set.Ioi (0 : ℝ) : Set ℝ)) =ᵐ[volume] (Set.univ : Set ℝ) := by
    rw [hset]; exact ae_eq_univ.2 (by simp)
  have split : ∀ F : ℝ → ℝ≥0∞,
      ∫⁻ x, F x ∂volume = (∫⁻ x in Set.Iio (0 : ℝ), F x) + ∫⁻ x in Set.Ioi (0 : ℝ), F x := by
    intro F
    rw [← setLIntegral_univ F, ← setLIntegral_congr hae,
      lintegral_union measurableSet_Ioi hdisj]
  -- The pointwise identity `|f' x| · ofReal (‖x⁻¹‖²)⁻¹ = 1` for `x ≠ 0`.
  have hscalar : ∀ x : ℝ, x ≠ 0 →
      ENNReal.ofReal |(-(x ^ 2)⁻¹)| * (ENNReal.ofReal (‖x⁻¹‖ ^ 2)⁻¹ * g x⁻¹) = g x⁻¹ := by
    intro x hx
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x ^ 2)⁻¹),
      show ‖x⁻¹‖ ^ 2 = (x ^ 2)⁻¹ from by rw [Real.norm_eq_abs, sq_abs, inv_pow], inv_inv,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ (ne_of_gt hx2), ENNReal.ofReal_one, one_mul]
  -- Change of variables on `(0, ∞)`: `t ↦ t⁻¹` is an antitone diffeomorphism
  -- with derivative `-(x²)⁻¹`, mapping `Set.Ioi 0` onto itself.
  have key_pos : (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖x‖ ^ 2)⁻¹ * g x)
      = ∫⁻ x in Set.Ioi (0 : ℝ), g x⁻¹ := by
    have himg : (fun t : ℝ => t⁻¹) '' Set.Ioi (0 : ℝ) = Set.Ioi 0 := by
      ext y; simp only [Set.mem_image, Set.mem_Ioi]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact inv_pos.2 hx
      · intro hy; exact ⟨y⁻¹, inv_pos.2 hy, inv_inv y⟩
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) (Set.Ioi 0) x :=
      fun x hx => (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt
    have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun t : ℝ => t⁻¹)
      (f' := fun x => -(x ^ 2)⁻¹) measurableSet_Ioi hderiv inv_injective.injOn
      (fun y => ENNReal.ofReal (‖y‖ ^ 2)⁻¹ * g y)
    rw [himg] at hcov
    rw [hcov]
    exact setLIntegral_congr_fun measurableSet_Ioi fun x hx => hscalar x (ne_of_gt hx)
  -- Change of variables on `(-∞, 0)`.
  have key_neg : (∫⁻ x in Set.Iio (0 : ℝ), ENNReal.ofReal (‖x‖ ^ 2)⁻¹ * g x)
      = ∫⁻ x in Set.Iio (0 : ℝ), g x⁻¹ := by
    have himg : (fun t : ℝ => t⁻¹) '' Set.Iio (0 : ℝ) = Set.Iio 0 := by
      ext y; simp only [Set.mem_image, Set.mem_Iio]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact inv_lt_zero.2 hx
      · intro hy; exact ⟨y⁻¹, inv_lt_zero.2 hy, inv_inv y⟩
    have hderiv : ∀ x ∈ Set.Iio (0 : ℝ),
        HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) (Set.Iio 0) x :=
      fun x hx => (hasDerivAt_inv (ne_of_lt hx)).hasDerivWithinAt
    have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun t : ℝ => t⁻¹)
      (f' := fun x => -(x ^ 2)⁻¹) measurableSet_Iio hderiv inv_injective.injOn
      (fun y => ENNReal.ofReal (‖y‖ ^ 2)⁻¹ * g y)
    rw [himg] at hcov
    rw [hcov]
    exact setLIntegral_congr_fun measurableSet_Iio fun x hx => hscalar x (ne_of_lt hx)
  rw [split (fun a => g a⁻¹), split (fun a => ENNReal.ofReal (‖a‖ ^ 2)⁻¹ * g a),
    key_pos, key_neg]

/-- Push-forward through a measurable equivalence commutes with `withDensity`
(pulling the density back along the equivalence). General measure-theory helper
for the product change of variables. -/
private theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) (ρ : Measure α) {h : β → ℝ≥0∞}
    (hh : Measurable h) :
    Measure.map e (ρ.withDensity (fun x => h (e x)))
      = (Measure.map e ρ).withDensity h := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hhe : Measurable (fun x => h (e x)) := hh.comp e.measurable
  have hfe : Measurable (fun a => f (e a)) := hf.comp e.measurable
  rw [lintegral_map hf e.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hhe hfe,
    lintegral_withDensity_eq_lintegral_mul _ hh hf]
  simp only [Pi.mul_apply]
  rw [lintegral_map (by fun_prop : Measurable (fun a => h a * f a)) e.measurable]

/-- **Product `withDensity`, constant family over `Fin n`.** The `Fin n`-fold
product of `μ.withDensity g` is the product measure `Measure.pi (fun _ => μ)`
weighted by the product density `x ↦ ∏ i, g (x i)`. Proved by induction on `n`
via `measurePreserving_piFinSuccAbove` and `prod_withDensity`. -/
private theorem pi_const_withDensity_fin {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] {g : E → ℝ≥0∞} (hg : Measurable g)
    [SigmaFinite (μ.withDensity g)] (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ.withDensity g)
      = (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x : Fin n → E => ∏ i, g (x i)) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty, Measure.pi_of_empty]
    have : (fun x : Fin 0 → E => ∏ i, g (x i)) = (fun _ => (1 : ℝ≥0∞)) := by
      funext x; simp
    rw [this]
    simp
  | succ n ih =>
    have hgprod : Measurable (fun x : Fin n → E => ∏ i, g (x i)) :=
      Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)
    have hgprod' : Measurable (fun x : Fin (n + 1) → E => ∏ i, g (x i)) :=
      Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)
    set e : (Fin (n + 1) → E) ≃ᵐ E × (Fin n → E) :=
      MeasurableEquiv.piFinSuccAbove (fun _ => E) 0 with he
    -- The density commutes with `Fin.cons`-insertion `e.symm`.
    have hcomp : (fun z : E × (Fin n → E) =>
          g z.1 * ∏ j : Fin n, g (z.2 j))
        = fun z => (fun x : Fin (n + 1) → E => ∏ i, g (x i)) (e.symm z) := by
      funext z
      have hz : (e.symm z) = Fin.cons z.1 z.2 := by
        simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv_zero]
        rfl
      change g z.1 * ∏ j, g (z.2 j) = ∏ i, g ((e.symm z) i)
      rw [hz, Fin.prod_univ_succ, Fin.cons_zero]
      simp [Fin.cons_succ]
    calc
      Measure.pi (fun _ : Fin (n + 1) => μ.withDensity g)
          = Measure.map e.symm
              ((μ.withDensity g).prod
                (Measure.pi fun _ : Fin n => μ.withDensity g)) :=
            ((measurePreserving_piFinSuccAbove
              (fun _ : Fin (n + 1) => μ.withDensity g) 0).symm.map_eq).symm
      _ = Measure.map e.symm
              ((μ.withDensity g).prod
                ((Measure.pi fun _ : Fin n => μ).withDensity
                  (fun y : Fin n → E => ∏ j, g (y j)))) := by rw [ih]
      _ = Measure.map e.symm
              (((μ).prod (Measure.pi fun _ : Fin n => μ)).withDensity
                (fun z : E × (Fin n → E) => g z.1 * ∏ j, g (z.2 j))) := by
            rw [prod_withDensity hg hgprod]
      _ = (Measure.map e.symm
              ((μ).prod (Measure.pi fun _ : Fin n => μ))).withDensity
                (fun x : Fin (n + 1) → E => ∏ i, g (x i)) := by
            rw [hcomp, map_withDensity_comp e.symm _ hgprod']
      _ = (Measure.pi (fun _ : Fin (n + 1) => μ)).withDensity
                (fun x : Fin (n + 1) → E => ∏ i, g (x i)) := by
            rw [(measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm.map_eq]

/-- **Product `withDensity`, constant family over a finite index type.**
General-`Fintype` version of `pi_const_withDensity_fin`, transported along
`Fintype.equivFin` via `measurePreserving_piCongrLeft`. -/
private theorem pi_const_withDensity {ι : Type*} [Fintype ι] {E : Type*}
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] {g : E → ℝ≥0∞}
    (hg : Measurable g) [SigmaFinite (μ.withDensity g)] :
    Measure.pi (fun _ : ι => μ.withDensity g)
      = (Measure.pi (fun _ : ι => μ)).withDensity (fun x : ι → E => ∏ i, g (x i)) := by
  classical
  have hgprod : Measurable (fun x : ι → E => ∏ i, g (x i)) :=
    Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  set P : (Fin (Fintype.card ι) → E) ≃ᵐ (ι → E) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι => E) e with hP
  have hcomp : (fun y : Fin (Fintype.card ι) → E => ∏ i', g (y i'))
      = fun y => (fun x : ι → E => ∏ i, g (x i)) (P y) := by
    funext y
    change ∏ i', g (y i') = ∏ i, g ((P y) i)
    rw [← e.prod_comp (fun i => g ((P y) i))]
    refine Finset.prod_congr rfl fun i' _ => ?_
    rw [hP, MeasurableEquiv.piCongrLeft_apply_apply]
  calc
    Measure.pi (fun _ : ι => μ.withDensity g)
        = Measure.map P (Measure.pi (fun _ : Fin (Fintype.card ι) => μ.withDensity g)) := by
          rw [hP, (measurePreserving_piCongrLeft (α := fun _ : ι => E)
            (μ := fun _ => μ.withDensity g) e).map_eq]
    _ = Measure.map P ((Measure.pi (fun _ : Fin (Fintype.card ι) => μ)).withDensity
            (fun y : Fin (Fintype.card ι) → E => ∏ i', g (y i'))) := by
          rw [pi_const_withDensity_fin μ hg]
    _ = (Measure.map P (Measure.pi (fun _ : Fin (Fintype.card ι) => μ))).withDensity
            (fun x : ι → E => ∏ i, g (x i)) := by
          rw [hcomp, map_withDensity_comp P _ hgprod]
    _ = (Measure.pi (fun _ : ι => μ)).withDensity (fun x : ι → E => ∏ i, g (x i)) := by
          rw [hP, (measurePreserving_piCongrLeft (α := fun _ : ι => E) (μ := fun _ => μ) e).map_eq]

open Classical in
/-- **Real-factor inversion Jacobian on the mixed space.** Componentwise field
inversion `x ↦ (x w)⁻¹` on the real coordinate factor
`{w : InfinitePlace K // IsReal w} → ℝ` of `K_ℝ` pushes the additive Lebesgue
measure forward to the measure with density `∏_{w real} |x_w|⁻²` — one
`|x_w|⁻²` Jacobian factor per real place. Obtained from the one-dimensional
input `map_inv_volume_real_one` by the product change of variables
(`MeasureTheory.Measure.pi_map_pi` on `volume = Measure.pi (fun _ => volume)`,
then the `withDensity` of the product density). -/
theorem map_inv_volume_real :
    Measure.map
        (fun x : {w : InfinitePlace K // IsReal w} → ℝ => fun w => (x w)⁻¹)
        volume
      = volume.withDensity
          (fun x : {w : InfinitePlace K // IsReal w} → ℝ =>
            ∏ w, ENNReal.ofReal (‖x w‖ ^ 2)⁻¹) := by
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (‖t‖ ^ 2)⁻¹ with hg_def
  have hg : Measurable g := ((measurable_norm.pow_const 2).inv).ennreal_ofReal
  -- The 1-D push-forward `map (·⁻¹) volume` is `SigmaFinite` (its density is
  -- everywhere finite, since `ENNReal.ofReal _ ≠ ∞`).
  have hsf : SigmaFinite ((volume : Measure ℝ).map (fun t : ℝ => t⁻¹)) := by
    rw [map_inv_volume_real_one]
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  haveI : ∀ _ : {w : InfinitePlace K // IsReal w},
      SigmaFinite ((volume : Measure ℝ).map (fun t : ℝ => t⁻¹)) := fun _ => hsf
  haveI : SigmaFinite ((volume : Measure ℝ).withDensity g) :=
    SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  -- Rewrite the target `volume` as a product measure first (only on the RHS).
  conv_rhs => rw [show (volume : Measure ({w : InfinitePlace K // IsReal w} → ℝ))
        = Measure.pi (fun _ => (volume : Measure ℝ)) from volume_pi]
  -- `volume = Measure.pi (fun _ => volume)` and componentwise push-forward.
  rw [show (volume : Measure ({w : InfinitePlace K // IsReal w} → ℝ))
        = Measure.pi (fun _ => (volume : Measure ℝ)) from volume_pi,
    Measure.pi_map_pi (fun _ => measurable_inv.aemeasurable)]
  -- Each factor is the 1-D Jacobian; reassemble via the product `withDensity`.
  simp_rw [map_inv_volume_real_one]
  rw [pi_const_withDensity (volume : Measure ℝ) hg]

set_option maxHeartbeats 1000000 in
-- The assembly below combines two product-measure rewrites, a change of
-- variables, and a per-place norm factorisation; the elaboration of the
-- `ENNReal.ofReal`/`withDensity` algebra exceeds the default heartbeat budget.
/-- **Inversion-invariance of the multiplicative Haar measure** `d^*x`
(the standard treatment): the standard-normalised multiplicative Haar measure
`mixedMulHaar = (2/π)^{r₂}·|N(x)|^{-1}·dx` on `K_ℝ^*` is invariant under the
group inversion `x ↦ x⁻¹`. This is the measure-theoretic content of the Mellin
principle's change of variables: the density `|N(x)|^{-1}` is itself the
multiplicative Haar density, hence inversion-stable once paired with the
componentwise Jacobian. -/
theorem mixedMulHaar_map_inv :
    Measure.map (fun x : mixedEmbedding.mixedSpace K => x⁻¹) (mixedMulHaar K)
      = mixedMulHaar K := by
  classical
  have hinv : Measurable (fun x : mixedEmbedding.mixedSpace K => x⁻¹) :=
    measurable_fst.inv.prodMk measurable_snd.inv
  -- The multiplicative-Haar density constant `c = (2/π)^{r₂}` and the additive
  -- density `D(x) = c·|N(x)|⁻¹` against which `mixedMulHaar = volume.withDensity D`.
  set c : ℝ := (2 / Real.pi) ^ nrComplexPlaces K with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set D : mixedEmbedding.mixedSpace K → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (c * (mixedEmbedding.norm x)⁻¹) with hD
  have hDmeas : Measurable D :=
    (((mixedEmbedding.continuous_norm K).measurable.inv).const_mul c).ennreal_ofReal
  -- Per-factor inversion-Jacobian densities (from the two child lemmas).
  set Dr : ({w : InfinitePlace K // IsReal w} → ℝ) → ℝ≥0∞ :=
    fun a => ∏ w, ENNReal.ofReal (‖a w‖ ^ 2)⁻¹ with hDr
  set Dc : ({w : InfinitePlace K // IsComplex w} → ℂ) → ℝ≥0∞ :=
    fun b => ∏ w, ENNReal.ofReal (‖b w‖ ^ 4)⁻¹ with hDc
  have hDrmeas : Measurable Dr := by
    rw [hDr]; exact Finset.measurable_prod _ fun w _ => by fun_prop
  have hDcmeas : Measurable Dc := by
    rw [hDc]; exact Finset.measurable_prod _ fun w _ => by fun_prop
  have hJmeas : Measurable (fun z : mixedEmbedding.mixedSpace K => Dr z.1 * Dc z.2) :=
    (hDrmeas.comp measurable_fst).mul (hDcmeas.comp measurable_snd)
  -- `mixedMulHaar = volume.withDensity D` (definitional).
  have hμ : mixedMulHaar K = volume.withDensity D := rfl
  -- The componentwise factor inversions are measurable.
  have hfr : Measurable (fun a : {w : InfinitePlace K // IsReal w} → ℝ => fun w => (a w)⁻¹) := by
    fun_prop
  have hfc : Measurable
      (fun b : {w : InfinitePlace K // IsComplex w} → ℂ => fun w => (b w)⁻¹) := by fun_prop
  -- **Full inversion Jacobian on the additive volume** (Step 1): combine the two
  -- per-factor Jacobians through the product measure `volume = volume.prod volume`.
  have hJac : Measure.map (fun x : mixedEmbedding.mixedSpace K => x⁻¹) volume
      = volume.withDensity (fun z => Dr z.1 * Dc z.2) := by
    have hpm := Measure.map_prod_map
      (volume : Measure ({w : InfinitePlace K // IsReal w} → ℝ))
      (volume : Measure ({w : InfinitePlace K // IsComplex w} → ℂ)) hfr hfc
    rw [map_inv_volume_real, volume_pi_complex_map_inv,
      prod_withDensity hDrmeas hDcmeas] at hpm
    rw [show (fun x : mixedEmbedding.mixedSpace K => x⁻¹)
        = Prod.map (fun a : {w : InfinitePlace K // IsReal w} → ℝ => fun w => (a w)⁻¹)
            (fun b : {w : InfinitePlace K // IsComplex w} → ℂ => fun w => (b w)⁻¹) from rfl,
      Measure.volume_eq_prod]
    exact hpm.symm
  -- Change-of-variables principle along inversion for the additive volume.
  have hcov : ∀ φ : mixedEmbedding.mixedSpace K → ℝ≥0∞, Measurable φ →
      ∫⁻ a, φ a⁻¹ ∂(volume : Measure (mixedEmbedding.mixedSpace K))
        = ∫⁻ a, (Dr a.1 * Dc a.2) * φ a ∂volume := by
    intro φ hφ
    rw [← lintegral_map hφ hinv, hJac,
      lintegral_withDensity_eq_lintegral_mul _ hJmeas hφ]
    simp only [Pi.mul_apply]
  -- Norm in factored form: `N(x) = (∏_{real} |x_w|)·(∏_{complex} |z_w|²)`.
  have hval : ∀ x : mixedEmbedding.mixedSpace K,
      (∏ w : {w : InfinitePlace K // IsReal w}, (‖x.1 w‖ ^ 2)⁻¹)
        * (∏ w : {w : InfinitePlace K // IsComplex w}, (‖x.2 w‖ ^ 4)⁻¹)
        = ((mixedEmbedding.norm x) ^ 2)⁻¹ := by
    intro x
    have hreal : (∏ w : {w : InfinitePlace K // IsReal w},
          (normAtPlace w.1 x) ^ (mult w.1))
        = ∏ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖ :=
      Finset.prod_congr rfl fun w _ => by
        rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.prop]
    have hcpx : (∏ w : {w : InfinitePlace K // IsComplex w},
          (normAtPlace w.1 x) ^ (mult w.1))
        = ∏ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2 :=
      Finset.prod_congr rfl fun w _ => by
        rw [mult_isComplex, normAtPlace_apply_of_isComplex w.prop]
    have hn : mixedEmbedding.norm x
        = (∏ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖)
          * (∏ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2) := by
      rw [mixedEmbedding.norm_apply, InfinitePlace.prod_eq_prod_mul_prod, hreal, hcpx]
    rw [hn, mul_pow, mul_inv, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [show ((‖x.2 w‖ : ℝ) ^ 2) ^ 2 = ‖x.2 w‖ ^ 4 from by ring]
  -- **Pointwise Jacobian identity** (Step 2): `D(x⁻¹)·J(x) = D(x)` everywhere.
  have hpt : ∀ a : mixedEmbedding.mixedSpace K,
      D a⁻¹ * (Dr a.1 * Dc a.2) = D a := by
    intro a
    have h1 : D a⁻¹ = ENNReal.ofReal (c * mixedEmbedding.norm a) := by
      show ENNReal.ofReal (c * (mixedEmbedding.norm a⁻¹)⁻¹) = _
      rw [mixedEmbedding_norm_inv, inv_inv]
    have h2 : Dr a.1 * Dc a.2 = ENNReal.ofReal ((mixedEmbedding.norm a ^ 2)⁻¹) := by
      simp only [hDr, hDc]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity),
        ← ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity),
        ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => by positivity), hval a]
    rw [h1, h2,
      ← ENNReal.ofReal_mul (mul_nonneg hc0 (mixedEmbedding.norm_nonneg a))]
    show ENNReal.ofReal _ = ENNReal.ofReal (c * (mixedEmbedding.norm a)⁻¹)
    congr 1
    rw [mul_assoc]
    congr 1
    rcases eq_or_ne (mixedEmbedding.norm a) 0 with h | h
    · simp [h]
    · field_simp
  -- **Assembly** (Step 3): test both measures against an arbitrary measurable `g`.
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hginv : Measurable (fun a : mixedEmbedding.mixedSpace K => g a⁻¹) :=
    hg.comp hinv
  rw [hμ, lintegral_map hg hinv,
    lintegral_withDensity_eq_lintegral_mul _ hDmeas hginv,
    lintegral_withDensity_eq_lintegral_mul _ hDmeas hg]
  simp only [Pi.mul_apply]
  -- Goal: `∫⁻ a, D a * g a⁻¹ = ∫⁻ a, D a * g a`.
  have hφg : Measurable (fun a : mixedEmbedding.mixedSpace K => D a⁻¹ * g a) :=
    (hDmeas.comp hinv).mul hg
  calc ∫⁻ a, D a * g a⁻¹ ∂(volume : Measure (mixedEmbedding.mixedSpace K))
      = ∫⁻ a, (fun y => D y⁻¹ * g y) a⁻¹ ∂volume := by
        refine lintegral_congr fun a => ?_; simp only [inv_inv]
    _ = ∫⁻ a, (Dr a.1 * Dc a.2) * (D a⁻¹ * g a) ∂volume :=
        hcov (fun a => D a⁻¹ * g a) hφg
    _ = ∫⁻ a, D a * g a ∂volume := by
        refine lintegral_congr fun a => ?_
        rw [← mul_assoc, mul_comm (Dr a.1 * Dc a.2) (D a⁻¹), hpt a]

/-- The inversion `x ↦ x⁻¹` of `K_ℝ^*` is measurable (componentwise inverse on
the real/complex coordinates of the mixed space). -/
theorem measurable_mixedSpace_inv :
    Measurable (fun x : mixedEmbedding.mixedSpace K => x⁻¹) :=
  measurable_fst.inv.prodMk measurable_snd.inv

/-- Inversion of a nonnegative real base flips the sign of a complex exponent:
`((r⁻¹ : ℝ) : ℂ) ^ s = ((r : ℝ) : ℂ) ^ (-s)` for `0 ≤ r`. This is the scalar
norm-exponent flip behind the Mellin principle. -/
theorem ofReal_inv_cpow {r : ℝ} (hr : 0 ≤ r) (s : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ s = ((r : ℝ) : ℂ) ^ (-s) := by
  rcases eq_or_lt_of_le hr with rfl | hr'
  · simp only [inv_zero, Complex.ofReal_zero]
    rcases eq_or_ne s 0 with rfl | hs0
    · simp
    · rw [Complex.zero_cpow hs0, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · have h4 : (r : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr]; exact (Real.pi_ne_zero).symm
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ h4, Complex.cpow_neg]

/-- **Mellin-principle substitution** (the standard treatment): the change of
variables `x ↦ x⁻¹` in the multiplicative Mellin integral over `K_ℝ^*` is
measure-preserving, hence `∫ g(x) d^*x = ∫ g(x⁻¹) d^*x`. (The standard
measurability hypothesis on the integrand is required for the Bochner
change-of-variables; the theta-kernel integrand it is applied to satisfies it.) -/
theorem mulHaar_integral_comp_inv (g : mixedEmbedding.mixedSpace K → ℂ)
    (hg : AEStronglyMeasurable g (mixedMulHaar K)) :
    ∫ x, g x ∂(mixedMulHaar K) = ∫ x, g x⁻¹ ∂(mixedMulHaar K) := by
  have hmap := mixedMulHaar_map_inv (K := K)
  calc ∫ x, g x ∂(mixedMulHaar K)
      = ∫ x, g x ∂(Measure.map (fun x => x⁻¹) (mixedMulHaar K)) := by rw [hmap]
    _ = ∫ x, g x⁻¹ ∂(mixedMulHaar K) :=
        integral_map measurable_mixedSpace_inv.aemeasurable (hmap.symm ▸ hg)


/-! ## `IsFundamentalDomain` for the fundamental cone

The Mathlib cone `mixedEmbedding.fundamentalCone K` is a fundamental domain for
the `(𝓞 K)ˣ`-action **modulo torsion**: distinct non-torsion-equivalent units
give disjoint translates that tile the norm-nonzero locus. The full `(𝓞 K)ˣ`
action is *not* free on the cone (a torsion unit `ζ` maps the cone onto itself,
`fundamentalCone.torsion_smul_mem_of_mem`), so we cannot use `G = (𝓞 K)ˣ`
directly. Nor does the quotient `(𝓞 K)ˣ ⧸ torsion K` act on the mixed space
(picking a representative is not well defined). Instead we use a genuine
*complement* of `torsion K`: the free abelian group `ℤ^(rank K)`, embedded into
`(𝓞 K)ˣ` via the fundamental system `fundSystem` (Dirichlet's unit theorem,
`NumberField.Units.dirichletUnitTheorem.exist_unique_eq_mul_prod`). The acting
group is therefore `Multiplicative (Fin (rank K) → ℤ)`, acting through the
monoid hom `coneUnitHom` and the existing unit action. -/

open NumberField.Units NumberField.Units.dirichletUnitTheorem

-- `coneUnitHom`/`coneMulAction`/`coneSMul_def`/`coneUnitHom_mem_torsion_iff`/
-- `ae_norm_ne_zero` and the cone `IsFundamentalDomain` instance
-- (`isFundamentalDomain_fundamentalCone`) now live upstream in
-- `DedekindZeta/Statements.lean` (section `MulHaarRightInvariance`), next to
-- `mixedMulHaar`, so the `Statements`-layer cone change-of-domain lemma
-- `mixedMulHaar_integral_mul_right_cone_eq` can consume
-- them. They are in scope here via `open DedekindZeta` (same namespace). The cone
-- action instances are `local` in `Statements.lean`; re-activate them here so the
-- cone `IsFundamentalDomain` machinery below can synthesise the
-- `MulAction`/measurability/invariance/countability instances.
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
/-- **Inverse image of the fundamental cone is again a fundamental domain**
The set `(·⁻¹) '' fundamentalCone K` is a
`MeasureTheory.IsFundamentalDomain` for the *same* acting group
`Multiplicative (Fin (rank K) → ℤ)` (via `coneUnitHom` and the unit action) and
the *same* measure `mixedMulHaar K` as the cone itself
(`isFundamentalDomain_fundamentalCone`).  Proof: inversion `x ↦ x⁻¹` is an
involutive measure-preserving equivalence of the mixed space
(`measurable_mixedSpace_inv`, `mixedMulHaar_map_inv`) which intertwines the
action along the group inversion `g ↦ g⁻¹` of
`Multiplicative (Fin (rank K) → ℤ)`, since
`(g • x)⁻¹ = g⁻¹ • x⁻¹` (from `unitSMul_inv` through `coneUnitHom`).  Hence
`IsFundamentalDomain.image_of_equiv` transports the cone's fundamental-domain
property across inversion. -/
theorem isFundamentalDomain_inv_image_fundamentalCone :
    IsFundamentalDomain (Multiplicative (Fin (rank K) → ℤ))
      ((fun y : mixedEmbedding.mixedSpace K => y⁻¹) ''
        mixedEmbedding.fundamentalCone K) (mixedMulHaar K) := by
  have hmp : MeasurePreserving (fun x : mixedEmbedding.mixedSpace K => x⁻¹)
      (mixedMulHaar K) (mixedMulHaar K) :=
    ⟨measurable_mixedSpace_inv, mixedMulHaar_map_inv⟩
  have himg := (isFundamentalDomain_fundamentalCone (K := K)).image_of_equiv
    (Equiv.inv (mixedEmbedding.mixedSpace K))
    (by simpa using hmp.quasiMeasurePreserving)
    (Equiv.inv (Multiplicative (Fin (rank K) → ℤ)))
    (fun g x => by
      -- Semiconj: `(g⁻¹ • x)⁻¹ = g • x⁻¹`.
      simp only [Equiv.inv_apply]
      rw [coneSMul_def, coneSMul_def, map_inv, Theta.unitSMul_inv, inv_inv])
  simpa using himg

/-- **Inverse-cone change of domain**: for an `(𝓞 K)ˣ`-invariant
integrand `h` (`h (u • x) = h x`, the action being `mixedEmbedding.unitSMul`), the
`mixedMulHaar`-integral of `h` over the inverse cone `(·⁻¹) '' fundamentalCone K`
equals its integral over `fundamentalCone K`.

Both `fundamentalCone K` and its inverse image are fundamental domains for the
action of `(𝓞 K)ˣ` (modulo torsion) on the norm-nonzero locus of `K_ℝ` — the
inverse image because `x ↦ x⁻¹` commutes with the unit action
(`(u • x)⁻¹ = u⁻¹ • x⁻¹`, `unitSMul_inv`) and is `mixedMulHaar`-measure-preserving
(`mixedMulHaar_map_inv`). Hence the integral of a unit-invariant `h` over either
fundamental domain agrees (Mathlib `IsFundamentalDomain.setIntegral_eq`).

This is the change-of-domain identity consumed to pass
from the whole-space inversion substitution (`mulHaar_mellin_inv`) to the
fundamental-cone Mellin inversion identity. The genuine measure-theoretic
infrastructure it rests on — assembling the `IsFundamentalDomain` instance for
`fundamentalCone K` w.r.t. `mixedMulHaar K` and the measure-preserving unit
action — is established elsewhere in this development. -/
theorem mixedMulHaar_integral_inv_cone_eq
    (h : mixedEmbedding.mixedSpace K → ℂ)
    (hinv : ∀ (u : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K), h (u • x) = h x)
    (hmeas : AEStronglyMeasurable h (mixedMulHaar K))
    (hint : Integrable
      ((mixedEmbedding.fundamentalCone K).indicator h) (mixedMulHaar K)) :
    ∫ x, ((fun y => y⁻¹) '' mixedEmbedding.fundamentalCone K).indicator h x
          ∂(mixedMulHaar K)
      = ∫ x, (mixedEmbedding.fundamentalCone K).indicator h x ∂(mixedMulHaar K) := by
  classical
  haveI : Countable (Multiplicative (Fin (rank K) → ℤ)) :=
    inferInstanceAs (Countable (Fin (rank K) → ℤ))
  -- The inverse image is a measurable set: inversion is involutive, so the image
  -- equals the preimage of the (measurable) cone under the measurable map `·⁻¹`.
  have himg_eq : (fun y : mixedEmbedding.mixedSpace K => y⁻¹) ''
        mixedEmbedding.fundamentalCone K
      = (fun y : mixedEmbedding.mixedSpace K => y⁻¹) ⁻¹'
        mixedEmbedding.fundamentalCone K := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨x⁻¹, hx, inv_inv x⟩
  have hmeas_img : MeasurableSet ((fun y : mixedEmbedding.mixedSpace K => y⁻¹) ''
      mixedEmbedding.fundamentalCone K) := by
    rw [himg_eq]
    exact measurable_mixedSpace_inv (measurableSet_fundamentalCone K)
  -- `h` is invariant under the acting group `Multiplicative (Fin (rank K) → ℤ)`,
  -- since `g • x = coneUnitHom g • x` and `h` is `(𝓞 K)ˣ`-invariant by `hinv`.
  have hG : ∀ (g : Multiplicative (Fin (rank K) → ℤ))
      (x : mixedEmbedding.mixedSpace K), h (g • x) = h x := by
    intro g x
    rw [coneSMul_def]
    exact hinv (coneUnitHom (K := K) g) x
  -- Both the cone and its inverse image are fundamental domains for the same
  -- action and measure, so the integral of the invariant `h` agrees.
  rw [integral_indicator hmeas_img,
    integral_indicator (measurableSet_fundamentalCone K),
    (isFundamentalDomain_inv_image_fundamentalCone (K := K)).setIntegral_eq
      (isFundamentalDomain_fundamentalCone (K := K)) hG]


/-! ## Substituting the corrected (+1 / -1) kernel inversion law on the cone

The Mellin/functional-equation argument needs to substitute
the **corrected** inversion law `Theta.idealThetaKernel_inversion`

    idealThetaKernel K 𝔞 x⁻¹
      = (|N(x)| / covolume K 𝔞) · (mixedThetaKernel K (dualIdeal K 𝔞) x + 1) − 1

into the inverse-variant cone integrand `Θ(𝔞, x⁻¹)·N(x)^{-s}`.  On the
fundamental cone `N(x) > 0` (`fundamentalCone.norm_pos_of_mem`), so
`|N(x)| = N(x)` and `N(x)·N(x)^{-s} = N(x)^{1-s}` (`Complex.cpow_add` with the
nonzero base from `N(x) > 0`).  This leaves the dual-fractional-ideal integrand
at `1−s`, scaled by `1/covolume`, **plus** an explicit scalar correction

    𝒞(𝔞,s) integrand : (1/covolume K 𝔞)·N(x)^{1-s} − N(x)^{-s}

which must be discharged downstream.  The correction is kept fully
explicit (never folded into `0`) below. -/




end

end DedekindZeta

/-! ## Per-element scale invariance and the norm identity (the standard treatment, steps 1–2)

This section formalises the two per-element ingredients of the the analytic argument per-class
Gamma-integral evaluation:

* the **norm identity** `|N(σ a)| = 𝔑((a))` (`mixedEmbedding_norm_eq_absNorm_span`), and
* the **per-element multiplicative-Haar scale invariance**
  `∫_{K_ℝ^*} g(x·σ(a)) |N(x)|^s d^*x = 𝔑((a))^{-s} · I(s)`
  (`mellin_mixedGaussian_mul_eq`).

These live here (downstream of `I`/`mixedMulHaar`), since `GammaIntegral` imports
`Statements`/`Theta`; the archimedean factor `I K s` and the measure `mixedMulHaar`
are therefore in scope while `Statements` cannot refer to `I`.

Domain bookkeeping for the assembly: the identity is stated over
the **whole** group `K_ℝ^*` (= `mixedMulHaar`). The cone integral of
`idealThetaKernel K 𝔞` interchanges the element-sum out through the cone integral
(step 3); summing the per-element terms over a set of
`𝓞ˣ`-orbit representatives in `𝔞`, the translated cones `σ(u·a)•cone` tile `K_ℝ^*`
(the cone is a fundamental domain for `𝓞ˣ`, and units have `|N| = 1`), so each
orbit-sum of cone-terms equals the whole-space integral here — which is exactly
`𝔑((a))^{-s}·I(s)` per element/orbit. -/

namespace DedekindZeta.GammaIntegral

open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem

-- The cone action instances are `local` in `Statements.lean`; re-activate them here so
-- the cone `IsFundamentalDomain` machinery (`isFundamentalDomain_inv_image_fundamentalCone`)
-- can synthesise the `MulAction`/measurability/invariance instances.
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

-- the standard treatment (norm identity, step 2): `|N(σ a)| = 𝔑((a))`.
/-- **Norm identity** (the standard treatment): the archimedean norm of the Minkowski
embedding of `a : 𝓞 K` equals the absolute norm of the principal ideal `(a)`,
`|N(σ a)| = 𝔑((a))` (as nonnegative reals). Bridges
`mixedEmbedding.norm_eq_norm` (`= |Algebra.norm ℚ a|`) and
`Ideal.absNorm_span_singleton` (`= |Algebra.norm ℤ a|`). -/
theorem mixedEmbedding_norm_eq_absNorm_span (a : 𝓞 K) :
    mixedEmbedding.norm (mixedEmbedding K ((a : 𝓞 K) : K))
      = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs,
    Algebra.coe_norm_int, ← norm_eq_norm]

variable {K} in
/-- For `a ≠ 0` the Minkowski embedding `σ a = mixedEmbedding K a` has nonzero
archimedean norm, hence lies in the multiplicative group `K_ℝ^*`. -/
theorem norm_mixedEmbedding_ne_zero {a : 𝓞 K} (ha : a ≠ 0) :
    mixedEmbedding.norm (mixedEmbedding K ((a : 𝓞 K) : K)) ≠ 0 := by
  rw [mixedEmbedding_norm_eq_absNorm_span]
  have : Ideal.span {a} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr this)

-- the standard treatment (measure-theoretic helpers):
-- the measurability of the Gaussian × norm-power integrand.
-- (The right-translation change of variables `lintegral_comp_mul_right_mixedMulHaar`
-- and the measure right-invariance `mixedMulHaar_map_mul_right` now live upstream in
-- `DedekindZeta/Statements.lean`, next to `mixedMulHaar`, so that the
-- `Statements`-layer lemma `dualIdeal_cone_integral_eq` can consume them.)

variable {K} in
/-- **Measurability of the Mellin integrand** `y ↦ g(y·c)·|N(y)|^s` against
`mixedMulHaar` (the standard hypothesis for the Bochner change of variables). -/
theorem aestronglyMeasurable_mixedGaussian_mul_norm_cpow (s : ℂ)
    (c : mixedEmbedding.mixedSpace K) :
    AEStronglyMeasurable
      (fun y : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K y : ℂ) * (mixedEmbedding.norm (y * c) : ℂ) ^ s)
      (mixedMulHaar K) := by
  -- A Borel-measurable function into a second-countable space is
  -- `AEStronglyMeasurable` against any measure.
  apply Measurable.aestronglyMeasurable
  apply Measurable.mul
  · refine Complex.measurable_ofReal.comp ?_
    unfold mixedGaussian
    fun_prop
  · refine (Complex.measurable_ofReal.comp ?_).pow_const s
    exact (mixedEmbedding.continuous_norm K).measurable.comp
      (continuous_id.mul continuous_const).measurable

variable {K} in
/-- **Mellin-principle right-translation substitution**: the change of variables
`x ↦ x·c` (`N(c) ≠ 0`) is measure-preserving for `d^*x`, hence
`∫ g(x·c) d^*x = ∫ g(x) d^*x`. -/
theorem mulHaar_integral_comp_mul_right (g : mixedEmbedding.mixedSpace K → ℂ)
    {c : mixedEmbedding.mixedSpace K} (hc : mixedEmbedding.norm c ≠ 0)
    (hg : AEStronglyMeasurable g (mixedMulHaar K)) :
    ∫ x, g (x * c) ∂(mixedMulHaar K) = ∫ x, g x ∂(mixedMulHaar K) := by
  have hmap := mixedMulHaar_map_mul_right (K := K) hc
  calc ∫ x, g (x * c) ∂(mixedMulHaar K)
      = ∫ y, g y ∂(Measure.map (fun x => x * c) (mixedMulHaar K)) :=
        (integral_map (measurable_mul_right_mixedSpace K c).aemeasurable
          (hmap.symm ▸ hg)).symm
    _ = ∫ y, g y ∂(mixedMulHaar K) := by rw [hmap]

-- `mul_inv_cancel_of_norm_ne_zero` lives upstream in `DedekindZeta.Theta`
-- (single source of truth); it is in scope here via `open DedekindZeta.Theta`.

variable {K} in
-- the standard treatment (per-element scale invariance, step 1).
/-- **Per-element multiplicative-Haar scale invariance** (the standard treatment): for
`a ≠ 0`, the multiplicative Mellin transform of the single shifted Minkowski
Gaussian `x ↦ g(x·σ(a))` over `K_ℝ^*` collapses to the element-norm power times
the archimedean Gamma factor:

    ∫_{K_ℝ^*} g(x·σ(a)) |N(x)|^s d^*x = 𝔑((a))^{-s} · I(s).

Proof: left-translation invariance of `mixedMulHaar` under `x ↦ x·σ(a)`
(`mulHaar_integral_comp_mul_right`) turns the integrand into
`g(y)·|N(y·σ(a)⁻¹)|^s`; then `|N(y·σ(a)⁻¹)| = |N(y)|·|N(σ a)|⁻¹` and the norm
identity `|N(σ a)| = 𝔑((a))` factor out the constant `𝔑((a))^{-s}`. -/
theorem mellin_mixedGaussian_mul_eq (s : ℂ) {a : 𝓞 K} (ha : a ≠ 0) :
    ∫ x, (mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ s ∂(mixedMulHaar K)
      = (Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s) * I K s := by
  set c : mixedEmbedding.mixedSpace K := mixedEmbedding K ((a : 𝓞 K) : K) with hcdef
  have hcne : mixedEmbedding.norm c ≠ 0 := norm_mixedEmbedding_ne_zero ha
  have hcinv : mixedEmbedding.norm c⁻¹ ≠ 0 := by
    rw [mixedEmbedding_norm_inv]; exact inv_ne_zero hcne
  have hcc : c * c⁻¹ = 1 := Theta.mul_inv_cancel_of_norm_ne_zero K hcne
  have hnc : mixedEmbedding.norm c = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
    rw [hcdef]; exact mixedEmbedding_norm_eq_absNorm_span K a
  -- The integrand as `F (x * c)` with `F y = g y · |N(y·c⁻¹)|^s`.
  set F : mixedEmbedding.mixedSpace K → ℂ :=
    fun y => (mixedGaussian K y : ℂ) * (mixedEmbedding.norm (y * c⁻¹) : ℂ) ^ s with hFdef
  have hFmeas : AEStronglyMeasurable F (mixedMulHaar K) :=
    aestronglyMeasurable_mixedGaussian_mul_norm_cpow s c⁻¹
  have hrw : (fun x => (mixedGaussian K (x * c) : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
      = fun x => F (x * c) := by
    funext x
    simp only [hFdef, mul_assoc, hcc, mul_one]
  calc
    ∫ x, (mixedGaussian K (x * c) : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s ∂(mixedMulHaar K)
        = ∫ x, F (x * c) ∂(mixedMulHaar K) := by rw [hrw]
      _ = ∫ y, F y ∂(mixedMulHaar K) :=
          mulHaar_integral_comp_mul_right F hcne hFmeas
      _ = ∫ y, ((mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ s)
              * ((Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s)) ∂(mixedMulHaar K) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
          simp only [hFdef]
          rw [map_mul mixedEmbedding.norm y c⁻¹, mixedEmbedding_norm_inv,
            Complex.ofReal_mul,
            Complex.mul_cpow_ofReal_nonneg (mixedEmbedding.norm_nonneg y)
              (inv_nonneg.mpr (mixedEmbedding.norm_nonneg c)),
            ofReal_inv_cpow (mixedEmbedding.norm_nonneg c) s, hnc]
          push_cast
          ring
      _ = (∫ y, (mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ s ∂(mixedMulHaar K))
              * ((Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s)) :=
          integral_mul_const _ _
      _ = (Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s) * I K s := by
          rw [mul_comm]; rfl

set_option maxHeartbeats 1000000 in
variable {K} in
/-- **Integrability of the whole-space shifted Gaussian Mellin integrand**
(the standard treatment).  For `1 < Re s` and nonzero `a`, the single shifted Minkowski
Gaussian times norm-power `x ↦ g(x·σ a)·|N x|^s` is `mixedMulHaar`-integrable on
`K_ℝ^*`.  This is the integrability hypothesis required to feed the whole-space
Mellin integral `mellin_mixedGaussian_mul_eq` into the fundamental-domain
`IsFundamentalDomain.integral_eq_tsum''`/`hasSum_integral_measure` machinery used
by the single-orbit collapse `cone_integral_orbit_collapse`.

Route: the right translation `x ↦ x·σ a` is `mixedMulHaar`-measure-preserving
(`mulHaar_integral_comp_mul_right` infrastructure / `mixedMulHaar_map_mul_right`),
so integrability reduces to that of `y ↦ g(y)·|N(y·σ(a)⁻¹)|^s`; the latter
factors as `𝔑((a))^{-Re s}·(g(y)·|N y|^s)`, integrable by
`integrable_gaussian_mellin` (the `gaussian`/`mulHaar` form) transported through
the `mixedGaussian`/`mixedMulHaar` identifications. -/
theorem integrable_mixedGaussian_mul_norm_cpow (s : ℂ) (hs : 1 < s.re)
    {a : 𝓞 K} (ha : a ≠ 0) :
    Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedMulHaar K) := by
  have hs0 : (0 : ℝ) < s.re := lt_trans one_pos hs
  set c : mixedEmbedding.mixedSpace K := mixedEmbedding K ((a : 𝓞 K) : K) with hcdef
  have hcne : mixedEmbedding.norm c ≠ 0 := norm_mixedEmbedding_ne_zero ha
  have hcc : c * c⁻¹ = 1 := Theta.mul_inv_cancel_of_norm_ne_zero K hcne
  have hnc : mixedEmbedding.norm c = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
    rw [hcdef]; exact mixedEmbedding_norm_eq_absNorm_span K a
  -- The integrand as `F (x * c)` with `F y = g y · |N(y·c⁻¹)|^s`.
  set F : mixedEmbedding.mixedSpace K → ℂ :=
    fun y => (mixedGaussian K y : ℂ) * (mixedEmbedding.norm (y * c⁻¹) : ℂ) ^ s with hFdef
  -- `F` factors as the basic Mellin integrand times the constant `𝔑((a))^{-s}`.
  have hFeq : F = fun y => ((mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ s)
      * ((Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s)) := by
    funext y
    simp only [hFdef]
    rw [map_mul mixedEmbedding.norm y c⁻¹, mixedEmbedding_norm_inv,
      Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (mixedEmbedding.norm_nonneg y)
        (inv_nonneg.mpr (mixedEmbedding.norm_nonneg c)),
      ofReal_inv_cpow (mixedEmbedding.norm_nonneg c) s, hnc]
    push_cast
    ring
  -- The basic Mellin integrand is integrable by `integrable_gaussian_mellin`
  -- (defeq through `mixedGaussian = gaussian`, `mixedMulHaar = mulHaar`).
  have hbase : Integrable
      (fun y : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ s) (mixedMulHaar K) :=
    integrable_gaussian_mellin K hs0
  have hFint : Integrable F (mixedMulHaar K) := by
    rw [hFeq]; exact hbase.mul_const _
  -- Right translation `x ↦ x · c` is measure-preserving for `mixedMulHaar`.
  have hmp : MeasurePreserving (fun x : mixedEmbedding.mixedSpace K => x * c)
      (mixedMulHaar K) (mixedMulHaar K) :=
    ⟨measurable_mul_right_mixedSpace K c, mixedMulHaar_map_mul_right K hcne⟩
  have hrw : (fun x => (mixedGaussian K (x * c) : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
      = fun x => F (x * c) := by
    funext x
    simp only [hFdef, mul_assoc, hcc, mul_one]
  rw [hrw]
  exact hmp.integrable_comp_of_integrable hFint

-- The measure-preserving unit action infrastructure (`measurable_unitSMul`,
-- `mixedMulHaar_map_unitSMul`, `measurePreserving_unitSMul`) now lives upstream in
-- `DedekindZeta/Statements.lean`, next to `mixedMulHaar_map_mul_right`, so that the
-- `IsFundamentalDomain` infrastructure and the `Statements`-layer cone
-- change-of-domain lemmas can consume it.

-- `IsFundamentalDomain` for the fundamental cone and its
-- supporting `coneUnitHom`/`coneMulAction`/`ae_norm_ne_zero` infrastructure now live
-- upstream in `DedekindZeta/Statements.lean` (section `MulHaarRightInvariance`), next
-- to `mixedMulHaar`, so the `Statements`-layer cone change-of-domain lemmas
-- (`mixedMulHaar_integral_mul_right_cone_eq`) can consume
-- the `IsFundamentalDomain` instance. They are referenced here via `open DedekindZeta`.
-- The inverse-image fundamental domain (`isFundamentalDomain_inv_image_fundamentalCone`)
-- now lives in the `namespace DedekindZeta` block above (next to its consumer
-- `mixedMulHaar_integral_inv_cone_eq`).

/-! ## Step 3 of the per-class evaluation: interchange + cone collapse -/

open scoped nonZeroDivisors

variable {K} in
/-- **Measurability** of the single shifted Gaussian × norm-power integrand
`x ↦ g(x·c)·|N(x)|^s` (the shift acting on the left of the Gaussian's argument).
Companion to `aestronglyMeasurable_mixedGaussian_mul_norm_cpow` (which shifts the
norm factor instead); needed for the interchange step's `integral_tsum`. -/
theorem measurable_mixedGaussian_comp_mul_norm_cpow (s : ℂ)
    (c : mixedEmbedding.mixedSpace K) :
    Measurable
      (fun x : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K (x * c) : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s) := by
  apply Measurable.mul
  · refine Complex.measurable_ofReal.comp ?_
    unfold mixedGaussian
    fun_prop
  · exact (Complex.measurable_ofReal.comp
      (mixedEmbedding.continuous_norm K).measurable).pow_const s

variable {K} in
/-- **L¹/Tonelli finiteness** for the interchange step (the standard treatment): the
element-wise sum (over nonzero `a' ∈ a`) of the cone `lintegral`s of the `enorm`
of `g(x·σ a')·|N x|^s` is finite for `1 < Re s`.  This is the dominated/Tonelli
bound underlying the sum/integral interchange: grouping the `a'` into `𝓞ˣ`-orbits,
each orbit's cone-lintegrals sum to the whole-space integral
`𝔑((a'))^{-Re s}·I(Re s)`, and `∑` over orbits converges by
`summable_absNorm_neg_cpow`. -/
theorem tsum_lintegral_enorm_cone_mixedGaussian_ne_top (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    (∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun x => (mixedGaussian K
                (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ ∂(mixedMulHaar K))
      ≠ ∞ := by
  classical
  set C := mixedEmbedding.fundamentalCone K with hC
  set μ := mixedMulHaar K with hμ
  -- `s ≠ 0` (from `1 < Re s`), so `(0 : ℂ) ^ s = 0`.
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  -- Helper: the `enorm` of a nonnegative real, embedded in `ℂ`.
  have enorm_ofReal_nonneg : ∀ r : ℝ, 0 ≤ r → ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
    intro r hr
    calc ‖(r : ℂ)‖ₑ = ENNReal.ofReal ‖(r : ℂ)‖ := (ofReal_norm _).symm
      _ = ENNReal.ofReal r := by rw [Complex.norm_real, Real.norm_of_nonneg hr]
  -- The per-element nonnegative integrand whose `tsum` of `lintegral`s we bound.
  set f : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0}
      → mixedEmbedding.mixedSpace K → ℝ≥0∞ :=
    fun a' x => ‖C.indicator (fun x => (mixedGaussian K
          (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ with hf
  -- Each `f a'` is measurable (enorm of a Borel indicator of a Borel function).
  haveI : Countable (RingOfIntegers K) := by
    let b := Module.Free.chooseBasis ℤ (RingOfIntegers K)
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  have hmeas : ∀ a', AEMeasurable (f a') μ := by
    intro a'
    exact (((measurable_mixedGaussian_comp_mul_norm_cpow s
      (mixedEmbedding K ((a'.1 : RingOfIntegers K) : K))).indicator
      (measurableSet_fundamentalCone K)).enorm).aemeasurable
  -- Tonelli: pull the `tsum` (nonnegative summands) inside the `lintegral`.
  rw [← lintegral_tsum hmeas]
  -- Pointwise, the element-wise `tsum` of `enorm`s is the `enorm` of the cone
  -- indicator of `idealThetaKernel K a · |N x|^s`.
  set I : FractionalIdeal (RingOfIntegers K)⁰ K :=
    (a : FractionalIdeal (RingOfIntegers K)⁰ K) with hI
  have hIne : I ≠ 0 := by
    rw [hI]; exact (FractionalIdeal.coeIdeal_ne_zero).mpr ha
  -- Membership of integral elements in the coerced fractional ideal.
  have hmem : ∀ a' : RingOfIntegers K, a' ∈ a →
      ((a' : RingOfIntegers K) : K) ∈ (I : Submodule (RingOfIntegers K) K) := by
    intro a' ha'
    rw [FractionalIdeal.mem_coe, hI, RingOfIntegers.coe_eq_algebraMap]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ ha'
  have hpt : (fun x => ∑' a', f a' x)
      = (fun x => ‖C.indicator (fun x => Theta.idealThetaKernel K a x
            * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ) := by
    funext x
    by_cases hx : x ∈ C
    · -- On the cone the indicators are transparent.
      have hfx : ∀ a', f a' x = ‖(mixedGaussian K
            (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s‖ₑ := by
        intro a'; rw [hf]; simp only [Set.indicator_of_mem hx]
      simp only [hfx, enorm_mul, ENNReal.tsum_mul_right, Set.indicator_of_mem hx, enorm_mul]
      -- It remains to compare the bracketed factors.
      by_cases hN : mixedEmbedding.norm x = 0
      · -- `|N x| = 0` kills the common norm-power factor.
        have : ‖(mixedEmbedding.norm x : ℂ) ^ s‖ₑ = 0 := by
          rw [hN]; simp [Complex.zero_cpow hs0]
        rw [this, mul_zero, mul_zero]
      · -- `|N x| ≠ 0`: the Gaussian lattice sum is summable, so the two brackets agree.
        have hsumC : Summable (fun b : (I : Submodule (RingOfIntegers K) K) =>
            (mixedGaussian K (x * mixedEmbedding K (b : K)) : ℂ)) :=
          summable_mixedGaussian_submodule K I hIne hN
        have hsumR : Summable (fun b : (I : Submodule (RingOfIntegers K) K) =>
            mixedGaussian K (x * mixedEmbedding K (b : K))) :=
          Complex.summable_ofReal.mp hsumC
        -- Inject the index `{a' ∈ a, a' ≠ 0}` into the fractional-ideal lattice.
        let ι : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0}
            → (I : Submodule (RingOfIntegers K) K) :=
          fun a' => ⟨((a'.1 : RingOfIntegers K) : K), hmem a'.1 a'.2.1⟩
        have hι : Function.Injective ι := by
          intro a₁ a₂ h
          apply Subtype.ext
          apply RingOfIntegers.coe_injective
          exact congrArg (fun t : (I : Submodule (RingOfIntegers K) K) => (t : K)) h
        have hsumS : Summable (fun a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0} =>
            mixedGaussian K (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K))) :=
          (hsumR.comp_injective hι).congr (fun a' => rfl)
        have hnn : ∀ a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
            0 ≤ mixedGaussian K (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) :=
          fun a' => (Real.exp_pos _).le
        -- LHS bracket.
        have hL : (∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
              ‖(mixedGaussian K
                  (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)‖ₑ)
            = ENNReal.ofReal (∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
                mixedGaussian K (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K))) := by
          rw [ENNReal.ofReal_tsum_of_nonneg hnn hsumS]
          exact tsum_congr (fun a' => enorm_ofReal_nonneg _ (hnn a'))
        -- RHS bracket.
        have hR : ‖Theta.idealThetaKernel K a x‖ₑ
            = ENNReal.ofReal (∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
                mixedGaussian K (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K))) := by
          rw [Theta.idealThetaKernel, ← Complex.ofReal_tsum,
            enorm_ofReal_nonneg _ (tsum_nonneg hnn)]
        rw [hL, hR]
    · -- Off the cone every indicator vanishes.
      have hfx : ∀ a', f a' x = 0 := by
        intro a'; rw [hf]; simp only [Set.indicator_of_notMem hx, enorm_zero]
      simp only [hfx, tsum_zero, Set.indicator_of_notMem hx, enorm_zero]
  rw [hpt]
  -- Identify `idealThetaKernel` with `mixedThetaKernel` of the coerced ideal and
  -- conclude finiteness from `integrable_indicator_mixedThetaKernel_mul_norm_cpow`.
  simp only [Theta.idealThetaKernel_eq_mixed, ← hI]
  have hint := integrable_indicator_mixedThetaKernel_mul_norm_cpow K I s hs
  exact (hint.hasFiniteIntegral).ne

variable {K} in
/-- **Step 3 / interchange** (the standard analytic argument).  The cone integral of
`idealThetaKernel K a · |N|^s` is the element-wise sum over the nonzero elements
of `a` of the cone integrals of the single shifted Minkowski Gaussians
`g(x·σ a') · |N x|^s`.  This is the sum/integral interchange step: pull the
defining `∑'` of `idealThetaKernel` (Tonelli for the nonnegative Gaussian /
dominated convergence for `1 < Re s`, dominating series
`summable_absNorm_neg_cpow`) out through the cone integral and the indicator. -/
theorem cone_integral_idealThetaKernel_eq_tsum (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    ∫ x, (mixedEmbedding.fundamentalCone K).indicator
            (fun x => Theta.idealThetaKernel K a x * (mixedEmbedding.norm x : ℂ) ^ s) x
          ∂(mixedMulHaar K)
      = ∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
          ∫ x, (mixedEmbedding.fundamentalCone K).indicator
              (fun x => (mixedGaussian K
                  (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
                * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K) := by
  classical
  haveI : Countable (RingOfIntegers K) := by
    let b := Module.Free.chooseBasis ℤ (RingOfIntegers K)
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  set C := mixedEmbedding.fundamentalCone K with hC
  set μ := mixedMulHaar K with hμ
  -- The per-element indicator integrand `F a'`.
  set F : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0}
      → mixedEmbedding.mixedSpace K → ℂ :=
    fun a' x => C.indicator
      (fun x => (mixedGaussian K
          (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
        * (mixedEmbedding.norm x : ℂ) ^ s) x with hF
  -- Each `F a'` is `AEStronglyMeasurable` (Borel indicator of a Borel function).
  have hmeas : ∀ a', AEStronglyMeasurable (F a') μ := by
    intro a'
    exact ((measurable_mixedGaussian_comp_mul_norm_cpow s
      (mixedEmbedding K ((a'.1 : RingOfIntegers K) : K))).aestronglyMeasurable).indicator
      (measurableSet_fundamentalCone K)
  -- The `lintegral`-norm series is finite, so `integral_tsum` applies.
  have hfin : (∑' a', ∫⁻ x, ‖F a' x‖ₑ ∂μ) ≠ ∞ :=
    tsum_lintegral_enorm_cone_mixedGaussian_ne_top s hs ha
  have key := integral_tsum (μ := μ) (f := F) hmeas hfin
  -- Pointwise, the indicator of the kernel × norm-power equals `∑' a', F a' x`.
  have hpt : (fun x => C.indicator
        (fun x => Theta.idealThetaKernel K a x * (mixedEmbedding.norm x : ℂ) ^ s) x)
      = (fun x => ∑' a', F a' x) := by
    funext x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]
      have hFx : ∀ a', F a' x
          = (mixedGaussian K
              (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ s := by
        intro a'; rw [hF]; simp only [Set.indicator_of_mem hx]
      simp only [hFx]
      rw [Theta.idealThetaKernel, ← tsum_mul_right]
    · rw [Set.indicator_of_notMem hx]
      have hFx : ∀ a', F a' x = 0 := by
        intro a'; rw [hF]; simp only [Set.indicator_of_notMem hx]
      simp only [hFx, tsum_zero]
  rw [hpt, key]

open scoped Pointwise in
variable {K} in
/-- **Step 3 / single-orbit collapse** (the standard analytic argument).  For a fixed
nonzero `a₀ : 𝓞 K`, the sum over the full unit group `(𝓞 K)ˣ` of the cone
integrals of `g(x·σ(u·a₀))·|N x|^s` collapses to `w_K · I(s) · 𝔑((a₀))^{-s}`.

This is the analytic heart of the fundamental-cone collapse: the map
`u ↦ ↑u · a₀` is injective (domain, `a₀ ≠ 0`) with image the `𝓞ˣ`-orbit
generating the principal ideal `span {a₀}`; `g(x·σ(↑u·a₀)) = g((u • x)·σ a₀)`
and `|N (u • x)| = |N x|` (`idealThetaKernel_mul_norm_cpow_unitSMul` /
`norm_unitSMul`), so each torsion coset contributes the whole-space integral
`∫_{K_ℝ^*} g(x·σ a₀)·|N x|^s d*x = 𝔑((a₀))^{-s}·I(s)`
(`mellin_mixedGaussian_mul_eq`), summed via the fundamental-cone
`IsFundamentalDomain` (`isFundamentalDomain_fundamentalCone`,
`IsFundamentalDomain.integral_eq_tsum`) over the free unit complement, times the
`w_K = torsionOrder K` torsion cosets. -/
theorem cone_integral_orbit_collapse (s : ℂ) (hs : 1 < s.re)
    {a₀ : RingOfIntegers K} (ha₀ : a₀ ≠ 0) :
    ∑' u : (RingOfIntegers K)ˣ,
          ∫ x, (mixedEmbedding.fundamentalCone K).indicator
              (fun x => (mixedGaussian K
                  (x * mixedEmbedding K
                    (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K)) : ℂ)
                * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K)
      = (Units.torsionOrder K : ℂ) * I K s *
          (Ideal.absNorm (Ideal.span {a₀}) : ℂ) ^ (-s) := by
  classical
  -- The shift `σ a₀` and the whole-space integrand `F y = g(y·σ a₀)·|N y|^s`.
  set c₀ : mixedEmbedding.mixedSpace K :=
    mixedEmbedding K ((a₀ : RingOfIntegers K) : K) with hc₀
  set F : mixedEmbedding.mixedSpace K → ℂ :=
    fun y => (mixedGaussian K (y * c₀) : ℂ) * (mixedEmbedding.norm y : ℂ) ^ s with hF
  -- Whole-space integrability and Mellin value of `F`.
  have hint : Integrable F (mixedMulHaar K) := by
    rw [hF, hc₀]; exact integrable_mixedGaussian_mul_norm_cpow s hs ha₀
  have hV : ∫ x, F x ∂(mixedMulHaar K)
      = (Ideal.absNorm (Ideal.span {a₀}) : ℂ) ^ (-s) * I K s := by
    rw [hF, hc₀]; exact mellin_mixedGaussian_mul_eq s ha₀
  -- The cone integrals along the free-complement action.
  let A : Multiplicative (Fin (rank K) → ℤ) → ℂ :=
    fun g => ∫ x in mixedEmbedding.fundamentalCone K, F (g • x) ∂(mixedMulHaar K)
  -- `HasSum A (∫ F)` from the cone fundamental domain.
  have hFD := isFundamentalDomain_fundamentalCone (K := K)
  have hAeq : (fun g : Multiplicative (Fin (rank K) → ℤ) =>
        ∫ x, F x ∂((mixedMulHaar K).restrict (g • mixedEmbedding.fundamentalCone K))) = A := by
    funext g
    show ∫ x in g • mixedEmbedding.fundamentalCone K, F x ∂(mixedMulHaar K)
        = ∫ x in mixedEmbedding.fundamentalCone K, F (g • x) ∂(mixedMulHaar K)
    rw [← (measurePreserving_smul g (mixedMulHaar K)).setIntegral_image_emb
          (measurableEmbedding_const_smul g) F (mixedEmbedding.fundamentalCone K),
      Set.image_smul]
  have hHS : HasSum A (∫ x, F x ∂(mixedMulHaar K)) := by
    have hms := hFD.sum_restrict
    have hintsum : Integrable F
        (Measure.sum (fun g : Multiplicative (Fin (rank K) → ℤ) => (mixedMulHaar K).restrict
          (g • mixedEmbedding.fundamentalCone K))) := by rw [hms]; exact hint
    have h0 := hasSum_integral_measure hintsum
    rw [hms] at h0
    rwa [hAeq] at h0
  have hsummableA : Summable A := hHS.summable
  have htsumA : ∑' g, A g = ∫ x, F x ∂(mixedMulHaar K) := hHS.tsum_eq
  -- Per-unit integrand collapses to `F (u • x)`.
  have hF_smul : ∀ (u : (RingOfIntegers K)ˣ) (x : mixedEmbedding.mixedSpace K),
      F (u • x) = (mixedGaussian K
          (x * mixedEmbedding K (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K)) : ℂ)
        * (mixedEmbedding.norm x : ℂ) ^ s := by
    intro u x
    have harg : (u • x) * c₀ = x * mixedEmbedding K
        (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K) := by
      rw [hc₀, unitSMul_smul,
        show (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K)
            = ((u : RingOfIntegers K) : K) * ((a₀ : RingOfIntegers K) : K) by push_cast; ring,
        map_mul]
      ring
    have hnorm : mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := norm_unit_smul u x
    simp only [hF]
    rw [harg, hnorm]
  -- The reindexing of the unit group by `torsion × free` (Dirichlet).
  let f₀ : torsion K × (Fin (rank K) → ℤ) → (RingOfIntegers K)ˣ :=
    fun p => (p.1 : (RingOfIntegers K)ˣ) * ∏ i, fundSystem K i ^ (p.2 i)
  have hf₀app : ∀ p, f₀ p
      = (p.1 : (RingOfIntegers K)ˣ) * ∏ i, fundSystem K i ^ (p.2 i) := fun _ => rfl
  have hbij : Function.Bijective f₀ := by
    refine ⟨fun p q h => ?_, fun x => ?_⟩
    · exact (exist_unique_eq_mul_prod K (f₀ p)).unique (hf₀app p) (by rw [h])
    · obtain ⟨p, hp, -⟩ := exist_unique_eq_mul_prod K x
      exact ⟨p, (hf₀app p).trans hp.symm⟩
  let ev : (torsion K × (Fin (rank K) → ℤ)) ≃ (RingOfIntegers K)ˣ :=
    Equiv.ofBijective f₀ hbij
  -- The free-part summand, indexed additively.
  let Ã : (Fin (rank K) → ℤ) → ℂ := fun e => A (Multiplicative.ofAdd e)
  -- Each unit-coset cone integral collapses to a free-part cone integral.
  have hBev : ∀ p : torsion K × (Fin (rank K) → ℤ),
      (∫ x in mixedEmbedding.fundamentalCone K, F ((ev p) • x) ∂(mixedMulHaar K)) = Ã p.2 := by
    rintro ⟨ζ, e⟩
    have hcu : (coneUnitHom (K := K) (Multiplicative.ofAdd e) : (RingOfIntegers K)ˣ)
        = ∏ i, fundSystem K i ^ (e i) := by simp [coneUnitHom]
    have hev : ev (ζ, e)
        = (ζ : (RingOfIntegers K)ˣ) * coneUnitHom (K := K) (Multiplicative.ofAdd e) := by
      show f₀ (ζ, e) = _
      show (ζ : (RingOfIntegers K)ˣ) * ∏ i, fundSystem K i ^ (e i)
          = (ζ : (RingOfIntegers K)ˣ) * coneUnitHom (K := K) (Multiplicative.ofAdd e)
      rw [hcu]
    have hcomm : ∀ y : mixedEmbedding.mixedSpace K,
        (ev (ζ, e)) • y
          = (coneUnitHom (K := K) (Multiplicative.ofAdd e)) • ((ζ : (RingOfIntegers K)ˣ) • y) := by
      intro y
      rw [hev, mul_smul]
      simp only [unitSMul_smul]
      ring
    have himg : (fun y : mixedEmbedding.mixedSpace K => (ζ : (RingOfIntegers K)ˣ) • y) ''
          mixedEmbedding.fundamentalCone K = mixedEmbedding.fundamentalCone K := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact fundamentalCone.torsion_smul_mem_of_mem hz ζ.2
      · intro hy
        exact ⟨(ζ : (RingOfIntegers K)ˣ)⁻¹ • y,
          fundamentalCone.torsion_smul_mem_of_mem hy ((torsion K).inv_mem ζ.2),
          by simp only [smul_smul, mul_inv_cancel, one_smul]⟩
    let ψ : mixedEmbedding.mixedSpace K ≃ᵐ mixedEmbedding.mixedSpace K :=
      { toFun := fun y => (ζ : (RingOfIntegers K)ˣ) • y
        invFun := fun y => (ζ : (RingOfIntegers K)ˣ)⁻¹ • y
        left_inv := fun y => by simp only [smul_smul, inv_mul_cancel, one_smul]
        right_inv := fun y => by simp only [smul_smul, mul_inv_cancel, one_smul]
        measurable_toFun := measurable_unitSMul _
        measurable_invFun := measurable_unitSMul _ }
    have hmp : MeasurePreserving (fun y : mixedEmbedding.mixedSpace K =>
        (ζ : (RingOfIntegers K)ˣ) • y) (mixedMulHaar K) (mixedMulHaar K) :=
      measurePreserving_unitSMul (ζ : (RingOfIntegers K)ˣ)
    calc ∫ x in mixedEmbedding.fundamentalCone K, F ((ev (ζ, e)) • x) ∂(mixedMulHaar K)
        = ∫ x in mixedEmbedding.fundamentalCone K,
            F ((coneUnitHom (K := K) (Multiplicative.ofAdd e)) • ((ζ : (RingOfIntegers K)ˣ) • x))
              ∂(mixedMulHaar K) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          simp only [hcomm]
      _ = ∫ y in (fun y => (ζ : (RingOfIntegers K)ˣ) • y) ''
              mixedEmbedding.fundamentalCone K,
            F ((coneUnitHom (K := K) (Multiplicative.ofAdd e)) • y) ∂(mixedMulHaar K) :=
          (hmp.setIntegral_image_emb ψ.measurableEmbedding
            (fun y => F ((coneUnitHom (K := K) (Multiplicative.ofAdd e)) • y))
            (mixedEmbedding.fundamentalCone K)).symm
      _ = ∫ y in mixedEmbedding.fundamentalCone K,
            F ((coneUnitHom (K := K) (Multiplicative.ofAdd e)) • y) ∂(mixedMulHaar K) := by
          rw [himg]
      _ = Ã e := rfl
  -- Summability transported to the additive free part.
  have hsummableÃ : Summable Ã :=
    (Equiv.summable_iff (Multiplicative.ofAdd)).mpr hsummableA
  have htsumÃ : ∑' e, Ã e = ∫ x, F x ∂(mixedMulHaar K) :=
    (Equiv.tsum_eq (Multiplicative.ofAdd) A).trans htsumA
  -- Summability of the torsion-indexed family `(ζ, e) ↦ Ã e`.
  letI : Fintype (torsion K) := Fintype.ofFinite _
  have hSumProd : Summable (fun p : torsion K × (Fin (rank K) → ℤ) => Ã p.2) := by
    have hsplit : (fun p : torsion K × (Fin (rank K) → ℤ) => Ã p.2)
        = fun p => ∑ ζ ∈ (Finset.univ : Finset (torsion K)),
            (fun q : torsion K × (Fin (rank K) → ℤ) => if q.1 = ζ then Ã q.2 else 0) p := by
      funext p
      simp
    rw [hsplit]
    apply summable_sum
    intro ζ _
    have hi : Function.Injective
        (fun e : (Fin (rank K) → ℤ) => ((ζ, e) : torsion K × (Fin (rank K) → ℤ))) := by
      intro a b h; simpa using h
    refine (Function.Injective.summable_iff hi ?_).mp ?_
    · intro q hq
      by_cases heq : q.1 = ζ
      · exact absurd ⟨q.2, by simp [← heq]⟩ hq
      · simp [heq]
    · have hcomp : ((fun q : torsion K × (Fin (rank K) → ℤ) =>
            if q.1 = ζ then Ã q.2 else 0) ∘ fun e => ((ζ, e) : torsion K × (Fin (rank K) → ℤ)))
          = Ã := by funext e; simp
      rw [hcomp]; exact hsummableÃ
  -- Reduce each unit term to a cone integral, then assemble.
  have hterm : ∀ u : (RingOfIntegers K)ˣ,
      (∫ x, (mixedEmbedding.fundamentalCone K).indicator
          (fun x => (mixedGaussian K
              (x * mixedEmbedding K
                (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K)) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K))
        = ∫ x in mixedEmbedding.fundamentalCone K, F (u • x) ∂(mixedMulHaar K) := by
    intro u
    rw [integral_indicator (measurableSet_fundamentalCone K)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact (hF_smul u x).symm
  have hstep2 : (∑' u : (RingOfIntegers K)ˣ,
        ∫ x in mixedEmbedding.fundamentalCone K, F (u • x) ∂(mixedMulHaar K))
      = ∑' p : torsion K × (Fin (rank K) → ℤ), Ã p.2 := by
    rw [← Equiv.tsum_eq ev
        (fun u => ∫ x in mixedEmbedding.fundamentalCone K, F (u • x) ∂(mixedMulHaar K))]
    exact tsum_congr (fun p => hBev p)
  rw [tsum_congr hterm]
  calc ∑' u : (RingOfIntegers K)ˣ,
          ∫ x in mixedEmbedding.fundamentalCone K, F (u • x) ∂(mixedMulHaar K)
      = ∑' p : torsion K × (Fin (rank K) → ℤ), Ã p.2 := hstep2
    _ = ∑' (ζ : torsion K), ∑' (c : (Fin (rank K) → ℤ)), Ã (ζ, c).2 := hSumProd.tsum_prod
    _ = ∑' (_ : torsion K), ∫ x, F x ∂(mixedMulHaar K) :=
        tsum_congr (fun ζ => by simpa using htsumÃ)
    _ = (Fintype.card (torsion K) : ℂ) * ∫ x, F x ∂(mixedMulHaar K) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Units.torsionOrder K : ℂ) * I K s
          * (Ideal.absNorm (Ideal.span {a₀}) : ℂ) ^ (-s) := by
        have hCard : (Units.torsionOrder K : Complex) = (Fintype.card (torsion K) : Complex) := by
          rw [Units.torsionOrder, Nat.card_eq_fintype_card]
        rw [hV, hCard]
        ring

set_option maxHeartbeats 1600000 in
variable {K} in
/-- **Step 3 / fundamental-cone collapse + multiplicity count** (the standard analytic argument
4/).  The element-wise sum (over nonzero `a' ∈ a`) of the cone integrals of
`g(x·σ a') · |N x|^s` collapses to `w_K · I(s)` times the partial zeta over the
nonzero principal ideals divisible by `a`.

Route: the fundamental cone is an `IsFundamentalDomain` for the free unit
complement (`isFundamentalDomain_fundamentalCone`); grouping the `a'` into
`𝓞ˣ`-orbits, each orbit's cone-terms sum (via `measurePreserving_unitSMul`,
`idealThetaKernel_mul_norm_cpow_unitSMul`) to the whole-space integral
`∫_{K_ℝ^*} g(x·σ a')·|N x|^s d*x = 𝔑((a'))^{-s} · I(s)`
(`mellin_mixedGaussian_mul_eq`), and each nonzero principal ideal divisible by
`a` is hit exactly `w_K = torsionOrder K` times
(`fundamentalCone.idealSetEquivNorm` / `card_isPrincipal_norm_eq_mul_torsion`). -/
theorem tsum_cone_integral_mixedGaussian_eq (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    ∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
          ∫ x, (mixedEmbedding.fundamentalCone K).indicator
              (fun x => (mixedGaussian K
                  (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
                * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K)
      = (Units.torsionOrder K : ℂ) * I K s *
          ∑' I : {I : (Ideal (RingOfIntegers K))⁰ //
                    (a ∣ (I : Ideal (RingOfIntegers K))) ∧
                      Submodule.IsPrincipal (I : Ideal (RingOfIntegers K))},
              (Ideal.absNorm (I : Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by
  classical
  set T := {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0} with hT
  set Idx := {J : (Ideal (RingOfIntegers K))⁰ //
      (a ∣ (J : Ideal (RingOfIntegers K))) ∧
        Submodule.IsPrincipal (J : Ideal (RingOfIntegers K))} with hIdx
  -- The element-wise cone-integral summand.
  set Φ : T → ℂ := fun a' => ∫ x, (mixedEmbedding.fundamentalCone K).indicator
      (fun x => (mixedGaussian K
          (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
        * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K) with hΦ
  -- A chosen generator of each principal ideal in the index set.
  let gen : Idx → RingOfIntegers K := fun J =>
    letI := J.2.2
    Submodule.IsPrincipal.generator
      ((J : (Ideal (RingOfIntegers K))⁰) : Ideal (RingOfIntegers K))
  have hgen : ∀ J : Idx, ((J : (Ideal (RingOfIntegers K))⁰) : Ideal (RingOfIntegers K))
      = Ideal.span {gen J} := by
    intro J
    letI := J.2.2
    exact (Submodule.IsPrincipal.span_singleton_generator _).symm
  -- The generator is nonzero (its span is the nonzero ideal `J`).
  have hgne : ∀ J : Idx, gen J ≠ 0 := by
    intro J h
    have hbot : ((J : (Ideal (RingOfIntegers K))⁰) : Ideal (RingOfIntegers K)) = ⊥ := by
      rw [hgen J, h]; exact Ideal.span_singleton_eq_bot.mpr rfl
    exact (mem_nonZeroDivisors_iff_ne_zero.mp J.1.2)
      (by rw [Ideal.zero_eq_bot]; exact hbot)
  -- The generator lies in `a` (since `a ∣ J = span {gen J}`).
  have hmemgen : ∀ J : Idx, gen J ∈ a := by
    intro J
    have hle : (Ideal.span {gen J} : Ideal (RingOfIntegers K)) ≤ a := by
      rw [← hgen J]; exact Ideal.dvd_iff_le.mp J.2.1
    exact (Ideal.span_singleton_le_iff_mem a).mp hle
  -- `span {↑u * x} = span {x}` for a unit `u`.
  have hspan_unit : ∀ (u : (RingOfIntegers K)ˣ) (x : RingOfIntegers K),
      Ideal.span {(u : RingOfIntegers K) * x} = Ideal.span {x} := by
    intro u x
    rw [Ideal.span_singleton_eq_span_singleton]
    exact ⟨u⁻¹, by rw [mul_right_comm, Units.mul_inv, one_mul]⟩
  -- The reindexing map `Σ J, units → {a' ∈ a, a' ≠ 0}`, `(J, u) ↦ ↑u · gen J`.
  set f : (Σ _ : Idx, (RingOfIntegers K)ˣ) → T :=
    fun p => ⟨(p.2 : RingOfIntegers K) * gen p.1,
      Ideal.mul_mem_left a (p.2 : RingOfIntegers K) (hmemgen p.1),
      mul_ne_zero p.2.ne_zero (hgne p.1)⟩ with hf
  have hinj : Function.Injective f := by
    rintro ⟨J1, u1⟩ ⟨J2, u2⟩ h
    have hval : (u1 : RingOfIntegers K) * gen J1 = (u2 : RingOfIntegers K) * gen J2 := by
      have := congrArg Subtype.val h
      simpa [hf] using this
    have hJ : ((J1 : (Ideal (RingOfIntegers K))⁰) : Ideal (RingOfIntegers K))
        = ((J2 : (Ideal (RingOfIntegers K))⁰) : Ideal (RingOfIntegers K)) := by
      rw [hgen J1, hgen J2, ← hspan_unit u1 (gen J1), ← hspan_unit u2 (gen J2), hval]
    have hJeq : J1 = J2 := Subtype.ext (Subtype.ext hJ)
    subst hJeq
    have huu := mul_right_cancel₀ (hgne J1) hval
    exact congrArg (Sigma.mk J1) (Units.ext huu)
  have hsurj : Function.Surjective f := by
    rintro ⟨a', ha'mem, ha'ne⟩
    have hJne : Ideal.span {a'} ∈ (Ideal (RingOfIntegers K))⁰ := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro h
      exact ha'ne (Ideal.span_singleton_eq_bot.mp (by rw [← Ideal.zero_eq_bot]; exact h))
    have hdvd : a ∣ ((⟨Ideal.span {a'}, hJne⟩ : (Ideal (RingOfIntegers K))⁰) :
        Ideal (RingOfIntegers K)) :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem a).mpr ha'mem)
    have hprin : Submodule.IsPrincipal
        ((⟨Ideal.span {a'}, hJne⟩ : (Ideal (RingOfIntegers K))⁰) :
          Ideal (RingOfIntegers K)) := ⟨a', rfl⟩
    set J : Idx := ⟨⟨Ideal.span {a'}, hJne⟩, hdvd, hprin⟩ with hJdef
    have hgenJ : Ideal.span {a'} = Ideal.span {gen J} := hgen J
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hgenJ
    refine ⟨⟨J, v⁻¹⟩, ?_⟩
    apply Subtype.ext
    show ((v⁻¹ : (RingOfIntegers K)ˣ) : RingOfIntegers K) * gen J = a'
    rw [← hv, mul_comm a' (v : RingOfIntegers K), ← mul_assoc, Units.inv_mul, one_mul]
  set e : (Σ _ : Idx, (RingOfIntegers K)ˣ) ≃ T := Equiv.ofBijective f ⟨hinj, hsurj⟩ with he
  -- Summability of the `a'`-family from the L¹/Tonelli finiteness.
  have hfin := tsum_lintegral_enorm_cone_mixedGaussian_ne_top s hs ha
  have hbsum : Summable (fun a' : T => (∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
        (fun x => (mixedGaussian K
            (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ ∂(mixedMulHaar K)).toReal) :=
    ENNReal.summable_toReal hfin
  have hbound : ∀ a' : T, ‖Φ a'‖ ≤ (∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
        (fun x => (mixedGaussian K
            (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ ∂(mixedMulHaar K)).toReal := by
    intro a'
    have hne := ENNReal.ne_top_of_tsum_ne_top hfin a'
    have key : ‖Φ a'‖ₑ ≤ ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
        (fun x => (mixedGaussian K
            (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ ∂(mixedMulHaar K) := by
      simp only [hΦ]; exact enorm_integral_le_lintegral_enorm _
    calc ‖Φ a'‖ = (‖Φ a'‖ₑ).toReal := (toReal_enorm (Φ a')).symm
      _ ≤ _ := ENNReal.toReal_mono hne key
  have hΦsum : Summable Φ := Summable.of_norm_bounded hbsum hbound
  have hcompsum : Summable (fun p => Φ (e p)) := (Equiv.summable_iff e).mpr hΦsum
  -- The single-orbit collapse evaluates each inner unit-sum.
  have hinner : ∀ J : Idx, (∑' u : (RingOfIntegers K)ˣ, Φ (e ⟨J, u⟩))
      = (Units.torsionOrder K : ℂ) * I K s
          * (Ideal.absNorm ((J : (Ideal (RingOfIntegers K))⁰) :
              Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by
    intro J
    have hc := cone_integral_orbit_collapse s hs (hgne J)
    rw [← hgen J] at hc
    rw [← hc]
    exact tsum_congr (fun u => rfl)
  rw [← Equiv.tsum_eq e Φ,
    hcompsum.tsum_sigma' (fun J => hcompsum.comp_injective sigma_mk_injective)]
  refine Eq.trans (tsum_congr (fun J => hinner J)) ?_
  rw [tsum_mul_left]

variable {K} in
/-- **Cone integral of the lattice theta kernel** (the standard analytic argument).
For `1 < Re s` and nonzero `a`, the multiplicative-Haar integral of
`idealThetaKernel K a * |N|^s` over the fundamental cone equals `w_K * I(s)` times
the partial zeta over the nonzero principal ideals divisible by `a`.
Assembled from the interchange step (`cone_integral_idealThetaKernel_eq_tsum`)
and the fundamental-cone collapse (`tsum_cone_integral_mixedGaussian_eq`). -/
theorem cone_integral_idealThetaKernel_eq (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    ∫ x, (mixedEmbedding.fundamentalCone K).indicator
            (fun x => Theta.idealThetaKernel K a x * (mixedEmbedding.norm x : ℂ) ^ s) x
          ∂(mixedMulHaar K)
      = (Units.torsionOrder K : ℂ) * I K s *
          ∑' I : {I : (Ideal (RingOfIntegers K))⁰ //
                    (a ∣ (I : Ideal (RingOfIntegers K))) ∧
                      Submodule.IsPrincipal (I : Ideal (RingOfIntegers K))},
              (Ideal.absNorm (I : Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by
  rw [cone_integral_idealThetaKernel_eq_tsum s hs ha,
    tsum_cone_integral_mixedGaussian_eq s hs ha]

variable {K} in
/-- **Step 3 intermediate identity** (the standard analytic argument).  For `1 < Re s`
and nonzero `a`, the completed partial zeta is `N(a)^s * Z_inf(s)` times the
partial zeta over nonzero principal ideals divisible by `a`.  The analytic core
is `cone_integral_idealThetaKernel_eq`; the remaining `(1/w_K)` and
`|d_K|^{s/2}*I = Z_inf` bookkeeping (`absdisc_rpow_mul_I_eq_ZInfty`) is algebra.
Consumed by step 5. -/
theorem completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    DedekindZeta.completedPartialZeta K a s
      = (Ideal.absNorm a : ℂ) ^ s * DedekindZeta.ZInfty K s *
          ∑' I : {I : (Ideal (RingOfIntegers K))⁰ //
                    (a ∣ (I : Ideal (RingOfIntegers K))) ∧
                      Submodule.IsPrincipal (I : Ideal (RingOfIntegers K))},
              (Ideal.absNorm (I : Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by
  have hw : (Units.torsionOrder K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Units.torsionOrder_ne_zero K)
  have hpos : (0 : ℝ) < s.re := by linarith
  rw [DedekindZeta.completedPartialZeta, cone_integral_idealThetaKernel_eq s hs ha,
    ← absdisc_rpow_mul_I_eq_ZInfty K hpos]
  field_simp

end

end DedekindZeta.GammaIntegral

/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: mathlib-initiative/sum_product at 80e4127a67742659d521466204c6d2d7e0ca2b3f.
- Formalization note: Lean 4.33.1 compatibility port with narrow imports for DedekindZeta.GammaIntegral.
- PROVENANCE-END
-/
