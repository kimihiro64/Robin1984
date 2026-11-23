/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.GammaIntegral
import DedekindZeta.MellinPrinciple
import DedekindZeta.Statements
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Norm-1 surface × radial `(0,∞)` decomposition of the fundamental cone

This module provides the purely geometric/measure-theoretic factorisation of
`NumberField.mixedEmbedding.fundamentalCone K` used by the Mellin-principle
argument. It lets the per-class cone Mellin integral
`∫_cone Θ(𝔞,x)·N(x)^s d^*x` be rewritten as a one-dimensional radial Mellin.

The construction follows the analytic setup around the Mellin principle and
theta series in Neukirch, *Algebraic Number Theory*, Chapter VII §§1 and 3.

This file introduces three pieces of infrastructure:

1. The **norm-1 surface fundamental domain** `normEqOneSurface K` — the slice
   `mixedEmbedding.fundamentalCone K ∩ {N = 1}` (a compact fundamental domain,
   mod torsion, for the `𝓞ˣ`-action on the norm-1 surface).
2. The **radial parametrisation** `(0,∞) × normEqOneSurface K ≃ cone ∖ {N=0}`
   via `(r, σ) ↦ radialMap K r σ`, scaled so `N (radialMap K r σ) = r`.
3. The **measure decomposition** `mixedMulHaar K = surfaceMeasure K ⊗ dr/r` on
   the cone, i.e. `∫_cone h d*x = ∫_0^∞ (∫_S h(r-scaled σ) dμ_S) dr/r`.

We reuse Mathlib's `mixedEmbedding`/`fundamentalCone`/`normLeOne` machinery and
the project's `DedekindZeta.mixedMulHaar` and `isFundamentalDomain_fundamentalCone`
(`DedekindZeta/Statements.lean`); we do **not** redefine the cone or the unit
logarithmic embedding.

## Scaling convention

`mixedEmbedding.norm` is homogeneous of degree `d = Module.finrank ℚ K` under
real scaling (`mixedEmbedding.norm_smul`: `N (c • x) = |c|^d · N x`). To send a
norm-`1` point `σ` to a point of norm `r > 0` along the ray, we scale by
`r^{1/d}`:

    radialMap K r x := (r ^ (1/d)) • x ,    so   N (radialMap K r x) = r · N x .

This is the scaling convention used by the cone integrals (`r` *is* the norm),
matching `mixedEmbedding.norm` as the radial coordinate.
-/

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors

namespace DedekindZeta.ConeRadialReduction

variable (K : Type*) [Field K] [NumberField K]

/-! ## 1. The radial scaling map and the norm-1 surface fundamental domain -/

/-- **Radial scaling.** `radialMap K r x = r^{1/d} • x` with `d = finrank ℚ K`,
the unique positive scaling sending the `mixedEmbedding.norm` of `x` to `r · N x`
(see `norm_radialMap`). For `r > 0` this is the radial coordinate `r = N(·)`
along the cone ray. -/
noncomputable def radialMap (r : ℝ) (x : mixedSpace K) : mixedSpace K :=
  (r ^ ((finrank ℚ K : ℝ)⁻¹)) • x

/-- **Radial projection** onto the norm-1 surface: `radialProj K x` rescales `x`
to norm `1` (when `N x ≠ 0`), i.e. `radialProj K x = radialMap K (N x)⁻¹ x`. Used
to define the surface measure as the `dr/r`-collar pushforward. -/
noncomputable def radialProj (x : mixedSpace K) : mixedSpace K :=
  radialMap K (mixedEmbedding.norm x)⁻¹ x

/-- **The norm-1 surface fundamental domain** `S K`: the slice of the fundamental
cone of `mixedEmbedding.norm = 1`. It is a compact fundamental domain (mod
torsion) for the `𝓞ˣ`-action on the norm-1 surface, and the base of the radial
parametrisation. the standard treatment. -/
def normEqOneSurface : Set (mixedSpace K) :=
  mixedEmbedding.fundamentalCone K ∩ {x | mixedEmbedding.norm x = 1}

variable {K}

@[simp] theorem mem_normEqOneSurface {x : mixedSpace K} :
    x ∈ normEqOneSurface K ↔
      x ∈ mixedEmbedding.fundamentalCone K ∧ mixedEmbedding.norm x = 1 :=
  Set.mem_sep_iff

theorem measurableSet_normEqOneSurface :
    MeasurableSet (normEqOneSurface K) :=
  (measurableSet_fundamentalCone K).inter <|
    measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

/-- The norm-1 surface fundamental domain is **relatively compact**: its closure
is compact.  the standard treatment states that the norm-1 surface fundamental domain
is compact, but Mathlib realises `mixedEmbedding.fundamentalCone K` via the
*half-open* `ZSpan.fundamentalDomain` (a half-open parallelepiped, see
`fundamentalCone` and the `Set.Ico 0 1` faces of `ZSpan.fundamentalDomain`).
Consequently the literal slice `normEqOneSurface K` is **not closed** (the faces
where a logarithmic coordinate hits `1` are genuine limit points that are
excluded), so it is not compact as a subset; only its closure is.  This mirrors
Mathlib's own choice to prove only `IsBounded` (never `IsCompact`) for the
analogous half-open set `normLeOne K` (`fundamentalCone.isBounded_normLeOne`).
The faithful, true encoding of the standard treatment's compactness here is therefore
compactness of the closure, which is what downstream finiteness/integrability
arguments actually use.  Proof: closed (`isClosed_closure`) and bounded (the
surface is contained in the bounded `normLeOne K`), via Heine–Borel. -/
theorem isCompact_closure_normEqOneSurface : IsCompact (closure (normEqOneSurface K)) := by
  classical
  refine Bornology.IsBounded.isCompact_closure ?_
  exact (fundamentalCone.isBounded_normLeOne K).subset fun x hx => ⟨hx.1, hx.2.le⟩

/-! ## 2. Radial parametrisation `(0,∞) × S K ≃ cone ∖ {N = 0}` -/

/-- **Norm scaling.** `N (radialMap K r x) = r · N x` for `r > 0`: the radial
parameter `r` is exactly the multiplicative factor on `mixedEmbedding.norm`. From
`mixedEmbedding.norm_smul` and `(r^{1/d})^d = r`. -/
theorem norm_radialMap (r : ℝ) (hr : 0 < r) (x : mixedSpace K) :
    mixedEmbedding.norm (radialMap K r x) = r * mixedEmbedding.norm x := by
  have hd : finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  simp only [radialMap, mixedEmbedding.norm_smul,
    abs_of_pos (Real.rpow_pos_of_pos hr ((finrank ℚ K : ℝ)⁻¹)),
    Real.rpow_inv_natCast_pow hr.le hd]

/-- For `σ` on the norm-1 surface and `r > 0`, `N (radialMap K r σ) = r`. -/
theorem norm_radialMap_of_mem (r : ℝ) (hr : 0 < r) {σ : mixedSpace K}
    (hσ : σ ∈ normEqOneSurface K) :
    mixedEmbedding.norm (radialMap K r σ) = r := by
  rw [norm_radialMap r hr σ, (mem_normEqOneSurface.mp hσ).2, mul_one]

/-- The radial scaling preserves the (scale-invariant) fundamental cone:
`radialMap K r x ∈ cone` whenever `x ∈ cone` and `r > 0`
(`fundamentalCone.smul_mem_of_mem`). -/
theorem radialMap_mem_cone (r : ℝ) (hr : 0 < r) {x : mixedSpace K}
    (hx : x ∈ mixedEmbedding.fundamentalCone K) :
    radialMap K r x ∈ mixedEmbedding.fundamentalCone K :=
  fundamentalCone.smul_mem_of_mem hx (Real.rpow_pos_of_pos hr _).ne'

/-- Continuity of the parametrisation `(r, σ) ↦ radialMap K r σ` on `(0,∞) × S`. -/
theorem continuous_radialMap_uncurry :
    Continuous (fun p : ℝ × mixedSpace K => radialMap K p.1 p.2) := by
  simp only [radialMap]
  exact ((Real.continuous_rpow_const (by positivity)).comp continuous_fst).smul continuous_snd


/-! ## 3. The measure decomposition `mixedMulHaar K = μ_S ⊗ dr/r` -/

/-- **The surface measure** `μ_S` on the norm-1 fundamental domain `S K`.

Defined faithfully and non-circularly as the `dr/r`-collar pushforward: since
the radial coordinate `r = N(·)` carries the multiplicative Haar `dr/r` and
`∫_1^{e} dr/r = 1`, pushing `mixedMulHaar K` restricted to the norm-collar
`{x ∈ cone | N x ∈ (1, e]}` forward along the norm-1 projection `radialProj K`
yields exactly the surface measure (the disintegration fibre of `mixedMulHaar K`
along `N`). It is supported on `normEqOneSurface K`. -/
noncomputable def surfaceMeasure (K : Type*) [Field K] [NumberField K] :
    Measure (mixedSpace K) :=
  Measure.map (radialProj K)
    ((DedekindZeta.mixedMulHaar K).restrict
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}))

/-- The surface measure is supported on the norm-1 surface fundamental domain. -/
theorem surfaceMeasure_apply_compl_normEqOneSurface :
    surfaceMeasure K (normEqOneSurface K)ᶜ = 0 := by
  -- `radialProj K` is measurable: `x ↦ ((N x)⁻¹) ^ (d⁻¹) • x`, with the scalar
  -- continuous (`d⁻¹ ≥ 0`, so `Real.continuous_rpow_const`) composed with the
  -- measurable `(N ·)⁻¹`.
  have hq : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹ := by positivity
  have hscalar : Measurable
      (fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹ ^ ((finrank ℚ K : ℝ))⁻¹) :=
    (Real.continuous_rpow_const hq).measurable.comp
      ((mixedEmbedding.continuous_norm K).measurable.inv)
  have hmeas : Measurable (radialProj K) := hscalar.smul measurable_id
  rw [surfaceMeasure,
    Measure.map_apply hmeas measurableSet_normEqOneSurface.compl,
    Measure.restrict_apply (hmeas measurableSet_normEqOneSurface.compl)]
  -- The preimage of the complement meets the norm-collar in the empty set:
  -- every collar point has `N x > 1 > 0`, so `radialProj K x` lands in the
  -- norm-1 surface (`norm_radialMap`, scale-invariance of the cone).
  have hempty : (radialProj K ⁻¹' (normEqOneSurface K)ᶜ) ∩
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hpre, hx, hN⟩
    have hpos : 0 < mixedEmbedding.norm x := lt_trans one_pos hN.1
    have hcone : radialProj K x ∈ mixedEmbedding.fundamentalCone K :=
      radialMap_mem_cone _ (inv_pos.mpr hpos) hx
    have hnorm : mixedEmbedding.norm (radialProj K x) = 1 := by
      rw [radialProj, norm_radialMap _ (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    exact hpre (mem_normEqOneSurface.mpr ⟨hcone, hnorm⟩)
  rw [hempty, measure_empty]


/-- **Composition of radial scalings.** For `a, b ≥ 0`,
`radialMap K a (radialMap K b x) = radialMap K (a*b) x`. From `smul_smul` and
`Real.mul_rpow` (`(a*b)^{1/d} = a^{1/d}·b^{1/d}`). Used to reduce the radial
integral over the collar to an integral over `(0,∞)` via the substitution
`r = N x · t`. -/
theorem radialMap_radialMap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (x : mixedSpace K) :
    radialMap K a (radialMap K b x) = radialMap K (a * b) x := by
  simp only [radialMap, smul_smul, ← Real.mul_rpow ha hb]

/-- **Radial-scaling invariance of the cone Haar measure** `mixedMulHaar K`.
For `t > 0` and nonnegative measurable `h`,
`∫⁻ h(radialMap K t x) dμ = ∫⁻ h(x) dμ`. The radial scaling
`radialMap K t x = s • x` (`s = t^{1/d} > 0`) is right multiplication by the
scalar element `c = s • 1`, which has `N(c) = |s|^d ≠ 0`; the multiplicative
Haar `mixedMulHaar K` is invariant under such right translations
(`DedekindZeta.lintegral_comp_mul_right_mixedMulHaar`). the standard treatment. -/
theorem lintegral_radialMap_mixedMulHaar (h : mixedSpace K → ℝ≥0∞)
    (hh : Measurable h) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, h (radialMap K t x) ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ x, h x ∂(DedekindZeta.mixedMulHaar K) := by
  set s : ℝ := t ^ ((finrank ℚ K : ℝ)⁻¹) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos ht _
  set c : mixedSpace K := s • (1 : mixedSpace K) with hc
  have hcN : mixedEmbedding.norm c ≠ 0 := by
    rw [hc, mixedEmbedding.norm_smul, map_one, mul_one]
    exact pow_ne_zero _ (abs_ne_zero.mpr hspos.ne')
  have hrw : (fun x : mixedSpace K => h (radialMap K t x))
      = fun x => h (x * c) := by
    funext x
    congr 1
    rw [radialMap, hc, mul_smul_comm, mul_one]
  rw [show (∫⁻ x, h (radialMap K t x) ∂(DedekindZeta.mixedMulHaar K))
        = ∫⁻ x, h (x * c) ∂(DedekindZeta.mixedMulHaar K) from by rw [hrw]]
  exact DedekindZeta.lintegral_comp_mul_right_mixedMulHaar K h hh hcN

/-- **Inner 1D radial weight integral** (step-5 helper for the collar
disintegration). For a fixed norm value `n`, the `t`-fiber of the collar
`{N ∈ (1, e]}` carries the multiplicative-Haar mass
`∫_{t : t < n ≤ e·t} dr/r = ∫_1^e dr/r = 1` when `n > 0`, and `0` when `n ≤ 0`
(then no `t > 0` can satisfy `t < n`). Concretely the membership
`n ∈ Ioc t (e·t)` is `t < n ∧ n ≤ e·t`, i.e. `t ∈ Ico (n/e) n`, and
`∫_{n/e}^{n} dt/t = log n - log (n/e) = log e = 1`. the standard treatment (radial
weight `dr/r`). Consumed by the collar disintegration assembly. -/
theorem lintegral_collar_weight (n : ℝ) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal t⁻¹ * (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞) n
          ∂volume
      = if 0 < n then 1 else 0 := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  split_ifs with hn
  · -- `n > 0`: rewrite the integrand to the indicator of `Ico (n/e) n`
    set a : ℝ := n / Real.exp 1 with ha
    have hapos : 0 < a := div_pos hn he
    have hbe : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
    have han : a < n := by
      rw [ha, div_lt_iff₀ he]
      nlinarith [hn]
    -- pointwise rewrite of the integrand on `Ioi 0`
    have hcongr : Set.EqOn
        (fun t => ENNReal.ofReal t⁻¹ *
            (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞) n)
        ((Set.Ico a n).indicator (fun t => ENNReal.ofReal t⁻¹))
        (Set.Ioi (0 : ℝ)) := by
      intro t _
      dsimp only
      by_cases hmem : n ∈ Set.Ioc t (Real.exp 1 * t)
      · rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one,
            Set.indicator_of_mem (Set.mem_Ico.mpr ⟨?_, hmem.1⟩)]
        rw [ha, div_le_iff₀ he, mul_comm]
        exact hmem.2
      · rw [Set.indicator_of_notMem hmem, mul_zero,
            Set.indicator_of_notMem ?_]
        intro hmem2
        rw [Set.mem_Ico] at hmem2
        exact hmem (Set.mem_Ioc.mpr ⟨hmem2.2, by
          rw [mul_comm]; rw [ha, div_le_iff₀ he] at hmem2; exact hmem2.1⟩)
    have hsub : Set.Ico a n ⊆ Set.Ioi (0 : ℝ) :=
      fun t ht => lt_of_lt_of_le hapos ht.1
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
        setLIntegral_indicator measurableSet_Ico,
        Set.inter_eq_left.mpr hsub]
    -- convert `Ico` to `Ioc` (single points are null), then to an interval integral
    rw [setLIntegral_congr (MeasureTheory.Ico_ae_eq_Icc.trans
        MeasureTheory.Ioc_ae_eq_Icc.symm)]
    have hne : ∀ x : ℝ, x ∈ Set.uIcc a n → id x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le han.le, Set.mem_Icc] at hx
      exact (lt_of_lt_of_le hapos hx.1).ne'
    have hii : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a n :=
      intervalIntegral.intervalIntegrable_inv (f := id) hne continuousOn_id
    have hintegrable : Integrable (fun t : ℝ => t⁻¹)
        (volume.restrict (Set.Ioc a n)) := hii.1
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc a n)] (fun t : ℝ => t⁻¹) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact inv_nonneg.mpr (lt_trans hapos ht.1).le
    have hint : ∫ t in Set.Ioc a n, t⁻¹ ∂volume = 1 := by
      have h0 : (0 : ℝ) ∉ Set.uIcc a n := by
        rw [Set.uIcc_of_le han.le, Set.mem_Icc]
        rintro ⟨hle, _⟩; linarith
      rw [← intervalIntegral.integral_of_le han.le, integral_inv h0]
      have hdiv : n / a = Real.exp 1 := by
        rw [ha, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hn.ne', mul_one]
      rw [hdiv, Real.log_exp]
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnonneg, hint,
        ENNReal.ofReal_one]
  · -- `n ≤ 0`: the indicator is identically `0` on `Ioi 0`
    refine setLIntegral_eq_zero measurableSet_Ioi ?_
    intro t ht
    have htpos : 0 < t := ht
    have hn' : n ≤ 0 := not_lt.mp hn
    have hnotmem : n ∉ Set.Ioc t (Real.exp 1 * t) := by
      rw [Set.mem_Ioc]; rintro ⟨h1, _⟩; linarith
    simp [Set.indicator_of_notMem hnotmem]

/-- **Step-1 restricted radial change of variable** (the standard treatment).
For `t > 0` and nonnegative measurable `h`, scaling the integration variable by
`radialMap K t` turns the collar `C = cone ∩ {N ∈ (1, e]}` into the scaled collar
`C_t = cone ∩ {N ∈ (t, e·t]}`:
  `∫⁻ x in C, h (radialMap K t x) dμ = ∫⁻ y in C_t, h y dμ`.
Proof: apply the radial-scaling invariance `lintegral_radialMap_mixedMulHaar` to
the nonnegative measurable `g = C_t.indicator h`, using that
`radialMap K t x ∈ C_t ↔ x ∈ C` (norm scales by `t` via `norm_radialMap`; the
cone is scale-invariant in both directions via `radialMap_mem_cone` and the
inverse scaling `radialMap K t⁻¹`). Consumed by the collar disintegration
assembly. -/
theorem lintegral_radialMap_collar (h : mixedSpace K → ℝ≥0∞) (hh : Measurable h)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        h (radialMap K t x) ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ y in (mixedEmbedding.fundamentalCone K ∩
            {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)}),
          h y ∂(DedekindZeta.mixedMulHaar K) := by
  set C : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hC
  set Ct : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)} with hCt
  have hC_meas : MeasurableSet C :=
    (measurableSet_fundamentalCone K).inter
      ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  have hCt_meas : MeasurableSet Ct :=
    (measurableSet_fundamentalCone K).inter
      ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  -- `radialMap K t x ∈ C_t ↔ x ∈ C`.
  have hiff : ∀ x, radialMap K t x ∈ Ct ↔ x ∈ C := by
    intro x
    rw [hCt, hC]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, norm_radialMap t ht x, Set.mem_Ioc]
    constructor
    · rintro ⟨hcone, hlo, hhi⟩
      refine ⟨?_, ?_, ?_⟩
      · have h1 := radialMap_mem_cone t⁻¹ (inv_pos.mpr ht) hcone
        rw [radialMap_radialMap _ _ (inv_pos.mpr ht).le ht.le,
          inv_mul_cancel₀ ht.ne'] at h1
        simpa [radialMap, Real.one_rpow] using h1
      · exact lt_of_mul_lt_mul_left (by rwa [mul_one]) ht.le
      · exact le_of_mul_le_mul_left (by rwa [mul_comm (Real.exp 1) t] at hhi) ht
    · rintro ⟨hcone, hlo, hhi⟩
      refine ⟨radialMap_mem_cone t ht hcone, ?_, ?_⟩
      · have := mul_lt_mul_of_pos_left hlo ht
        rwa [mul_one] at this
      · have := mul_le_mul_of_nonneg_left hhi ht.le
        rwa [mul_comm t (Real.exp 1)] at this
  rw [← lintegral_indicator hC_meas, ← lintegral_indicator hCt_meas]
  have hpt : (fun x => C.indicator (fun x => h (radialMap K t x)) x)
      = fun x => Ct.indicator h (radialMap K t x) := by
    classical
    funext x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hx : x ∈ C
    · rw [if_pos hx, if_pos ((hiff x).mpr hx)]
    · rw [if_neg hx, if_neg (fun hc => hx ((hiff x).mp hc))]
  rw [hpt]
  exact lintegral_radialMap_mixedMulHaar (Ct.indicator h) (hh.indicator hCt_meas) ht

/-- **Multiplicative-Haar radial disintegration of the cone Haar measure**
(collar form). The cone integral against `mixedMulHaar K` equals the integral,
over the norm-collar `C = {x ∈ cone | N x ∈ (1, e]}`, of the radial collapse
`∫_0^∞ h(radialMap K t x) · ofReal t⁻¹ dt`.

This is the genuine mathematical core: `mixedMulHaar K` is multiplicative Haar on
the cone (off `N = 0`), invariant under the radial scaling `x ↦ radialMap K t x`
(`mixedMulHaar` is a multiplicative Haar measure, cf.
`DedekindZeta.lintegral_comp_mul_right_mixedMulHaar`), and the collar `C` is a
fundamental domain for that `(0,∞)`-scaling action on the cone with the
multiplicative weight `dr/r` (`∫_1^e dr/r = 1`). The norm-vanishing locus is
`mixedMulHaar`-null (`DedekindZeta.ae_norm_ne_zero` style), so it does not
contribute. the standard treatment; the polar/`expMapBasis` Jacobian underlying
Mathlib's `NormLeOne.volume_normLeOne`. -/
theorem setLIntegral_cone_eq_collar_radial (h : mixedSpace K → ℝ≥0∞)
    (hh : Measurable h) :
    ∫⁻ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
            {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          (∫⁻ t in Set.Ioi (0 : ℝ),
              h (radialMap K t x) * ENNReal.ofReal t⁻¹ ∂volume)
            ∂(DedekindZeta.mixedMulHaar K) := by
  classical
  -- `mixedMulHaar K = volume.withDensity (ofReal _)` has a finite density, hence is
  -- `SigmaFinite`; this powers the two Tonelli swaps below.
  haveI hsf : SigmaFinite (DedekindZeta.mixedMulHaar K) := by
    unfold DedekindZeta.mixedMulHaar
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  have hN_meas : Measurable (mixedEmbedding.norm : mixedSpace K → ℝ) :=
    (mixedEmbedding.continuous_norm K).measurable
  have hcone_meas : MeasurableSet (mixedEmbedding.fundamentalCone K) :=
    measurableSet_fundamentalCone K
  -- Measurability of the collar indicator as a function of the radius `t` (fixed `n`).
  have hg1_meas : ∀ n : ℝ, Measurable
      (fun t : ℝ => (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞) n) := by
    intro n
    have heq : (fun t : ℝ => (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞) n)
        = Set.indicator {t : ℝ | n ∈ Set.Ioc t (Real.exp 1 * t)} (fun _ => (1 : ℝ≥0∞)) := by
      funext t
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    rw [heq]
    refine measurable_const.indicator ?_
    have hset : {t : ℝ | n ∈ Set.Ioc t (Real.exp 1 * t)}
        = {t : ℝ | t < n} ∩ {t : ℝ | n ≤ Real.exp 1 * t} := by
      ext t; simp [Set.mem_Ioc, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hset]
    exact (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const (measurable_const.mul measurable_id))
  -- Joint measurability of the collar indicator in `(t, y)`.
  have hg2_meas : Measurable (fun p : ℝ × mixedSpace K =>
      (Set.Ioc p.1 (Real.exp 1 * p.1)).indicator (1 : ℝ → ℝ≥0∞)
        (mixedEmbedding.norm p.2)) := by
    have heq : (fun p : ℝ × mixedSpace K =>
        (Set.Ioc p.1 (Real.exp 1 * p.1)).indicator (1 : ℝ → ℝ≥0∞)
          (mixedEmbedding.norm p.2))
        = Set.indicator {p : ℝ × mixedSpace K |
            mixedEmbedding.norm p.2 ∈ Set.Ioc p.1 (Real.exp 1 * p.1)}
          (fun _ => (1 : ℝ≥0∞)) := by
      funext p
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    rw [heq]
    refine measurable_const.indicator ?_
    have hset : {p : ℝ × mixedSpace K |
          mixedEmbedding.norm p.2 ∈ Set.Ioc p.1 (Real.exp 1 * p.1)}
        = {p : ℝ × mixedSpace K | p.1 < mixedEmbedding.norm p.2} ∩
          {p : ℝ × mixedSpace K | mixedEmbedding.norm p.2 ≤ Real.exp 1 * p.1} := by
      ext p; simp [Set.mem_Ioc, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hset]
    exact (measurableSet_lt measurable_fst (hN_meas.comp measurable_snd)).inter
      (measurableSet_le (hN_meas.comp measurable_snd)
        (measurable_const.mul measurable_fst))
  -- Joint measurability of `(x, t) ↦ h (radialMap K t x)`.
  have hrad_xt : Measurable (fun p : mixedSpace K × ℝ => radialMap K p.2 p.1) :=
    (continuous_radialMap_uncurry.comp continuous_swap).measurable
  -- `uncurry` measurabilities for the two Tonelli swaps.
  have huncurry1 : Measurable
      (fun p : mixedSpace K × ℝ => h (radialMap K p.2 p.1) * ENNReal.ofReal p.2⁻¹) :=
    (hh.comp hrad_xt).mul (measurable_snd.inv.ennreal_ofReal)
  have huncurry2 : Measurable
      (fun p : ℝ × mixedSpace K => h p.2 *
        ((Set.Ioc p.1 (Real.exp 1 * p.1)).indicator (1 : ℝ → ℝ≥0∞)
            (mixedEmbedding.norm p.2) * ENNReal.ofReal p.1⁻¹)) :=
    (hh.comp measurable_snd).mul (hg2_meas.mul (measurable_fst.inv.ennreal_ofReal))
  refine Eq.symm ?_
  calc
    ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        (∫⁻ t in Set.Ioi (0 : ℝ),
            h (radialMap K t x) * ENNReal.ofReal t⁻¹ ∂volume)
          ∂(DedekindZeta.mixedMulHaar K)
        = ∫⁻ t in Set.Ioi (0 : ℝ),
            ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
                {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
              h (radialMap K t x) * ENNReal.ofReal t⁻¹
              ∂(DedekindZeta.mixedMulHaar K) ∂volume :=
        lintegral_lintegral_swap huncurry1.aemeasurable
    -- step 1: restricted radial change of variable, then pull the radial weight out
    _ = ∫⁻ t in Set.Ioi (0 : ℝ),
          (∫⁻ y in (mixedEmbedding.fundamentalCone K ∩
              {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)}),
            h y ∂(DedekindZeta.mixedMulHaar K)) * ENNReal.ofReal t⁻¹ ∂volume := by
        refine lintegral_congr_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have htpos : 0 < t := ht
        have hrad_t : Measurable (fun x : mixedSpace K => radialMap K t x) :=
          (continuous_radialMap_uncurry.comp
            (continuous_const.prodMk continuous_id)).measurable
        have hcomp : Measurable (fun x : mixedSpace K => h (radialMap K t x)) :=
          hh.comp hrad_t
        rw [lintegral_mul_const (ENNReal.ofReal t⁻¹) hcomp,
          lintegral_radialMap_collar h hh htpos]
    -- rewrite the scaled collar as a cone integral against the collar indicator
    _ = ∫⁻ t in Set.Ioi (0 : ℝ),
          ∫⁻ y in mixedEmbedding.fundamentalCone K,
            h y * ((Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
              (mixedEmbedding.norm y) * ENNReal.ofReal t⁻¹)
            ∂(DedekindZeta.mixedMulHaar K) ∂volume := by
        refine lintegral_congr (fun t => ?_)
        have hS_meas : MeasurableSet
            {y : mixedSpace K | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)} :=
          hN_meas measurableSet_Ioc
        have hindmeas : Measurable (fun y : mixedSpace K =>
            (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
              (mixedEmbedding.norm y)) :=
          (measurable_const.indicator measurableSet_Ioc).comp hN_meas
        have hpt : ∀ y : mixedSpace K,
            h y * (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
                (mixedEmbedding.norm y)
              = {y : mixedSpace K |
                  mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)}.indicator h y := by
          intro y
          by_cases hyn : mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)
          · rw [Set.indicator_of_mem hyn, Set.indicator_of_mem (show y ∈ _ from hyn),
              Pi.one_apply, mul_one]
          · rw [Set.indicator_of_notMem hyn, Set.indicator_of_notMem (show y ∉ _ from hyn),
              mul_zero]
        have hcs : ∫⁻ y in (mixedEmbedding.fundamentalCone K ∩
              {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)}),
            h y ∂(DedekindZeta.mixedMulHaar K)
            = ∫⁻ y in mixedEmbedding.fundamentalCone K,
              h y * (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
                (mixedEmbedding.norm y) ∂(DedekindZeta.mixedMulHaar K) := by
          rw [lintegral_congr hpt, ← lintegral_indicator hcone_meas,
            Set.indicator_indicator, lintegral_indicator (hcone_meas.inter hS_meas)]
        rw [hcs]
        refine (lintegral_mul_const _ (hh.mul hindmeas)).symm.trans ?_
        exact lintegral_congr (fun _ => by simp only [Pi.mul_apply, mul_assoc])
    -- step: Tonelli swap `t` and `y`
    _ = ∫⁻ y in mixedEmbedding.fundamentalCone K,
          ∫⁻ t in Set.Ioi (0 : ℝ),
            h y * ((Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
              (mixedEmbedding.norm y) * ENNReal.ofReal t⁻¹) ∂volume
            ∂(DedekindZeta.mixedMulHaar K) :=
        lintegral_lintegral_swap huncurry2.aemeasurable
    -- step 5: the inner 1D radial weight integral equals `1` on `N y > 0`
    _ = ∫⁻ y in mixedEmbedding.fundamentalCone K,
          h y * (if 0 < mixedEmbedding.norm y then (1 : ℝ≥0∞) else 0)
          ∂(DedekindZeta.mixedMulHaar K) := by
        refine lintegral_congr (fun y => ?_)
        refine (lintegral_const_mul (h y)
          ((hg1_meas (mixedEmbedding.norm y)).mul (measurable_inv.ennreal_ofReal))).trans ?_
        congr 1
        simp only [Pi.mul_apply]
        rw [show (fun t => (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
                (mixedEmbedding.norm y) * ENNReal.ofReal t⁻¹)
              = (fun t => ENNReal.ofReal t⁻¹ *
                  (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
                    (mixedEmbedding.norm y)) from by funext t; rw [mul_comm]]
        exact lintegral_collar_weight (mixedEmbedding.norm y)
    -- step 6: discard the `μ`-null locus `{N = 0}`
    _ = ∫⁻ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (DedekindZeta.ae_norm_ne_zero (K := K))] with y hy
        have hpos : 0 < mixedEmbedding.norm y :=
          lt_of_le_of_ne (mixedEmbedding.norm_nonneg y) (Ne.symm hy)
        rw [if_pos hpos, mul_one]

/-- **Multiplicative substitution on the half-line.** For `n > 0` and measurable
`F`, `∫⁻ s in (0,∞), F (n·s) dvol = n⁻¹ · ∫⁻ r in (0,∞), F r dvol`. This is the
`r = n·t` change of variables (`Real.map_volume_mul_left`) restricted to the
positive half-line; the assembly of `setLIntegral_cone_eq_radial` uses it to
collapse the inner `r`-integral after Tonelli. -/
private theorem lintegral_Ioi_const_mul {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    {n : ℝ} (hn : 0 < n) :
    ∫⁻ s in Set.Ioi (0:ℝ), F (n * s) ∂volume
      = ENNReal.ofReal n⁻¹ * ∫⁻ r in Set.Ioi (0:ℝ), F r ∂volume := by
  have hind : Measurable ((Set.Ioi (0:ℝ)).indicator F) := hF.indicator measurableSet_Ioi
  have hkey : (fun s : ℝ => (Set.Ioi (0:ℝ)).indicator F (n * s))
      = (Set.Ioi (0:ℝ)).indicator (fun s => F (n * s)) := by
    funext s
    by_cases hs : s ∈ Set.Ioi (0:ℝ)
    · have hns : n * s ∈ Set.Ioi (0:ℝ) := by
        simp only [Set.mem_Ioi] at hs ⊢; positivity
      rw [Set.indicator_of_mem hns, Set.indicator_of_mem hs]
    · have hns : n * s ∉ Set.Ioi (0:ℝ) := by
        simp only [Set.mem_Ioi, not_lt] at hs ⊢
        exact mul_nonpos_iff.mpr (Or.inl ⟨hn.le, hs⟩)
      rw [Set.indicator_of_notMem hns, Set.indicator_of_notMem hs]
  calc
    ∫⁻ s in Set.Ioi (0:ℝ), F (n * s) ∂volume
        = ∫⁻ s, (Set.Ioi (0:ℝ)).indicator (fun s => F (n * s)) s ∂volume := by
          rw [lintegral_indicator measurableSet_Ioi]
      _ = ∫⁻ s, (Set.Ioi (0:ℝ)).indicator F (n * s) ∂volume := by rw [hkey]
      _ = ∫⁻ r, (Set.Ioi (0:ℝ)).indicator F r ∂(Measure.map (fun s : ℝ => n * s) volume) := by
          rw [lintegral_map hind (by fun_prop)]
      _ = ∫⁻ r, (Set.Ioi (0:ℝ)).indicator F r ∂(ENNReal.ofReal |n⁻¹| • volume) := by
          rw [Real.map_volume_mul_left hn.ne']
      _ = ENNReal.ofReal |n⁻¹| * ∫⁻ r, (Set.Ioi (0:ℝ)).indicator F r ∂volume := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ = ENNReal.ofReal n⁻¹ * ∫⁻ r in Set.Ioi (0:ℝ), F r ∂volume := by
          rw [lintegral_indicator measurableSet_Ioi, abs_of_pos (inv_pos.mpr hn)]

/-- **Lebesgue (`ℝ≥0∞`) form of the measure decomposition**, for nonnegative
measurable integrands — the unconditional `lintegral` statement that powers the
Bochner version and the `IsMellinPair` decay estimates.

Proof: assemble the collar-form core (`setLIntegral_cone_eq_collar_radial`) with
the `surfaceMeasure` pushforward.  Unfolding `surfaceMeasure K = map (radialProj K)
(μ.restrict C)` and using `radialMap K r (radialProj K x) = radialMap K (r / N x) x`
(`radialMap_radialMap`) rewrites the inner surface integral as a collar integral;
Tonelli (`lintegral_lintegral_swap`) swaps the `r`- and `x`-integrals, and the
`r = N x · t` substitution (`lintegral_Ioi_const_mul`) collapses each fibre to the
collar core's `dt/t` integral.  the standard treatment. -/
theorem setLIntegral_cone_eq_radial (h : mixedSpace K → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ r in Set.Ioi (0 : ℝ),
          (∫⁻ σ in normEqOneSurface K, h (radialMap K r σ) ∂(surfaceMeasure K))
            * ENNReal.ofReal (r⁻¹) ∂volume := by
  classical
  haveI : SFinite (DedekindZeta.mixedMulHaar K) := by
    unfold DedekindZeta.mixedMulHaar; infer_instance
  have hq : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹ := by positivity
  have hradialProj : Measurable (radialProj K) := by
    have hscalar : Measurable
        (fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹ ^ ((finrank ℚ K : ℝ))⁻¹) :=
      (Real.continuous_rpow_const hq).measurable.comp
        ((mixedEmbedding.continuous_norm K).measurable.inv)
    exact hscalar.smul measurable_id
  -- (1) Push the surface measure back to the collar, rewriting the inner integral.
  have hinner : ∀ r : ℝ, 0 ≤ r →
      (∫⁻ σ in normEqOneSurface K, h (radialMap K r σ) ∂(surfaceMeasure K))
        = ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
            {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
            h (radialMap K (r / mixedEmbedding.norm x) x) ∂(DedekindZeta.mixedMulHaar K) := by
    intro r hr
    have hgσ : Measurable (fun σ : mixedSpace K => h (radialMap K r σ)) := by
      have hcont : Continuous (fun σ : mixedSpace K => radialMap K r σ) := by
        simp only [radialMap]
        fun_prop
      exact hh.comp hcont.measurable
    rw [show (surfaceMeasure K).restrict (normEqOneSurface K) = surfaceMeasure K from
          Measure.restrict_eq_self_of_ae_mem
            (ae_iff.mpr surfaceMeasure_apply_compl_normEqOneSurface)]
    unfold surfaceMeasure
    rw [lintegral_map hgσ hradialProj]
    refine lintegral_congr (fun x => ?_)
    congr 1
    rw [radialProj,
      radialMap_radialMap r (mixedEmbedding.norm x)⁻¹ hr
        (inv_nonneg.mpr (mixedEmbedding.norm_nonneg x)) x,
      div_eq_mul_inv]
  -- (2) Measurability of the integrand in `x` for fixed `r`, and jointly in `(r, x)`.
  have hFmeas : ∀ r : ℝ,
      Measurable (fun x : mixedSpace K => h (radialMap K (r / mixedEmbedding.norm x) x)) := by
    intro r
    have hsc : Measurable (fun x : mixedSpace K =>
        (r / mixedEmbedding.norm x) ^ ((finrank ℚ K : ℝ))⁻¹) :=
      (Real.continuous_rpow_const hq).measurable.comp
        (measurable_const.div (mixedEmbedding.continuous_norm K).measurable)
    have hrm : Measurable (fun x : mixedSpace K => radialMap K (r / mixedEmbedding.norm x) x) := by
      simp only [radialMap]; exact hsc.smul measurable_id
    exact hh.comp hrm
  have hf_meas : Measurable (fun p : ℝ × mixedSpace K =>
      h (radialMap K (p.1 / mixedEmbedding.norm p.2) p.2) * ENNReal.ofReal p.1⁻¹) := by
    refine Measurable.mul ?_ ?_
    · have hpair : Measurable (fun p : ℝ × mixedSpace K =>
          (p.1 / mixedEmbedding.norm p.2, p.2)) :=
        (measurable_fst.div
          ((mixedEmbedding.continuous_norm K).measurable.comp measurable_snd)).prodMk
            measurable_snd
      exact hh.comp ((continuous_radialMap_uncurry).measurable.comp hpair)
    · exact (measurable_fst.inv).ennreal_ofReal
  -- (3) The per-`x` radial substitution `r = N x · t`, collapsing the `r`-integral.
  have hsub : ∀ x : mixedSpace K, 0 < mixedEmbedding.norm x →
      (∫⁻ r in Set.Ioi (0:ℝ),
          h (radialMap K (r / mixedEmbedding.norm x) x) * ENNReal.ofReal r⁻¹ ∂volume)
        = ∫⁻ t in Set.Ioi (0:ℝ),
            h (radialMap K t x) * ENNReal.ofReal t⁻¹ ∂volume := by
    intro x hn
    set n : ℝ := mixedEmbedding.norm x with hndef
    have hf0 : Measurable (fun r : ℝ =>
        h (radialMap K (r / n) x) * ENNReal.ofReal r⁻¹) := by
      refine Measurable.mul ?_ ?_
      · have hsc : Measurable (fun r : ℝ => (r / n) ^ ((finrank ℚ K : ℝ))⁻¹) :=
          (Real.continuous_rpow_const hq).measurable.comp (measurable_id.div_const n)
        have hrm : Measurable (fun r : ℝ => radialMap K (r / n) x) := by
          simp only [radialMap]; exact hsc.smul measurable_const
        exact hh.comp hrm
      · exact (measurable_id.inv).ennreal_ofReal
    have hmeas2 : Measurable (fun s : ℝ =>
        h (radialMap K s x) * ENNReal.ofReal s⁻¹) := by
      refine Measurable.mul ?_ ?_
      · have hsc : Measurable (fun s : ℝ => s ^ ((finrank ℚ K : ℝ))⁻¹) :=
          (Real.continuous_rpow_const hq).measurable
        have hrm : Measurable (fun s : ℝ => radialMap K s x) := by
          simp only [radialMap]; exact hsc.smul measurable_const
        exact hh.comp hrm
      · exact (measurable_id.inv).ennreal_ofReal
    have hIA : (∫⁻ s in Set.Ioi (0:ℝ),
        h (radialMap K ((n * s) / n) x) * ENNReal.ofReal (n * s)⁻¹ ∂volume)
        = ENNReal.ofReal n⁻¹ * ∫⁻ r in Set.Ioi (0:ℝ),
            h (radialMap K (r / n) x) * ENNReal.ofReal r⁻¹ ∂volume :=
      lintegral_Ioi_const_mul hf0 hn
    have hIB : (∫⁻ s in Set.Ioi (0:ℝ),
        h (radialMap K ((n * s) / n) x) * ENNReal.ofReal (n * s)⁻¹ ∂volume)
        = ENNReal.ofReal n⁻¹ * ∫⁻ t in Set.Ioi (0:ℝ),
            h (radialMap K t x) * ENNReal.ofReal t⁻¹ ∂volume := by
      have hcongr : (∫⁻ s in Set.Ioi (0:ℝ),
            h (radialMap K ((n * s) / n) x) * ENNReal.ofReal (n * s)⁻¹ ∂volume)
            = ∫⁻ s in Set.Ioi (0:ℝ),
                ENNReal.ofReal n⁻¹ * (h (radialMap K s x) * ENNReal.ofReal s⁻¹) ∂volume :=
        setLIntegral_congr_fun measurableSet_Ioi (fun s hs => by
          have hs0 : (0:ℝ) < s := hs
          rw [mul_div_cancel_left₀ s hn.ne', mul_inv_rev,
            ENNReal.ofReal_mul (inv_nonneg.mpr hs0.le)]
          ring)
      rw [hcongr, lintegral_const_mul _ hmeas2]
    have hne0 : ENNReal.ofReal n⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hn)).ne'
    exact (ENNReal.mul_right_inj hne0 ENNReal.ofReal_ne_top).mp (hIA.symm.trans hIB)
  -- (4) Assemble: collar-form core, then the three rewrites above.
  rw [setLIntegral_cone_eq_collar_radial h hh]
  refine Eq.symm ?_
  calc
    ∫⁻ r in Set.Ioi (0:ℝ),
        (∫⁻ σ in normEqOneSurface K, h (radialMap K r σ) ∂(surfaceMeasure K))
          * ENNReal.ofReal r⁻¹ ∂volume
      = ∫⁻ r in Set.Ioi (0:ℝ),
          (∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
              {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
              h (radialMap K (r / mixedEmbedding.norm x) x)
                ∂(DedekindZeta.mixedMulHaar K)) * ENNReal.ofReal r⁻¹ ∂volume := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
        rw [hinner r (Set.mem_Ioi.mp hr).le]
    _ = ∫⁻ r in Set.Ioi (0:ℝ),
          ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
              {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
              h (radialMap K (r / mixedEmbedding.norm x) x) * ENNReal.ofReal r⁻¹
                ∂(DedekindZeta.mixedMulHaar K) ∂volume := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
        rw [← lintegral_mul_const (ENNReal.ofReal r⁻¹) (hFmeas r)]
    _ = ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
            {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          ∫⁻ r in Set.Ioi (0:ℝ),
              h (radialMap K (r / mixedEmbedding.norm x) x) * ENNReal.ofReal r⁻¹
                ∂volume ∂(DedekindZeta.mixedMulHaar K) :=
        lintegral_lintegral_swap hf_meas.aemeasurable
    _ = ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
            {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          ∫⁻ t in Set.Ioi (0:ℝ), h (radialMap K t x) * ENNReal.ofReal t⁻¹
                ∂volume ∂(DedekindZeta.mixedMulHaar K) := by
        refine setLIntegral_congr_fun ?_ (fun x hx => ?_)
        · exact (measurableSet_fundamentalCone K).inter
            ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
        · exact hsub x (lt_trans one_pos (Set.mem_Ioc.mp hx.2).1)

/-- **Measure-level form of the cone decomposition.** The cone-restricted Haar
measure `mixedMulHaar K` is the pushforward, along the radial parametrisation
`(r, σ) ↦ radialMap K r σ`, of the multiplicative-Haar weighted product measure
`(volume.restrict (0,∞)) ⊗ μ_S` with density `dr/r` (`ofReal r⁻¹`):

    (mixedMulHaar K).restrict cone
      = map (uncurry radialMap) (((vol|_{(0,∞)}) ⊗ μ_S).withDensity (ofReal ·.1⁻¹)) .

This is the measure-equality repackaging of the Lebesgue identity
`setLIntegral_cone_eq_radial`: two measures whose `lintegral` against every
measurable `ℝ≥0∞`-valued function agree are equal, and the iterated
`lintegral` on the right of `setLIntegral_cone_eq_radial` is, by Tonelli, the
`lintegral` of `h ∘ radialMap` against this pushforward. It is the bridge that
lets the Bochner (`ℂ`-valued) form `setIntegral_cone_eq_radial` be obtained by
`integral_map` + Fubini. Faithful to the standard treatment. -/
theorem mixedMulHaar_restrict_cone_eq_map :
    (DedekindZeta.mixedMulHaar K).restrict (mixedEmbedding.fundamentalCone K)
      = Measure.map (fun p : ℝ × mixedSpace K => radialMap K p.1 p.2)
          (((volume.restrict (Set.Ioi (0 : ℝ))).prod (surfaceMeasure K)).withDensity
            (fun p => ENNReal.ofReal p.1⁻¹)) := by
  -- Two measures agree iff their `lintegral` against every measurable
  -- `ℝ≥0∞`-valued function agrees (`Measure.ext_of_lintegral`).
  refine Measure.ext_of_lintegral _ (fun h hh => ?_)
  haveI : SFinite (DedekindZeta.mixedMulHaar K) := by
    unfold DedekindZeta.mixedMulHaar; infer_instance
  haveI : SFinite (surfaceMeasure K) := by
    unfold surfaceMeasure; infer_instance
  have hF : Measurable (fun p : ℝ × mixedSpace K => radialMap K p.1 p.2) :=
    continuous_radialMap_uncurry.measurable
  have hdens : Measurable (fun p : ℝ × mixedSpace K => ENNReal.ofReal p.1⁻¹) :=
    ENNReal.measurable_ofReal.comp measurable_fst.inv
  -- The surface measure is supported on `normEqOneSurface K`, so a.e. point lies
  -- in it (`surfaceMeasure_apply_compl_normEqOneSurface`).
  have hae : ∀ᵐ σ ∂(surfaceMeasure K), σ ∈ normEqOneSurface K := by
    rw [ae_iff]
    simpa only [Set.mem_compl_iff, Set.compl_def] using
      surfaceMeasure_apply_compl_normEqOneSurface
  -- LHS: rewrite the cone restriction as the proved Lebesgue radial form.
  -- RHS: `lintegral_map` reduces the pushforward, `withDensity` peels off the
  -- `ofReal r⁻¹` weight, and Tonelli (`lintegral_prod`) gives the iterated form.
  have hmprod : Measurable (fun a : ℝ × mixedSpace K => h (radialMap K a.1 a.2)) :=
    hh.comp hF
  rw [setLIntegral_cone_eq_radial h hh, lintegral_map hh hF,
    lintegral_withDensity_eq_lintegral_mul _ hdens hmprod]
  rw [lintegral_prod _ ((hdens.mul hmprod).aemeasurable)]
  refine lintegral_congr (fun r => ?_)
  -- The inner `σ`-integral: pull out the constant `ofReal r⁻¹` and extend the
  -- surface integral from `normEqOneSurface K` to all of `mixedSpace K`.
  have hmσ : Measurable (fun σ : mixedSpace K => h (radialMap K r σ)) :=
    hh.comp ((continuous_radialMap_uncurry.comp
      (continuous_const.prodMk continuous_id)).measurable)
  simp only [Pi.mul_apply]
  rw [lintegral_const_mul _ hmσ, Measure.restrict_eq_self_of_ae_mem hae, mul_comm]

/-- **Measure decomposition of the cone Haar measure** (Bochner, `ℂ`-valued).

For `h` integrable over the cone against `mixedMulHaar K`, the cone integral
factors through the norm-1 surface × radial `(0,∞)` decomposition with the
multiplicative-Haar weight `dr/r`:

    ∫_cone h x d^*x
      = ∫_0^∞ (∫_{S K} h (radialMap K r σ) dμ_S σ) · r⁻¹ dr .

Reuses `bijOn_radialMap`, the polar/`expMapBasis` Jacobian underlying the
`normLeOne` volume computation, and the `dr/r`-collar definition of
`surfaceMeasure`. Faithful to the standard treatment; no special-case narrowing. -/
theorem setIntegral_cone_eq_radial (h : mixedSpace K → ℂ)
    (hh : IntegrableOn h (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K)) :
    ∫ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K)
      = ∫ r in Set.Ioi (0 : ℝ),
          (∫ σ in normEqOneSurface K, h (radialMap K r σ) ∂(surfaceMeasure K)) * (r : ℝ)⁻¹
            ∂volume := by
  -- Notation: `F` is the radial parametrisation, `νd` the weighted product.
  haveI : SFinite (DedekindZeta.mixedMulHaar K) := by
    unfold DedekindZeta.mixedMulHaar; infer_instance
  haveI : SFinite (surfaceMeasure K) := by
    unfold surfaceMeasure; infer_instance
  have hbridge := mixedMulHaar_restrict_cone_eq_map (K := K)
  set F : ℝ × mixedSpace K → mixedSpace K := fun p => radialMap K p.1 p.2 with hFdef
  have hFmeas : Measurable F := continuous_radialMap_uncurry.measurable
  have hdens : Measurable (fun p : ℝ × mixedSpace K => ENNReal.ofReal p.1⁻¹) :=
    ENNReal.measurable_ofReal.comp measurable_fst.inv
  have hdenslt : ∀ᵐ p ∂(((volume.restrict (Set.Ioi (0 : ℝ))).prod (surfaceMeasure K))),
      ENNReal.ofReal p.1⁻¹ < ⊤ := ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  -- The surface measure is supported on `normEqOneSurface K`.
  have hae : ∀ᵐ σ ∂(surfaceMeasure K), σ ∈ normEqOneSurface K := by
    rw [ae_iff]
    simpa only [Set.mem_compl_iff, Set.compl_def] using
      surfaceMeasure_apply_compl_normEqOneSurface
  -- Transfer the cone integral through the pushforward bridge.
  have hh' : Integrable h ((DedekindZeta.mixedMulHaar K).restrict
      (mixedEmbedding.fundamentalCone K)) := hh
  rw [hbridge] at hh'
  -- LHS: `∫ x in cone, h = ∫ x, h ∂(restrict cone) = ∫ x, h ∂(map F νd)`.
  rw [show (∫ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K))
        = ∫ x, h x ∂((DedekindZeta.mixedMulHaar K).restrict
            (mixedEmbedding.fundamentalCone K)) from rfl, hbridge,
    integral_map hFmeas.aemeasurable hh'.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hdens hdenslt]
  -- Integrability of the weighted integrand against the product measure.
  have hint : Integrable
      (fun p : ℝ × mixedSpace K => (ENNReal.ofReal p.1⁻¹).toReal • h (F p))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (surfaceMeasure K)) := by
    refine (integrable_withDensity_iff_integrable_smul' hdens hdenslt
      (g := fun p => h (F p))).mp ?_
    exact (integrable_map_measure hh'.aestronglyMeasurable hFmeas.aemeasurable).mp hh'
  -- Fubini.
  rw [integral_prod _ hint]
  simp only [hFdef]
  -- Inner `σ`-integral: pull out `r⁻¹`, extend the surface integral to `S K`.
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := hr
  have hpos : (0 : ℝ) ≤ r⁻¹ := le_of_lt (inv_pos.mpr hr0)
  rw [integral_smul, ENNReal.toReal_ofReal hpos, Complex.real_smul, mul_comm,
    Measure.restrict_eq_self_of_ae_mem hae]

/-! ## 4. The orbit-integrated radial theta `F(𝔞, r)` and the radial-Mellin reduction

This section builds the orbit-integrated radial theta `F(𝔞, r)` by integrating
`Theta.idealThetaKernel K 𝔞` over the radius-`r` slice
of the norm-1 surface fundamental domain, and turn the per-class cone Mellin
`∫_cone Θ(𝔞,x)·N(x)^s d^*x` into the one-dimensional radial Mellin
`∫_0^∞ F(𝔞,r)·r^s dr/r = mellin (F 𝔞) s`, the shape consumed by the abstract
Mellin principle (`DedekindZeta/MellinPrinciple.lean`). -/

variable (K) in
/-- **The orbit-integrated radial theta** `F(𝔞, r)`.

`F(𝔞, r) = ∫_{S K} Θ(𝔞, radialMap K r σ) dμ_S σ`, the integral of
`Theta.idealThetaKernel K 𝔞` over the radius-`r` slice of the norm-1 surface
fundamental domain `normEqOneSurface K`: every `σ ∈ S K` is rescaled by
`radialMap K r` so that `mixedEmbedding.norm (radialMap K r σ) = r`
(`norm_radialMap_of_mem`). This is the one-dimensional function whose Mellin
transform is the per-class cone Mellin (`coneMellin_idealThetaKernel_eq_mellin`). -/
noncomputable def orbitTheta (𝔞 : Ideal (𝓞 K)) (r : ℝ) : ℂ :=
  ∫ σ in normEqOneSurface K, Theta.idealThetaKernel K 𝔞 (radialMap K r σ)
    ∂(surfaceMeasure K)

/-- **Radial reduction of the cone Mellin.** Applying the measure decomposition
`mixedMulHaar K = μ_S ⊗ dr/r` (`setIntegral_cone_eq_radial`) and the norm scaling
`N (radialMap K r σ) = r` (`norm_radialMap_of_mem`) to factor `N(x)^s = r^s` out
of the surface integral, the per-class cone Mellin becomes a one-dimensional
radial Mellin of the orbit-integrated theta `F = orbitTheta K 𝔞`:

    ∫_cone Θ(𝔞,x)·N(x)^s d^*x = ∫_0^∞ F(𝔞,r)·r^s · r⁻¹ dr .

Faithful to the standard treatment; no special-case narrowing. -/
theorem coneMellin_idealThetaKernel_eq_radial (𝔞 : Ideal (𝓞 K)) (s : ℂ)
    (hh : IntegrableOn
        (fun x => Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s)
        (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K)) :
    ∫ x in mixedEmbedding.fundamentalCone K,
        Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s
          ∂(DedekindZeta.mixedMulHaar K)
      = ∫ r in Set.Ioi (0 : ℝ),
          orbitTheta K 𝔞 r * (r : ℂ) ^ s * (r : ℝ)⁻¹ ∂volume := by
  rw [setIntegral_cone_eq_radial _ hh]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := hr
  -- Inner surface integral: factor `N(radialMap K r σ)^s = r^s` out of the
  -- `σ`-integral (`norm_radialMap_of_mem`), leaving `orbitTheta K 𝔞 r · r^s`.
  have hinner : (∫ σ in normEqOneSurface K,
        Theta.idealThetaKernel K 𝔞 (radialMap K r σ) *
          (mixedEmbedding.norm (radialMap K r σ) : ℂ) ^ s ∂(surfaceMeasure K))
      = orbitTheta K 𝔞 r * (r : ℂ) ^ s := by
    rw [orbitTheta, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_normEqOneSurface (fun σ hσ => ?_)
    rw [norm_radialMap_of_mem r hr0 hσ]
  rw [hinner]

/-- **The radial Mellin is Mathlib's `mellin` of `F`.** Since for `r > 0`,
`(r : ℂ)^s · r⁻¹ = (r : ℂ)^(s-1)`, the radial integral
`∫_0^∞ F(𝔞,r)·r^s · r⁻¹ dr` is exactly `mellin (orbitTheta K 𝔞) s`
(`= ∫_0^∞ (r:ℂ)^(s-1) • F(𝔞,r) dr`). This is the `reducedMellin`-shaped spelling
(`y^s dy/y = y^{s-1} dy`) of `DedekindZeta/MellinPrinciple.lean`. -/
theorem radialIntegral_eq_mellin (𝔞 : Ideal (𝓞 K)) (s : ℂ) :
    ∫ r in Set.Ioi (0 : ℝ),
        orbitTheta K 𝔞 r * (r : ℂ) ^ s * (r : ℝ)⁻¹ ∂volume
      = mellin (orbitTheta K 𝔞) s := by
  rw [mellin]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := hr
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  rw [smul_eq_mul, Complex.ofReal_inv, Complex.cpow_sub _ _ hrne, Complex.cpow_one]
  field_simp

/-- **The per-class cone Mellin is `mellin (F 𝔞)`.** Combining
`coneMellin_idealThetaKernel_eq_radial` with `radialIntegral_eq_mellin`: the cone
Mellin integral equals the one-dimensional Mellin transform of the
orbit-integrated radial theta `F = orbitTheta K 𝔞`. This is the shape consumed
by the abstract Mellin principle. -/
theorem coneMellin_idealThetaKernel_eq_mellin (𝔞 : Ideal (𝓞 K)) (s : ℂ)
    (hh : IntegrableOn
        (fun x => Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s)
        (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K)) :
    ∫ x in mixedEmbedding.fundamentalCone K,
        Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s
          ∂(DedekindZeta.mixedMulHaar K)
      = mellin (orbitTheta K 𝔞) s := by
  rw [coneMellin_idealThetaKernel_eq_radial 𝔞 s hh, radialIntegral_eq_mellin 𝔞 s]


/-! ## 5. Constant term, exponential decay, and the `IsMellinPair` packaging

This section supplies the asymptotic data that the abstract Mellin principle
(`DedekindZeta/MellinPrinciple.lean`) needs and bundles it into an `IsMellinPair`
hypothesis for the radial theta and its dual.

### Why the constant term `a₀` is the surface volume, not `0`

The orbit-integrated theta `orbitTheta K 𝔞` integrates `Theta.idealThetaKernel`,
which sums the Minkowski Gaussian over the **nonzero** ideal points only (the
`θ(iy) − 1` version). As `r → ∞` the radial scaling `radialMap K r σ` blows up
every coordinate of the compact norm-1 slice, so each Gaussian — hence the whole
kernel and `orbitTheta K 𝔞 r` — tends to `0`. Thus `orbitTheta K 𝔞` *alone* has
limit `0` and does **not** satisfy a clean inversion law: the kernel inversion
`Theta.idealThetaKernel_inversion` carries the additive `+1`/`-1` corrections
(the `a = 0` lattice term), and after orbit integration these become the
additive surface-volume constant
`V = (surfaceMeasure K (normEqOneSurface K)).toReal` (the orbit integral of the
constant `1`, i.e. the `+1`/zero-lattice term of the standard treatment).

To recover a function with the clean inversion law required by
`IsMellinPair.hfe`, we therefore form the **completed radial theta**
`radialTheta K 𝔞 r = orbitTheta K 𝔞 r + V`, whose constant term at `∞` is exactly
`a₀ = V` (the `+1` term) and which inverts as
`radialTheta K 𝔞 (1/r) = (1/covol 𝔞) · r · radialThetaDual K 𝔞 r`. Note that
`reducedMellin (radialTheta K 𝔞) V s = mellin (orbitTheta K 𝔞) s`, so this
completion changes nothing the regularised cone Mellin sees: it only restores
the constant term that powers the polar part `−a₀/s + C·b₀/(s−k)`.
-/

variable (K) in
/-- **The surface-volume constant** `V = vol(normEqOneSurface K)` (as a complex
scalar): the orbit integral of the constant `1` over the norm-1 surface
fundamental domain. This is the `+1`/zero-lattice term of the orbit-integrated
theta (the standard treatment) and the constant term `a₀` of the completed radial
theta `radialTheta`. It does not depend on the ideal `𝔞`. -/
noncomputable def surfaceVolume : ℂ :=
  ((surfaceMeasure K (normEqOneSurface K)).toReal : ℂ)

variable (K) in
/-- **Orbit-integrated radial theta of a fractional ideal** `I` (the dual case).

Like `orbitTheta`, but integrating `Theta.mixedThetaKernel K I` (the
fractional-ideal kernel) over the radius-`r` slice of the norm-1 surface, so it
applies to the dual fractional ideal `Theta.dualIdeal K 𝔞`. For integral `𝔞` it
agrees with `orbitTheta K 𝔞` via `Theta.idealThetaKernel_eq_mixed`. -/
noncomputable def orbitThetaFrac (I : FractionalIdeal (𝓞 K)⁰ K) (r : ℝ) : ℂ :=
  ∫ σ in normEqOneSurface K, Theta.mixedThetaKernel K I (radialMap K r σ)
    ∂(surfaceMeasure K)

variable (K) in
/-- **The completed radial theta** `F(𝔞, r) = orbitTheta K 𝔞 r + V` (the standard treatment's
`f(y)`): the orbit-integrated theta with the zero-lattice constant `V` restored,
so that its limit at `∞` is `a₀ = V` and it satisfies the clean inversion law
fed to `IsMellinPair`. See the section docstring for why the `+ V` is required. -/
noncomputable def radialTheta (𝔞 : Ideal (𝓞 K)) (r : ℝ) : ℂ :=
  orbitTheta K 𝔞 r + surfaceVolume K

variable (K) in
/-- **The dual completed radial theta** `G(𝔞, r) = orbitThetaFrac K (𝔞𝔡)⁻¹ r + V`
(the standard treatment's `g(y)`): the completed radial theta of the dual ideal
`Theta.dualIdeal K 𝔞`, the partner of `radialTheta K 𝔞` in the functional
equation. -/
noncomputable def radialThetaDual (𝔞 : Ideal (𝓞 K)) (r : ℝ) : ℂ :=
  orbitThetaFrac K (Theta.dualIdeal K 𝔞) r + surfaceVolume K




-- `integrableOn_mixedThetaKernel_radialMap` is stated and proved further below,
-- after its prerequisites `measure_normEqOneSurface_lt_top` and
-- `exists_bound_mixedThetaKernel_radialMap`.

/-- **Finiteness of the surface measure of the norm-1 surface.** The surface
measure `μ_S = surfaceMeasure K` (the `dr/r`-collar pushforward of the cone Haar
measure) assigns finite mass to the relatively compact norm-1 surface
fundamental domain, so the constant `1` is `μ_S`-integrable on it (and
`∫_S 1 dμ_S = V = surfaceVolume K`). the standard treatment. -/
theorem measure_normEqOneSurface_lt_top :
    surfaceMeasure K (normEqOneSurface K) < ⊤ := by
  classical
  -- Measurability of the radial projection `radialProj K`.
  have hq : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹ := by positivity
  have hscalar : Measurable
      (fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹ ^ ((finrank ℚ K : ℝ))⁻¹) :=
    (Real.continuous_rpow_const hq).measurable.comp
      ((mixedEmbedding.continuous_norm K).measurable.inv)
  have hmeas : Measurable (radialProj K) := hscalar.smul measurable_id
  -- The norm-collar `C = {x ∈ cone | N x ∈ (1, e]}`.
  set C : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hCdef
  have hCmeas : MeasurableSet C := by
    refine (measurableSet_fundamentalCone K).inter ?_
    exact (mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc
  -- `surfaceMeasure` is the pushforward of `mixedMulHaar` restricted to `C`, so its
  -- total mass is `mixedMulHaar C`; bound the surface mass by it.
  refine lt_of_le_of_lt (measure_mono (Set.subset_univ _)) ?_
  have huniv : surfaceMeasure K Set.univ = (DedekindZeta.mixedMulHaar K) C := by
    rw [surfaceMeasure, Measure.map_apply hmeas MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply_univ]
  rw [huniv]
  -- `mixedMulHaar C = ∫_C (2/π)^{r₂}·(N x)⁻¹ dx`; on `C` we have `N x > 1`, hence the
  -- density is bounded by the constant `(2/π)^{r₂}`.
  have hdensity : (DedekindZeta.mixedMulHaar K) C
      = ∫⁻ x in C, ENNReal.ofReal
          ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹) ∂volume :=
    withDensity_apply _ hCmeas
  have hbound : (DedekindZeta.mixedMulHaar K) C
      ≤ ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K) * volume C := by
    rw [hdensity, ← setLIntegral_const C]
    refine setLIntegral_mono measurable_const ?_
    rintro x ⟨-, hxN⟩
    apply ENNReal.ofReal_le_ofReal
    have hxpos : 0 < mixedEmbedding.norm x := lt_trans one_pos hxN.1
    have hinv : (mixedEmbedding.norm x)⁻¹ ≤ 1 := (inv_le_one₀ hxpos).mpr hxN.1.le
    calc (2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹
        ≤ (2 / Real.pi) ^ nrComplexPlaces K * 1 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (2 / Real.pi) ^ nrComplexPlaces K := mul_one _
  refine lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  -- Finiteness of `volume C`: `C` is bounded (a scaled copy of `normLeOne K`).
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hCbdd : Bornology.IsBounded C := by
    refine ((fundamentalCone.isBounded_normLeOne K).smul₀
      ((Real.exp 1) ^ ((finrank ℚ K : ℝ)⁻¹))).subset ?_
    rintro x ⟨hxcone, hxN⟩
    refine Set.mem_smul_set.mpr ⟨radialMap K (Real.exp 1)⁻¹ x, ?_, ?_⟩
    · rw [fundamentalCone.mem_normLeOne]
      refine ⟨radialMap_mem_cone (Real.exp 1)⁻¹ (inv_pos.mpr hepos) hxcone, ?_⟩
      rw [norm_radialMap (Real.exp 1)⁻¹ (inv_pos.mpr hepos) x]
      calc (Real.exp 1)⁻¹ * mixedEmbedding.norm x
          ≤ (Real.exp 1)⁻¹ * Real.exp 1 :=
            mul_le_mul_of_nonneg_left hxN.2 (inv_pos.mpr hepos).le
        _ = 1 := inv_mul_cancel₀ hepos.ne'
    · show radialMap K (Real.exp 1) (radialMap K (Real.exp 1)⁻¹ x) = x
      rw [radialMap_radialMap (Real.exp 1) (Real.exp 1)⁻¹ hepos.le (inv_pos.mpr hepos).le,
        mul_inv_cancel₀ hepos.ne']
      simp [radialMap]
  exact hCbdd.measure_lt_top

/-- **Uniform summable Gaussian majorant over the norm-1 surface.** For a nonzero
fractional ideal `I` there is a single `S ≥ 0` so that for *every* point `σ` of
the norm-1 surface fundamental domain `normEqOneSurface K`, the fixed-`σ`
fractional Gaussian lattice sum over the nonzero elements of `I` is summable and
bounded by `S`. Mechanism (the standard treatment): on the surface every place-norm
`normAtPlace w σ` is bounded above by a uniform `M ≥ 1` (the surface is
relatively compact, `isCompact_closure_normEqOneSurface`); since
`∏_w normAtPlace w σ ^ mult w = N σ = 1`, each `normAtPlace w σ` is then bounded
*below* by `κ = (M^d)⁻¹ > 0` (`d = [K:ℚ]`), uniformly in `σ`. Hence the
quadratic exponent obeys `Q_σ(a) ≥ κ² · Q₁(a)`, so every summand is dominated by
the single `σ`-independent Gaussian `mixedGaussian K (κ • mixedEmbedding K a)`,
whose lattice sum (`summable_mixedGaussian_submodule`) is the uniform `S`. -/
theorem mixedGaussian_surface_majorant (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ S : ℝ, 0 ≤ S ∧
      ∀ σ ∈ normEqOneSurface K,
        Summable (fun a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} =>
            Theta.mixedGaussian K (σ * mixedEmbedding K (a : K))) ∧
          (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
              Theta.mixedGaussian K (σ * mixedEmbedding K (a : K))) ≤ S := by
  classical
  -- Step 1: uniform upper bound `M ≥ 1` on every place-norm over the surface.
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ closure (normEqOneSurface K),
      ‖∑ w : InfinitePlace K, normAtPlace w x‖ ≤ C :=
    (isCompact_closure_normEqOneSurface (K := K)).exists_bound_of_continuousOn
      (by fun_prop)
  set M : ℝ := max C 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hupper : ∀ σ ∈ normEqOneSurface K, ∀ w : InfinitePlace K,
      normAtPlace w σ ≤ M := by
    intro σ hσ w
    have hsum := hC σ (subset_closure hσ)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun w _ => normAtPlace_nonneg w σ))] at hsum
    calc normAtPlace w σ
        ≤ ∑ w : InfinitePlace K, normAtPlace w σ :=
          Finset.single_le_sum (fun w _ => normAtPlace_nonneg w σ) (Finset.mem_univ w)
      _ ≤ C := hsum
      _ ≤ M := le_max_left _ _
  -- Step 2: uniform positive lower bound `κ = (M^d)⁻¹`.
  set d : ℕ := finrank ℚ K with hddef
  set κ : ℝ := (M ^ d)⁻¹ with hκdef
  have hMd : (1 : ℝ) ≤ M ^ d := one_le_pow₀ hM1
  have hκpos : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by rw [hκdef]; exact inv_le_one_of_one_le₀ hMd
  have hlower : ∀ σ ∈ normEqOneSurface K, ∀ w : InfinitePlace K,
      κ ≤ normAtPlace w σ := by
    intro σ hσ w₀
    have hnorm1 : mixedEmbedding.norm σ = 1 := (mem_normEqOneSurface.mp hσ).2
    have hne : mixedEmbedding.norm σ ≠ 0 := by rw [hnorm1]; exact one_ne_zero
    have hpos_all : ∀ w, 0 < normAtPlace w σ := by
      intro w
      refine lt_of_le_of_ne (normAtPlace_nonneg w σ) (Ne.symm ?_)
      intro h0
      exact hne (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, h0⟩)
    have hprod : ∏ w : InfinitePlace K, normAtPlace w σ ^ (mult w) = 1 := by
      rw [← mixedEmbedding.norm_apply]; exact hnorm1
    set X : ℝ := ∏ w ∈ Finset.univ.erase w₀, normAtPlace w σ ^ (mult w) with hXdef
    have hsplit : normAtPlace w₀ σ ^ (mult w₀) * X = 1 := by
      rw [hXdef, Finset.mul_prod_erase Finset.univ
        (fun w => normAtPlace w σ ^ (mult w)) (Finset.mem_univ w₀)]
      exact hprod
    have hXpos : 0 < X :=
      Finset.prod_pos (fun w _ => pow_pos (hpos_all w) _)
    have hX_le : X ≤ M ^ d := by
      have h1 : X ≤ ∏ w ∈ Finset.univ.erase w₀, M ^ (mult w) :=
        Finset.prod_le_prod (fun w _ => pow_nonneg (normAtPlace_nonneg w σ) _)
          (fun w _ => pow_le_pow_left₀ (normAtPlace_nonneg w σ) (hupper σ hσ w) _)
      have h3 : (∑ w ∈ Finset.univ.erase w₀, mult w) ≤ d := by
        rw [hddef, ← sum_mult_eq]
        exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      calc X ≤ ∏ w ∈ Finset.univ.erase w₀, M ^ (mult w) := h1
        _ = M ^ (∑ w ∈ Finset.univ.erase w₀, mult w) := by
            rw [Finset.prod_pow_eq_pow_sum]
        _ ≤ M ^ d := pow_le_pow_right₀ hM1 h3
    -- from `p ^ m * X = 1` and `X ≤ M^d`: `κ ≤ p ^ m`.
    have ha_eq : normAtPlace w₀ σ ^ (mult w₀) = 1 / X :=
      eq_one_div_of_mul_eq_one_left hsplit
    have hpow_ge : κ ≤ normAtPlace w₀ σ ^ (mult w₀) := by
      rw [hκdef, ha_eq, show (M ^ d)⁻¹ = 1 / (M ^ d) from (one_div _).symm]
      exact one_div_le_one_div_of_le hXpos hX_le
    -- conclude `κ ≤ p` from `κ ≤ p ^ m`, `κ ≤ 1`, `m ≥ 1`.
    rcases le_total (normAtPlace w₀ σ) 1 with hp1 | hp1
    · have hpm_le : normAtPlace w₀ σ ^ (mult w₀) ≤ normAtPlace w₀ σ :=
        pow_le_of_le_one (normAtPlace_nonneg w₀ σ) hp1 mult_ne_zero
      exact le_trans hpow_ge hpm_le
    · exact le_trans hκ1 hp1
  -- Step 3: the `σ`-independent majorant point `y = κ • 1`.
  set y : mixedSpace K := (κ : ℝ) • (1 : mixedSpace K) with hydef
  have hny : ∀ w : InfinitePlace K, normAtPlace w y = κ := by
    intro w
    rw [hydef, normAtPlace_smul, map_one, mul_one, abs_of_pos hκpos]
  have hyne : mixedEmbedding.norm y ≠ 0 := by
    rw [hydef, mixedEmbedding.norm_smul, map_one, mul_one, abs_of_pos hκpos]
    exact pow_ne_zero _ hκpos.ne'
  -- Step 4: pointwise majorant bound, uniform over the surface.
  have hbound : ∀ σ ∈ normEqOneSurface K, ∀ a : K,
      Theta.mixedGaussian K (σ * mixedEmbedding K a)
        ≤ Theta.mixedGaussian K (y * mixedEmbedding K a) := by
    intro σ hσ a
    rw [Theta.mixedGaussian, Theta.mixedGaussian]
    apply Real.exp_le_exp.mpr
    have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    have hsum_le : ∑ w : InfinitePlace K,
          (mult w : ℝ) * normAtPlace w (y * mixedEmbedding K a) ^ 2
        ≤ ∑ w : InfinitePlace K,
          (mult w : ℝ) * normAtPlace w (σ * mixedEmbedding K a) ^ 2 := by
      refine Finset.sum_le_sum (fun w _ => ?_)
      have hyw : normAtPlace w (y * mixedEmbedding K a)
          = κ * normAtPlace w (mixedEmbedding K a) := by
        rw [map_mul, hny]
      have hσw : normAtPlace w (σ * mixedEmbedding K a)
          = normAtPlace w σ * normAtPlace w (mixedEmbedding K a) := by rw [map_mul]
      rw [hyw, hσw]
      have hnz : (0 : ℝ) ≤ normAtPlace w (mixedEmbedding K a) := normAtPlace_nonneg _ _
      have hle : κ * normAtPlace w (mixedEmbedding K a)
          ≤ normAtPlace w σ * normAtPlace w (mixedEmbedding K a) :=
        mul_le_mul_of_nonneg_right (hlower σ hσ w) hnz
      have hsq : (κ * normAtPlace w (mixedEmbedding K a)) ^ 2
          ≤ (normAtPlace w σ * normAtPlace w (mixedEmbedding K a)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hκpos.le hnz) hle 2
      exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    nlinarith [hsum_le, Real.pi_pos]
  -- Step 5: summability + uniform tsum bound.
  set T := {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}
  let inc : T → (I : Submodule (𝓞 K) K) := fun a => ⟨a.1, a.2.1⟩
  have hinc_inj : Function.Injective inc := by
    intro a b h
    have hval : a.1 = b.1 := by simpa [inc] using h
    exact Subtype.ext hval
  -- summability of any fixed `y'` with `N y' ≠ 0`, over `T`.
  have hsummable : ∀ y' : mixedSpace K, mixedEmbedding.norm y' ≠ 0 →
      Summable (fun a : T => Theta.mixedGaussian K (y' * mixedEmbedding K (a : K))) := by
    intro y' hy'
    have hfull := Theta.summable_mixedGaussian_submodule K I hI hy'
    have hcomp := hfull.comp_injective hinc_inj
    rw [← Complex.summable_ofReal]
    exact hcomp.congr (fun a => rfl)
  -- the uniform majorant value.
  set S : ℝ := ∑' a : T, Theta.mixedGaussian K (y * mixedEmbedding K (a : K)) with hSdef
  have hSsummable : Summable (fun a : T =>
      Theta.mixedGaussian K (y * mixedEmbedding K (a : K))) := hsummable y hyne
  refine ⟨S, ?_, ?_⟩
  · rw [hSdef]
    exact tsum_nonneg (fun a => Real.exp_nonneg _)
  · intro σ hσ
    have hσne : mixedEmbedding.norm σ ≠ 0 := by
      rw [(mem_normEqOneSurface.mp hσ).2]; exact one_ne_zero
    have hσsummable := hsummable σ hσne
    refine ⟨hσsummable, ?_⟩
    rw [hSdef]
    exact hσsummable.tsum_le_tsum (fun a => hbound σ hσ (a : K)) hSsummable

/-! ### Minkowski quadratic form and the radial Gaussian scaling -/

variable (K) in
/-- **The Minkowski quadratic form** `Q(y) = ∑_w mult w · ‖y‖_w²` on `K_ℝ`: the
exponent (up to `-π`) of `Theta.mixedGaussian`. A complex place contributes
`2|y_w|²` via `mult w = 2`. the standard treatment. -/
noncomputable def mixedQuadForm (y : mixedSpace K) : ℝ :=
  ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w y ^ 2

/-- `mixedGaussian K y = exp(-π · Q(y))` (definitional unfolding through
`mixedQuadForm`). -/
theorem mixedGaussian_eq_exp_quadForm (y : mixedSpace K) :
    Theta.mixedGaussian K y = Real.exp (-Real.pi * mixedQuadForm K y) := rfl

/-- The Minkowski Gaussian is nonnegative (`exp ≥ 0`). -/
theorem mixedGaussian_nonneg (y : mixedSpace K) : 0 ≤ Theta.mixedGaussian K y := by
  rw [mixedGaussian_eq_exp_quadForm]; positivity

/-- **Homogeneity of degree 2.** `Q(c • y) = c² · Q(y)`: each place norm scales
by `|c|` (`normAtPlace_smul`), so its square scales by `c²`. -/
theorem mixedQuadForm_smul (c : ℝ) (y : mixedSpace K) :
    mixedQuadForm K (c • y) = c ^ 2 * mixedQuadForm K y := by
  unfold mixedQuadForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [normAtPlace_smul, mul_pow, sq_abs]
  ring

/-- **The radial blow-up scaling of the quadratic form.** Since
`radialMap K r y = r^{1/d} • y`, homogeneity gives
`Q(radialMap K r y) = r^{2/d} · Q(y)` (with `d = [K:ℚ]`). -/
theorem mixedQuadForm_radialMap (r : ℝ) (hr : 0 < r) (y : mixedSpace K) :
    mixedQuadForm K (radialMap K r y)
      = r ^ (2 * (finrank ℚ K : ℝ)⁻¹) * mixedQuadForm K y := by
  rw [radialMap, mixedQuadForm_smul]
  congr 1
  rw [mul_comm (2 : ℝ), Real.rpow_mul hr.le,
    ← Real.rpow_natCast (r ^ ((finrank ℚ K : ℝ)⁻¹)) 2]
  norm_num

/-- **Summability of the integral-kernel Gaussian family** over the nonzero
elements of `𝔞` (for any unit point `x`, `N x ≠ 0`): a subfamily of the
whole-lattice Gaussian sum `summable_mixedGaussian_submodule`, reindexed through
the injection `𝓞 K ↪ K` and brought back to `ℝ` via `Complex.summable_ofReal`. -/
theorem summable_mixedGaussian_idealKernel (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥)
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    Summable (fun a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} =>
      Theta.mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K))) := by
  set J : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hJ
  have hJ0 : J ≠ 0 := (FractionalIdeal.coeIdeal_ne_zero).mpr h𝔞
  have hmem : ∀ a : 𝓞 K, a ∈ 𝔞 → (a : K) ∈ (J : Submodule (𝓞 K) K) := by
    intro a ha
    rw [FractionalIdeal.mem_coe, hJ, RingOfIntegers.coe_eq_algebraMap]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ ha
  have hC := Theta.summable_mixedGaussian_submodule K J hJ0 hx
  let f : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} → (J : Submodule (𝓞 K) K) :=
    fun a => ⟨(a.1 : K), hmem a.1 a.2.1⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have hval : ((f a : (J : Submodule (𝓞 K) K)) : K) = ((f b : (J : Submodule (𝓞 K) K)) : K) :=
      congrArg (fun t : (J : Submodule (𝓞 K) K) => (t : K)) hab
    exact Subtype.ext (RingOfIntegers.coe_injective hval)
  have hCsub := hC.comp_injective hfinj
  rw [← Complex.summable_ofReal]
  exact hCsub

/-- **Uniform positive lower bound on the nonzero Minkowski norms over the
surface.** There is `q > 0` with `q ≤ Q(σ · σ(a))` for every `σ` on the norm-1
surface fundamental domain and every nonzero `a ∈ 𝔞`. The points `σ · σ(a)`
range over a (rescaled) lattice with no accumulation at `0` away from `a = 0`,
and the surface is relatively compact, so the smallest nonzero squared norm is
bounded below by a positive constant. the standard treatment. -/
theorem exists_pos_lower_mixedQuadForm (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ q : ℝ, 0 < q ∧ ∀ σ ∈ normEqOneSurface K,
      ∀ a : 𝓞 K, a ∈ 𝔞 → a ≠ 0 →
        q ≤ mixedQuadForm K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by
  classical
  -- Step 1: a uniform upper bound `M ≥ 1` on every place-norm over the surface
  -- (same mechanism as in `mixedGaussian_surface_majorant`).
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ closure (normEqOneSurface K),
      ‖∑ w : InfinitePlace K, normAtPlace w x‖ ≤ C :=
    (isCompact_closure_normEqOneSurface (K := K)).exists_bound_of_continuousOn
      (by fun_prop)
  set M : ℝ := max C 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hupper : ∀ σ ∈ normEqOneSurface K, ∀ w : InfinitePlace K,
      normAtPlace w σ ≤ M := by
    intro σ hσ w
    have hsum := hC σ (subset_closure hσ)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun w _ => normAtPlace_nonneg w σ))] at hsum
    calc normAtPlace w σ
        ≤ ∑ w : InfinitePlace K, normAtPlace w σ :=
          Finset.single_le_sum (fun w _ => normAtPlace_nonneg w σ) (Finset.mem_univ w)
      _ ≤ C := hsum
      _ ≤ M := le_max_left _ _
  -- Step 2: uniform positive lower bound `κ = (M^d)⁻¹` on every place-norm.
  set d : ℕ := finrank ℚ K with hddef
  set κ : ℝ := (M ^ d)⁻¹ with hκdef
  have hMd : (1 : ℝ) ≤ M ^ d := one_le_pow₀ hM1
  have hκpos : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by rw [hκdef]; exact inv_le_one_of_one_le₀ hMd
  have hlower : ∀ σ ∈ normEqOneSurface K, ∀ w : InfinitePlace K,
      κ ≤ normAtPlace w σ := by
    intro σ hσ w₀
    have hnorm1 : mixedEmbedding.norm σ = 1 := (mem_normEqOneSurface.mp hσ).2
    have hne : mixedEmbedding.norm σ ≠ 0 := by rw [hnorm1]; exact one_ne_zero
    have hpos_all : ∀ w, 0 < normAtPlace w σ := by
      intro w
      refine lt_of_le_of_ne (normAtPlace_nonneg w σ) (Ne.symm ?_)
      intro h0
      exact hne (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, h0⟩)
    have hprod : ∏ w : InfinitePlace K, normAtPlace w σ ^ (mult w) = 1 := by
      rw [← mixedEmbedding.norm_apply]; exact hnorm1
    set X : ℝ := ∏ w ∈ Finset.univ.erase w₀, normAtPlace w σ ^ (mult w) with hXdef
    have hsplit : normAtPlace w₀ σ ^ (mult w₀) * X = 1 := by
      rw [hXdef, Finset.mul_prod_erase Finset.univ
        (fun w => normAtPlace w σ ^ (mult w)) (Finset.mem_univ w₀)]
      exact hprod
    have hXpos : 0 < X :=
      Finset.prod_pos (fun w _ => pow_pos (hpos_all w) _)
    have hX_le : X ≤ M ^ d := by
      have h1 : X ≤ ∏ w ∈ Finset.univ.erase w₀, M ^ (mult w) :=
        Finset.prod_le_prod (fun w _ => pow_nonneg (normAtPlace_nonneg w σ) _)
          (fun w _ => pow_le_pow_left₀ (normAtPlace_nonneg w σ) (hupper σ hσ w) _)
      have h3 : (∑ w ∈ Finset.univ.erase w₀, mult w) ≤ d := by
        rw [hddef, ← sum_mult_eq]
        exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      calc X ≤ ∏ w ∈ Finset.univ.erase w₀, M ^ (mult w) := h1
        _ = M ^ (∑ w ∈ Finset.univ.erase w₀, mult w) := by
            rw [Finset.prod_pow_eq_pow_sum]
        _ ≤ M ^ d := pow_le_pow_right₀ hM1 h3
    have ha_eq : normAtPlace w₀ σ ^ (mult w₀) = 1 / X :=
      eq_one_div_of_mul_eq_one_left hsplit
    have hpow_ge : κ ≤ normAtPlace w₀ σ ^ (mult w₀) := by
      rw [hκdef, ha_eq, show (M ^ d)⁻¹ = 1 / (M ^ d) from (one_div _).symm]
      exact one_div_le_one_div_of_le hXpos hX_le
    rcases le_total (normAtPlace w₀ σ) 1 with hp1 | hp1
    · have hpm_le : normAtPlace w₀ σ ^ (mult w₀) ≤ normAtPlace w₀ σ :=
        pow_le_of_le_one (normAtPlace_nonneg w₀ σ) hp1 mult_ne_zero
      exact le_trans hpow_ge hpm_le
    · exact le_trans hκ1 hp1
  -- Step 3: the uniform lower bound is `q = κ²`.
  refine ⟨κ ^ 2, by positivity, ?_⟩
  intro σ hσ a ha𝔞 ha0
  set P : mixedSpace K := mixedEmbedding K ((a : 𝓞 K) : K) with hPdef
  -- `|N a| ≥ 1`, hence `∏_w ‖P‖_w^{mult w} ≥ 1` and `P ≠ 0`.
  have h1le : (1 : ℝ) ≤ |Algebra.norm ℚ ((a : 𝓞 K) : K)| := by
    rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_intCast, Int.cast_le]
    exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha0)
  have hnormP : mixedEmbedding.norm P = |Algebra.norm ℚ ((a : 𝓞 K) : K)| :=
    mixedEmbedding.norm_eq_norm _
  have hPne : mixedEmbedding.norm P ≠ 0 := by
    rw [hnormP]; exact ne_of_gt (lt_of_lt_of_le one_pos h1le)
  have hpos : ∀ w : InfinitePlace K, 0 < normAtPlace w P := by
    intro w
    refine lt_of_le_of_ne (normAtPlace_nonneg w P) (Ne.symm ?_)
    intro h0
    exact hPne (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, h0⟩)
  have hprodP : (1 : ℝ) ≤ ∏ w : InfinitePlace K, normAtPlace w P ^ (mult w) := by
    rw [← mixedEmbedding.norm_apply, hnormP]; exact h1le
  -- There is a place `w₀` with `‖P‖_{w₀} ≥ 1`.
  obtain ⟨w₀, hw₀⟩ : ∃ w : InfinitePlace K, 1 ≤ normAtPlace w P := by
    by_contra h
    push_neg at h
    have hlt : ∏ w : InfinitePlace K, normAtPlace w P ^ (mult w) < 1 := by
      calc ∏ w : InfinitePlace K, normAtPlace w P ^ (mult w)
          < ∏ _w : InfinitePlace K, (1 : ℝ) :=
            Finset.prod_lt_prod_of_nonempty
              (fun w _ => pow_pos (hpos w) _)
              (fun w _ => pow_lt_one₀ (normAtPlace_nonneg w P) (h w) mult_ne_zero)
              Finset.univ_nonempty
        _ = 1 := by simp
    exact absurd hprodP (not_le.mpr hlt)
  -- Conclude: `Q(σ·P) ≥ mult w₀ · (‖σ‖_{w₀}·‖P‖_{w₀})² ≥ κ²`.
  have hterm : κ ^ 2 ≤ (mult w₀ : ℝ) * normAtPlace w₀ (σ * P) ^ 2 := by
    have hmap : normAtPlace w₀ (σ * P) = normAtPlace w₀ σ * normAtPlace w₀ P := by
      rw [map_mul]
    have e2 : κ ≤ normAtPlace w₀ σ := hlower σ hσ w₀
    have hb : κ ≤ normAtPlace w₀ σ * normAtPlace w₀ P := by
      calc κ = κ * 1 := (mul_one κ).symm
        _ ≤ normAtPlace w₀ σ * normAtPlace w₀ P :=
          mul_le_mul e2 hw₀ zero_le_one (le_trans hκpos.le e2)
    have hsq : κ ^ 2 ≤ (normAtPlace w₀ σ * normAtPlace w₀ P) ^ 2 :=
      pow_le_pow_left₀ hκpos.le hb 2
    rw [hmap]
    calc κ ^ 2 = 1 * κ ^ 2 := (one_mul _).symm
      _ ≤ (mult w₀ : ℝ) * (normAtPlace w₀ σ * normAtPlace w₀ P) ^ 2 :=
        mul_le_mul one_le_mult hsq (sq_nonneg _) (le_trans zero_le_one one_le_mult)
  have hsum_ge : (mult w₀ : ℝ) * normAtPlace w₀ (σ * P) ^ 2
      ≤ ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w (σ * P) ^ 2 :=
    Finset.single_le_sum
      (f := fun w : InfinitePlace K => (InfinitePlace.mult w : ℝ) * normAtPlace w (σ * P) ^ 2)
      (fun w _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Finset.mem_univ w₀)
  calc κ ^ 2 ≤ (mult w₀ : ℝ) * normAtPlace w₀ (σ * P) ^ 2 := hterm
    _ ≤ mixedQuadForm K (σ * P) := hsum_ge

/-- **Uniform bound on the `r = 1` lattice Gaussian sum over the surface.**
There is `M ≥ 0` with `∑'_{a≠0} mixedGaussian K (σ · σ(a)) ≤ M` for every `σ` on
the norm-1 surface fundamental domain: the residual convergent lattice theta sum
at radius `1`, bounded uniformly over the relatively compact surface. the standard treatment. -/
theorem exists_bound_tsum_mixedGaussian_surface (𝔞 : Ideal (𝓞 K)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ normEqOneSurface K,
      ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
        Theta.mixedGaussian K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) ≤ M := by
  -- Reproved by the termwise-majorant
  -- route, staying inside the nonzero-norm locus: NOT the unsound global
  -- continuity / closure-maximum argument. The integer-indexed sum over the
  -- nonzero elements of `𝔞` injects into the fractional-ideal-indexed sum over
  -- `(𝔞 : FractionalIdeal)`, for which `mixedGaussian_surface_majorant` already
  -- supplies a uniform `σ`-independent bound `S` (a single convergent Gaussian
  -- lattice majorant via the uniform place-norm lower bound `κ`). Comparing the
  -- two tsums termwise (all summands nonnegative) through that injection gives
  -- the same bound for the integer-indexed sum.
  classical
  by_cases h𝔞 : 𝔞 = ⊥
  · -- the zero ideal: the index set is empty, so the sum is `0`.
    subst h𝔞
    refine ⟨0, le_refl 0, ?_⟩
    intro σ _
    have hempty : IsEmpty {a : 𝓞 K // a ∈ (⊥ : Ideal (𝓞 K)) ∧ a ≠ 0} := by
      constructor
      rintro ⟨a, ha, hne⟩
      rw [Ideal.mem_bot] at ha
      exact hne ha
    rw [tsum_empty]
  · set J : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hJ
    have hJ0 : J ≠ 0 := (FractionalIdeal.coeIdeal_ne_zero).mpr h𝔞
    obtain ⟨S, hS, hSbound⟩ := mixedGaussian_surface_majorant J hJ0
    refine ⟨S, hS, ?_⟩
    intro σ hσ
    obtain ⟨hσsum, hσle⟩ := hSbound σ hσ
    -- the injection `{a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} ↪ {a : K // a ∈ J ∧ a ≠ 0}`.
    have hmem : ∀ a : 𝓞 K, a ∈ 𝔞 → (a : K) ∈ (J : Submodule (𝓞 K) K) := by
      intro a ha
      rw [FractionalIdeal.mem_coe, hJ, RingOfIntegers.coe_eq_algebraMap]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ ha
    set i : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} →
        {a : K // a ∈ (J : Submodule (𝓞 K) K) ∧ a ≠ 0} :=
      fun a => ⟨(a.1 : K), hmem a.1 a.2.1,
        (RingOfIntegers.coe_ne_zero_iff).mpr a.2.2⟩ with hidef
    have hiinj : Function.Injective i := by
      intro a b hab
      have hval : ((i a).1) = ((i b).1) := congrArg Subtype.val hab
      exact Subtype.ext (RingOfIntegers.coe_injective hval)
    -- compare the integer-indexed tsum with the submodule-indexed tsum.
    have hcomp := tsum_comp_le_tsum_of_inj hσsum
      (fun a => mixedGaussian_nonneg (σ * mixedEmbedding K (a : K))) hiinj
    calc ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
            Theta.mixedGaussian K (σ * mixedEmbedding K ((a : 𝓞 K) : K))
        = ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
            Theta.mixedGaussian K (σ * mixedEmbedding K ((i a).1)) := rfl
      _ ≤ ∑' a : {a : K // a ∈ (J : Submodule (𝓞 K) K) ∧ a ≠ 0},
            Theta.mixedGaussian K (σ * mixedEmbedding K (a : K)) := hcomp
      _ ≤ S := hσle

/-- **Uniform Gaussian bound on the orbit kernel over the norm-1 surface** (the
analytic crux of `orbitTheta_isBigO_exp`). There are `c, α > 0` and `B ≥ 0` such
that for every radius `r ≥ 1` and every point `σ` of the norm-1 surface
fundamental domain,
`‖idealThetaKernel K 𝔞 (radialMap K r σ)‖ ≤ B · exp(-c r^α)`.

This is the radial blow-up estimate: `radialMap K r σ = r^{1/d} • σ` scales the
Minkowski quadratic exponent of every Gaussian summand by `r^{2/d}`, so the
whole kernel decays like `exp(-c r^{2/d})` (`α = 2/[K:ℚ]`), uniformly in `σ`
over the relatively compact surface. the standard treatment. -/
theorem norm_idealThetaKernel_radialMap_isBigO (𝔞 : Ideal (𝓞 K)) :
    ∃ c α B : ℝ, 0 < c ∧ 0 < α ∧ 0 ≤ B ∧
      ∀ r : ℝ, 1 ≤ r → ∀ σ ∈ normEqOneSurface K,
        ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖ ≤ B * Real.exp (-c * r ^ α) := by
  -- The zero ideal: the kernel sums over the empty index set, hence vanishes.
  by_cases h𝔞 : 𝔞 = ⊥
  · subst h𝔞
    refine ⟨1, 1, 0, one_pos, one_pos, le_refl 0, ?_⟩
    intro r _ σ _
    have hempty : IsEmpty {a : 𝓞 K // a ∈ (⊥ : Ideal (𝓞 K)) ∧ a ≠ 0} := by
      constructor
      rintro ⟨a, ha, hne⟩
      rw [Ideal.mem_bot] at ha
      exact hne ha
    rw [Theta.idealThetaKernel, tsum_empty]
    simp
  -- Nonzero ideal. Extract the analytic constants.
  obtain ⟨q, hq, hlower⟩ := exists_pos_lower_mixedQuadForm 𝔞 h𝔞
  obtain ⟨M, hM, hMbound⟩ := exists_bound_tsum_mixedGaussian_surface 𝔞
  have hfr : 0 < (finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  set α : ℝ := 2 * (finrank ℚ K : ℝ)⁻¹ with hαdef
  have hαpos : 0 < α := by rw [hαdef]; positivity
  refine ⟨Real.pi * q, α, M * Real.exp (Real.pi * q), mul_pos Real.pi_pos hq, hαpos,
    mul_nonneg hM (Real.exp_pos _).le, ?_⟩
  intro r hr σ hσ
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have hg_nonneg : ∀ z : mixedSpace K, 0 ≤ Theta.mixedGaussian K z := mixedGaussian_nonneg
  -- Summability of the integral-kernel Gaussian family at `radialMap K r σ` and at `σ`.
  have hxnorm : mixedEmbedding.norm (radialMap K r σ) ≠ 0 := by
    rw [norm_radialMap_of_mem r hr0 hσ]; exact hr0.ne'
  have hσnorm : mixedEmbedding.norm σ ≠ 0 := by
    rw [(mem_normEqOneSurface.mp hσ).2]; exact one_ne_zero
  have hsum_x := summable_mixedGaussian_idealKernel 𝔞 h𝔞 hxnorm
  have hsum_σ := summable_mixedGaussian_idealKernel 𝔞 h𝔞 hσnorm
  -- `‖kernel‖ ≤ ∑` of the (real, nonneg) Gaussian summands.
  have hnorm_le : ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖
      ≤ ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
          Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by
    rw [Theta.idealThetaKernel]
    have hsummablenorm : Summable (fun a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} =>
        ‖(Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)‖) := by
      have hfun : (fun a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} =>
          ‖(Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)‖)
          = (fun a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} => Theta.mixedGaussian K
              (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K))) := by
        funext a
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg_nonneg _)]
      rw [hfun]; exact hsum_x
    refine (norm_tsum_le_tsum_norm hsummablenorm).trans_eq (tsum_congr (fun a => ?_))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg_nonneg _)]
  -- Per-summand radial decay split, summed up.
  have hstep : (∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
        Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)))
      ≤ Real.exp (-Real.pi * (r ^ α - 1) * q)
          * ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
              Theta.mixedGaussian K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun a => ?_) hsum_x
      (hsum_σ.mul_left (Real.exp (-Real.pi * (r ^ α - 1) * q)))
    have hQ : q ≤ mixedQuadForm K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) :=
      hlower σ hσ a.1 a.2.1 a.2.2
    have hmul : radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)
        = radialMap K r (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by
      rw [radialMap, radialMap, smul_mul_assoc]
    rw [hmul, mixedGaussian_eq_exp_quadForm, mixedQuadForm_radialMap r hr0, ← hαdef,
      mixedGaussian_eq_exp_quadForm, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hprod : 0 ≤ Real.pi *
        ((r ^ α - 1) * (mixedQuadForm K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) - q)) :=
      mul_nonneg Real.pi_pos.le
        (mul_nonneg (by linarith [Real.one_le_rpow hr hαpos.le]) (by linarith))
    nlinarith [hprod]
  -- Algebra: `M · exp(-π(r^α-1)q) = (M·exp(πq)) · exp(-(πq)·r^α)`.
  have hexp_eq : Real.exp (-Real.pi * (r ^ α - 1) * q)
      = Real.exp (Real.pi * q) * Real.exp (-(Real.pi * q) * r ^ α) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖
      ≤ ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
          Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)) := hnorm_le
    _ ≤ Real.exp (-Real.pi * (r ^ α - 1) * q)
          * ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
              Theta.mixedGaussian K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := hstep
    _ ≤ Real.exp (-Real.pi * (r ^ α - 1) * q) * M :=
          mul_le_mul_of_nonneg_left (hMbound σ hσ) (Real.exp_nonneg _)
    _ = M * Real.exp (Real.pi * q) * Real.exp (-(Real.pi * q) * r ^ α) := by
          rw [hexp_eq]; ring

variable (K) in
/-- **The closure of the norm-1 surface lies in the norm-1 locus.**
`mixedEmbedding.norm` is continuous and `{x | N x = 1}` is closed, while
`normEqOneSurface K ⊆ {N = 1}` (`mem_normEqOneSurface`), so the closure stays
inside.  In particular every point of the closure has nonzero norm.  This is the
geometric input letting `radialMap K r` push the (relatively compact) surface
slice into the Gaussian-summable nonzero-norm locus.  the standard treatment. -/
theorem closure_normEqOneSurface_subset :
    closure (normEqOneSurface K) ⊆ {x : mixedSpace K | mixedEmbedding.norm x = 1} := by
  have hclosed : IsClosed {x : mixedSpace K | mixedEmbedding.norm x = 1} :=
    isClosed_eq (mixedEmbedding.continuous_norm K) continuous_const
  refine closure_minimal (fun x hx => ?_) hclosed
  exact (mem_normEqOneSurface.mp hx).2

variable (K) in
/-- For `r > 0`, the radial scaling `radialMap K r` maps the closure of the
norm-1 surface into the nonzero-norm locus: for `x` with `N x = 1` we get
`N (radialMap K r x) = r > 0` (`norm_radialMap`).  the standard treatment. -/
theorem mapsTo_radialMap_closure_normEqOneSurface (r : ℝ) (hr : 0 < r) :
    Set.MapsTo (radialMap K r) (closure (normEqOneSurface K))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
  intro x hx
  have hx1 : mixedEmbedding.norm x = 1 := closure_normEqOneSurface_subset K hx
  simp only [Set.mem_setOf_eq, norm_radialMap r hr x, hx1, mul_one]
  exact hr.ne'

variable (K) in
/-- **Continuity of the mixed theta kernel along the radius-`r` surface slice.**
For `r > 0`, `σ ↦ Theta.mixedThetaKernel K I (radialMap K r σ)` is continuous on
`closure (normEqOneSurface K)`: `radialMap K r` is continuous and maps the
closure into the nonzero-norm locus (`mapsTo_radialMap_closure_normEqOneSurface`),
on which `Theta.mixedThetaKernel K I` is continuous
(`Theta.continuousOn_mixedThetaKernel`).  The kernel is genuinely discontinuous
at `{N = 0}` (the Gaussian lattice sum diverges there), which is exactly why we
restrict to this slice where `N (radialMap K r σ) = r > 0`.  the standard treatment.
Reusable by `continuousOn_orbitThetaFrac` / `orbitTheta_isBigO_exp`. -/
theorem continuousOn_mixedThetaKernel_radialMap (I : FractionalIdeal (𝓞 K)⁰ K)
    (r : ℝ) (hr : 0 < r) :
    ContinuousOn (fun σ => Theta.mixedThetaKernel K I (radialMap K r σ))
      (closure (normEqOneSurface K)) :=
  (Theta.continuousOn_mixedThetaKernel K I).comp
    (continuous_const_smul (r ^ ((finrank ℚ K : ℝ)⁻¹))).continuousOn
    (mapsTo_radialMap_closure_normEqOneSurface K r hr)

variable (K) in
/-- **Uniform bound for the mixed theta kernel on the radius-`r` surface slice.**
For `r > 0` there is a constant `C` with
`‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ≤ C` for every
`σ ∈ normEqOneSurface K`.  Obtained by bounding the continuous function
(`continuousOn_mixedThetaKernel_radialMap`) over the compact closure
(`isCompact_closure_normEqOneSurface`, `IsCompact.exists_bound_of_continuousOn`)
and restricting to `normEqOneSurface K ⊆ closure (normEqOneSurface K)`.  This is
the form the integrability child consumes via `Integrable.mono'`.
the standard treatment. -/
theorem exists_bound_mixedThetaKernel_radialMap (I : FractionalIdeal (𝓞 K)⁰ K)
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, ∀ σ ∈ normEqOneSurface K,
      ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closure_normEqOneSurface (K := K)).exists_bound_of_continuousOn
    (continuousOn_mixedThetaKernel_radialMap K I r hr)
  exact ⟨C, fun σ hσ => hC σ (subset_closure hσ)⟩

/-- **Integrability of the dual kernel over the radius-`r` surface slice.** For
`r > 0` the integrand `σ ↦ Θ_mix(I, radialMap K r σ)` defining `orbitThetaFrac`
is integrable over the (relatively compact) norm-1 surface fundamental domain
against `surfaceMeasure K`. The surface measure of the (relatively compact)
norm-1 surface is finite (`measure_normEqOneSurface_lt_top`), so the constant
bound `C` from `exists_bound_mixedThetaKernel_radialMap` is integrable on the
restricted (finite) measure; the integrand is `AEStronglyMeasurable` because it
is `ContinuousOn` the closure (`continuousOn_mixedThetaKernel_radialMap`), hence
on `normEqOneSurface K`.  Conclude via `Integrable.mono'`.  the standard treatment. -/
theorem integrableOn_mixedThetaKernel_radialMap
    (I : FractionalIdeal (𝓞 K)⁰ K) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun σ => Theta.mixedThetaKernel K I (radialMap K r σ))
      (normEqOneSurface K) (surfaceMeasure K) := by
  -- Finite restricted measure ⇒ constants are integrable on `S`.
  haveI : IsFiniteMeasure ((surfaceMeasure K).restrict (normEqOneSurface K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_normEqOneSurface_lt_top⟩
  -- Uniform bound `C` on the kernel over the surface slice.
  obtain ⟨C, hC⟩ := exists_bound_mixedThetaKernel_radialMap K I r hr
  -- The integrand is `AEStronglyMeasurable` (continuous on `S ⊆ closure S`).
  have hcont : ContinuousOn (fun σ => Theta.mixedThetaKernel K I (radialMap K r σ))
      (normEqOneSurface K) :=
    (continuousOn_mixedThetaKernel_radialMap K I r hr).mono subset_closure
  refine Integrable.mono' (g := fun _ => C)
    (integrable_const C)
    (hcont.aestronglyMeasurable measurableSet_normEqOneSurface) ?_
  exact (ae_restrict_iff' measurableSet_normEqOneSurface).mpr
    (Filter.Eventually.of_forall (fun σ hσ => hC σ hσ))

variable (K) in
/-- **Continuity of the fractional orbit-integrated radial theta**
`r ↦ orbitThetaFrac K I r` **on the open ray `(0, ∞)`**, the dual-side analogue
of `continuousOn_orbitTheta` with `Theta.mixedThetaKernel K I` in place of
`Theta.idealThetaKernel K 𝔞`. Like the primal case this is `ContinuousOn`
`Set.Ioi 0`, not global: `radialMap K r σ` lands in the nonzero-norm
Gaussian-summable locus — on which `Theta.mixedThetaKernel` is continuous
(`Theta.continuousOn_mixedThetaKernel`) — exactly when `r > 0`. the standard treatment. -/
theorem continuousOn_orbitThetaFrac (I : FractionalIdeal (𝓞 K)⁰ K) :
    ContinuousOn (orbitThetaFrac K I) (Set.Ioi 0) := by
  classical
  -- The zero ideal: the kernel sums over the empty index set, so `orbitThetaFrac ≡ 0`.
  by_cases hI : I = 0
  · have hzero : orbitThetaFrac K I = fun _ : ℝ => (0 : ℂ) := by
      funext r
      rw [orbitThetaFrac]
      have hker : ∀ σ : mixedSpace K,
          Theta.mixedThetaKernel K I (radialMap K r σ) = 0 := by
        intro σ
        subst hI
        haveI : IsEmpty {a : K // a ∈ ((0 : FractionalIdeal (𝓞 K)⁰ K) :
            Submodule (𝓞 K) K) ∧ a ≠ 0} := by
          refine ⟨?_⟩
          rintro ⟨a, ha, ha0⟩
          rw [FractionalIdeal.coe_zero, Submodule.mem_bot] at ha
          exact ha0 ha
        rw [Theta.mixedThetaKernel, tsum_empty]
      simp only [hker, integral_zero]
    rw [hzero]
    exact continuousOn_const
  -- Nonzero ideal: dominated continuity of the parametric integral over the
  -- (finite-measure) norm-1 surface slice.
  set μ : Measure (mixedSpace K) := (surfaceMeasure K).restrict (normEqOneSurface K)
    with hμ
  -- Summability of the real Gaussian family over the nonzero elements of `I`,
  -- at any nonzero-norm point `y` (subfamily of `summable_mixedGaussian_submodule`).
  set T := {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} with hT
  have hsummable : ∀ y : mixedSpace K, mixedEmbedding.norm y ≠ 0 →
      Summable (fun a : T => Theta.mixedGaussian K (y * mixedEmbedding K (a : K))) := by
    intro y hy
    have hinc_inj : Function.Injective
        (fun a : T => (⟨a.1, a.2.1⟩ : (I : Submodule (𝓞 K) K))) := by
      intro a b h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
    have hcomp := (Theta.summable_mixedGaussian_submodule K I hI hy).comp_injective hinc_inj
    rw [← Complex.summable_ofReal]
    exact hcomp.congr (fun a => rfl)
  -- `‖kernel x‖` equals the real lattice Gaussian sum at any nonzero-norm `x`.
  have hnorm_eq : ∀ {x : mixedSpace K}, mixedEmbedding.norm x ≠ 0 →
      ‖Theta.mixedThetaKernel K I x‖
        = ∑' a : T, Theta.mixedGaussian K (x * mixedEmbedding K (a : K)) := by
    intro x _hx
    rw [Theta.mixedThetaKernel, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg (fun a => mixedGaussian_nonneg _))]
  refine continuousOn_of_forall_continuousAt (fun r₀ hr₀ => ?_)
  have hr₀0 : (0 : ℝ) < r₀ := hr₀
  set rlo : ℝ := r₀ / 2 with hrlo
  have hlo0 : (0 : ℝ) < rlo := by rw [hrlo]; linarith
  have hlt : rlo < r₀ := by rw [hrlo]; linarith
  -- The dominating function `g σ = ‖kernel (radialMap K rlo σ)‖`, integrable on `S`.
  have hint_lo : IntegrableOn
      (fun σ => Theta.mixedThetaKernel K I (radialMap K rlo σ))
      (normEqOneSurface K) (surfaceMeasure K) :=
    integrableOn_mixedThetaKernel_radialMap (K := K) I rlo hlo0
  have hbound_int :
      Integrable (fun σ => ‖Theta.mixedThetaKernel K I (radialMap K rlo σ)‖) μ :=
    hint_lo.norm
  -- Per-radius monotone domination for `r ≥ rlo` over the surface.
  have hdom : ∀ x : ℝ, rlo ≤ x → ∀ σ ∈ normEqOneSurface K,
      ‖Theta.mixedThetaKernel K I (radialMap K x σ)‖
        ≤ ‖Theta.mixedThetaKernel K I (radialMap K rlo σ)‖ := by
    intro x hx σ hσ
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hlo0 hx
    have hxnorm : mixedEmbedding.norm (radialMap K x σ) ≠ 0 := by
      rw [norm_radialMap_of_mem x hx0 hσ]; exact hx0.ne'
    have hlonorm : mixedEmbedding.norm (radialMap K rlo σ) ≠ 0 := by
      rw [norm_radialMap_of_mem rlo hlo0 hσ]; exact hlo0.ne'
    rw [hnorm_eq hxnorm, hnorm_eq hlonorm]
    refine Summable.tsum_le_tsum (fun a => ?_)
      (hsummable _ hxnorm) (hsummable _ hlonorm)
    have hmulx : radialMap K x σ * mixedEmbedding K (a : K)
        = radialMap K x (σ * mixedEmbedding K (a : K)) := by
      rw [radialMap, radialMap, smul_mul_assoc]
    have hmullo : radialMap K rlo σ * mixedEmbedding K (a : K)
        = radialMap K rlo (σ * mixedEmbedding K (a : K)) := by
      rw [radialMap, radialMap, smul_mul_assoc]
    rw [hmulx, hmullo, mixedGaussian_eq_exp_quadForm, mixedGaussian_eq_exp_quadForm,
      mixedQuadForm_radialMap x hx0, mixedQuadForm_radialMap rlo hlo0]
    refine Real.exp_le_exp.mpr ?_
    set Q : ℝ := mixedQuadForm K (σ * mixedEmbedding K (a : K)) with hQ
    have hQ0 : 0 ≤ Q := by
      rw [hQ, mixedQuadForm]
      exact Finset.sum_nonneg (fun w _ => by positivity)
    have hexp : (0 : ℝ) ≤ 2 * (finrank ℚ K : ℝ)⁻¹ := by positivity
    have hrpow : rlo ^ (2 * (finrank ℚ K : ℝ)⁻¹) ≤ x ^ (2 * (finrank ℚ K : ℝ)⁻¹) :=
      Real.rpow_le_rpow hlo0.le hx hexp
    have hπ := Real.pi_pos
    nlinarith [mul_nonneg (mul_nonneg hπ.le (sub_nonneg.mpr hrpow)) hQ0]
  -- Assemble the four hypotheses of `continuousAt_of_dominated`.
  have hmeas : ∀ x ∈ Set.Ioi rlo,
      AEStronglyMeasurable (fun σ => Theta.mixedThetaKernel K I (radialMap K x σ)) μ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hlo0 hx
    exact (integrableOn_mixedThetaKernel_radialMap (K := K) I x hx0).aestronglyMeasurable
  have hF_meas : ∀ᶠ x in nhds r₀,
      AEStronglyMeasurable (fun σ => Theta.mixedThetaKernel K I (radialMap K x σ)) μ :=
    Filter.eventually_of_mem (Ioi_mem_nhds hlt) hmeas
  have hbound : ∀ᶠ x in nhds r₀, ∀ᵐ σ ∂μ,
      ‖Theta.mixedThetaKernel K I (radialMap K x σ)‖
        ≤ ‖Theta.mixedThetaKernel K I (radialMap K rlo σ)‖ := by
    refine Filter.eventually_of_mem (Ioi_mem_nhds hlt) (fun x hx => ?_)
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_normEqOneSurface).mpr ?_
    exact Filter.Eventually.of_forall (fun σ hσ => hdom x (le_of_lt hx) σ hσ)
  have hcont : ∀ᵐ σ ∂μ,
      ContinuousAt (fun x => Theta.mixedThetaKernel K I (radialMap K x σ)) r₀ := by
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_normEqOneSurface).mpr ?_
    refine Filter.Eventually.of_forall (fun σ hσ => ?_)
    have hr₀norm : mixedEmbedding.norm (radialMap K r₀ σ) ≠ 0 := by
      rw [norm_radialMap_of_mem r₀ hr₀0 hσ]; exact hr₀0.ne'
    have hUopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
      isOpen_ne.preimage (mixedEmbedding.continuous_norm K)
    have houter : ContinuousAt (Theta.mixedThetaKernel K I) (radialMap K r₀ σ) :=
      (Theta.continuousOn_mixedThetaKernel K I).continuousAt (hUopen.mem_nhds hr₀norm)
    have hinner : ContinuousAt (fun x : ℝ => radialMap K x σ) r₀ := by
      have hc : Continuous (fun x : ℝ => radialMap K x σ) :=
        continuous_radialMap_uncurry.comp (Continuous.prodMk continuous_id continuous_const)
      exact hc.continuousAt
    exact houter.comp_of_eq hinner rfl
  have hrw : orbitThetaFrac K I
      = fun x => ∫ σ, Theta.mixedThetaKernel K I (radialMap K x σ) ∂μ := by
    funext x; rw [orbitThetaFrac, hμ]
  rw [hrw]
  exact continuousAt_of_dominated hF_meas hbound hbound_int hcont

/-- **Gaussian tail of the orbit-integrated theta** (the analytic crux): there
are `c, α > 0` with `orbitTheta K 𝔞 r =O[atTop] e^{-c r^α}`. After the radial
blow-up `radialMap K r σ = r^{1/d} • σ`, the Minkowski Gaussian summands of
`idealThetaKernel` scale as `exp(-π r^{2/d} · Q(σ·a))`, so the whole kernel — and
its integral over the finite-measure compact surface slice — decays like a
Gaussian with `α = 2/[K:ℚ]`. the standard treatment. -/
theorem orbitTheta_isBigO_exp (𝔞 : Ideal (𝓞 K)) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      (fun r : ℝ => orbitTheta K 𝔞 r) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) := by
  obtain ⟨c, α, B, hc, hα, hB, hbound⟩ :=
    norm_idealThetaKernel_radialMap_isBigO (K := K) 𝔞
  refine ⟨c, α, hc, hα, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨(surfaceMeasure K (normEqOneSurface K)).toReal * B, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  have hpos : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  -- The orbit kernel is integrable on the surface slice (via the fractional kernel).
  have hint : IntegrableOn
      (fun σ => Theta.idealThetaKernel K 𝔞 (radialMap K r σ))
      (normEqOneSurface K) (surfaceMeasure K) := by
    have h := integrableOn_mixedThetaKernel_radialMap (K := K)
      (𝔞 : FractionalIdeal (𝓞 K)⁰ K) r hpos
    simpa only [← Theta.idealThetaKernel_eq_mixed] using h
  -- The constant `B · exp(-c r^α)` is integrable on the finite-measure slice.
  have hgint : IntegrableOn (fun _ : mixedSpace K => B * Real.exp (-c * r ^ α))
      (normEqOneSurface K) (surfaceMeasure K) :=
    integrableOn_const (measure_normEqOneSurface_lt_top (K := K)).ne
  -- `‖∫‖ ≤ ∫ ‖·‖ ≤ ∫ const = μ(S) · B · exp(-c r^α)`.
  have hnorm_int :
      ∫ σ in normEqOneSurface K,
          ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖ ∂(surfaceMeasure K)
        ≤ ∫ _σ in normEqOneSurface K, B * Real.exp (-c * r ^ α) ∂(surfaceMeasure K) :=
    setIntegral_mono_on (f := fun σ => ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖)
      (g := fun _ => B * Real.exp (-c * r ^ α)) hint.norm hgint
      measurableSet_normEqOneSurface (fun σ hσ => hbound r hr σ hσ)
  have hge : (0 : ℝ) ≤ ‖(fun r : ℝ => Real.exp (-c * r ^ α)) r‖ := norm_nonneg _
  calc ‖orbitTheta K 𝔞 r‖
      = ‖∫ σ in normEqOneSurface K,
            Theta.idealThetaKernel K 𝔞 (radialMap K r σ) ∂(surfaceMeasure K)‖ := by
        rw [orbitTheta]
    _ ≤ ∫ σ in normEqOneSurface K,
            ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖ ∂(surfaceMeasure K) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _σ in normEqOneSurface K, B * Real.exp (-c * r ^ α) ∂(surfaceMeasure K) :=
        hnorm_int
    _ = (surfaceMeasure K (normEqOneSurface K)).toReal * (B * Real.exp (-c * r ^ α)) := by
        rw [setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def]
    _ = (surfaceMeasure K (normEqOneSurface K)).toReal * B
          * ‖(fun r : ℝ => Real.exp (-c * r ^ α)) r‖ := by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; ring

/-- **Uniform lower bound on the absolute norm of nonzero ideal elements.**
For a nonzero fractional ideal `I` there is `m > 0` with
`m ≤ N(σ a) = |Algebra.norm ℚ a|` for *every* nonzero `a ∈ I`.  This is the
lattice analogue of "a nonzero algebraic integer has `|N| ≥ 1`": writing the
fractional ideal as `δ⁻¹ · (integral ideal)` (`IsFractional`, witness
`δ ∈ (𝓞 K)⁰`), `δ·a` is a nonzero algebraic integer, so `|N(δ a)| ≥ 1` and
`|N a| ≥ 1/|N δ| =: m`.  the standard treatment (the discrete-lattice positivity
underlying the spectral gap). -/
theorem exists_mixedEmbedding_norm_lower_bound (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ a : K, a ∈ (I : Submodule (𝓞 K) K) → a ≠ 0 →
      m ≤ mixedEmbedding.norm (mixedEmbedding K a) := by
  classical
  -- A nonzero algebraic integer has `mixedEmbedding.norm ≥ 1`.
  have hint_ge : ∀ c : 𝓞 K, c ≠ 0 →
      (1 : ℝ) ≤ mixedEmbedding.norm (mixedEmbedding K ((c : 𝓞 K) : K)) := by
    intro c hc
    rw [mixedEmbedding.norm_eq_norm, ← Algebra.coe_norm_int]
    have hz : Algebra.norm ℤ c ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc
    have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ c| := Int.one_le_abs hz
    push_cast
    rw [← Int.cast_abs]
    exact_mod_cast h1
  -- The denominator witness `δ ∈ (𝓞 K)⁰`.
  obtain ⟨δ, hδS, hint⟩ := I.isFractional
  have hδ0 : δ ≠ 0 := nonZeroDivisors.ne_zero hδS
  set D : ℝ := mixedEmbedding.norm (mixedEmbedding K (algebraMap (𝓞 K) K δ)) with hD
  have hDpos : 0 < D := by
    rw [hD, show algebraMap (𝓞 K) K δ = ((δ : 𝓞 K) : K) from
      (RingOfIntegers.coe_eq_algebraMap δ).symm]
    exact lt_of_lt_of_le one_pos (hint_ge δ hδ0)
  refine ⟨D⁻¹, inv_pos.mpr hDpos, ?_⟩
  intro a ha ha0
  obtain ⟨c, hc⟩ := hint a ha
  -- `hc : algebraMap (𝓞 K) K c = δ • a = algebraMap δ * a`.
  have hcK : algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K δ * a := by
    rw [hc, Algebra.smul_def]
  have hc0 : c ≠ 0 := by
    intro h
    apply ha0
    have hδK : algebraMap (𝓞 K) K δ ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hδ0
    have : algebraMap (𝓞 K) K δ * a = 0 := by rw [← hcK, h, map_zero]
    exact (mul_eq_zero.mp this).resolve_left hδK
  -- Split the norm multiplicatively.
  have hsplit : mixedEmbedding.norm (mixedEmbedding K (algebraMap (𝓞 K) K c))
      = D * mixedEmbedding.norm (mixedEmbedding K a) := by
    rw [hcK, map_mul (mixedEmbedding K), map_mul]
  have hge1 : (1 : ℝ) ≤ mixedEmbedding.norm (mixedEmbedding K (algebraMap (𝓞 K) K c)) := by
    rw [show algebraMap (𝓞 K) K c = ((c : 𝓞 K) : K) from
      (RingOfIntegers.coe_eq_algebraMap c).symm]
    exact hint_ge c hc0
  rw [hsplit] at hge1
  -- From `1 ≤ D * X` and `D > 0` conclude `D⁻¹ ≤ X`.
  set X : ℝ := mixedEmbedding.norm (mixedEmbedding K a) with hX
  calc D⁻¹ = D⁻¹ * 1 := (mul_one _).symm
    _ ≤ D⁻¹ * (D * X) :=
        mul_le_mul_of_nonneg_left hge1 (inv_nonneg.mpr hDpos.le)
    _ = X := by field_simp

/-- **Uniform spectral gap of the fractional-ideal Gaussian over the norm-1
surface.**  There is `c₀ > 0` so that every *nonzero* lattice term
`mixedGaussian K (σ · σ(a))` along the norm-1 surface is `≤ e^{-π c₀}`.
Mechanism (the standard treatment): `mixedGaussian K (σ·σ(a)) = exp(-π Q_σ(a))` with
`Q_σ(a) = ∑_w mult w · normAtPlace w (σ·σ(a))²`.  The weighted AM-GM inequality
(`Real.geom_mean_le_arith_mean`) gives
`Q_σ(a) ≥ d · (∏_w normAtPlace w (σ·σ(a))^{mult w})^{2/d} = d · N(σ·σ(a))^{2/d}`,
and `N(σ·σ(a)) = N(σ)·N(σ(a)) = N(σ(a)) ≥ m` on the surface (`N σ = 1`) where
`m > 0` is the uniform lower bound `exists_mixedEmbedding_norm_lower_bound`.  So
`c₀ = d · (m²)^{1/d}` works, with `d = [K:ℚ]`. -/
theorem mixedGaussian_surface_gap (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ σ ∈ normEqOneSurface K,
        ∀ a : K, a ∈ (I : Submodule (𝓞 K) K) → a ≠ 0 →
          Theta.mixedGaussian K (σ * mixedEmbedding K a) ≤ Real.exp (-Real.pi * c₀) := by
  classical
  obtain ⟨m, hm0, hm⟩ := exists_mixedEmbedding_norm_lower_bound I hI
  set d : ℝ := (finrank ℚ K : ℝ) with hd
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  refine ⟨d * (m ^ 2) ^ (d⁻¹),
    mul_pos hd0 (Real.rpow_pos_of_pos (pow_pos hm0 2) (d⁻¹)), ?_⟩
  intro σ hσ a ha ha0
  set x : mixedSpace K := σ * mixedEmbedding K a with hx
  set Q : ℝ := ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w x ^ 2 with hQdef
  -- `N x = N σ · N (σ a) = N (σ a)` on the surface.
  have hnormσ : mixedEmbedding.norm σ = 1 := (mem_normEqOneSurface.mp hσ).2
  have hNx : mixedEmbedding.norm x = mixedEmbedding.norm (mixedEmbedding K a) := by
    rw [hx, map_mul, hnormσ, one_mul]
  have hNlb : m ≤ mixedEmbedding.norm x := by rw [hNx]; exact hm a ha ha0
  -- The sum of the weights is `d = [K:ℚ]`.
  have hsumw : ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) = d := by
    rw [hd, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  -- Weighted AM-GM on the squared per-place norms.
  have hAMGM := Real.geom_mean_le_arith_mean Finset.univ
    (fun w : InfinitePlace K => (InfinitePlace.mult w : ℝ))
    (fun w : InfinitePlace K => normAtPlace w x ^ 2)
    (fun w _ => by positivity)
    (by rw [hsumw]; exact hd0)
    (fun w _ => by positivity)
  -- The geometric-mean product is `(N x)²`.
  have hprod : (∏ w : InfinitePlace K,
      (normAtPlace w x ^ 2) ^ ((InfinitePlace.mult w : ℝ)))
      = (mixedEmbedding.norm x) ^ 2 := by
    rw [mixedEmbedding.norm_apply, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [show ((InfinitePlace.mult w : ℝ)) = ((InfinitePlace.mult w : ℕ) : ℝ) from rfl,
      Real.rpow_natCast, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hsumw, hprod] at hAMGM
  -- `hAMGM : ((N x)²)^{1/d} ≤ Q / d`.  Bound the base below by `m²`.
  have hmono : (m ^ 2) ^ (d⁻¹) ≤ ((mixedEmbedding.norm x) ^ 2) ^ (d⁻¹) :=
    Real.rpow_le_rpow (by positivity)
      (pow_le_pow_left₀ hm0.le hNlb 2) (inv_nonneg.mpr hd0.le)
  have hge : (m ^ 2) ^ (d⁻¹) ≤ Q / d := le_trans hmono hAMGM
  have hQge : d * (m ^ 2) ^ (d⁻¹) ≤ Q := by
    rw [mul_comm]
    exact (le_div_iff₀ hd0).mp hge
  -- Conclude via monotonicity of `exp`.
  have hgauss : Theta.mixedGaussian K x = Real.exp (-Real.pi * Q) := by
    simp only [Theta.mixedGaussian, hQdef]
  rw [hgauss]
  refine Real.exp_le_exp.mpr ?_
  have hπ := Real.pi_pos
  nlinarith [hQge, hπ]

variable (K) in
/-- **Continuity of the orbit-integrated radial theta** `r ↦ orbitTheta K 𝔞 r`
**on the open ray `(0, ∞)`**.

The statement is `ContinuousOn` over `Set.Ioi 0`, NOT global continuity: for
`σ ∈ normEqOneSurface K` (`mixedEmbedding.norm σ = 1`) the radial point
`radialMap K r σ` has `mixedEmbedding.norm = r` (`norm_radialMap_of_mem`), so it
lands in the Gaussian-summable nonzero-norm locus
`{x | mixedEmbedding.norm x ≠ 0}` — on which `Theta.idealThetaKernel` is
continuous (`Theta.continuousOn_idealThetaKernel`) — **exactly when `r > 0`**.
At `r ≤ 0` the integrand hits the zero-norm locus where the theta kernel is the
junk value `0`/non-summable, so `orbitTheta` is not continuous there.

The proof is the dominated-continuity argument for parametric integrals
(`continuousAt_of_dominated`) using the restricted (`Ioi 0`) kernel continuity
and the uniform Gaussian bound over the surface. the standard treatment. -/
theorem continuousOn_orbitTheta (𝔞 : Ideal (𝓞 K)) :
    ContinuousOn (orbitTheta K 𝔞) (Set.Ioi 0) := by
  -- The zero ideal: the kernel sums over the empty index set, so `orbitTheta ≡ 0`.
  by_cases h𝔞 : 𝔞 = ⊥
  · have hzero : orbitTheta K 𝔞 = fun _ : ℝ => (0 : ℂ) := by
      funext r
      rw [orbitTheta]
      have hker : ∀ σ : mixedSpace K,
          Theta.idealThetaKernel K 𝔞 (radialMap K r σ) = 0 := by
        intro σ
        have hempty : IsEmpty {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} := by
          refine ⟨?_⟩
          rintro ⟨a, ha, hne⟩
          rw [h𝔞, Ideal.mem_bot] at ha
          exact hne ha
        rw [Theta.idealThetaKernel, tsum_empty]
      simp only [hker, integral_zero]
    rw [hzero]
    exact continuousOn_const
  -- Nonzero ideal: dominated continuity of the parametric integral over the
  -- (finite-measure) norm-1 surface slice.
  set μ : Measure (mixedSpace K) := (surfaceMeasure K).restrict (normEqOneSurface K)
    with hμ
  -- `‖kernel x‖` equals the real lattice Gaussian sum at any nonzero-norm `x`.
  have hnorm_eq : ∀ {x : mixedSpace K}, mixedEmbedding.norm x ≠ 0 →
      ‖Theta.idealThetaKernel K 𝔞 x‖
        = ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
            Theta.mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K)) := by
    intro x _hx
    rw [Theta.idealThetaKernel, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg (fun a => mixedGaussian_nonneg _))]
  refine continuousOn_of_forall_continuousAt (fun r₀ hr₀ => ?_)
  have hr₀0 : (0 : ℝ) < r₀ := hr₀
  set rlo : ℝ := r₀ / 2 with hrlo
  have hlo0 : (0 : ℝ) < rlo := by rw [hrlo]; linarith
  have hlt : rlo < r₀ := by rw [hrlo]; linarith
  -- The dominating function `g σ = ‖kernel (radialMap K rlo σ)‖`, integrable on `S`.
  have hint_lo : IntegrableOn
      (fun σ => Theta.idealThetaKernel K 𝔞 (radialMap K rlo σ))
      (normEqOneSurface K) (surfaceMeasure K) := by
    have h := integrableOn_mixedThetaKernel_radialMap (K := K)
      (𝔞 : FractionalIdeal (𝓞 K)⁰ K) rlo hlo0
    simpa only [← Theta.idealThetaKernel_eq_mixed] using h
  have hbound_int :
      Integrable (fun σ => ‖Theta.idealThetaKernel K 𝔞 (radialMap K rlo σ)‖) μ :=
    hint_lo.norm
  -- Per-radius monotone domination for `r ≥ rlo` over the surface.
  have hdom : ∀ x : ℝ, rlo ≤ x → ∀ σ ∈ normEqOneSurface K,
      ‖Theta.idealThetaKernel K 𝔞 (radialMap K x σ)‖
        ≤ ‖Theta.idealThetaKernel K 𝔞 (radialMap K rlo σ)‖ := by
    intro x hx σ hσ
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hlo0 hx
    have hxnorm : mixedEmbedding.norm (radialMap K x σ) ≠ 0 := by
      rw [norm_radialMap_of_mem x hx0 hσ]; exact hx0.ne'
    have hlonorm : mixedEmbedding.norm (radialMap K rlo σ) ≠ 0 := by
      rw [norm_radialMap_of_mem rlo hlo0 hσ]; exact hlo0.ne'
    rw [hnorm_eq hxnorm, hnorm_eq hlonorm]
    refine Summable.tsum_le_tsum (fun a => ?_)
      (summable_mixedGaussian_idealKernel 𝔞 h𝔞 hxnorm)
      (summable_mixedGaussian_idealKernel 𝔞 h𝔞 hlonorm)
    have hmulx : radialMap K x σ * mixedEmbedding K ((a : 𝓞 K) : K)
        = radialMap K x (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by
      rw [radialMap, radialMap, smul_mul_assoc]
    have hmullo : radialMap K rlo σ * mixedEmbedding K ((a : 𝓞 K) : K)
        = radialMap K rlo (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by
      rw [radialMap, radialMap, smul_mul_assoc]
    rw [hmulx, hmullo, mixedGaussian_eq_exp_quadForm, mixedGaussian_eq_exp_quadForm,
      mixedQuadForm_radialMap x hx0, mixedQuadForm_radialMap rlo hlo0]
    refine Real.exp_le_exp.mpr ?_
    set Q : ℝ := mixedQuadForm K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) with hQ
    have hQ0 : 0 ≤ Q := by
      rw [hQ, mixedQuadForm]
      exact Finset.sum_nonneg (fun w _ => by positivity)
    have hexp : (0 : ℝ) ≤ 2 * (finrank ℚ K : ℝ)⁻¹ := by positivity
    have hrpow : rlo ^ (2 * (finrank ℚ K : ℝ)⁻¹) ≤ x ^ (2 * (finrank ℚ K : ℝ)⁻¹) :=
      Real.rpow_le_rpow hlo0.le hx hexp
    have hπ := Real.pi_pos
    nlinarith [mul_nonneg (mul_nonneg hπ.le (sub_nonneg.mpr hrpow)) hQ0]
  -- Assemble the four hypotheses of `continuousAt_of_dominated`.
  have hmeas : ∀ x ∈ Set.Ioi rlo,
      AEStronglyMeasurable (fun σ => Theta.idealThetaKernel K 𝔞 (radialMap K x σ)) μ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hlo0 hx
    have h := integrableOn_mixedThetaKernel_radialMap (K := K)
      (𝔞 : FractionalIdeal (𝓞 K)⁰ K) x hx0
    have hI : IntegrableOn
        (fun σ => Theta.idealThetaKernel K 𝔞 (radialMap K x σ))
        (normEqOneSurface K) (surfaceMeasure K) := by
      simpa only [← Theta.idealThetaKernel_eq_mixed] using h
    exact hI.aestronglyMeasurable
  have hF_meas : ∀ᶠ x in nhds r₀,
      AEStronglyMeasurable (fun σ => Theta.idealThetaKernel K 𝔞 (radialMap K x σ)) μ :=
    Filter.eventually_of_mem (Ioi_mem_nhds hlt) hmeas
  have hbound : ∀ᶠ x in nhds r₀, ∀ᵐ σ ∂μ,
      ‖Theta.idealThetaKernel K 𝔞 (radialMap K x σ)‖
        ≤ ‖Theta.idealThetaKernel K 𝔞 (radialMap K rlo σ)‖ := by
    refine Filter.eventually_of_mem (Ioi_mem_nhds hlt) (fun x hx => ?_)
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_normEqOneSurface).mpr ?_
    exact Filter.Eventually.of_forall (fun σ hσ => hdom x (le_of_lt hx) σ hσ)
  have hcont : ∀ᵐ σ ∂μ,
      ContinuousAt (fun x => Theta.idealThetaKernel K 𝔞 (radialMap K x σ)) r₀ := by
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_normEqOneSurface).mpr ?_
    refine Filter.Eventually.of_forall (fun σ hσ => ?_)
    have hr₀norm : mixedEmbedding.norm (radialMap K r₀ σ) ≠ 0 := by
      rw [norm_radialMap_of_mem r₀ hr₀0 hσ]; exact hr₀0.ne'
    have hUopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
      isOpen_ne.preimage (mixedEmbedding.continuous_norm K)
    have houter : ContinuousAt (Theta.idealThetaKernel K 𝔞) (radialMap K r₀ σ) :=
      (Theta.continuousOn_idealThetaKernel K 𝔞).continuousAt (hUopen.mem_nhds hr₀norm)
    have hinner : ContinuousAt (fun x : ℝ => radialMap K x σ) r₀ := by
      have hc : Continuous (fun x : ℝ => radialMap K x σ) :=
        continuous_radialMap_uncurry.comp (Continuous.prodMk continuous_id continuous_const)
      exact hc.continuousAt
    exact houter.comp_of_eq hinner rfl
  have hrw : orbitTheta K 𝔞
      = fun x => ∫ σ, Theta.idealThetaKernel K 𝔞 (radialMap K x σ) ∂μ := by
    funext x; rw [orbitTheta, hμ]
  rw [hrw]
  exact continuousAt_of_dominated hF_meas hbound hbound_int hcont

/-- **Radial scaling identity for the Minkowski Gaussian.** With
`d = Module.finrank ℚ K`, scaling `σ` radially by `r ≥ 0` along the cone ray
(`radialMap K r σ = r^{1/d} • σ`) turns the multiplicative Gaussian into its
`r^{2/d}`-power: the Minkowski quadratic form `Q(x) = ∑_w mult w · normAtPlace w x ^ 2`
scales as `Q((r^{1/d}•σ)·y) = r^{2/d} · Q(σ·y)` (via `normAtPlace_smul` and
`r^{1/d} ≥ 0`), so `mixedGaussian = exp(-π Q)` gives the displayed power law
(`Real.exp_mul`). Used to reduce the cone theta integral to a one-dimensional
radial Mellin (the standard treatment). -/
theorem mixedGaussian_radialMap (r : ℝ) (hr : 0 ≤ r) (σ y : mixedSpace K) :
    Theta.mixedGaussian K (radialMap K r σ * y)
      = (Theta.mixedGaussian K (σ * y)) ^ (r ^ (2 / (finrank ℚ K : ℝ))) := by
  set d : ℝ := (finrank ℚ K : ℝ) with hd
  have hc : (0 : ℝ) ≤ r ^ (d⁻¹) := Real.rpow_nonneg hr _
  -- place-wise scaling of the quadratic-form summand by `(r^{1/d})²`
  have hstep : ∀ w : InfinitePlace K,
      (mult w : ℝ) * normAtPlace w (radialMap K r σ * y) ^ 2
        = (r ^ d⁻¹) ^ 2 * ((mult w : ℝ) * normAtPlace w (σ * y) ^ 2) := by
    intro w
    rw [radialMap, smul_mul_assoc, normAtPlace_smul, abs_of_nonneg hc, mul_pow]
    ring
  rw [Theta.mixedGaussian, Theta.mixedGaussian,
    Finset.sum_congr rfl (fun w _ => hstep w), ← Finset.mul_sum]
  rw [show -Real.pi * ((r ^ d⁻¹) ^ 2 *
        ∑ w : InfinitePlace K, (mult w : ℝ) * normAtPlace w (σ * y) ^ 2)
      = (-Real.pi *
        ∑ w : InfinitePlace K, (mult w : ℝ) * normAtPlace w (σ * y) ^ 2)
        * (r ^ d⁻¹) ^ 2 by ring]
  rw [Real.exp_mul]
  congr 1
  -- `(r^{1/d})² = r^{2/d}`
  rw [← Real.rpow_natCast (r ^ d⁻¹) 2, ← Real.rpow_mul hr]
  congr 1
  push_cast
  rw [div_eq_mul_inv]
  ring

/-- **Uniform Gaussian tail of the fractional theta kernel along the radial ray**
(the genuine analytic crux). There are `c, α, B > 0` so that for every `r ≥ 1`
and every point `σ` of the compact norm-1 surface fundamental domain
`normEqOneSurface K`, the radially blown-up kernel obeys
`‖Θ_mix(I, radialMap K r σ)‖ ≤ B · e^{-c r^α}`. Since `radialMap K r σ = r^{1/d} • σ`
scales each Minkowski coordinate by `r^{1/d}`, the quadratic exponent of every
Gaussian summand of `mixedThetaKernel` scales as `r^{2/d}`; bounding the sum by
the smallest-nonzero-`I`-lattice-point Gaussian over the compact slice gives a
uniform Gaussian bound with `α = 2/[K:ℚ]`. This uniform-in-`σ` bound is what the
orbit integral `orbitThetaFrac_isBigO_exp` then integrates over the
finite-measure surface. the standard treatment. -/
theorem mixedThetaKernel_radialMap_isBigO_uniform (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ c α B : ℝ, 0 < c ∧ 0 < α ∧ 0 ≤ B ∧
      ∀ r : ℝ, 1 ≤ r → ∀ σ ∈ normEqOneSurface K,
        ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖
          ≤ B * Real.exp (-c * r ^ α) := by
  classical
  by_cases hI : I = 0
  · -- Empty index set: the kernel is the empty `tsum`, hence `0`.
    refine ⟨1, 1, 0, one_pos, one_pos, le_refl 0, ?_⟩
    intro r _hr σ _hσ
    haveI hempty : IsEmpty {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} := by
      subst hI
      refine ⟨fun a => ?_⟩
      obtain ⟨ha, ha0⟩ := a.2
      exact ha0 (by simpa using ha)
    have hzero : Theta.mixedThetaKernel K I (radialMap K r σ) = 0 := by
      rw [Theta.mixedThetaKernel,
        tsum_eq_sum (s := ∅) (fun b _ => isEmptyElim b), Finset.sum_empty]
    rw [hzero]; simp
  · -- `I ≠ 0`: combine the scaling identity, surface gap, and uniform majorant.
    obtain ⟨c₀, hc₀, hgap⟩ := mixedGaussian_surface_gap I hI
    obtain ⟨S, hS0, hSummaj⟩ := mixedGaussian_surface_majorant I hI
    have hd0 : (0:ℝ) < (finrank ℚ K : ℝ) := by
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
    refine ⟨Real.pi * c₀, 2 / (finrank ℚ K : ℝ), S * Real.exp (Real.pi * c₀),
      mul_pos Real.pi_pos hc₀, div_pos (by norm_num) hd0,
      mul_nonneg hS0 (Real.exp_pos _).le, ?_⟩
    intro r hr σ hσ
    have hr0 : (0:ℝ) ≤ r := le_trans zero_le_one hr
    set t : ℝ := r ^ (2 / (finrank ℚ K : ℝ)) with htdef
    have ht1 : 1 ≤ t := by
      have h := Real.rpow_le_rpow_of_exponent_le hr
        (show (0:ℝ) ≤ 2 / (finrank ℚ K : ℝ) by positivity)
      rwa [Real.rpow_zero] at h
    obtain ⟨hsum, hle⟩ := hSummaj σ hσ
    set g : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} → ℝ :=
      fun a => Theta.mixedGaussian K (σ * mixedEmbedding K (a : K)) with hgdef
    -- Per-term gap bound and positivity of the Gaussian.
    have hpos : ∀ a, 0 < g a := fun a => Real.exp_pos _
    have hgapa : ∀ a, g a ≤ Real.exp (-Real.pi * c₀) :=
      fun a => hgap σ hσ a.1 a.2.1 a.2.2
    have hElt1 : Real.exp (-Real.pi * c₀) < 1 := by
      rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_lt_exp.mpr (by nlinarith [mul_pos Real.pi_pos hc₀])
    -- Scaling rewrite of the kernel summands (`mixedGaussian_radialMap`).
    have hker : Theta.mixedThetaKernel K I (radialMap K r σ)
        = ∑' a, ((g a ^ t : ℝ) : ℂ) := by
      rw [Theta.mixedThetaKernel]
      refine tsum_congr (fun a => ?_)
      rw [mixedGaussian_radialMap r hr0 σ (mixedEmbedding K (a : K)), ← htdef]
    -- Comparison `g^t ≤ g` (so the powered sum is summable).
    have hcmp : ∀ a, g a ^ t ≤ g a := by
      intro a
      have h1 : g a ≤ 1 := le_of_lt (lt_of_le_of_lt (hgapa a) hElt1)
      calc g a ^ t ≤ g a ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge (hpos a) h1 ht1
        _ = g a := Real.rpow_one _
    have hsumt : Summable (fun a => g a ^ t) :=
      Summable.of_nonneg_of_le (fun a => Real.rpow_nonneg (hpos a).le t) hcmp hsum
    -- Per-term majorant bound `g^t ≤ E^{t-1} · g` with `E = e^{-π c₀}`.
    have hterm : ∀ a, g a ^ t ≤ Real.exp (-Real.pi * c₀) ^ (t - 1) * g a := by
      intro a
      have e1 : g a ^ (t - 1) * g a = g a ^ t := by
        have h := Real.rpow_add (hpos a) (t - 1) 1
        rw [Real.rpow_one] at h
        rw [← h]; congr 1; ring
      have hbase : g a ^ (t - 1) ≤ Real.exp (-Real.pi * c₀) ^ (t - 1) :=
        Real.rpow_le_rpow (hpos a).le (hgapa a) (by linarith [ht1])
      calc g a ^ t = g a ^ (t - 1) * g a := e1.symm
        _ ≤ Real.exp (-Real.pi * c₀) ^ (t - 1) * g a :=
            mul_le_mul_of_nonneg_right hbase (hpos a).le
    -- Norm of each (real, nonnegative) complex summand.
    have hnormeq : ∀ a, ‖((g a ^ t : ℝ) : ℂ)‖ = g a ^ t := by
      intro a
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hpos a).le t)]
    have hsumnorm : Summable (fun a => ‖((g a ^ t : ℝ) : ℂ)‖) :=
      hsumt.congr (fun a => (hnormeq a).symm)
    -- Collapse `E^{t-1}` into a Gaussian factor.
    have hEpow : Real.exp (-Real.pi * c₀) ^ (t - 1)
        = Real.exp ((-Real.pi * c₀) * (t - 1)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    have hfinal : Real.exp (-Real.pi * c₀) ^ (t - 1) * S
        = (S * Real.exp (Real.pi * c₀)) * Real.exp (-(Real.pi * c₀) * t) := by
      rw [hEpow, (by ring : (-Real.pi * c₀) * (t - 1)
            = Real.pi * c₀ + -(Real.pi * c₀) * t), Real.exp_add]
      ring
    calc ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖
        = ‖∑' a, ((g a ^ t : ℝ) : ℂ)‖ := by rw [hker]
      _ ≤ ∑' a, ‖((g a ^ t : ℝ) : ℂ)‖ := norm_tsum_le_tsum_norm hsumnorm
      _ = ∑' a, g a ^ t := tsum_congr hnormeq
      _ ≤ ∑' a, Real.exp (-Real.pi * c₀) ^ (t - 1) * g a :=
            hsumt.tsum_le_tsum hterm (hsum.mul_left _)
      _ = Real.exp (-Real.pi * c₀) ^ (t - 1) * ∑' a, g a := tsum_mul_left
      _ ≤ Real.exp (-Real.pi * c₀) ^ (t - 1) * S :=
            mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (Real.exp_pos _).le _)
      _ = (S * Real.exp (Real.pi * c₀)) * Real.exp (-(Real.pi * c₀) * t) := hfinal

/-- **Gaussian tail of the fractional orbit-integrated theta** (the dual case of
`orbitTheta_isBigO_exp`): `orbitThetaFrac K I r =O[atTop] e^{-c r^α}` for the
fractional ideal `I` (applied below to the dual `Theta.dualIdeal K 𝔞`). Same
Gaussian mechanism via `mixedThetaKernel`. The proof integrates the uniform
Gaussian bound `mixedThetaKernel_radialMap_isBigO_uniform` over the finite-measure
compact surface slice: `‖∫_S Θ_mix‖ ≤ ∫_S ‖Θ_mix‖ ≤ μ_S(S)·B·e^{-c r^α}`, using
`integrableOn_mixedThetaKernel_radialMap` and `measure_normEqOneSurface_lt_top`.
the standard treatment. -/
theorem orbitThetaFrac_isBigO_exp (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      (fun r : ℝ => orbitThetaFrac K I r) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) := by
  obtain ⟨c, α, B, hc, hα, hB, hbound⟩ :=
    mixedThetaKernel_radialMap_isBigO_uniform (K := K) I
  refine ⟨c, α, hc, hα, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨B * (surfaceMeasure K (normEqOneSurface K)).toReal, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hfin : surfaceMeasure K (normEqOneSurface K) < ⊤ :=
    measure_normEqOneSurface_lt_top
  -- Integrability of the kernel on the surface slice (sibling lemma).
  have hintker : IntegrableOn
      (fun σ => Theta.mixedThetaKernel K I (radialMap K r σ))
      (normEqOneSurface K) (surfaceMeasure K) :=
    integrableOn_mixedThetaKernel_radialMap I r hr0
  -- `‖∫ Θ‖ ≤ ∫ ‖Θ‖`.
  have hnorm_le : ‖orbitThetaFrac K I r‖
      ≤ ∫ σ in normEqOneSurface K,
          ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ∂(surfaceMeasure K) := by
    rw [orbitThetaFrac]
    exact norm_integral_le_integral_norm _
  -- `∫ ‖Θ‖ ≤ ∫ (B·e^{-c r^α}) = μ_S(S)·B·e^{-c r^α}`.
  have hmono : ∫ σ in normEqOneSurface K,
        ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ∂(surfaceMeasure K)
      ≤ ∫ _σ in normEqOneSurface K, B * Real.exp (-c * r ^ α) ∂(surfaceMeasure K) := by
    refine setIntegral_mono_on hintker.norm ?_ measurableSet_normEqOneSurface ?_
    · exact integrableOn_const hfin.ne
    · intro σ hσ; exact hbound r hr σ hσ
  have hconst : ∫ _σ in normEqOneSurface K, B * Real.exp (-c * r ^ α)
        ∂(surfaceMeasure K)
      = (surfaceMeasure K (normEqOneSurface K)).toReal * (B * Real.exp (-c * r ^ α)) := by
    rw [setIntegral_const]
    simp [MeasureTheory.measureReal_def, smul_eq_mul]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc ‖orbitThetaFrac K I r‖
      ≤ ∫ σ in normEqOneSurface K,
          ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ∂(surfaceMeasure K) := hnorm_le
    _ ≤ (surfaceMeasure K (normEqOneSurface K)).toReal * (B * Real.exp (-c * r ^ α)) :=
        hmono.trans_eq hconst
    _ = B * (surfaceMeasure K (normEqOneSurface K)).toReal * Real.exp (-c * r ^ α) := by
        ring

/-- **Comparison of Gaussian tails.** A faster Gaussian decay dominates a slower
one: if `0 < c ≤ c₁` and `α ≤ α₁` then `e^{-c₁ r^{α₁}} =O[atTop] e^{-c r^α}`
(for `r ≥ 1`, `c r^α ≤ c₁ r^{α₁}`). Used to unify the two decay rates of
`orbitTheta`/`orbitThetaFrac` into a single `(c, α)` pair. -/
theorem exp_isBigO_exp_of_le {c₁ α₁ c α : ℝ} (hcpos : 0 < c) (hcle : c ≤ c₁)
    (hαle : α ≤ α₁) :
    (fun r : ℝ => Real.exp (-c₁ * r ^ α₁)) =O[Filter.atTop]
      (fun r : ℝ => Real.exp (-c * r ^ α)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  have hc1pos : 0 < c₁ := lt_of_lt_of_le hcpos hcle
  have h1 : r ^ α ≤ r ^ α₁ := Real.rpow_le_rpow_of_exponent_le hr hαle
  have hrα : 0 ≤ r ^ α := Real.rpow_nonneg hr0 α
  have hle : c * r ^ α ≤ c₁ * r ^ α₁ := by nlinarith [hrα, hc1pos.le, h1]
  have hexp : Real.exp (-c₁ * r ^ α₁) ≤ Real.exp (-c * r ^ α) :=
    Real.exp_le_exp.mpr (by nlinarith [hle])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _), one_mul]
  exact hexp

/-- **Exponential decay of the completed radial theta**: there are `c, α > 0` with
`F(𝔞, r) − a₀ = orbitTheta K 𝔞 r = O(e^{-c r^α})` as `r → ∞` (the Gaussian tail
of the nonzero lattice points after orbit integration; `α = 2 / [K:ℚ]` from the
radial scaling). The same `c, α` work for the dual. Built from the two crux tail
bounds `orbitTheta_isBigO_exp`/`orbitThetaFrac_isBigO_exp` (unified to a single
`(c, α)` via `exp_isBigO_exp_of_le`), using `radialTheta − V = orbitTheta` and
`radialThetaDual − V = orbitThetaFrac (dualIdeal 𝔞)`. -/
theorem exists_decay_radialTheta (𝔞 : Ideal (𝓞 K)) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      (fun r : ℝ => radialTheta K 𝔞 r - surfaceVolume K) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) ∧
      (fun r : ℝ => radialThetaDual K 𝔞 r - surfaceVolume K) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) := by
  obtain ⟨c₁, α₁, hc₁, hα₁, hf⟩ := orbitTheta_isBigO_exp (K := K) 𝔞
  obtain ⟨c₂, α₂, hc₂, hα₂, hg⟩ := orbitThetaFrac_isBigO_exp (K := K) (Theta.dualIdeal K 𝔞)
  refine ⟨min c₁ c₂, min α₁ α₂, lt_min hc₁ hc₂, lt_min hα₁ hα₂, ?_, ?_⟩
  · have hsimp : (fun r : ℝ => radialTheta K 𝔞 r - surfaceVolume K)
        = (fun r : ℝ => orbitTheta K 𝔞 r) := by
      funext r; simp [radialTheta, add_sub_cancel_right]
    rw [hsimp]
    exact hf.trans
      (exp_isBigO_exp_of_le (lt_min hc₁ hc₂) (min_le_left _ _) (min_le_left _ _))
  · have hsimp : (fun r : ℝ => radialThetaDual K 𝔞 r - surfaceVolume K)
        = (fun r : ℝ => orbitThetaFrac K (Theta.dualIdeal K 𝔞) r) := by
      funext r; simp [radialThetaDual, add_sub_cancel_right]
    rw [hsimp]
    exact hg.trans
      (exp_isBigO_exp_of_le (lt_min hc₁ hc₂) (min_le_right _ _) (min_le_right _ _))

omit [NumberField K] in
/-- **Inversion commutes with real scaling on the mixed space.** For `c : ℝ`
and `x : mixedSpace K`, `(c • x)⁻¹ = c⁻¹ • x⁻¹` (componentwise `mul_inv`, with
`(↑c)⁻¹ = ↑(c⁻¹)` on the complex factor). the standard treatment (the radial scaling
bookkeeping). -/
theorem smul_inv_mixedSpace (c : ℝ) (x : mixedSpace K) :
    (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  ext i <;>
    simp [Pi.smul_apply, Pi.inv_apply, Complex.ofReal_inv,
      Complex.real_smul, smul_eq_mul, mul_comm]

/-- **Radial inversion identity.** For `0 < r`, the radius-`1/r` rescaling of an
inverse point equals the inverse of the radius-`r` rescaling:
`radialMap K (1/r) x⁻¹ = (radialMap K r x)⁻¹`. From
`radialMap K r x = r^{1/d} • x`, `(1/r)^{1/d} = (r^{1/d})⁻¹` (`Real.inv_rpow`) and
`smul_inv_mixedSpace`. the standard treatment. -/
theorem radialMap_inv (r : ℝ) (hr : 0 < r) (x : mixedSpace K) :
    radialMap K (1 / r) x⁻¹ = (radialMap K r x)⁻¹ := by
  simp only [radialMap, one_div, Real.inv_rpow hr.le, smul_inv_mixedSpace]

/-- **Radial projection commutes with inversion.** For `N x ≠ 0`,
`(radialProj K x)⁻¹ = radialProj K x⁻¹`. From `radialProj K x = radialMap K (N x)⁻¹ x`,
the radial inversion identity `radialMap_inv`, and `N x⁻¹ = (N x)⁻¹`
(`DedekindZeta.mixedEmbedding_norm_inv`). the standard treatment. -/
theorem radialProj_inv {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    (radialProj K x)⁻¹ = radialProj K x⁻¹ := by
  have hpos : 0 < mixedEmbedding.norm x :=
    (mixedEmbedding.norm_nonneg x).lt_of_ne (Ne.symm hx)
  have hinvpos : 0 < (mixedEmbedding.norm x)⁻¹ := inv_pos.mpr hpos
  rw [radialProj, radialProj, DedekindZeta.mixedEmbedding_norm_inv,
    ← radialMap_inv (mixedEmbedding.norm x)⁻¹ hinvpos x, one_div]

/-- **Radial projection is unit-equivariant.** `radialProj K (u • x) = u • radialProj K x`,
since the unit action preserves the norm (`Theta.norm_unitSMul`) and real scaling
commutes with the multiplicative unit action (`Algebra.mul_smul_comm`).
the standard treatment. -/
theorem radialProj_unitSMul (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    radialProj K (u • x) = u • radialProj K x := by
  rw [radialProj, radialProj, Theta.norm_unitSMul]
  simp only [radialMap, NumberField.mixedEmbedding.unitSMul_smul]
  exact (Algebra.mul_smul_comm _ _ _).symm

/-- **Radial projection is radial-scale invariant.** For `t > 0`,
`radialProj K (radialMap K t x) = radialProj K x`. From `norm_radialMap`
(`N (radialMap K t x) = t * N x`) and `radialMap_radialMap`, the rescaling
cancels: `(t * N x)⁻¹ * t = (N x)⁻¹`. the standard treatment. -/
theorem radialProj_radialMap {t : ℝ} (ht : 0 < t) (x : mixedSpace K) :
    radialProj K (radialMap K t x) = radialProj K x := by
  rw [radialProj, norm_radialMap t ht x,
    radialMap_radialMap _ t
      (inv_nonneg.mpr (mul_nonneg ht.le (mixedEmbedding.norm_nonneg x))) ht.le,
    radialProj]
  congr 1
  rw [mul_comm ((t * mixedEmbedding.norm x)⁻¹) t, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ ht.ne', one_mul]

variable (K) in
/-- **Inversion is continuous on the nonzero-norm locus.** The mixed-space
inversion `x ↦ x⁻¹` is componentwise (real/complex) inversion, continuous exactly
where every coordinate is nonzero, i.e. where `N x ≠ 0`
(`mixedEmbedding.norm_eq_zero_iff`). the standard treatment. -/
theorem continuousOn_inv_norm_ne_zero :
    ContinuousOn (Inv.inv : mixedSpace K → mixedSpace K)
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  -- On `{N x ≠ 0}` every coordinate is nonzero (`norm_ne_zero_iff` says every
  -- `normAtPlace w x ≠ 0`, and `normAtPlace` is the coordinate's absolute value).
  have hx' : ∀ w, mixedEmbedding.normAtPlace w x ≠ 0 :=
    mixedEmbedding.norm_ne_zero_iff.mp hx
  have hre : ∀ i : {w : InfinitePlace K // IsReal w}, x.1 i ≠ 0 := by
    intro i
    have h := hx' i.1
    rw [mixedEmbedding.normAtPlace_apply_of_isReal i.2] at h
    simpa using h
  have hco : ∀ i : {w : InfinitePlace K // IsComplex w}, x.2 i ≠ 0 := by
    intro i
    have h := hx' i.1
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex i.2] at h
    simpa using h
  -- Componentwise (Pi) inversion is continuous at a point whose coordinates are
  -- all nonzero, by `continuousAt_inv₀` on ℝ / ℂ at each coordinate.
  have h1 : ContinuousAt (fun p : mixedSpace K => (p.1)⁻¹) x := by
    have hpi : ContinuousAt (Inv.inv : ({w : InfinitePlace K // IsReal w} → ℝ) → _) x.1 := by
      rw [continuousAt_pi]
      intro i
      exact (continuousAt_apply i x.1).inv₀ (hre i)
    exact hpi.comp continuousAt_fst
  have h2 : ContinuousAt (fun p : mixedSpace K => (p.2)⁻¹) x := by
    have hpi : ContinuousAt (Inv.inv : ({w : InfinitePlace K // IsComplex w} → ℂ) → _) x.2 := by
      rw [continuousAt_pi]
      intro i
      exact (continuousAt_apply i x.2).inv₀ (hco i)
    exact hpi.comp continuousAt_snd
  -- `Inv.inv` on the product is `p ↦ (p.1⁻¹, p.2⁻¹)`.
  have hprod : ContinuousAt (fun p : mixedSpace K => ((p.1)⁻¹, (p.2)⁻¹)) x := h1.prodMk h2
  exact hprod

/-- **The norm-collar has finite `mixedMulHaar`-measure.** On
`C = cone ∩ {N ∈ (1, e]}` the density `(2/π)^{r₂}·(N x)⁻¹` is bounded by the
constant `(2/π)^{r₂}` (since `N x > 1`), and `C` is bounded (a scaled copy of
`normLeOne K`), so `volume C < ∞` and hence `mixedMulHaar C < ∞`. Extracted from
the proof of `measure_normEqOneSurface_lt_top`. the standard treatment. -/
theorem mixedMulHaar_collar_lt_top :
    (DedekindZeta.mixedMulHaar K)
        (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}) < ⊤ := by
  classical
  set C : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hCdef
  have hCmeas : MeasurableSet C := by
    refine (measurableSet_fundamentalCone K).inter ?_
    exact (mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc
  have hdensity : (DedekindZeta.mixedMulHaar K) C
      = ∫⁻ x in C, ENNReal.ofReal
          ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹) ∂volume :=
    withDensity_apply _ hCmeas
  have hbound : (DedekindZeta.mixedMulHaar K) C
      ≤ ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K) * volume C := by
    rw [hdensity, ← setLIntegral_const C]
    refine setLIntegral_mono measurable_const ?_
    rintro x ⟨-, hxN⟩
    apply ENNReal.ofReal_le_ofReal
    have hxpos : 0 < mixedEmbedding.norm x := lt_trans one_pos hxN.1
    have hinv : (mixedEmbedding.norm x)⁻¹ ≤ 1 := (inv_le_one₀ hxpos).mpr hxN.1.le
    calc (2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹
        ≤ (2 / Real.pi) ^ nrComplexPlaces K * 1 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (2 / Real.pi) ^ nrComplexPlaces K := mul_one _
  refine lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hCbdd : Bornology.IsBounded C := by
    refine ((fundamentalCone.isBounded_normLeOne K).smul₀
      ((Real.exp 1) ^ ((finrank ℚ K : ℝ)⁻¹))).subset ?_
    rintro x ⟨hxcone, hxN⟩
    refine Set.mem_smul_set.mpr ⟨radialMap K (Real.exp 1)⁻¹ x, ?_, ?_⟩
    · rw [fundamentalCone.mem_normLeOne]
      refine ⟨radialMap_mem_cone (Real.exp 1)⁻¹ (inv_pos.mpr hepos) hxcone, ?_⟩
      rw [norm_radialMap (Real.exp 1)⁻¹ (inv_pos.mpr hepos) x]
      calc (Real.exp 1)⁻¹ * mixedEmbedding.norm x
          ≤ (Real.exp 1)⁻¹ * Real.exp 1 :=
            mul_le_mul_of_nonneg_left hxN.2 (inv_pos.mpr hepos).le
        _ = 1 := inv_mul_cancel₀ hepos.ne'
    · show radialMap K (Real.exp 1) (radialMap K (Real.exp 1)⁻¹ x) = x
      rw [radialMap_radialMap (Real.exp 1) (Real.exp 1)⁻¹ hepos.le (inv_pos.mpr hepos).le,
        mul_inv_cancel₀ hepos.ne']
      simp [radialMap]
  exact hCbdd.measure_lt_top

/-- **Positive norm-level sets are `mixedMulHaar`-null.** For every `c > 0` the
fiber `{x | N x = c}` has `mixedMulHaar K`-measure zero. Proof (the standard treatment, radial scaling): `mixedMulHaar` is a `σ`-finite measure
(`volume.withDensity` of an everywhere-finite density), so by
`countable_meas_level_set_pos` only countably many levels `c` can have
`μ {N = c} > 0`. But the radial scaling `radialMap K (a/b)` (measure-preserving,
`lintegral_radialMap_mixedMulHaar`) maps `{N = b}` onto `{N = a}`, hence
`μ {N = a} = μ {N = b}` for all `a, b > 0`; if one positive level had positive
measure then *every* positive level would, contradicting countability (the
interval `Ioo 0 1` of levels is uncountable). -/
theorem mixedMulHaar_norm_eq_eq_zero {c : ℝ} (hc : 0 < c) :
    DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = c} = 0 := by
  classical
  haveI : SigmaFinite (DedekindZeta.mixedMulHaar K) := by
    unfold DedekindZeta.mixedMulHaar
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  have hnormmeas : Measurable (mixedEmbedding.norm : mixedSpace K → ℝ) :=
    (mixedEmbedding.continuous_norm K).measurable
  -- The measure of a positive norm-level set is independent of the level.
  have hlevel : ∀ a b : ℝ, 0 < a → 0 < b →
      DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = a}
        = DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = b} := by
    intro a b ha hb
    have hi : ∀ (s : Set (mixedSpace K)), MeasurableSet s →
        ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂(DedekindZeta.mixedMulHaar K)
          = DedekindZeta.mixedMulHaar K s := by
      intro s hs
      rw [lintegral_indicator hs]
      exact setLIntegral_one s
    have ht : 0 < a / b := div_pos ha hb
    have hmeasa : MeasurableSet {x : mixedSpace K | mixedEmbedding.norm x = a} :=
      hnormmeas (measurableSet_singleton a)
    have hmeasb : MeasurableSet {x : mixedSpace K | mixedEmbedding.norm x = b} :=
      hnormmeas (measurableSet_singleton b)
    have key := lintegral_radialMap_mixedMulHaar
      ({x : mixedSpace K | mixedEmbedding.norm x = a}.indicator (fun _ => (1 : ℝ≥0∞)))
      ((measurable_const).indicator hmeasa) ht
    -- Pointwise: the scaled indicator of `{N = a}` is the indicator of `{N = b}`.
    have hpt : (fun x => ({x : mixedSpace K | mixedEmbedding.norm x = a}.indicator
          (fun _ => (1 : ℝ≥0∞))) (radialMap K (a / b) x))
        = {x : mixedSpace K | mixedEmbedding.norm x = b}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext x
      have hN : mixedEmbedding.norm (radialMap K (a / b) x) = (a / b) * mixedEmbedding.norm x :=
        norm_radialMap (a / b) ht x
      by_cases hx : mixedEmbedding.norm x = b
      · rw [Set.indicator_of_mem (s := {x : mixedSpace K | mixedEmbedding.norm x = a})
              (show radialMap K (a / b) x ∈ {x : mixedSpace K | mixedEmbedding.norm x = a} by
                simp only [Set.mem_setOf_eq, hN, hx, div_mul_cancel₀ a hb.ne']),
            Set.indicator_of_mem (show x ∈ {x : mixedSpace K | mixedEmbedding.norm x = b} from hx)]
      · rw [Set.indicator_of_notMem
              (show radialMap K (a / b) x ∉ {x : mixedSpace K | mixedEmbedding.norm x = a} by
                simp only [Set.mem_setOf_eq, hN]
                intro h
                apply hx
                have hcancel : (a / b) * mixedEmbedding.norm x = (a / b) * b := by
                  rw [h, div_mul_cancel₀ a hb.ne']
                exact mul_left_cancel₀ (div_ne_zero ha.ne' hb.ne') hcancel),
            Set.indicator_of_notMem (show x ∉ {x : mixedSpace K | mixedEmbedding.norm x = b} from hx)]
    rw [hpt, hi _ hmeasb, hi _ hmeasa] at key
    exact key.symm
  -- If `{N = c}` had positive measure, all positive levels would, contradicting countability.
  by_contra hne
  have hpos : 0 < DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = c} :=
    pos_iff_ne_zero.mpr hne
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆
      {t : ℝ | 0 < DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = t}} := by
    intro b hb
    rw [Set.mem_setOf_eq, hlevel b c hb.1 hc]
    exact hpos
  have hcount : Set.Countable
      {t : ℝ | 0 < DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = t}} :=
    Measure.countable_meas_level_set_pos hnormmeas
  have hIoo : (Set.Ioo (0 : ℝ) 1).Countable := hcount.mono hsub
  rw [Cardinal.Real.Ioo_countable_iff] at hIoo
  linarith



/-- **Bochner collar shift** (`ℂ`-valued analogue of `lintegral_collar_shift`).
For a measurable scale-invariant set `S` (membership equivalence
`radialMap K t x ∈ S ↔ x ∈ S` for `t > 0`) and a radial-scale-invariant
measurable `g : mixedSpace K → ℂ`, the `mixedMulHaar`-integral of `g` over
`S ∩ {N ∈ (t, e·t]}` is independent of the collar position `t > 0`. The radial
scaling `radialMap K t = (· * c)` (with `N c ≠ 0`) is `mixedMulHaar`-measure-
preserving (`mixedMulHaar_map_mul_right`), so the substitution `x ↦ radialMap K t x`
on the half-open collar identifies the two integrals. No integrability is needed.
the standard treatment. -/
theorem setIntegral_collar_shift {S : Set (mixedSpace K)} (hS : MeasurableSet S)
    (hSinv : ∀ (t : ℝ), 0 < t → ∀ x, (radialMap K t x ∈ S ↔ x ∈ S))
    (g : mixedSpace K → ℂ)
    (hg : AEStronglyMeasurable g (DedekindZeta.mixedMulHaar K))
    (hgscale : ∀ (t : ℝ), 0 < t → ∀ x, g (radialMap K t x) = g x)
    {t : ℝ} (ht : 0 < t) :
    ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc t (Real.exp 1 * t)}),
        g x ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          g x ∂(DedekindZeta.mixedMulHaar K) := by
  classical
  set C : Set (mixedSpace K) := S ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hC
  set Ct : Set (mixedSpace K) := S ∩
      {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)} with hCt
  have hC_meas : MeasurableSet C :=
    hS.inter ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  have hCt_meas : MeasurableSet Ct :=
    hS.inter ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  have hiff : ∀ x, radialMap K t x ∈ Ct ↔ x ∈ C := by
    intro x
    rw [hCt, hC]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, norm_radialMap t ht x, Set.mem_Ioc]
    constructor
    · rintro ⟨hSmem, hlo, hhi⟩
      refine ⟨(hSinv t ht x).mp hSmem, ?_, ?_⟩
      · exact lt_of_mul_lt_mul_left (by rwa [mul_one]) ht.le
      · exact le_of_mul_le_mul_left (by rwa [mul_comm (Real.exp 1) t] at hhi) ht
    · rintro ⟨hSmem, hlo, hhi⟩
      refine ⟨(hSinv t ht x).mpr hSmem, ?_, ?_⟩
      · have := mul_lt_mul_of_pos_left hlo ht
        rwa [mul_one] at this
      · have := mul_le_mul_of_nonneg_left hhi ht.le
        rwa [mul_comm t (Real.exp 1)] at this
  -- `radialMap K t` is right translation by the nonzero-norm scalar `c = s • 1`,
  -- hence `mixedMulHaar`-measure-preserving.
  set s : ℝ := t ^ ((finrank ℚ K : ℝ)⁻¹) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos ht _
  set c : mixedSpace K := s • (1 : mixedSpace K) with hc
  have hcN : mixedEmbedding.norm c ≠ 0 := by
    rw [hc, mixedEmbedding.norm_smul, map_one, mul_one]
    exact pow_ne_zero _ (abs_ne_zero.mpr hspos.ne')
  have hrw : (fun x : mixedSpace K => radialMap K t x) = fun x => x * c := by
    funext x; rw [radialMap, hc, mul_smul_comm, mul_one]
  have hmp : MeasurePreserving (fun x : mixedSpace K => radialMap K t x)
      (DedekindZeta.mixedMulHaar K) (DedekindZeta.mixedMulHaar K) := by
    rw [hrw]
    exact ⟨DedekindZeta.measurable_mul_right_mixedSpace K c,
      DedekindZeta.mixedMulHaar_map_mul_right (K := K) hcN⟩
  rw [← integral_indicator hCt_meas, ← integral_indicator hC_meas]
  have hpt : (fun x => C.indicator g x)
      = fun x => (Ct.indicator g) (radialMap K t x) := by
    funext x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hiff x).mpr hx), hgscale t ht x]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun hcc => hx ((hiff x).mp hcc))]
  have hmap : (∫ x, Ct.indicator g x ∂(DedekindZeta.mixedMulHaar K))
      = ∫ y, Ct.indicator g y ∂(Measure.map (fun x => radialMap K t x)
          (DedekindZeta.mixedMulHaar K)) := by rw [hmp.map_eq]
  rw [hpt, hmap,
    integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hg.indicator hCt_meas)]

/-- **Bochner reflected collar** (`ℂ`-valued analogue of
`lintegral_reflected_collar_eq`). For a measurable scale-invariant set `S` and a
radial-scale-invariant measurable `g`, the integral over the reflected collar
`S ∩ {N ∈ [1/e, 1)}` equals the integral over the half-open collar
`S ∩ {N ∈ (1, e]}`. Route: `[1/e, 1)` agrees with `(1/e, 1] = (1/e, e·(1/e)]`
up to the `mixedMulHaar`-null boundary norm-levels `{N = 1/e}`, `{N = 1}`
(`mixedMulHaar_norm_eq_eq_zero`), to which `setIntegral_collar_shift` applies
with `t = 1/e`. the standard treatment. -/
theorem setIntegral_reflected_collar_eq {S : Set (mixedSpace K)} (hS : MeasurableSet S)
    (hSinv : ∀ (t : ℝ), 0 < t → ∀ x, (radialMap K t x ∈ S ↔ x ∈ S))
    (g : mixedSpace K → ℂ)
    (hg : AEStronglyMeasurable g (DedekindZeta.mixedMulHaar K))
    (hgscale : ∀ (t : ℝ), 0 < t → ∀ x, g (radialMap K t x) = g x) :
    ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ico (Real.exp 1)⁻¹ 1}),
        g x ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          g x ∂(DedekindZeta.mixedMulHaar K) := by
  classical
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  set a : ℝ := (Real.exp 1)⁻¹ with ha
  have hapos : 0 < a := inv_pos.mpr hepos
  have hmul : Real.exp 1 * a = 1 := by rw [ha, mul_inv_cancel₀ hepos.ne']
  have hshift := setIntegral_collar_shift hS hSinv g hg hgscale (t := a) hapos
  rw [hmul] at hshift
  have haeeq : {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ico a 1}
      =ᵐ[DedekindZeta.mixedMulHaar K] {x | mixedEmbedding.norm x ∈ Set.Ioc a 1} := by
    refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
    · refine measure_mono_null (t := {x : mixedSpace K | mixedEmbedding.norm x = a}) ?_
        (mixedMulHaar_norm_eq_eq_zero hapos)
      intro x hx
      obtain ⟨hin, hout⟩ := hx
      simp only [Set.mem_setOf_eq, Set.mem_Ico] at hin
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, not_and, not_le] at hout
      rcases eq_or_lt_of_le hin.1 with h | h
      · exact h.symm
      · exact absurd (hout h) (not_lt.mpr hin.2.le)
    · refine measure_mono_null (t := {x : mixedSpace K | mixedEmbedding.norm x = 1}) ?_
        (mixedMulHaar_norm_eq_eq_zero one_pos)
      intro x hx
      obtain ⟨hin, hout⟩ := hx
      simp only [Set.mem_setOf_eq, Set.mem_Ioc] at hin
      simp only [Set.mem_setOf_eq, Set.mem_Ico, not_and, not_lt] at hout
      rcases eq_or_lt_of_le hin.2 with h | h
      · exact h
      · exact absurd (hout hin.1.le) (not_le.mpr h)
  have hsetaeeq : (S ∩ {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ico a 1}
        : Set (mixedSpace K))
      =ᵐ[DedekindZeta.mixedMulHaar K]
        (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc a 1} : Set (mixedSpace K)) := by
    refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
    · have hsub : (S ∩ {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ico a 1})
          \ (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc a 1})
          ⊆ {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ico a 1}
            \ {x | mixedEmbedding.norm x ∈ Set.Ioc a 1} :=
        fun x hx => ⟨hx.1.2, fun hB => hx.2 ⟨hx.1.1, hB⟩⟩
      exact measure_mono_null hsub (MeasureTheory.ae_eq_set.mp haeeq).1
    · have hsub : (S ∩ {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ioc a 1})
          \ (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ico a 1})
          ⊆ {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ioc a 1}
            \ {x | mixedEmbedding.norm x ∈ Set.Ico a 1} :=
        fun x hx => ⟨hx.1.2, fun hA => hx.2 ⟨hx.1.1, hA⟩⟩
      exact measure_mono_null hsub (MeasureTheory.ae_eq_set.mp haeeq).2
  rw [setIntegral_congr_set hsetaeeq, hshift]

variable (K) in
/-- **Collar-reflection crux: inversion preserves the norm-collar Haar integral
for scale + unit-invariant integrands.** Let
`C = mixedEmbedding.fundamentalCone K ∩ {x | N x ∈ Set.Ioc 1 (Real.exp 1)}` be the
norm-collar of the fundamental cone. For an integrand `g` that is *both*
unit-invariant (`g (u • x) = g x`) and radial-scale-invariant
(`g (radialMap K t x) = g x` for `t > 0`), the group inversion `x ↦ x⁻¹` leaves
the `mixedMulHaar K`-integral over `C` unchanged:

    ∫_C g(x⁻¹) dμ_Haar = ∫_C g(x) dμ_Haar.

This is the geometric core (part (b)) of the norm-1 surface inversion law
`integral_surface_inv`, and the only piece of it not already available upstream.

Math (the standard treatment). `mixedMulHaar K` is inversion-invariant on the
punctured mixed space (`DedekindZeta.GammaIntegral.mixedMulHaar_map_inv`), so the
measurable involution `y = x⁻¹` gives `∫_C g(x⁻¹) dμ = ∫_{C⁻¹} g dμ`, where
`C⁻¹ = inv(cone) ∩ {N ∈ [1/e, 1)}` (using `mixedEmbedding_norm_inv :
N x⁻¹ = (N x)⁻¹`). Both `C` and `C⁻¹` are fundamental domains for the same
combined `(0,∞)`-scaling × `(𝓞 K)ˣ`-action on the norm-nonzero locus: the cone is
a fundamental domain for the unit action
(`isFundamentalDomain_fundamentalCone`), and within a scale-invariant set the
half-open collar `{N ∈ (1,e]}` is a fundamental domain for the radial scaling
with weight `dr/r` (`∫_1^e dr/r = 1`, `lintegral_collar_weight`). Inversion maps
cone → inv(cone) commuting with the unit action and reflects the collar; for `g`
invariant under both actions the integral over either fundamental domain agrees
(cf. the whole-cone analogue
`DedekindZeta.GammaIntegral.mixedMulHaar_integral_inv_cone_eq`, which handles the
unit-fundamental-domain step; the new content is the radial collar reflection on
top of it). -/
theorem mixedMulHaar_collar_integral_inv_eq (g : mixedSpace K → ℂ)
    (hunit : ∀ (u : (𝓞 K)ˣ) (x : mixedSpace K), g (u • x) = g x)
    (hscale : ∀ (t : ℝ), 0 < t → ∀ x, g (radialMap K t x) = g x)
    (hmeas : AEStronglyMeasurable g (DedekindZeta.mixedMulHaar K))
    (hint : IntegrableOn g
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})
      (DedekindZeta.mixedMulHaar K)) :
    ∫ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        g x⁻¹ ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        g x ∂(DedekindZeta.mixedMulHaar K) := by
  classical
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hA_meas : MeasurableSet
      {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} :=
    (mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc
  have hcone_meas : MeasurableSet (mixedEmbedding.fundamentalCone K) :=
    measurableSet_fundamentalCone K
  have hC_meas : MeasurableSet (mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}) := hcone_meas.inter hA_meas
  -- inversion image = preimage (involutive), hence measurable
  have himg_eq : ∀ T : Set (mixedSpace K),
      (fun y : mixedSpace K => y⁻¹) '' T = (fun y => y⁻¹) ⁻¹' T := by
    intro T; ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩; rwa [inv_inv]
    · intro hz; exact ⟨z⁻¹, hz, inv_inv z⟩
  have hinvcone_meas : MeasurableSet
      ((fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K) := by
    rw [himg_eq]; exact DedekindZeta.measurable_mixedSpace_inv hcone_meas
  have hinvC_meas : MeasurableSet ((fun y : mixedSpace K => y⁻¹) ''
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})) := by
    rw [himg_eq]; exact DedekindZeta.measurable_mixedSpace_inv hC_meas
  -- `radialMap K 1 = id`
  have hone : ∀ z : mixedSpace K, radialMap K 1 z = z := fun z => by
    simp [radialMap, Real.one_rpow, one_smul]
  -- the inverse cone is scale-invariant
  have hSinv : ∀ (t : ℝ), 0 < t → ∀ x,
      (radialMap K t x ∈ (fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K
        ↔ x ∈ (fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K) := by
    intro t ht x
    simp only [himg_eq, Set.mem_preimage]
    have hkey : (radialMap K t x)⁻¹ = radialMap K t⁻¹ x⁻¹ := by
      have h := radialMap_inv t ht x; rw [one_div] at h; exact h.symm
    rw [hkey]
    constructor
    · intro h
      have h2 := radialMap_mem_cone t ht h
      rwa [radialMap_radialMap t t⁻¹ ht.le (inv_pos.mpr ht).le,
        mul_inv_cancel₀ ht.ne', hone] at h2
    · intro h; exact radialMap_mem_cone t⁻¹ (inv_pos.mpr ht) h
  -- collar reflection bijection: `N x⁻¹ = (N x)⁻¹` flips `(1, e]` to `[1/e, 1)`
  have hball2 : ∀ z : ℝ, 0 ≤ z →
      (z ∈ Set.Ioc 1 (Real.exp 1) ↔ z⁻¹ ∈ Set.Ico (Real.exp 1)⁻¹ 1) := by
    intro z hz0
    rcases eq_or_lt_of_le hz0 with h | hz
    · subst h
      simp only [Set.mem_Ioc, Set.mem_Ico, inv_zero]
      constructor
      · rintro ⟨h1, _⟩; exact absurd h1 (by norm_num)
      · rintro ⟨h1, _⟩; exact absurd h1 (not_le.mpr (inv_pos.mpr he))
    · simp only [Set.mem_Ioc, Set.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(inv_le_inv₀ he hz).mpr h2, inv_lt_one_of_one_lt₀ h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(inv_lt_one₀ hz).mp h2, (inv_le_inv₀ he hz).mp h1⟩
  have claim1 : (fun y : mixedSpace K => y⁻¹) ''
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})
      = ((fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K)
        ∩ {x | mixedEmbedding.norm x ∈ Set.Ico (Real.exp 1)⁻¹ 1} := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨hyc, hyA⟩, rfl⟩
      refine ⟨⟨y, hyc, rfl⟩, ?_⟩
      rw [DedekindZeta.mixedEmbedding_norm_inv (K := K) y]
      exact (hball2 (mixedEmbedding.norm y) (mixedEmbedding.norm_nonneg y)).mp hyA
    · rintro ⟨⟨y, hyc, rfl⟩, hz⟩
      refine ⟨y, ⟨hyc, ?_⟩, rfl⟩
      rw [DedekindZeta.mixedEmbedding_norm_inv (K := K) y] at hz
      exact (hball2 (mixedEmbedding.norm y) (mixedEmbedding.norm_nonneg y)).mpr hz
  calc
    ∫ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        g x⁻¹ ∂(DedekindZeta.mixedMulHaar K)
        = ∫ x in ((fun y : mixedSpace K => y⁻¹) ''
            (mixedEmbedding.fundamentalCone K ∩
              {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})),
            g x ∂(DedekindZeta.mixedMulHaar K) := by
          -- (A) inversion change of variables
          rw [← integral_indicator hC_meas, ← integral_indicator hinvC_meas]
          have hpt : (fun x => (mixedEmbedding.fundamentalCone K ∩
                {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}).indicator
                  (fun y => g y⁻¹) x)
              = fun x => ((fun y : mixedSpace K => y⁻¹) ''
                  (mixedEmbedding.fundamentalCone K ∩
                    {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})).indicator g x⁻¹ := by
            funext x
            by_cases hx : x ∈ (mixedEmbedding.fundamentalCone K ∩
                {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})
            · rw [Set.indicator_of_mem hx,
                Set.indicator_of_mem (Set.mem_image_of_mem _ hx)]
            · have hxinv : x⁻¹ ∉ ((fun y : mixedSpace K => y⁻¹) ''
                  (mixedEmbedding.fundamentalCone K ∩
                    {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})) := by
                rintro ⟨y, hy, hyx⟩
                have hyx2 : y⁻¹ = x⁻¹ := hyx
                have hyx' : y = x := by rw [← inv_inv y, hyx2, inv_inv]
                exact hx (hyx' ▸ hy)
              rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxinv]
          rw [hpt]
          exact (DedekindZeta.mulHaar_integral_comp_inv
            (fun x => ((fun y : mixedSpace K => y⁻¹) ''
              (mixedEmbedding.fundamentalCone K ∩
                {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})).indicator g x)
            (hmeas.indicator hinvC_meas)).symm
    _ = ∫ x in (((fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K)
          ∩ {x | mixedEmbedding.norm x ∈ Set.Ico (Real.exp 1)⁻¹ 1}),
            g x ∂(DedekindZeta.mixedMulHaar K) := by rw [claim1]
    _ = ∫ x in (((fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K)
          ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
            g x ∂(DedekindZeta.mixedMulHaar K) :=
          -- (B) collar reflection on the inverse cone
          setIntegral_reflected_collar_eq hinvcone_meas hSinv g hmeas hscale
    _ = ∫ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
            g x ∂(DedekindZeta.mixedMulHaar K) := by
          -- (C) unit-fundamental-domain inversion
          have hAg_unit : ∀ (u : (𝓞 K)ˣ) (x : mixedSpace K),
              ({x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}).indicator g (u • x)
                = ({x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}).indicator g x := by
            intro u x
            simp only [Set.indicator_apply, Set.mem_setOf_eq, Theta.norm_unitSMul, hunit]
          have hAg_int : Integrable
              ((mixedEmbedding.fundamentalCone K).indicator
                (({x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}).indicator g))
              (DedekindZeta.mixedMulHaar K) := by
            rw [Set.indicator_indicator]
            exact (integrable_indicator_iff hC_meas).mpr hint
          have hstepC := DedekindZeta.mixedMulHaar_integral_inv_cone_eq
            (({x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}).indicator g)
            hAg_unit (hmeas.indicator hA_meas) hAg_int
          rw [Set.indicator_indicator, Set.indicator_indicator,
            integral_indicator (hinvcone_meas.inter hA_meas),
            integral_indicator hC_meas] at hstepC
          exact hstepC

variable (K) in
/-- **Inversion invariance of the surface integral (modulo the unit action).**
For a *unit-invariant* integrand `f` (`f (u • x) = f x` for all `u : (𝓞 K)ˣ`),
the norm-1 involution `σ ↦ σ⁻¹` leaves the surface integral unchanged.

The unit-invariance hypothesis is essential and cannot be dropped. The
fundamental cone `mixedEmbedding.fundamentalCone K` is
`logMap ⁻¹' (ZSpan.fundamentalDomain …) \ {N = 0}`, and `ZSpan.fundamentalDomain`
is the **half-open** parallelepiped `{∑ cᵢ bᵢ : cᵢ ∈ Set.Ico 0 1}`. On the
`N ≠ 0` locus `logMap x⁻¹ = - logMap x`, and negation sends `Ico 0 1` into
`Ioc (-1) 0`, so `x ∈ cone` does **not** imply `x⁻¹ ∈ cone`: `normEqOneSurface K`
is not setwise invariant under `σ ↦ σ⁻¹`, and `surfaceMeasure K` is not invariant
under inversion. (Taking `f = indicator (normEqOneSurface K)` exhibits the
failure for arbitrary `f`.) the standard treatment's involution acts on the norm-1 torus
**modulo units** — its integrand descends to the idele-class quotient, i.e. is
invariant under the `(𝓞 K)ˣ`-action — which is exactly the hypothesis `hf`.
the standard treatment. -/
theorem integral_surface_inv (f : mixedSpace K → ℂ)
    (hf : ∀ (u : (𝓞 K)ˣ) (x : mixedSpace K), f (u • x) = f x)
    (hf_meas : AEStronglyMeasurable f (surfaceMeasure K))
    (hfinv_meas : AEStronglyMeasurable (fun σ => f σ⁻¹) (surfaceMeasure K))
    (hg_meas : AEStronglyMeasurable (fun x => f (radialProj K x))
      (DedekindZeta.mixedMulHaar K))
    (hg_int : IntegrableOn (fun x => f (radialProj K x))
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})
      (DedekindZeta.mixedMulHaar K)) :
    ∫ σ in normEqOneSurface K, f σ⁻¹ ∂(surfaceMeasure K)
      = ∫ σ in normEqOneSurface K, f σ ∂(surfaceMeasure K) := by
  classical
  -- The four side conditions are pure measurability/integrability hypotheses
  -- (not a mathematical strengthening); they are discharged at the consumer
  -- `orbitTheta_inv_apply` from continuity of the theta kernel on the
  -- nonzero-norm locus and finiteness of the norm collar.
  set C : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hCdef
  have hCmeas : MeasurableSet C :=
    (measurableSet_fundamentalCone K).inter
      ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  have hq : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹ := by positivity
  have hscalar : Measurable
      (fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹ ^ ((finrank ℚ K : ℝ))⁻¹) :=
    (Real.continuous_rpow_const hq).measurable.comp
      ((mixedEmbedding.continuous_norm K).measurable.inv)
  have hmeasproj : Measurable (radialProj K) := hscalar.smul measurable_id
  -- `surfaceMeasure K` is supported on the norm-1 surface.
  have hae : ∀ᵐ σ ∂(surfaceMeasure K), σ ∈ normEqOneSurface K := by
    rw [ae_iff]
    simpa only [Set.mem_compl_iff, Set.compl_def] using
      surfaceMeasure_apply_compl_normEqOneSurface
  -- Transport a surface integral to the norm collar via the `radialProj` pushforward.
  have key : ∀ F : mixedSpace K → ℂ, AEStronglyMeasurable F (surfaceMeasure K) →
      ∫ σ in normEqOneSurface K, F σ ∂(surfaceMeasure K)
        = ∫ x in C, F (radialProj K x) ∂(DedekindZeta.mixedMulHaar K) := by
    intro F hF
    rw [← integral_eq_setIntegral hae]
    exact integral_map hmeasproj.aemeasurable hF
  rw [key (fun σ => f σ⁻¹) hfinv_meas, key f hf_meas]
  -- On the collar `N x ≠ 0`, so `(radialProj K x)⁻¹ = radialProj K x⁻¹`.
  have hcongr : ∫ x in C, f ((radialProj K x)⁻¹) ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in C, f (radialProj K x⁻¹) ∂(DedekindZeta.mixedMulHaar K) := by
    refine setIntegral_congr_fun hCmeas (fun x hx => ?_)
    obtain ⟨-, hxN⟩ := hx
    simp only [Set.mem_setOf_eq, Set.mem_Ioc] at hxN
    have hxNe : mixedEmbedding.norm x ≠ 0 := (lt_trans one_pos hxN.1).ne'
    rw [radialProj_inv hxNe]
  rw [hcongr]
  -- The remaining identity over the collar is the crux lemma applied to
  -- `g := f ∘ radialProj`, which is unit- and radial-scale-invariant.
  exact mixedMulHaar_collar_integral_inv_eq K (fun x => f (radialProj K x))
    (fun u x => by
      change f (radialProj K (u • x)) = f (radialProj K x)
      rw [radialProj_unitSMul]; exact hf u (radialProj K x))
    (fun t ht x => by
      change f (radialProj K (radialMap K t x)) = f (radialProj K x)
      rw [radialProj_radialMap ht])
    hg_meas hg_int

/-- **Norm-1 involution substitution for `orbitTheta`.** Substituting the
radius-`1/r` slice through the measure-preserving norm-1 involution `σ ↦ σ⁻¹`
(`surfaceMeasure`-preserving on `normEqOneSurface K`, since `N σ⁻¹ = 1`) together
with the radial identity `radialMap K (1/r) σ⁻¹ = (radialMap K r σ)⁻¹` rewrites
the `r ↦ 1/r` orbit theta as the surface integral of the *inverted* kernel
`Θ(𝔞, (radialMap K r σ)⁻¹)`. This isolates the geometric substitution underlying
the orbit inversion law (the standard treatment). -/
theorem orbitTheta_inv_apply (𝔞 : Ideal (𝓞 K)) (r : ℝ) (hr : 0 < r) :
    orbitTheta K 𝔞 (1 / r)
      = ∫ σ in normEqOneSurface K,
          Theta.idealThetaKernel K 𝔞 (radialMap K r σ)⁻¹ ∂(surfaceMeasure K) := by
  classical
  have hr1 : (0 : ℝ) < 1 / r := div_pos one_pos hr
  set f : mixedSpace K → ℂ :=
    fun σ => Theta.idealThetaKernel K 𝔞 (radialMap K (1 / r) σ) with hf_def
  set C : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hCdef
  have hCmeas : MeasurableSet C :=
    (measurableSet_fundamentalCone K).inter
      ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  have hq : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹ := by positivity
  -- Measurable set `{N ≠ 0}` and `surfaceMeasure` support fact.
  have hms : MeasurableSet {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
    have heq : {x : mixedSpace K | mixedEmbedding.norm x ≠ 0}
        = {x | mixedEmbedding.norm x = 0}ᶜ := by ext x; simp
    rw [heq]
    exact (measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable
      measurable_const).compl
  have hae : ∀ᵐ σ ∂(surfaceMeasure K), σ ∈ normEqOneSurface K := by
    rw [ae_iff]
    simpa only [Set.mem_compl_iff, Set.compl_def] using
      surfaceMeasure_apply_compl_normEqOneSurface
  have hSsub : normEqOneSurface K ⊆ {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    fun σ hσ => by
      simp only [Set.mem_setOf_eq, (mem_normEqOneSurface.mp hσ).2]; exact one_ne_zero
  -- Unit-invariance of `f`.
  have hunit : ∀ (u : (𝓞 K)ˣ) (x : mixedSpace K), f (u • x) = f x := by
    intro u x
    simp only [hf_def]
    have hcomm : radialMap K (1 / r) (u • x) = u • radialMap K (1 / r) x := by
      simp only [radialMap, NumberField.mixedEmbedding.unitSMul_smul]
      exact (Algebra.mul_smul_comm _ _ _).symm
    simp only [hcomm, Theta.idealThetaKernel_unitSMul]
  -- Continuity of `f` and `f ∘ inv` on the norm-1 surface.
  have hfcont : ContinuousOn f (normEqOneSurface K) := by
    have h := (continuousOn_mixedThetaKernel_radialMap K
      (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (1 / r) hr1).mono subset_closure
    simpa only [hf_def, ← Theta.idealThetaKernel_eq_mixed] using h
  have hf_meas : AEStronglyMeasurable f (surfaceMeasure K) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hfcont.aestronglyMeasurable measurableSet_normEqOneSurface
  have hfinvcont : ContinuousOn (fun σ => f σ⁻¹) (normEqOneSurface K) := by
    have hinv : ContinuousOn (Inv.inv : mixedSpace K → mixedSpace K)
        (normEqOneSurface K) := (continuousOn_inv_norm_ne_zero K).mono hSsub
    have hrm : ContinuousOn (fun σ => radialMap K (1 / r) σ⁻¹) (normEqOneSurface K) :=
      ((continuous_const_smul ((1 / r) ^ ((finrank ℚ K : ℝ)⁻¹))).continuousOn).comp
        hinv (Set.mapsTo_univ _ _)
    have hmaps : Set.MapsTo (fun σ => radialMap K (1 / r) σ⁻¹) (normEqOneSurface K)
        {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
      intro σ hσ
      have hN : mixedEmbedding.norm (radialMap K (1 / r) σ⁻¹) = 1 / r := by
        rw [norm_radialMap (1 / r) hr1, DedekindZeta.mixedEmbedding_norm_inv,
          (mem_normEqOneSurface.mp hσ).2, inv_one, mul_one]
      simp only [Set.mem_setOf_eq, hN]; exact hr1.ne'
    have := (Theta.continuousOn_idealThetaKernel K 𝔞).comp hrm hmaps
    simpa only [hf_def, Function.comp_def] using this
  have hfinv_meas : AEStronglyMeasurable (fun σ => f σ⁻¹) (surfaceMeasure K) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hfinvcont.aestronglyMeasurable measurableSet_normEqOneSurface
  -- Continuity of `f ∘ radialProj` on the nonzero-norm locus.
  have hscalarcont : ContinuousOn
      (fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹ ^ ((finrank ℚ K : ℝ)⁻¹))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    (Real.continuous_rpow_const hq).comp_continuousOn
      ((mixedEmbedding.continuous_norm K).continuousOn.inv₀ (fun x hx => hx))
  have hprojcont : ContinuousOn (radialProj K)
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    hscalarcont.smul continuousOn_id
  have hg1 : ContinuousOn (fun x => radialMap K (1 / r) (radialProj K x))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    ((continuous_const_smul ((1 / r) ^ ((finrank ℚ K : ℝ)⁻¹))).continuousOn).comp
      hprojcont (Set.mapsTo_univ _ _)
  have hg2 : Set.MapsTo (fun x => radialMap K (1 / r) (radialProj K x))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0}
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
    intro x hx
    have hpos : 0 < mixedEmbedding.norm x :=
      (mixedEmbedding.norm_nonneg x).lt_of_ne (Ne.symm hx)
    have hN1 : mixedEmbedding.norm (radialProj K x) = 1 := by
      rw [radialProj, norm_radialMap _ (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    simp only [Set.mem_setOf_eq, norm_radialMap (1 / r) hr1, hN1, mul_one]
    exact hr1.ne'
  have hgcont : ContinuousOn (fun x => f (radialProj K x))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
    have := (Theta.continuousOn_idealThetaKernel K 𝔞).comp hg1 hg2
    simpa only [hf_def, Function.comp_def] using this
  have hg_meas : AEStronglyMeasurable (fun x => f (radialProj K x))
      (DedekindZeta.mixedMulHaar K) := by
    rw [← Measure.restrict_eq_self_of_ae_mem DedekindZeta.ae_norm_ne_zero]
    exact hgcont.aestronglyMeasurable hms
  -- Integrability of `f ∘ radialProj` on the finite-measure collar.
  have hg_int : IntegrableOn (fun x => f (radialProj K x)) C
      (DedekindZeta.mixedMulHaar K) := by
    obtain ⟨M, hM⟩ := exists_bound_mixedThetaKernel_radialMap K
      (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (1 / r) hr1
    haveI : IsFiniteMeasure ((DedekindZeta.mixedMulHaar K).restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact mixedMulHaar_collar_lt_top⟩
    refine Integrable.mono' (integrable_const M) hg_meas.restrict ?_
    refine (ae_restrict_iff' hCmeas).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    obtain ⟨hxc, hxN⟩ := hx
    simp only [Set.mem_setOf_eq, Set.mem_Ioc] at hxN
    have hpos : 0 < mixedEmbedding.norm x := lt_trans one_pos hxN.1
    have hσ : radialProj K x ∈ normEqOneSurface K := by
      refine mem_normEqOneSurface.mpr ⟨radialMap_mem_cone _ (inv_pos.mpr hpos) hxc, ?_⟩
      rw [radialProj, norm_radialMap _ (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    change ‖f (radialProj K x)‖ ≤ M
    rw [hf_def]
    simp only [Theta.idealThetaKernel_eq_mixed]
    exact hM (radialProj K x) hσ
  rw [orbitTheta, ← hf_def]
  have hsub : (∫ σ in normEqOneSurface K, f σ ∂(surfaceMeasure K))
        = ∫ σ in normEqOneSurface K, f σ⁻¹ ∂(surfaceMeasure K) :=
    (integral_surface_inv K f hunit hf_meas hfinv_meas hg_meas hg_int).symm
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_normEqOneSurface (fun σ _ => ?_)
  simp only [hf_def, radialMap_inv r hr σ]


/-- **Orbit-integrated inversion law** (the orbit-level form of
`Theta.idealThetaKernel_inversion`): for `r > 0` and `𝔞 ≠ 0`,
`F(𝔞, 1/r) = (1/covol 𝔞) · r · G(𝔞, r)`. Derived by substituting the kernel
inversion into the surface integral, using the norm-1 involution `σ ↦ σ⁻¹` and
`∫_S 1 = V` to absorb the additive `±1` corrections into the constant `V` of the
completed thetas. This is exactly `IsMellinPair.hfe` with `C = (covol 𝔞)⁻¹`,
`k = 1`. -/
theorem radialTheta_inversion (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (r : ℝ) (hr : 0 < r) :
    radialTheta K 𝔞 (1 / r)
      = (Theta.covolume K 𝔞 : ℂ)⁻¹ * ((r ^ (1 : ℝ) : ℝ) : ℂ) * radialThetaDual K 𝔞 r := by
  -- Abbreviation for the inversion constant `c = r / covol 𝔞`.
  set c : ℂ := ((r / Theta.covolume K 𝔞 : ℝ) : ℂ) with hc
  -- Finiteness of the surface measure ⇒ constants are integrable on `S`.
  haveI : IsFiniteMeasure ((surfaceMeasure K).restrict (normEqOneSurface K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_normEqOneSurface_lt_top⟩
  -- Pointwise: the inverted kernel equals `c·Θ_mix(dual) + (c − 1)` on `S`.
  have hcongr : Set.EqOn
      (fun σ => Theta.idealThetaKernel K 𝔞 (radialMap K r σ)⁻¹)
      (fun σ => c * Theta.mixedThetaKernel K (Theta.dualIdeal K 𝔞) (radialMap K r σ)
          + (c - 1))
      (normEqOneSurface K) := by
    intro σ hσ
    have hxr : mixedEmbedding.norm (radialMap K r σ) = r := norm_radialMap_of_mem r hr hσ
    have hxne : mixedEmbedding.norm (radialMap K r σ) ≠ 0 := by rw [hxr]; exact hr.ne'
    show Theta.idealThetaKernel K 𝔞 (radialMap K r σ)⁻¹ = _
    rw [hc, Theta.idealThetaKernel_inversion K 𝔞 hne _ hxne, hxr, abs_of_pos hr]
    ring
  -- Integrability of the two pieces.
  have hint1 : Integrable
      (fun σ => c * Theta.mixedThetaKernel K (Theta.dualIdeal K 𝔞) (radialMap K r σ))
      ((surfaceMeasure K).restrict (normEqOneSurface K)) :=
    (integrableOn_mixedThetaKernel_radialMap (Theta.dualIdeal K 𝔞) r hr).const_mul c
  have hint2 : Integrable (fun _ : mixedSpace K => c - 1)
      ((surfaceMeasure K).restrict (normEqOneSurface K)) := integrable_const _
  -- Assemble.
  simp only [radialTheta]
  rw [orbitTheta_inv_apply 𝔞 r hr,
    setIntegral_congr_fun measurableSet_normEqOneSurface hcongr,
    integral_add hint1 hint2, integral_const_mul, setIntegral_const,
    Complex.real_smul, Real.rpow_one]
  simp only [radialThetaDual, orbitThetaFrac, surfaceVolume, hc,
    MeasureTheory.measureReal_def]
  push_cast [Complex.ofReal_div]
  ring

/-- **The `IsMellinPair` packaging of the radial theta**.

Bundles the constant term (`tendsto_radialTheta`), the exponential decay
(`exists_decay_radialTheta`) and the orbit inversion law
(`radialTheta_inversion`) into the `IsMellinPair` hypothesis consumed by
`DedekindZeta/MellinPrinciple.lean`:

* weight `k = 1` (matching the `1 − s` exponent of the cone inversion),
* inversion constant `C = (covolume K 𝔞)⁻¹`,
* constant terms `a₀ = b₀ = V = surfaceVolume K`,
* decay `c, α > 0` from `exists_decay_radialTheta`.

This instance feeds to `mellin_principle` to
obtain the polar terms `−a₀/s + C·b₀/(s−1)`. -/
theorem exists_isMellinPair_radialTheta (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    ∃ c α : ℝ,
      MellinPrinciple.IsMellinPair (radialTheta K 𝔞) (radialThetaDual K 𝔞)
        (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 c α := by
  obtain ⟨c, α, hc, hα, hf, hg⟩ := exists_decay_radialTheta (K := K) 𝔞
  refine ⟨c, α, ?_⟩
  refine
    { hf_cont := ?_
      hg_cont := ?_
      hk := one_pos
      hc := hc
      hα := hα
      hC := ?_
      hf_decay := hf
      hg_decay := hg
      hfe := ?_ }
  · -- continuity of `radialTheta K 𝔞 = orbitTheta K 𝔞 + V` on `Ioi 0`
    -- (`orbitTheta` is only continuous on `Ioi 0`; see `continuousOn_orbitTheta`).
    exact (continuousOn_orbitTheta K 𝔞).add continuousOn_const
  · -- continuity of `radialThetaDual K 𝔞 = orbitThetaFrac K (dualIdeal K 𝔞) + V`
    --  on `Ioi 0` (`continuousOn_orbitThetaFrac`).
    exact (continuousOn_orbitThetaFrac K (Theta.dualIdeal K 𝔞)).add continuousOn_const
  · -- `(covolume K 𝔞)⁻¹ ≠ 0`: reduces to `covolume K 𝔞 ≠ 0`, i.e.
    -- `(absNorm 𝔞 : ℝ) ≠ 0` (`Ideal.absNorm_eq_zero_iff`, `𝔞 ≠ 0`) and
    -- `√|discr K| ≠ 0` (`NumberField.discr_ne_zero`).
    have hcov : Theta.covolume K 𝔞 ≠ 0 := by
      rw [Theta.covolume]
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast (Ideal.absNorm_eq_zero_iff (I := 𝔞)).not.mpr hne
      · exact (Real.sqrt_pos_of_pos
          (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)))).ne'
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hcov)
  · -- inversion law `f(1/y) = C · y^k · g(y)`
    intro y hy
    exact radialTheta_inversion (K := K) 𝔞 hne y hy

end DedekindZeta.ConeRadialReduction

/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: mathlib-initiative/sum_product at 80e4127a67742659d521466204c6d2d7e0ca2b3f.
- Formalization note: Lean 4.33.1 compatibility port with narrow imports for DedekindZeta.ConeRadialReduction.
- PROVENANCE-END
-/
