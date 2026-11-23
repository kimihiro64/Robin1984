/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.PoissonSummation
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Theta series over the Minkowski space and its transformation law

This module is the geometric / Poisson-summation layer supporting the completed
Dedekind-zeta objects in `DedekindZeta.Statements`. It sets up the weighted
Minkowski model, theta kernels for ideal lattices, dual-lattice identifications,
and the inversion law used downstream.

This material follows Neukirch, *Algebraic Number Theory*, Chapter VII §§3 and 5:
theta series and their transformation law, then the specialization to ideal
lattices.

The geometric core here has no Mathlib counterpart yet.

## The Minkowski space `K_ℝ`

Mathlib's Minkowski / Minkowski-ℝ space `K_ℝ ≅ ℝ^{r₁} × ℂ^{r₂}` is
`NumberField.mixedEmbedding.mixedSpace K`, with the field embedding
`NumberField.mixedEmbedding K : K →+* mixedSpace K`. For the theta series we
need the Euclidean trace-form inner product `⟨·,·⟩` on `K_ℝ`. The customary
Minkowski metric carries a **factor `2` on the complex places**:

    ⟨x, y⟩_N = ∑_{real σ} σx·σy + ∑_{cplx σ} 2·Re(conj(σx)·σy),

whereas Mathlib's plain Euclidean model
`NumberField.mixedEmbedding.euclidean.mixedSpace K` (a `WithLp 2` space) uses the
*unweighted* `L²` inner product (factor `1` on the complex places). To recover
this normalisation we therefore scale the complex coordinates by `√2`
before landing in the Euclidean model (see `scaleMixed`/`eEmb` below): then

    ‖eEmb x‖² = ∑_{real σ} (σx)² + ∑_{cplx σ} 2·|σx|² = ⟨x, x⟩_N

is exactly the Minkowski quadratic form appearing in `θ`. This factor `2` is
essential: it is what makes `covolume Λ(𝓞_K) = √|d_K|` (the plain Mathlib metric
gives `2^{-r₂}√|d_K|`) and what makes the dual of `Λ(𝔞)` equal `Λ((𝔞𝔡)⁻¹)`
(the standard treatment); under the unweighted metric both statements are off
by a power of `2`.
-/

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff

namespace DedekindZeta.Theta

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

/-- The Euclidean Minkowski space `K_ℝ ≅ ℝ^{r₁} × ℂ^{r₂}` of `K`, carrying the
inner product `⟨·,·⟩` used in the standard treatment's theta series. -/
abbrev minkowskiSpace : Type _ := mixedEmbedding.euclidean.mixedSpace K

/-- `√2` as a (nonzero) real unit; used to weight the complex coordinates so
that the Euclidean quadratic form realises the standard treatment's factor `2` on the complex
places (the standard treatment). -/
def sqrtTwo : ℝˣ := Units.mk0 (Real.sqrt 2) (Real.sqrt_ne_zero'.mpr (by norm_num))

/-- The `ℝ`-linear weighting of the mixed space `K_ℝ = ℝ^{r₁} × ℂ^{r₂}` that
leaves the real coordinates fixed and scales the complex coordinates by `√2`.
Applying it before the (coordinate-preserving) identification with the Euclidean
model turns the unweighted `L²` norm into the standard treatment's Minkowski quadratic form
`∑_real (σx)² + ∑_cplx 2|σx|²` (the standard treatment). -/
def scaleMixed : mixedSpace K ≃L[ℝ] mixedSpace K :=
  (ContinuousLinearEquiv.refl ℝ ({w : InfinitePlace K // InfinitePlace.IsReal w} → ℝ)).prodCongr
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ)
      (M₁ := {w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ) sqrtTwo)

/-- The embedding `K → K_ℝ` of `K` into the Euclidean Minkowski space:
`mixedEmbedding` followed by the `√2`-weighting on the complex places
(`scaleMixed`) and the identification with the Euclidean model. With this
normalisation `‖eEmb x‖² = ∑_real (σx)² + ∑_cplx 2|σx|²` is exactly the
Minkowski quadratic form `⟨x, x⟩_N` of the standard treatment. -/
def eEmb (x : K) : minkowskiSpace K :=
  (mixedEmbedding.euclidean.toMixed K).symm (scaleMixed K (mixedEmbedding K x))

/-- The `ℝ`-linear identification `K_ℝ = mixedSpace K ≃ minkowskiSpace K`
(weight the complex places by `√2` via `scaleMixed`, then pass to the Euclidean
model `euclidean.mixedSpace`). This transports the Minkowski inner product of
`minkowskiSpace` back to `mixedSpace`; it is the equivalence `g` already used in
`summable_theta`, and satisfies `eEmb K x = toMinkowski K (mixedEmbedding K x)`. -/
def toMinkowski : mixedSpace K ≃L[ℝ] minkowskiSpace K :=
  (scaleMixed K).trans (mixedEmbedding.euclidean.toMixed K).symm

/-- **ℝ-linear extension of `eEmb`**.
The canonical embedding `eEmb : K → minkowskiSpace K` extends to the `ℝ`-linear
isomorphism `eEmbℝ : K_ℝ = mixedSpace K ≃L[ℝ] minkowskiSpace K`, namely
`scaleMixed` (the `√2`-weighting on complex places) followed by the
identification with the Euclidean model. It is definitionally `toMinkowski` and
satisfies `eEmbℝ (mixedEmbedding K a) = eEmb K a` (`eEmbℝ_mixedEmbedding`). Both
factors are isomorphisms, so `eEmbℝ` is bijective: every `y : minkowskiSpace K`
is `eEmbℝ ξ` for a unique `ξ : mixedSpace K` (it is a `ContinuousLinearEquiv`). -/
abbrev eEmbℝ : mixedSpace K ≃L[ℝ] minkowskiSpace K := toMinkowski K

/-- `eEmbℝ` extends `eEmb`: on the image of `mixedEmbedding` it agrees with the
canonical embedding `eEmb`. -/
@[simp]
theorem eEmbℝ_mixedEmbedding (a : K) :
    eEmbℝ K (mixedEmbedding K a) = eEmb K a := rfl

/-- The image lattice `Λ(I)` of a fractional ideal `I` in the Euclidean
Minkowski space `K_ℝ`: the `ℤ`-span of `eEmb '' I`. For a nonzero `I` this is a
complete lattice (the standard treatment). -/
def idealLattice (I : FractionalIdeal (𝓞 K)⁰ K) :
    Submodule ℤ (minkowskiSpace K) :=
  Submodule.span ℤ (eEmb K '' (I : Submodule (𝓞 K) K))

/-- The covolume constant of the lattice `Λ(𝔞)` of a nonzero integral ideal
`𝔞`, namely `vol(Λ(𝔞)) = 𝔑(𝔞) · √|d_K|` (the standard treatment and the
computation `vol(𝔞) = 𝔑(𝔞)|d_K|^{1/2}`). -/
def covolume (𝔞 : Ideal (𝓞 K)) : ℝ :=
  (Ideal.absNorm 𝔞 : ℝ) * Real.sqrt (|(NumberField.discr K : ℝ)|)

/-! ## The theta series (the standard treatment) -/


/-- **Convergence** (the standard treatment): for `t > 0` the theta series of a
nonzero fractional ideal converges absolutely. -/
theorem summable_theta {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {t : ℝ}
    (ht : 0 < t) :
    Summable fun x : (I : Submodule (𝓞 K) K) =>
      Real.exp (-Real.pi * t * ‖eEmb K (x : K)‖ ^ 2) := by
  classical
  -- View `I` as a unit (nonzero fractional ideals form a `CommGroupWithZero`).
  set I' : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 I hI with hI'
  -- The image lattice of `I` in the (non-Euclidean) mixed space.  It is a full,
  -- discrete lattice, so power-law sums over it converge (`ZLattice`).
  set M := mixedEmbedding.idealLattice K I' with hM
  -- The continuous linear equivalence relating the two models of `K_ℝ`.
  set toM := mixedEmbedding.euclidean.toMixed K with htoM
  -- The full embedding map `K_ℝ → K_ℝ^{eucl}` used by `eEmb`: weight the complex
  -- places by `√2`, then pass to the Euclidean model.  It is a fixed `ℝ`-linear
  -- iso, so it does not affect summability.
  set g : mixedSpace K ≃L[ℝ] minkowskiSpace K := (scaleMixed K).trans toM.symm with hg
  -- A norm-comparison constant for the inverse of `g`.
  set Cl : ℝ := ‖g.symm.toContinuousLinearMap‖ with hCl
  set Ko : ℝ := Cl + 1 with hKo
  have hCl_nonneg : 0 ≤ Cl := norm_nonneg _
  have hKo_pos : 0 < Ko := by rw [hKo]; linarith
  set c : ℝ := Ko⁻¹ with hc
  have hc_pos : 0 < c := by rw [hc]; exact inv_pos.mpr hKo_pos
  set a : ℝ := Real.pi * t * c ^ 2 with hadef
  have ha : 0 < a := by
    rw [hadef]; have := Real.pi_pos; positivity
  -- Finiteness of lattice points in any ball (discreteness of `M`).
  have hfin : ∀ R : ℝ, {z : M | ‖(z : mixedSpace K)‖ < R}.Finite := by
    intro R
    have hb : (Metric.ball (0 : mixedSpace K) R ∩ (M : Set (mixedSpace K))).Finite := by
      rw [hM, ← mixedEmbedding.span_idealLatticeBasis]
      exact ZSpan.setFinite_inter _ Metric.isBounded_ball
    apply (hb.preimage (Subtype.val_injective.injOn)).subset
    intro z hz
    refine ⟨?_, z.2⟩
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  -- Power-law summability over the lattice `M`.
  set r : ℝ := -(Module.finrank ℤ M : ℝ) - 1 with hr
  have hsum_rpow : Summable (fun z : M => ‖(z : mixedSpace K)‖ ^ r) :=
    ZLattice.summable_norm_rpow M r (by rw [hr]; linarith)
  -- Gaussian decay beats any negative power.
  have hev : ∀ᶠ s : ℝ in Filter.atTop, Real.exp (-a * s ^ 2) ≤ s ^ r := by
    have key : Filter.Tendsto (fun s : ℝ => s ^ (-r) * Real.exp (-a * s ^ 2))
        Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun s : ℝ => s ^ 2) Filter.atTop Filter.atTop :=
        Filter.tendsto_pow_atTop two_ne_zero
      have hcomp := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-r / 2) a ha).comp h2
      refine hcomp.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with s hs
      simp only [Function.comp_apply]
      congr 1
      rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs]
      congr 1
      push_cast; ring
    filter_upwards [key.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
      Filter.eventually_gt_atTop (0 : ℝ)] with s hs1 hs2
    have hsr : (0 : ℝ) < s ^ r := Real.rpow_pos_of_pos hs2 r
    have hrw : s ^ r * (s ^ (-r) * Real.exp (-a * s ^ 2)) = Real.exp (-a * s ^ 2) := by
      rw [← mul_assoc, ← Real.rpow_add hs2, add_neg_cancel, Real.rpow_zero, one_mul]
    calc Real.exp (-a * s ^ 2)
        = s ^ r * (s ^ (-r) * Real.exp (-a * s ^ 2)) := hrw.symm
      _ ≤ s ^ r * 1 := by exact mul_le_mul_of_nonneg_left hs1.le hsr.le
      _ = s ^ r := mul_one _
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hev
  -- Summability of the Gaussian over the lattice `M` (in the Euclidean model).
  have hsum_g : Summable (fun z : M =>
      Real.exp (-Real.pi * t * ‖g (z : mixedSpace K)‖ ^ 2)) := by
    apply Summable.of_norm_bounded_eventually hsum_rpow
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (hfin R)
    intro z hz
    simp only [Set.mem_setOf_eq]
    by_contra hlt
    push_neg at hlt
    apply hz
    set s : ℝ := ‖(z : mixedSpace K)‖ with hsdef
    set w := g (z : mixedSpace K) with hw
    have hsKo : s ≤ Ko * ‖w‖ := by
      calc s = ‖g.symm w‖ := by
              rw [hsdef, hw, ContinuousLinearEquiv.symm_apply_apply]
        _ ≤ Cl * ‖w‖ := g.symm.toContinuousLinearMap.le_opNorm w
        _ ≤ Ko * ‖w‖ := by gcongr; linarith
    have hcs : c * s ≤ ‖w‖ := by
      rw [hc]
      rw [inv_mul_le_iff₀ hKo_pos]
      linarith
    have hcs_nonneg : 0 ≤ c * s := by positivity
    have hws : c ^ 2 * s ^ 2 ≤ ‖w‖ ^ 2 := by
      have := pow_le_pow_left₀ hcs_nonneg hcs 2
      rwa [mul_pow] at this
    have hexp_le : Real.exp (-Real.pi * t * ‖w‖ ^ 2) ≤ Real.exp (-a * s ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hle : a * s ^ 2 ≤ Real.pi * t * ‖w‖ ^ 2 := by
        have heq : a * s ^ 2 = Real.pi * t * (c ^ 2 * s ^ 2) := by rw [hadef]; ring
        rw [heq]
        have hpt : (0 : ℝ) ≤ Real.pi * t := by have := Real.pi_pos; positivity
        exact mul_le_mul_of_nonneg_left hws hpt
      linarith
    have hg_nonneg : (0 : ℝ) ≤ Real.exp (-Real.pi * t * ‖w‖ ^ 2) := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hg_nonneg]
    exact hexp_le.trans (hR s hlt)
  -- Transfer summability back along the injection `I ↪ M`.
  have hφ : ∀ x : ↥(I : Submodule (𝓞 K) K), mixedEmbedding K (x : K) ∈ M := by
    intro x
    rw [hM, mixedEmbedding.mem_idealLattice]
    refine ⟨(x : K), ?_, rfl⟩
    have hx : (x : K) ∈ (I : Submodule (𝓞 K) K) := x.2
    simpa [hI', FractionalIdeal.mem_coe] using hx
  set φ : ↥(I : Submodule (𝓞 K) K) → M := fun x => ⟨mixedEmbedding K (x : K), hφ x⟩ with hφdef
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have h1 : mixedEmbedding K (x : K) = mixedEmbedding K (y : K) := by
      simpa [hφdef] using congrArg (Subtype.val) hxy
    have h2 : (x : K) = (y : K) := mixedEmbedding_injective K h1
    exact Subtype.ext h2
  refine (hsum_g.comp_injective hφ_inj).congr (fun x => ?_)
  simp only [Function.comp_apply, hφdef, eEmb, hg, htoM,
    ContinuousLinearEquiv.trans_apply]

/-! ## The different and the dual lattice (the standard treatment) -/

/-- The (inverse) different as a fractional ideal: `𝔡 = differentIdeal ℤ 𝓞_K`,
viewed in `FractionalIdeal (𝓞 K)⁰ K`. -/
abbrev differentFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)

/-- The fractional ideal `(𝔞𝔡)⁻¹` whose lattice `Λ((𝔞𝔡)⁻¹)` is dual to
`Λ(𝔞)` in `K_ℝ` (the standard treatment): the dual of the lattice of `𝔞` is
the lattice of `(𝔞𝔡)⁻¹`, where `𝔡` is the different. -/
def dualIdeal (𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K :=
  ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) * differentFractionalIdeal K)⁻¹

/-- The `dualIdeal` is exactly Mathlib's trace-form dual fractional ideal
`FractionalIdeal.dual ℤ ℚ 𝔞` (the standard treatment: the trace dual of `𝔞` is
`(𝔞𝔡)⁻¹`, with `𝔡` the different). -/
theorem dualIdeal_eq_dual (𝔞 : Ideal (𝓞 K)) :
    FractionalIdeal.dual ℤ ℚ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = dualIdeal K 𝔞 := by
  have hd1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (differentFractionalIdeal K)⁻¹ := by
    have h := coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)
    rw [differentFractionalIdeal, h, inv_inv]
  rw [FractionalIdeal.dual_eq_mul_inv, hd1, dualIdeal, mul_inv, mul_comm]



/-- **ℝ-bilinear extension of `inner_eEmb`.** For an arbitrary point
`ξ : mixedSpace K = K_ℝ` and `y : K`, the Minkowski inner product of `eEmbℝ ξ`
(the `ℝ`-linear extension of `eEmb`) against `eEmb y` is the place-sum Hermitian
pairing `B(ξ, y)` (the standard treatment): the factor `2` on the complex places
comes from the `√2`-weighting baked into `eEmbℝ`/`eEmb`. Specialising
`ξ = mixedEmbedding K x` recovers `inner_eEmb`. -/
theorem inner_eEmbℝ (ξ : mixedSpace K) (y : K) :
    (inner ℝ (eEmbℝ K ξ) (eEmb K y) : ℝ) =
      (∑ w : {w : InfinitePlace K // w.IsReal},
          ξ.1 w * (mixedEmbedding K y).1 w) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
          (starRingEnd ℂ (ξ.2 w) * (mixedEmbedding K y).2 w).re := by
  classical
  rw [WithLp.prod_inner_apply,
      show (WithLp.ofLp (eEmbℝ K ξ)).fst
          = WithLp.toLp 2 (scaleMixed K ξ).1 from rfl,
      show (WithLp.ofLp (eEmb K y)).fst
          = WithLp.toLp 2 (scaleMixed K (mixedEmbedding K y)).1 from rfl,
      show (WithLp.ofLp (eEmbℝ K ξ)).snd
          = WithLp.toLp 2 (scaleMixed K ξ).2 from rfl,
      show (WithLp.ofLp (eEmb K y)).snd
          = WithLp.toLp 2 (scaleMixed K (mixedEmbedding K y)).2 from rfl]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, scaleMixed,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_refl', id_eq,
    ContinuousLinearEquiv.smulLeft_apply_apply, real_inner_eq_re_inner ℂ]
  rw [Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl (fun w _ => mul_comm _ _)
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    have key : (sqrtTwo • (mixedEmbedding K y).2) w *
        (starRingEnd ℂ) ((sqrtTwo • ξ.2) w)
        = ((2 : ℝ) : ℂ) *
          ((starRingEnd ℂ) (ξ.2 w) * (mixedEmbedding K y).2 w) := by
      simp only [Pi.smul_apply, Units.smul_def, sqrtTwo, Units.val_mk0, Complex.real_smul,
        map_mul, Complex.conj_ofReal]
      rw [← hsq]; ring
    rw [key]; exact Complex.re_ofReal_mul _ _

/-- **Coordinatewise complex conjugation `c` on `K_ℝ = mixedSpace K`.** It fixes
the real coordinates and conjugates the complex coordinates. This is the
conjugation appearing in the conjugate-trace identity
`inner_eEmbℝ_eq_traceForm_conjMixed`. -/
def conjMixed (ξ : mixedSpace K) : mixedSpace K :=
  ⟨ξ.1, fun w => (starRingEnd ℂ) (ξ.2 w)⟩

@[simp]
theorem conjMixed_fst (ξ : mixedSpace K) : (conjMixed K ξ).1 = ξ.1 := rfl

@[simp]
theorem conjMixed_snd (ξ : mixedSpace K) (w : {w : InfinitePlace K // w.IsComplex}) :
    (conjMixed K ξ).2 w = (starRingEnd ℂ) (ξ.2 w) := rfl

/-- **Coordinatewise complex conjugation as an `ℝ`-linear continuous involution**
of `mixedSpace K`: the identity on the real coordinates and `Complex.conjLIE`
(`z ↦ conj z`) on each complex coordinate. It is the bundled form of `conjMixed`
(`conjMixedₗ_apply`). Complex conjugation is an `ℝ`-linear isometry of `ℂ`, so
this is an `ℝ`-linear isometric involution. -/
def conjMixedₗ : mixedSpace K ≃L[ℝ] mixedSpace K :=
  (ContinuousLinearEquiv.refl ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)).prodCongr
    (ContinuousLinearEquiv.piCongrRight
      (fun _ : {w : InfinitePlace K // w.IsComplex} =>
        Complex.conjLIE.toContinuousLinearEquiv))

@[simp]
theorem conjMixedₗ_apply (ξ : mixedSpace K) : conjMixedₗ K ξ = conjMixed K ξ := rfl


@[simp]
theorem conjMixedₗ_conjMixedₗ (ξ : mixedSpace K) :
    conjMixedₗ K (conjMixedₗ K ξ) = ξ := by
  apply Prod.ext
  · rfl
  · funext w
    simp only [conjMixedₗ_apply, conjMixed_snd, conjMixed_fst]
    exact Complex.conj_conj _

/-- **The induced complex conjugation `conjMink` on the Euclidean Minkowski
space** `minkowskiSpace K`, transported from `conjMixedₗ` through the `ℝ`-linear
identification `eEmbℝ : mixedSpace K ≃L[ℝ] minkowskiSpace K`:
`conjMink = eEmbℝ ∘ conjMixed ∘ eEmbℝ⁻¹`. It is the conjugation twist appearing
in the Hermitian Minkowski dual of `Λ(𝔞)` (the standard treatment): the dual
of `Λ(𝔞)` is `conjMink '' Λ((𝔞𝔡)⁻¹)`, which equals `Λ((𝔞𝔡)⁻¹)` itself only when
complex conjugation is a `K`-automorphism (the CM / totally-real case). Since
conjugation commutes with the `√2`-weighting `scaleMixed` and preserves `|·|` on
each complex factor, `conjMink` is an isometric involution preserving the
Euclidean norm and covolume. -/
def conjMink : minkowskiSpace K ≃L[ℝ] minkowskiSpace K :=
  ((eEmbℝ K).symm.trans (conjMixedₗ K)).trans (eEmbℝ K)

theorem conjMink_apply (y : minkowskiSpace K) :
    conjMink K y = eEmbℝ K (conjMixed K ((eEmbℝ K).symm y)) := rfl

@[simp]
theorem conjMink_conjMink (y : minkowskiSpace K) :
    conjMink K (conjMink K y) = y := by
  simp only [conjMink_apply, ContinuousLinearEquiv.symm_apply_apply, ← conjMixedₗ_apply,
    conjMixedₗ_conjMixedₗ, ContinuousLinearEquiv.apply_symm_apply]

@[simp]
theorem conjMink_symm_apply (y : minkowskiSpace K) :
    (conjMink K).symm y = conjMink K y := by
  apply (conjMink K).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, conjMink_conjMink]





/-- **The `ℝ`-bilinear trace form `T` on `K_ℝ`.** For `ξ : mixedSpace K` and
`a : K`, `T(ξ, a) = Re(∑_σ ξ_σ · σ a)`, written here as the place sum
`∑_{w real} ξ.1 w · σ_w a + 2·∑_{w cplx} Re(ξ.2 w · σ_w a)`. Its defining
property (`traceForm_mixedEmbedding`) is
`T(mixedEmbedding K b, a) = (algebraMap ℚ ℝ) (Algebra.trace ℚ K (b*a)) = Tr_{K/ℚ}(b·a)`,
so it is the canonical-embedding extension of the `ℚ`-trace form. NB: this is
the *trace* form (no conjugation), distinct from the Hermitian inner product
`inner_eEmbℝ`; the two are related by `c` via `inner_eEmbℝ_eq_traceForm_conjMixed`. -/
def traceForm (ξ : mixedSpace K) (a : K) : ℝ :=
  (∑ w : {w : InfinitePlace K // w.IsReal}, ξ.1 w * (mixedEmbedding K a).1 w) +
  2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
      (ξ.2 w * (mixedEmbedding K a).2 w).re

/-- **Conjugate-trace pairing identity** (caution: it is the
*conjugate* trace `T(cξ, ·)`, NOT `Tr(ξ··)`). The Minkowski inner product of the
`ℝ`-linear extension `eEmbℝ ξ` against `eEmb a` equals the trace form evaluated
at the conjugate `c ξ`: `B(ξ, a) = T(c ξ, a)`. -/
theorem inner_eEmbℝ_eq_traceForm_conjMixed (ξ : mixedSpace K) (a : K) :
    (inner ℝ (eEmbℝ K ξ) (eEmb K a) : ℝ) = traceForm K (conjMixed K ξ) a := by
  rw [inner_eEmbℝ, traceForm]
  simp only [conjMixed_fst, conjMixed_snd]

/-- The sum over all complex embeddings `∑_{σ : K →+* ℂ} σ b · σ a` equals the
image of the `ℚ`-trace `Tr_{K/ℚ}(b·a)` under `algebraMap ℚ ℂ`
(`trace_eq_sum_embeddings`, reindexed from `K →ₐ[ℚ] ℂ` to `K →+* ℂ`). -/
theorem sum_embeddings_mul (b a : K) :
    (∑ σ : K →+* ℂ, σ b * σ a) = algebraMap ℚ ℂ (Algebra.trace ℚ K (b * a)) := by
  have hmul : ∀ σ : K →+* ℂ, σ b * σ a = σ (b * a) := fun σ => (map_mul σ b a).symm
  simp_rw [hmul]
  rw [trace_eq_sum_embeddings (E := ℂ)]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom K Complex) (fun s : RingHom K Complex => s (b * a))
    (fun φ : K →ₐ[ℚ] ℂ => φ (b * a)) (fun σ => rfl)

/-- **Defining property of `T`**: on canonical-embedding images the trace form
is the `ℚ`-trace, `T(mixedEmbedding K b, a) = (algebraMap ℚ ℝ)(Tr_{K/ℚ}(b·a))`
(the standard treatment). -/
theorem traceForm_mixedEmbedding (b a : K) :
    traceForm K (mixedEmbedding K b) a
      = algebraMap ℚ ℝ (Algebra.trace ℚ K (b * a)) := by
  classical
  -- The `mk`-fiber over a place `w` is the conjugate pair (singleton when real).
  have hfib : ∀ w : InfinitePlace K,
      (Finset.univ.filter fun σ : K →+* ℂ => InfinitePlace.mk σ = w)
        = {InfinitePlace.embedding w,
            ComplexEmbedding.conjugate (InfinitePlace.embedding w)} := by
    intro w
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      rcases InfinitePlace.mk_eq_iff.mp (h.trans (InfinitePlace.mk_embedding w).symm) with
        h1 | h1
      · exact Or.inl h1
      · exact Or.inr ((ComplexEmbedding.involutive_conjugate K).eq_iff.mp h1)
    · rintro (h1 | h1)
      · rw [h1, InfinitePlace.mk_embedding]
      · rw [h1, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have hReal : ∀ w : {w : InfinitePlace K // w.IsReal},
      (∑ σ ∈ Finset.univ.filter fun σ : K →+* ℂ =>
            InfinitePlace.mk σ = (w : InfinitePlace K),
          (σ b * σ a).re)
        = (mixedEmbedding K b).1 w * (mixedEmbedding K a).1 w := by
    intro w
    rw [hfib w.1, InfinitePlace.conjugate_embedding_eq_of_isReal w.2,
      Finset.insert_eq_self.mpr (Finset.mem_singleton_self _), Finset.sum_singleton,
      mixedEmbedding_apply_isReal, mixedEmbedding_apply_isReal,
      ← InfinitePlace.embedding_of_isReal_apply w.2 b,
      ← InfinitePlace.embedding_of_isReal_apply w.2 a,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hCplx : ∀ w : {w : InfinitePlace K // w.IsComplex},
      (∑ σ ∈ Finset.univ.filter fun σ : K →+* ℂ =>
            InfinitePlace.mk σ = (w : InfinitePlace K),
          (σ b * σ a).re)
        = 2 * ((mixedEmbedding K b).2 w * (mixedEmbedding K a).2 w).re := by
    intro w
    have hne : InfinitePlace.embedding (w : InfinitePlace K)
        ≠ ComplexEmbedding.conjugate (InfinitePlace.embedding (w : InfinitePlace K)) := by
      intro h
      refine (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) ?_
      rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
      exact h.symm
    rw [hfib w.1, Finset.sum_pair hne, mixedEmbedding_apply_isComplex,
      mixedEmbedding_apply_isComplex, ComplexEmbedding.conjugate_coe_eq,
      ComplexEmbedding.conjugate_coe_eq]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hsum : traceForm K (mixedEmbedding K b) a = (∑ σ : K →+* ℂ, σ b * σ a).re := by
    rw [traceForm, Complex.re_sum,
      ← Finset.sum_fiberwise Finset.univ (fun σ : K →+* ℂ => InfinitePlace.mk σ)
        (fun σ : K →+* ℂ => (σ b * σ a).re),
      InfinitePlace.sum_eq_sum_add_sum]
    rw [Finset.sum_congr rfl (fun w _ => hReal w),
      show (∑ w : {w : InfinitePlace K // w.IsComplex},
            ∑ σ ∈ Finset.univ.filter fun σ : K →+* ℂ =>
              InfinitePlace.mk σ = (w : InfinitePlace K),
            (σ b * σ a).re)
          = 2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
              ((mixedEmbedding K b).2 w * (mixedEmbedding K a).2 w).re
        from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => hCplx w)]
  rw [hsum, sum_embeddings_mul, IsScalarTower.algebraMap_apply ℚ ℝ ℂ,
    Complex.coe_algebraMap, Complex.ofReal_re]

/-- **Reduction to generators** of the dual-lattice integrality condition.
Since `inner ℝ y ·` is `ℤ`-linear and the integers are closed under `ℤ`-linear
combinations, the condition `⟪y, x⟫ ∈ ℤ` for *all* `x` in the lattice
`Λ(I) = span ℤ (eEmb '' I)` is equivalent to its holding only on the generators
`x = eEmb a`, `a ∈ I`. This is step 2(a) towards `dual_idealLattice`: it
removes the `span`/lattice quantifier so the remaining work is the
inner-product ↔ trace-form bridge on individual ideal elements. -/
theorem forall_inner_int_iff_gens (I : FractionalIdeal (𝓞 K)⁰ K)
    (y : minkowskiSpace K) :
    (∀ x ∈ idealLattice K I, ∃ k : ℤ, (inner ℝ y x : ℝ) = k) ↔
      ∀ a ∈ (I : Submodule (𝓞 K) K), ∃ k : ℤ,
        (inner ℝ y (eEmb K a) : ℝ) = k := by
  classical
  -- The set of points pairing integrally with `y` is a `ℤ`-submodule.
  set N : Submodule ℤ (minkowskiSpace K) :=
    { carrier := {x | ∃ k : ℤ, (inner ℝ y x : ℝ) = k}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro a b ⟨ka, ha⟩ ⟨kb, hb⟩
        exact ⟨ka + kb, by rw [inner_add_right, ha, hb]; push_cast; ring⟩
      smul_mem' := by
        rintro c a ⟨k, hk⟩
        refine ⟨c * k, ?_⟩
        have hcs : (c • a : minkowskiSpace K) = (c : ℝ) • a :=
          (Int.cast_smul_eq_zsmul ℝ c a).symm
        rw [hcs, real_inner_smul_right, hk]; push_cast; ring } with hN
  constructor
  · intro h a ha
    exact h (eEmb K a) (Submodule.subset_span ⟨a, ha, rfl⟩)
  · intro h x hx
    have hle : idealLattice K I ≤ N := by
      rw [idealLattice, Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      exact h a ha
    exact hle hx

/-! ## Bridging `theta` to a lattice Gaussian sum

The theta series sums the Gaussian over the elements of the ideal `I`; the
image map `eEmb : K → K_ℝ` carries the ℤ-module `I` *onto* its lattice
`idealLattice K I = span ℤ (eEmb '' I)` (the image of an additive subgroup is
already a subgroup, so the ℤ-span adds nothing new). Hence the sum over `I` and
the sum over the lattice agree. This is the form consumed by the Poisson step. -/

/-- `eEmb` packaged as an additive group homomorphism `K →+ minkowskiSpace K`
(`mixedEmbedding` is a ring hom, `scaleMixed`/`toMixed` are `ℝ`-linear), so it
is automatically `ℤ`-linear. -/
def eEmbHom : K →+ minkowskiSpace K :=
  ((mixedEmbedding.euclidean.toMixed K).symm.toLinearEquiv.toLinearMap.toAddMonoidHom).comp <|
    (((scaleMixed K).toLinearEquiv.toLinearMap.toAddMonoidHom).comp
      (mixedEmbedding K).toAddMonoidHom)

@[simp] theorem eEmbHom_apply (x : K) : eEmbHom K x = eEmb K x := rfl


theorem eEmb_injective : Function.Injective (eEmb K) := by
  intro x y h
  apply mixedEmbedding_injective K
  have h2 := (mixedEmbedding.euclidean.toMixed K).symm.injective.eq_iff.mp
    (by simpa only [eEmb] using h)
  exact (scaleMixed K).injective h2

/-- The ideal lattice is exactly the `ℤ`-linear image of `I`:
`idealLattice K I = (I.restrictScalars ℤ).map eEmbHom`. -/
theorem idealLattice_eq_map (I : FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice K I =
      Submodule.map (eEmbHom K).toIntLinearMap ((I : Submodule (𝓞 K) K).restrictScalars ℤ) := by
  rw [idealLattice, ← Submodule.span_eq
    (Submodule.map (eEmbHom K).toIntLinearMap ((I : Submodule (𝓞 K) K).restrictScalars ℤ))]
  congr 1

theorem mem_idealLattice_iff (I : FractionalIdeal (𝓞 K)⁰ K) (v : minkowskiSpace K) :
    v ∈ idealLattice K I ↔ ∃ a ∈ (I : Submodule (𝓞 K) K), eEmb K a = v := by
  rw [idealLattice_eq_map]
  simp only [Submodule.mem_map, Submodule.restrictScalars_mem, AddMonoidHom.coe_toIntLinearMap,
    eEmbHom_apply]

/-- **Trace-dual identification, `K`-rational form** (the standard treatment).
A field element `b : K` pairs integrally under
the symmetric trace form `T` with every element of the ideal `𝔞` iff `b` lies in
the dual ideal `(𝔞𝔡)⁻¹ = dualIdeal K 𝔞`. This is the element-level core of the
trace-dual statement: `traceForm_mixedEmbedding`
(`T(mixedEmbedding b, a) = (algebraMap ℚ ℝ)(Tr_{K/ℚ}(b·a))`) turns the integrality
into `Tr(b·a) ∈ ℤ`, which by `FractionalIdeal.mem_dual` and `dualIdeal_eq_dual` is
exactly membership of `b` in `dualIdeal K 𝔞`. NB: this is the *symmetric* trace
form, with no complex conjugation — the conjugation twist lives in the passage
from the Hermitian Minkowski inner product to `T` (`dual_idealLattice`). -/
theorem traceForm_mixedEmbedding_int_iff_mem_dualIdeal
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (b : K) :
    (∀ a ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ,
        traceForm K (mixedEmbedding K b) a = (k : ℝ)) ↔
      b ∈ (dualIdeal K 𝔞 : Submodule (𝓞 K) K) := by
  rw [FractionalIdeal.mem_coe, ← dualIdeal_eq_dual K 𝔞,
    FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr hne)]
  refine forall₂_congr fun a ha => ?_
  rw [traceForm_mixedEmbedding, Algebra.traceForm_apply, RingHom.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply FaithfulSMul.algebraMap_injective ℚ ℝ
    rw [hk, ← IsScalarTower.algebraMap_apply ℤ ℚ ℝ]
    simp
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, ← IsScalarTower.algebraMap_apply ℤ ℚ ℝ]
    simp

/-- The point `eEmbℝ η` lies in the ideal lattice `Λ(I)` iff `η` is the
`mixedEmbedding` image of some `b ∈ I`. (`eEmb K b = eEmbℝ K (mixedEmbedding K b)`
and `eEmbℝ` is a linear iso, so this is `mem_idealLattice_iff` transported through
`eEmbℝ`.) -/
theorem eEmbℝ_mem_idealLattice_iff (I : FractionalIdeal (𝓞 K)⁰ K) (η : mixedSpace K) :
    eEmbℝ K η ∈ idealLattice K I ↔
      ∃ b ∈ (I : Submodule (𝓞 K) K), mixedEmbedding K b = η := by
  rw [mem_idealLattice_iff]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  rw [← eEmbℝ_mixedEmbedding, (eEmbℝ K).injective.eq_iff]

/-- **The trace form as an `ℝ`-bilinear functional in its mixed-space argument.**
For fixed `η : K_ℝ`, `traceFormLin K η : K_ℝ →ₗ[ℝ] ℝ` is the `ℝ`-linear map
`χ ↦ ∑_{w real} η.1 w · χ.1 w + 2 ∑_{w cplx} Re(η.2 w · χ.2 w)`. It agrees with
`traceForm K η` after applying `mixedEmbedding` (`traceFormLin_mixedEmbedding`),
and is the bookkeeping device for the `ℚ`-rationality / nondegeneracy argument:
the underlying real symmetric form is nondegenerate, so a
point that pairs to `0` with every lattice basis vector is `0`. -/
def traceFormLin (η : mixedSpace K) : mixedSpace K →ₗ[ℝ] ℝ where
  toFun χ := (∑ w : {w : InfinitePlace K // w.IsReal}, η.1 w * χ.1 w) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex}, (η.2 w * χ.2 w).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Complex.add_re,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    have h1 : ∀ w : {w : InfinitePlace K // w.IsReal},
        η.1 w * (c • x).1 w = c * (η.1 w * x.1 w) := by
      intro w; show η.1 w * (c * x.1 w) = _; ring
    have h2 : ∀ w : {w : InfinitePlace K // w.IsComplex},
        (η.2 w * (c • x).2 w).re = c * (η.2 w * x.2 w).re := by
      intro w; show (η.2 w * (c • x.2 w)).re = _
      rw [mul_smul_comm, Complex.smul_re, smul_eq_mul]
    simp only [RingHom.id_apply, smul_eq_mul, h1, h2, ← Finset.mul_sum]
    ring

@[simp] theorem traceFormLin_apply (η χ : mixedSpace K) :
    traceFormLin K η χ =
      (∑ w : {w : InfinitePlace K // w.IsReal}, η.1 w * χ.1 w) +
        2 * ∑ w : {w : InfinitePlace K // w.IsComplex}, (η.2 w * χ.2 w).re := rfl

theorem traceFormLin_mixedEmbedding (η : mixedSpace K) (a : K) :
    traceFormLin K η (mixedEmbedding K a) = traceForm K η a := rfl

/-- `traceForm K η` is additive (here: respects subtraction) in its `K_ℝ`
argument. Used to compare `η` with `mixedEmbedding K b` in the fullness
argument. -/
theorem traceForm_sub_left (η η' : mixedSpace K) (a : K) :
    traceForm K (η - η') a = traceForm K η a - traceForm K η' a := by
  simp only [traceForm, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_mul, Complex.sub_re,
    Finset.sum_sub_distrib]
  ring

/-- `traceForm K η` scales by a natural number under the corresponding scaling of
its field argument: `T(η, n·a) = n·T(η, a)`. (`traceForm` factors through the
ring hom `mixedEmbedding` and the `ℝ`-linear `traceFormLin`, both of which
respect `n • ·`.) -/
theorem traceForm_natCast_mul (η : mixedSpace K) (n : ℕ) (a : K) :
    traceForm K η ((n : K) * a) = n * traceForm K η a := by
  rw [← traceFormLin_mixedEmbedding, ← nsmul_eq_mul, map_nsmul, map_nsmul,
    traceFormLin_mixedEmbedding, nsmul_eq_mul]

/-- **Nondegeneracy of the real trace form** (the analytic input to the
fullness/ℚ-rationality argument). A point `ζ : K_ℝ` whose
trace-form pairing vanishes against every integral-basis element is `0`. Proof:
the pairings against `mixedEmbedding (integralBasis K i)` are the values of the
`ℝ`-linear functional `traceFormLin K ζ` on the `ℝ`-basis `latticeBasis K`, so
the functional vanishes identically; evaluating at the "conjugate" witness
`(ζ.1, conj ζ.2)` gives `∑ (ζ.1 w)² + 2 ∑ ‖ζ.2 w‖² = 0`, forcing `ζ = 0`. -/
theorem traceForm_eq_zero_of_forall_integralBasis (ζ : mixedSpace K)
    (hz : ∀ i, traceForm K ζ (integralBasis K i) = 0) : ζ = 0 := by
  have hlin : traceFormLin K ζ = 0 := by
    refine (latticeBasis K).ext (fun i => ?_)
    rw [latticeBasis_apply, traceFormLin_mixedEmbedding]
    simpa using hz i
  have hval : (∑ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w * ζ.1 w) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (ζ.2 w) = 0 := by
    have hv := LinearMap.congr_fun hlin
      (⟨ζ.1, fun w => starRingEnd ℂ (ζ.2 w)⟩ : mixedSpace K)
    rw [LinearMap.zero_apply, traceFormLin_apply] at hv
    rw [← hv]
    have hre : ∀ w : {w : InfinitePlace K // w.IsComplex},
        Complex.normSq (ζ.2 w) = (ζ.2 w * starRingEnd ℂ (ζ.2 w)).re := by
      intro w; rw [Complex.mul_conj, Complex.ofReal_re]
    simp_rw [hre]
  have hA : (0 : ℝ) ≤ ∑ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w * ζ.1 w :=
    Finset.sum_nonneg (fun w _ => mul_self_nonneg _)
  have hB : (0 : ℝ) ≤ ∑ w : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (ζ.2 w) :=
    Finset.sum_nonneg (fun w _ => Complex.normSq_nonneg _)
  have hA0 : (∑ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w * ζ.1 w) = 0 := by linarith
  have hB0 : (∑ w : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (ζ.2 w)) = 0 := by
    linarith
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w = 0 := by
    intro w
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => mul_self_nonneg (ζ.1 w))).mp hA0 w
      (Finset.mem_univ w)
    exact mul_self_eq_zero.mp this
  have hcplx : ∀ w : {w : InfinitePlace K // w.IsComplex}, ζ.2 w = 0 := by
    intro w
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun w _ => Complex.normSq_nonneg (ζ.2 w))).mp hB0 w (Finset.mem_univ w)
    exact Complex.normSq_eq_zero.mp this
  ext w
  · exact hreal w
  · rw [Prod.snd_zero, Pi.zero_apply]; rw [hcplx w]

/-- **Trace-dual identification, full `K_ℝ` form** (the standard treatment).
An arbitrary
point `η : K_ℝ` pairs integrally under the symmetric trace form `T` with every
element of `𝔞` iff `eEmbℝ η` lies in the lattice `Λ((𝔞𝔡)⁻¹)` of the dual ideal,
equivalently iff `η = mixedEmbedding K b` for some `b ∈ dualIdeal K 𝔞`.

This is the trace-dual statement that `dual_idealLattice` consumes after writing
the Minkowski inner product as `T(cξ, ·)` (`inner_eEmbℝ_eq_traceForm_conjMixed`):
taking `η = conjMixed K ξ` gives `eEmbℝ (conjMixed ξ) = conjMink (eEmbℝ ξ)`
(`conjMink_apply`), the conjugation-twisted dual lattice membership.

The reverse direction is `traceForm_mixedEmbedding_int_iff_mem_dualIdeal`. The
forward ("fullness") direction — every `η` integral against the full-rank lattice
`mixedEmbedding '' 𝔞` is rational, i.e. `η ∈ mixedEmbedding '' K`, hence in
`mixedEmbedding '' dualIdeal` — is a standalone lattice-duality / `ℚ`-rationality
argument. -/
theorem traceForm_int_iff_eEmbℝ_mem_dualLattice
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (η : mixedSpace K) :
    (∀ a ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ, traceForm K η a = (k : ℝ)) ↔
      eEmbℝ K η ∈ idealLattice K (dualIdeal K 𝔞) := by
  rw [eEmbℝ_mem_idealLattice_iff]
  constructor
  · intro h
    classical
    -- A nonzero rational integer `m ∈ 𝔞` (the absolute norm), so that
    -- `m · (integral basis) ⊆ 𝔞` and we can extract rational pairings.
    set m : ℕ := Ideal.absNorm 𝔞 with hm
    have hm0 : (m : ℝ) ≠ 0 := by
      have : 𝔞 ≠ ⊥ := hne
      exact_mod_cast (Ideal.absNorm_eq_zero_iff (I := 𝔞)).not.mpr this
    have hmem : (m : 𝓞 K) ∈ 𝔞 := Ideal.absNorm_mem 𝔞
    -- Rationality: `T(η, integralBasis i) = algebraMap (q i)` for `q i ∈ ℚ`.
    have hq : ∀ i, ∃ q : ℚ, traceForm K η (integralBasis K i) = algebraMap ℚ ℝ q := by
      intro i
      have hmemf : ((m : K) * integralBasis K i) ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
        have he : ((m : K) * integralBasis K i)
            = algebraMap (𝓞 K) K ((m : 𝓞 K) * RingOfIntegers.basis K i) := by
          rw [map_mul, integralBasis_apply, map_natCast]
        rw [he]
        exact FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰
          (Ideal.mul_mem_right (RingOfIntegers.basis K i) 𝔞 hmem)
      obtain ⟨k, hk⟩ := h _ hmemf
      refine ⟨(k : ℚ) / (m : ℚ), ?_⟩
      rw [traceForm_natCast_mul] at hk
      have : traceForm K η (integralBasis K i) = (k : ℝ) / (m : ℝ) := by
        field_simp at hk ⊢; linarith [hk]
      rw [this, map_div₀, map_intCast, map_natCast]
    choose q hqeq using hq
    -- Construct `b ∈ K` with the prescribed pairings via the trace-dual basis.
    set b : K := ∑ i, q i • (integralBasis K).traceDual i with hb
    have htr : ∀ j, Algebra.trace ℚ K (b * integralBasis K j) = q j := by
      intro j
      rw [hb, Finset.sum_mul, map_sum]
      have : ∀ i, Algebra.trace ℚ K ((q i • (integralBasis K).traceDual i) * integralBasis K j)
          = q i • (if j = i then (1 : ℚ) else 0) := by
        intro i
        rw [smul_mul_assoc, map_smul, (integralBasis K).trace_traceDual_mul]
      rw [Finset.sum_congr rfl (fun i _ => this i)]
      simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ j q]
      simp
    -- `mixedEmbedding K b` and `η` have equal trace pairings against the basis.
    have hpair : ∀ j, traceForm K (mixedEmbedding K b) (integralBasis K j)
        = traceForm K η (integralBasis K j) := by
      intro j
      rw [traceForm_mixedEmbedding, ← Algebra.traceForm_apply, Algebra.traceForm_apply,
        htr j, hqeq j]
    -- Nondegeneracy forces `mixedEmbedding K b = η`.
    have hbη : mixedEmbedding K b = η := by
      have := traceForm_eq_zero_of_forall_integralBasis K (mixedEmbedding K b - η)
        (fun j => by rw [traceForm_sub_left, hpair j, sub_self])
      rwa [sub_eq_zero] at this
    refine ⟨b, ?_, hbη⟩
    -- `b ∈ dualIdeal K 𝔞` from the integrality hypothesis transported through `hbη`.
    refine (traceForm_mixedEmbedding_int_iff_mem_dualIdeal K 𝔞 hne b).mp ?_
    intro a ha
    rw [hbη]
    exact h a ha
  · rintro ⟨b, hb, rfl⟩
    exact (traceForm_mixedEmbedding_int_iff_mem_dualIdeal K 𝔞 hne b).mpr hb

/-- **Duality of the lattices, Hermitian Minkowski dual** (the standard treatment corrected for the complex-conjugation twist). With respect to the
Minkowski inner product (which is the
*Hermitian* form `Re ∑_σ conj(σx)·σy`, see `inner_eEmbℝ_eq_traceForm_conjMixed`),
a point `y : K_ℝ` lies in the dual lattice of `Λ(𝔞)` (its inner product with
every point of `Λ(𝔞)` is an integer) iff its conjugate `conjMink K y` lies in
`Λ((𝔞𝔡)⁻¹)`. The naive (untwisted) form `y ∈ Λ((𝔞𝔡)⁻¹)` is **false for
non-CM `K`** (e.g. `K = ℚ(∛2)`): the symmetric trace-form duality identifies the
trace-dual with `Λ((𝔞𝔡)⁻¹)`, but the Hermitian inner product introduces the
conjugation `conjMink`, which preserves `Λ((𝔞𝔡)⁻¹)` setwise only in the CM /
totally-real case. Since `conjMink` is an involution this is equivalent to
`y ∈ conjMink '' Λ((𝔞𝔡)⁻¹)`. -/
theorem dual_idealLattice (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    (y : minkowskiSpace K) :
    (∀ x ∈ idealLattice K (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ,
        (inner ℝ y x : ℝ) = k) ↔
      conjMink K y ∈ idealLattice K (dualIdeal K 𝔞) := by
  -- Write `y = eEmbℝ ξ` with `ξ = eEmbℝ⁻¹ y`.
  set ξ := (eEmbℝ K).symm y with hξ
  have hy : y = eEmbℝ K ξ := by rw [hξ, ContinuousLinearEquiv.apply_symm_apply]
  -- The conjugate `conjMink y` is `eEmbℝ (conjMixed ξ)`.
  have hconj : conjMink K y = eEmbℝ K (conjMixed K ξ) := by
    rw [conjMink_apply, ← hξ]
  -- Reduce the lattice quantifier to generators, then identify with the dual lattice.
  rw [forall_inner_int_iff_gens, hconj,
    ← traceForm_int_iff_eEmbℝ_mem_dualLattice K 𝔞 hne]
  -- Bridge each generator condition: `⟪y, eEmb a⟫ = T(conjMixed ξ, a)`.
  refine forall_congr' fun a => ?_
  rw [FractionalIdeal.mem_coe]
  refine imp_congr_right fun _ => ?_
  rw [hy, inner_eEmbℝ_eq_traceForm_conjMixed]

/-- **Dual lattice as a submodule equality, Hermitian Minkowski dual** (the standard treatment, corrected for the conjugation twist).
The inner-product dual lattice of `Λ(𝔞)` is the conjugate
`conjMink '' Λ((𝔞𝔡)⁻¹)`, written as the image submodule
`(idealLattice K (dualIdeal K 𝔞)).map (conjMink K)`; `conjMink` is an isometric
involution preserving covolume and the Gaussian sum, so the transformation law
is unaffected. The bridge
is `Submodule.mem_one` for `(1 : Submodule ℤ ℝ)` (its elements are the integer
multiples of `1`, i.e. `∃ k : ℤ, (k : ℝ) = r`), matching the `∃ k : ℤ, ⟪y,x⟫ = k`
condition of `dual_idealLattice`; the inner-product argument order already
agrees (`⟪y, x⟫` with `y` dual, `x ∈ Λ(𝔞)`). -/
theorem dualLattice_idealLattice (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    PoissonSummation.dualLattice (idealLattice K (𝔞 : FractionalIdeal (𝓞 K)⁰ K))
      = (idealLattice K (dualIdeal K 𝔞)).map
          ((conjMink K).toLinearEquiv.restrictScalars ℤ).toLinearMap := by
  refine Submodule.ext fun y => ?_
  rw [PoissonSummation.mem_dualLattice, Submodule.mem_map_equiv]
  -- `((conjMink K).toLinearEquiv.restrictScalars ℤ).symm y` equals `conjMink K y`
  -- since `conjMink` is an involution (`conjMink_symm_apply`); the underlying
  -- function is unchanged by `toLinearEquiv`/`restrictScalars`.
  have key : ((conjMink K).toLinearEquiv.restrictScalars ℤ).symm y = conjMink K y := by
    rw [← conjMink_symm_apply]; rfl
  rw [key, ← dual_idealLattice K 𝔞 hne y]
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨k, hk⟩ := Submodule.mem_one.mp (h x hx)
    exact ⟨k, by simpa using hk.symm⟩
  · obtain ⟨k, hk⟩ := h x hx
    exact Submodule.mem_one.mpr ⟨k, by simpa using hk.symm⟩

/-- The Minkowski ideal lattice `Λ(I)` is the image of the mixed-space ideal
lattice `mixedEmbedding.idealLattice K I'` under the linear iso `eEmbℝ`,
phrased as a `ZLattice.comap` along `eEmbℝ.symm` so the `instIsZLatticeComap`
instance applies. For `v : minkowskiSpace K`, `v ∈ Λ(I)` iff its preimage
`eEmbℝ.symm v` lies in the mixed-space lattice (both reduce to `∃ a ∈ I, …`).
the standard treatment: `Λ(I)` is a full discrete lattice. -/
theorem idealLattice_eq_comap (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    idealLattice K I =
      ZLattice.comap ℝ (mixedEmbedding.idealLattice K (Units.mk0 I hI))
        (eEmbℝ K).symm.toLinearMap := by
  ext v
  rw [mem_idealLattice_iff]
  rw [show ZLattice.comap ℝ (mixedEmbedding.idealLattice K (Units.mk0 I hI))
        (eEmbℝ K).symm.toLinearMap
      = (mixedEmbedding.idealLattice K (Units.mk0 I hI)).comap
          ((eEmbℝ K).symm.toLinearMap.restrictScalars ℤ) from rfl,
    Submodule.mem_comap]
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [LinearMap.restrictScalars_apply, ← eEmbℝ_mixedEmbedding]
    exact (ContinuousLinearEquiv.symm_apply_apply (eEmbℝ K) _).symm
  · rintro ⟨a, ha, hav⟩
    refine ⟨a, ha, ?_⟩
    have : eEmbℝ K (mixedEmbedding K a) = eEmbℝ K ((eEmbℝ K).symm v) := by
      rw [hav]; rfl
    rwa [eEmbℝ_mixedEmbedding, ContinuousLinearEquiv.apply_symm_apply] at this

/-- `Λ(I)` is discrete in `minkowskiSpace K` for nonzero `I` (the standard treatment): it is the image of the mixed-space ideal lattice under `eEmbℝ`. -/
theorem discreteTopology_idealLattice (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    DiscreteTopology (idealLattice K I) := by
  rw [idealLattice_eq_comap K I hI]
  infer_instance

/-- `Λ(I)` is a full `ℤ`-lattice of `minkowskiSpace K` for nonzero `I`
(the standard treatment): the image of the mixed-space ideal lattice under the
linear iso `eEmbℝ`. This is what `tsum_eq_tsum_fourier` needs. -/
theorem isZLattice_idealLattice (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    [DiscreteTopology (idealLattice K I)] :
    IsZLattice ℝ (idealLattice K I) where
  span_top := by
    rw [idealLattice_eq_comap K I hI]
    exact (inferInstance : IsZLattice ℝ (ZLattice.comap ℝ
      (mixedEmbedding.idealLattice K (Units.mk0 I hI))
      (eEmbℝ K).symm.toLinearMap)).span_top

/-- The equivalence `I ≃ Λ(I)` induced by `eEmb` (injective, and surjective onto
the lattice by `mem_idealLattice_iff`). -/
def idealLatticeEquiv (I : FractionalIdeal (𝓞 K)⁰ K) :
    (I : Submodule (𝓞 K) K) ≃ idealLattice K I :=
  Equiv.ofBijective
    (fun a => ⟨eEmb K (a : K), (mem_idealLattice_iff K I _).mpr ⟨a, a.2, rfl⟩⟩)
    (by
      constructor
      · intro a b h
        exact Subtype.ext (eEmb_injective K (Subtype.ext_iff.mp h))
      · rintro ⟨v, hv⟩
        obtain ⟨a, ha, rfl⟩ := (mem_idealLattice_iff K I v).mp hv
        exact ⟨⟨a, ha⟩, rfl⟩)


/-! ## The theta transformation law (the standard treatment) -/



/-! ## The multiplicative lattice theta kernel over `K_ℝ^*` and its inversion law

This is the *kernel-level* input that the Mellin/functional-equation step
(`completedPartialZeta`) actually consumes. The
relevant object is not the scalar `theta` (a function of a single real `t > 0`),
but the **multiplicative** lattice kernel obtained by summing the Minkowski
Gaussian over the nonzero ideal elements, acting *multiplicatively* on
`K_ℝ = mixedSpace K` (`a` acts as `x ↦ x · σ(a)` via the ring map
`mixedEmbedding K`). These definitions previously lived in
`DedekindZeta/Statements.lean`; they are the natural responsibility of the
theta layer (the standard treatment), so they live here and `Statements.lean`
imports them.

The transformation law needed is the inversion `x ↦ x⁻¹` of `K_ℝ^*`, which is
the standard treatment applied to the lattice `x · Λ(𝔞)`: Poisson summation
for the self-dual Minkowski Gaussian gives

    ∑_{λ ∈ Λ} g(x · λ) = 1 / (|N(x)| · vol(Λ)) · ∑_{μ ∈ Λ*} g(x⁻¹ · μ),

so, since the dual lattice of `Λ(𝔞)` is `Λ((𝔞𝔡)⁻¹)` (`dual_idealLattice`) and
`vol(Λ(𝔞)) = 𝔑(𝔞)·√|d_K|` (`covolume`), substituting `x ↦ x⁻¹` (and using
`N(x⁻¹) = N(x)⁻¹`) yields

    Θ(𝔞, x⁻¹) = (|N(x)| / vol(Λ(𝔞))) · Θ((𝔞𝔡)⁻¹, x),

with the *same* covolume constant `t^{n/2}/vol` of the scalar
`theta_transformation` (there `t^{n/2}` is `√N(z/i)`; here it is `N(x)`, the
determinant of the multiplicative scaling by `x`). -/

open scoped Real in
/-- The Minkowski Gaussian `g(x) = exp(-π ⟨x,x⟩)` on `K_ℝ = mixedSpace K`, where
`⟨x,x⟩ = ∑_w mult w · ‖x_w‖²` is the Minkowski quadratic form (a complex place
contributes `2|x_w|²` via `mult w = 2`). This is the `t = 1` Gaussian whose
lattice sum is the theta series of the standard treatment. Moved here from
`Statements.lean` (theta-layer responsibility). -/
def mixedGaussian (x : mixedEmbedding.mixedSpace K) : ℝ :=
  Real.exp (-Real.pi *
    ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w x ^ 2)

/-- The **fractional-ideal theta kernel** over `K_ℝ`: the sum of the Minkowski
Gaussian over the nonzero elements of a fractional ideal `I`, acting
*multiplicatively* on `x ∈ K_ℝ` (`a ∈ I` acts as `x ↦ x · σ(a)`). This is the
general form needed to state the inversion law, whose dual side is the
*fractional* ideal `(𝔞𝔡)⁻¹` (the standard treatment). -/
def mixedThetaKernel (I : FractionalIdeal (𝓞 K)⁰ K)
    (x : mixedEmbedding.mixedSpace K) : ℂ :=
  ∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
    (mixedGaussian K (x * mixedEmbedding K (a : K)) : ℂ)

/-- The **lattice theta kernel** of a nonzero integral ideal `𝔞` (the standard treatment): the sum of the Minkowski Gaussian over the nonzero elements of `𝔞`, acting
multiplicatively on `K_ℝ`. Its multiplicative Mellin transform over `K_ℝ^*`
extracts the absolute norms `N(a)`. Moved here from `Statements.lean`; the body
is identical (so `DedekindZeta.completedPartialZeta` is unchanged). -/
def idealThetaKernel (𝔞 : Ideal (𝓞 K)) (x : mixedEmbedding.mixedSpace K) : ℂ :=
  ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
    (mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)

/-- The integral kernel of `𝔞` is the fractional kernel of `(𝔞 : FractionalIdeal)`:
the two index sets `{a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0}` and
`{a : K // a ∈ (𝔞 : FractionalIdeal) ∧ a ≠ 0}` are in canonical bijection via
the embedding `𝓞 K ↪ K`, and the summands agree. This bridges the integral
kernel used by `completedPartialZeta` to the fractional kernel in which the
inversion law is most naturally stated. -/
theorem idealThetaKernel_eq_mixed (𝔞 : Ideal (𝓞 K))
    (x : mixedEmbedding.mixedSpace K) :
    idealThetaKernel K 𝔞 x = mixedThetaKernel K (𝔞 : FractionalIdeal (𝓞 K)⁰ K) x := by
  -- The integral-closure embedding `𝓞 K ↪ K` restricts to a bijection between
  -- the nonzero elements of `𝔞` and the nonzero elements of the coerced
  -- fractional ideal: surjectivity is `FractionalIdeal.mem_coeIdeal`
  -- (every element of `↑𝔞` is `algebraMap` of an element of `𝔞`), and
  -- injectivity is `RingOfIntegers.coe_injective`.
  set I : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hI
  -- For every element `b` of the coerced ideal there is an integral preimage in `𝔞`.
  have key : ∀ b : K, b ∈ (I : Submodule (𝓞 K) K) → ∃ a : 𝓞 K, a ∈ 𝔞 ∧ (a : K) = b := by
    intro b hb
    rw [FractionalIdeal.mem_coe, hI, FractionalIdeal.mem_coeIdeal] at hb
    obtain ⟨a, ha, hab⟩ := hb
    exact ⟨a, ha, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hab⟩
  have hmem : ∀ a : 𝓞 K, a ∈ 𝔞 → (a : K) ∈ (I : Submodule (𝓞 K) K) := by
    intro a ha
    rw [FractionalIdeal.mem_coe, hI, RingOfIntegers.coe_eq_algebraMap]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ ha
  let e : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} ≃
      {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} :=
  { toFun := fun a => ⟨(a.1 : K), hmem a.1 a.2.1, RingOfIntegers.coe_ne_zero_iff.mpr a.2.2⟩
    invFun := fun b => ⟨(key b.1 b.2.1).choose, (key b.1 b.2.1).choose_spec.1, by
      intro h0
      apply b.2.2
      rw [← (key b.1 b.2.1).choose_spec.2, h0]; simp⟩
    left_inv := fun a => by
      apply Subtype.ext
      apply RingOfIntegers.coe_injective
      simpa using (key (a.1 : K) (hmem a.1 a.2.1)).choose_spec.2
    right_inv := fun b => by
      apply Subtype.ext
      simpa using (key b.1 b.2.1).choose_spec.2 }
  rw [idealThetaKernel, mixedThetaKernel, ← Equiv.tsum_eq e]
  rfl

/-- **The Minkowski quadratic form is the squared Minkowski norm** (general
point). Factored out of `mixedGaussian_eq`: for every `x : K_ℝ`,
`‖toMinkowski K x‖² = ∑_w mult w · normAtPlace w x²`. Used to dominate the
lattice Gaussian sum by the convergent theta series `summable_theta`. -/
theorem norm_toMinkowski_sq (x : mixedEmbedding.mixedSpace K) :
    ‖toMinkowski K x‖ ^ 2 =
      ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w x ^ 2 := by
  classical
  have hre : ∀ z : ℂ, ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hinner : (inner ℝ (toMinkowski K x) (toMinkowski K x) : ℝ) =
      (∑ w : {w : InfinitePlace K // w.IsReal}, (x.1 w) * (x.1 w)) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
          ((starRingEnd ℂ) (x.2 w) * (x.2 w)).re := by
    rw [toMinkowski, WithLp.prod_inner_apply,
        show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
            (mixedEmbedding.euclidean.toMixed K).symm) x)).fst
            = WithLp.toLp 2 (scaleMixed K x).1 from rfl,
        show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
            (mixedEmbedding.euclidean.toMixed K).symm) x)).snd
            = WithLp.toLp 2 (scaleMixed K x).2 from rfl]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, scaleMixed,
      ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_refl', id_eq,
      ContinuousLinearEquiv.smulLeft_apply_apply, real_inner_eq_re_inner ℂ]
    rw [Finset.mul_sum]
    have hcplx : ∀ w : {w : InfinitePlace K // w.IsComplex},
        RCLike.re ((sqrtTwo • x.2) w * (starRingEnd ℂ) ((sqrtTwo • x.2) w))
          = 2 * ((starRingEnd ℂ) (x.2 w) * x.2 w).re := by
      intro w
      have hnorm : ‖(sqrtTwo • x.2) w‖ = Real.sqrt 2 * ‖x.2 w‖ := by
        rw [Pi.smul_apply, Units.smul_def, _root_.norm_smul, sqrtTwo, Units.val_mk0,
          Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
      rw [RCLike.mul_conj, RCLike.re_ofReal_pow, hnorm, mul_pow,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hre]
    rw [Finset.sum_congr rfl (fun w (_ : w ∈ Finset.univ) => hcplx w)]
  rw [← real_inner_self_eq_norm_sq, hinner, InfinitePlace.sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [InfinitePlace.mult_isReal, normAtPlace_apply_of_isReal w.2]
    push_cast; rw [Real.norm_eq_abs, sq_abs]; ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [InfinitePlace.mult_isComplex, normAtPlace_apply_of_isComplex w.2, hre]
    push_cast; ring

/-- **Continuity of the Minkowski Gaussian** `x ↦ mixedGaussian K x = exp(-π ⟨x,x⟩)`. -/
theorem continuous_mixedGaussian : Continuous (mixedGaussian K) := by
  unfold mixedGaussian
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  refine continuous_finset_sum _ (fun w _ => ?_)
  exact continuous_const.mul ((continuous_normAtPlace w).pow 2)

/-- **Continuity of the fractional theta kernel** `x ↦ mixedThetaKernel K I x` on
the open nonzero-norm locus `{x | N(x) ≠ 0}` (the exact Gaussian-convergence
region: on the zero-norm locus the lattice family is non-summable).

The kernel is the lattice sum `∑'_{a} g(x · σ(a))` of the (continuous) Minkowski
Gaussian over the nonzero elements of `I`.  Working locally at a point `x₀` with
`N(x₀) ≠ 0`: a closed ball `B ⊆ {N ≠ 0}` is compact, so each `normAtPlace w` is
bounded below by some `δ > 0` on `B`; multiplicativity gives, for `x ∈ B`,
`∑_w mult w · normAtPlace w (x·σ(a))² ≥ δ²‖eEmb a‖²`, hence each summand is
dominated by `exp(-π δ²‖eEmb a‖²)`, which is summable (`summable_theta`).
`continuousOn_tsum` then gives continuity on `B`, hence `ContinuousAt x₀`
(the standard treatment). -/
theorem continuousOn_mixedThetaKernel (I : FractionalIdeal (𝓞 K)⁰ K) :
    ContinuousOn (mixedThetaKernel K I)
      {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
  classical
  rcases eq_or_ne I 0 with hI | hI
  · -- `I = 0`: the index set is empty, so the kernel is the constant `0`.
    subst hI
    haveI : IsEmpty {a : K // a ∈ ((0 : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K) ∧ a ≠ 0} := by
      refine ⟨?_⟩
      rintro ⟨a, ha, ha0⟩
      rw [FractionalIdeal.coe_zero, Submodule.mem_bot] at ha
      exact ha0 ha
    have hzero : mixedThetaKernel K (0 : FractionalIdeal (𝓞 K)⁰ K) = fun _ => (0 : ℂ) := by
      funext x; rw [mixedThetaKernel, tsum_empty]
    rw [hzero]; exact continuousOn_const
  · -- `I ≠ 0`: prove `ContinuousAt` at each point of the open locus.
    have hopen : IsOpen {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
      isOpen_compl_singleton.preimage (mixedEmbedding.continuous_norm K)
    intro x₀ hx₀
    refine ContinuousAt.continuousWithinAt ?_
    -- A closed ball around `x₀` contained in the open locus.
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen x₀ hx₀
    set B := Metric.closedBall x₀ (ε / 2) with hBdef
    have hBs : B ⊆ {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
      (Metric.closedBall_subset_ball (by linarith)).trans hsub
    have hBcpt : IsCompact B := isCompact_closedBall x₀ (ε / 2)
    have hBne : B.Nonempty := ⟨x₀, Metric.mem_closedBall_self (by positivity)⟩
    -- Each `normAtPlace w` is bounded below by a positive constant on `B`.
    have hpos : ∀ w : InfinitePlace K, ∃ d : ℝ, 0 < d ∧ ∀ x ∈ B, d ≤ normAtPlace w x := by
      intro w
      obtain ⟨xm, hxm, hmin⟩ :=
        hBcpt.exists_isMinOn hBne (continuous_normAtPlace w).continuousOn
      refine ⟨normAtPlace w xm, ?_, fun x hx => isMinOn_iff.mp hmin x hx⟩
      exact lt_of_le_of_ne (normAtPlace_nonneg w xm)
        (Ne.symm (mixedEmbedding.norm_ne_zero_iff.mp (hBs hxm) w))
    choose d hd_pos hd_le using hpos
    obtain ⟨δ, hδ_pos, hδ_le⟩ :
        ∃ δ : ℝ, 0 < δ ∧ ∀ (w : InfinitePlace K), ∀ x ∈ B, δ ≤ normAtPlace w x := by
      refine ⟨Finset.univ.inf' Finset.univ_nonempty d, ?_, ?_⟩
      · exact (Finset.lt_inf'_iff _).mpr (fun w _ => hd_pos w)
      · intro w x hx
        exact le_trans (Finset.inf'_le d (Finset.mem_univ w)) (hd_le w x hx)
    -- Summability of the dominating function (subtype of the lattice theta series).
    have hδ2 : 0 < δ ^ 2 := by positivity
    have hinj : Function.Injective
        (fun a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} =>
          (⟨a.1, a.2.1⟩ : (I : Submodule (𝓞 K) K))) := by
      intro a b h
      apply Subtype.ext
      simpa using congrArg Subtype.val h
    -- The majorant `∑' a, exp(-πδ²‖eEmb a‖²)` is summable: it is the lattice theta
    -- series of `summable_theta` restricted along the injection `incl`.  We align
    -- the result with `(a : K)` via `congrArg` (a *syntactic* congruence on the
    -- `K`-coercion), so unification never descends through `eEmb`/the norm (which
    -- would blow up `whnf` because the two subtype coercions differ).
    have hu : Summable (fun a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} =>
        Real.exp (-Real.pi * δ ^ 2 * ‖eEmb K (a : K)‖ ^ 2)) := by
      refine ((summable_theta K hI hδ2).comp_injective hinj).congr (fun a => ?_)
      exact congrArg (fun z : K => Real.exp (-Real.pi * δ ^ 2 * ‖eEmb K z‖ ^ 2))
        (rfl : ((⟨a.1, a.2.1⟩ : (I : Submodule (𝓞 K) K)) : K) = (a : K))
    -- Each summand is continuous (on `B`).
    have hf_cont : ∀ a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
        ContinuousOn (fun x => (mixedGaussian K (x * mixedEmbedding K (a : K)) : ℂ)) B := by
      intro a
      refine Continuous.continuousOn ?_
      exact Complex.continuous_ofReal.comp
        ((continuous_mixedGaussian K).comp (continuous_id.mul continuous_const))
    -- The uniform dominating bound on `B`.
    have hbound : ∀ (a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) x, x ∈ B →
        ‖(mixedGaussian K (x * mixedEmbedding K (a : K)) : ℂ)‖
          ≤ Real.exp (-Real.pi * δ ^ 2 * ‖eEmb K (a : K)‖ ^ 2) := by
      intro a x hx
      have hg0 : 0 ≤ mixedGaussian K (x * mixedEmbedding K (a : K)) := by
        rw [mixedGaussian]; positivity
      have hQ : ‖eEmb K (a : K)‖ ^ 2
          = ∑ w : InfinitePlace K,
              (InfinitePlace.mult w : ℝ) * normAtPlace w (mixedEmbedding K (a : K)) ^ 2 := by
        rw [← eEmbℝ_mixedEmbedding K (a : K)]
        exact norm_toMinkowski_sq K (mixedEmbedding K (a : K))
      have key : δ ^ 2 * ‖eEmb K (a : K)‖ ^ 2
          ≤ ∑ w : InfinitePlace K,
              (InfinitePlace.mult w : ℝ) * normAtPlace w (x * mixedEmbedding K (a : K)) ^ 2 := by
        rw [hQ, Finset.mul_sum]
        refine Finset.sum_le_sum (fun w _ => ?_)
        have hδle : δ ≤ normAtPlace w x := hδ_le w x hx
        have hsq : δ ^ 2 ≤ normAtPlace w x ^ 2 := by
          have := normAtPlace_nonneg w x
          nlinarith [hδ_pos.le, hδle, this]
        have hmult : (0 : ℝ) ≤ (InfinitePlace.mult w : ℝ) := by positivity
        have hP : (0 : ℝ) ≤ normAtPlace w (mixedEmbedding K (a : K)) ^ 2 := sq_nonneg _
        rw [map_mul, mul_pow]
        nlinarith [mul_nonneg (mul_nonneg hmult hP) (sub_nonneg.mpr hsq)]
      rw [Complex.norm_real, Real.norm_of_nonneg hg0, mixedGaussian]
      refine Real.exp_le_exp.mpr ?_
      rw [mul_assoc]
      nlinarith [Real.pi_pos, key]
    -- Continuity on `B`, hence `ContinuousAt x₀`.
    have hcontB : ContinuousOn (mixedThetaKernel K I) B :=
      continuousOn_tsum hf_cont hu hbound
    exact hcontB.continuousAt (Metric.closedBall_mem_nhds x₀ (by positivity))

/-- **Continuity of the integral theta kernel** `x ↦ idealThetaKernel K 𝔞 x`,
on the nonzero-norm locus, the integral-ideal specialisation of
`continuousOn_mixedThetaKernel` via `idealThetaKernel_eq_mixed`. -/
theorem continuousOn_idealThetaKernel (𝔞 : Ideal (𝓞 K)) :
    ContinuousOn (idealThetaKernel K 𝔞)
      {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
  have h : idealThetaKernel K 𝔞
      = mixedThetaKernel K (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
    funext (idealThetaKernel_eq_mixed K 𝔞)
  rw [h]
  exact continuousOn_mixedThetaKernel K _

/- **Kernel inversion law via Poisson summation** (the standard treatment at
the multiplicative lattice level): for a nonzero integral ideal `𝔞` and a unit
`x ∈ K_ℝ^*` (`N(x) ≠ 0`),

    Θ(𝔞, x⁻¹) = (|N(x)| / vol(Λ(𝔞))) · (Θ((𝔞𝔡)⁻¹, x) + 1) - 1,

where `vol(Λ(𝔞)) = 𝔑(𝔞)·√|d_K|` is `covolume K 𝔞` and `(𝔞𝔡)⁻¹` is the dual
fractional ideal `dualIdeal K 𝔞`.

**The `+1`/`-1` correction is essential; the clean identity
`Θ(𝔞,x⁻¹) = (|N(x)|/vol)·Θ((𝔞𝔡)⁻¹,x)` is false in general** (it was the
previously committed, unfaithful form). The reason: `mixedThetaKernel` sums the
Minkowski Gaussian over the *nonzero* ideal elements (index set
`{a // a ∈ I ∧ a ≠ 0}`), whereas lattice Poisson summation
(`PoissonSummation.tsum_eq_tsum_fourier`) sums over the *whole* lattice
`Λ(𝔞) = idealLattice K 𝔞`, which contains `0`. With
`f(v) = mixedGaussian (x⁻¹ · (toMinkowski K).symm v)` and `g(0) = 1`:
  * LHS = `g(0) + ∑_{a≠0} = 1 + Θ(𝔞, x⁻¹)`;
  * `𝓕 f (w) = |N(x)| · g(x · (toMinkowski K).symm w)`
    (`fourier_mixedGaussian_scaling` at `x⁻¹`, with `|N(x⁻¹)|⁻¹ = |N(x)|`,
    `(x⁻¹)⁻¹ = x`);
  * dual sum over `Λ((𝔞𝔡)⁻¹) = idealLattice K (dualIdeal K 𝔞)`
    (`dual_idealLattice`) `= |N(x)|·(1 + Θ((𝔞𝔡)⁻¹, x))`;
  * constant `(ZLattice.covolume (idealLattice K 𝔞))⁻¹ = (covolume K 𝔞)⁻¹`.
Hence `1 + Θ(𝔞,x⁻¹) = (|N(x)|/vol)·(1 + Θ((𝔞𝔡)⁻¹,x))`, i.e. the stated form.
The `g(0)=1` lattice terms carry the asymmetric weights `1` (primal) and
`|N(x)|/vol` (dual) and do not cancel - this is the source's reduced-theta
`θ(iy) - 1` (the standard treatment). The theorem itself
(`mixedThetaKernel_inversion`) is stated and proved at the END of this file,
after its analytic prerequisites (`mixedGaussianSchwartz`,
`fourier_mixedGaussian_scaling`, `covolume_idealLattice`,
`dualLattice_idealLattice`) have been established. -/




/- **Inversion law for the integral kernel** (the exact form consumed by the
Mellin step): for a nonzero integral ideal `𝔞` and
`x ∈ K_ℝ^*`,

    idealThetaKernel K 𝔞 x⁻¹
      = (|N(x)| / vol(Λ(𝔞))) · (mixedThetaKernel K ((𝔞𝔡)⁻¹) x + 1) - 1

(the `+1`/`-1` correction carried over from `mixedThetaKernel_inversion`; see
there for why the clean form is false).

Proved by rewriting the integral kernel as the fractional kernel
(`idealThetaKernel_eq_mixed`) and applying `mixedThetaKernel_inversion`. The
theorem itself (`idealThetaKernel_inversion`) is stated and proved at the END of
this file, after `mixedThetaKernel_inversion`. -/

/-! ## `𝓞ˣ`-invariance of the cone Mellin integrand

The multiplicative Mellin integral defining `completedPartialZeta` is an integral
over the unit cone `K_ℝ^* / 𝓞ˣ`; to push it down to a fundamental domain one needs
the integrand `Θ(𝔞, x)·N(x)^t` (and its `x⁻¹` variant) to be invariant under the
`(𝓞 K)ˣ`-action `NumberField.mixedEmbedding.unitSMul` (`u • x = mixedEmbedding K u * x`).
The theta kernel sums the Gaussian over **all** nonzero `a ∈ 𝔞`; scaling `x` by a unit
`u` merely permutes the summands (`a ↦ u·a` is a bijection of the nonzero elements of
`𝔞`), so the kernel is unchanged, and `mixedEmbedding.norm` is unit-invariant by
`norm_unit_smul`. -/

/-- **Multiplicativity of the mixed-space inverse on field embeddings**:
`(mixedEmbedding K y)⁻¹ = mixedEmbedding K y⁻¹`. The mixed space is a product of
function spaces into the fields `ℝ`/`ℂ`, where inversion is componentwise; each
place embedding is a field hom and so commutes with `⁻¹` (`map_inv₀`). -/
theorem mixedEmbedding_inv (y : K) :
    (mixedEmbedding K y)⁻¹ = mixedEmbedding K y⁻¹ := by
  apply Prod.ext <;> funext i <;> simp [Pi.inv_apply, map_inv₀]

/-- **Componentwise multiplicativity of the mixed-space inverse**:
`(a * b)⁻¹ = a⁻¹ * b⁻¹` in `mixedSpace K` (a product of function spaces into
fields, where this is `mul_inv₀` in each coordinate). -/
theorem mixedSpace_mul_inv (a b : mixedEmbedding.mixedSpace K) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  apply Prod.ext <;> funext i <;> simp [Pi.inv_apply, mul_inv_rev, mul_comm]

/-- The coercion `(↑u : K)` of a unit `u : (𝓞 K)ˣ` is invertible in `K`, with
inverse the coercion of `u⁻¹`. -/
theorem coe_unit_inv (u : (𝓞 K)ˣ) :
    ((u : 𝓞 K) : K)⁻¹ = (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap,
    ← map_mul, Units.mul_inv, map_one]

/-- The `unitSMul` action commutes with the mixed-space inverse:
`(u • x)⁻¹ = u⁻¹ • x⁻¹`. -/
theorem unitSMul_inv (u : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K) :
    (u • x)⁻¹ = u⁻¹ • x⁻¹ := by
  rw [unitSMul_smul, unitSMul_smul, mixedSpace_mul_inv, mixedEmbedding_inv]
  have : ((algebraMap (𝓞 K) K) (u : 𝓞 K))⁻¹
      = (algebraMap (𝓞 K) K) ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
      coe_unit_inv]
  rw [this]

/-- **`𝓞ˣ`-invariance of the theta kernel**: for a unit
`u : (𝓞 K)ˣ` acting by `mixedEmbedding.unitSMul`, the kernel of any ideal `𝔞` is
unchanged: `idealThetaKernel K 𝔞 (u • x) = idealThetaKernel K 𝔞 x`. Multiplying
`x` by the unit `u` reindexes the sum over nonzero `a ∈ 𝔞` by the bijection
`a ↦ u·a` of the nonzero elements of `𝔞`, leaving the total unchanged. -/
theorem idealThetaKernel_unitSMul (𝔞 : Ideal (𝓞 K)) (u : (𝓞 K)ˣ)
    (x : mixedEmbedding.mixedSpace K) :
    idealThetaKernel K 𝔞 (u • x) = idealThetaKernel K 𝔞 x := by
  -- Bijection `a ↦ u·a` of the nonzero elements of `𝔞` (`u` is a unit).
  let e : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} ≃ {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} :=
  { toFun := fun a => ⟨(u : 𝓞 K) * a, Ideal.mul_mem_left _ _ a.2.1,
      mul_ne_zero (Units.ne_zero u) a.2.2⟩
    invFun := fun a => ⟨((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * a, Ideal.mul_mem_left _ _ a.2.1,
      mul_ne_zero (Units.ne_zero u⁻¹) a.2.2⟩
    left_inv := fun a => by
      apply Subtype.ext; simp [← mul_assoc]
    right_inv := fun a => by
      apply Subtype.ext; simp [← mul_assoc] }
  rw [idealThetaKernel, idealThetaKernel]
  conv_rhs => rw [← Equiv.tsum_eq e]
  refine tsum_congr (fun a => ?_)
  -- `(u • x) * emb(a) = x * emb(u·a) = x * emb((e a))`
  have hcoe : (((e a : 𝓞 K)) : K) = ((u : 𝓞 K) : K) * ((a : 𝓞 K) : K) := by
    change (((u : 𝓞 K) * a : 𝓞 K) : K) = _
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul,
      ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap]
  congr 1
  congr 1
  rw [unitSMul_smul]
  simp only [← RingOfIntegers.coe_eq_algebraMap]
  rw [hcoe, map_mul]; ring

/-- **`mixedEmbedding.norm` is `𝓞ˣ`-invariant** (re-export of Mathlib's
`norm_unit_smul` for use beside `idealThetaKernel_unitSMul`). -/
theorem norm_unitSMul (u : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x :=
  norm_unit_smul u x



/-! ## Fourier self-duality and multiplicative scaling of the Minkowski Gaussian

The Poisson-summation proof of `mixedThetaKernel_inversion`
consumes two analytic facts about `mixedGaussian`, both made precise here against
the **Minkowski inner product** of `minkowskiSpace K = euclidean.mixedSpace K`
(the `√2`-weighted Euclidean model for which `Λ(𝓞_K)` has covolume `√|d_K|`; see
the header and `inner_eEmb`). We use Mathlib's Fourier transform `𝓕` on a
finite-dimensional real inner product space (`Mathlib/Analysis/Fourier/`,
convention `𝓕 f w = ∫ v, exp(-2πi⟪v,w⟫) f v`) and its Gaussian evaluation
`fourier_gaussian_innerProductSpace`
(`Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`).

1. **Self-duality** (`fourier_gaussV`): the `t = 1` Minkowski Gaussian
   `gaussV v = exp(-π‖v‖²)` is its own Fourier transform (`(π/π)^{n/2} = 1`,
   `-π²‖w‖²/π = -π‖w‖²`). This is proved here outright.
2. **Multiplicative scaling** (`fourier_mixedGaussian_scaling`): the Fourier
   transform of `v ↦ mixedGaussian (x · v)` (multiplicative scaling by
   `x ∈ K_ℝ^*` on `mixedSpace K`) acquires the Jacobian factor
   `|N(x)|⁻¹ = |mixedEmbedding.norm x|⁻¹` and re-expresses as `mixedGaussian`
   at the inverse scaling `x⁻¹ · (·)`. (The change-of-variables `u = x·v` has
   `|det| = |N(x)|`; since `gaussV` depends only on the per-place absolute
   values, the inverse-adjoint scaling and `x⁻¹`-scaling give the same value.) -/

/-- The (self-dual, `t = 1`) Minkowski Gaussian on `minkowskiSpace K` as a
ℂ-valued function: `gaussV v = exp(-π‖v‖²)`, with `‖·‖` the Minkowski norm.
This is `mixedGaussian` transported through `toMinkowski` (`mixedGaussian_eq`). -/
def gaussV (v : minkowskiSpace K) : ℂ := Complex.exp (-(Real.pi : ℂ) * ‖v‖ ^ 2)

/-- **Bridge** `mixedGaussian = gaussV ∘ toMinkowski`: the Minkowski quadratic
form `∑_w mult w · normAtPlace w x²` equals `‖toMinkowski K x‖²` (the
`√2`-weighting puts the factor `2` on the complex places — the general-point
analog of `inner_eEmb`). Hence `(mixedGaussian K x : ℂ) = gaussV K (toMinkowski K x)`. -/
theorem mixedGaussian_eq (x : mixedEmbedding.mixedSpace K) :
    (mixedGaussian K x : ℂ) = gaussV K (toMinkowski K x) := by
  classical
  -- `(conj z · z).re = ‖z‖²` on `ℂ`, used on each complex place.
  have hre : ∀ z : ℂ, ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  -- General-point analog of `inner_eEmb`: the Minkowski inner product of
  -- `toMinkowski K x` with itself expands over the real/complex places, the
  -- `√2`-weighting (`scaleMixed`) putting the factor `2` on the complex places.
  have hinner : (inner ℝ (toMinkowski K x) (toMinkowski K x) : ℝ) =
      (∑ w : {w : InfinitePlace K // w.IsReal}, (x.1 w) * (x.1 w)) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
          ((starRingEnd ℂ) (x.2 w) * (x.2 w)).re := by
    rw [toMinkowski, WithLp.prod_inner_apply,
        show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
            (mixedEmbedding.euclidean.toMixed K).symm) x)).fst
            = WithLp.toLp 2 (scaleMixed K x).1 from rfl,
        show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
            (mixedEmbedding.euclidean.toMixed K).symm) x)).snd
            = WithLp.toLp 2 (scaleMixed K x).2 from rfl]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, scaleMixed,
      ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_refl', id_eq,
      ContinuousLinearEquiv.smulLeft_apply_apply, real_inner_eq_re_inner ℂ]
    rw [Finset.mul_sum]
    -- The complex-place summand identity (the `√2`-weighting gives the factor `2`).
    have hcplx : ∀ w : {w : InfinitePlace K // w.IsComplex},
        RCLike.re ((sqrtTwo • x.2) w * (starRingEnd ℂ) ((sqrtTwo • x.2) w))
          = 2 * ((starRingEnd ℂ) (x.2 w) * x.2 w).re := by
      intro w
      have hnorm : ‖(sqrtTwo • x.2) w‖ = Real.sqrt 2 * ‖x.2 w‖ := by
        rw [Pi.smul_apply, Units.smul_def, _root_.norm_smul, sqrtTwo, Units.val_mk0,
          Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
      -- LHS: `RCLike.re (z * conj z) = ‖z‖² = 2‖x.2 w‖²` with `z = (√2 • x.2) w`;
      -- RHS rewritten by `hre`.
      rw [RCLike.mul_conj, RCLike.re_ofReal_pow, hnorm, mul_pow,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hre]
    rw [Finset.sum_congr rfl (fun w (_ : w ∈ Finset.univ) => hcplx w)]
  -- Hence the Minkowski norm-squared is the Minkowski quadratic form.
  have hnorm2 : ‖toMinkowski K x‖ ^ 2 =
      ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hinner, InfinitePlace.sum_eq_sum_add_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [InfinitePlace.mult_isReal, normAtPlace_apply_of_isReal w.2]
      push_cast; rw [Real.norm_eq_abs, sq_abs]; ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [InfinitePlace.mult_isComplex, normAtPlace_apply_of_isComplex w.2, hre]
      push_cast; ring
  -- Push the real Gaussian through `Complex.ofReal_exp` and substitute.
  rw [mixedGaussian, gaussV, Complex.ofReal_exp]
  congr 1
  rw [← hnorm2]
  push_cast; ring

/-- **Fourier self-duality of the Minkowski Gaussian** (the `t = 1` self-dual
Gaussian): with respect to the Minkowski inner product on `minkowskiSpace K`,
the Fourier transform of `gaussV` is `gaussV`. This is
`fourier_gaussian_innerProductSpace` at `b = π`. -/
theorem fourier_gaussV (w : minkowskiSpace K) : 𝓕 (gaussV K) w = gaussV K w := by
  unfold gaussV
  rw [fourier_gaussian_innerProductSpace (b := (Real.pi : ℂ)) (by simp [Real.pi_pos])]
  rw [div_self (by exact_mod_cast Real.pi_ne_zero), Complex.one_cpow, one_mul]
  congr 1
  field_simp

/-- When `mixedEmbedding.norm x ≠ 0` every real/complex coordinate of `x` is
nonzero, so `x` is a unit in the ring `mixedSpace K` with two-sided inverse the
per-place reciprocal `x⁻¹` (componentwise inverse). -/
theorem mul_inv_cancel_of_norm_ne_zero {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) : x * x⁻¹ = 1 := by
  classical
  have hcomp : ∀ w : InfinitePlace K, normAtPlace w x ≠ 0 := fun w hw =>
    hx (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, hw⟩)
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have hw : x.1 w ≠ 0 := by
      have := hcomp w.1
      rw [normAtPlace_apply_of_isReal w.2] at this
      simpa using this
    show x.1 w * (x.1 w)⁻¹ = 1
    field_simp
  · have hw : x.2 w ≠ 0 := by
      have := hcomp w.1
      rw [normAtPlace_apply_of_isComplex w.2] at this
      simpa using this
    show x.2 w * (x.2 w)⁻¹ = 1
    field_simp

/-- **Multiplication-by-`x` as a continuous linear automorphism of `mixedSpace K`.**
For `x` a unit (`mixedEmbedding.norm x ≠ 0`, so all coordinates are nonzero),
multiplication-by-`x` is an `ℝ`-linear automorphism of the finite-dimensional
ring `mixedSpace K`, with inverse multiplication-by-`x⁻¹`. -/
def mulLeftMixed {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) :
    mixedEmbedding.mixedSpace K ≃L[ℝ] mixedEmbedding.mixedSpace K :=
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel_of_norm_ne_zero K hx
  have hxinv' : x⁻¹ * x = 1 := by rw [mul_comm]; exact hxinv
  (LinearEquiv.ofLinear (LinearMap.mulLeft ℝ x) (LinearMap.mulLeft ℝ x⁻¹)
    (LinearMap.ext fun y => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.id_coe, id_eq, ← mul_assoc, hxinv, one_mul])
    (LinearMap.ext fun y => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.id_coe, id_eq, ← mul_assoc, hxinv', one_mul])).toContinuousLinearEquiv


/-- **The multiplication-by-`x` automorphism `A_x` of the Minkowski space.**
The conjugate of `mulLeftMixed` (multiplication-by-`x` on `mixedSpace K`) through
the Minkowski identification `toMinkowski K`, so that
`A_x v = toMinkowski K (x * (toMinkowski K).symm v)`. -/
def A_x {x : mixedEmbedding.mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    minkowskiSpace K ≃L[ℝ] minkowskiSpace K :=
  (toMinkowski K).symm.trans ((mulLeftMixed K hx).trans (toMinkowski K))

@[simp]
theorem A_x_apply {x : mixedEmbedding.mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0)
    (v : minkowskiSpace K) :
    A_x K hx v = toMinkowski K (x * (toMinkowski K).symm v) := rfl

/-- **Bilinear Minkowski inner product through `toMinkowski`.** The Euclidean
inner product of `toMinkowski K p` and `toMinkowski K q` expands per place as
`∑_real p₁ q₁ + 2 ∑_cplx Re(conj p₂ q₂)` (the `√2`-weighting on `scaleMixed`
puts the factor `2` on the complex places). The single-argument case is the
quadratic form used in `mixedGaussian_eq`. -/
theorem toMinkowski_inner (p q : mixedEmbedding.mixedSpace K) :
    (inner ℝ (toMinkowski K p) (toMinkowski K q) : ℝ) =
      (∑ w : {w : InfinitePlace K // w.IsReal}, (p.1 w) * (q.1 w)) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
          ((p.2 w) * (starRingEnd ℂ) (q.2 w)).re := by
  classical
  rw [toMinkowski, WithLp.prod_inner_apply,
      show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
          (mixedEmbedding.euclidean.toMixed K).symm) p)).fst
          = WithLp.toLp 2 (scaleMixed K p).1 from rfl,
      show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
          (mixedEmbedding.euclidean.toMixed K).symm) p)).snd
          = WithLp.toLp 2 (scaleMixed K p).2 from rfl,
      show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
          (mixedEmbedding.euclidean.toMixed K).symm) q)).fst
          = WithLp.toLp 2 (scaleMixed K q).1 from rfl,
      show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
          (mixedEmbedding.euclidean.toMixed K).symm) q)).snd
          = WithLp.toLp 2 (scaleMixed K q).2 from rfl]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, scaleMixed,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_refl', id_eq,
    ContinuousLinearEquiv.smulLeft_apply_apply, real_inner_eq_re_inner ℂ]
  rw [Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    ring
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    have hz : (sqrtTwo • q.2) w * (starRingEnd ℂ) ((sqrtTwo • p.2) w)
        = (↑(2:ℝ) : ℂ) * (q.2 w * (starRingEnd ℂ) (p.2 w)) := by
      simp only [Pi.smul_apply, Units.smul_def, sqrtTwo, Units.val_mk0, Complex.real_smul,
        map_mul, Complex.conj_ofReal]
      have h2 : (↑(Real.sqrt 2) : ℂ) * (↑(Real.sqrt 2) : ℂ) = (↑(2:ℝ) : ℂ) := by
        norm_cast; exact Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
      linear_combination (q.2 w * (starRingEnd ℂ) (p.2 w)) * h2
    rw [hz]
    simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring

/-- **Determinant of `A_x`.** Conjugation by `toMinkowski` leaves the determinant
unchanged, so it equals `|det (mulLeft ℝ x)|` on `mixedSpace K`: over each real
place the block is scalar `x_w`, over each complex place multiplication by
`x_w ∈ ℂ` as an `ℝ`-linear map has determinant `|x_w|²`, and the product over all
places is `∏_w |x_w|^{mult w} = |mixedEmbedding.norm x|`. -/
theorem A_x_det_abs {x : mixedEmbedding.mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    |LinearMap.det ((A_x K hx).toLinearEquiv : minkowskiSpace K →ₗ[ℝ] minkowskiSpace K)|
      = |mixedEmbedding.norm x| := by
  -- Step 1: conjugation by `toMinkowski` does not change the determinant, so
  -- `det (A_x) = det (mulLeft ℝ x)` on `mixedSpace K`.
  have hconj : ((A_x K hx).toLinearEquiv : minkowskiSpace K →ₗ[ℝ] minkowskiSpace K)
      = ((toMinkowski K).toLinearEquiv : mixedSpace K →ₗ[ℝ] minkowskiSpace K) ∘ₗ
          (LinearMap.mulLeft ℝ x) ∘ₗ
          ((toMinkowski K).toLinearEquiv.symm : minkowskiSpace K →ₗ[ℝ] mixedSpace K) := by
    refine LinearMap.ext fun v => ?_
    simp [A_x_apply, LinearMap.mulLeft_apply]
  rw [hconj, LinearMap.det_conj]
  -- Step 2: `mulLeft ℝ x` is block-diagonal across the real/complex factors.
  have hprod : LinearMap.mulLeft ℝ x
      = LinearMap.prodMap (LinearMap.mulLeft ℝ x.1) (LinearMap.mulLeft ℝ x.2) := by
    refine LinearMap.ext fun v => ?_
    apply Prod.ext <;> simp [LinearMap.mulLeft_apply, Prod.fst_mul, Prod.snd_mul]
  -- Real block: a diagonal map with determinant `∏_w x.1 w`.
  have hdetR : LinearMap.det (LinearMap.mulLeft ℝ x.1) = ∏ w, x.1 w := by
    have hR : LinearMap.mulLeft ℝ x.1
        = LinearMap.pi (fun w => (LinearMap.mulLeft ℝ (x.1 w)).comp (LinearMap.proj w)) := by
      refine LinearMap.ext fun v => ?_
      funext w
      simp [LinearMap.mulLeft_apply, Pi.mul_apply]
    rw [hR, LinearMap.det_pi]
    simp_rw [LinearMap.det_mulLeft]
  -- Complex block: per place the `ℝ`-linear determinant of `mulLeft (x.2 w)` on `ℂ`
  -- is `Algebra.norm ℝ (x.2 w) = normSq (x.2 w) = ‖x.2 w‖²`.
  have hdetC : LinearMap.det (LinearMap.mulLeft ℝ x.2) = ∏ w, ‖x.2 w‖ ^ 2 := by
    have hC : LinearMap.mulLeft ℝ x.2
        = LinearMap.pi (fun w => (LinearMap.mulLeft ℝ (x.2 w)).comp (LinearMap.proj w)) := by
      refine LinearMap.ext fun v => ?_
      funext w
      simp [LinearMap.mulLeft_apply, Pi.mul_apply]
    rw [hC, LinearMap.det_pi]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hlmul : LinearMap.mulLeft ℝ (x.2 w) = Algebra.lmul ℝ ℂ (x.2 w) := by
      ext y
      simp [LinearMap.mulLeft_apply, Algebra.coe_lmul_eq_mul]
    rw [hlmul, ← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  -- Step 3: assemble `|det| = (∏_real |x.1 w|)·(∏_complex ‖x.2 w‖²) = |N(x)|`.
  have hreal : (∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w},
        normAtPlace w.1 x ^ InfinitePlace.mult w.1)
      = ∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w}, ‖x.1 w‖ :=
    Finset.prod_congr rfl fun w _ => by
      rw [InfinitePlace.mult_isReal, pow_one, normAtPlace_apply_of_isReal w.prop]
  have hcpx : (∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w},
        normAtPlace w.1 x ^ InfinitePlace.mult w.1)
      = ∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w}, ‖x.2 w‖ ^ 2 :=
    Finset.prod_congr rfl fun w _ => by
      rw [InfinitePlace.mult_isComplex, normAtPlace_apply_of_isComplex w.prop]
  have hn : mixedEmbedding.norm x
      = (∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w}, ‖x.1 w‖)
        * (∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w}, ‖x.2 w‖ ^ 2) := by
    rw [mixedEmbedding.norm_apply, InfinitePlace.prod_eq_prod_mul_prod, hreal, hcpx]
  rw [hprod, LinearMap.det_prodMap, hdetR, hdetC, abs_mul, Finset.abs_prod,
    _root_.abs_of_nonneg (Finset.prod_nonneg fun w _ => sq_nonneg _),
    _root_.abs_of_nonneg (mixedEmbedding.norm_nonneg x), hn]
  congr 1

/-- **Inverse-adjoint of `A_x` acts like the `x⁻¹`-scaling on `gaussV`.** Since
`gaussV` depends only on the Minkowski norm `‖·‖`, and per place the adjoint of
multiplication-by-`x_w` is multiplication-by-`conj x_w` (modulus `|x_w|`, the
same as `x⁻¹_w = 1/x_w`), the inverse-adjoint `(A_x.symm)ᴴ` and the
`x⁻¹`-scaling `toMinkowski (x⁻¹ · (toMinkowski).symm ·)` agree under `gaussV`. -/
theorem A_x_symm_adjoint_gaussV {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) (w : minkowskiSpace K) :
    gaussV K (ContinuousLinearMap.adjoint
        ((A_x K hx).symm : minkowskiSpace K →L[ℝ] minkowskiSpace K) w)
      = gaussV K (toMinkowski K (x⁻¹ * (toMinkowski K).symm w)) := by
  classical
  -- Coordinatewise conjugate of `x⁻¹`: per place the adjoint of multiplication
  -- by `x_w` (w.r.t. the Minkowski inner product) is multiplication by `conj x_w`.
  set z : mixedEmbedding.mixedSpace K := conjMixed K x⁻¹ with hz
  -- Candidate adjoint of `(A_x).symm`: the `z`-scaling conjugated by `toMinkowski`.
  set B : minkowskiSpace K →L[ℝ] minkowskiSpace K :=
    (toMinkowski K : mixedEmbedding.mixedSpace K →L[ℝ] minkowskiSpace K).comp
      ((LinearMap.mulLeft ℝ z).toContinuousLinearMap.comp
        ((toMinkowski K).symm : minkowskiSpace K →L[ℝ] mixedEmbedding.mixedSpace K)) with hB
  have hBapp : ∀ v, B v = toMinkowski K (z * (toMinkowski K).symm v) := fun _ => rfl
  -- Explicit inverse of `A_x`.
  have hAsymm : ∀ v, (A_x K hx).symm v = toMinkowski K (x⁻¹ * (toMinkowski K).symm v) := by
    intro v
    rw [ContinuousLinearEquiv.symm_apply_eq, A_x_apply,
      ContinuousLinearEquiv.symm_apply_apply, ← mul_assoc,
      mul_inv_cancel_of_norm_ne_zero K hx, one_mul,
      ContinuousLinearEquiv.apply_symm_apply]
  -- `B` is the adjoint of `(A_x).symm`: the per-place adjoint identity.
  have hinner_eq : ∀ (u v : minkowskiSpace K),
      (inner ℝ ((A_x K hx).symm u) v : ℝ) = inner ℝ u (B v) := by
    intro u v
    have hu : u = toMinkowski K ((toMinkowski K).symm u) :=
      ((toMinkowski K).apply_symm_apply u).symm
    have hv : v = toMinkowski K ((toMinkowski K).symm v) :=
      ((toMinkowski K).apply_symm_apply v).symm
    rw [hAsymm u, hBapp v]
    conv_lhs => rw [hv]
    conv_rhs => rw [hu]
    rw [toMinkowski_inner, toMinkowski_inner]
    refine congr_arg₂ (· + ·) ?_ (congr_arg (fun s => 2 * s) ?_)
    · refine Finset.sum_congr rfl (fun w _ => ?_)
      simp only [Prod.fst_mul, Pi.mul_apply, hz, conjMixed_fst]
      ring
    · refine Finset.sum_congr rfl (fun w _ => ?_)
      congr 1
      simp only [Prod.snd_mul, Pi.mul_apply, hz, conjMixed_snd, map_mul, Complex.conj_conj]
      ring
  have hadj : ContinuousLinearMap.adjoint
      ((A_x K hx).symm : minkowskiSpace K →L[ℝ] minkowskiSpace K) = B := by
    have hAB : ((A_x K hx).symm : minkowskiSpace K →L[ℝ] minkowskiSpace K)
        = ContinuousLinearMap.adjoint B :=
      (ContinuousLinearMap.eq_adjoint_iff
        ((A_x K hx).symm : minkowskiSpace K →L[ℝ] minkowskiSpace K) B).2 hinner_eq
    rw [hAB, ContinuousLinearMap.adjoint_adjoint]
  -- `gaussV` depends only on the Minkowski norm; the two arguments have equal norm.
  have hns : (inner ℝ (toMinkowski K (z * (toMinkowski K).symm w))
        (toMinkowski K (z * (toMinkowski K).symm w)) : ℝ)
      = inner ℝ (toMinkowski K (x⁻¹ * (toMinkowski K).symm w))
        (toMinkowski K (x⁻¹ * (toMinkowski K).symm w)) := by
    rw [toMinkowski_inner, toMinkowski_inner]
    refine congr_arg₂ (· + ·) ?_ (congr_arg (fun s => 2 * s) ?_)
    · refine Finset.sum_congr rfl (fun w' _ => ?_)
      simp only [Prod.fst_mul, Pi.mul_apply, hz, conjMixed_fst]
    · refine Finset.sum_congr rfl (fun w' _ => ?_)
      rw [Complex.mul_conj, Complex.mul_conj, Complex.ofReal_re, Complex.ofReal_re]
      simp only [Prod.snd_mul, Pi.mul_apply, hz, conjMixed_snd, Complex.normSq_mul,
        Complex.normSq_conj]
  have hnorm2 : ‖toMinkowski K (z * (toMinkowski K).symm w)‖ ^ 2
      = ‖toMinkowski K (x⁻¹ * (toMinkowski K).symm w)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hns]
  rw [hadj, hBapp w]
  unfold gaussV
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, hnorm2]

/-! ## Schwartz structure for the scaled Minkowski Gaussian -/

/-- **Smoothness of the Minkowski Gaussian.** `gaussV v = exp(-π‖v‖²)` is `C^∞`
on the finite-dimensional inner-product space `minkowskiSpace K`: the norm-square
`v ↦ ‖v‖²` is smooth (`contDiff_norm_sq`), `Complex.ofRealCLM` and scalar
multiplication are smooth, and `Complex.exp` is entire, so the composite is
`C^∞`. -/
theorem gaussV_contDiff : ContDiff ℝ ∞ (gaussV K) := by
  have h1 : ContDiff ℝ ∞ (fun v : minkowskiSpace K => (‖v‖ ^ 2 : ℝ)) :=
    contDiff_norm_sq ℝ
  have h2 : ContDiff ℝ ∞
      (fun v : minkowskiSpace K => (-(Real.pi : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ))) :=
    contDiff_const.mul ((Complex.ofRealCLM.contDiff).comp h1)
  have h3 : ContDiff ℝ ∞
      (fun v : minkowskiSpace K => Complex.exp (-(Real.pi : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp h2
  have hfun : gaussV K =
      fun v : minkowskiSpace K => Complex.exp (-(Real.pi : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ)) := by
    funext v
    rw [gaussV]
    push_cast
    ring_nf
  rw [hfun]
  exact h3

/-- **One-dimensional Gaussian-times-polynomial bound.** For every `N`, the
function `t ↦ (1 + t)^N · exp(-π t²)` is bounded above on `[0, ∞)` by the
explicit constant `exp(N²/(4π))`.  No limiting argument is needed: for `t ≥ 0`,
`1 + t ≤ exp t` (`Real.add_one_le_exp`), so `(1 + t)^N ≤ exp(N t)`, and
`N t - π t² = N²/(4π) - π (t - N/(2π))² ≤ N²/(4π)`. -/
theorem exp_neg_pi_sq_mul_poly_bddAbove (N : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      (1 + t) ^ N * Real.exp (-Real.pi * t ^ 2) ≤ C := by
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * Real.pi)), fun t ht => ?_⟩
  have hpi := Real.pi_pos
  have h4pi : (0 : ℝ) < 4 * Real.pi := by linarith
  have h1t : (0 : ℝ) ≤ 1 + t := by linarith
  have hexp_pos : (0 : ℝ) < Real.exp (-Real.pi * t ^ 2) := Real.exp_pos _
  have hb : (1 + t) ^ N ≤ Real.exp ((N : ℝ) * t) := by
    calc (1 + t) ^ N
        ≤ (Real.exp t) ^ N :=
          pow_le_pow_left₀ h1t (by linarith [Real.add_one_le_exp t]) N
      _ = Real.exp ((N : ℝ) * t) := (Real.exp_nat_mul t N).symm
  calc (1 + t) ^ N * Real.exp (-Real.pi * t ^ 2)
      ≤ Real.exp ((N : ℝ) * t) * Real.exp (-Real.pi * t ^ 2) :=
        mul_le_mul_of_nonneg_right hb hexp_pos.le
    _ = Real.exp ((N : ℝ) * t + -Real.pi * t ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * Real.pi)) := by
        apply Real.exp_le_exp.mpr
        rw [le_div_iff₀ h4pi]
        nlinarith [sq_nonneg ((N : ℝ) - 2 * Real.pi * t)]

/-! ### Iterated-derivative bound for `gaussV`

The `gaussV_iteratedFDeriv_bound` below is proved via the Faà-di-Bruno-type
composition bound `norm_iteratedFDeriv_comp_le`, using the three helper lemmas
`norm_iteratedFDeriv_cexp`, `norm_iteratedFDeriv_clm_succ` and
`norm_iteratedFDeriv_normSq_le`. -/

/-- Norm of the `i`-th *real* iterated Fréchet derivative of `Complex.exp` at `z`
equals `exp (re z)`. -/
theorem norm_iteratedFDeriv_cexp (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  rw [← (Complex.contDiff_exp (𝕜 := ℂ) (n := (i : ℕ∞ω))).contDiffAt.restrictScalars_iteratedFDeriv
        (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hexp : iteratedDeriv i Complex.exp = Complex.exp := by
    rw [iteratedDeriv_eq_iterate]; exact Complex.iter_deriv_exp i
  rw [hexp, Complex.norm_exp]

theorem norm_iteratedFDeriv_clm_succ {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : F →L[ℝ] G) (i : ℕ) (v : F) :
    ‖iteratedFDeriv ℝ (i + 1) (⇑A) v‖ = ‖iteratedFDeriv ℝ i (fun _ : F => A) v‖ := by
  rw [← norm_iteratedFDeriv_fderiv]
  have hfd : (fderiv ℝ (⇑A)) = fun _ : F => A := by
    ext x : 1; exact A.fderiv
  rw [hfd]

theorem norm_iteratedFDeriv_normSq_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (i : ℕ) (hi : 1 ≤ i) (v : F) :
    ‖iteratedFDeriv ℝ i (fun w : F => ‖w‖ ^ 2) v‖ ≤ (2 * (1 + ‖v‖)) ^ i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  set A : F →L[ℝ] F →L[ℝ] ℝ := 2 • innerSL ℝ with hAdef
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hbase : (1 : ℝ) ≤ 2 * (1 + ‖v‖) := by nlinarith
  have hfderiv : ‖iteratedFDeriv ℝ (k + 1) (fun w : F => ‖w‖ ^ 2) v‖
      = ‖iteratedFDeriv ℝ k (⇑A) v‖ := by
    rw [← norm_iteratedFDeriv_fderiv]
    have hh : (fderiv ℝ fun w : F => ‖w‖ ^ 2) = ⇑A := fderiv_norm_sq
    rw [hh]
  rw [hfderiv]
  have hAval : ∀ w : F, A w = 2 • (innerSL ℝ w) := by
    intro w
    have hfd := fderiv_norm_sq_apply (F := F) w
    rw [fderiv_norm_sq] at hfd
    rw [hAdef]; exact hfd
  have hnormAw : ∀ w : F, ‖A w‖ = 2 * ‖w‖ := by
    intro w
    rw [hAval w, RCLike.norm_nsmul (K := ℝ), innerSL_apply_norm, nsmul_eq_mul]; norm_num
  have hAnorm : ‖A‖ ≤ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun w => ?_)
    rw [hnormAw w]
  have hAv : ‖A v‖ = 2 * ‖v‖ := hnormAw v
  match k with
  | 0 =>
    rw [norm_iteratedFDeriv_zero, hAv, pow_one]; nlinarith
  | 1 =>
    rw [norm_iteratedFDeriv_clm_succ A 0 v, norm_iteratedFDeriv_zero]
    have hexp : (2 * (1 + ‖v‖)) ^ (1 + 1) = (2 * (1 + ‖v‖)) * (2 * (1 + ‖v‖)) := by ring
    rw [hexp]; nlinarith [hAnorm, hnv, sq_nonneg ‖v‖]
  | l + 2 =>
    rw [norm_iteratedFDeriv_clm_succ A (l + 1) v,
      iteratedFDeriv_const_of_ne (by omega) A, Pi.zero_apply, norm_zero]
    positivity

theorem gaussV_iteratedFDeriv_bound (n : ℕ) :
    ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ v : minkowskiSpace K,
      ‖iteratedFDeriv ℝ n (gaussV K) v‖
        ≤ C * (1 + ‖v‖) ^ d * Real.exp (-Real.pi * ‖v‖ ^ 2) := by
  have hpi := Real.pi_pos
  set p : minkowskiSpace K → ℝ := fun v => (-Real.pi) • (‖v‖ ^ 2 : ℝ) with hpdef
  set u : minkowskiSpace K → ℂ := fun v => Complex.ofRealLI (p v) with hudef
  have hp_cd : ContDiff ℝ ∞ p := (contDiff_norm_sq ℝ).const_smul _
  have hu_cd : ContDiff ℝ ∞ u :=
    Complex.ofRealLI.toContinuousLinearMap.contDiff.comp hp_cd
  have hgauss : gaussV K = Complex.exp ∘ u := by
    funext v
    simp only [gaussV, Function.comp_apply, hudef, hpdef, Complex.ofRealLI_apply]
    congr 1
    push_cast [smul_eq_mul]
    ring
  refine ⟨n, (Nat.factorial n : ℝ) * (2 * Real.pi) ^ n, by positivity, fun v => ?_⟩
  set D : ℝ := 2 * Real.pi * (1 + ‖v‖) with hDdef
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i u v‖ ≤ D ^ i := by
    intro i hi _
    have hcomp : ‖iteratedFDeriv ℝ i u v‖ = ‖iteratedFDeriv ℝ i p v‖ :=
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hp_cd.contDiffAt) (by exact_mod_cast le_top)
    have hpe : p = (-Real.pi) • (fun w : minkowskiSpace K => ‖w‖ ^ 2) := by
      funext w; simp [hpdef, smul_eq_mul]
    have hsmul : ‖iteratedFDeriv ℝ i p v‖
        = Real.pi * ‖iteratedFDeriv ℝ i (fun w : minkowskiSpace K => ‖w‖ ^ 2) v‖ := by
      rw [hpe, iteratedFDeriv_const_smul_apply (contDiff_norm_sq ℝ).contDiffAt,
        _root_.norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hpi.le]
    rw [hcomp, hsmul]
    have hns := norm_iteratedFDeriv_normSq_le (F := minkowskiSpace K) i hi v
    have h1 : Real.pi ≤ Real.pi ^ i := by
      calc Real.pi = Real.pi ^ 1 := (pow_one _).symm
        _ ≤ Real.pi ^ i := pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hi
    have hexpand : D ^ i = Real.pi ^ i * (2 * (1 + ‖v‖)) ^ i := by
      rw [hDdef, show 2 * Real.pi * (1 + ‖v‖) = Real.pi * (2 * (1 + ‖v‖)) from by ring, mul_pow]
    calc Real.pi * ‖iteratedFDeriv ℝ i (fun w : minkowskiSpace K => ‖w‖ ^ 2) v‖
        ≤ Real.pi * (2 * (1 + ‖v‖)) ^ i :=
          mul_le_mul_of_nonneg_left hns hpi.le
      _ ≤ Real.pi ^ i * (2 * (1 + ‖v‖)) ^ i :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = D ^ i := hexpand.symm
  have hure : (u v).re = -Real.pi * ‖v‖ ^ 2 := by
    simp only [hudef, hpdef, Complex.ofRealLI_apply, Complex.ofReal_re, smul_eq_mul]
  have hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i Complex.exp (u v)‖
      ≤ Real.exp (-Real.pi * ‖v‖ ^ 2) := by
    intro i _
    rw [norm_iteratedFDeriv_cexp, hure]
  have hmain := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Complex.exp) (f := u)
    Complex.contDiff_exp hu_cd (by exact_mod_cast le_top) v
    (C := Real.exp (-Real.pi * ‖v‖ ^ 2)) (D := D) hC hD
  rw [hgauss]
  calc ‖iteratedFDeriv ℝ n (Complex.exp ∘ u) v‖
      ≤ (Nat.factorial n : ℝ) * Real.exp (-Real.pi * ‖v‖ ^ 2) * D ^ n := hmain
    _ = (Nat.factorial n : ℝ) * (2 * Real.pi) ^ n * (1 + ‖v‖) ^ n
          * Real.exp (-Real.pi * ‖v‖ ^ 2) := by
        rw [hDdef, mul_pow]; ring

/-- **Polynomial decay of the Minkowski Gaussian and its derivatives.** Every
iterated Fréchet derivative of `gaussV v = exp(-π‖v‖²)` is a Gaussian times a
polynomial in `v`, and `exp(-π‖v‖²)` decays faster than any polynomial grows, so
`‖v‖^k · ‖iteratedFDeriv ℝ n (gaussV K) v‖` is bounded for every `k, n`.  This is
the `SchwartzMap.decay'` obligation, obtained by combining the structural bound
`gaussV_iteratedFDeriv_bound` with the explicit one-dimensional bound
`exp_neg_pi_sq_mul_poly_bddAbove` (using `‖v‖^k (1+‖v‖)^d ≤ (1+‖v‖)^{k+d}`). -/
theorem gaussV_decay :
    ∀ (k n : ℕ), ∃ C : ℝ, ∀ v : minkowskiSpace K,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (gaussV K) v‖ ≤ C := by
  intro k n
  obtain ⟨d, C, hC0, hbound⟩ := gaussV_iteratedFDeriv_bound K n
  obtain ⟨C', hC'⟩ := exp_neg_pi_sq_mul_poly_bddAbove (k + d)
  refine ⟨C * C', fun v => ?_⟩
  have hv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hexp : (0 : ℝ) ≤ Real.exp (-Real.pi * ‖v‖ ^ 2) := (Real.exp_pos _).le
  have hpoly : ‖v‖ ^ k * (1 + ‖v‖) ^ d ≤ (1 + ‖v‖) ^ (k + d) := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv (by linarith) k) (by positivity)
  calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (gaussV K) v‖
      ≤ ‖v‖ ^ k * (C * (1 + ‖v‖) ^ d * Real.exp (-Real.pi * ‖v‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (hbound v) (by positivity)
    _ = C * (‖v‖ ^ k * (1 + ‖v‖) ^ d) * Real.exp (-Real.pi * ‖v‖ ^ 2) := by ring
    _ ≤ C * (1 + ‖v‖) ^ (k + d) * Real.exp (-Real.pi * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC0) hexp
    _ = C * ((1 + ‖v‖) ^ (k + d) * Real.exp (-Real.pi * ‖v‖ ^ 2)) := by ring
    _ ≤ C * C' := mul_le_mul_of_nonneg_left (hC' ‖v‖ hv) hC0

/-- The (self-dual, `t = 1`) Minkowski Gaussian `gaussV v = exp(-π‖v‖²)` packaged
as a `SchwartzMap` on the inner-product space `minkowskiSpace K`.  Smoothness is
`gaussV_contDiff`; the polynomial-decay bounds are `gaussV_decay`. -/
def gaussVSchwartz : SchwartzMap (minkowskiSpace K) ℂ where
  toFun := gaussV K
  smooth' := gaussV_contDiff K
  decay' := gaussV_decay K

@[simp]
theorem gaussVSchwartz_apply (v : minkowskiSpace K) :
    gaussVSchwartz K v = gaussV K v := rfl

/-- **Schwartz structure for the multiplicatively-scaled Minkowski Gaussian.**
For `x ∈ K_ℝ^*` (`mixedEmbedding.norm x ≠ 0`, so multiplication-by-`x` is a
continuous linear *automorphism* `A_x` of `minkowskiSpace K`), the function
`v ↦ mixedGaussian K (x · σ⁻¹ v)` (`σ⁻¹ = (toMinkowski K).symm`) is the Gaussian
`gaussVSchwartz` precomposed with the linear equiv `A_x`, hence a `SchwartzMap`.
This is the honest `SchwartzMap` argument that
`PoissonSummation.tsum_eq_tsum_fourier` demands of the kernel inversion.

The hypothesis `mixedEmbedding.norm x ≠ 0` is genuinely required (it is what
makes `A_x` a *continuous linear equiv* rather than a mere map): if some
coordinate of `x` vanished the function would be constant in a direction and so
not Schwartz.  It is available at every call site — the kernel inversion only
uses this for `x` with nonzero norm. -/
def mixedGaussianSchwartz {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) : SchwartzMap (minkowskiSpace K) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (A_x K hx) (gaussVSchwartz K)

@[simp]
theorem mixedGaussianSchwartz_apply {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) (v : minkowskiSpace K) :
    mixedGaussianSchwartz K hx v
      = (mixedGaussian K (x * (toMinkowski K).symm v) : ℂ) := by
  simp only [mixedGaussianSchwartz,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    gaussVSchwartz_apply, A_x_apply]
  exact (mixedGaussian_eq K _).symm

/-! ## Covolume of the √2-weighted ideal lattice -/

/-- The inverse weighting `(scaleMixed K).symm` written as an explicit
`ℝ`-linear endomorphism of the mixed space: it fixes the real coordinates and
scales each complex coordinate by `(√2)⁻¹`. -/
theorem scaleMixed_symm_apply (x : mixedSpace K) :
    (scaleMixed K).symm x = (x.1, (Real.sqrt 2)⁻¹ • x.2) := by
  have hsqrt : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  symm
  rw [← ContinuousLinearEquiv.symm_apply_eq]
  show (scaleMixed K) (x.1, (Real.sqrt 2)⁻¹ • x.2) = x
  rw [scaleMixed]
  ext i
  · rfl
  · show (sqrtTwo : ℝ) • ((Real.sqrt 2)⁻¹ • x.2) i = x.2 i
    simp only [sqrtTwo, Units.val_mk0, Pi.smul_apply]
    rw [smul_smul, mul_inv_cancel₀ hsqrt, one_smul]

open Module in
/-- The real dimension of the complex part of the mixed space is twice the
number of complex places. -/
theorem finrank_complexPart :
    finrank ℝ ({w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ)
      = 2 * nrComplexPlaces K := by
  rw [Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [nrComplexPlaces, mul_comm]

open Module in
/-- Determinant of the inverse √2-weighting as an `ℝ`-linear endomorphism of the
mixed space: it fixes `r₁` real coordinates and scales the `r₂` complex
coordinates (real dimension 2 each) by `(√2)⁻¹`, hence has determinant
`((√2)⁻¹) ^ (2·r₂)`. -/
theorem det_scaleMixed_symm :
    LinearMap.det ((scaleMixed K).symm.toLinearEquiv.toLinearMap :
        mixedSpace K →ₗ[ℝ] mixedSpace K)
      = ((Real.sqrt 2)⁻¹) ^ (2 * nrComplexPlaces K) := by
  have hform : LinearMap.prodMap LinearMap.id
          (((Real.sqrt 2)⁻¹) • (LinearMap.id :
            ({w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ) →ₗ[ℝ] _))
      = ((scaleMixed K).symm.toLinearEquiv.toLinearMap :
          mixedSpace K →ₗ[ℝ] mixedSpace K) := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.prodMap_apply, LinearMap.id_coe, id_eq, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq]
    show (x.1, (Real.sqrt 2)⁻¹ • x.2) = (scaleMixed K).symm x
    rw [scaleMixed_symm_apply]
  rw [← hform, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_smul,
    LinearMap.det_id, mul_one, finrank_complexPart]

open MeasureTheory in
/-- Pushing the (Euclidean) Lebesgue measure of `minkowskiSpace K` back to the
mixed space along `(toMinkowski K).symm` multiplies it by `2 ^ r₂`: `toMixed` is
volume preserving while the `√2`-weighting on the `r₂` complex coordinates
scales volume by `(√2)^(2·r₂) = 2 ^ r₂`. -/
theorem map_toMinkowski_symm_volume :
    Measure.map (toMinkowski K).symm (volume : Measure (minkowskiSpace K))
      = ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K) • (volume : Measure (mixedSpace K)) := by
  have hsq : ((Real.sqrt 2)⁻¹) ^ (2 * nrComplexPlaces K) ≠ 0 := by
    have : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    positivity
  -- `(toMinkowski K).symm = (scaleMixed K).symm ∘ toMixed K` as a function.
  have hcomp : ((toMinkowski K).symm : minkowskiSpace K → mixedSpace K)
      = (scaleMixed K).symm ∘ (mixedEmbedding.euclidean.toMixed K) := by
    funext w
    show (toMinkowski K).symm w = (scaleMixed K).symm (mixedEmbedding.euclidean.toMixed K w)
    have hw : toMinkowski K ((scaleMixed K).symm (mixedEmbedding.euclidean.toMixed K w)) = w := by
      rw [toMinkowski, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact (ContinuousLinearEquiv.symm_apply_eq (toMinkowski K)).mpr hw.symm
  rw [hcomp, ← Measure.map_map ((scaleMixed K).symm.continuous.measurable)
    ((mixedEmbedding.euclidean.toMixed K).continuous.measurable),
    (mixedEmbedding.euclidean.volumePreserving_toMixed K).map_eq]
  -- Now reduce `Measure.map (scaleMixed K).symm volume` to the linear-map formula.
  have hcoe : ((scaleMixed K).symm : mixedSpace K → mixedSpace K)
      = ⇑((scaleMixed K).symm.toLinearEquiv.toLinearMap :
          mixedSpace K →ₗ[ℝ] mixedSpace K) := rfl
  rw [hcoe, Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (by rw [det_scaleMixed_symm]; exact hsq), det_scaleMixed_symm]
  congr 1
  rw [abs_of_pos (by positivity)]
  congr 1
  rw [inv_pow, inv_inv, pow_mul, Real.sq_sqrt (by norm_num)]

open MeasureTheory in
/-- **Covolume of the √2-weighted ideal lattice** (the standard treatment):
for a nonzero integral ideal `𝔞`, the Euclidean lattice `Λ(𝔞)` of
`DedekindZeta.Theta.idealLattice` (the image of `𝔞` under the `√2`-weighted
embedding `eEmb = toMinkowski ∘ mixedEmbedding`) has covolume exactly
`𝔑(𝔞)·√|d_K| = covolume K 𝔞`.

The `√2`-weighting contributes a Jacobian factor `2 ^ r₂` that cancels the
`(2⁻¹) ^ r₂` appearing in Mathlib's unweighted
`mixedEmbedding.covolume_idealLattice`. -/
theorem covolume_idealLattice (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    ZLattice.covolume (idealLattice K (𝔞 : FractionalIdeal (𝓞 K)⁰ K))
      = covolume K 𝔞 := by
  classical
  set I : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hI
  have hI0 : I ≠ 0 := by
    rw [hI]; exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr hne
  set I' : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 I hI0 with hI'
  set M := mixedEmbedding.idealLattice K I' with hM
  set c : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K) with hc
  haveI : (c • (volume : Measure (mixedSpace K))).IsAddHaarMeasure :=
    MeasureTheory.Measure.IsAddHaarMeasure.smul _ (by simp [hc]) (by simp [hc])
  -- `Λ(𝔞)` is the preimage lattice of `M` under `(toMinkowski K).symm`.
  have hLeq : ZLattice.comap ℝ M (toMinkowski K).symm.toLinearMap = idealLattice K I := by
    apply Submodule.ext
    intro x
    show (toMinkowski K).symm.toLinearMap.restrictScalars ℤ x ∈ M ↔ _
    show (toMinkowski K).symm x ∈ M ↔ _
    rw [hM, mixedEmbedding.mem_idealLattice, mem_idealLattice_iff]
    constructor
    · rintro ⟨a, ha, hax⟩
      have ha' : a ∈ (I : Submodule (𝓞 K) K) := ha
      refine ⟨a, ha', ?_⟩
      show toMinkowski K (mixedEmbedding K a) = x
      rw [hax, ContinuousLinearEquiv.apply_symm_apply]
    · rintro ⟨a, ha, hax⟩
      refine ⟨a, ?_, ?_⟩
      · exact ha
      · have heq : eEmb K a = toMinkowski K (mixedEmbedding K a) := rfl
        rw [← hax, heq, ContinuousLinearEquiv.symm_apply_apply]
  -- `(toMinkowski K).symm` maps `volume` to `c • volume`.
  have hmp : MeasurePreserving (toMinkowski K).symm (volume : Measure (minkowskiSpace K))
      (c • (volume : Measure (mixedSpace K))) :=
    ⟨(toMinkowski K).symm.continuous.measurable, by rw [hc, map_toMinkowski_symm_volume]⟩
  have hcov := ZLattice.covolume_comap M (c • volume) volume hmp
  rw [hLeq] at hcov
  -- `covolume M (c • volume) = c.toReal * covolume M volume`.
  set b := Module.Free.chooseBasis ℤ M with hb
  have hcv1 : ZLattice.covolume M (c • volume)
      = c.toReal * ZLattice.covolume M volume := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain M (c • volume)
        (ZLattice.isAddFundamentalDomain b (c • volume)),
      ZLattice.covolume_eq_measure_fundamentalDomain M volume
        (ZLattice.isAddFundamentalDomain b volume)]
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
      Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [hcv1] at hcov
  -- Assemble with Mathlib's unweighted covolume.
  rw [mixedEmbedding.covolume_idealLattice] at hcov
  have hctoReal : c.toReal = (2 : ℝ) ^ nrComplexPlaces K := by
    rw [hc, ENNReal.toReal_ofReal (by positivity)]
  rw [hctoReal] at hcov
  -- `2 ^ r₂ * (absNorm · * (2⁻¹) ^ r₂ * √|d|) = absNorm · * √|d|`.
  have habs : (FractionalIdeal.absNorm (I' : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
      = (Ideal.absNorm 𝔞 : ℝ) := by
    rw [hI', Units.val_mk0, hI, FractionalIdeal.coeIdeal_absNorm]
    push_cast; ring
  rw [hcov, covolume, ← habs]
  rw [show ((2 : ℝ) ^ nrComplexPlaces K)
        * ((FractionalIdeal.absNorm (I' : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
            * (2⁻¹) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)
      = (FractionalIdeal.absNorm (I' : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
          * (((2 : ℝ) ^ nrComplexPlaces K) * (2⁻¹) ^ nrComplexPlaces K)
          * Real.sqrt |(discr K : ℝ)| by ring]
  rw [← mul_pow]
  norm_num


/-! ## General Fourier linear change-of-variables law

Mathlib provides `fourier_comp_linearIsometry` (the Fourier transform commutes
with a linear *isometry*) but not the general law with a Jacobian factor and
the inverse-adjoint twist. We supply it here as a reusable lemma; the
Gaussian-scaling lemma `fourier_mixedGaussian_scaling` above consumes it. -/

section LinearChangeOfVariables

open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **Linear change of variables for the additive Haar measure `volume`.**
For a continuous linear automorphism `A` of a finite-dimensional real inner
product space, integrating `g ∘ A` against `volume` scales the integral of `g`
by the absolute value of the inverse Jacobian determinant `|det A|⁻¹`. The
formula holds for *any* `g` (even non-integrable), since it is proved through
the pushforward of `volume` along the measurable equivalence `A`. -/
lemma integral_comp_continuousLinearEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : V ≃L[ℝ] V) (g : V → F) :
    ∫ v, g (A v) = |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • ∫ u, g u := by
  by_cases hF : CompleteSpace F
  · have hdet : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := by
      have : IsUnit (LinearMap.det (A.toLinearEquiv : V →ₗ[ℝ] V)) :=
        LinearEquiv.isUnit_det' A.toLinearEquiv
      simpa using this.ne_zero
    have hmap : Measure.map A (volume : Measure V)
        = ENNReal.ofReal |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • (volume : Measure V) := by
      simpa using Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure V) hdet
    calc
      ∫ v, g (A v)
          = ∫ u, g u ∂(Measure.map A (volume : Measure V)) :=
            (integral_map_equiv A.toHomeomorph.toMeasurableEquiv g).symm
      _ = |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • ∫ u, g u := by
            rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]
  · simp [integral, hF]

/-- **General Fourier linear change-of-variables law.** For a continuous linear
automorphism `A` of a finite-dimensional real inner product space,

    𝓕 (f ∘ A) w = |det A|⁻¹ • 𝓕 f ((A⁻¹)ᴴ w),

where `(A⁻¹)ᴴ = ContinuousLinearMap.adjoint (A.symm)` is the inverse-adjoint of
`A`. This generalises Mathlib's `fourier_comp_linearIsometry` (the case `det = 1`
with `(A⁻¹)ᴴ = A`) to an arbitrary automorphism: the real-linear substitution
`u = A v` contributes the Jacobian `|det A|⁻¹` (`integral_comp_continuousLinearEquiv`),
and `⟪A.symm u, w⟫ = ⟪u, (A.symm)ᴴ w⟫` (`ContinuousLinearMap.adjoint_inner_right`)
moves the character argument to the inverse-adjoint. -/
lemma fourier_comp_continuousLinearEquiv (A : V ≃L[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (fun v => f (A v)) w
      = ((|(LinearMap.det (A : V →ₗ[ℝ] V))|⁻¹ : ℝ) : ℂ) •
          𝓕 f (ContinuousLinearMap.adjoint (A.symm : V →L[ℝ] V) w) := by
  -- Set `g u := 𝐞(-⟪A.symm u, w⟫) • f u`; then the Fourier integrand for `f ∘ A`
  -- equals `g ∘ A` pointwise, because `A.symm (A v) = v`.
  set g : V → ℂ := fun u => (Real.fourierChar (-⟪u, ContinuousLinearMap.adjoint
    (A.symm : V →L[ℝ] V) w⟫ : ℝ) : ℂ) • f u with hg
  have key : ∀ v : V, (Real.fourierChar (-⟪v, w⟫ : ℝ) : ℂ) • f (A v) = g (A v) := by
    intro v
    have hadj : (⟪(A v), ContinuousLinearMap.adjoint (A.symm : V →L[ℝ] V) w⟫ : ℝ)
        = ⟪v, w⟫ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
      simp
    simp only [hg]
    rw [hadj]
  rw [Real.fourier_eq]
  simp only [Circle.smul_def] at key ⊢
  rw [show (∫ v, (Real.fourierChar (-⟪v, w⟫ : ℝ) : ℂ) • f (A v))
        = ∫ v, g (A v) from integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [integral_comp_continuousLinearEquiv A g, Real.fourier_eq]
  simp only [hg, Circle.smul_def]
  rw [Complex.real_smul, smul_eq_mul, abs_inv]

end LinearChangeOfVariables

/-- **Multiplicative scaling of the Minkowski Gaussian's Fourier transform.**
For `x ∈ K_ℝ^*` (`mixedEmbedding.norm x ≠ 0`), the multiplicative scaling
`v ↦ x · v` on `mixedSpace K` is `ℝ`-linear with Jacobian determinant of
absolute value `|N(x)| = |mixedEmbedding.norm x|`; therefore the Fourier
transform of `v ↦ mixedGaussian (x · v)` (read on `minkowskiSpace K` through
`toMinkowski`) is `|N(x)|⁻¹` times `mixedGaussian` evaluated at the inverse
scaling `x⁻¹ · (·)`:

    𝓕 (v ↦ mixedGaussian (x · σ⁻¹ v)) w
      = |N(x)|⁻¹ · mixedGaussian (x⁻¹ · σ⁻¹ w),

where `σ⁻¹ = (toMinkowski K).symm`. This is the `|N(x)|`-Jacobian fact the
kernel inversion `mixedThetaKernel_inversion` consumes;
it combines the change-of-variables `u = x·v` (`|det| = |N(x)|`) with the
self-duality `fourier_gaussV` and the conjugation-invariance of the per-place
absolute values (so the inverse-adjoint and `x⁻¹`-scalings agree on `gaussV`). -/
theorem fourier_mixedGaussian_scaling (x : mixedEmbedding.mixedSpace K)
    (hx : mixedEmbedding.norm x ≠ 0) (w : minkowskiSpace K) :
    𝓕 (fun v : minkowskiSpace K =>
        (mixedGaussian K (x * (toMinkowski K).symm v) : ℂ)) w
      = ((|mixedEmbedding.norm x|⁻¹ : ℝ) : ℂ) *
          (mixedGaussian K (x⁻¹ * (toMinkowski K).symm w) : ℂ) := by
  -- Step 1: rewrite the integrand as `gaussV K ∘ A_x`.
  have hint : (fun v : minkowskiSpace K =>
      (mixedGaussian K (x * (toMinkowski K).symm v) : ℂ))
        = fun v : minkowskiSpace K => gaussV K (A_x K hx v) := by
    funext v
    rw [A_x_apply, mixedGaussian_eq]
  rw [hint]
  -- Step 2: apply the general |det|-Jacobian Fourier law.
  rw [fourier_comp_continuousLinearEquiv (A_x K hx) (gaussV K) w]
  -- Step 3: self-duality of `gaussV`.
  rw [fourier_gaussV]
  -- Step 4: rewrite the inverse-adjoint argument and the determinant.
  rw [A_x_symm_adjoint_gaussV, ← mixedGaussian_eq, A_x_det_abs]
  -- Step 5: convert the `•` on `ℂ` into the `*` product.
  rw [smul_eq_mul]

/-! ## Assembly of the kernel inversion law

With all analytic prerequisites in place (`mixedGaussianSchwartz`,
`fourier_mixedGaussian_scaling`, `covolume_idealLattice`,
`dualLattice_idealLattice`, the lattice instances and `idealLatticeEquiv`), we
now prove the corrected kernel inversion law by lattice Poisson summation
(`PoissonSummation.tsum_eq_tsum_fourier`).  The `+1`/`-1` constant correction
comes from the `g(0) = 1` lattice term, which is present on the whole-lattice
Poisson sum but excluded from the nonzero-element theta kernel. -/

/-- `mixedGaussian` at `0` is `1` (`g(0) = exp 0 = 1`). -/
theorem mixedGaussian_zero : mixedGaussian K 0 = 1 := by
  rw [mixedGaussian, Finset.sum_eq_zero (fun w _ => by
    rw [show normAtPlace w (0 : mixedSpace K) = 0 from map_zero (normAtPlace w)]; ring),
    mul_zero, Real.exp_zero]

/-- The Minkowski place-norm is invariant under the complex conjugation
`conjMixed` (real places are fixed; on complex places `‖conj z‖ = ‖z‖`). -/
theorem normAtPlace_conjMixed (w : InfinitePlace K) (ξ : mixedSpace K) :
    normAtPlace w (conjMixed K ξ) = normAtPlace w ξ := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, normAtPlace_apply_of_isReal hw, conjMixed_fst]
  · rw [normAtPlace_apply_of_isComplex hw, normAtPlace_apply_of_isComplex hw, conjMixed_snd,
      Complex.norm_conj]

/-- `mixedGaussian` is invariant under conjugating the second factor: since
`mixedGaussian` depends only on the per-place Minkowski norms, and
`normAtPlace w` is multiplicative (`map_mul`) and `conjMixed`-invariant
(`normAtPlace_conjMixed`), we have `g(z · conj ξ) = g(z · ξ)`.  This is what
makes the conjugation twist in `dualLattice_idealLattice` disappear from the
Gaussian dual sum. -/
theorem mixedGaussian_mul_conjMixed (z ξ : mixedSpace K) :
    mixedGaussian K (z * conjMixed K ξ) = mixedGaussian K (z * ξ) := by
  have hsum : ∀ w : InfinitePlace K,
      (InfinitePlace.mult w : ℝ) * normAtPlace w (z * conjMixed K ξ) ^ 2
        = (InfinitePlace.mult w : ℝ) * normAtPlace w (z * ξ) ^ 2 := by
    intro w
    rw [show normAtPlace w (z * conjMixed K ξ)
          = normAtPlace w z * normAtPlace w (conjMixed K ξ) from map_mul (normAtPlace w) _ _,
        show normAtPlace w (z * ξ) = normAtPlace w z * normAtPlace w ξ from map_mul (normAtPlace w) _ _,
        normAtPlace_conjMixed]
  rw [mixedGaussian, mixedGaussian, Finset.sum_congr rfl (fun w _ => hsum w)]

/-- **Summability of the multiplicatively-scaled Gaussian over a fractional
ideal** (for a unit `y`, `mixedEmbedding.norm y ≠ 0`): the family
`a ↦ g(y · σ(a))` over `a ∈ J` is summable, being the Schwartz function
`mixedGaussianSchwartz K hy` restricted to the lattice `Λ(J)` and reindexed
through `idealLatticeEquiv`. -/
theorem summable_mixedGaussian_submodule (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) :
    Summable (fun a : (J : Submodule (𝓞 K) K) =>
      (mixedGaussian K (y * mixedEmbedding K (a : K)) : ℂ)) := by
  haveI := discreteTopology_idealLattice K J hJ
  haveI := isZLattice_idealLattice K J hJ
  have hL : Summable (fun v : idealLattice K J =>
      (mixedGaussianSchwartz K hy : minkowskiSpace K → ℂ) v) := by
    have h := PoissonSummation.summable_periodisation (idealLattice K J)
      (mixedGaussianSchwartz K hy) 0
    simpa using h
  have h2 := (Equiv.summable_iff (idealLatticeEquiv K J)).mpr hL
  refine h2.congr (fun a => ?_)
  simp only [Function.comp_apply]
  rw [mixedGaussianSchwartz_apply]
  have hv : ((idealLatticeEquiv K J a : idealLattice K J) : minkowskiSpace K)
      = toMinkowski K (mixedEmbedding K (a : K)) := rfl
  rw [hv, ContinuousLinearEquiv.symm_apply_apply]

/-- **Whole-lattice Gaussian sum splits off the `g(0) = 1` term.** Summing the
scaled Gaussian over *all* of `J` (including `0`) gives `1` (from `a = 0`) plus
the nonzero-element theta kernel `mixedThetaKernel K J y`. -/
theorem tsum_mixedGaussian_submodule (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) :
    ∑' a : (J : Submodule (𝓞 K) K), (mixedGaussian K (y * mixedEmbedding K (a : K)) : ℂ)
      = 1 + mixedThetaKernel K J y := by
  classical
  set G := fun (a : (J : Submodule (𝓞 K) K)) =>
    (mixedGaussian K (y * mixedEmbedding K (a : K)) : ℂ) with hG
  have hsum : Summable G := summable_mixedGaussian_submodule K J hJ hy
  set z₀ : (J : Submodule (𝓞 K) K) := ⟨0, (J : Submodule (𝓞 K) K).zero_mem⟩ with hz₀
  rw [hsum.tsum_eq_add_tsum_ite z₀]
  have hG0 : G z₀ = 1 := by
    show (mixedGaussian K (y * mixedEmbedding K ((z₀ : (J : Submodule (𝓞 K) K)) : K)) : ℂ) = 1
    rw [show ((z₀ : (J : Submodule (𝓞 K) K)) : K) = 0 from rfl, map_zero, mul_zero,
      mixedGaussian_zero, Complex.ofReal_one]
  rw [hG0]
  congr 1
  -- The remaining `ite`-sum is the nonzero-element kernel.
  set S := {a : K // a ∈ (J : Submodule (𝓞 K) K) ∧ a ≠ 0} with hS
  let eJc : ↥(({z₀} : Set (J : Submodule (𝓞 K) K))ᶜ) ≃ S :=
  { toFun := fun a => ⟨((a : (J : Submodule (𝓞 K) K)) : K), (a : (J : Submodule (𝓞 K) K)).2, by
        intro h0
        apply a.2
        apply Subtype.ext
        exact h0⟩
    invFun := fun s => ⟨⟨s.1, s.2.1⟩, by
        intro h
        exact s.2.2 (congrArg (fun t : (J : Submodule (𝓞 K) K) => (t : K)) h)⟩
    left_inv := fun a => by apply Subtype.ext; rfl
    right_inv := fun s => by apply Subtype.ext; rfl }
  have hite : (fun a : (J : Submodule (𝓞 K) K) => ite (a = z₀) (0 : ℂ) (G a))
      = (({z₀} : Set (J : Submodule (𝓞 K) K))ᶜ).indicator G := by
    funext a
    rw [Set.indicator_apply]
    by_cases h : a = z₀
    · simp [h]
    · simp [h, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [hite, ← tsum_subtype ({z₀} : Set (J : Submodule (𝓞 K) K))ᶜ G, mixedThetaKernel,
    ← Equiv.tsum_eq eJc (fun s => (mixedGaussian K (y * mixedEmbedding K (s : K)) : ℂ))]
  exact tsum_congr (fun x => rfl)

/-- **Kernel inversion law via Poisson summation** (the standard treatment at
the multiplicative lattice level): for a nonzero integral ideal `𝔞` and a unit
`x ∈ K_ℝ^*` (`N(x) ≠ 0`),

    Θ(𝔞, x⁻¹) = (|N(x)| / vol(Λ(𝔞))) · (Θ((𝔞𝔡)⁻¹, x) + 1) - 1,

where `vol(Λ(𝔞)) = covolume K 𝔞` and `(𝔞𝔡)⁻¹ = dualIdeal K 𝔞`.  The proof
applies lattice Poisson summation to the Schwartz Gaussian
`mixedGaussianSchwartz K hxinv` over `Λ(𝔞)`: the primal whole-lattice sum is
`1 + Θ(𝔞, x⁻¹)` (`tsum_mixedGaussian_submodule`), and the Fourier side, via
`fourier_mixedGaussian_scaling` (Jacobian `|N(x)|`) and the conjugation-twisted
dual lattice `dualLattice_idealLattice` (the twist is absorbed by
`mixedGaussian_mul_conjMixed`), is `|N(x)| · (1 + Θ((𝔞𝔡)⁻¹, x))`; the covolume
constant is `covolume_idealLattice`.  The `+1`/`-1` correction is the
asymmetric `g(0) = 1` term and is essential (the clean form is false). -/
theorem mixedThetaKernel_inversion (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    (x : mixedEmbedding.mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    mixedThetaKernel K (𝔞 : FractionalIdeal (𝓞 K)⁰ K) x⁻¹ =
      ((|mixedEmbedding.norm x| / covolume K 𝔞 : ℝ) : ℂ) *
        (mixedThetaKernel K (dualIdeal K 𝔞) x + 1) - 1 := by
  classical
  set I : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hIdef
  have hI : I ≠ 0 := by rw [hIdef]; exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr hne
  -- The dual ideal is nonzero (inverse of a nonzero fractional ideal).
  have hdiff : differentFractionalIdeal K ≠ 0 := by
    rw [differentFractionalIdeal]
    exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr differentIdeal_ne_bot
  have hD : dualIdeal K 𝔞 ≠ 0 := by
    rw [dualIdeal]
    exact inv_ne_zero (mul_ne_zero (by rw [← hIdef]; exact hI) hdiff)
  -- Inverse-scaling facts: `N(x⁻¹) ≠ 0` and `|N(x⁻¹)|⁻¹ = |N(x)|`.
  have hxx : x * x⁻¹ = 1 := mul_inv_cancel_of_norm_ne_zero K hx
  have hN1 : mixedEmbedding.norm x * mixedEmbedding.norm x⁻¹ = 1 := by
    rw [← map_mul, hxx, map_one]
  have hxinv : mixedEmbedding.norm x⁻¹ ≠ 0 := by
    intro h; rw [h, mul_zero] at hN1; exact one_ne_zero hN1.symm
  have hb : mixedEmbedding.norm x⁻¹ = (mixedEmbedding.norm x)⁻¹ :=
    eq_inv_of_mul_eq_one_right hN1
  have hAbs : |mixedEmbedding.norm x⁻¹|⁻¹ = |mixedEmbedding.norm x| := by
    rw [hb, abs_inv, inv_inv]
  -- Lattice instances on `Λ(𝔞)`.
  haveI := discreteTopology_idealLattice K I hI
  haveI := isZLattice_idealLattice K I hI
  -- Lattice Poisson summation for the scaled Gaussian Schwartz function.
  have hPoisson := PoissonSummation.tsum_eq_tsum_fourier (idealLattice K I)
    (mixedGaussianSchwartz K hxinv)
  -- Primal side: `∑_{v ∈ Λ(𝔞)} g(x⁻¹·σ⁻¹ v) = 1 + Θ(𝔞, x⁻¹)`.
  have hprimal : ∑' v : idealLattice K I,
        (mixedGaussianSchwartz K hxinv : minkowskiSpace K → ℂ) v
      = 1 + mixedThetaKernel K I x⁻¹ := by
    rw [← tsum_mixedGaussian_submodule K I hI hxinv,
      ← Equiv.tsum_eq (idealLatticeEquiv K I)
        (fun v : idealLattice K I => (mixedGaussianSchwartz K hxinv : minkowskiSpace K → ℂ) v)]
    refine tsum_congr (fun a => ?_)
    rw [mixedGaussianSchwartz_apply]
    have hv : ((idealLatticeEquiv K I a : idealLattice K I) : minkowskiSpace K)
        = toMinkowski K (mixedEmbedding K (a : K)) := rfl
    rw [hv, ContinuousLinearEquiv.symm_apply_apply]
  -- Dual lattice reindexing equiv `(𝔞𝔡)⁻¹ ≃ dualLattice Λ(𝔞)` via `conjMink ∘ eEmb`.
  let φD := fun (a : (dualIdeal K 𝔞 : Submodule (𝓞 K) K)) =>
    (⟨conjMink K (eEmb K (a : K)), by
      rw [dualLattice_idealLattice K 𝔞 hne]
      exact Submodule.mem_map.mpr ⟨eEmb K (a : K),
        (mem_idealLattice_iff K (dualIdeal K 𝔞) _).mpr ⟨(a : K), a.2, rfl⟩, rfl⟩⟩ :
      PoissonSummation.dualLattice (idealLattice K I))
  have hφD_inj : Function.Injective φD := by
    intro a b h
    have h1 : conjMink K (eEmb K (a : K)) = conjMink K (eEmb K (b : K)) := Subtype.ext_iff.mp h
    exact Subtype.ext (eEmb_injective K ((conjMink K).injective h1))
  have hφD_surj : Function.Surjective φD := by
    rintro ⟨w, hw⟩
    rw [dualLattice_idealLattice K 𝔞 hne] at hw
    obtain ⟨u, hu, hφu⟩ := Submodule.mem_map.mp hw
    obtain ⟨b, hb, hbu⟩ := (mem_idealLattice_iff K (dualIdeal K 𝔞) u).mp hu
    refine ⟨⟨b, hb⟩, ?_⟩
    apply Subtype.ext
    show conjMink K (eEmb K b) = w
    rw [hbu]; exact hφu
  let eD := Equiv.ofBijective φD ⟨hφD_inj, hφD_surj⟩
  -- Dual side: `∑_{w ∈ Λ(𝔞)*} 𝓕 f w = |N(x)| · (Θ((𝔞𝔡)⁻¹, x) + 1)`.
  have hDsum : ∑' w : PoissonSummation.dualLattice (idealLattice K I),
        (mixedGaussian K (x * (toMinkowski K).symm (w : minkowskiSpace K)) : ℂ)
      = 1 + mixedThetaKernel K (dualIdeal K 𝔞) x := by
    rw [← tsum_mixedGaussian_submodule K (dualIdeal K 𝔞) hD hx,
      ← Equiv.tsum_eq eD
        (fun w : PoissonSummation.dualLattice (idealLattice K I) =>
          (mixedGaussian K (x * (toMinkowski K).symm (w : minkowskiSpace K)) : ℂ))]
    refine tsum_congr (fun a => ?_)
    have hval : ((eD a : PoissonSummation.dualLattice (idealLattice K I)) : minkowskiSpace K)
        = conjMink K (eEmb K (a : K)) := rfl
    rw [hval]
    have hpre : (eEmbℝ K).symm (eEmb K (a : K)) = mixedEmbedding K (a : K) := by
      rw [← eEmbℝ_mixedEmbedding K (a : K), ContinuousLinearEquiv.symm_apply_apply]
    have h1 : conjMink K (eEmb K (a : K))
        = toMinkowski K (conjMixed K (mixedEmbedding K (a : K))) := by
      rw [conjMink_apply, hpre]
    rw [h1, ContinuousLinearEquiv.symm_apply_apply, mixedGaussian_mul_conjMixed]
  have hdual : ∑' w : PoissonSummation.dualLattice (idealLattice K I),
        𝓕 (mixedGaussianSchwartz K hxinv : minkowskiSpace K → ℂ) (w : minkowskiSpace K)
      = ((|mixedEmbedding.norm x| : ℝ) : ℂ) * (mixedThetaKernel K (dualIdeal K 𝔞) x + 1) := by
    have hpt : ∀ w : PoissonSummation.dualLattice (idealLattice K I),
        𝓕 (mixedGaussianSchwartz K hxinv : minkowskiSpace K → ℂ) (w : minkowskiSpace K)
          = ((|mixedEmbedding.norm x| : ℝ) : ℂ) *
              (mixedGaussian K (x * (toMinkowski K).symm (w : minkowskiSpace K)) : ℂ) := by
      intro w
      have hFeq : (mixedGaussianSchwartz K hxinv : minkowskiSpace K → ℂ)
          = fun v => (mixedGaussian K (x⁻¹ * (toMinkowski K).symm v) : ℂ) := by
        funext v; exact mixedGaussianSchwartz_apply K hxinv v
      rw [hFeq, fourier_mixedGaussian_scaling K x⁻¹ hxinv (w : minkowskiSpace K), hAbs, inv_inv]
    rw [tsum_congr hpt, tsum_mul_left, hDsum, add_comm (1 : ℂ)]
  -- Combine, identify the covolume, and solve for `Θ(𝔞, x⁻¹)`.
  rw [hprimal, hdual] at hPoisson
  have hcov : ZLattice.covolume (idealLattice K I) = covolume K 𝔞 := by
    rw [hIdef]; exact covolume_idealLattice K 𝔞 hne
  rw [hcov] at hPoisson
  have hgoaldiv : ((|mixedEmbedding.norm x| / covolume K 𝔞 : ℝ) : ℂ)
      = ((|mixedEmbedding.norm x| : ℝ) : ℂ) / ((covolume K 𝔞 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hgoaldiv]
  linear_combination hPoisson

/-- **Inversion law for the integral kernel** (the exact form consumed by the
Mellin step): for a nonzero integral ideal `𝔞` and
`x ∈ K_ℝ^*`,

    idealThetaKernel K 𝔞 x⁻¹
      = (|N(x)| / vol(Λ(𝔞))) · (mixedThetaKernel K ((𝔞𝔡)⁻¹) x + 1) - 1.

Proved by rewriting the integral kernel as the fractional kernel
(`idealThetaKernel_eq_mixed`) and applying `mixedThetaKernel_inversion`. -/
theorem idealThetaKernel_inversion (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    (x : mixedEmbedding.mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    idealThetaKernel K 𝔞 x⁻¹ =
      ((|mixedEmbedding.norm x| / covolume K 𝔞 : ℝ) : ℂ) *
        (mixedThetaKernel K (dualIdeal K 𝔞) x + 1) - 1 := by
  rw [idealThetaKernel_eq_mixed]
  exact mixedThetaKernel_inversion K 𝔞 hne x hx


end

end DedekindZeta.Theta

/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: mathlib-initiative/sum_product at 80e4127a67742659d521466204c6d2d7e0ca2b3f.
- Formalization note: Lean 4.33.1 compatibility port with narrow imports for DedekindZeta.Theta.
- PROVENANCE-END
-/
