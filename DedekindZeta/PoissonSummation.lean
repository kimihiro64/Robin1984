/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Data.Finset.Functor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Abstract lattice Poisson summation

This module provides the **multidimensional Poisson summation formula** over an
arbitrary full-rank lattice in a finite-dimensional real inner product space.
It is the piece of analytic infrastructure that the Minkowski theta kernel
inversion law `DedekindZeta.Theta.mixedThetaKernel_inversion` requires. That
inversion law is used by the theta-series material following Neukirch,
*Algebraic Number Theory*, Chapter VII §§3 and 5. The multidimensional formula
is **absent from Mathlib v4.30.0**: Mathlib only proves the one-variable Poisson
summation formula (`Real.tsum_eq_tsum_fourier_of_rpow_decay`,
`SchwartzMap.tsum_eq_tsum_fourier` in
`Mathlib/Analysis/Fourier/PoissonSummation.lean`).

## Conventions

* `V` is a finite-dimensional real inner product space, equipped with the
  canonical Lebesgue–Haar measure `volume` coming from the global
  `measureSpaceOfInnerProductSpace` instance. This is **the same** measure that
  defines Mathlib's Fourier transform `𝓕`, so the `𝓕`-relating statements below
  are exact (no shadowing free `[MeasureSpace V]` instance).
* `L : Submodule ℤ V` is a full-rank lattice (`[DiscreteTopology L]`,
  `[IsZLattice ℝ L]`).
* The Fourier transform is Mathlib's `𝓕`, i.e.
  `𝓕 f w = ∫ v, exp (-2πi⟪v, w⟫) • f v` (the `exp(-2πi⟪x,ξ⟫)` convention used
  throughout the development; see `Mathlib/Analysis/Fourier/FourierTransform.lean`).
* `ZLattice.covolume L` is the covolume `vol(L)` of the lattice (volume of a
  fundamental domain), and the **dual lattice** is
  `dualLattice L = {w | ∀ v ∈ L, ⟪w, v⟫ ∈ ℤ}`, realised through Mathlib's
  `LinearMap.BilinForm.dualSubmodule` for the inner-product bilinear form
  `innerₗ V`.

With these conventions the Poisson summation formula reads

    ∑_{v ∈ L} f(v) = (1 / vol(L)) · ∑_{w ∈ L*} f̂(w).

The constant is the faithful `vol(L)⁻¹`; both measures (the one defining the
covolume and the one defining `𝓕`) are the same `volume`, so the identity is
internally consistent for any choice of Haar normalisation on `V`.
-/

open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace

namespace DedekindZeta.PoissonSummation

-- We deliberately do **not** introduce a free `[MeasureSpace V]` here: the
-- ambient `volume` must be the canonical `measureSpaceOfInnerProductSpace`
-- instance (`Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean`), which is
-- exactly the measure that defines Mathlib's Fourier transform `𝓕`
-- (`Real.instFourierTransform`). A free `[MeasureSpace V]` would shadow that
-- instance and the `∫_D … = 𝓕 f w` statements would be off by a Haar
-- normalisation constant. Supplying
-- `[MeasurableSpace V] [BorelSpace V]` makes `measureSpaceOfInnerProductSpace`
-- (priority 100) provide the `MeasureSpace`/`volume`, and the sibling instance
-- in the same file makes that `volume` add-Haar automatically.
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The **dual lattice** `L* = {w | ∀ v ∈ L, ⟪w, v⟫ ∈ ℤ}` of a lattice
`L ⊆ V` with respect to the inner product, realised through Mathlib's
`LinearMap.BilinForm.dualSubmodule` for the inner-product bilinear form
`innerₗ V`. -/
noncomputable def dualLattice (L : Submodule ℤ V) : Submodule ℤ V :=
  LinearMap.BilinForm.dualSubmodule (innerₗ V) L

theorem mem_dualLattice {L : Submodule ℤ V} {w : V} :
    w ∈ dualLattice L ↔ ∀ v ∈ L, (⟪w, v⟫ : ℝ) ∈ (1 : Submodule ℤ ℝ) :=
  Iff.rfl

/-! ## Lattice structure of the dual lattice

The dual lattice of a full-rank lattice is again a full-rank lattice. We obtain
this through Mathlib's bilinear-form dual-basis machinery: writing `L` as the
ℤ-span of an ℝ-basis `B` of `V` (via `Basis.ofZLatticeBasis`), the dual lattice
`dualLattice L = (innerₗ V).dualSubmodule L` is, by
`LinearMap.BilinForm.dualSubmodule_span_of_basis` (using that the inner-product
form `innerₗ V` is nondegenerate), the ℤ-span of the dual basis
`(innerₗ V).dualBasis _ B`, which is again an ℝ-basis of `V`. The ℤ-span of an
ℝ-basis is a full-rank `ZLattice`, supplying both instances below. -/

/-- The inner-product bilinear form `innerₗ V` is nondegenerate: if `⟪x, y⟫ = 0`
for all `y`, then in particular `⟪x, x⟫ = 0`, so `x = 0`. -/
theorem innerₗ_nondegenerate : (innerₗ V).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h := hx x
    rw [innerₗ_apply_apply] at h
    exact inner_self_eq_zero.mp h
  · have h := hy y
    rw [innerₗ_apply_apply] at h
    exact inner_self_eq_zero.mp h

/-- `dualLattice L` is the ℤ-span of the dual basis (an ℝ-basis of `V`) of any
ℤ-basis of `L`. -/
theorem dualLattice_eq_span_dualBasis (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    letI := Classical.decEq (Module.Free.ChooseBasisIndex ℤ L)
    dualLattice L = Submodule.span ℤ (Set.range
      (LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate
        ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))) := by
  classical
  set b := Module.Free.chooseBasis ℤ L with hb
  set B : Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ V := b.ofZLatticeBasis ℝ L with hB
  have hLspan : L = Submodule.span ℤ (Set.range B) := (b.ofZLatticeBasis_span ℝ).symm
  change LinearMap.BilinForm.dualSubmodule (innerₗ V) L = _
  -- Rewrite the explicit `L` argument only (a plain `rw [hLspan]` would also try
  -- to rewrite the `L` hidden inside `B = b.ofZLatticeBasis ℝ L`).
  exact (congrArg (LinearMap.BilinForm.dualSubmodule (innerₗ V)) hLspan).trans
    (LinearMap.BilinForm.dualSubmodule_span_of_basis _ innerₗ_nondegenerate B)

instance instDiscreteTopologyDualLattice (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] : DiscreteTopology (dualLattice L) := by
  classical
  rw [dualLattice_eq_span_dualBasis L]
  infer_instance


/-! ## Periodisation over the lattice

The standard route to lattice Poisson summation is via the **periodisation**
`F(x) = ∑_{v ∈ L} f(x + v)` of a Schwartz function `f`. It is summable for
every `x` (rapid Schwartz decay against the polynomially-controlled lattice
sum), `L`-periodic, continuous, and therefore descends to a continuous function
on the compact torus `V ⧸ L`. -/

section Periodisation

variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)

/-- The **periodisation** of a Schwartz function `f` over the lattice `L`:
`periodisation f x = ∑' v : L, f (x + v)`. (the analytic material, the standard
torus-Fourier route to lattice Poisson summation.) -/
noncomputable def periodisation : V → ℂ := fun x => ∑' v : L, (f : V → ℂ) (x + v)

theorem periodisation_apply (x : V) :
    periodisation L f x = ∑' v : L, (f : V → ℂ) (x + v) := rfl

/-- For every `x`, the family `v ↦ f (x + v)` over the lattice `L` is summable:
this is Schwartz rapid decay against the polynomially-bounded lattice
(`ZLattice.summable_norm_sub_rpow` controls `∑_{v∈L} ‖v - y‖^r` for `r < -d`,
and `SchwartzMap.isBigO_cocompact_zpow` bounds `f`). -/
theorem summable_periodisation (x : V) :
    Summable fun v : L => (f : V → ℂ) (x + v) := by
  classical
  set d : ℕ := Module.finrank ℤ L with hd
  -- The exponent `s = -(d+1) < -d` controlling both the Schwartz decay and the
  -- lattice sum.
  set s : ℝ := -(d : ℝ) - 1 with hs
  have hsd : s < -(Module.finrank ℤ L : ℝ) := by rw [hs, ← hd]; linarith
  -- Schwartz rapid decay: `f =O[cocompact V] (‖·‖ ^ s)` (`ProperSpace V` from
  -- finite dimensionality). See `SchwartzMap.isBigO_cocompact_rpow`.
  have hfO : (f : V → ℂ) =O[Filter.cocompact V] fun y => ‖y‖ ^ s :=
    f.isBigO_cocompact_rpow s
  -- The translated lattice inclusion `v ↦ x + v` tends to `cocompact V` along
  -- `cofinite`: the lattice is a closed discrete set, so its inclusion does
  -- (`tendsto_cofinite_cocompact_of_discrete`), and translation by `x` is a
  -- homeomorphism, hence proper.
  have hLclosed : IsClosed (X := V) (L : Set V) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hcoe : Filter.Tendsto ((↑) : L → V) Filter.cofinite (Filter.cocompact V) :=
    tendsto_cofinite_cocompact_of_discrete
      hLclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have htrans : Filter.Tendsto (fun y : V => x + y)
      (Filter.cocompact V) (Filter.cocompact V) :=
    (Homeomorph.addLeft x).isClosedEmbedding.tendsto_cocompact
  have he : Filter.Tendsto (fun v : L => x + (v : V))
      Filter.cofinite (Filter.cocompact V) := htrans.comp hcoe
  -- Compose the decay estimate with the translated inclusion.
  have hbo : (fun v : L => (f : V → ℂ) (x + v)) =O[Filter.cofinite]
      fun v : L => ‖x + (v : V)‖ ^ s := hfO.comp_tendsto he
  -- The polynomial lattice sum converges (`ZLattice.summable_norm_sub_rpow`).
  have hsum : Summable fun v : L => ‖x + (v : V)‖ ^ s := by
    have := ZLattice.summable_norm_sub_rpow L s hsd (-x)
    refine this.congr fun v => ?_
    rw [sub_neg_eq_add, add_comm]
  exact summable_of_isBigO hsum hbo

/-- `L`-periodicity of the periodisation: `F(x + v) = F(x)` for `v ∈ L`
(reindex the lattice sum by translation). -/
theorem periodisation_add_mem (x : V) {v : V} (hv : v ∈ L) :
    periodisation L f (x + v) = periodisation L f x := by
  rw [periodisation_apply, periodisation_apply]
  have hreindex :=
    Equiv.tsum_eq (Equiv.addRight (⟨v, hv⟩ : L))
      (fun w : L => (f : V → ℂ) (x + w))
  rw [← hreindex]
  refine tsum_congr fun w => ?_
  congr 1
  simp only [Equiv.coe_addRight, Submodule.coe_add]
  abel

/-- The periodisation evaluated at `0` is the lattice sum `∑_{v∈L} f v`. -/
theorem periodisation_zero : periodisation L f 0 = ∑' v : L, (f : V → ℂ) v := by
  simp only [periodisation_apply, zero_add]

/-- The periodisation is continuous (locally uniform convergence of the Schwartz
lattice sum). -/
theorem continuous_periodisation : Continuous (periodisation L f) := by
  classical
  -- Continuity is local; we prove `ContinuousAt` at every point `x₀` by exhibiting
  -- a uniform (cofinite) Schwartz tail bound on the open ball `Metric.ball x₀ 1`.
  rw [continuous_iff_continuousAt]
  intro x₀
  set d : ℕ := Module.finrank ℤ L with hd
  set N : ℕ := d + 1 with hN
  -- The real exponent `s = -(d+1) < -d` controlling the lattice sum.
  set s : ℝ := -(N : ℝ) with hs
  have hsd : s < -(Module.finrank ℤ L : ℝ) := by
    rw [hs, hN, ← hd]; push_cast; linarith
  -- The neighbourhood: the unit ball around `x₀`. On it `‖x‖ ≤ C₀ := ‖x₀‖ + 1`.
  set C₀ : ℝ := ‖x₀‖ + 1 with hC₀
  have hC₀pos : 0 < C₀ := by positivity
  have hxle : ∀ x ∈ Metric.ball x₀ 1, ‖x‖ ≤ C₀ := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
      _ ≤ ‖x₀‖ + 1 := by have h := hx.le; gcongr
  -- Schwartz decay with `k = N`: `‖y‖ ^ N * ‖f y‖ ≤ C`.
  obtain ⟨C, hCpos, hC⟩ := f.decay N 0
  have hC' : ∀ y : V, ‖y‖ ^ N * ‖(f : V → ℂ) y‖ ≤ C := by
    intro y; have := hC y; rwa [norm_iteratedFDeriv_zero] at this
  -- The dominating function `u v = C · 2^N · ‖v‖ ^ s`, summable over the lattice.
  set u : L → ℝ := fun v => C * 2 ^ N * ‖(v : V)‖ ^ s with hu_def
  have husum : Summable u := by
    have h0 := ZLattice.summable_norm_sub_rpow L s hsd 0
    have h0' : Summable fun v : L => ‖(v : V)‖ ^ s := by
      refine h0.congr fun v => ?_; rw [sub_zero]
    exact h0'.mul_left (C * 2 ^ N)
  -- The lattice inclusion tends to `cocompact V` along `cofinite`, so `‖v‖ → ∞`.
  have hLclosed : IsClosed (X := V) (L : Set V) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hcoe : Filter.Tendsto ((↑) : L → V) Filter.cofinite (Filter.cocompact V) :=
    tendsto_cofinite_cocompact_of_discrete
      hLclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hnorm : Filter.Tendsto (fun v : L => ‖(v : V)‖) Filter.cofinite Filter.atTop :=
    tendsto_norm_cocompact_atTop.comp hcoe
  -- The eventual (cofinite) uniform tail bound on the ball.
  have hfu : ∀ᶠ v : L in Filter.cofinite,
      ∀ x ∈ Metric.ball x₀ 1, ‖(fun x => (f : V → ℂ) (x + v)) x‖ ≤ u v := by
    filter_upwards [hnorm.eventually_ge_atTop (2 * C₀)] with v hv x hx
    have hxC₀ : ‖x‖ ≤ C₀ := hxle x hx
    have hbpos : 0 < ‖(v : V)‖ := lt_of_lt_of_le (by positivity) hv
    -- `a := ‖x + v‖ ≥ ‖v‖ / 2 > 0`.
    have hage : ‖(v : V)‖ / 2 ≤ ‖x + (v : V)‖ := by
      have h1 : ‖(v : V)‖ - ‖x‖ ≤ ‖x + (v : V)‖ := by
        have htri : ‖(v : V)‖ ≤ ‖x + (v : V)‖ + ‖x‖ := by
          calc ‖(v : V)‖ = ‖(x + (v : V)) - x‖ := by rw [add_sub_cancel_left]
            _ ≤ ‖x + (v : V)‖ + ‖x‖ := norm_sub_le _ _
        linarith
      have h2 : ‖(v : V)‖ / 2 ≤ ‖(v : V)‖ - ‖x‖ := by
        have : ‖x‖ ≤ ‖(v : V)‖ / 2 := by
          have : C₀ ≤ ‖(v : V)‖ / 2 := by linarith
          linarith
        linarith
      linarith
    have hapos : 0 < ‖x + (v : V)‖ := lt_of_lt_of_le (by positivity) hage
    -- From decay: `‖f(x+v)‖ ≤ C / ‖x+v‖^N`.
    have hfle : ‖(f : V → ℂ) (x + (v : V))‖ ≤ C / ‖x + (v : V)‖ ^ N := by
      rw [le_div_iff₀ (by positivity)]
      have := hC' (x + (v : V))
      linarith [this, mul_comm (‖x + (v:V)‖ ^ N) (‖(f:V→ℂ) (x+(v:V))‖)]
    -- `‖x+v‖^N ≥ (‖v‖/2)^N = ‖v‖^N / 2^N`.
    have hpow : (‖(v : V)‖ / 2) ^ N ≤ ‖x + (v : V)‖ ^ N := by
      gcongr
    have hpow' : ‖(v : V)‖ ^ N / 2 ^ N ≤ ‖x + (v : V)‖ ^ N := by
      rw [div_pow] at hpow; exact hpow
    -- Combine and rewrite `‖v‖^s = (‖v‖^N)⁻¹`.
    have hrpow : ‖(v : V)‖ ^ s = (‖(v : V)‖ ^ N)⁻¹ := by
      rw [hs, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    show ‖(f : V → ℂ) (x + (v : V))‖ ≤ C * 2 ^ N * ‖(v : V)‖ ^ s
    rw [hrpow]
    have hvN : (0 : ℝ) < ‖(v : V)‖ ^ N := by positivity
    calc ‖(f : V → ℂ) (x + (v : V))‖
        ≤ C / ‖x + (v : V)‖ ^ N := hfle
      _ ≤ C / (‖(v : V)‖ ^ N / 2 ^ N) := by
            apply div_le_div_of_nonneg_left (le_of_lt hCpos) (by positivity) hpow'
      _ = C * 2 ^ N * (‖(v : V)‖ ^ N)⁻¹ := by
            rw [div_div_eq_mul_div, div_eq_mul_inv]
  -- Uniform convergence of the partial sums on the ball, hence continuity there.
  have hcont : ∀ v : L, Continuous (fun x => (f : V → ℂ) (x + v)) := fun v =>
    f.continuous.comp (by fun_prop)
  have htu : TendstoUniformlyOn
      (fun t : Finset L => fun x => ∑ v ∈ t, (f : V → ℂ) (x + v))
      (periodisation L f) Filter.atTop (Metric.ball x₀ 1) := by
    have := tendstoUniformlyOn_tsum_of_cofinite_eventually husum hfu
    exact this
  have hcontOn : ContinuousOn (periodisation L f) (Metric.ball x₀ 1) :=
    htu.continuousOn (Filter.Eventually.frequently <| Filter.Eventually.of_forall fun t =>
      continuousOn_finsetSum t fun v _ => (hcont v).continuousOn)
  exact hcontOn.continuousAt (Metric.ball_mem_nhds x₀ one_pos)

/-! ### Descent to the compact torus `V ⧸ L`

We use `L.toAddSubgroup` and the quotient additive group `V ⧸ L.toAddSubgroup`,
which carries Mathlib's quotient topology and is a topological additive group.
For a full-rank lattice it is **compact**. -/


/-- The **continuous descent** of the periodisation to the compact torus
`V ⧸ L`. Well-defined by `L`-periodicity (`periodisation_add_mem`). -/
noncomputable def periodisationTorus : (V ⧸ L.toAddSubgroup) → ℂ := fun q =>
  Quotient.liftOn' q (periodisation L f) <| by
    intro a b h
    rw [QuotientAddGroup.leftRel_apply] at h
    have hv : -a + b ∈ L := by simpa using h
    have : periodisation L f (a + (-a + b)) = periodisation L f a :=
      periodisation_add_mem L f a hv
    simpa using this.symm

theorem periodisationTorus_mk (x : V) :
    periodisationTorus L f (QuotientAddGroup.mk x) = periodisation L f x := rfl

/-- The descended periodisation is continuous on the torus `V ⧸ L`
(from continuity of `periodisation` and the quotient topology). -/
theorem continuous_periodisationTorus : Continuous (periodisationTorus L f) :=
  -- A map out of the quotient (coinduced) topology is continuous iff its
  -- composite with the quotient map is; that composite is `periodisation L f`.
  (continuous_periodisation L f).quotient_liftOn' _

end Periodisation

/-! ## Fourier coefficients of the periodisation

For `w ∈ dualLattice L`, the dual character `x ↦ 𝐞(⟪w, x⟫)` is `L`-periodic
(since `⟪w, v⟫ ∈ ℤ` for `v ∈ L`), so it descends to the torus `V ⧸ L`. The
`w`-th Fourier coefficient of the periodisation `F` over the torus, with the
integral taken over a fundamental domain `D` of `L`, is

    c_w = (vol L)⁻¹ · ∫_D 𝐞(-⟪x, w⟫) • F(x) dx = (vol L)⁻¹ · 𝓕 f w.

The key computation `∫_D 𝐞(-⟪x,w⟫)•F(x) = 𝓕 f w` unfolds the lattice sum in
`F` and, using the `L`-periodicity of the character, recombines the integral
over the fundamental domain into the full Fourier integral over `V`; the
covolume enters only through the `(vol L)⁻¹` normalisation of the torus
Fourier coefficient. -/

section FourierCoefficients

variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)

/-- **Unfolding the Fourier coefficient integral.** For `w ∈ dualLattice L`
and any fundamental domain `D` of the lattice `L`, the integral of the
periodisation `F` against the dual character `x ↦ 𝐞(-⟪x, w⟫)` over `D` equals
the full Fourier transform `𝓕 f w`. (Unfold `F(x) = ∑_{v∈L} f(x+v)`; the
character is `L`-periodic because `⟪w, v⟫ ∈ ℤ`, so `∑_{v∈L} ∫_D = ∫_V`, the
full Fourier integral.) The `exp(-2πi⟪·,w⟫)` convention matches `𝓕`. -/
theorem integral_fundamentalDomain_periodisation
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    (w : dualLattice L) :
    (∫ x in D, 𝐞 (-⟪x, (w : V)⟫) • periodisation L f x)
      = 𝓕 (f : V → ℂ) (w : V) := by
  classical
  haveI : Countable (↥L.toAddSubgroup) :=
    Countable.of_equiv (↥L)
      (Equiv.subtypeEquivRight (fun a => Submodule.mem_toAddSubgroup L)).symm
  have hf_int : Integrable (f : V → ℂ) := f.integrable
  have hg_int : Integrable (fun v => 𝐞 (-⟪v, (w : V)⟫) • (f : V → ℂ) v) :=
    (Real.fourierIntegral_convergent_iff (w : V)).mpr hf_int
  have hchar : ∀ (γ : ↥L.toAddSubgroup) (x : V),
      𝐞 (-⟪(γ : V) + x, (w : V)⟫) = 𝐞 (-⟪x, (w : V)⟫) := by
    intro γ x
    have hmem : (γ : V) ∈ L := by
      have := γ.2; rwa [Submodule.mem_toAddSubgroup] at this
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp (mem_dualLattice.mp w.2 (γ : V) hmem)
    have hn' : ⟪(w : V), (γ : V)⟫ = (n : ℝ) := by rw [← hn]; simp
    have hgw : ⟪(γ : V), (w : V)⟫ = (n : ℝ) := by rw [real_inner_comm]; exact hn'
    have hsplit : -⟪(γ : V) + x, (w : V)⟫ = -(n : ℝ) + -⟪x, (w : V)⟫ := by
      rw [inner_add_left, hgw]; ring
    have hen : (𝐞 (-(n : ℝ)) : Circle) = 1 := by
      rw [show (-(n : ℝ)) = (((-n : ℤ)) : ℝ) by push_cast; ring, Real.fourierChar_apply']
      exact Circle.exp_two_pi_mul_int (-n)
    rw [hsplit, AddChar.map_add_eq_mul, hen, one_mul]
  have hbody : ∀ (γ : ↥L.toAddSubgroup) (x : V),
      (fun v => 𝐞 (-⟪v, (w : V)⟫) • (f : V → ℂ) v) (γ +ᵥ x)
        = 𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x) := by
    intro γ x; simp only [AddSubgroup.vadd_def, vadd_eq_add]; rw [hchar γ x]
  have hmeas : ∀ γ : ↥L.toAddSubgroup,
      AEStronglyMeasurable
        (fun x => 𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x)) (volume.restrict D) := by
    intro γ
    refine Continuous.aestronglyMeasurable ?_
    have hinner : Continuous fun x : V => ⟪x, (w : V)⟫ := continuous_id.inner continuous_const
    exact (Real.continuous_fourierChar.comp hinner.neg).smul
      (f.continuous.comp (continuous_const.add continuous_id))
  have hnorm : ∀ (γ : ↥L.toAddSubgroup) (x : V),
      ‖𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x)‖ₑ = ‖(f : V → ℂ) ((γ : V) + x)‖ₑ := by
    intro γ x; rw [enorm_eq_nnnorm, enorm_eq_nnnorm]; congr 1
    exact Subtype.ext (Circle.norm_smul _ _)
  have hfin : (∑' γ : ↥L.toAddSubgroup,
      ∫⁻ x in D, ‖𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x)‖ₑ ∂volume) ≠ (⊤ : ENNReal) := by
    have hcongr : (∑' γ : ↥L.toAddSubgroup,
          ∫⁻ x in D, ‖𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x)‖ₑ ∂volume)
        = ∑' γ : ↥L.toAddSubgroup, ∫⁻ x in D, ‖(f : V → ℂ) ((γ : V) + x)‖ₑ ∂volume :=
      tsum_congr (fun γ => lintegral_congr (fun x => hnorm γ x))
    have h1 : (∑' γ : ↥L.toAddSubgroup, ∫⁻ x in D, ‖(f : V → ℂ) ((γ : V) + x)‖ₑ ∂volume)
        = ∫⁻ x, ‖(f : V → ℂ) x‖ₑ ∂volume := by
      rw [hD.lintegral_eq_tsum'' (fun v => ‖(f : V → ℂ) v‖ₑ)]
      simp only [AddSubgroup.vadd_def, vadd_eq_add]
    rw [hcongr, h1]; exact hf_int.hasFiniteIntegral.ne
  have hpt : ∀ x : V,
      (∑' γ : ↥L.toAddSubgroup, 𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x))
        = 𝐞 (-⟪x, (w : V)⟫) • periodisation L f x := by
    intro x
    rw [tsum_const_smul' (𝐞 (-⟪x, (w : V)⟫))]
    congr 1
    rw [periodisation_apply]
    rw [← (Equiv.subtypeEquivRight (fun a => Submodule.mem_toAddSubgroup L)).tsum_eq
          (fun v : ↥L => (f : V → ℂ) (x + (v : V)))]
    exact tsum_congr (fun γ => by rw [add_comm]; rfl)
  have e1 : 𝓕 (f : V → ℂ) (w : V)
      = ∑' γ : ↥L.toAddSubgroup, ∫ x in D,
          (fun v => 𝐞 (-⟪v, (w : V)⟫) • (f : V → ℂ) v) (γ +ᵥ x) :=
    (Real.fourier_eq _ _).trans
      (hD.integral_eq_tsum'' (fun v => 𝐞 (-⟪v, (w : V)⟫) • (f : V → ℂ) v) hg_int)
  rw [e1]; symm; simp_rw [hbody]; rw [← integral_tsum hmeas hfin]; simp_rw [hpt]


end FourierCoefficients

/-! ## Torus Fourier inversion for the periodisation

The periodisation `F = periodisation L f` is a continuous `L`-periodic function
on `V`, hence descends to a continuous function on the compact torus
`V ⧸ L`. Its Fourier coefficients with respect to the dual characters
`x ↦ 𝐞(⟪x, w⟫)`, `w ∈ dualLattice L`, are `c_w = (vol L)⁻¹ · 𝓕 f w`
(`fourierCoeff_periodisation`). Since `𝓕 f` is again Schwartz, the family
`(c_w)` decays rapidly over the dual lattice, so the Fourier series converges
absolutely and — by multidimensional torus Fourier inversion — reconstructs
`F` pointwise:

    F(x) = ∑_{w ∈ L*} c_w · 𝐞(⟪x, w⟫).

This multidimensional torus Fourier-inversion statement is **absent from
Mathlib v4.30.0** (which only has the `AddCircle` one-variable version
`hasSum_fourier_series_of_summable`); we state it faithfully here and defer its
analytic proof to a follow-up task. -/

section FourierInversion

variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)

/-- **Absolute convergence of the dual Fourier series.** For every `x`, the
character-weighted family of Fourier coefficients
`w ↦ 𝐞(⟪x,w⟫) • (vol L)⁻¹ · 𝓕 f w` is summable over `dualLattice L`. The
coefficients decay rapidly because `𝓕 f` is again Schwartz
(`SchwartzMap.fourierTransformCLM`); the character has modulus one, so it does
not affect summability. Reuse the
`ZLattice.summable_norm_sub_rpow` + `summable_of_isBigO` pattern of
`summable_periodisation`, transported to the dual lattice. -/
theorem summable_periodisation_fourier (x : V) :
    Summable (fun w : dualLattice L =>
      𝐞 (⟪x, (w : V)⟫) •
        ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V))) := by
  classical
  -- The character has modulus one: reduce to summability of the norms.
  apply Summable.of_norm
  -- 𝓕 f is again Schwartz.
  set g : SchwartzMap V ℂ := SchwartzMap.fourierTransformCLM ℂ f with hg
  have hgc : (g : V → ℂ) = 𝓕 (f : V → ℂ) := by
    rw [hg]; rfl
  set Lstar := dualLattice L
  set d : ℕ := Module.finrank ℤ Lstar with hd
  set s : ℝ := -(d : ℝ) - 1 with hs
  have hsd : s < -(Module.finrank ℤ Lstar : ℝ) := by rw [hs, ← hd]; linarith
  have hgO : (g : V → ℂ) =O[Filter.cocompact V] fun y => ‖y‖ ^ s :=
    g.isBigO_cocompact_rpow s
  have hLclosed : IsClosed (X := V) (Lstar : Set V) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ Lstar.toAddSubgroup
      (inferInstanceAs (DiscreteTopology Lstar))
  have hcoe : Filter.Tendsto ((↑) : Lstar → V) Filter.cofinite
      (Filter.cocompact V) :=
    tendsto_cofinite_cocompact_of_discrete
      hLclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hbo : (fun w : Lstar => (g : V → ℂ) (w : V)) =O[Filter.cofinite]
      fun w : Lstar => ‖(w : V)‖ ^ s := hgO.comp_tendsto hcoe
  have hsum : Summable fun w : Lstar => ‖(w : V)‖ ^ s := by
    have := ZLattice.summable_norm_sub_rpow Lstar s hsd 0
    refine this.congr fun w => ?_; rw [sub_zero]
  have hg_sum : Summable fun w : Lstar => (g : V → ℂ) (w : V) :=
    summable_of_isBigO hsum hbo
  -- Multiply by the constant `(vol L)⁻¹` and rewrite via `Circle.norm_smul`.
  have hconst : Summable fun w : Lstar =>
      ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ‖𝓕 (f : V → ℂ) (w : V)‖ := by
    refine (hg_sum.norm.mul_left ‖(ZLattice.covolume L : ℂ)⁻¹‖).congr fun w => ?_
    rw [hgc]
  refine hconst.congr fun w => ?_
  rw [Circle.norm_smul, norm_mul]

end FourierInversion

/-! ## Transport layer: realising the torus `V ⧸ L` as a product of circles

The multidimensional torus Fourier inversion (`periodisation_eq_tsum_fourier`)
is obtained by transporting Mathlib's one-variable `AddCircle` inversion
(`hasSum_fourier_series_of_summable`) across an explicit identification of the
compact torus `V ⧸ L` with the product of circles `(AddCircle 1)^d`. This
section introduces that transport data, parametrised by a fixed `ℤ`-basis
`b : Basis (Fin d) ℤ L` of the full-rank lattice `L` (so
`d = Module.finrank ℤ L = Module.finrank ℝ V`).

The geometric heart is the ℝ-linear continuous isomorphism
`Φ = latticeEquivFun L b : V ≃L[ℝ] (Fin d → ℝ)` (Mathlib's `Basis.equivFunL`
of the induced ℝ-basis `b.ofZLatticeBasis ℝ L`), which carries `L` *onto* the
integer points `ℤ^d`. Descending `Φ` along the two quotient maps
`V → V ⧸ L` and `(Fin d → ℝ) → (Fin d → AddCircle 1)` yields the continuous
additive-group isomorphism of tori; transporting the torus Haar measure and the
dual characters across it is what converts the sum over `dualLattice L` (with
the `(vol L)⁻¹` normalisation and the `exp(2πi⟪x,w⟫)` synthesis convention)
into the product Fourier series over `ℤ^d`. -/

section TorusTransport

variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)

/-- The ℝ-linear continuous isomorphism `Φ : V ≃L[ℝ] (Fin d → ℝ)` induced by a
ℤ-basis `b` of the lattice `L`. It is `Basis.equivFunL` of the induced ℝ-basis
`b.ofZLatticeBasis ℝ L` of `V`, and by construction carries `L` onto the
integer points `ℤ^d` (see `latticeEquivFun_image_lattice`). This is the
geometric core of the transport `V ⧸ L ≅ (AddCircle 1)^d`. -/
noncomputable def latticeEquivFun : V ≃L[ℝ] (Fin d → ℝ) :=
  (b.ofZLatticeBasis ℝ L).equivFunL

theorem latticeEquivFun_apply (x : V) (i : Fin d) :
    latticeEquivFun L b x i = (b.ofZLatticeBasis ℝ L).repr x i := by
  simp [latticeEquivFun]

/-- `Φ = latticeEquivFun L b` carries the lattice `L` exactly onto the integer
points `ℤ^d = {z | ∀ i, z i ∈ range Int.cast}`. This is the precise sense in
which the basis identifies `L` with the standard lattice and is what makes the
quotient `V ⧸ L` correspond to `(Fin d → AddCircle 1)`. -/
theorem latticeEquivFun_image_lattice :
    latticeEquivFun L b '' (L : Set V)
      = {z : Fin d → ℝ | ∀ i, z i ∈ Set.range ((↑) : ℤ → ℝ)} := by
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    rw [latticeEquivFun_apply, b.ofZLatticeBasis_repr_apply ℝ L ⟨x, hx⟩ i]
    exact ⟨b.repr ⟨x, hx⟩ i, rfl⟩
  · intro hz
    choose n hn using hz
    refine ⟨(latticeEquivFun L b).symm z, ?_, (latticeEquivFun L b).apply_symm_apply z⟩
    have hsymm : (latticeEquivFun L b).symm z
        = ∑ i, z i • (b.ofZLatticeBasis ℝ L) i := by
      rw [show (latticeEquivFun L b).symm z
            = (b.ofZLatticeBasis ℝ L).equivFun.symm z from rfl,
        Basis.equivFun_symm_apply]
    rw [hsymm]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hn i, Basis.ofZLatticeBasis_apply, Int.cast_smul_eq_zsmul ℝ]
    exact L.smul_mem (n i) (b i).2

/-- `Φ = latticeEquivFun L b` as a bare additive-group homomorphism `V →+ ℝ^d`. -/
private noncomputable def latticeEquivFunHom : V →+ (Fin d → ℝ) :=
  (latticeEquivFun L b).toLinearEquiv.toLinearMap.toAddMonoidHom

/-- Coordinatewise circle projection `ℝ^d →+ (AddCircle 1)^d`, i.e. apply the
quotient map `ℝ → AddCircle 1 = ℝ ⧸ ℤ∙1` in each coordinate. -/
private noncomputable def piCircleHom :
    (Fin d → ℝ) →+ (Fin d → AddCircle (1 : ℝ)) :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).compLeft (Fin d)

/-- The additive-group homomorphism `V →+ (AddCircle 1)^d` obtained by composing
`Φ = latticeEquivFun L b` with the coordinatewise circle projection. By
`latticeEquivFun_image_lattice` its kernel is exactly the lattice `L`, so it
descends to the torus isomorphism `torusEquiv`. -/
private noncomputable def toPiCircleHom :
    V →+ (Fin d → AddCircle (1 : ℝ)) :=
  (piCircleHom (d := d)).comp (latticeEquivFunHom L b)

private theorem toPiCircleHom_apply (x : V) :
    toPiCircleHom L b x
      = fun i => ((latticeEquivFun L b x i : ℝ) : AddCircle (1 : ℝ)) := rfl

/-- The kernel of `toPiCircleHom` is exactly the lattice `L`: `Φ x` has all
coordinates in `ℤ` (hence vanishes in `(AddCircle 1)^d`) iff `x ∈ L`. -/
private theorem toPiCircleHom_eq_zero_iff (x : V) :
    toPiCircleHom L b x = 0 ↔ x ∈ L.toAddSubgroup := by
  have hcoe : ∀ r : ℝ,
      ((r : AddCircle (1 : ℝ)) = 0 ↔ r ∈ Set.range ((↑) : ℤ → ℝ)) := by
    intro r
    rw [AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn⟩
    · rintro ⟨n, rfl⟩; exact ⟨n, by simp⟩
  rw [toPiCircleHom_apply, funext_iff]
  simp only [Pi.zero_apply, hcoe]
  rw [show (∀ i, latticeEquivFun L b x i ∈ Set.range ((↑) : ℤ → ℝ))
        ↔ latticeEquivFun L b x
            ∈ {z : Fin d → ℝ | ∀ i, z i ∈ Set.range ((↑) : ℤ → ℝ)} from Iff.rfl,
    ← latticeEquivFun_image_lattice L b,
    (latticeEquivFun L b).injective.mem_set_image]
  exact (Submodule.mem_toAddSubgroup L).symm

/-- The descent of `toPiCircleHom` to the torus `V ⧸ L`, as an additive-group
homomorphism. -/
private noncomputable def torusHom :
    (V ⧸ L.toAddSubgroup) →+ (Fin d → AddCircle (1 : ℝ)) :=
  QuotientAddGroup.lift L.toAddSubgroup (toPiCircleHom L b)
    (by intro x hx; rw [AddMonoidHom.mem_ker]; exact (toPiCircleHom_eq_zero_iff L b x).2 hx)

private theorem continuous_toPiCircleHom :
    Continuous (toPiCircleHom L b) := by
  refine continuous_pi (fun i => ?_)
  simp only [toPiCircleHom_apply]
  exact QuotientAddGroup.continuous_mk.comp
    ((continuous_apply i).comp (latticeEquivFun L b).continuous)

/-- The torus `V ⧸ L` is compact: the quotient map `V → V ⧸ L` is continuous and
`L`-periodic, so its (full) range is compact by `IsZLattice`. -/
instance instCompactSpaceTorus :
    CompactSpace (V ⧸ L.toAddSubgroup) := by
  rw [← isCompact_univ_iff]
  have hrange : Set.range ((↑) : V → V ⧸ L.toAddSubgroup) = Set.univ :=
    QuotientAddGroup.range_mk
  rw [← hrange]
  refine IsZLattice.isCompact_range_of_periodic L _ QuotientAddGroup.continuous_mk ?_
  intro z w hw
  rw [QuotientAddGroup.eq]
  have hzw : -(z + w) + z = -w := by abel
  rw [hzw]
  exact (L.toAddSubgroup).neg_mem ((Submodule.mem_toAddSubgroup L).2 hw)

private theorem torusHom_bijective : Function.Bijective (torusHom L b) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    induction a using QuotientAddGroup.induction_on with
    | _ x =>
      rw [show torusHom L b (x : V ⧸ L.toAddSubgroup) = toPiCircleHom L b x from rfl] at ha
      exact (QuotientAddGroup.eq_zero_iff (N := L.toAddSubgroup) x).2 ((toPiCircleHom_eq_zero_iff L b x).1 ha)
  · intro t
    choose r hr using fun i => QuotientAddGroup.mk_surjective (t i)
    refine ⟨((latticeEquivFun L b).symm r : V ⧸ L.toAddSubgroup), ?_⟩
    rw [show torusHom L b ((latticeEquivFun L b).symm r : V ⧸ L.toAddSubgroup)
          = toPiCircleHom L b ((latticeEquivFun L b).symm r) from rfl, toPiCircleHom_apply]
    funext i
    rw [(latticeEquivFun L b).apply_symm_apply]
    exact hr i

/-- **Continuous additive-group isomorphism of tori**
`V ⧸ L ≃ₜ+ (AddCircle 1)^d`, obtained by descending the basis-induced linear
isomorphism `Φ = latticeEquivFun L b` along the quotient maps `V → V ⧸ L` and
coordinatewise `ℝ → AddCircle 1`. The forward map is the continuous descent of
`Φ`; since `V ⧸ L` is compact and the product torus is Hausdorff, the inverse is
automatically continuous. -/
noncomputable def torusEquiv :
    (V ⧸ L.toAddSubgroup) ≃ₜ+ (Fin d → AddCircle (1 : ℝ)) := by
  let e : (V ⧸ L.toAddSubgroup) ≃+ (Fin d → AddCircle (1 : ℝ)) :=
    AddEquiv.ofBijective (torusHom L b) (torusHom_bijective L b)
  have hcont : Continuous e := by
    rw [← (QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff]
    have hcomp : (e ∘ (QuotientAddGroup.mk : V → V ⧸ L.toAddSubgroup))
        = fun x => toPiCircleHom L b x := by
      funext x; rfl
    rw [hcomp]
    exact continuous_toPiCircleHom L b
  exact ContinuousAddEquiv.mk'
    (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) hcont)
    (fun x y => map_add e x y)

@[simp] theorem torusEquiv_mk (x : V) :
    (torusEquiv L b) (x : V ⧸ L.toAddSubgroup)
      = fun i => ((latticeEquivFun L b x i : ℝ) : AddCircle (1 : ℝ)) := by
  have h : (torusEquiv L b) (x : V ⧸ L.toAddSubgroup) = toPiCircleHom L b x := rfl
  rw [h, toPiCircleHom_apply]


/-- The inverse torus isomorphism is continuous. -/
theorem continuous_torusEquiv_symm : Continuous (torusEquiv L b).symm :=
  map_continuous (torusEquiv L b).symm

/-! ### Dual lattice ↔ `ℤ^d` and the dual character

Under `torusEquiv L b`, the dual character `x ↦ 𝐞(⟪x, w⟫)` for `w ∈ dualLattice L`
becomes the product Fourier character `(θ_i) ↦ ∏ i, fourier (n_i) (θ_i)` on
`(Fin d → AddCircle 1)`, where `n = (n_i)` are the integer coordinates of `w` in
the dual basis. This is the character bookkeeping that converts the sum over
`dualLattice L` into the sum over `ℤ^d` in the product-torus Fourier inversion. -/

/-- The ℝ-basis of `V` dual to `b.ofZLatticeBasis ℝ L` with respect to the inner
product `⟪·,·⟫`. It satisfies `⟪dualBasisR i, (b.ofZLatticeBasis ℝ L) j⟫ = δ_ij`
(`apply_dualBasis_left`) and its ℤ-span is exactly `dualLattice L`. -/
noncomputable def dualBasisR : Basis (Fin d) ℝ V :=
  LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate (b.ofZLatticeBasis ℝ L)

/-- `dualLattice L` is the ℤ-span of the dual basis `dualBasisR L b` of the chosen
ℤ-basis `b`. (Per-`b` form of `dualLattice_eq_span_dualBasis`.) -/
theorem dualLattice_eq_span_dualBasisR :
    dualLattice L = Submodule.span ℤ (Set.range (dualBasisR L b)) := by
  classical
  have hLspan : L = Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) :=
    (b.ofZLatticeBasis_span ℝ).symm
  change LinearMap.BilinForm.dualSubmodule (innerₗ V) L = _
  exact (congrArg (LinearMap.BilinForm.dualSubmodule (innerₗ V)) hLspan).trans
    (LinearMap.BilinForm.dualSubmodule_span_of_basis _ innerₗ_nondegenerate
      (b.ofZLatticeBasis ℝ L))

/-- The defining duality: `⟪x, dualBasisR i⟫` reads off the `i`-th coordinate of
`x` in the primal ℝ-basis `b.ofZLatticeBasis ℝ L`, i.e. equals `Φ x i`. -/
theorem inner_dualBasisR (x : V) (i : Fin d) :
    (⟪x, dualBasisR L b i⟫ : ℝ) = latticeEquivFun L b x i := by
  classical
  rw [latticeEquivFun_apply]
  set P := b.ofZLatticeBasis ℝ L with hP
  have hkron : ∀ j, (⟪P j, dualBasisR L b i⟫ : ℝ) = (if j = i then (1 : ℝ) else 0) := by
    intro j
    rw [real_inner_comm]
    have hd := LinearMap.BilinForm.apply_dualBasis_left innerₗ_nondegenerate P i j
    rw [innerₗ_apply_apply] at hd
    exact hd
  have hx : x = ∑ j, P.repr x j • P j := (P.sum_repr x).symm
  conv_lhs => rw [hx]
  rw [sum_inner]
  have : ∀ j, (⟪P.repr x j • P j, dualBasisR L b i⟫ : ℝ)
      = P.repr x j * (if j = i then (1 : ℝ) else 0) := by
    intro j; rw [real_inner_smul_left, hkron j]
  rw [Finset.sum_congr rfl (fun j _ => this j)]
  simp [Finset.sum_ite_eq']

private theorem dualBasisR_linearIndependent :
    LinearIndependent ℤ (dualBasisR L b) := by
  have hinj : Function.Injective (fun c : ℤ => c • (1 : ℝ)) := by
    intro a c h; simpa using h
  exact (dualBasisR L b).linearIndependent.restrict_scalars hinj

/-- The ℤ-basis of `dualLattice L` given by the dual basis vectors `dualBasisR i`
(they are ℤ-independent and ℤ-span `dualLattice L`). -/
noncomputable def dualLatticeBasis : Basis (Fin d) ℤ (dualLattice L) :=
  (Basis.span (dualBasisR_linearIndependent L b)).map
    (LinearEquiv.ofEq _ _ (dualLattice_eq_span_dualBasisR L b).symm)

theorem dualLatticeBasis_coe (i : Fin d) :
    ((dualLatticeBasis L b i : dualLattice L) : V) = dualBasisR L b i := by
  rw [dualLatticeBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]

/-- **Bijection `dualLattice L ≃ ℤ^d`** matching a dual-lattice vector with its
integer multi-index of coordinates in the dual basis `dualBasisR`. -/
noncomputable def dualLatticeEquiv : (dualLattice L) ≃ (Fin d → ℤ) :=
  (dualLatticeBasis L b).equivFun.toEquiv

theorem dualLatticeEquiv_apply (w : dualLattice L) (i : Fin d) :
    dualLatticeEquiv L b w i = (dualLatticeBasis L b).repr w i := rfl

/-- **Defining property of `dualLatticeEquiv`.** Each `w ∈ dualLattice L` is the
ℤ-combination of the dual basis with coefficients `n = dualLatticeEquiv L b w`:
`(w : V) = ∑ i, (n i : ℝ) • dualBasisR i`. -/
theorem dualLatticeEquiv_symm_repr (w : dualLattice L) :
    (w : V) = ∑ i, ((dualLatticeEquiv L b w i : ℤ) : ℝ) • dualBasisR L b i := by
  have h := (dualLatticeBasis L b).sum_repr w
  have hcoe : (w : V)
      = ((∑ i, ((dualLatticeBasis L b).repr w i) • (dualLatticeBasis L b i)
          : dualLattice L) : V) := by rw [h]
  rw [hcoe, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SetLike.val_smul, dualLatticeBasis_coe, ← Int.cast_smul_eq_zsmul ℝ, dualLatticeEquiv_apply]

/-- The inner product against `w ∈ dualLattice L` decomposes through `Φ`'s
coordinates: `⟪x, w⟫ = ∑ i, (n i) * (Φ x i)` with `n = dualLatticeEquiv L b w`. -/
theorem inner_dualLattice_eq_sum (w : dualLattice L) (x : V) :
    (⟪x, (w : V)⟫ : ℝ)
      = ∑ i, ((dualLatticeEquiv L b w i : ℤ) : ℝ) * latticeEquivFun L b x i := by
  conv_lhs => rw [dualLatticeEquiv_symm_repr L b w]
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, inner_dualBasisR]

/-- **Character correspondence.** Under `torusEquiv L b`, the dual character
`x ↦ 𝐞(⟪x, w⟫)` (`w ∈ dualLattice L`, the `exp(2πi⟪x,w⟫)` synthesis convention
dual to `𝓕`) equals the product Fourier character `∏ i, fourier (n i) (θ_i)`
evaluated at `θ = torusEquiv L b ↑x`, where `n = dualLatticeEquiv L b w`. -/
theorem fourierChar_inner_eq_prod_fourier (w : dualLattice L) (x : V) :
    ((𝐞 (⟪x, (w : V)⟫) : Circle) : ℂ)
      = ∏ i, fourier (dualLatticeEquiv L b w i)
          ((torusEquiv L b (x : V ⧸ L.toAddSubgroup)) i) := by
  classical
  set n := dualLatticeEquiv L b w with hn
  -- Right-hand side: each factor is `exp (2π · (n i · Φ x i) · I)`.
  have hR : ∀ i,
      fourier (n i) ((torusEquiv L b (x : V ⧸ L.toAddSubgroup)) i)
        = Complex.exp (2 * Real.pi * ((n i : ℝ) * latticeEquivFun L b x i) * Complex.I) := by
    intro i
    simp only [torusEquiv_mk, fourier_coe_apply]
    push_cast
    ring_nf
  rw [Finset.prod_congr rfl (fun i _ => hR i)]
  rw [← Complex.exp_sum]
  -- Left-hand side: `𝐞 (∑ ...) = exp (2π · (∑ ...) · I)`, split the exponent.
  rw [inner_dualLattice_eq_sum L b w x, Real.fourierChar_apply]
  congr 1
  push_cast [Finset.mul_sum]
  rw [Finset.sum_mul]

end TorusTransport

/-! ## Multidimensional Fourier inversion on the product torus `(AddCircle 1)^d`

This section records the pure-analysis Fourier inversion theorem on the product
torus `(AddCircle 1)^d`, used by the periodisation transport. Mathlib v4.30.0
*does* provide this in `Mathlib/Analysis/Fourier/AddCircleMulti.lean` as
`UnitAddTorus.hasSum_mFourier_series_apply_of_summable` (note `UnitAddTorus d`
is definitionally `d → AddCircle 1`); we therefore **reuse** that engine rather
than re-deriving it by induction on `d`, and only repackage it under the
project-local names and the explicit conjugate-character integral convention
that the geometry transport refers to. -/
section ProductTorusFourier

open UnitAddTorus ComplexConjugate

-- Match the measure normalisation used by Mathlib's `AddCircleMulti`: each
-- circle `AddCircle 1` carries its Haar probability measure (unit mass), and
-- the product torus the corresponding product measure.  This is the *same*
-- `MeasureSpace` instance (`⟨AddCircle.haarAddCircle⟩`) under which Mathlib
-- elaborated `UnitAddTorus.mFourierCoeff`, so the integrals coincide.
noncomputable local instance : MeasureSpace (AddCircle (1 : ℝ)) :=
  ⟨AddCircle.haarAddCircle⟩

variable {d : ℕ}

/-- The multidimensional Fourier coefficient of `F : (AddCircle 1)^d → ℂ` at a
multi-index `n : Fin d → ℤ`, with the conjugate product-character analysis
convention `c n = ∫ θ, (∏ i, conj (fourier (n i) (θ i))) • F θ` over the product
Haar measure (each circle normalised to unit mass). This matches Mathlib's
one-variable `fourierCoeff` convention coordinatewise; it agrees with Mathlib's
multidimensional `UnitAddTorus.mFourierCoeff` (see
`fourierCoeffProd_eq_mFourierCoeff`). -/
noncomputable def fourierCoeffProd (F : (Fin d → AddCircle (1 : ℝ)) → ℂ)
    (n : Fin d → ℤ) : ℂ :=
  ∫ θ, (∏ i, conj (fourier (n i) (θ i))) • F θ

/-- The conjugate-character coefficient `fourierCoeffProd` agrees with Mathlib's
`UnitAddTorus.mFourierCoeff` (whose integrand is the single product character
`mFourier (-n)`). -/
theorem fourierCoeffProd_eq_mFourierCoeff (F : (Fin d → AddCircle (1 : ℝ)) → ℂ)
    (n : Fin d → ℤ) : fourierCoeffProd F n = mFourierCoeff F n := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  -- `mFourier (-n) θ = ∏ i, fourier (-(n i)) (θ i) = ∏ i, conj (fourier (n i) (θ i))`.
  rw [mFourier]
  simp only [ContinuousMap.coe_mk, Pi.neg_apply, fourier_neg]

/-- **Multidimensional Fourier inversion on the product torus** `(AddCircle 1)^d`.
If `F` is continuous and its product-character Fourier coefficients are
absolutely summable, then at every point `θ` the multidimensional Fourier series
`∑_n (∏ i, fourier (n i) (θ i)) • c n` reconstructs `F θ`. The synthesis
character is `∏ i, fourier (n i)` (dual to the conjugate analysis character of
`fourierCoeffProd`). Reuses `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`. -/
theorem hasSum_fourier_product_of_summable
    {F : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hF : Continuous F)
    (h : Summable (fun n : Fin d → ℤ => fourierCoeffProd F n))
    (θ : Fin d → AddCircle (1 : ℝ)) :
    HasSum (fun n : Fin d → ℤ => (∏ i, fourier (n i) (θ i)) • fourierCoeffProd F n)
      (F θ) := by
  -- Bundle `F` as a continuous map and transfer the coefficient identity.
  set f : C(UnitAddTorus (Fin d), ℂ) := ⟨F, hF⟩ with hf
  have hcoeff : mFourierCoeff (⇑f) = fun n => fourierCoeffProd F n := by
    funext n; rw [fourierCoeffProd_eq_mFourierCoeff, hf, ContinuousMap.coe_mk]
  have hsum : Summable (mFourierCoeff (⇑f)) := by rw [hcoeff]; exact h
  have hHS := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f) hsum θ
  -- Rewrite `mFourierCoeff f i • mFourier i θ` into the target form.
  have hfun : (fun i : Fin d → ℤ => mFourierCoeff (⇑f) i • (mFourier i) θ)
      = fun n : Fin d → ℤ => (∏ i, fourier (n i) (θ i)) • fourierCoeffProd F n := by
    funext n
    have hc : mFourierCoeff (⇑f) n = fourierCoeffProd F n := by
      rw [fourierCoeffProd_eq_mFourierCoeff, hf, ContinuousMap.coe_mk]
    rw [mFourier]
    simp only [ContinuousMap.coe_mk, hc, smul_eq_mul, mul_comm]
  rw [hfun] at hHS
  exact hHS

end ProductTorusFourier

/-! ## Measure transport across the torus iso

This section records the single measure-theoretic identity consumed by the
torus Fourier-inversion assembly: an integral
over the product torus `(AddCircle 1)^d` (with each circle normalised to Haar
probability mass, the *same* `⟨AddCircle.haarAddCircle⟩` measure under which
`fourierCoeffProd` is defined) equals — up to the `ZLattice.covolume L` Jacobian
— an integral over a fundamental domain `D` of `L`, pulled back along the torus
iso `torusEquiv L b`.

Geometrically: `Φ = latticeEquivFun L b : V ≃L[ℝ] (Fin d → ℝ)` carries `D` onto
a fundamental box of `ℤ^d` of Lebesgue volume `1`, with Jacobian
`vol(Φ '' s) = vol s / vol(L)` (`ZLattice.volume_image_eq_volume_div_covolume`),
and the coordinatewise quotient `ℝ → AddCircle 1` carries that box onto the
product torus with its mass-1 Haar measure. -/
section TorusMeasureTransport

open UnitAddTorus

-- Same normalisation as `ProductTorusFourier`: each circle carries its Haar
-- probability measure (`AddCircle.haarAddCircle`), so that the product-torus
-- `volume` here is the *same* measure under which `fourierCoeffProd` /
-- `mFourierCoeff` are elaborated and the integrals coincide.
noncomputable local instance : MeasureSpace (AddCircle (1 : ℝ)) :=
  ⟨AddCircle.haarAddCircle⟩

variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)

/- **Measure pushforward across the torus iso** (the form consumed by the
inversion assembly). For an integrable `g` on the product torus
`(Fin d → AddCircle 1)` (with each circle of unit Haar mass), the product-torus
integral equals `(vol L)⁻¹` times the integral, over any fundamental domain `D`
of `L`, of `g` pulled back along `torusEquiv L b`:

    ∫ θ, g θ = (vol L)⁻¹ • ∫ x in D, g (torusEquiv L b x).

This is the volume-correct statement of "a fundamental-domain integral over `L`
equals the product-torus integral up to the covolume Jacobian". The `(vol L)⁻¹`
normalisation is exactly the one carried by `fourierCoeff_periodisation`, so this
turns `fourierCoeffProd Fp n` into `(vol L)⁻¹ · 𝓕 f w`. -/
/-- **Step 1: product torus = unit box.** Writing the coordinatewise quotient
`red : (Fin d → ℝ) → (Fin d → AddCircle 1)`, `red y i = (y i : AddCircle 1)`,
the mass-1 Haar integral over the product torus equals the Lebesgue integral of
`g ∘ red` over the half-open unit box `(Ioc 0 1)^d`. This is Fubini for
`Measure.pi` together with the one-variable identity relating
`∫ t : AddCircle 1, h t` to `∫ t in Ioc 0 1, h t` (period `1`, unit mass). -/
theorem integral_prod_torus_eq_integral_box
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ θ, g θ)
      = ∫ y in Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1),
          g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))) := by
  -- `UnitAddTorus.integral_preimage` (Mathlib) is exactly the product-torus = box
  -- identity for the mass-1 Haar product measure, with the fundamental box
  -- `(Ioc (a i) (a i + 1))^d`. Specialise to `a = 0`, giving the half-open unit
  -- box, and rewrite the set into `Set.univ.pi` form.
  have h := UnitAddTorus.integral_preimage (d := Fin d) g (0 : Fin d → ℝ)
  simp only [Pi.zero_apply, zero_add] at h
  have hset : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}
      = Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1) := by
    ext x; simp
  rw [h, hset]

/-- **Step 2: unit box = covolume⁻¹ • fundamental-domain integral.** Substitute
`y = Φ x` with `Φ = latticeEquivFun L b`: `Φ` carries the fundamental domain `D`
onto a fundamental box of `ℤ^d` (same product torus image as the standard
`(Ioc 0 1)^d` box, by `latticeEquivFun_image_lattice`), and scales Lebesgue
volume by `(covolume L)⁻¹` (`ZLattice.volume_image_eq_volume_div_covolume`).
Hence the box integral of `g ∘ red` equals `(covolume L)⁻¹` times the integral
over `D` of `g ∘ red ∘ Φ`. -/
theorem latticeEquivFun_map_volume :
    Measure.map (latticeEquivFun L b) volume
      = ENNReal.ofReal (ZLattice.covolume L) • (volume : Measure (Fin d → ℝ)) := by
  refine Measure.ext fun t ht => ?_
  rw [Measure.map_apply (latticeEquivFun L b).continuous.measurable ht,
    Measure.smul_apply, smul_eq_mul]
  -- Rewrite the preimage as the image under `Φ.symm`.
  have hpre : (latticeEquivFun L b) ⁻¹' t = (latticeEquivFun L b).symm '' t :=
    ((latticeEquivFun L b).image_symm_eq_preimage t).symm
  rw [hpre]
  -- `equivFun ∘ Φ.symm = id`, so the image formula applied to `Φ.symm '' t` gives back `t`.
  have hid : ((b.ofZLatticeBasis ℝ).equivFun ∘ ⇑(latticeEquivFun L b).symm) = id := by
    funext y
    show (latticeEquivFun L b) ((latticeEquivFun L b).symm y) = y
    exact (latticeEquivFun L b).apply_symm_apply y
  have himg : (b.ofZLatticeBasis ℝ).equivFun '' ((latticeEquivFun L b).symm '' t) = t := by
    rw [← Set.image_comp, hid, Set.image_id]
  have hmeas : MeasurableSet ((latticeEquivFun L b).symm '' t) := by
    rw [(latticeEquivFun L b).image_symm_eq_preimage]
    exact ht.preimage (latticeEquivFun L b).continuous.measurable
  have hvol := ZLattice.volume_image_eq_volume_div_covolume' L b
    (s := (latticeEquivFun L b).symm '' t) hmeas.nullMeasurableSet
  rw [himg] at hvol
  have ha : ENNReal.ofReal (ZLattice.covolume L) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (ZLattice.covolume_pos L volume)).ne'
  have ha' : ENNReal.ofReal (ZLattice.covolume L) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact ((ENNReal.eq_div_iff ha ha').1 hvol).symm

/-- **Step 2a: periodic fundamental-domain swap.** The half-open box
`(Ioc 0 1)^d` and `Φ '' D` (with `Φ = latticeEquivFun L b`) are both fundamental
domains of the integer lattice `ℤ^d` (the latter by `latticeEquivFun_image_lattice`),
and the integrand `g ∘ red` is `ℤ^d`-periodic (`red` collapses integer
translations), so the box and `Φ '' D` integrals agree. -/
theorem integral_box_eq_integral_image_fundamentalDomain
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ y in Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1),
        g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))))
      = ∫ y in (latticeEquivFun L b) '' D,
          g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))) := by
  classical
  set Φ := latticeEquivFun L b with hΦ
  -- The integrand on `ℝ^d`, `F y = g (red y)` with `red y i = (y i : AddCircle 1)`.
  set F : (Fin d → ℝ) → ℂ := fun y => g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))) with hF
  -- The integer lattice `Γ = ℤ^d ⊆ (Fin d → ℝ)`.
  set Γ : AddSubgroup (Fin d → ℝ) :=
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))).toAddSubgroup with hΓ
  -- Membership in `Γ`: integer coordinates.
  have hΓmem : ∀ z : Fin d → ℝ, z ∈ Γ ↔ ∀ i, z i ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro z
    rw [hΓ, Submodule.mem_toAddSubgroup,
      (Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ z]
    simp only [Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom]
  -- `Γ` as a set is exactly `Φ '' L` (`latticeEquivFun_image_lattice`).
  have hΓimg : (Γ : Set (Fin d → ℝ)) = Φ '' (L : Set V) := by
    rw [hΦ, latticeEquivFun_image_lattice]
    ext z
    rw [SetLike.mem_coe, hΓmem]
    rfl
  -- `Φ` carries `L` into `Γ` and `Φ.symm` carries `Γ` into `L`.
  have hmemΓ : ∀ x : V, x ∈ L → Φ x ∈ Γ := by
    intro x hx
    rw [← SetLike.mem_coe, hΓimg]
    exact ⟨x, hx, rfl⟩
  have hmemL : ∀ z : Fin d → ℝ, z ∈ Γ → Φ.symm z ∈ L := by
    intro z hz
    rw [← SetLike.mem_coe, hΓimg] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  -- The group equivalence `e : Γ ≃ L.toAddSubgroup` induced by `Φ`.
  let e : Γ ≃ (↥L.toAddSubgroup) :=
    { toFun := fun z => ⟨Φ.symm z, hmemL z z.2⟩
      invFun := fun x => ⟨Φ x, hmemΓ x x.2⟩
      left_inv := fun z => by
        apply Subtype.ext; simp [ContinuousLinearEquiv.apply_symm_apply]
      right_inv := fun x => by
        apply Subtype.ext; simp [ContinuousLinearEquiv.symm_apply_apply] }
  -- `Φ.symm` is quasi-measure-preserving (it scales volume by `(covolume L)⁻¹`).
  have hmap := latticeEquivFun_map_volume L b
  set c := ENNReal.ofReal (ZLattice.covolume L) with hc
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (ZLattice.covolume_pos L volume)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsymm_map : Measure.map Φ.symm volume = c⁻¹ • volume := by
    have h1 : Measure.map Φ.symm (Measure.map Φ volume) = volume := by
      rw [Measure.map_map Φ.symm.continuous.measurable Φ.continuous.measurable]
      simp
    rw [hmap, Measure.map_smul] at h1
    rw [← h1, smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
  have hqmp : Measure.QuasiMeasurePreserving (⇑Φ.symm) volume volume :=
    ⟨Φ.symm.continuous.measurable, by
      rw [hsymm_map]; exact Measure.smul_absolutelyContinuous⟩
  -- `Φ '' D` is a fundamental domain of `Γ`.
  have himg : IsAddFundamentalDomain Γ (Φ '' D) volume := by
    have h := hD.image_of_equiv (ν := (volume : Measure (Fin d → ℝ)))
      Φ.toHomeomorph.toEquiv ?_ e ?_
    · simpa using h
    · simpa using hqmp
    · intro z x
      show Φ ((e z : V) + x) = (z : Fin d → ℝ) + Φ x
      rw [map_add]
      congr 1
      show Φ (Φ.symm z) = (z : Fin d → ℝ)
      rw [ContinuousLinearEquiv.apply_symm_apply]
  -- The Ico-box (= `ZSpan.fundamentalDomain (Pi.basisFun)`) is a fundamental domain of `Γ`.
  haveI : Countable ↥Γ := by
    rw [hΓ]
    exact inferInstanceAs
      (Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))))
  have hbox_ico : IsAddFundamentalDomain Γ
      (Set.univ.pi fun _ : Fin d => Set.Ico (0 : ℝ) 1) volume := by
    rw [← ZSpan.fundamentalDomain_pi_basisFun]
    exact ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin d)) volume
  -- `F` is `Γ`-invariant: `red` collapses integer translations.
  have hFinv : ∀ (z : Γ) (y : Fin d → ℝ), F (z +ᵥ y) = F y := by
    intro z y
    rw [hF]
    refine congrArg g ?_
    funext i
    have hzi : (z : Fin d → ℝ) i ∈ Set.range ((↑) : ℤ → ℝ) := (hΓmem _).1 z.2 i
    obtain ⟨n, hn⟩ := hzi
    have hvadd : (z +ᵥ y) = (z : Fin d → ℝ) + y := rfl
    rw [hvadd]
    show (((z : Fin d → ℝ) i + y i : ℝ) : AddCircle (1 : ℝ)) = ((y i : ℝ) : AddCircle (1 : ℝ))
    rw [← hn, add_comm, AddCircle.coe_add,
      show (((n : ℝ)) : AddCircle (1 : ℝ)) = 0 from by
        rw [AddCircle.coe_eq_zero_iff]; exact ⟨n, by simp⟩,
      add_zero]
  -- `(Ioc 0 1)^d =ᵐ (Ico 0 1)^d` (boundaries are null).
  have hae : (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) 1)
      =ᵐ[volume] (Set.univ.pi fun _ : Fin d => Set.Ico (0 : ℝ) 1) := by
    have h1 := Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
      (s := Set.univ) (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
    have h2 := Measure.pi_Ico_ae_eq_pi_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
      (s := Set.univ) (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
    rw [← volume_pi] at h1 h2
    exact h1.trans h2.symm
  calc
    (∫ y in Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) 1, F y)
        = ∫ y in Set.univ.pi fun _ : Fin d => Set.Ico (0 : ℝ) 1, F y :=
          setIntegral_congr_set hae
    _ = ∫ y in Φ '' D, F y := hbox_ico.setIntegral_eq himg hFinv

/-- **Step 2b: covolume change of variables.** Substituting `y = Φ x` with
`Φ = latticeEquivFun L b`, the `Φ '' D` integral of `g ∘ red` equals
`(covolume L)⁻¹` times the integral over `D` of `g ∘ red ∘ Φ`, by the covolume
Jacobian `latticeEquivFun_map_volume` (`Φ` scales volume by `(covolume L)⁻¹`). -/
theorem integral_image_fundamentalDomain_eq_covolume_inv_smul
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ y in (latticeEquivFun L b) '' D,
        g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))))
      = (ZLattice.covolume L)⁻¹ •
          ∫ x in D, g (fun i => ((latticeEquivFun L b x i : ℝ) : AddCircle (1 : ℝ))) := by
  classical
  -- `Φ = latticeEquivFun L b` and the common integrand `F = g ∘ red`.
  set Φ := latticeEquivFun L b with hΦ
  set F : (Fin d → ℝ) → ℂ :=
    fun y => g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))) with hFdef
  -- `Φ` is a continuous linear equiv, hence a measurable embedding.
  have hemb : MeasurableEmbedding (Φ : V → (Fin d → ℝ)) := by
    have := Φ.toHomeomorph.measurableEmbedding
    rwa [ContinuousLinearEquiv.coe_toHomeomorph] at this
  -- Change of variables `y = Φ x` over `Φ '' D` (no integrability needed): the
  -- measurable-embedding set-integral pushforward, then the Jacobian
  -- `latticeEquivFun_map_volume` (`map Φ volume = ofReal (covolume L) • volume`).
  have key : (∫ x in D, F (Φ x))
      = ZLattice.covolume L • ∫ y in Φ '' D, F y := by
    have hmap := hemb.setIntegral_map (μ := (volume : Measure V)) F (Φ '' D)
    rw [Set.preimage_image_eq D hemb.injective] at hmap
    -- `hmap : ∫ y in Φ '' D, F y ∂(map Φ volume) = ∫ x in D, F (Φ x)`.
    rw [← hmap, latticeEquivFun_map_volume L b, Measure.restrict_smul,
      integral_smul_measure, ENNReal.toReal_ofReal (ZLattice.covolume_pos L volume).le]
  -- Invert the `covolume` factor.
  rw [key, smul_smul, inv_mul_cancel₀ (ZLattice.covolume_pos L volume).ne', one_smul]

theorem integral_box_eq_covolume_inv_smul_integral_fundamentalDomain
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ y in Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1),
        g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))))
      = (ZLattice.covolume L)⁻¹ •
          ∫ x in D, g (fun i => ((latticeEquivFun L b x i : ℝ) : AddCircle (1 : ℝ))) := by
  rw [integral_box_eq_integral_image_fundamentalDomain L b hD hg,
    integral_image_fundamentalDomain_eq_covolume_inv_smul L b hD hg]

theorem integral_eq_covolume_inv_smul_integral_fundamentalDomain
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ θ, g θ)
      = (ZLattice.covolume L)⁻¹ •
          ∫ x in D, g (torusEquiv L b (x : V ⧸ L.toAddSubgroup)) := by
  -- Convert the `torusEquiv` pullback to the explicit coordinatewise form `red ∘ Φ`,
  -- then chain Step 1 (torus = box) and Step 2 (box = covolume⁻¹ • domain).
  simp only [torusEquiv_mk]
  rw [integral_prod_torus_eq_integral_box hg]
  exact integral_box_eq_covolume_inv_smul_integral_fundamentalDomain L b hD hg

end TorusMeasureTransport

/-! ## Assembly: torus Fourier inversion and lattice Poisson summation

This final section discharges the multidimensional torus Fourier inversion for
the periodisation (`periodisation_eq_tsum_fourier`) by transporting the
product-torus inversion (`hasSum_fourier_product_of_summable`) across the torus
iso `torusEquiv L b`, identifying the product Fourier coefficient of the
transported periodisation `Fp` with `(vol L)⁻¹ · 𝓕 f w`
(`fourierCoeff_periodisation` + the measure pushforward
`integral_eq_covolume_inv_smul_integral_fundamentalDomain` + the character
correspondence `fourierChar_inner_eq_prod_fourier`), then re-indexing the
resulting `∑_{n∈ℤ^d}` back to `∑_{w∈L*}` via the dual-lattice bijection
`dualLatticeEquiv`. The `exp(2πi⟪x,w⟫)` synthesis convention is dual to the
`exp(-2πi⟪·,w⟫)` analysis convention of `𝓕`. -/
section FourierInversionAssembly

open UnitAddTorus ComplexConjugate

-- Same circle-measure normalisation as `ProductTorusFourier`/`TorusMeasureTransport`:
-- each circle `AddCircle 1` carries its Haar probability measure, so the
-- product-torus `volume` is the *same* measure under which `fourierCoeffProd`
-- is defined and `integral_eq_covolume_inv_smul_integral_fundamentalDomain` is
-- stated.
noncomputable local instance : MeasureSpace (AddCircle (1 : ℝ)) :=
  ⟨AddCircle.haarAddCircle⟩

-- The circle Haar measure is a probability measure, so the product-torus volume
-- is finite (hence finite on compacts), giving integrability of continuous
-- functions on the compact torus.
local instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)

set_option maxHeartbeats 1000000 in
/-- **Torus Fourier inversion for the periodisation.** The periodisation
`F = periodisation L f` is reconstructed at every point `x` by the sum of its
Fourier series over the dual lattice, with coefficients
`c_w = (vol L)⁻¹ · 𝓕 f w`. This is the multidimensional torus Fourier
inversion theorem, **absent from Mathlib v4.30.0** (which only has the
`AddCircle` one-variable `hasSum_fourier_series_of_summable`). The
`exp(2πi⟪x,w⟫)` synthesis convention is dual to the `exp(-2πi⟪·,w⟫)` analysis
convention of `𝓕`/`fourierCoeff_periodisation`. -/
theorem periodisation_eq_tsum_fourier (x : V) :
    periodisation L f x
      = ∑' w : dualLattice L,
          𝐞 (⟪x, (w : V)⟫) •
            ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V)) := by
  classical
  -- A ℤ-basis of `L` provides the torus iso `torusEquiv` and the dual-lattice
  -- bijection `dualLatticeEquiv`.
  set d := Module.finrank ℤ L with hd
  let b : Basis (Fin d) ℤ L := Module.finBasis ℤ L
  -- The periodisation transported to the product torus `(AddCircle 1)^d`.
  set Fp : (Fin d → AddCircle (1 : ℝ)) → ℂ :=
    fun θ => periodisationTorus L f ((torusEquiv L b).symm θ) with hFp
  have hcont : Continuous Fp :=
    (continuous_periodisationTorus L f).comp (continuous_torusEquiv_symm L b)
  -- A fundamental domain of `L`, in the `↥L.toAddSubgroup` form expected by the
  -- Fourier-coefficient and measure-transport lemmas.
  set D : Set V := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) with hDdef
  have hDmeas : MeasurableSet D :=
    ZSpan.fundamentalDomain_measurableSet (b.ofZLatticeBasis ℝ L)
  have hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D := by
    have h := ZSpan.isAddFundamentalDomain' (b.ofZLatticeBasis ℝ L) (volume)
    rwa [b.ofZLatticeBasis_span ℝ] at h
  -- Coefficient identity: the product Fourier coefficient of `Fp` at the
  -- multi-index `dualLatticeEquiv L b w` equals `(vol L)⁻¹ · 𝓕 f w`.
  have hcoeff : ∀ w : dualLattice L,
      fourierCoeffProd Fp (dualLatticeEquiv L b w)
        = (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V) := by
    intro w
    have hgcont : Continuous
        (fun θ : Fin d → AddCircle (1 : ℝ) =>
          (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i) (θ i))) • Fp θ) := by
      have hProd : Continuous
          (fun x : Fin d -> AddCircle (1 : Real) =>
            Finset.prod Finset.univ
              (fun i => (starRingEnd Complex) (fourier (dualLatticeEquiv L b w i) (x i)))) := by
        refine continuous_finset_prod (Finset.univ : Finset (Fin d)) ?_
        intro i _
        exact Complex.continuous_conj.comp
          ((fourier (dualLatticeEquiv L b w i)).continuous.comp (continuous_apply i))
      exact hProd.smul hcont
    have hgint : Integrable
        (fun θ : Fin d → AddCircle (1 : ℝ) =>
          (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i) (θ i))) • Fp θ) :=
      hgcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    -- Transport the product-torus integral to a fundamental-domain integral.
    have step1 : fourierCoeffProd Fp (dualLatticeEquiv L b w)
        = (ZLattice.covolume L)⁻¹ •
            ∫ x' in D,
              (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i)
                  ((torusEquiv L b (x' : V ⧸ L.toAddSubgroup)) i)))
                • Fp (torusEquiv L b (x' : V ⧸ L.toAddSubgroup)) :=
      integral_eq_covolume_inv_smul_integral_fundamentalDomain L b hD hgint
    -- Identify the fundamental-domain integral with `𝓕 f w`.
    have hbody : ∀ x' : V,
        (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i)
            ((torusEquiv L b (x' : V ⧸ L.toAddSubgroup)) i)))
              • Fp (torusEquiv L b (x' : V ⧸ L.toAddSubgroup))
          = 𝐞 (-⟪x', (w : V)⟫) • periodisation L f x' := by
      intro x'
      have hFval : Fp (torusEquiv L b (x' : V ⧸ L.toAddSubgroup))
          = periodisation L f x' := by
        change periodisationTorus L f
            ((torusEquiv L b).symm (torusEquiv L b (x' : V ⧸ L.toAddSubgroup)))
            = periodisation L f x'
        rw [(torusEquiv L b).symm_apply_apply, periodisationTorus_mk]
      have hchar : (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i)
            ((torusEquiv L b (x' : V ⧸ L.toAddSubgroup)) i)))
          = ((𝐞 (-⟪x', (w : V)⟫) : Circle) : ℂ) := by
        rw [← map_prod (starRingEnd ℂ),
          ← fourierChar_inner_eq_prod_fourier L b w x',
          AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
      rw [hFval, hchar, Circle.smul_def]
    have hII : (∫ x' in D,
          (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i)
              ((torusEquiv L b (x' : V ⧸ L.toAddSubgroup)) i)))
                • Fp (torusEquiv L b (x' : V ⧸ L.toAddSubgroup)))
        = 𝓕 (f : V → ℂ) (w : V) := by
      rw [← integral_fundamentalDomain_periodisation L f hD w]
      exact setIntegral_congr_fun hDmeas (fun x' _ => hbody x')
    rw [step1, hII, Complex.real_smul, Complex.ofReal_inv]
  -- Summability of the product Fourier coefficients (no character, modulus 1).
  have hs0 := summable_periodisation_fourier L f 0
  simp only [inner_zero_left, AddChar.map_zero_eq_one, one_smul] at hs0
  have hsumw : Summable (fun w : dualLattice L =>
      fourierCoeffProd Fp (dualLatticeEquiv L b w)) :=
    hs0.congr (fun w => (hcoeff w).symm)
  have hsum : Summable (fun n : Fin d → ℤ => fourierCoeffProd Fp n) :=
    (dualLatticeEquiv L b).summable_iff.mp hsumw
  -- Apply product-torus inversion at `θ = torusEquiv L b ↑x`.
  set θ := torusEquiv L b (x : V ⧸ L.toAddSubgroup) with hθ
  have hHS := hasSum_fourier_product_of_summable hcont hsum θ
  have hFpθ : Fp θ = periodisation L f x := by
    change periodisationTorus L f ((torusEquiv L b).symm θ) = periodisation L f x
    rw [hθ, (torusEquiv L b).symm_apply_apply, periodisationTorus_mk]
  rw [hFpθ] at hHS
  -- Re-index `∑_{n∈ℤ^d}` back to `∑_{w∈L*}` via `dualLatticeEquiv`.
  have hHS2 : HasSum (fun w : dualLattice L =>
      (∏ i, fourier (dualLatticeEquiv L b w i) (θ i))
        • fourierCoeffProd Fp (dualLatticeEquiv L b w))
      (periodisation L f x) :=
    (dualLatticeEquiv L b).hasSum_iff.mpr hHS
  have htarget : (fun w : dualLattice L =>
        (∏ i, fourier (dualLatticeEquiv L b w i) (θ i))
          • fourierCoeffProd Fp (dualLatticeEquiv L b w))
      = (fun w : dualLattice L =>
        𝐞 (⟪x, (w : V)⟫) •
          ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V))) := by
    funext w
    rw [hcoeff w,
      show (∏ i, fourier (dualLatticeEquiv L b w i) (θ i))
            = ((𝐞 (⟪x, (w : V)⟫) : Circle) : ℂ) from
        (fourierChar_inner_eq_prod_fourier L b w x).symm,
      Circle.smul_def]
  rw [htarget] at hHS2
  exact hHS2.tsum_eq.symm

/-- **Multidimensional torus Fourier inversion for the periodisation.** The
Fourier series of the periodisation `F = periodisation L f` over the torus
`V ⧸ L` converges and sums to `F(x)` at every point `x`. -/
theorem hasSum_periodisation_fourier (x : V) :
    HasSum (fun w : dualLattice L =>
      𝐞 (⟪x, (w : V)⟫) •
        ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V)))
      (periodisation L f x) := by
  rw [periodisation_eq_tsum_fourier L f x]
  exact (summable_periodisation_fourier L f x).hasSum

/-- **Lattice Poisson summation** in a finite-dimensional real inner product
space. For a full-rank lattice `L ⊆ V` with covolume `vol(L)`, dual lattice
`L* = {w | ∀ v ∈ L, ⟪w, v⟫ ∈ ℤ}`, and a Schwartz function `f : V → ℂ`,

    ∑_{v ∈ L} f(v) = (1 / vol(L)) · ∑_{w ∈ L*} f̂(w),

where `f̂ = 𝓕 f` is the Fourier transform with the `exp(-2πi⟪x,ξ⟫)` convention.
This is the multidimensional analogue of `SchwartzMap.tsum_eq_tsum_fourier`,
which Mathlib only provides in one variable. -/
theorem tsum_eq_tsum_fourier :
    ∑' v : L, (f : V → ℂ) v
      = (ZLattice.covolume L : ℂ)⁻¹ * ∑' w : dualLattice L, 𝓕 (f : V → ℂ) w := by
  -- Evaluate the torus Fourier inversion at `x = 0`: the characters become `1`.
  have h := hasSum_periodisation_fourier L f 0
  simp only [inner_zero_left, AddChar.map_zero_eq_one, one_smul] at h
  rw [← periodisation_zero L f, ← h.tsum_eq, tsum_mul_left]

end FourierInversionAssembly

end DedekindZeta.PoissonSummation

/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: mathlib-initiative/sum_product at 80e4127a67742659d521466204c6d2d7e0ca2b3f.
- Formalization note: Lean 4.33.1 compatibility port with narrow imports for DedekindZeta.PoissonSummation.
- PROVENANCE-END
-/
