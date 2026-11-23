/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smooth maps composed with absolutely continuous curves

Locally Lipschitz maps preserve the absolute continuity of metric-valued curves under composition,
and isometries moreover reflect it.
In particular, a map that is continuously differentiable near every point of the compact trace of
an absolutely continuous curve preserves absolute continuity.
-/

public section

open Set

/-- A locally Lipschitz map preserves the absolute continuity of a metric-valued curve whose
trace lies in its domain of local Lipschitz continuity. -/
theorem LocallyLipschitzOn.comp_absolutelyContinuousOnInterval
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {phi : X -> Y} {gamma : Real -> X}
    {s : Set X} {a b : Real} (hphi : LocallyLipschitzOn s phi)
    (hmap : MapsTo gamma (uIcc a b) s) (hGamma : AbsolutelyContinuousOnInterval gamma a b) :
    AbsolutelyContinuousOnInterval (Function.comp phi gamma) a b := by
  obtain hLip := (hphi.mono hmap.image_subset).exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn hGamma.continuousOn')
  let K := Classical.choose hLip
  have hK := Classical.choose_spec hLip
  rw [absolutelyContinuousOnInterval_iff] at hGamma
  rw [absolutelyContinuousOnInterval_iff]
  intro eps hEps
  have hPos : 0 < (K : Real) + 1 := by positivity
  obtain h := hGamma (eps / ((K : Real) + 1)) (div_pos hEps hPos)
  let delta := Classical.choose h
  have hDelta := Classical.choose_spec h
  refine Exists.intro delta (And.intro hDelta.1 ?_)
  intro E hE hLength
  have hSmall := hDelta.2 E hE hLength
  have hSmallScaled := mul_lt_mul_of_pos_left hSmall hPos
  have hCancel : ((K : Real) + 1) * (eps / ((K : Real) + 1)) = eps := by
    field_simp [hPos.ne']
  rw [hCancel] at hSmallScaled
  let mass := (Finset.range E.1).sum (fun i => dist (gamma (E.2 i).1) (gamma (E.2 i).2))
  have hMassNonneg : 0 <= mass := Finset.sum_nonneg (fun i _ => dist_nonneg)
  calc
    _ <= (K : Real) * mass := by
      change _ <= (K : Real) * (Finset.range E.1).sum _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      exact LipschitzOnWith.dist_le_mul hK
        (gamma (E.2 i).1) (mem_image_of_mem gamma (hE.1 i hi).1)
        (gamma (E.2 i).2) (mem_image_of_mem gamma (hE.1 i hi).2)
    _ <= ((K : Real) + 1) * mass :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hMassNonneg
    _ < eps := hSmallScaled

/-- Post-composition with an isometry preserves and reflects the absolute continuity of a
metric-valued curve. -/
theorem Isometry.absolutelyContinuousOnInterval_comp_iff
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y} (hf : Isometry f)
    {γ : ℝ → X} {a b : ℝ} :
    AbsolutelyContinuousOnInterval (f ∘ γ) a b ↔ AbsolutelyContinuousOnInterval γ a b := by
  simp only [absolutelyContinuousOnInterval_iff, Function.comp_apply, hf.dist_eq]

namespace AbsolutelyContinuousOnInterval

/-- Composing an absolutely continuous curve with a map that is `C¹` at every point of its trace
preserves absolute continuity. The smoothness assumption is local to the trace. -/
theorem comp_of_contDiffAt {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {γ : ℝ → F} {φ : F → G} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hφ : ∀ x ∈ γ '' uIcc a b, ContDiffAt ℝ 1 φ x) :
    AbsolutelyContinuousOnInterval (φ ∘ γ) a b := by
  have hloc : LocallyLipschitzOn (γ '' uIcc a b) φ := by
    intro x hx
    obtain ⟨K, U, hU, hLip⟩ := (hφ x hx).exists_lipschitzOnWith
    exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩
  exact hloc.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ

/-- The logarithm of an absolutely continuous real function that does not vanish on the interval
is absolutely continuous. -/
protected theorem log {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (h0 : ∀ t ∈ uIcc a b, f t ≠ 0) :
    AbsolutelyContinuousOnInterval (fun t => Real.log (f t)) a b := by
  change AbsolutelyContinuousOnInterval (Function.comp Real.log f) a b
  apply comp_of_contDiffAt hf
  intro x hx
  let t := Classical.choose hx
  have ht := Classical.choose_spec hx
  rw [<- ht.2]
  exact Real.contDiffAt_log.2 (h0 t ht.1)

end AbsolutelyContinuousOnInterval

/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: Tau Ceti at 1bf9d63472811e1dfe2ebf0c2f3bb5bc411bd6d5.
- Formalization note: Lean 4.33.1 compatibility port for Smooth maps composed with absolutely continuous curves.
- PROVENANCE-END
-/
