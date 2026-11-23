/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.ConeRadialReduction
import DedekindZeta.MellinPrinciple
import DedekindZeta.Statements
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Tactic.NormNum

/-!
# Bridge: raw cone integral ↔ reduced radial Mellin + polar terms

This module ties the project's *raw* cone Bochner integral
`DedekindZeta.completedPartialZeta K 𝔞 s` (`DedekindZeta/Statements.lean`,
convergent on `Re s > 1`) to the **regularised reduced radial Mellin** of the
abstract Mellin principle (`DedekindZeta/MellinPrinciple.lean`), via the
cone→radial reduction (`DedekindZeta/ConeRadialReduction.lean`).

This bridge follows the analytic pattern in Neukirch, *Algebraic Number Theory*,
Chapter VII §§1, 3, and 5.

The upshot of the Mellin-principle framework is that the `+1`/`−1` inversion
correction integral

    𝒞(𝔞,s) = ∫_cone [ (1/covol 𝔞)·N^{1−s} − N^{−s} ] d^*x

is **not** the vacuous `0` that the Bochner
non-integrability convention would assign to the divergent raw integral; it is
the genuine, convergent **polar term**

    𝒞(𝔞,s) = −a₀/s + C·b₀/(s−k)

with the cone-scaling instantiation `a₀ = b₀ = V = surfaceVolume K`,
`C = (covolume K 𝔞)⁻¹`, `k = 1` produced by
`ConeRadialReduction.exists_isMellinPair_radialTheta`. We package this term as
`conePolarCorrection` and prove (`coneMellin_eq_mellinContinuation`,
`completedPartialZeta_eq_mellinContinuation`,
`mellinContinuation_eq_conePolarCorrection_add_tail`,
`conePolarCorrection_residue_zero`/`_one`) the bridge identities consumed
downstream.

## How the pieces fit

* `ConeRadialReduction.coneMellin_idealThetaKernel_eq_mellin` reduces the
  per-class cone Mellin `∫_cone Θ(𝔞,x)·N^s d^*x` to the one-dimensional
  `mellin (orbitTheta K 𝔞) s` (under integrability, available on `Re s > 1`).
* The completed radial theta `radialTheta K 𝔞 = orbitTheta K 𝔞 + V` restores the
  constant term `V`, so `reducedMellin (radialTheta K 𝔞) V s = mellin (orbitTheta K 𝔞) s`
  (the regularisation changes nothing the raw cone Mellin sees), and
  `(radialTheta K 𝔞, radialThetaDual K 𝔞, V, V, (covol 𝔞)⁻¹, 1)` is a Mellin pair.
* `MellinPrinciple.mellinContinuation_eq` then identifies, on `Re s > 1`, the
  reduced Mellin with the explicit continuation
  `−a₀/s + C·b₀/(s−k) + mellinTail`, whose polar head is `conePolarCorrection`.

No definition or statement here narrows to a special case; integrability on
`Re s > 1` is supplied by the proved
`DedekindZeta.integrable_indicator_mixedThetaKernel_mul_norm_cpow`.
-/

open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real nonZeroDivisors

namespace DedekindZeta.ConeMellinBridge

open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple

variable (K : Type*) [Field K] [NumberField K]

/-! ## The polar correction term `𝒞(𝔞,s) = −a₀/s + C·b₀/(s−k)` -/

/-- **The cone correction term** `𝒞(𝔞,s)`, read — as
as the explicit **polar part** of the reduced radial Mellin's continuation,
*not* as the vacuous `0` of the divergent raw
integral `∫_cone[(1/covol)N^{1−s} − N^{−s}] d^*x`.

With the cone-scaling instantiation of the Mellin principle
(`exists_isMellinPair_radialTheta`): constant terms `a₀ = b₀ = surfaceVolume K`,
inversion constant `C = (covolume K 𝔞)⁻¹`, weight `k = 1`, this is

    𝒞(𝔞,s) = −surfaceVolume K / s  +  (covolume K 𝔞)⁻¹ · surfaceVolume K / (s − 1).

It is the genuine `−a₀/s + C·b₀/(s−k)` head of
`MellinPrinciple.mellinContinuation` (see
`mellinContinuation_eq_conePolarCorrection_add_tail`), carrying the simple poles
of `ζ_K` at `s = 0` and `s = 1`; never `0`. -/
noncomputable def conePolarCorrection (𝔞 : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  -surfaceVolume K / s
    + (Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K / (s - 1)

/-- The polar correction is exactly the `−a₀/s + C·b₀/(s−k)` head of the Mellin
continuation `mellinContinuation (radialTheta K 𝔞) (radialThetaDual K 𝔞) …`,
i.e. `mellinContinuation = 𝒞(𝔞,s) + mellinTail`. This is the precise sense in
which the `+1`/`−1` correction `𝒞` is *not* `0`: it is the polar head of the
genuine analytic continuation. -/
theorem mellinContinuation_eq_conePolarCorrection_add_tail (𝔞 : Ideal (𝓞 K)) (s : ℂ) :
    mellinContinuation (radialTheta K 𝔞) (radialThetaDual K 𝔞)
        (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s
      = conePolarCorrection K 𝔞 s
        + mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
            (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s := by
  unfold conePolarCorrection mellinContinuation
  norm_num

/-! ## The cone Mellin equals the regularised continuation -/

variable {K}

/-- `reducedMellin (radialTheta K 𝔞) (surfaceVolume K) s = mellin (orbitTheta K 𝔞) s`.

The completed radial theta `radialTheta K 𝔞 = orbitTheta K 𝔞 + surfaceVolume K`
restores the constant term `V = surfaceVolume K`; subtracting it back inside the
reduced Mellin recovers exactly the raw `mellin (orbitTheta K 𝔞)`. So the
regularisation `+V` changes nothing the raw cone Mellin sees — it only restores
the constant term that powers the polar part. -/
theorem reducedMellin_radialTheta (𝔞 : Ideal (𝓞 K)) (s : ℂ) :
    reducedMellin (radialTheta K 𝔞) (surfaceVolume K) s = mellin (orbitTheta K 𝔞) s := by
  unfold reducedMellin radialTheta
  simp


/-- **Integrability of the integral-ideal cone Mellin integrand on `Re s > 1`.**

Transports the proved fractional-ideal integrability
`DedekindZeta.integrable_indicator_mixedThetaKernel_mul_norm_cpow` along
`Theta.idealThetaKernel_eq_mixed` to the integral ideal `𝔞`, in the
`IntegrableOn … fundamentalCone` form required by
`coneMellin_idealThetaKernel_eq_mellin`. -/
theorem integrableOn_idealThetaKernel_mul_norm_cpow (𝔞 : Ideal (𝓞 K)) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn
      (fun x => Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K) := by
  have h := DedekindZeta.integrable_indicator_mixedThetaKernel_mul_norm_cpow K
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K) s hs
  rw [integrable_indicator_iff (mixedEmbedding.measurableSet_fundamentalCone K)] at h
  simpa only [Theta.idealThetaKernel_eq_mixed] using h

/-- **Core bridge.** On `Re s > 1`, the raw cone Mellin integral
`∫_cone Θ(𝔞,x)·N(x)^s d^*x` of `completedPartialZeta` equals the **regularised
analytic continuation** `mellinContinuation (radialTheta K 𝔞) …` of the reduced
radial Mellin, instantiated at the cone-scaling weight `k = 1`, constants
`a₀ = b₀ = surfaceVolume K` and inversion constant `C = (covolume K 𝔞)⁻¹`.

Assembled from the cone→radial reduction
(`coneMellin_idealThetaKernel_eq_mellin`), the constant-term restoration
(`reducedMellin_radialTheta`), and the Mellin-principle identity on `Re s > k`
(`mellinContinuation_eq`). -/
theorem coneMellin_eq_mellinContinuation (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) {s : ℂ}
    (hs : 1 < s.re) :
    (∫ x in mixedEmbedding.fundamentalCone K,
        Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s
          ∂(DedekindZeta.mixedMulHaar K))
      = mellinContinuation (radialTheta K 𝔞) (radialThetaDual K 𝔞)
          (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s := by
  obtain ⟨c, α, hpair⟩ := exists_isMellinPair_radialTheta (K := K) 𝔞 hne
  have hint := integrableOn_idealThetaKernel_mul_norm_cpow 𝔞 hs
  rw [coneMellin_idealThetaKernel_eq_mellin 𝔞 s hint,
    ← reducedMellin_radialTheta 𝔞 s,
    ← mellinContinuation_eq hpair (show ((1 : ℝ)) < s.re by exact_mod_cast hs)]

/-- **Bridge for `completedPartialZeta`.** On `Re s > 1`, the raw completed
partial zeta equals its prefactor times the regularised continuation of the
reduced radial Mellin. It exhibits `completedPartialZeta` as
`(prefactor)·mellinContinuation`, whose polar head is the correction
`𝒞(𝔞,s) = conePolarCorrection K 𝔞 s` (NOT `0`), ready for the final assembly chain. -/
theorem completedPartialZeta_eq_mellinContinuation (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    DedekindZeta.completedPartialZeta K 𝔞 s
      = (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ s
          * (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2))
          * mellinContinuation (radialTheta K 𝔞) (radialThetaDual K 𝔞)
              (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s := by
  unfold DedekindZeta.completedPartialZeta
  rw [integral_indicator (mixedEmbedding.measurableSet_fundamentalCone K),
    coneMellin_eq_mellinContinuation 𝔞 hne hs]

/-! ## Strip-level swapped-pair ↔ dual-class bridge -/



/-! ## Residues: the correction carries the simple poles, never `0` -/

variable (K)


/-- **The correction `𝒞` has a simple pole at `s = 1` with residue `C·b₀ = C·V`.**
`lim_{s→1} (s−1)·𝒞(𝔞,s) = (covolume K 𝔞)⁻¹ · surfaceVolume K`. The residue
powering the simple pole of `ζ_K` at `s = 1`. Proved from the closed form. -/
theorem conePolarCorrection_residue_one (𝔞 : Ideal (𝓞 K)) :
    Filter.Tendsto (fun s : ℂ => (s - 1) * conePolarCorrection K 𝔞 s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K)) := by
  set C : ℂ := (Theta.covolume K 𝔞 : ℂ)⁻¹ with hC
  set V : ℂ := surfaceVolume K with hV
  have hcont : ContinuousAt (fun s : ℂ => (s - 1) * (-V / s) + C * V) 1 := by
    refine (((continuousAt_id.sub continuousAt_const).mul ?_).add continuousAt_const)
    exact continuousAt_const.div continuousAt_id (by norm_num)
  have hψ : Filter.Tendsto (fun s : ℂ => (s - 1) * (-V / s) + C * V)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (C * V)) := by
    have h1 := hcont.tendsto.mono_left
      (nhdsWithin_le_nhds : nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ ≤ nhds 1)
    convert h1 using 2
    simp
  refine hψ.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  have hs10 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hcancel : (s - 1) * (C * V / (s - 1)) = C * V := by
    rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ hs10
  unfold conePolarCorrection
  rw [mul_add, hcancel]

/-! ## Assembly-facing packaging of the correction `𝒞(𝔞,s)`

This exposes the `+1`/`−1`
inversion correction `𝒞(𝔞,s)` to downstream users in the form consumed by the
sum-product residue inequality — as the explicit, convergent **polar term**
`conePolarCorrection K 𝔞 s = −a₀/s + C·b₀/(s−k)`, *never* the vacuous `0` of the
divergent raw integral `∫_cone[(1/cov)N^{1−s} − N^{−s}] d^*x` (which the Bochner
convention assigns by `integral_undef`, silently deleting the poles of `ζ_K`). -/

variable {K}

/-- **The completed partial zeta, polar part + regularised tail.** On `Re s > 1`,
`completedPartialZeta K 𝔞 s` equals its prefactor times
`conePolarCorrection K 𝔞 s + mellinTail …`. This is the assembly-facing
spelling of the final-assembly step 3: the `+1`/`−1` correction `𝒞(𝔞,s)`
appears as the explicit summand `conePolarCorrection K 𝔞 s` (the genuine polar
head carrying the simple poles of `ζ_K` at `s = 0, 1` — see
`conePolarCorrection_residue_zero`/`_one`), and is therefore *removed from the
assembly by being replaced with its true value*, **not** dropped as `0`. The
remaining `mellinTail` summand is the entire regularised dual contribution.

Immediate from `completedPartialZeta_eq_mellinContinuation` together with
`mellinContinuation_eq_conePolarCorrection_add_tail`. -/
theorem completedPartialZeta_eq_conePolarCorrection_add_tail (𝔞 : Ideal (𝓞 K))
    (hne : 𝔞 ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    DedekindZeta.completedPartialZeta K 𝔞 s
      = (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ s
          * (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2))
          * (conePolarCorrection K 𝔞 s
              + mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
                  (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s) := by
  rw [completedPartialZeta_eq_mellinContinuation 𝔞 hne hs,
    mellinContinuation_eq_conePolarCorrection_add_tail]

/-! ## Scope of this pruned bridge

This vendored file stops at the strip-level identities needed by
`SumProduct.PartialZetaMellin`: the raw completed partial zeta on `Re s > 1` is
rewritten as an explicit polar correction plus a regularised tail. The upstream
Dedekind-zeta development also contained a meromorphic-continuation / functional-
equation layer, but those final theorems were pruned because the sum-product
argument only uses the residue inequality for real `s > 1`.
-/

variable (K)

end DedekindZeta.ConeMellinBridge

/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: mathlib-initiative/sum_product at 80e4127a67742659d521466204c6d2d7e0ca2b3f.
- Formalization note: Lean 4.33.1 compatibility port with narrow imports for DedekindZeta.ConeMellinBridge.
- PROVENANCE-END
-/
