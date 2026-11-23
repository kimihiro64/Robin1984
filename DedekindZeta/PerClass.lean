/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.GammaIntegral
import DedekindZeta.Statements
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Tactic.Ring

/-!
# Per-class Gamma-integral evaluation and agreement with `dedekindZeta`

This module discharges the **per-class evaluation** and the resulting agreement
of the genuine completed object with `Z_∞ · ζ_K` on `Re s > 1`.

This material follows the completed-zeta and higher-dimensional Gamma-integral
setup in Neukirch, *Algebraic Number Theory*, Chapter VII §§4 and 5.

These two theorems consume the analytic intermediate identity
`DedekindZeta.GammaIntegral.completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum`,
which lives in `DedekindZeta/GammaIntegral.lean` (downstream of
`DedekindZeta/Statements.lean`). Because Lean forbids the circular import that
would be required to prove them inside `Statements.lean`, they are stated and
proved here, in a module that imports both `Statements` and `GammaIntegral`.

* `completedPartialZeta_idealClassRep_eq` — Step 5 of the per-class evaluation:
  reindex the principal ideals `(a) = 𝔞·𝔟` divisible by a
  class representative `𝔞` of `c` onto the integral ideals `𝔟` of the inverse
  class `c⁻¹`, cancel the `𝔑(𝔞)^{±s}` prefactor, and read off the partial zeta.
* `completedDedekindZeta_eq`: sum the per-class identity over the finite class group
  to recover `Z_∞(s) · ζ_K(s)`.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

/-- **Per-class Gamma-integral evaluation** (the standard treatment). On `Re s > 1`
the completed partial zeta of an ideal-class representative `𝔞` of the class `c`
is `Z_∞(s)` times the partial Dedekind zeta `∑_{𝔟 ∈ class c⁻¹} 𝔑(𝔟)^{-s}` over the
integral ideals of the **inverse** class `c⁻¹`. This is the evaluation of the
multiplicative Mellin transform of the lattice theta kernel over `K_ℝ^*`: the
principal ideals `(a)` with `a ∈ 𝔞` factor as `(a) = 𝔞·𝔟` with `𝔟` integral, and
the map `a ↦ 𝔟 = 𝔞⁻¹(a)` ranges over the integral ideals of class
`[𝔟] = [𝔞]⁻¹ = c⁻¹`; the `𝔑(𝔞)^s` normalisation in `completedPartialZeta`
cancels the representative's norm contribution `𝔑((a)) = 𝔑(𝔞)·𝔑(𝔟)`.

This is Step 5: the analytic core is the intermediate identity
`GammaIntegral.completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum`;
the work here is the purely ideal-theoretic reindexing
`{(a) principal : 𝔞 ∣ (a)} ≃ {𝔟 : [𝔟] = c⁻¹}` and the norm bookkeeping. -/
theorem completedPartialZeta_idealClassRep_eq {s : ℂ} (hs : 1 < s.re)
    (c : ClassGroup (𝓞 K)) :
    completedPartialZeta K (idealClassRep K c) s
      = ZInfty K s * ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
          (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  -- The chosen representative `𝔞 = idealClassRep K c`, with `[𝔞] = c` and `𝔞 ≠ 0`.
  set J𝔞 : (Ideal (𝓞 K))⁰ := Function.surjInv ClassGroup.mk0_surjective c with hJ
  have hmkJ : ClassGroup.mk0 J𝔞 = c := Function.surjInv_eq _ _
  rw [show idealClassRep K c = (J𝔞 : Ideal (𝓞 K)) from rfl]
  set 𝔞 : Ideal (𝓞 K) := (J𝔞 : Ideal (𝓞 K)) with h𝔞def
  have h𝔞ne : 𝔞 ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp J𝔞.2
  -- Step 3 intermediate identity (analytic core).
  rw [GammaIntegral.completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum s hs h𝔞ne]
  -- Splitting `𝔑(m·n)^{-s} = 𝔑(m)^{-s}·𝔑(n)^{-s}` over the casts.
  have hsplit_term : ∀ (m n : ℕ),
      ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
    intro m n
    have h := Complex.mul_cpow_ofReal_nonneg (a := (m : ℝ)) (b := (n : ℝ))
      (Nat.cast_nonneg m) (Nat.cast_nonneg n) (-s)
    simpa [Complex.ofReal_natCast, Nat.cast_mul] using h
  -- The reindexing bijection `{𝔟 : [𝔟] = c⁻¹} ≃ {(a) principal : 𝔞 ∣ (a)}`,
  -- realised by `𝔟 ↦ 𝔞 · 𝔟`.
  set f : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹} →
      {I : (Ideal (𝓞 K))⁰ //
        (𝔞 ∣ (I : Ideal (𝓞 K))) ∧ Submodule.IsPrincipal (I : Ideal (𝓞 K))} :=
    fun 𝔟 =>
      ⟨⟨𝔞 * ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)),
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (mul_ne_zero h𝔞ne (𝔟 : NonzeroIdeal K).2)⟩,
        dvd_mul_right _ _,
        (ClassGroup.mk0_eq_one_iff
          (mem_nonZeroDivisors_iff_ne_zero.mpr
            (mul_ne_zero h𝔞ne (𝔟 : NonzeroIdeal K).2))).mp (by
            have hs2 : (⟨𝔞 * ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)),
                  mem_nonZeroDivisors_iff_ne_zero.mpr
                    (mul_ne_zero h𝔞ne (𝔟 : NonzeroIdeal K).2)⟩ : (Ideal (𝓞 K))⁰)
                = J𝔞 * ⟨((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)),
                    mem_nonZeroDivisors_iff_ne_zero.mpr (𝔟 : NonzeroIdeal K).2⟩ := by
              apply Subtype.ext
              simp [Submonoid.coe_mul, h𝔞def]
            rw [hs2, map_mul, hmkJ]
            have hic : ClassGroup.mk0 ⟨((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)),
                mem_nonZeroDivisors_iff_ne_zero.mpr (𝔟 : NonzeroIdeal K).2⟩
                = idealClass K (𝔟 : NonzeroIdeal K) := rfl
            rw [hic, 𝔟.2, mul_inv_cancel])⟩
    with hf
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    have hh : 𝔞 * ((x : NonzeroIdeal K) : Ideal (𝓞 K))
        = 𝔞 * ((y : NonzeroIdeal K) : Ideal (𝓞 K)) :=
      congrArg
        (fun d : {I : (Ideal (𝓞 K))⁰ //
            (𝔞 ∣ (I : Ideal (𝓞 K))) ∧ Submodule.IsPrincipal (I : Ideal (𝓞 K))} =>
          ((d.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) h
    exact mul_left_cancel₀ h𝔞ne hh
  have hsurj : Function.Surjective f := by
    rintro ⟨I, hdvd, hprin⟩
    obtain ⟨b, hb⟩ := hdvd
    have hbne : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hb
      exact (mem_nonZeroDivisors_iff_ne_zero.mp I.2) hb
    have hbmem : b ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hbne
    have hIsplit : I = J𝔞 * ⟨b, hbmem⟩ := by
      apply Subtype.ext
      simp [Submonoid.coe_mul, h𝔞def, hb]
    have hmkI : ClassGroup.mk0 I = 1 := (ClassGroup.mk0_eq_one_iff I.2).mpr hprin
    rw [hIsplit, map_mul, hmkJ] at hmkI
    have hcl : idealClass K ⟨b, hbne⟩ = c⁻¹ := by
      rw [show idealClass K ⟨b, hbne⟩ = ClassGroup.mk0 ⟨b, hbmem⟩ from rfl,
        eq_inv_iff_mul_eq_one, mul_comm]
      exact hmkI
    refine ⟨⟨⟨b, hbne⟩, hcl⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change 𝔞 * b = (I : Ideal (𝓞 K))
    rw [hb]
  set e : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹} ≃
      {I : (Ideal (𝓞 K))⁰ //
        (𝔞 ∣ (I : Ideal (𝓞 K))) ∧ Submodule.IsPrincipal (I : Ideal (𝓞 K))} :=
    Equiv.ofBijective f ⟨hinj, hsurj⟩ with he
  -- Reindex the principal-ideal tsum onto the inverse class via `e`.
  have hreindex :
      (∑' I : {I : (Ideal (𝓞 K))⁰ //
            (𝔞 ∣ (I : Ideal (𝓞 K))) ∧ Submodule.IsPrincipal (I : Ideal (𝓞 K))},
          (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℂ) ^ (-s))
        = ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
            (Ideal.absNorm 𝔞 : ℂ) ^ (-s)
              * (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    rw [← Equiv.tsum_eq e (fun I => (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) :
        Ideal (𝓞 K)) : ℂ) ^ (-s))]
    apply tsum_congr
    intro 𝔟
    change (Ideal.absNorm (𝔞 * ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K))) : ℂ) ^ (-s) = _
    rw [map_mul Ideal.absNorm, hsplit_term]
  rw [hreindex, tsum_mul_left]
  -- Cancel the `𝔑(𝔞)^{±s}` prefactor.
  have hAnat : Ideal.absNorm 𝔞 ≠ 0 := fun h =>
    h𝔞ne (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
  have hAne : (Ideal.absNorm 𝔞 : ℂ) ≠ 0 := by exact_mod_cast hAnat
  have hcancel : (Ideal.absNorm 𝔞 : ℂ) ^ s * (Ideal.absNorm 𝔞 : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hAne, add_neg_cancel, Complex.cpow_zero]
  calc (Ideal.absNorm 𝔞 : ℂ) ^ s * ZInfty K s
          * ((Ideal.absNorm 𝔞 : ℂ) ^ (-s)
            * ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
                (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s))
        = ((Ideal.absNorm 𝔞 : ℂ) ^ s * (Ideal.absNorm 𝔞 : ℂ) ^ (-s))
            * (ZInfty K s
              * ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
                  (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
          ring
      _ = ZInfty K s
            * ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
                (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
          rw [hcancel, one_mul]

/-! ## Agreement with Mathlib's `dedekindZeta` on `Re s > 1`

On the convergence strip `Re s > 1` the genuine completed object equals
`Z_∞(s) · ζ_K(s)`; this is the evaluation of the higher-dimensional
Gamma-integral (the standard treatment). -/
theorem completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s = ZInfty K s * NumberField.dedekindZeta K s := by
  simp only [completedDedekindZeta]
  simp_rw [completedPartialZeta_idealClassRep_eq K hs]
  rw [← Finset.mul_sum]
  -- Reindex the class sum `c ↦ c⁻¹` (an involution of the finite class group) so
  -- the inverse-class fibres become the direct-class fibres.
  rw [show (∑ c : ClassGroup (𝓞 K),
        ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
          (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s))
        = ∑ c : ClassGroup (𝓞 K),
            ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c},
              (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s) from
      Equiv.sum_comp (Equiv.inv (ClassGroup (𝓞 K)))
        (fun c => ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c},
          (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s))]
  rw [sum_class_tsum_absNorm K hs, ← dedekindZeta_eq_tsum_absNorm K hs]

end

end DedekindZeta

/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: mathlib-initiative/sum_product at 80e4127a67742659d521466204c6d2d7e0ca2b3f.
- Formalization note: Lean 4.33.1 compatibility port with narrow imports for DedekindZeta.PerClass.
- PROVENANCE-END
-/
