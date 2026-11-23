/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.Theta
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Finset.Functor
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Dedekind zeta function: retained statements and analytic infrastructure

This module contains the parts of a Dedekind-zeta development following
Neukirch, *Algebraic Number Theory*, Chapter VII §5 (with supporting material
from §§1, 3, and 4) that are retained in this repository after pruning to the
dependency closure used by `SumProduct.PartialZetaMellin`.

The retained public interface includes:

* the sum-over-ideals identity;
* definitions of the completed partial and total zeta objects on the convergence
  strip;
* theta/cone integrability infrastructure for the per-class Mellin evaluation;
* agreement of the completed zeta with Mathlib's `dedekindZeta` on `Re s > 1`
  (proved downstream in `DedekindZeta.PerClass`).

The upstream production also contained fuller Euler-product and functional-equation
material; those final exported deliverables are not part of this pruned in-repo
library. Comments below distinguish retained helper blocks from omitted final
statements.

`K` is a number field, `s : ℂ`, `𝓞 K` its ring of integers, `Ideal.absNorm`
the absolute ideal norm `𝔑`, and `NumberField.dedekindZeta` Mathlib's Dedekind
zeta (the `LSeries` of the ideal-counting function).
-/

open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

/-! ## Index sets -/

/-- The nonzero integral ideals of `𝓞 K`, as a subtype of `Ideal (𝓞 K)`. -/
abbrev NonzeroIdeal := {I : Ideal (𝓞 K) // I ≠ 0}


/-! ## The sum-over-ideals identity

For `Re s > 1`, Mathlib's `dedekindZeta` (the `LSeries` of
`n ↦ #{ideals of absNorm n}`) regroups into the sum over nonzero integral
ideals of `𝔑(𝔞)^{-s}`. -/
theorem dedekindZeta_eq_tsum_absNorm {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s =
      ∑' 𝔞 : NonzeroIdeal K, (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  -- the ideal-counting coefficient
  set g : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) with hg
  set φ : NonzeroIdeal K → ℕ := fun 𝔞 ↦ Ideal.absNorm (𝔞 : Ideal (𝓞 K)) with hφ
  set h : NonzeroIdeal K → ℂ := fun 𝔞 ↦ (φ 𝔞 : ℂ) ^ (-s) with hh
  set e := Equiv.sigmaFiberEquiv φ with he
  -- finiteness of fibres
  have hfin : ∀ n : ℕ, Finite {a : NonzeroIdeal K // φ a = n} := by
    intro n
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq n).to_subtype
    apply Finite.of_injective
      (f := fun c : {a : NonzeroIdeal K // φ a = n} ↦
        (⟨(c.1 : Ideal (𝓞 K)), c.2⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    intro a b hab
    have : (a.1 : Ideal (𝓞 K)) = (b.1 : Ideal (𝓞 K)) := by
      simpa using congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  -- card of a fibre over nonzero ideals = card of all ideals of that norm (for n ≠ 0)
  have hcard : ∀ n : ℕ, n ≠ 0 →
      Nat.card {a : NonzeroIdeal K // φ a = n}
        = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
    intro n hn
    refine Nat.card_congr ?_
    refine
      { toFun := fun c ↦ ⟨(c.1 : Ideal (𝓞 K)), c.2⟩
        invFun := fun d ↦ ⟨⟨d.1, ?_⟩, d.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro hI0
      apply hn
      have : Ideal.absNorm d.1 = 0 := by rw [hI0]; simp
      rw [← d.2, this]
    · intro c; exact Subtype.ext (Subtype.ext rfl)
    · intro d; exact Subtype.ext rfl
  -- partial-sum identity
  have hpart : ∀ n : ℕ,
      ∑ k ∈ Finset.Icc 1 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k}
        = Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} := by
    intro n
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  -- real coefficient and the big-O bound on partial sums
  set gℝ : ℕ → ℝ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) with hgℝ
  have hbigO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, gℝ k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    have H := (Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
    have h2 := (H.isBigO_one ℝ).mul (isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)
    refine h2.congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      simp only [Function.comp_apply]
      rw [div_mul_cancel₀ _ (by exact_mod_cast hn.ne')]
      rw [hgℝ, ← Nat.cast_sum, hpart n]
      congr 1
      exact (Nat.card_congr (Equiv.subtypeEquivRight (fun I ↦ by exact_mod_cast Iff.rfl))).symm
    · filter_upwards [eventually_ge_atTop 0] with n hn
      rw [one_mul, Real.rpow_one]
  have hLS : LSeriesSummable g s := by
    have hsum := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := gℝ)
      hbigO (fun n ↦ Nat.cast_nonneg _) zero_le_one hs
    refine (LSeriesSummable_congr s (fun {n} _ ↦ ?_)).mp hsum
    simp [hgℝ, hg]
  have hnorm : Summable (fun n : ℕ ↦ ‖LSeries.term g s n‖) := summable_norm_iff.mpr hLS
  -- constant tsum over a finite fibre
  have hconst : ∀ (n : ℕ), n ≠ 0 → ∀ z : ℂ,
      (∑' _y : {a : NonzeroIdeal K // φ a = n}, z)
        = (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) * z := by
    intro n hn z
    haveI := hfin n
    haveI : Fintype {a : NonzeroIdeal K // φ a = n} := Fintype.ofFinite _
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, hcard n hn]
  -- the term-by-term identity
  have hterm : ∀ n : ℕ, (∑' y : {a : NonzeroIdeal K // φ a = n}, h (e ⟨n, y⟩))
      = LSeries.term g s n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      haveI : IsEmpty {a : NonzeroIdeal K // φ a = 0} := by
        refine ⟨fun a ↦ ?_⟩
        have : Ideal.absNorm (a.1 : Ideal (𝓞 K)) = 0 := a.2
        exact a.1.2 ((Ideal.absNorm_eq_zero_iff).mp this)
      simp [tsum_empty, LSeries.term_zero]
    · have hval : ∀ y : {a : NonzeroIdeal K // φ a = n}, h (e ⟨n, y⟩) = (n : ℂ) ^ (-s) := by
        intro y
        have : e ⟨n, y⟩ = y.1 := rfl
        rw [this, hh]
        simp only
        rw [y.2]
      rw [tsum_congr hval, hconst n hn]
      rw [LSeries.term_of_ne_zero hn, hg]
      simp only
      rw [Complex.cpow_neg, div_eq_mul_inv]
  -- summability of h via the real majorant
  have hsumH : Summable h := by
    apply Summable.of_norm
    have hnormeq : ∀ 𝔞 : NonzeroIdeal K, ‖h 𝔞‖ = (φ 𝔞 : ℝ) ^ (-s.re) := by
      intro 𝔞
      have hpos : 0 < φ 𝔞 := by
        rw [hφ]; simp only
        exact Nat.pos_of_ne_zero (fun hz ↦ 𝔞.2 ((Ideal.absNorm_eq_zero_iff).mp hz))
      rw [hh]; simp only
      rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    rw [funext hnormeq]
    refine (Equiv.summable_iff e).mp ?_
    change Summable fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) =>
      (φ (e p) : ℝ) ^ (-s.re)
    rw [summable_sigma_of_nonneg (fun p ↦ Real.rpow_nonneg (by positivity) _)]
    refine ⟨fun n ↦ ?_, ?_⟩
    · haveI := hfin n
      exact Summable.of_finite
    · refine hnorm.congr (fun n ↦ ?_)
      by_cases hn : n = 0
      · subst hn
        haveI : IsEmpty {a : NonzeroIdeal K // φ a = 0} := by
          refine ⟨fun a ↦ ?_⟩
          have : Ideal.absNorm (a.1 : Ideal (𝓞 K)) = 0 := a.2
          exact a.1.2 ((Ideal.absNorm_eq_zero_iff).mp this)
        simp [tsum_empty, LSeries.term_zero]
      · have hval : ∀ y : {a : NonzeroIdeal K // φ a = n},
            (fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) =>
              (φ (e p) : ℝ) ^ (-s.re)) ⟨n, y⟩ = (n : ℝ) ^ (-s.re) := by
          intro y; simp only; rw [show e ⟨n, y⟩ = y.1 from rfl, y.2]
        rw [tsum_congr hval]
        haveI := hfin n
        haveI : Fintype {a : NonzeroIdeal K // φ a = n} := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card, hcard n hn]
        rw [LSeries.norm_term_eq, if_neg hn, hg]
        simp only [Complex.norm_natCast, Real.rpow_neg (Nat.cast_nonneg _)]
        rw [div_eq_mul_inv]
  -- assemble
  have hsig : Summable (fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) => h (e p)) :=
    (Equiv.summable_iff e).mpr hsumH
  have key : (∑' 𝔞 : NonzeroIdeal K, h 𝔞) = ∑' n, LSeries.term g s n := by
    rw [← Equiv.tsum_eq e h,
      hsig.tsum_sigma' (fun n => by haveI := hfin n; exact Summable.of_finite)]
    exact tsum_congr hterm
  rw [NumberField.dedekindZeta, LSeries, ← key]

/-! ## Retained Euler-product helper material (the standard treatment)

The full Euler-product theorem from the upstream development is not exported in
this pruned repository. What remains here is a private helper block from that
route: the abstract geometric-series product identity and the ideal-factorisation
reindexing lemmas. They are retained infrastructure, not current public API for
`SumProduct`.
-/

/-! ### Helper lemmas for the abstract geometric-series product identity

The private theorem `hasProd_finsuppMonomial` is decomposed into three
self-contained analytic facts:

* `summable_norm_finsuppMonomial` — absolute summability of the monomials over
  finitely supported exponent vectors;
* `prod_geometric_eq_tsum_finsuppSupportedIn` — the finite-product expansion:
  the partial product over a finset `s` of the per-factor geometric series equals
  the sum of the monomials over exponent vectors supported in `s`;
* `hasProd_finsuppMonomial` — taking the limit over the directed family of
  finsets, the per-factor geometric series are multipliable with product equal to
  the sum over all exponent vectors.

The main theorem is then immediate from `hasProd_finsuppMonomial`. -/

open scoped NNReal ENNReal

/-- Finite-product distributivity in `ℝ≥0∞`: the sum, over exponent vectors
supported in a finite set `T`, of the monomials `∏_{i ∈ T} a i ^ f i`, factors as
the product over `T` of the per-factor geometric series. Proved by induction on
`T`; this is the engine behind `summable_norm_finsuppMonomial`. -/
private theorem tsum_prod_finsuppSupported {ι : Type*} (a : ι → ℝ≥0∞) (T : Finset ι) :
    ∑' f : {f : ι →₀ ℕ // f.support ⊆ T}, ∏ i ∈ T, a i ^ ((f : ι →₀ ℕ) i)
      = ∏ i ∈ T, ∑' k : ℕ, a i ^ k := by
  classical
  induction T using Finset.induction with
  | empty =>
      have hsub : ∀ x : {f : ι →₀ ℕ // f.support ⊆ (∅ : Finset ι)},
          x = ⟨0, by simp⟩ := by
        rintro ⟨f, hf⟩
        simp only [Finset.subset_empty, Finsupp.support_eq_empty] at hf
        exact Subtype.ext hf
      rw [tsum_eq_single ⟨0, by simp⟩ (fun b hb => absurd (hsub b) hb)]
      simp
  | @insert j T' hj ih =>
      let e' : ℕ × {f : ι →₀ ℕ // f.support ⊆ T'} ≃
          {f : ι →₀ ℕ // f.support ⊆ insert j T'} :=
      { toFun := fun p => ⟨Finsupp.single j p.1 + (p.2 : ι →₀ ℕ), by
          intro i hi
          have hmem := Finsupp.support_add hi
          rw [Finset.mem_union] at hmem
          rcases hmem with h | h
          · exact Finset.mem_insert.mpr
              (Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h)))
          · exact Finset.mem_insert_of_mem (p.2.2 h)⟩
        invFun := fun f => (((f : ι →₀ ℕ) j),
          ⟨(f : ι →₀ ℕ).erase j, by
            intro i hi
            rw [Finsupp.support_erase, Finset.mem_erase] at hi
            have h2 := f.2 hi.2
            rw [Finset.mem_insert] at h2
            exact h2.resolve_left hi.1⟩)
        left_inv := by
          rintro ⟨k, f', hf'⟩
          have hj0 : f' j = 0 := by
            by_contra h
            exact hj (hf' (Finsupp.mem_support_iff.mpr h))
          have hje : Finsupp.erase j f' = f' :=
            Finsupp.erase_of_notMem_support (by simp [hj0])
          apply Prod.ext
          · simp [Finsupp.add_apply, hj0]
          · apply Subtype.ext
            simp only [Finsupp.erase_add, Finsupp.erase_single, zero_add, hje]
        right_inv := by
          rintro ⟨f, hf⟩
          apply Subtype.ext
          simp [Finsupp.single_add_erase] }
      have hterm : ∀ p : ℕ × {f : ι →₀ ℕ // f.support ⊆ T'},
          ∏ i ∈ insert j T', a i ^ ((e' p : ι →₀ ℕ) i)
            = a j ^ p.1 * ∏ i ∈ T', a i ^ ((p.2 : ι →₀ ℕ) i) := by
        rintro ⟨k, f', hf'⟩
        have hcoe : (e' (k, ⟨f', hf'⟩) : ι →₀ ℕ)
            = Finsupp.single j k + f' := rfl
        rw [hcoe, Finset.prod_insert hj]
        have hjval : (Finsupp.single j k + f') j = k := by
          have hj0 : f' j = 0 := by
            by_contra h
            exact hj (hf' (Finsupp.mem_support_iff.mpr h))
          simp [Finsupp.add_apply, hj0]
        rw [hjval]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        have : (Finsupp.single j k + f') i = f' i := by
          rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hij), zero_add]
        rw [this]
      rw [Finset.prod_insert hj, ← ih, ← Equiv.tsum_eq e']
      simp_rw [hterm]
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right]

/-- Absolute summability of the monomials
`∏ᶠ i, g i ^ f i` over finitely supported exponent vectors `f : ι →₀ ℕ`, for a
complex family with `‖g i‖ < 1` for all `i` and `Summable (‖g ·‖)`. -/
private theorem summable_norm_finsuppMonomial {ι : Type*} {g : ι → ℂ}
    (hg : ∀ i, ‖g i‖ < 1) (hsum : Summable fun i ↦ ‖g i‖) :
    Summable fun f : ι →₀ ℕ ↦ ‖∏ᶠ i, g i ^ f i‖ := by
  classical
  set r : ι → ℝ := fun i => ‖g i‖ with hr
  have hr01 : ∀ i, r i < 1 := hg
  have hr0 : ∀ i, 0 ≤ r i := fun i => norm_nonneg _
  -- Multipliability in `ℝ` of the per-factor geometric values `(1 - r i)⁻¹`.
  have hb : Summable (fun i => r i * (1 - r i)⁻¹) := by
    refine Summable.mul_tendsto_const (c := (1 : ℝ)) (by simpa only [hr, norm_norm] using hsum) ?_
    have h0 : Tendsto r cofinite (𝓝 0) := by
      simpa only [hr] using hsum.tendsto_cofinite_zero
    have h1 : Tendsto (fun i => 1 - r i) cofinite (𝓝 (1 - 0)) := tendsto_const_nhds.sub h0
    simpa using h1.inv₀ (by norm_num)
  -- Summability of the logarithms of the geometric values.
  have hL : Summable (fun i => Real.log ((1 - r i)⁻¹)) := by
    refine (Real.summable_log_one_add_of_summable hb).congr (fun i => ?_)
    have hne : (1 : ℝ) - r i ≠ 0 := by have := hr01 i; linarith
    rw [show 1 + r i * (1 - r i)⁻¹ = (1 - r i)⁻¹ by field_simp; ring]
  have hLnonneg : ∀ i, 0 ≤ Real.log ((1 - r i)⁻¹) := by
    intro i
    have hpos : (0 : ℝ) < 1 - r i := by have := hr01 i; linarith
    have : (1 : ℝ) ≤ (1 - r i)⁻¹ := (one_le_inv₀ hpos).mpr (by have := hr0 i; linarith)
    exact Real.log_nonneg this
  set C : ℝ := Real.exp (∑' i, Real.log ((1 - r i)⁻¹)) with hC
  -- It suffices to show summability of the `ℝ≥0`-valued norms.
  have hsummN : Summable (fun f : ι →₀ ℕ => (‖∏ᶠ i, g i ^ f i‖₊ : ℝ≥0)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    set a : ι → ℝ≥0∞ := fun i => (‖g i‖₊ : ℝ≥0∞) with ha
    have hcoe : ∀ f : ι →₀ ℕ,
        ((‖∏ᶠ i, g i ^ f i‖₊ : ℝ≥0) : ℝ≥0∞) = ∏ i ∈ f.support, a i ^ f i := by
      intro f
      have hms : Function.mulSupport (fun i => g i ^ f i) ⊆ ↑f.support := by
        intro i hi
        simp only [Function.mem_mulSupport] at hi
        rw [Finset.mem_coe, Finsupp.mem_support_iff]
        intro hf0
        exact hi (by rw [hf0, pow_zero])
      rw [finprod_eq_prod_of_mulSupport_subset _ hms, nnnorm_prod, ENNReal.coe_finsetProd]
      apply Finset.prod_congr rfl
      intro i _
      rw [nnnorm_pow, ENNReal.coe_pow]
    simp only [hcoe]
    -- The factor norms in `ℝ≥0∞`.
    have hfac : ∀ i, (1 - a i)⁻¹ = ENNReal.ofReal ((1 - r i)⁻¹) := by
      intro i
      have hai : a i = ENNReal.ofReal (r i) := by
        simp only [ha, hr, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
      rw [hai, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
        ← ENNReal.ofReal_sub 1 (hr0 i),
        ENNReal.ofReal_inv_of_pos (by have := hr01 i; linarith)]
    have hle : ∑' f : ι →₀ ℕ, ∏ i ∈ f.support, a i ^ f i ≤ ENNReal.ofReal C := by
      rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le (fun s => ?_)
      set T : Finset ι := s.biUnion (fun f => f.support) with hT
      have hsubT : ∀ f ∈ s, f.support ⊆ T :=
        fun f hf => Finset.subset_biUnion_of_mem (fun f => f.support) hf
      have hstep : ∑ f ∈ s, ∏ i ∈ f.support, a i ^ f i
          = ∑ f ∈ s, ∏ i ∈ T, a i ^ f i := by
        refine Finset.sum_congr rfl (fun f hf => ?_)
        refine Finset.prod_subset (hsubT f hf) (fun i _ hi => ?_)
        rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
      rw [hstep]
      have hfilter : ∑ x ∈ s.subtype (fun fn : ι →₀ ℕ => fn.support ⊆ T),
            ∏ i ∈ T, a i ^ ((x : ι →₀ ℕ) i)
          = ∑ f ∈ s, ∏ i ∈ T, a i ^ f i :=
        Finset.sum_subtype_of_mem (fun fn : ι →₀ ℕ => ∏ i ∈ T, a i ^ fn i) hsubT
      calc ∑ f ∈ s, ∏ i ∈ T, a i ^ f i
            = ∑ x ∈ s.subtype (fun fn : ι →₀ ℕ => fn.support ⊆ T),
                ∏ i ∈ T, a i ^ ((x : ι →₀ ℕ) i) := hfilter.symm
        _ ≤ ∑' x : {f : ι →₀ ℕ // f.support ⊆ T}, ∏ i ∈ T, a i ^ ((x : ι →₀ ℕ) i) :=
              ENNReal.sum_le_tsum _
        _ = ∏ i ∈ T, ∑' k : ℕ, a i ^ k := tsum_prod_finsuppSupported a T
        _ = ∏ i ∈ T, (1 - a i)⁻¹ := by
              simp_rw [ENNReal.tsum_geometric]
        _ = ∏ i ∈ T, ENNReal.ofReal ((1 - r i)⁻¹) := Finset.prod_congr rfl (fun i _ => hfac i)
        _ = ENNReal.ofReal (∏ i ∈ T, (1 - r i)⁻¹) :=
              (ENNReal.ofReal_prod_of_nonneg (fun i _ => by
                have hpos : (0 : ℝ) < 1 - r i := by have := hr01 i; linarith
                positivity)).symm
        _ ≤ ENNReal.ofReal C := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hprodlog : ∏ i ∈ T, (1 - r i)⁻¹
                  = Real.exp (∑ i ∈ T, Real.log ((1 - r i)⁻¹)) := by
                rw [Real.exp_sum]
                refine Finset.prod_congr rfl (fun i _ => ?_)
                have hpos : (0 : ℝ) < 1 - r i := by have := hr01 i; linarith
                exact (Real.exp_log (by positivity)).symm
              rw [hprodlog, hC]
              exact Real.exp_le_exp.mpr (hL.sum_le_tsum T (fun i _ => hLnonneg i))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  simpa only [coe_nnnorm] using NNReal.summable_coe.mpr hsummN

/-- Finite-product expansion. For a finset `s`, the partial
product of the per-factor geometric series `(1 - g i)⁻¹ = ∑' k, g i ^ k` equals
the sum of the monomials over the exponent vectors supported in `s`. -/
private theorem prod_geometric_eq_tsum_finsuppSupportedIn {ι : Type*} {g : ι → ℂ}
    (hg : ∀ i, ‖g i‖ < 1) (hsum : Summable fun i ↦ ‖g i‖) (s : Finset ι) :
    ∏ i ∈ s, (1 - g i)⁻¹ =
      ∑' f : {f : ι →₀ ℕ // f.support ⊆ s}, ∏ᶠ i, g i ^ ((f : ι →₀ ℕ) i) := by
  classical
  -- Each monomial is supported on the (finite) support of its exponent vector.
  have hmulsupp : ∀ (h : ι →₀ ℕ) (S : Finset ι), h.support ⊆ S →
      Function.mulSupport (fun i ↦ g i ^ h i) ⊆ (S : Set ι) := by
    intro h S hS i hi
    simp only [Function.mem_mulSupport] at hi
    have : i ∈ h.support := by
      rw [Finsupp.mem_support_iff]
      intro h0
      exact hi (by rw [h0, pow_zero])
    exact_mod_cast hS this
  -- The monomial as a finite product over the support.
  have hmono : ∀ h : ι →₀ ℕ, (∏ᶠ i, g i ^ h i) = ∏ i ∈ h.support, g i ^ h i := by
    intro h
    exact finprod_eq_prod_of_mulSupport_subset _ (hmulsupp h h.support (Finset.Subset.refl _))
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    have he : (∑' f : {f : ι →₀ ℕ // f.support ⊆ (∅ : Finset ι)},
          ∏ᶠ i, g i ^ ((f : ι →₀ ℕ) i))
        = ∏ᶠ i, g i ^ ((⟨0, by simp⟩ :
            {f : ι →₀ ℕ // f.support ⊆ (∅ : Finset ι)}) : ι →₀ ℕ) i := by
      apply tsum_eq_single
      intro b hb
      exact absurd
        (Subtype.ext (Finsupp.support_eq_empty.1 (Finset.subset_empty.1 b.2))) hb
    rw [he]
    simp
  | @insert a s ha ih =>
    -- Absolute summability facts needed to multiply the two series.
    have hga : Summable fun k : ℕ ↦ ‖g a ^ k‖ := by
      simp_rw [norm_pow]
      exact summable_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hg a)
    have hMs : Summable fun f : {f : ι →₀ ℕ // f.support ⊆ s} ↦
        ‖∏ᶠ i, g i ^ ((f : ι →₀ ℕ) i)‖ :=
      (summable_norm_finsuppMonomial hg hsum).subtype _
    -- Splitting off the `a`-factor of a monomial.
    have key : ∀ (k : ℕ) (f : ι →₀ ℕ), f.support ⊆ s →
        (∏ᶠ i, g i ^ ((f + Finsupp.single a k) i))
          = g a ^ k * ∏ᶠ i, g i ^ (f i) := by
      intro k f hf
      have ha' : a ∉ f.support := fun h ↦ ha (hf h)
      have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha'
      have hsub : (f + Finsupp.single a k).support ⊆ insert a f.support := by
        intro i hi
        rcases Finset.mem_union.1 (Finsupp.support_add hi) with h1 | h1
        · exact Finset.mem_insert_of_mem h1
        · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h1)]
          exact Finset.mem_insert_self _ _
      rw [finprod_eq_prod_of_mulSupport_subset _
            (hmulsupp _ _ hsub), hmono f]
      rw [Finset.prod_insert ha']
      have hxa : (f + Finsupp.single a k) a = k := by
        rw [Finsupp.add_apply, hfa, Finsupp.single_eq_same, zero_add]
      rw [hxa]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro i hi
      have hne : i ≠ a := fun h ↦ ha' (h ▸ hi)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hne, add_zero]
    -- The reindexing equivalence `ℕ × {supp ⊆ s} ≃ {supp ⊆ insert a s}`.
    let e : ℕ × {f : ι →₀ ℕ // f.support ⊆ s} ≃
        {f : ι →₀ ℕ // f.support ⊆ insert a s} :=
      { toFun := fun p ↦ ⟨p.2.1 + Finsupp.single a p.1, by
          intro i hi
          rcases Finset.mem_union.1 (Finsupp.support_add hi) with h1 | h1
          · exact Finset.mem_insert_of_mem (p.2.2 h1)
          · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h1)]
            exact Finset.mem_insert_self _ _⟩
        invFun := fun h ↦ (h.1 a, ⟨h.1.erase a, by
          intro i hi
          rw [Finsupp.support_erase] at hi
          have hmem := Finset.mem_of_mem_erase hi
          have hne := Finset.ne_of_mem_erase hi
          rcases Finset.mem_insert.1 (h.2 hmem) with h1 | h1
          · exact absurd h1 hne
          · exact h1⟩)
        left_inv := by
          rintro ⟨k, f, hf⟩
          have hfa : f a = 0 := Finsupp.notMem_support_iff.1 (fun h ↦ ha (hf h))
          have e1 : (f + Finsupp.single a k) a = k := by
            rw [Finsupp.add_apply, hfa, Finsupp.single_eq_same, zero_add]
          have e2 : Finsupp.erase a (f + Finsupp.single a k) = f := by
            ext i
            by_cases h : i = a
            · subst h
              rw [Finsupp.erase_same, hfa]
            · rw [Finsupp.erase_ne h, Finsupp.add_apply,
                Finsupp.single_eq_of_ne h, add_zero]
          rw [Prod.ext_iff]
          exact ⟨e1, Subtype.ext e2⟩
        right_inv := by
          rintro ⟨h, hh⟩
          apply Subtype.ext
          ext i
          by_cases hi : i = a
          · subst hi
            rw [Finsupp.add_apply, Finsupp.erase_same, Finsupp.single_eq_same, zero_add]
          · rw [Finsupp.add_apply, Finsupp.erase_ne hi,
              Finsupp.single_eq_of_ne hi, add_zero] }
    rw [Finset.prod_insert ha, ← tsum_geometric_of_norm_lt_one (hg a), ih,
      tsum_mul_tsum_of_summable_norm hga hMs,
      ← Equiv.tsum_eq e (fun w ↦ ∏ᶠ i, g i ^ ((w : ι →₀ ℕ) i))]
    refine tsum_congr ?_
    rintro ⟨k, f, hf⟩
    exact (key k f hf).symm

/-- The per-factor geometric series are multipliable with
product equal to the sum of the monomials over all exponent vectors. This is the
limit over the directed family of finsets of
`prod_geometric_eq_tsum_finsuppSupportedIn`, controlled by the absolute
summability `summable_norm_finsuppMonomial`. -/
private theorem hasProd_finsuppMonomial {ι : Type*} {g : ι → ℂ}
    (hg : ∀ i, ‖g i‖ < 1) (hsum : Summable fun i ↦ ‖g i‖) :
    HasProd (fun i ↦ (1 - g i)⁻¹) (∑' f : ι →₀ ℕ, ∏ᶠ i, g i ^ f i) := by
  classical
  set M : (ι →₀ ℕ) → ℂ := fun f ↦ ∏ᶠ i, g i ^ f i with hMdef
  have hu : Summable fun f ↦ ‖M f‖ := summable_norm_finsuppMonomial hg hsum
  have hMsum : Summable M := hu.of_norm
  set T : ℂ := ∑' f : ι →₀ ℕ, M f with hT
  rw [HasProd, SummationFilter.unconditional, Metric.tendsto_atTop]
  intro ε hε
  -- The tail of the absolutely convergent norm series vanishes as the finset grows.
  have htail : Tendsto (fun A : Finset (ι →₀ ℕ) ↦ ∑' f : {x // x ∉ A}, ‖M f‖)
      atTop (𝓝 0) := tendsto_tsum_compl_atTop_zero (fun f ↦ ‖M f‖)
  obtain ⟨A, hA⟩ := (Metric.tendsto_atTop.mp htail) ε hε
  -- All indices appearing in the support of some `f ∈ A`.
  refine ⟨A.biUnion (fun f ↦ f.support), fun s hs ↦ ?_⟩
  set Sset : Set (ι →₀ ℕ) := {f | f.support ⊆ s} with hSset
  -- Partial product over `s` is the sum of the monomials supported in `s`.
  have hpart : ∏ i ∈ s, (1 - g i)⁻¹ = ∑' f : Sset, M f :=
    prod_geometric_eq_tsum_finsuppSupportedIn hg hsum s
  -- Splitting the full sum into supported-in-`s` and the rest.
  have hdecomp : (∑' f : Sset, M f) + (∑' f : ↥Ssetᶜ, M f) = T := by
    rw [hT]; exact hMsum.tsum_subtype_add_tsum_subtype_compl Sset
  rw [dist_eq_norm, hpart]
  have heq : (∑' f : Sset, M f) - T = -(∑' f : ↥Ssetᶜ, M f) := by
    rw [← hdecomp]; ring
  rw [heq, norm_neg]
  -- Exponent vectors not supported in `s` were not in `A`.
  have hsub : Ssetᶜ ⊆ {x | x ∉ A} := by
    intro f hf hfA
    exact hf (fun i hi ↦ hs (Finset.mem_biUnion.mpr ⟨f, hfA, hi⟩))
  have hbound : (∑' f : ↥Ssetᶜ, ‖M f‖) ≤ ∑' f : {x // x ∉ A}, ‖M f‖ := by
    exact Summable.tsum_le_tsum_of_inj (Set.inclusion hsub) (Set.inclusion_injective hsub)
      (fun _ _ ↦ norm_nonneg _) (fun _ ↦ le_rfl) (hu.subtype _) (hu.subtype _)
  have hltε : (∑' f : {x // x ∉ A}, ‖M f‖) < ε := by
    have h := hA A le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)] at h
  calc ‖∑' f : ↥Ssetᶜ, M f‖
      ≤ ∑' f : ↥Ssetᶜ, ‖M f‖ := norm_tsum_le_tsum_norm (hu.subtype _)
    _ ≤ ∑' f : {x // x ∉ A}, ‖M f‖ := hbound
    _ < ε := hltε


section ReIndex

/-- The `v`-adic exponent in the factorization of a nonzero ideal `I`, packaged
as a natural number via `IsDedekindDomain.HeightOneSpectrum.count`. -/
private noncomputable def idealExp (I : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)).toNat

private lemma idealExp_eq {I : Ideal (𝓞 K)} (hI : I ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    idealExp K I v = (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  rw [idealExp, FractionalIdeal.count_coe K v hI, Int.toNat_natCast]

private lemma idealExp_ne_zero_iff {I : Ideal (𝓞 K)} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) : idealExp K I v ≠ 0 ↔ v.asIdeal ∣ I := by
  rw [idealExp_eq K hI, Associates.count_ne_zero_iff_dvd hI v.irreducible]

private lemma finite_idealExp_support {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | idealExp K I v ≠ 0}.Finite := by
  apply (Ideal.finite_factors hI).subset
  intro v hv
  exact (idealExp_ne_zero_iff K hI v).mp hv

private lemma finprod_asIdeal_pow_idealExp {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ idealExp K I v = I := by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  refine finprod_congr (fun v => ?_)
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, idealExp_eq K hI]

/-- The factorization bijection between nonzero ideals and finitely supported
exponent vectors on the height-one spectrum. -/
private noncomputable def nonzeroIdealEquivFinsupp :
    NonzeroIdeal K ≃ (HeightOneSpectrum (𝓞 K) →₀ ℕ) where
  toFun I :=
    { support := (finite_idealExp_support K I.2).toFinset
      toFun := idealExp K I.1
      mem_support_toFun := fun v => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] }
  invFun f := ⟨f.prod (fun v n => v.asIdeal ^ n), by
    rw [Finsupp.prod, Ne, Finset.prod_eq_zero_iff]
    rintro ⟨v, -, hv⟩
    exact pow_ne_zero _ (by simpa [Ideal.zero_eq_bot] using v.ne_bot) hv⟩
  left_inv := by
    rintro ⟨I, hI⟩
    apply Subtype.ext
    change (Finsupp.mk _ (idealExp K I) _).prod (fun v n => v.asIdeal ^ n) = I
    rw [Finsupp.prod]
    simp only [Finsupp.coe_mk]
    rw [← finprod_eq_prod_of_mulSupport_subset (fun v => v.asIdeal ^ idealExp K I v) ?_]
    · exact finprod_asIdeal_pow_idealExp K hI
    · intro v hv
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq,
        Function.mem_mulSupport] at *
      intro h
      exact hv (by rw [h, pow_zero])
  right_inv := by
    intro f
    ext v
    change idealExp K (f.prod (fun v n => v.asIdeal ^ n)) v = f v
    have hJ : f.prod (fun v n => v.asIdeal ^ n) ≠ 0 := by
      rw [Finsupp.prod, Ne, Finset.prod_eq_zero_iff]
      rintro ⟨w, -, hw⟩
      exact pow_ne_zero _ (by simpa [Ideal.zero_eq_bot] using w.ne_bot) hw
    rw [idealExp, ← Int.toNat_natCast (f v)]
    congr 1
    classical
    have hcoe : ((f.prod (fun v n => v.asIdeal ^ n) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K)
        = ∏ w ∈ f.support, ((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) ^ (f w) := by
      rw [Finsupp.prod, ← FractionalIdeal.coeIdealHom_apply, map_prod]
      refine Finset.prod_congr rfl (fun w _ => ?_)
      rw [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]
    rw [hcoe, FractionalIdeal.count_prod K v]
    · simp only [FractionalIdeal.count_pow, FractionalIdeal.count_maximal]
      rw [Finset.sum_congr rfl (fun w _ => by rw [mul_ite, mul_one, mul_zero])]
      rw [Finset.sum_ite_eq' f.support v]
      split_ifs with h
      · simp
      · simp only [Finsupp.mem_support_iff, not_not] at h
        simp [h]
    · exact fun w _ => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)

/-- The complex monoid hom `n ↦ (n : ℂ) ^ (-s)` on `(ℕ, *)`. -/
private noncomputable def cpowHom (s : ℂ) : ℕ →* ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]

private lemma absNorm_cpow_eq_finprod {I : Ideal (𝓞 K)} (hI : I ≠ 0) (s : ℂ) :
    (Ideal.absNorm I : ℂ) ^ (-s)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ idealExp K I v := by
  have hfin : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      v.asIdeal ^ idealExp K I v) := by
    apply (finite_idealExp_support K hI).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro h
    exact hv (by rw [h, pow_zero])
  have hfin2 : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm v.asIdeal) ^ idealExp K I v) := by
    apply (finite_idealExp_support K hI).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro h
    exact hv (by rw [h, pow_zero])
  have hN : Ideal.absNorm I
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal) ^ idealExp K I v := by
    conv_lhs => rw [← finprod_asIdeal_pow_idealExp K hI]
    rw [map_finprod Ideal.absNorm hfin]
    refine finprod_congr (fun v => ?_)
    rw [map_pow]
  rw [show (Ideal.absNorm I : ℂ) ^ (-s) = cpowHom s (Ideal.absNorm I) from rfl, hN,
    map_finprod (cpowHom s) hfin2]
  refine finprod_congr (fun v => ?_)
  rw [map_pow]
  rfl

end ReIndex



/-- Absolute summability over the height-one spectrum reduces to summability of
the ideal-counting Dirichlet series: for `1 < σ`, the series
`∑ₙ #{ideals of absNorm n} · n^(-σ)` converges. -/
private theorem summable_card_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ ↦
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-σ)) := by
  classical
  set D : ℕ → ℕ := fun n ↦ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} with hD
  -- The complex-valued coefficient sequence.
  set f : ℕ → ℂ := fun n ↦ (D n : ℂ) with hf
  -- Number of ideals of norm `≤ n` (real predicate, matching the asymptotic).
  set A : ℕ → ℝ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} : ℝ)
    with hA
  have hAbigO : A =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    have htend := (Ideal.tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop
    have hgf : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) = 0 → A n = 0 := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn h0
      exact absurd h0 (Nat.cast_ne_zero.mpr (by omega))
    exact Asymptotics.isBigO_of_div_tendsto_nhds hgf _ htend
  -- The partial sums of the coefficient norms.
  have hsumbigO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =O[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
    have hle : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, ‖f k‖‖ ≤ ‖A n‖ := by
      intro n
      have hSeq : (∑ k ∈ Finset.Icc 1 n, ‖f k‖)
          = (Nat.card (Ideal.absNorm ⁻¹' (Finset.Icc 1 n : Finset ℕ) :
              Set (Ideal (𝓞 K))) : ℝ) := by
        rw [Finset.card_preimage_eq_sum_card_image_eq
          (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
        push_cast
        refine Finset.sum_congr rfl (fun k _ ↦ ?_)
        simp only [hf, norm_natCast, hD]
      rw [hSeq]
      have hsub : (Ideal.absNorm ⁻¹' (Finset.Icc 1 n : Finset ℕ) : Set (Ideal (𝓞 K)))
          ⊆ {I : Ideal (𝓞 K) | (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} := by
        intro I hI
        simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc] at hI
        simp only [Set.mem_setOf_eq]
        exact_mod_cast hI.2
      have hfin : {I : Ideal (𝓞 K) | (Ideal.absNorm I : ℝ) ≤ (n : ℝ)}.Finite := by
        refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) n).subset ?_
        intro I hI
        simp only [Set.mem_setOf_eq] at hI ⊢
        exact_mod_cast hI
      haveI : Finite {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} := hfin.to_subtype
      have hcardle : Nat.card (Ideal.absNorm ⁻¹' (Finset.Icc 1 n : Finset ℕ) :
            Set (Ideal (𝓞 K)))
          ≤ Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} :=
        Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity)]
      change (Nat.card (Ideal.absNorm ⁻¹' (Finset.Icc 1 n : Finset ℕ) :
          Set (Ideal (𝓞 K))) : ℝ)
          ≤ (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} : ℝ)
      exact_mod_cast hcardle
    refine ((Asymptotics.isBigO_of_le _ hle).trans hAbigO).trans ?_
    refine Asymptotics.isBigO_of_le _ (fun n ↦ ?_)
    rw [Real.rpow_one]
  have hLS : LSeriesSummable f (σ : ℂ) := by
    refine LSeriesSummable_of_sum_norm_bigO hsumbigO (by norm_num) ?_
    simpa using hσ
  -- Convert the (complex) L-series summability into real summability.
  have hterm : ∀ n : ℕ, LSeries.term f (σ : ℂ) n
      = (((D n : ℝ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term, Real.zero_rpow (by linarith : (-σ) ≠ 0)]
    · rw [LSeries.term_of_ne_zero hn]
      simp only [hf]
      have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
      rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_cpow hnpos.le,
        Complex.ofReal_natCast, Complex.ofReal_neg, Complex.cpow_neg, div_eq_mul_inv]
  have hsummable_complex : Summable (fun n : ℕ ↦ (((D n : ℝ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
    have := hLS
    rw [LSeriesSummable, summable_congr hterm] at this
    exact this
  rw [Complex.summable_ofReal] at hsummable_complex
  simpa [hD, D] using hsummable_complex




/-! ## The archimedean completion factor and the completed zeta

the standard treatment:

* `L_ℝ(s) = π^{-s/2} Γ(s/2)`,
* `L_ℂ(s) = 2 (2π)^{-s} Γ(s)`,
* `Z_∞(s) = |d_K|^{s/2} · L_ℝ(s)^{r₁} · L_ℂ(s)^{r₂}`,

with `r₁ = nrRealPlaces K`, `r₂ = nrComplexPlaces K`, `d_K = NumberField.discr K`.
-/

/-- The real Γ-factor `L_ℝ(s) = π^{-s/2} Γ(s/2)` (the standard treatment). -/
def LReal (s : ℂ) : ℂ := (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-- The complex Γ-factor `L_ℂ(s) = 2 (2π)^{-s} Γ(s)` (the standard treatment). -/
def LComplex (s : ℂ) : ℂ := 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s

/-- The archimedean completion (Euler factor at infinity)
`Z_∞(s) = |d_K|^{s/2} L_ℝ(s)^{r₁} L_ℂ(s)^{r₂}` of the standard treatment. -/
def ZInfty (s : ℂ) : ℂ :=
    ((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)
      * LReal s ^ (nrRealPlaces K)
      * LComplex s ^ (nrComplexPlaces K)

/-! ### The genuine completed Dedekind zeta object (the standard treatment)

Following the standard treatment the completed-zeta framework, the completed Dedekind zeta is built
from the *higher-dimensional Gamma-integral* — the multiplicative Mellin
transform over the Minkowski space `K_ℝ = mixedSpace K` — of the lattice theta
kernels of the ideal classes, **not** a scalar Mellin transform of the
single-variable theta series (which would only yield an Epstein-type zeta in the
Minkowski quadratic form).

The object is a genuine total `ℂ`-valued function on all of `ℂ` (the Bochner
integral over the multiplicative Haar measure is a total function); its
meromorphic-continuation/`Re s > 1` properties are *theorems* proved elsewhere. -/

-- `mixedGaussian` (the Minkowski Gaussian `g(x) = exp(-π ⟨x,x⟩)` on `K_ℝ`) now
-- lives in `DedekindZeta/Theta.lean` (`DedekindZeta.Theta.mixedGaussian`), the
-- theta-layer module imported above. It was moved there so the kernel-level
-- theta inversion law (the standard treatment) can be
-- stated and proved alongside the Poisson-summation infrastructure without an
-- import cycle (`Statements` imports `Theta`, not vice versa).

open Classical in
/-- The standard multiplicative Haar measure `d^*x` on `K_ℝ^*`, written as a
density against the additive Lebesgue measure on `K_ℝ`:
`d^*x = (2/π)^{r₂} · |N(x)|^{-1} · dx`. The factor `|N(x)|^{-1}` turns the
additive `dx_w` into the one-dimensional multiplicative Haar measures
`dx_w/|x_w|` (real) and `dλ_w/|z_w|²` (complex), and the constant `(2/π)^{r₂}`
is the per-complex-place normalisation pinning the complex factor to `L_ℂ`. The
density vanishes on the measure-zero locus `N(x) = 0`, so the measure lives on
`K_ℝ^*`. -/
def mixedMulHaar : MeasureTheory.Measure (mixedEmbedding.mixedSpace K) :=
  MeasureTheory.volume.withDensity fun x =>
    ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹)

/-! ### Right-invariance of `mixedMulHaar` and the measure-preserving unit action

(Layering fix.) The multiplicative-Haar right-translation
machinery is collected here, immediately after `mixedMulHaar`, so that the
`Statements`-layer lemma `dualIdeal_cone_integral_eq` (and its cone
change-of-domain helper below) can consume it. It used to live downstream in
`DedekindZeta/GammaIntegral.lean`, which *imports* `Statements`; relocating it
upstream resolves the layering cycle. `GammaIntegral` now imports these lemmas
(its per-element scale-invariance proof `mellin_mixedGaussian_mul_eq` and the
`IsFundamentalDomain` infrastructure consume them). -/

section MulHaarRightInvariance
open MeasureTheory NumberField.mixedEmbedding

-- the standard treatment (measure-theoretic helper).
set_option maxHeartbeats 1000000 in
/-- **Right-multiplication change of variables for `d^*x`** (the lintegral core of
the per-element scale invariance): for `c` with `N(c) ≠ 0`, the translation
`x ↦ x·c` of `K_ℝ^*` preserves the multiplicative Haar measure `mixedMulHaar`, so
for any nonnegative measurable `h`, `∫⁻ h(y·c) d^*x = ∫⁻ h(y) d^*x`. Proof route:
unfold `mixedMulHaar = (2/π)^{r₂}·|N|⁻¹·volume`
and reduce to the *additive* Jacobian `map (·*c) volume = ofReal N(c)⁻¹ • volume`
(`map_linearMap_addHaar_eq_smul_addHaar`, `|LinearMap.det| = N(c)`: real places
contribute `|c_w|`, complex places `|c_w|²`); the density change
`|N(x·c)|⁻¹ = |N(x)|⁻¹·N(c)⁻¹` cancels that Jacobian exactly. -/
theorem lintegral_comp_mul_right_mixedMulHaar (h : mixedEmbedding.mixedSpace K → ℝ≥0∞)
    (hh : Measurable h) {c : mixedEmbedding.mixedSpace K}
    (hc : mixedEmbedding.norm c ≠ 0) :
    ∫⁻ y, h (y * c) ∂(mixedMulHaar K) = ∫⁻ y, h y ∂(mixedMulHaar K) := by
  classical
  -- Norm in factored form: `N(x) = (∏_{real} ‖x_w‖)·(∏_{complex} ‖z_w‖²)`.
  have hnormfac : ∀ x : mixedEmbedding.mixedSpace K,
      mixedEmbedding.norm x
        = (∏ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖)
          * (∏ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2) := by
    intro x
    have hreal : (∏ w : {w : InfinitePlace K // IsReal w}, (normAtPlace w.1 x) ^ (mult w.1))
        = ∏ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖ :=
      Finset.prod_congr rfl fun w _ => by
        rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.prop]
    have hcpx : (∏ w : {w : InfinitePlace K // IsComplex w}, (normAtPlace w.1 x) ^ (mult w.1))
        = ∏ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2 :=
      Finset.prod_congr rfl fun w _ => by
        rw [mult_isComplex, normAtPlace_apply_of_isComplex w.prop]
    rw [mixedEmbedding.norm_apply, InfinitePlace.prod_eq_prod_mul_prod, hreal, hcpx]
  -- Every place-coordinate of `c` is nonzero (else a factor, hence `N(c)`, vanishes).
  have hr_ne : (∏ w : {w : InfinitePlace K // IsReal w}, ‖c.1 w‖) ≠ 0 := by
    intro h0; exact hc (by rw [hnormfac c, h0, zero_mul])
  have hcx_ne : (∏ w : {w : InfinitePlace K // IsComplex w}, ‖c.2 w‖ ^ 2) ≠ 0 := by
    intro h0; exact hc (by rw [hnormfac c, h0, mul_zero])
  have hc1 : ∀ w : {w : InfinitePlace K // IsReal w}, c.1 w ≠ 0 := by
    intro w hw
    exact hr_ne (Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hw, norm_zero]))
  have hc2 : ∀ w : {w : InfinitePlace K // IsComplex w}, c.2 w ≠ 0 := by
    intro w hw
    exact hcx_ne (Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hw, norm_zero]; ring))
  -- **Additive Jacobian (Step 1).** `x ↦ x·c` is the ℝ-linear automorphism built
  -- from the diagonal scaling on the real factor and (the ℝ-restriction of) the
  -- diagonal complex-scaling on the complex factor.
  set Lr : ({w : InfinitePlace K // IsReal w} → ℝ) →ₗ[ℝ]
      ({w : InfinitePlace K // IsReal w} → ℝ) := Matrix.toLin' (Matrix.diagonal c.1) with hLr
  set Lc0 : ({w : InfinitePlace K // IsComplex w} → ℂ) →ₗ[ℂ]
      ({w : InfinitePlace K // IsComplex w} → ℂ) := Matrix.toLin' (Matrix.diagonal c.2) with hLc0
  set Lc : ({w : InfinitePlace K // IsComplex w} → ℂ) →ₗ[ℝ]
      ({w : InfinitePlace K // IsComplex w} → ℂ) := Lc0.restrictScalars ℝ with hLc
  set L : mixedEmbedding.mixedSpace K →ₗ[ℝ] mixedEmbedding.mixedSpace K :=
    Lr.prodMap Lc with hL
  -- `⇑L = (·*c)` (componentwise multiplication).
  have hLfun : (⇑L) = fun x : mixedEmbedding.mixedSpace K => x * c := by
    funext x
    have h1 : (L x).1 = fun w => c.1 w * x.1 w := by
      simp only [hL, LinearMap.prodMap_apply, hLr, Matrix.toLin'_apply]
      funext w; rw [Matrix.mulVec_diagonal]
    have h2 : (L x).2 = fun w => c.2 w * x.2 w := by
      simp only [hL, LinearMap.prodMap_apply, hLc, LinearMap.coe_restrictScalars, hLc0,
        Matrix.toLin'_apply]
      funext w; rw [Matrix.mulVec_diagonal]
    apply Prod.ext
    · rw [h1]; funext w; exact mul_comm _ _
    · rw [h2]; funext w; exact mul_comm _ _
  -- Determinants of the three maps.
  have hdetLr : LinearMap.det Lr = ∏ w : {w : InfinitePlace K // IsReal w}, c.1 w := by
    rw [hLr, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdetLc0 : LinearMap.det Lc0 = ∏ w : {w : InfinitePlace K // IsComplex w}, c.2 w := by
    rw [hLc0, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdetLc : LinearMap.det Lc
      = ‖∏ w : {w : InfinitePlace K // IsComplex w}, c.2 w‖ ^ 2 := by
    rw [hLc, LinearMap.det_restrictScalars, hdetLc0, Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq]
  have hdetL : LinearMap.det L
      = (∏ w : {w : InfinitePlace K // IsReal w}, c.1 w)
        * ‖∏ w : {w : InfinitePlace K // IsComplex w}, c.2 w‖ ^ 2 := by
    rw [hL, LinearMap.det_prodMap, hdetLr, hdetLc]
  -- `|det L| = N(c)`.
  have habs : |LinearMap.det L| = mixedEmbedding.norm c := by
    have hL_left : |∏ w : {w : InfinitePlace K // IsReal w}, c.1 w|
        = ∏ w : {w : InfinitePlace K // IsReal w}, ‖c.1 w‖ := by
      rw [Finset.abs_prod]
      exact Finset.prod_congr rfl fun w _ => (Real.norm_eq_abs _).symm
    have hL_right : ‖∏ w : {w : InfinitePlace K // IsComplex w}, c.2 w‖ ^ 2
        = ∏ w : {w : InfinitePlace K // IsComplex w}, ‖c.2 w‖ ^ 2 := by
      rw [norm_prod, ← Finset.prod_pow]
    rw [hdetL, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤
        ‖∏ w : {w : InfinitePlace K // IsComplex w}, c.2 w‖ ^ 2), hL_left, hL_right, hnormfac c]
  have hdetne : LinearMap.det L ≠ 0 := by
    intro h0; rw [h0, abs_zero] at habs; exact hc habs.symm
  -- Pushforward of `volume` under `x ↦ x·c`.
  have hmulmeas : Measurable (fun x : mixedEmbedding.mixedSpace K => x * c) :=
    (continuous_id.mul continuous_const).measurable
  have hmapvol :
      Measure.map (fun x : mixedEmbedding.mixedSpace K => x * c)
          (volume : Measure (mixedEmbedding.mixedSpace K))
        = ENNReal.ofReal (mixedEmbedding.norm c)⁻¹ • volume := by
    rw [← hLfun, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdetne]
    congr 1
    rw [abs_inv, habs]
  -- Lebesgue change-of-variables form of the additive Jacobian.
  have hjac : ∀ H : mixedEmbedding.mixedSpace K → ℝ≥0∞, Measurable H →
      ∫⁻ y, H (y * c) ∂(volume : Measure (mixedEmbedding.mixedSpace K))
        = ENNReal.ofReal (mixedEmbedding.norm c)⁻¹ * ∫⁻ y, H y ∂volume := by
    intro H hH
    rw [← lintegral_map hH hmulmeas, hmapvol, lintegral_smul_measure, smul_eq_mul]
  -- **Density cancellation (Step 2).** `D` is the additive density of `mixedMulHaar`.
  set D : mixedEmbedding.mixedSpace K → ℝ≥0∞ :=
    fun x => ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹)
    with hD
  have hDmeas : Measurable D :=
    (((mixedEmbedding.continuous_norm K).measurable.inv).const_mul _).ennreal_ofReal
  have hμ : mixedMulHaar K = volume.withDensity D := rfl
  -- Pointwise: `D x = D(x·c)·ofReal N(c)` (everywhere, incl. the `N(x)=0` null set).
  have hpt : ∀ x : mixedEmbedding.mixedSpace K,
      D x = D (x * c) * ENNReal.ofReal (mixedEmbedding.norm c) := by
    intro x
    have hnonneg : (0:ℝ) ≤ (2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm (x * c))⁻¹ :=
      mul_nonneg (by positivity) (inv_nonneg.mpr (mixedEmbedding.norm_nonneg _))
    simp only [hD]
    rw [← ENNReal.ofReal_mul hnonneg]
    congr 1
    rw [map_mul mixedEmbedding.norm x c]
    rcases eq_or_ne (mixedEmbedding.norm x) 0 with hx | hx
    · simp [hx]
    · field_simp
  -- Assembly.
  have hhc : Measurable (fun x : mixedEmbedding.mixedSpace K => h (x * c)) := hh.comp hmulmeas
  rw [hμ, lintegral_withDensity_eq_lintegral_mul volume hDmeas hhc,
    lintegral_withDensity_eq_lintegral_mul volume hDmeas hh]
  simp only [Pi.mul_apply]
  have hHmeas : Measurable
      (fun y : mixedEmbedding.mixedSpace K =>
        D y * ENNReal.ofReal (mixedEmbedding.norm c) * h y) :=
    (hDmeas.mul measurable_const).mul hh
  calc ∫⁻ x, D x * h (x * c) ∂(volume : Measure (mixedEmbedding.mixedSpace K))
      = ∫⁻ x, (fun y => D y * ENNReal.ofReal (mixedEmbedding.norm c) * h y) (x * c) ∂volume := by
        refine lintegral_congr fun x => ?_
        rw [hpt x]
    _ = ENNReal.ofReal (mixedEmbedding.norm c)⁻¹
          * ∫⁻ y, D y * ENNReal.ofReal (mixedEmbedding.norm c) * h y ∂volume :=
        hjac _ hHmeas
    _ = ENNReal.ofReal (mixedEmbedding.norm c)⁻¹
          * (ENNReal.ofReal (mixedEmbedding.norm c) * ∫⁻ y, D y * h y ∂volume) := by
        congr 1
        rw [← lintegral_const_mul' (ENNReal.ofReal (mixedEmbedding.norm c)) _
          ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y => ?_; ring
    _ = ∫⁻ y, D y * h y ∂volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (mixedEmbedding.norm_nonneg c)),
          inv_mul_cancel₀ hc, ENNReal.ofReal_one, one_mul]


/-- **Right-invariance of the multiplicative Haar measure** `d^*x` under
multiplication by a fixed `c` with `N(c) ≠ 0` (so `c ∈ K_ℝ^*`). This is the
measure-theoretic core of the per-element scale invariance: `mixedMulHaar` is the
Haar measure of the multiplicative group `K_ℝ^*`, hence invariant under the
translations `x ↦ x·c`. Tested against a nonnegative measurable `g`, the
right-invariance is exactly the change-of-variables identity
`lintegral_comp_mul_right_mixedMulHaar`. -/
theorem mixedMulHaar_map_mul_right {c : mixedEmbedding.mixedSpace K}
    (hc : mixedEmbedding.norm c ≠ 0) :
    Measure.map (fun x : mixedEmbedding.mixedSpace K => x * c) (mixedMulHaar K)
      = mixedMulHaar K := by
  have hfmeas : Measurable (fun x : mixedEmbedding.mixedSpace K => x * c) :=
    (continuous_id.mul continuous_const).measurable
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg hfmeas]
  exact lintegral_comp_mul_right_mixedMulHaar K g hg hc

/-- Multiplication on the right by a fixed `c` is measurable on the mixed space
(componentwise continuous multiplication). -/
theorem measurable_mul_right_mixedSpace (c : mixedEmbedding.mixedSpace K) :
    Measurable (fun x : mixedEmbedding.mixedSpace K => x * c) :=
  (continuous_id.mul continuous_const).measurable

variable {K} in
/-- Right translation by `mixedEmbedding K u` (`= x ↦ u • x` by commutativity of
the mixed space) is measurable. -/
theorem measurable_unitSMul (u : (𝓞 K)ˣ) :
    Measurable (fun x : mixedEmbedding.mixedSpace K => u • x) := by
  simp only [unitSMul_smul]
  exact (continuous_const.mul continuous_id).measurable

variable {K} in
/-- **The unit action is `mixedMulHaar`-measure-preserving**: the pushforward of
`mixedMulHaar K` under `x ↦ u • x` is `mixedMulHaar K`.
Proof: `u • x = mixedEmbedding K u * x = x * mixedEmbedding K u` (mixed-space
multiplication is commutative), and `mixedEmbedding.norm (mixedEmbedding K u) = 1`
(`norm_unit`), so this is the right-translation invariance
`mixedMulHaar_map_mul_right`. -/
theorem mixedMulHaar_map_unitSMul (u : (𝓞 K)ˣ) :
    Measure.map (fun x : mixedEmbedding.mixedSpace K => u • x) (mixedMulHaar K)
      = mixedMulHaar K := by
  have hfun : (fun x : mixedEmbedding.mixedSpace K => u • x)
      = fun x => x * mixedEmbedding K (u : K) := by
    funext x; rw [unitSMul_smul, mul_comm]
  have hc : mixedEmbedding.norm (mixedEmbedding K (u : K)) ≠ 0 := by
    rw [norm_unit]; norm_num
  rw [hfun]
  exact mixedMulHaar_map_mul_right (K := K) hc

variable {K} in
/-- **The unit action is measure-preserving** for `mixedMulHaar K`,
packaged as `MeasureTheory.MeasurePreserving`
(the form consumed by Mathlib's `IsFundamentalDomain` machinery). -/
theorem measurePreserving_unitSMul (u : (𝓞 K)ˣ) :
    MeasurePreserving (fun x : mixedEmbedding.mixedSpace K => u • x)
      (mixedMulHaar K) (mixedMulHaar K) :=
  ⟨measurable_unitSMul u, mixedMulHaar_map_unitSMul u⟩

/-! ### `IsFundamentalDomain` for the fundamental cone

(Relocated here from `DedekindZeta/GammaIntegral.lean`,
for the same layering reason as the right-translation machinery above: the
`Statements`-layer cone change-of-domain lemma `mixedMulHaar_integral_mul_right_cone_eq`
below consumes the `IsFundamentalDomain` instance, and `Statements` cannot import
the downstream `GammaIntegral`.)

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
group is therefore `Multiplicative (Fin (NumberField.Units.rank K) → ℤ)`, acting through the
monoid hom `coneUnitHom` and the existing unit action. -/

open NumberField.Units NumberField.Units.dirichletUnitTheorem

variable {K} in
/-- The monoid hom `ℤ^(rank K) → (𝓞 K)ˣ` sending `(eᵢ)` to `∏ᵢ (fundSystem K i)^(eᵢ)`.
Its image is a complement of `torsion K` in `(𝓞 K)ˣ` (Dirichlet's unit theorem),
so it realises the free part `(𝓞 K)ˣ ⧸ torsion K ≅ ℤ^(rank K)` as a genuine
subgroup acting on the mixed space. -/
def coneUnitHom : Multiplicative (Fin (NumberField.Units.rank K) → ℤ) →* (𝓞 K)ˣ where
  toFun g := ∏ i, fundSystem K i ^ (Multiplicative.toAdd g i)
  map_one' := by simp
  map_mul' g h := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

variable {K} in
/-- The acting group `Multiplicative (Fin (NumberField.Units.rank K) → ℤ)` acts on the mixed space
through `coneUnitHom` and the unit action. -/
local instance coneMulAction :
    MulAction (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) (mixedEmbedding.mixedSpace K) :=
  MulAction.compHom _ (coneUnitHom (K := K))

variable {K} in
/-- Unfolding of the cone action: `g • x = coneUnitHom g • x`. -/
theorem coneSMul_def (g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
    (x : mixedEmbedding.mixedSpace K) :
    g • x = (coneUnitHom (K := K) g) • x := rfl

variable {K} in
/-- The cone action is by measurable maps (`g • · = coneUnitHom g • ·`, and the unit
action is measurable), as required by Mathlib's `IsFundamentalDomain.setIntegral_eq`
machinery. -/
local instance coneMeasurableConstSMul :
    MeasurableConstSMul (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) (mixedEmbedding.mixedSpace K) :=
  ⟨fun g => measurable_unitSMul (coneUnitHom g)⟩

variable {K} in
/-- The acting group is countable (`Fin (rank K) → ℤ` with finite domain and
countable codomain), as required by the fundamental-domain tsum machinery. -/
local instance coneCountable : Countable (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) :=
  inferInstanceAs (Countable (Fin (rank K) → ℤ))

variable {K} in
/-- `mixedMulHaar K` is invariant under the cone action (the unit action is
measure-preserving, `measurePreserving_unitSMul`), as required by Mathlib's
`IsFundamentalDomain.setIntegral_eq` machinery. -/
local instance coneSMulInvariantMeasure :
    SMulInvariantMeasure (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) (mixedEmbedding.mixedSpace K)
      (mixedMulHaar K) :=
  ⟨fun g s hs =>
    (measurePreserving_unitSMul (coneUnitHom g)).measure_preimage hs.nullMeasurableSet⟩

variable {K} in
/-- `coneUnitHom g` is a root of unity (torsion) iff `g` is trivial: the image of
`coneUnitHom` meets `torsion K` only in the identity, i.e. `coneUnitHom` realises
a complement of `torsion K`. Proved from the uniqueness in Dirichlet's unit
theorem (`exist_unique_eq_mul_prod`). -/
theorem coneUnitHom_mem_torsion_iff (g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) :
    (coneUnitHom (K := K) g : (𝓞 K)ˣ) ∈ torsion K ↔ g = 1 := by
  constructor
  · intro hmem
    have hA : (coneUnitHom (K := K) g : (𝓞 K)ˣ)
        = ((1 : torsion K) : (𝓞 K)ˣ)
          * ∏ i, fundSystem K i ^ ((Multiplicative.toAdd g) i) := by
      simp [coneUnitHom]
    have hB : (coneUnitHom (K := K) g : (𝓞 K)ˣ)
        = ((⟨coneUnitHom (K := K) g, hmem⟩ : torsion K) : (𝓞 K)ˣ)
          * ∏ i, fundSystem K i ^ ((0 : Fin (rank K) → ℤ) i) := by
      simp
    have hpair :=
      (exist_unique_eq_mul_prod K (coneUnitHom (K := K) g)).unique
        (y₁ := ((1 : torsion K), (Multiplicative.toAdd g : Fin (rank K) → ℤ)))
        (y₂ := ((⟨coneUnitHom (K := K) g, hmem⟩ : torsion K), (0 : Fin (rank K) → ℤ))) hA hB
    have h2 : Multiplicative.toAdd g = 0 := congrArg Prod.snd hpair
    exact Multiplicative.toAdd.injective (h2.trans toAdd_one.symm)
  · rintro rfl; simpa using (one_mem (torsion K))

variable {K} in
/-- The norm-vanishing locus is `mixedMulHaar`-null: the density of `mixedMulHaar`
vanishes where `mixedEmbedding.norm = 0`. -/
theorem ae_norm_ne_zero :
    ∀ᵐ x ∂(mixedMulHaar K), mixedEmbedding.norm x ≠ 0 := by
  rw [ae_iff]
  have hset : {x : mixedEmbedding.mixedSpace K | ¬ mixedEmbedding.norm x ≠ 0}
      = {x | mixedEmbedding.norm x = 0} := by
    ext x; simp
  rw [hset]
  have hms : MeasurableSet {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x = 0} :=
    measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const
  rw [mixedMulHaar, withDensity_apply _ hms]
  refine setLIntegral_eq_zero hms ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp [hx]

variable {K} in
/-- **The fundamental cone is a fundamental domain (modulo torsion).**
`mixedEmbedding.fundamentalCone K` is a `MeasureTheory.IsFundamentalDomain` for
the action of `Multiplicative (Fin (NumberField.Units.rank K) → ℤ)` (the free complement of
`torsion K`, acting via `coneUnitHom` and the unit action) on the mixed space
w.r.t. `mixedMulHaar K`. The three predicates are:
* measurability — `measurableSet_fundamentalCone`;
* a.e.-cover — `ae_norm_ne_zero` reduces to the norm-nonzero locus, where
  `fundamentalCone.exists_unit_smul_mem` plus the torsion decomposition
  (`exist_unique_eq_mul_prod`) provides a translate landing in the cone;
* a.e.-disjointness — for `g ≠ 1` the translates `g • cone` and `cone` are
  genuinely disjoint, since two cone elements differing by `coneUnitHom g` would
  force `coneUnitHom g ∈ torsion K` (`fundamentalCone.unit_smul_mem_iff_mem_torsion`),
  i.e. `g = 1` (`coneUnitHom_mem_torsion_iff`).
Measure-invariance of the action is `measurePreserving_unitSMul`. -/
theorem isFundamentalDomain_fundamentalCone :
    IsFundamentalDomain (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      (mixedEmbedding.fundamentalCone K) (mixedMulHaar K) := by
  refine IsFundamentalDomain.mk'' (measurableSet_fundamentalCone K).nullMeasurableSet ?_ ?_ ?_
  · -- a.e.-cover
    filter_upwards [ae_norm_ne_zero (K := K)] with x hx
    obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem hx
    obtain ⟨⟨ζ, e⟩, he, -⟩ := exist_unique_eq_mul_prod K u
    refine ⟨Multiplicative.ofAdd e, ?_⟩
    rw [coneSMul_def]
    have hcone : (coneUnitHom (K := K) (Multiplicative.ofAdd e) : (𝓞 K)ˣ)
        = ∏ i, fundSystem K i ^ (e i) := by
      simp [coneUnitHom]
    have hsplit : u • x
        = (ζ : (𝓞 K)ˣ) • ((coneUnitHom (K := K) (Multiplicative.ofAdd e)) • x) := by
      rw [← mul_smul, hcone, ← he]
    have hz : (↑ζ⁻¹ * ↑ζ : (𝓞 K)ˣ) = 1 := by
      rw [← Subgroup.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
    have hinv : (↑ζ⁻¹ : (𝓞 K)ˣ) • (u • x)
        = (coneUnitHom (K := K) (Multiplicative.ofAdd e)) • x := by
      rw [hsplit, ← mul_smul, hz, one_smul]
    rw [← hinv]
    exact fundamentalCone.torsion_smul_mem_of_mem hu ((torsion K).inv_mem ζ.2)
  · -- a.e.-disjointness (genuine disjointness for `g ≠ 1`)
    intro g hg
    refine Disjoint.aedisjoint (Set.disjoint_left.2 ?_)
    intro x hx hx'
    rw [Set.mem_smul_set_iff_inv_smul_mem, coneSMul_def, map_inv] at hx
    have htor := (fundamentalCone.unit_smul_mem_iff_mem_torsion hx'
      (coneUnitHom (K := K) g)⁻¹).mp hx
    have hmem : (coneUnitHom (K := K) g : (𝓞 K)ˣ) ∈ torsion K := by
      simpa using (torsion K).inv_mem htor
    exact hg ((coneUnitHom_mem_torsion_iff g).mp hmem)
  · -- quasi-measure-preserving
    intro g
    exact (measurePreserving_unitSMul (coneUnitHom (K := K) g)).quasiMeasurePreserving


end MulHaarRightInvariance

-- `idealThetaKernel` (the multiplicative lattice theta kernel of a nonzero
-- integral ideal `𝔞`) now lives in `DedekindZeta/Theta.lean`
-- (`DedekindZeta.Theta.idealThetaKernel`); see the note above. The kernel-level
-- inversion law under `x ↦ x⁻¹` (`Theta.idealThetaKernel_inversion`) is proved
-- there. `completedPartialZeta` below refers to it via the `Theta.` namespace.

/-- The **completed partial zeta** `Z(𝔞, s)` of an integral ideal `𝔞`
(the standard treatment): the discriminant- and norm-weighted higher-dimensional
Gamma-integral (multiplicative Mellin transform over `K_ℝ^*`) of the lattice
theta kernel of `𝔞`. The discriminant power `|d_K|^{s/2}` is the faithful
archimedean normalisation of the standard treatment, and the **ideal-norm power
`𝔑(𝔞)^s`** is the standard treatment's normalisation of `Z(𝔞, s)`: the term-by-term Mellin
evaluation of the theta kernel produces `𝔑((a))^{-s} = (𝔑(𝔞)·𝔑(𝔟))^{-s}` for
`(a) = 𝔞·𝔟`, so the `𝔑(𝔞)^s` factor cancels the representative's norm and leaves
exactly the partial zeta `∑_{𝔟} 𝔑(𝔟)^{-s}` over the integral ideals `𝔟` of the
inverse class. Without it the class sum would not telescope to `ζ_K`.

**Unit quotient (the standard treatment).** The Mellin integral is taken
*not* over all of `K_ℝ^*`, but over a **fundamental domain for the
multiplicative `𝓞ˣ`-action** on `K_ℝ^*` — here Mathlib's
`mixedEmbedding.fundamentalCone K`, the standard fundamental cone. This is
essential for soundness: the element-sum kernel `idealThetaKernel` sums the
Gaussian over *all* nonzero `a ∈ 𝔞`, hence over every `𝓞ˣ`-associate `u·a`
separately. For a field with infinite unit group (rank `r₁+r₂−1 > 0`, i.e. all
`K` except `ℚ` and imaginary quadratic fields) each principal ideal is hit
infinitely often, so the integral over the *whole* space `K_ℝ^*` of the positive
integrand would diverge and the Bochner integral would return `0`. Integrating
over the fundamental cone instead collapses each `𝓞ˣ`-orbit to a single
representative, so the term-by-term Mellin gives one finite contribution
`𝔑((a))^{-s}` per nonzero principal ideal `(a) ⊆ 𝔞` — i.e. exactly the
ideal-sum `∑_{𝔟} 𝔑(𝔟)^{-s}` of the inverse class (the standard treatment).

**Torsion normalisation `1 / w_K` (soundness fix).** The
fundamental cone `mixedEmbedding.fundamentalCone K` is a fundamental domain for
the `𝓞ˣ`-action only **modulo torsion**: it is invariant under the finite
torsion subgroup (`torsion_unit_smul_mem_of_mem`), which acts freely on the
locus `N ≠ 0`. The element-sum kernel `idealThetaKernel` sums over *all* nonzero
`a ∈ 𝔞`, i.e. over full `𝓞ˣ`-orbits, so reassembling the cone over-counts each
orbit's intersection with the cone by the full torsion order
`w_K = Units.torsionOrder K`. The leading factor `1 / w_K` divides this out, so
the per-class evaluation `∑_{𝔟} 𝔑(𝔟)^{-s}` is exact (without it the identity
`completedPartialZeta_idealClassRep_eq` would be off by `w_K`, which is `> 1`
whenever `K` has a nontrivial root of unity, e.g. ℚ or any imaginary quadratic
field).

**Archimedean factor is the whole-space Mellin integral.** The archimedean
Gamma-factor `I(s)` extracted by the term-by-term Mellin evaluation is the
multiplicative Mellin integral of the single Gaussian over the **whole**
`K_ℝ^* = mixedSpace K` (= `DedekindZeta.GammaIntegral.gammaIntegral` of
`gaussian K`), for which `|d_K|^{s/2}·I(s) = ZInfty K s` (`gammaIntegral_gaussian_eq`,
over all of `mixedSpace K` via polar coordinates) — *not* the cone integral, which
is closed under all nonzero real scalings and so yields only a single radial
`Γ`-factor times an angular (regulator) factor rather than the per-place product
`L_ℝ^{r₁}·L_ℂ^{r₂}`. -/
def completedPartialZeta (𝔞 : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  (1 / (Units.torsionOrder K : ℂ)) *
    (Ideal.absNorm 𝔞 : ℂ) ^ s *
      ((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) *
        MeasureTheory.integral (mixedMulHaar K)
          (fun x => (mixedEmbedding.fundamentalCone K).indicator
            (fun x => Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s) x)

open Classical in
/-- A choice of integral-ideal representative for each ideal class, via the
surjectivity of `ClassGroup.mk0` onto the (finite) class group `ClassGroup (𝓞 K)`. -/
def idealClassRep (c : ClassGroup (𝓞 K)) : Ideal (𝓞 K) :=
  ((Function.surjInv ClassGroup.mk0_surjective c : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))

/-- The **completed Dedekind zeta function** `Z_K` of the standard treatment, as
a genuine total function on all of `ℂ`: the finite sum, over the ideal classes
of `𝓞 K`, of the completed partial zeta `Z(𝔞, s)` of a representative ideal `𝔞`
of each class. This is the higher-dimensional Gamma-integral object of
the standard treatment — an actual analytic object à la `completedRiemannZeta`, *not* a
piecewise placeholder. Its meromorphic continuation and its agreement with
`Z_∞ · ζ_K` on `Re s > 1` are stated below. -/
def completedDedekindZeta (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  letI : NumberField K := ‹_›
  ∑ c : ClassGroup (𝓞 K), completedPartialZeta K (idealClassRep K c) s

open Classical in
/-- The ideal class of a nonzero integral ideal `𝔟`, as an element of
`ClassGroup (𝓞 K)`. -/
noncomputable def idealClass (𝔟 : NonzeroIdeal K) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨(𝔟 : Ideal (𝓞 K)), mem_nonZeroDivisors_iff_ne_zero.mpr 𝔟.2⟩

/-! ### Intermediate steps for agreement with Mathlib's `dedekindZeta`

The agreement of the genuine higher-dimensional Gamma-integral object with
`Z_∞ · ζ_K` on `Re s > 1` factors through two lemmas:

* the **per-class Gamma-integral evaluation** (the analytic core of the standard treatment): the completed partial zeta of a class representative equals
  `Z_∞(s)` times the partial zeta `∑_{𝔟 ∈ class c} 𝔑(𝔟)^{-s}`; and
* the **partition over ideal classes**: summing those partial zetas over the
  (finite) class group recovers the full sum over nonzero integral ideals. -/

/-! **Per-class Gamma-integral evaluation** (the standard treatment) and the
resulting agreement `completedDedekindZeta = Z_∞ · ζ_K` on `Re s > 1` are stated
and proved in `DedekindZeta/PerClass.lean` (theorems
`completedPartialZeta_idealClassRep_eq` and `completedDedekindZeta_eq`). They
cannot live here: their proofs consume the analytic intermediate identity
`GammaIntegral.completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum`, which lives
in `DedekindZeta/GammaIntegral.lean` (downstream of this module), so a proof here
would require a circular import. -/

/-- **Absolute summability** of `𝔞 ↦ 𝔑(𝔞)^{-s}` over the nonzero integral ideals
for `1 < s.re`. This is the convergence underlying `dedekindZeta_eq_tsum_absNorm`
(the standard treatment): the analytic input is the big-O bound on the ideal-counting
partial sums together with `LSeriesSummable_of_sum_norm_bigO_and_nonneg`. -/
theorem summable_absNorm_neg_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun 𝔞 : NonzeroIdeal K => (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  classical
  set g : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) with hg
  set φ : NonzeroIdeal K → ℕ := fun 𝔞 ↦ Ideal.absNorm (𝔞 : Ideal (𝓞 K)) with hφ
  set h : NonzeroIdeal K → ℂ := fun 𝔞 ↦ (φ 𝔞 : ℂ) ^ (-s) with hh
  set e := Equiv.sigmaFiberEquiv φ with he
  have hfin : ∀ n : ℕ, Finite {a : NonzeroIdeal K // φ a = n} := by
    intro n
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq n).to_subtype
    apply Finite.of_injective
      (f := fun c : {a : NonzeroIdeal K // φ a = n} ↦
        (⟨(c.1 : Ideal (𝓞 K)), c.2⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    intro a b hab
    have : (a.1 : Ideal (𝓞 K)) = (b.1 : Ideal (𝓞 K)) := by
      simpa using congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hcard : ∀ n : ℕ, n ≠ 0 →
      Nat.card {a : NonzeroIdeal K // φ a = n}
        = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
    intro n hn
    refine Nat.card_congr ?_
    refine
      { toFun := fun c ↦ ⟨(c.1 : Ideal (𝓞 K)), c.2⟩
        invFun := fun d ↦ ⟨⟨d.1, ?_⟩, d.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro hI0
      apply hn
      have : Ideal.absNorm d.1 = 0 := by rw [hI0]; simp
      rw [← d.2, this]
    · intro c; exact Subtype.ext (Subtype.ext rfl)
    · intro d; exact Subtype.ext rfl
  have hpart : ∀ n : ℕ,
      ∑ k ∈ Finset.Icc 1 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k}
        = Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} := by
    intro n
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  set gℝ : ℕ → ℝ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) with hgℝ
  have hbigO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, gℝ k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    have H := (Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
    have h2 := (H.isBigO_one ℝ).mul (isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)
    refine h2.congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      simp only [Function.comp_apply]
      rw [div_mul_cancel₀ _ (by exact_mod_cast hn.ne')]
      rw [hgℝ, ← Nat.cast_sum, hpart n]
      congr 1
      exact (Nat.card_congr (Equiv.subtypeEquivRight (fun I ↦ by exact_mod_cast Iff.rfl))).symm
    · filter_upwards [eventually_ge_atTop 0] with n hn
      rw [one_mul, Real.rpow_one]
  have hLS : LSeriesSummable g s := by
    have hsum := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := gℝ)
      hbigO (fun n ↦ Nat.cast_nonneg _) zero_le_one hs
    refine (LSeriesSummable_congr s (fun {n} _ ↦ ?_)).mp hsum
    simp [hgℝ, hg]
  have hnorm : Summable (fun n : ℕ ↦ ‖LSeries.term g s n‖) := summable_norm_iff.mpr hLS
  have hsumH : Summable h := by
    apply Summable.of_norm
    have hnormeq : ∀ 𝔞 : NonzeroIdeal K, ‖h 𝔞‖ = (φ 𝔞 : ℝ) ^ (-s.re) := by
      intro 𝔞
      have hpos : 0 < φ 𝔞 := by
        rw [hφ]; simp only
        exact Nat.pos_of_ne_zero (fun hz ↦ 𝔞.2 ((Ideal.absNorm_eq_zero_iff).mp hz))
      rw [hh]; simp only
      rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    rw [funext hnormeq]
    refine (Equiv.summable_iff e).mp ?_
    change Summable fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) =>
      (φ (e p) : ℝ) ^ (-s.re)
    rw [summable_sigma_of_nonneg (fun p ↦ Real.rpow_nonneg (by positivity) _)]
    refine ⟨fun n ↦ ?_, ?_⟩
    · haveI := hfin n
      exact Summable.of_finite
    · refine hnorm.congr (fun n ↦ ?_)
      by_cases hn : n = 0
      · subst hn
        haveI : IsEmpty {a : NonzeroIdeal K // φ a = 0} := by
          refine ⟨fun a ↦ ?_⟩
          have : Ideal.absNorm (a.1 : Ideal (𝓞 K)) = 0 := a.2
          exact a.1.2 ((Ideal.absNorm_eq_zero_iff).mp this)
        simp [tsum_empty, LSeries.term_zero]
      · have hval : ∀ y : {a : NonzeroIdeal K // φ a = n},
            (fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) =>
              (φ (e p) : ℝ) ^ (-s.re)) ⟨n, y⟩ = (n : ℝ) ^ (-s.re) := by
          intro y; simp only; rw [show e ⟨n, y⟩ = y.1 from rfl, y.2]
        rw [tsum_congr hval]
        haveI := hfin n
        haveI : Fintype {a : NonzeroIdeal K // φ a = n} := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card, hcard n hn]
        rw [LSeries.norm_term_eq, if_neg hn, hg]
        simp only [Complex.norm_natCast, Real.rpow_neg (Nat.cast_nonneg _)]
        rw [div_eq_mul_inv]
  exact hsumH

/-- **Partition over ideal classes**: the finite sum over the class group of the
partial Dedekind zetas recovers the full sum over nonzero integral ideals. -/
theorem sum_class_tsum_absNorm {s : ℂ} (hs : 1 < s.re) :
    ∑ c : ClassGroup (𝓞 K),
        ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c},
          (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s)
      = ∑' 𝔞 : NonzeroIdeal K, (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  set F : NonzeroIdeal K → ℂ :=
    fun 𝔞 => (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s) with hF
  -- `idealClass` partitions the nonzero integral ideals into the finitely many
  -- ideal classes; identify `NonzeroIdeal K` with the sigma of the fibres.
  set e := Equiv.sigmaFiberEquiv (idealClass K) with he
  have hsummable := summable_absNorm_neg_cpow K hs
  have hsig : Summable
      (fun p : (Σ c, {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c}) => F (e p)) :=
    (Equiv.summable_iff e).mpr hsummable
  -- Expand the full ideal sum as the (finite) class sum of fibrewise sums.
  rw [← Equiv.tsum_eq e F, hsig.tsum_sigma, tsum_fintype]
  refine Finset.sum_congr rfl (fun c _ => tsum_congr (fun 𝔟 => ?_))
  rw [he, hF]
  rfl

/-! ## Theta/cone integrability infrastructure retained for the partial-zeta bridge

The following material supports the per-class Mellin evaluation on the convergence
strip and the cone/radial estimates consumed by `DedekindZeta.ConeMellinBridge`.
A fuller upstream development also built a meromorphic-continuation/functional-
equation layer, but the final functional-equation theorems are not part of this
pruned in-repo closure because `SumProduct` only needs the residue inequality on
real `s > 1`.
-/





/-- **Measurability of the fractional theta integrand.**
For any fractional ideal `I` and any `t : ℂ`, the integrand
`y ↦ Θ(I, y)·N(y)^t` is `AEStronglyMeasurable` against `mixedMulHaar K`.

`Theta.mixedThetaKernel K I` is the `∑'` over the countable index
`{a : K // a ∈ I ∧ a ≠ 0}` of the summands `y ↦ (mixedGaussian K (y·σa) : ℂ)`,
each (strongly) measurable (mirroring
`GammaIntegral.aestronglyMeasurable_mixedGaussian_mul_norm_cpow`); the `∑'` of
(AE)strongly-measurable functions over a countable index is (AE)strongly
measurable (`AEStronglyMeasurable.tsum`). Multiplying by the measurable norm power
`N(y)^t` keeps it measurable. This part does **not** use `1 < t.re`. -/
theorem aestronglyMeasurable_mixedThetaKernel_mul_norm_cpow
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) :
    MeasureTheory.AEStronglyMeasurable
      (fun y => Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ t)
      (mixedMulHaar K) := by
  -- `K` is countable (finite-dimensional over the countable field `ℚ`), hence so
  -- is the index set of the theta `∑'`; this gives `IsCountablyGenerated` for the
  -- unconditional summation filter consumed by `AEStronglyMeasurable.tsum`.
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hker : MeasureTheory.AEStronglyMeasurable
      (fun y => Theta.mixedThetaKernel K I y) (mixedMulHaar K) := by
    simp only [Theta.mixedThetaKernel]
    apply MeasureTheory.AEStronglyMeasurable.tsum
    intro a
    apply Measurable.aestronglyMeasurable
    refine Complex.measurable_ofReal.comp ?_
    unfold Theta.mixedGaussian
    fun_prop
  have hpow : MeasureTheory.AEStronglyMeasurable
      (fun y => (mixedEmbedding.norm y : ℂ) ^ t) (mixedMulHaar K) := by
    apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp
      (mixedEmbedding.continuous_norm K).measurable).pow_const t
  exact hker.mul hpow

/-- **Per-element whole-space `enorm` scale invariance** for the shifted Minkowski
Gaussian Mellin integrand (helper 1). For any
nonzero `a : K` and `t : ℂ`, translating the Gaussian argument by `σ a` rescales
the whole-space `enorm`-`lintegral` of `g(x·σ a)·N(x)^t` by the constant
`𝔑(σ a)^{-Re t} = N(σ a)^{-Re t}`:

    ∫⁻ x, ‖g(x·σ a)·N(x)^t‖ₑ d^*x
      = ENNReal.ofReal (N(σ a)^{-Re t}) · ∫⁻ x, ‖g(x)·N(x)^t‖ₑ d^*x.

This is the `lintegral`/`enorm` analogue of
`GammaIntegral.mellin_mixedGaussian_mul_eq` (which is downstream and so cannot be
cited here): right-translation invariance of `mixedMulHaar`
(`mixedMulHaar_map_mul_right`) reduces the integrand to `g(y)·N(y·σ(a)⁻¹)^t`, and
`|N(y·σ(a)⁻¹)| = |N y|·|N(σ a)|⁻¹` factors out the constant
`N(σ a)^{-Re t}` from the `enorm`. It is stated for a *general* nonzero `a ∈ K`
(not just an integral element), as needed by the fractional-ideal assembly. -/
theorem lintegral_enorm_mixedGaussian_mul_norm_cpow_eq
    {a : K} (ha : a ≠ 0) (t : ℂ) :
    ∫⁻ x, ‖(Theta.mixedGaussian K (x * mixedEmbedding K a) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K)
      = ENNReal.ofReal (mixedEmbedding.norm (mixedEmbedding K a) ^ (-t.re))
          * ∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) := by
  -- Mirror `GammaIntegral.mellin_mixedGaussian_mul_eq`, but on `ℝ≥0∞`/`enorm`.
  set c : mixedEmbedding.mixedSpace K := mixedEmbedding K a with hcdef
  have hcne : mixedEmbedding.norm c ≠ 0 := by
    have hn : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
    rw [hcdef, mixedEmbedding.norm_eq_norm]
    simpa using hn
  have hcpos : 0 < mixedEmbedding.norm c :=
    (mixedEmbedding.norm_nonneg c).lt_of_ne (Ne.symm hcne)
  have hcinvpos : 0 < (mixedEmbedding.norm c)⁻¹ := inv_pos.mpr hcpos
  have hcc : c * c⁻¹ = 1 := Theta.mul_inv_cancel_of_norm_ne_zero K hcne
  -- `N(c⁻¹) = (N c)⁻¹` from `N(c)·N(c⁻¹) = N(1) = 1` (the downstream
  -- `mixedEmbedding_norm_inv` is not available at this layer).
  have hNcinv : mixedEmbedding.norm c⁻¹ = (mixedEmbedding.norm c)⁻¹ := by
    have h1 : mixedEmbedding.norm c * mixedEmbedding.norm c⁻¹ = 1 := by
      rw [← map_mul, hcc, map_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  -- The integrand is `F (x·c)` with `F y = g y · N(y·c⁻¹)^t`.
  set F : mixedEmbedding.mixedSpace K → ℂ :=
    fun y => (Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm (y * c⁻¹) : ℂ) ^ t
    with hFdef
  have hFmeas : Measurable (fun y => ‖F y‖ₑ) := by
    refine Measurable.enorm ?_
    refine Measurable.mul ?_ ?_
    · refine Complex.measurable_ofReal.comp ?_
      unfold Theta.mixedGaussian; fun_prop
    · refine (Complex.measurable_ofReal.comp ?_).pow_const t
      exact (mixedEmbedding.continuous_norm K).measurable.comp
        (continuous_id.mul continuous_const).measurable
  -- Base (unshifted) integrand measurability, for `lintegral_mul_const`.
  have hgmeas : Measurable
      (fun y => ‖(Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ) := by
    refine Measurable.enorm ?_
    refine Measurable.mul ?_ ?_
    · refine Complex.measurable_ofReal.comp ?_
      unfold Theta.mixedGaussian; fun_prop
    · exact (Complex.measurable_ofReal.comp
        (mixedEmbedding.continuous_norm K).measurable).pow_const t
  -- Rewrite the LHS integrand as `‖F (x·c)‖ₑ`.
  have hrw : (fun x => ‖(Theta.mixedGaussian K (x * c) : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ)
      = fun x => ‖F (x * c)‖ₑ := by
    funext x
    simp only [hFdef, mul_assoc, hcc, mul_one]
  -- Right-translation invariance of `mixedMulHaar` substitutes `x ↦ x·c`.
  have hmap := mixedMulHaar_map_mul_right (K := K) hcne
  have hsub : ∫⁻ x, ‖F (x * c)‖ₑ ∂(mixedMulHaar K)
      = ∫⁻ y, ‖F y‖ₑ ∂(mixedMulHaar K) := by
    rw [← MeasureTheory.lintegral_map hFmeas (measurable_mul_right_mixedSpace K c), hmap]
  -- Pointwise factorization of the constant `N(c)^{-Re t}` out of the `enorm`.
  have hptw : ∀ y, ‖F y‖ₑ
      = ‖(Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ
          * ENNReal.ofReal (mixedEmbedding.norm c ^ (-t.re)) := by
    intro y
    rw [hFdef]
    simp only
    rw [map_mul mixedEmbedding.norm y c⁻¹, hNcinv,
      Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (mixedEmbedding.norm_nonneg y)
        (inv_nonneg.mpr (mixedEmbedding.norm_nonneg c)) t,
      ← mul_assoc, enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hcinvpos,
      Real.inv_rpow (mixedEmbedding.norm_nonneg c),
      ← Real.rpow_neg (mixedEmbedding.norm_nonneg c)]
  calc
    ∫⁻ x, ‖(Theta.mixedGaussian K (x * c) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K)
        = ∫⁻ x, ‖F (x * c)‖ₑ ∂(mixedMulHaar K) := by rw [hrw]
      _ = ∫⁻ y, ‖F y‖ₑ ∂(mixedMulHaar K) := hsub
      _ = ∫⁻ y, ‖(Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ
              * ENNReal.ofReal (mixedEmbedding.norm c ^ (-t.re)) ∂(mixedMulHaar K) :=
          MeasureTheory.lintegral_congr hptw
      _ = (∫⁻ y, ‖(Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ
              ∂(mixedMulHaar K))
            * ENNReal.ofReal (mixedEmbedding.norm c ^ (-t.re)) :=
          MeasureTheory.lintegral_mul_const _ hgmeas
      _ = ENNReal.ofReal (mixedEmbedding.norm c ^ (-t.re))
            * ∫⁻ y, ‖(Theta.mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ
              ∂(mixedMulHaar K) := by rw [mul_comm]

section GaussianMellinConvergence
open MeasureTheory NumberField.mixedEmbedding

/-- **Real-place 1D integrability helper** (the standard treatment). The per-real-place
integrand obtained after absorbing the `dx/|x|` density of `mixedMulHaar`, namely
`x ↦ e^{-π x²} |x|^{σ-1}`, is `volume`-integrable on `ℝ` when `0 < σ`. Established
here at the `Statements` layer (rather than cited from the downstream
`GammaIntegral`, which imports this file) to feed the whole-space convergence
lemma below. Mirrors `integrable_rpow_mul_exp_neg_mul_sq`, using evenness and
`integrableOn_rpow_mul_exp_neg_mul_sq` on `Set.Ioi 0`. -/
theorem integrable_real_gaussian_mul_abs_rpow {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.Integrable
      (fun x : ℝ => Real.exp (-Real.pi * x ^ 2) * |x| ^ (σ - 1)) := by
  set b : ℝ := Real.pi
  set s : ℝ := σ - 1
  have hb : 0 < b := Real.pi_pos
  have hs : -1 < s := by simp only [s]; linarith
  suffices h : MeasureTheory.Integrable
      (fun x : ℝ => |x| ^ s * Real.exp (-b * x ^ 2)) by
    refine h.congr ?_
    filter_upwards with x
    ring
  have hIoi : MeasureTheory.IntegrableOn
      (fun x : ℝ => |x| ^ s * Real.exp (-b * x ^ 2)) (Set.Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq hb hs).congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with x hx
    rw [abs_of_nonneg (le_of_lt hx)]
  rw [← integrableOn_univ, ← @Set.Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hIoi⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simp only [Function.comp_def, neg_sq, Set.neg_preimage, Set.neg_Iio, neg_zero, abs_neg]
  exact hIoi

open Set in
/-- **Per-complex-place 1D integrability helper** (the standard treatment). After absorbing
the `(2/π) dλ/|z|²` density of `mixedMulHaar` at a complex place, the per-place
integrand is `e^{-2π‖z‖²}·‖z‖^{2(σ-1)}`, `volume`-integrable on `ℂ` exactly when
`0 < σ`. Established here at the `Statements` layer. Proof by polar coordinates,
reducing to a radial integral via `integrableOn_rpow_mul_exp_neg_mul_sq`. -/
theorem integrable_complexPlace_gaussian_rpow {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.Integrable
      (fun z : ℂ => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (σ - 1))) volume := by
  have hmeas : Measurable
      (fun z : ℂ => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (σ - 1))) := by
    fun_prop
  have hnonneg : 0 ≤ᵐ[volume]
      (fun z : ℂ => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (σ - 1))) := by
    filter_upwards with z
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (norm_nonneg _) _)
  have hrad : (∫⁻ x in Set.Ioi (0:ℝ),
      ENNReal.ofReal (x ^ (2*σ - 1) * Real.exp (-(2*Real.pi) * x ^ 2))) < ∞ := by
    have hb : (0:ℝ) < 2 * Real.pi := by positivity
    have hs : (-1:ℝ) < 2*σ - 1 := by linarith
    have hint := integrableOn_rpow_mul_exp_neg_mul_sq hb hs
    have hfin := hint.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal] at hfin
    · exact hfin
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have htgt : (polarCoord.target : Set (ℝ×ℝ)) = Set.Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  rw [htgt]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      (g := fun p : ℝ×ℝ => ENNReal.ofReal p.1 •
        ENNReal.ofReal (Real.exp (-2 * π * p.1 ^ 2) * p.1 ^ (2 * (σ - 1)))) ?_]
  · rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
    · simp_rw [lintegral_const, Measure.restrict_apply_univ]
      rw [lintegral_mul_const]
      · refine ENNReal.mul_lt_top ?_ ?_
        · rw [setLIntegral_congr_fun measurableSet_Ioi
            (g := fun x : ℝ => ENNReal.ofReal (x ^ (2*σ-1) * Real.exp (-(2*Real.pi) * x ^ 2))) ?_]
          · exact hrad
          · intro x hx
            have hx0 : (0:ℝ) < x := hx
            dsimp only
            rw [smul_eq_mul, ← ENNReal.ofReal_mul hx0.le]
            congr 1
            rw [show (-2 * π * x ^ 2) = (-(2*π)*x^2) by ring]
            have hxc : x * x ^ (2*(σ-1)) = x ^ (2*σ-1) := by
              rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hx0)]
              congr 1; ring
            rw [mul_comm (Real.exp (-(2*π)*x^2)) (x ^ (2*(σ-1))), ← mul_assoc, hxc]
        · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      · fun_prop
    · fun_prop
  · intro p hp
    have hp1 : (0:ℝ) < p.1 := hp.1
    simp only [Complex.norm_polarCoord_symm, abs_of_pos hp1]

-- The product-measure reduction unfolds `mixedMulHaar` and the place-by-place
-- norm/Gaussian factorisations, whose combined definitional unfolding and `rpow`
-- rewriting exceeds the default heartbeat budget.
set_option maxHeartbeats 1600000 in
/-- **`withDensity` + product-measure reduction for the Gaussian Mellin integrand**
(the standard treatment). Reduces whole-space integrability of `g(x)·N(x)^s` against
`mixedMulHaar K` to the per-place 1D integrabilities `hr`, `hc` (with `σ := s.re`).
Established at the `Statements` layer (rather than cited from `GammaIntegral`,
which imports this file). Route: `mixedMulHaar = volume.withDensity (...)`, reduce
via `integrable_withDensity_iff_integrable_smul'`, dominate the integrand by the
place-wise product `(2/π)^{r₂}·∏ f_ℝ·∏ f_ℂ` (equal off the null locus `N(x)=0`),
which is `volume`-integrable by `Integrable.fintype_prod`/`Integrable.mul_prod`. -/
theorem integrable_mixedGaussian_mellin_of_perPlace {s : ℂ} (hs : 0 < s.re)
    (hr : MeasureTheory.Integrable
      (fun x : ℝ => Real.exp (-Real.pi * x ^ 2) * |x| ^ (s.re - 1)) volume)
    (hc : MeasureTheory.Integrable
      (fun z : ℂ => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (s.re - 1)))
        volume) :
    MeasureTheory.Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (Theta.mixedGaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedMulHaar K) := by
  classical
  set σ : ℝ := s.re with hσ
  set c : ℝ := (2 / Real.pi) ^ nrComplexPlaces K with hc_def
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def]; positivity
  set fR : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2) * |x| ^ (σ - 1) with hfR
  set fC : ℂ → ℝ := fun z => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (σ - 1)) with hfC
  set F : mixedEmbedding.mixedSpace K → ℝ := fun x =>
    c * ((∏ w : {w : InfinitePlace K // IsReal w}, fR (x.1 w)) *
          (∏ w : {w : InfinitePlace K // IsComplex w}, fC (x.2 w))) with hF
  have hRprod : MeasureTheory.Integrable
      (fun a : {w : InfinitePlace K // IsReal w} → ℝ => ∏ w, fR (a w)) volume := by
    rw [volume_pi]
    exact MeasureTheory.Integrable.fintype_prod (fun _ => hr)
  have hCprod : MeasureTheory.Integrable
      (fun b : {w : InfinitePlace K // IsComplex w} → ℂ => ∏ w, fC (b w)) volume := by
    rw [volume_pi]
    exact MeasureTheory.Integrable.fintype_prod (fun _ => hc)
  have hmul : MeasureTheory.Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (∏ w : {w : InfinitePlace K // IsReal w}, fR (x.1 w)) *
          (∏ w : {w : InfinitePlace K // IsComplex w}, fC (x.2 w))) volume := by
    exact MeasureTheory.Integrable.mul_prod hRprod hCprod
  have hFint : MeasureTheory.Integrable F volume := by
    rw [hF]; exact hmul.const_mul c
  rw [mixedMulHaar, integrable_withDensity_iff_integrable_smul']
  rotate_left
  · refine (Measurable.ennreal_ofReal ?_)
    exact (measurable_const.mul ((mixedEmbedding.continuous_norm K).measurable.inv))
  · exact ae_of_all _ (fun x => ENNReal.ofReal_lt_top)
  refine hFint.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.smul
    next =>
      exact Complex.measurable_ofReal.comp
        (((measurable_const.mul
          ((mixedEmbedding.continuous_norm K).measurable.inv))).ennreal_ofReal).ennreal_toReal
    · apply Measurable.mul
      · refine Complex.measurable_ofReal.comp ?_
        have : Measurable fun x : mixedEmbedding.mixedSpace K => Theta.mixedGaussian K x := by
          unfold Theta.mixedGaussian; fun_prop
        exact this
      · exact (Complex.measurable_ofReal.comp
          (mixedEmbedding.continuous_norm K).measurable).pow_const s
  · refine ae_of_all _ (fun x => ?_)
    have hN0 : 0 ≤ mixedEmbedding.norm x := mixedEmbedding.norm_nonneg x
    have hdens : (ENNReal.ofReal (c * (mixedEmbedding.norm x)⁻¹)).toReal
        = c * (mixedEmbedding.norm x)⁻¹ := by
      rw [ENNReal.toReal_ofReal]
      positivity
    have hFnonneg : 0 ≤ F x := by
      rw [hF]
      refine mul_nonneg hc_nonneg (mul_nonneg (Finset.prod_nonneg ?_) (Finset.prod_nonneg ?_))
      · intro w _; rw [hfR]; positivity
      · intro w _; rw [hfC]; positivity
    have hgauss_pos : 0 < Theta.mixedGaussian K x := Real.exp_pos _
    have hnormg : ‖(Theta.mixedGaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s‖
        = Theta.mixedGaussian K x * (mixedEmbedding.norm x) ^ σ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hgauss_pos.le,
        Complex.norm_cpow_eq_rpow_re_of_nonneg hN0 (by rw [← hσ]; exact ne_of_gt hs)]
    rw [_root_.norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, hdens, hnormg]
    by_cases hx0 : mixedEmbedding.norm x = 0
    · rw [hx0]
      simp only [inv_zero, mul_zero, zero_mul]
      exact hFnonneg
    · have hNpos : 0 < mixedEmbedding.norm x := lt_of_le_of_ne hN0 (Ne.symm hx0)
      have hgaussprod : Theta.mixedGaussian K x
          = ∏ w : InfinitePlace K, Real.exp (-Real.pi * ((mult w : ℝ) * normAtPlace w x ^ 2)) := by
        rw [Theta.mixedGaussian, Finset.mul_sum, Real.exp_sum]
      have hpowprod : (mixedEmbedding.norm x) ^ σ * (mixedEmbedding.norm x)⁻¹
          = ∏ w : InfinitePlace K, normAtPlace w x ^ ((mult w : ℝ) * (σ - 1)) := by
        rw [← Real.rpow_neg_one (mixedEmbedding.norm x),
          ← Real.rpow_add hNpos]
        rw [mixedEmbedding.norm_apply]
        rw [← Real.finsetProd_rpow _ _
          (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _)]
        refine Finset.prod_congr rfl (fun w _ => ?_)
        rw [← Real.rpow_natCast (normAtPlace w x) (mult w),
          ← Real.rpow_mul (normAtPlace_nonneg w x)]
        ring_nf
      have hval : c * (mixedEmbedding.norm x)⁻¹ *
          (Theta.mixedGaussian K x * (mixedEmbedding.norm x) ^ σ) = F x := by
        have e1 : c * (mixedEmbedding.norm x)⁻¹ *
            (Theta.mixedGaussian K x * (mixedEmbedding.norm x) ^ σ)
            = c * (Theta.mixedGaussian K x *
                ((mixedEmbedding.norm x) ^ σ * (mixedEmbedding.norm x)⁻¹)) := by ring
        rw [e1, hgaussprod, hpowprod, ← Finset.prod_mul_distrib, hF,
          InfinitePlace.prod_eq_prod_mul_prod
            (fun w => Real.exp (-Real.pi * ((mult w : ℝ) * normAtPlace w x ^ 2)) *
              normAtPlace w x ^ ((mult w : ℝ) * (σ - 1)))]
        congr 1
        congr 1
        · refine Finset.prod_congr rfl (fun w _ => ?_)
          rw [hfR, mult_isReal, normAtPlace_apply_of_isReal w.2, Nat.cast_one, one_mul, one_mul,
            Real.norm_eq_abs, sq_abs]
        · refine Finset.prod_congr rfl (fun w _ => ?_)
          rw [hfC, mult_isComplex, normAtPlace_apply_of_isComplex w.2, Nat.cast_ofNat]
          congr 1
          congr 1
          ring
      rw [hval]

/-- **Whole-space Gaussian Mellin convergence** (the standard treatment). For `0 < s.re` the
base Minkowski Gaussian Mellin integrand `g(x)·N(x)^s` is `mixedMulHaar`-integrable
on `K_ℝ^*`. Established at the `Statements` layer (mirror of
`GammaIntegral.integrable_gaussian_mellin`, which lives downstream and so cannot
be cited here) by feeding the per-place 1D helpers into the product-measure
reduction. NB: this is against the canonical upstream `mixedGaussian`/`mixedMulHaar`
objects, whereas `GammaIntegral.integrable_gaussian_mellin` is the legacy
`gaussian`/`mulHaar` form; both reuse the single-home generic 1D helpers
(`integrable_real_gaussian_mul_abs_rpow`, `integrable_complexPlace_gaussian_rpow`)
defined here, so no generic analysis lemma is duplicated. -/
theorem integrable_mixedGaussian_mellin {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (Theta.mixedGaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedMulHaar K) :=
  integrable_mixedGaussian_mellin_of_perPlace K hs
    (integrable_real_gaussian_mul_abs_rpow hs)
    (integrable_complexPlace_gaussian_rpow hs)

end GaussianMellinConvergence

/-- **Whole-space Gaussian Mellin `enorm` finiteness**
(helper 2). For `1 < t.re` the whole-space
`enorm`-`lintegral` of the base Minkowski Gaussian Mellin integrand
`g(x)·N(x)^t` is finite:

    ∫⁻ x, ‖g(x)·N(x)^t‖ₑ d^*x ≠ ∞.

This is the `M`/`|I(t)|` archimedean Gamma-factor finiteness: Gaussian decay at
the large-norm end controls the `N → ∞` tail, and the condition `Re t > 1`
governs convergence at the small-norm end. It is the genuine convergence input
(the `1 < Re t` threshold) feeding the fractional-ideal assembly. -/
theorem lintegral_enorm_mixedGaussian_mul_norm_cpow_ne_top
    {t : ℂ} (ht : 1 < t.re) :
    ∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) ≠ ∞ := by
  -- `1 < Re t ⇒ 0 < Re t`, the convergence threshold for whole-space
  -- integrability; finiteness of `∫⁻ ‖·‖ₑ` is exactly `HasFiniteIntegral`.
  have ht0 : (0 : ℝ) < t.re := lt_trans one_pos ht
  exact (integrable_mixedGaussian_mellin K ht0).hasFiniteIntegral.ne

/-- **Unit-orbit cone → whole-space collapse** for the shifted Gaussian Mellin
`enorm` integrand (helper 3). For any `a : K`
and `t : ℂ`, summing the fundamental-cone `enorm`-`lintegral` of the
`g`-argument shifted along the `(𝓞 K)ˣ`-orbit (the cone-action group
`Multiplicative (Fin (NumberField.Units.rank K) → ℤ)`) over the whole group collapses to the
whole-space `enorm`-`lintegral`:

    ∑' g, ∫⁻ x in C, ‖g((g • x)·σ a)·N(x)^t‖ₑ d^*x
      = ∫⁻ x, ‖g(x·σ a)·N(x)^t‖ₑ d^*x.

This is `IsFundamentalDomain.lintegral_eq_tsum` for
`isFundamentalDomain_fundamentalCone` applied to the nonnegative integrand
`y ↦ ‖g(y·σ a)·N(y)^t‖ₑ`, using that the unit action is measure-preserving
(`measurePreserving_unitSMul`) and norm-1 (so `N(g • x) = N x`, which is why the
norm-power factor reads `N(x)^t` rather than `N(g • x)^t`). The orbit shift is
written with the global unit action `coneUnitHom g • y` (equal to the cone action
`g • y` by `coneSMul_def`), since the cone `MulAction` instance is section-local.
Stated in the
cone-indicator `enorm`-`lintegral` form that the assembly child consumes. -/
theorem tsum_unit_lintegral_enorm_cone_eq_lintegral_whole
    (a : K) (t : ℂ) :
    (∑' g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ),
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K
                ((coneUnitHom (K := K) g • y) * mixedEmbedding K a) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K))
      = ∫⁻ x, ‖(Theta.mixedGaussian K (x * mixedEmbedding K a) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) := by
  -- The cone `MulAction`/measurability/invariance instances are `local` to the
  -- `MulHaarRightInvariance` section above; re-introduce them locally so the
  -- `IsFundamentalDomain.lintegral_eq_tsum''` machinery applies here.
  letI := DedekindZeta.coneMulAction (K := K)
  letI := DedekindZeta.coneMeasurableConstSMul (K := K)
  letI := DedekindZeta.coneCountable (K := K)
  letI := DedekindZeta.coneSMulInvariantMeasure (K := K)
  -- The nonnegative whole-space integrand `f y = ‖g(y·σa)·N(y)^t‖ₑ`.
  set f : mixedEmbedding.mixedSpace K → ℝ≥0∞ :=
    fun y => ‖(Theta.mixedGaussian K (y * mixedEmbedding K a) : ℂ)
      * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ with hf
  have hFD := isFundamentalDomain_fundamentalCone (K := K)
  have hmeas : MeasurableSet (mixedEmbedding.fundamentalCone K) :=
    mixedEmbedding.measurableSet_fundamentalCone K
  -- `∫⁻ f = ∑' g, ∫⁻ x in C, f (g • x)` for the cone fundamental domain.
  rw [hFD.lintegral_eq_tsum'' f]
  refine tsum_congr (fun g => ?_)
  -- Move the cone restriction back into an indicator on the right.
  rw [← MeasureTheory.lintegral_indicator hmeas]
  refine MeasureTheory.lintegral_congr (fun x => ?_)
  by_cases hx : x ∈ mixedEmbedding.fundamentalCone K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hf]
    -- `g • x = coneUnitHom g • x` and the unit action preserves `N`, so
    -- `N (g • x) = N x` and the two integrands coincide.
    simp only [coneSMul_def, Theta.norm_unitSMul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, enorm_zero]

variable {K} in
/-- **The cone-action group acting on the nonzero elements of a fractional ideal.**
The cone-action group
`G = Multiplicative (Fin (rank K) → ℤ)` acts on
`S = {a : K // a ∈ I ∧ a ≠ 0}` by multiplication through `coneUnitHom`:
`g • a = ((coneUnitHom g : 𝓞 K) : K) * a`. Membership in `I` is preserved because
`I` is an `𝓞 K`-submodule (`Submodule.smul_mem`) and `coneUnitHom g` is a unit, so
the product stays nonzero. This is the algebraic input to the free-orbit collapse
of the dominating series. -/
instance coneFracSMul (I : FractionalIdeal (𝓞 K)⁰ K) :
    MulAction (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} where
  smul g a := ⟨((coneUnitHom (K := K) g : 𝓞 K) : K) * a.1, by
    refine ⟨?_, ?_⟩
    · have h := (I : Submodule (𝓞 K) K).smul_mem (coneUnitHom (K := K) g : 𝓞 K) a.2.1
      rwa [Algebra.smul_def] at h
    · refine mul_ne_zero ?_ a.2.2
      simpa using (coneUnitHom (K := K) g).ne_zero⟩
  one_smul a := by
    apply Subtype.ext
    show ((coneUnitHom (K := K) 1 : 𝓞 K) : K) * a.1 = a.1
    simp
  mul_smul g h a := by
    apply Subtype.ext
    show ((coneUnitHom (K := K) (g * h) : 𝓞 K) : K) * a.1
        = ((coneUnitHom (K := K) g : 𝓞 K) : K)
            * (((coneUnitHom (K := K) h : 𝓞 K) : K) * a.1)
    rw [map_mul]
    push_cast
    ring

/-- **Free-orbit collapse for the fractional cone theta dominating series.**
The per-element series over the nonzero
`a ∈ I` of cone `enorm`-`lintegral`s of the shifted Gaussian Mellin integrand
`g(y·σ a)·N(y)^t` collapses to the base whole-space Gaussian Mellin
`enorm`-`lintegral` `M` times an *orbit-indexed* norm-power series.

The acting group `G = Multiplicative (Fin (rank K) → ℤ)` acts on
`S = {a : K // a ∈ I ∧ a ≠ 0}` by multiplication through `coneUnitHom`
(`coneFracSMul`), and this action is free (`coneUnitHom` is injective via
`coneUnitHom_mem_torsion_iff`, and `a ≠ 0`). For an orbit representative `a₀`,
summing the per-element cone-lintegral over the orbit equals (via
`mixedEmbedding.unitSMul_smul` + `map_mul` rewriting each `a = coneUnitHom g • a₀`
to the helper-4 summand, then `tsum_unit_lintegral_enorm_cone_eq_lintegral_whole`)
the whole-space value, which by `lintegral_enorm_mixedGaussian_mul_norm_cpow_eq`
is `ofReal (N(σ a₀)^{-Re t}) · M`. Reassembling over the free `G`-orbits
(`MulAction` orbit decomposition of `∑' a : S`) factors out `M`. Each orbit term
is `ofReal (N(σ a₀)^{-Re t})` for an orbit representative `a₀ ∈ I`, `a₀ ≠ 0`, and
the orbit index injects into the nonzero principal fractional ideals `⊆ I`, as
required by the downstream finiteness conclusion. -/
theorem tsum_cone_lintegral_enorm_eq_mul_tsum_orbit
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) :
    (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K a.1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K))
      = (∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K))
        * ∑' o : Quotient (MulAction.orbitRel
              (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
              {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
            ENNReal.ofReal
              (mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)) := by
  classical
  -- The cone-action group and the index set of nonzero elements of `I`.
  -- `coneFracSMul I` is a global instance, so the `MulAction` is available.
  -- Abbreviations are written out in full to keep instance resolution happy.
  -- `coneUnitHom` is injective: if `coneUnitHom a = coneUnitHom b` then
  -- `coneUnitHom (a*b⁻¹) = 1 ∈ torsion K`, so `a*b⁻¹ = 1` by
  -- `coneUnitHom_mem_torsion_iff`.
  have hcuh_inj : Function.Injective (coneUnitHom (K := K)) := by
    intro a b hab
    have h1 : coneUnitHom (K := K) (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : (coneUnitHom (K := K) (a * b⁻¹) : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
      rw [h1]; exact one_mem _
    have h3 := (coneUnitHom_mem_torsion_iff (K := K) (a * b⁻¹)).mp h2
    rwa [mul_inv_eq_one] at h3
  -- The cone action on `S`, unfolded, multiplies by `coneUnitHom g` in `K`.
  have hsmul : ∀ (g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      (a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
      (g • a).1 = ((coneUnitHom (K := K) g : 𝓞 K) : K) * a.1 := fun _ _ => rfl
  -- Freeness: `g • a = g' • a` with `a ≠ 0` forces `g = g'`.
  have hfree : ∀ {g g' : Multiplicative (Fin (NumberField.Units.rank K) → ℤ)}
      {a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}},
      g • a = g' • a → g = g' := by
    intro g g' a h
    have hval : ((coneUnitHom (K := K) g : 𝓞 K) : K) * a.1
        = ((coneUnitHom (K := K) g' : 𝓞 K) : K) * a.1 := by
      rw [← hsmul, ← hsmul, h]
    have hk : ((coneUnitHom (K := K) g : 𝓞 K) : K)
        = ((coneUnitHom (K := K) g' : 𝓞 K) : K) := mul_right_cancel₀ a.2.2 hval
    apply hcuh_inj
    apply Units.ext
    exact_mod_cast hk
  -- The free-orbit reindexing equivalence `Σ (o : Ω), G ≃ S`.
  let F : (Σ _o : Quotient (MulAction.orbitRel
        (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
        {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
        Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      → {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} :=
    fun p => p.2 • Quotient.out p.1
  have hFsurj : Function.Surjective F := by
    intro a
    set o₀ := Quotient.mk (MulAction.orbitRel
      (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) a with ho₀
    have hrel : MulAction.orbitRel _ _ (Quotient.out o₀) a :=
      Quotient.exact (Quotient.out_eq o₀)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨c, hc⟩ := hrel
    refine ⟨⟨o₀, c⁻¹⟩, ?_⟩
    show c⁻¹ • Quotient.out o₀ = a
    rw [← hc, inv_smul_smul]
  have hFinj : Function.Injective F := by
    rintro ⟨o, g⟩ ⟨o', g'⟩ h
    have h' : g • Quotient.out o = g' • Quotient.out o' := h
    have hmem : Quotient.out o ∈ MulAction.orbit _ (Quotient.out o') :=
      MulAction.mem_orbit_iff.mpr ⟨g⁻¹ * g', by rw [mul_smul, ← h', inv_smul_smul]⟩
    have hoo : o = o' := by
      have hsound := Quotient.sound (MulAction.orbitRel_apply.mpr hmem)
      rwa [Quotient.out_eq, Quotient.out_eq] at hsound
    subst hoo
    have hgg : g = g' := hfree h'
    subst hgg
    rfl
  let E := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
  -- Package the per-element cone-lintegral as `P`.
  set P : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} → ℝ≥0∞ :=
    fun a => ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
        (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K a.1) : ℂ)
          * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K) with hP
  -- For each orbit `o`, the per-element sum over the orbit collapses (helper -4)
  -- to the whole-space lintegral, which (helper -2) is `ofReal (N^{-Re t}) * M`.
  have step : ∀ o, (∑' g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ),
        P (E ⟨o, g⟩))
      = ENNReal.ofReal
          (mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re))
        * ∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) := by
    intro o
    have hPeq : ∀ g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ),
        P (E ⟨o, g⟩)
        = ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K
                ((coneUnitHom (K := K) g • y) * mixedEmbedding K (Quotient.out o).1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K) := by
      intro g
      have harg : ∀ y, y * mixedEmbedding K (E ⟨o, g⟩).1
          = (coneUnitHom (K := K) g • y) * mixedEmbedding K (Quotient.out o).1 := by
        intro y
        show y * mixedEmbedding K (((coneUnitHom (K := K) g : 𝓞 K) : K) * (Quotient.out o).1)
            = _
        rw [map_mul, NumberField.mixedEmbedding.unitSMul_smul]
        ring
      have hfun : (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K (E ⟨o, g⟩).1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t)
          = (fun y => (Theta.mixedGaussian K
                ((coneUnitHom (K := K) g • y) * mixedEmbedding K (Quotient.out o).1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) := by
        funext y; rw [harg y]
      rw [hP]
      simp only [hfun]
    rw [tsum_congr hPeq,
      tsum_unit_lintegral_enorm_cone_eq_lintegral_whole K (Quotient.out o).1 t,
      lintegral_enorm_mixedGaussian_mul_norm_cpow_eq K (Quotient.out o).2.2 t]
  -- Reindex `∑' a : S` over the free orbits, then collapse each orbit and pull `M`.
  rw [← Equiv.tsum_eq E P, ENNReal.tsum_sigma', tsum_congr step,
    ENNReal.tsum_mul_right, mul_comm]

/-- **Abstract bounded-fiber summability comparison.** If a real family `f` over
`ι` factors through a map `ψ : ι → κ` as `f i = c · h (ψ i)` with `c ≥ 0`, `h`
summable and nonnegative, and every fibre `ψ⁻¹ {k}` is finite with cardinality
bounded by a fixed `N`, then `f` is summable. (Each fibre contributes
`≤ N · c · h k`, and `∑ₖ h k < ∞`.) -/
theorem summable_of_bounded_fiber {ι : Type*} {κ : Type*}
    {f : ι → ℝ} {h : κ → ℝ} {ψ : ι → κ} {c : ℝ} {N : ℕ}
    (hf : ∀ i, f i = c * h (ψ i)) (hc : 0 ≤ c) (hh : Summable h)
    (hhnn : ∀ k, 0 ≤ h k) (hfin : ∀ k, Finite {i // ψ i = k})
    (hcard : ∀ k, Nat.card {i // ψ i = k} ≤ N) :
    Summable f := by
  have hfnn : ∀ i, 0 ≤ f i := fun i => by
    rw [hf i]; exact mul_nonneg hc (hhnn _)
  set f' : ι → ℝ≥0 := fun i => (f i).toNNReal with hf'
  have hcoe : ∀ i, (f' i : ℝ) = f i := fun i => Real.coe_toNNReal _ (hfnn i)
  have hofReal : ∀ i, ENNReal.ofReal (f i) = (f' i : ℝ≥0∞) := fun i => by
    rw [hf', ENNReal.ofReal]
  have htsum_h : (∑' k, ENNReal.ofReal (h k)) = ENNReal.ofReal (∑' k, h k) :=
    (ENNReal.ofReal_tsum_of_nonneg hhnn hh).symm
  -- Per-fibre bound: a constant summed over a fibre of card `≤ N`.
  have step3b : ∀ k, (∑' (i : {i // ψ i = k}), ENNReal.ofReal (h (ψ i.1)))
      ≤ (N : ℝ≥0∞) * ENNReal.ofReal (h k) := by
    intro k
    have hconst : ∀ (i : {i // ψ i = k}),
        ENNReal.ofReal (h (ψ i.1)) = ENNReal.ofReal (h k) := by
      rintro ⟨i, rfl⟩; rfl
    rw [tsum_congr hconst]
    haveI : Finite {i // ψ i = k} := hfin k
    rw [ENNReal.tsum_const]
    gcongr
    calc (ENat.card {i // ψ i = k} : ℝ≥0∞)
        = ((Nat.card {i // ψ i = k} : ℕ∞) : ℝ≥0∞) := by rw [ENat.card_eq_coe_natCard]
      _ ≤ ((N : ℕ∞) : ℝ≥0∞) := by rw [ENat.toENNReal_le]; exact_mod_cast hcard k
      _ = (N : ℝ≥0∞) := by rw [ENat.toENNReal_coe]
  have key : (∑' i, ENNReal.ofReal (f i)) ≠ ∞ := by
    have step2 : (∑' i, ENNReal.ofReal (f i))
        = ENNReal.ofReal c * ∑' i, ENNReal.ofReal (h (ψ i)) := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (fun i => by rw [hf i, ENNReal.ofReal_mul hc])
    have e1 : (∑' i, ENNReal.ofReal (h (ψ i)))
        = ∑' (p : Σ k, {i // ψ i = k}), ENNReal.ofReal (h (ψ p.2.1)) :=
      ((Equiv.sigmaFiberEquiv ψ).tsum_eq
        (fun i => ENNReal.ofReal (h (ψ i)))).symm
    have step3 : (∑' i, ENNReal.ofReal (h (ψ i)))
        = ∑' k, ∑' (i : {i // ψ i = k}), ENNReal.ofReal (h (ψ i.1)) := by
      rw [e1, ENNReal.tsum_sigma']
    have hbound : (∑' k, ∑' (i : {i // ψ i = k}), ENNReal.ofReal (h (ψ i.1)))
        ≤ (N : ℝ≥0∞) * ENNReal.ofReal (∑' k, h k) := by
      calc (∑' k, ∑' (i : {i // ψ i = k}), ENNReal.ofReal (h (ψ i.1)))
          ≤ ∑' k, (N : ℝ≥0∞) * ENNReal.ofReal (h k) := ENNReal.tsum_le_tsum step3b
        _ = (N : ℝ≥0∞) * ∑' k, ENNReal.ofReal (h k) := ENNReal.tsum_mul_left
        _ = (N : ℝ≥0∞) * ENNReal.ofReal (∑' k, h k) := by rw [htsum_h]
    rw [step2, step3]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine ne_top_of_le_ne_top ?_ hbound
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.ofReal_ne_top
  have hsummable' : Summable f' := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simp_rw [← hofReal]; exact key
  exact (NNReal.summable_coe.mpr hsummable').congr hcoe

variable {K} in
/-- **Norm identity** (the standard treatment, local replica of
`DedekindZeta.GammaIntegral.mixedEmbedding_norm_eq_absNorm_span`, which lives
downstream and is therefore not importable here): the archimedean Minkowski norm
of `σ b` equals the absolute norm of the principal ideal `(b)`. -/
theorem mixedEmbedding_norm_eq_absNorm_span_local (b : 𝓞 K) :
    mixedEmbedding.norm (mixedEmbedding K ((b : 𝓞 K) : K))
      = (Ideal.absNorm (Ideal.span {b}) : ℝ) := by
  rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs,
    Algebra.coe_norm_int, ← mixedEmbedding.norm_eq_norm]

/-- **Bounded-fibre injection for the orbit-indexed principal-ideal map.** With
`bfun` a choice of clear-denominator representatives `(bfun a : K) = (d:K)·a` and
`ψ o = (bfun (out o))`, each fibre `{o // ψ o = J}` injects into the finite
torsion group `torsion K`: two orbit representatives generating the same
principal ideal differ by a unit `u = ζ · coneUnitHom g` (Dirichlet,
`exist_unique_eq_mul_prod`); the free part `coneUnitHom g` keeps them in the same
orbit, so the residual torsion factor `ζ` determines the orbit. Hence the fibre
is finite with cardinality `≤ w_K = torsionOrder K`. -/
theorem orbitIdeal_fibre_aux (I : FractionalIdeal (𝓞 K)⁰ K)
    (bfun : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} → 𝓞 K)
    (hbfun : ∀ a, (bfun a : K) = ((I.den : 𝓞 K) : K) * a.1)
    (hd_ne : ((I.den : 𝓞 K) : K) ≠ 0)
    (ψ : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) → NonzeroIdeal K)
    (hψval : ∀ o, ((ψ o : NonzeroIdeal K) : Ideal (𝓞 K))
        = Ideal.span {bfun (Quotient.out o)})
    (J : NonzeroIdeal K) :
    Finite {o // ψ o = J}
      ∧ Nat.card {o // ψ o = J} ≤ NumberField.Units.torsionOrder K := by
  classical
  by_cases hne : Nonempty {o // ψ o = J}
  · obtain ⟨ostar⟩ := hne
    -- For each fibre element, the relating unit decomposes (Dirichlet) into a
    -- torsion factor `ζ` and a free part `coneUnitHom (ofAdd e)`.
    have hex : ∀ oo : {o // ψ o = J},
        ∃ ζ : NumberField.Units.torsion K,
          ∃ g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ),
            (Quotient.out ostar.1).1
              = ((ζ : (𝓞 K)ˣ) : K) * ((coneUnitHom (K := K) g : 𝓞 K) : K)
                  * (Quotient.out oo.1).1 := by
      intro oo
      have hoo : Ideal.span {bfun (Quotient.out oo.1)} = (J : Ideal (𝓞 K)) := by
        rw [← hψval oo.1]; exact congrArg Subtype.val oo.2
      have hostar : Ideal.span {bfun (Quotient.out ostar.1)} = (J : Ideal (𝓞 K)) := by
        rw [← hψval ostar.1]; exact congrArg Subtype.val ostar.2
      have hspan : Ideal.span {bfun (Quotient.out oo.1)}
          = Ideal.span {bfun (Quotient.out ostar.1)} := hoo.trans hostar.symm
      obtain ⟨u, hu_assoc⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
      -- Cast `bfun oo · u = bfun ostar` into `K` and cancel `d`.
      have hcastK : (bfun (Quotient.out oo.1) : K) * ((u : 𝓞 K) : K)
          = (bfun (Quotient.out ostar.1) : K) := by
        rw [← hu_assoc]; push_cast; ring
      rw [hbfun (Quotient.out oo.1), hbfun (Quotient.out ostar.1), mul_assoc] at hcastK
      have hcancel : (Quotient.out oo.1).1 * ((u : 𝓞 K) : K) = (Quotient.out ostar.1).1 :=
        mul_left_cancel₀ hd_ne hcastK
      -- Dirichlet decomposition of the unit `u`.
      obtain ⟨⟨ζ, ee⟩, hu_eq, -⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
      have hcuh : (coneUnitHom (K := K) (Multiplicative.ofAdd ee) : (𝓞 K)ˣ)
          = ∏ i, NumberField.Units.fundSystem K i ^ (ee i) := by
        simp [coneUnitHom]
      have hu_eq2 : u = (ζ : (𝓞 K)ˣ) * coneUnitHom (K := K) (Multiplicative.ofAdd ee) := by
        rw [hu_eq, ← hcuh]
      have hu_castK : ((u : 𝓞 K) : K)
          = ((ζ : (𝓞 K)ˣ) : K)
            * ((coneUnitHom (K := K) (Multiplicative.ofAdd ee) : 𝓞 K) : K) := by
        rw [hu_eq2]; push_cast; ring
      refine ⟨ζ, Multiplicative.ofAdd ee, ?_⟩
      rw [← hcancel, hu_castK]; ring
    choose ζfun gfun hζgfun using hex
    -- Injectivity of `oo ↦ ζfun oo` into `torsion K`.
    have hΦinj : Function.Injective ζfun := by
      intro x y hxy
      have heq := (hζgfun x).symm.trans (hζgfun y)
      rw [hxy] at heq
      rw [mul_assoc, mul_assoc] at heq
      have hζ0 : (((ζfun y : (𝓞 K)ˣ) : 𝓞 K) : K) ≠ 0 :=
        RingOfIntegers.coe_ne_zero_iff.mpr (Units.ne_zero _)
      have hcc : ((coneUnitHom (K := K) (gfun x) : 𝓞 K) : K) * (Quotient.out x.1).1
          = ((coneUnitHom (K := K) (gfun y) : 𝓞 K) : K) * (Quotient.out y.1).1 :=
        mul_left_cancel₀ hζ0 heq
      have hSeq : (gfun x • Quotient.out x.1 :
            {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0})
          = gfun y • Quotient.out y.1 := by
        apply Subtype.ext
        show ((coneUnitHom (K := K) (gfun x) : 𝓞 K) : K) * (Quotient.out x.1).1
            = ((coneUnitHom (K := K) (gfun y) : 𝓞 K) : K) * (Quotient.out y.1).1
        exact hcc
      have hmem : Quotient.out y.1 ∈ MulAction.orbit
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) (Quotient.out x.1) :=
        ⟨(gfun y)⁻¹ * gfun x, by
          show ((gfun y)⁻¹ * gfun x) • Quotient.out x.1 = Quotient.out y.1
          rw [mul_smul, hSeq, inv_smul_smul]⟩
      have hyx : y.1 = x.1 := by
        have hsound := Quotient.sound (MulAction.orbitRel_apply.mpr hmem)
        rwa [Quotient.out_eq, Quotient.out_eq] at hsound
      exact Subtype.ext hyx.symm
    refine ⟨Finite.of_injective ζfun hΦinj, ?_⟩
    calc Nat.card {o // ψ o = J}
        ≤ Nat.card (NumberField.Units.torsion K) :=
          Nat.card_le_card_of_injective ζfun hΦinj
      _ = NumberField.Units.torsionOrder K := rfl
  · -- Empty fibre.
    haveI : IsEmpty {o // ψ o = J} := not_nonempty_iff.mp hne
    exact ⟨inferInstance, by
      rw [Nat.card_eq_zero.mpr (Or.inl this)]; exact Nat.zero_le _⟩

/-- **Orbit-indexed principal-ideal representative with norm identity.** Clearing
denominators of `I` via `d := (I.den : 𝓞 K)`, each `G`-orbit `o` of the nonzero
elements of `I` has a principal-ideal representative `ψ o = (b₀) ∈ NonzeroIdeal K`
with `(b₀ : K) = (d : K)·a₀` (`a₀ = (Quotient.out o).1`), satisfying the norm
identity `N(σ a₀)^{-Re t} = N(σ d)^{Re t} · 𝔑(ψ o)^{-Re t}`. The map `ψ` is
finite-to-one with each fibre of cardinality `≤ w_K = Units.torsionOrder K`
(two reps generating the same principal ideal differ by a unit, hence by a
torsion factor modulo the free part `coneUnitHom`; `coneUnitHom_mem_torsion_iff`). -/
theorem exists_orbitIdeal_norm_eq (I : FractionalIdeal (𝓞 K)⁰ K) {t : ℂ} :
    ∃ ψ : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) → NonzeroIdeal K,
      (∀ o, mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)
          = mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)) ^ t.re
            * (Ideal.absNorm ((ψ o : NonzeroIdeal K) : Ideal (𝓞 K)) : ℝ) ^ (-t.re))
      ∧ (∀ J : NonzeroIdeal K, Finite {o // ψ o = J})
      ∧ (∀ J : NonzeroIdeal K,
          Nat.card {o // ψ o = J} ≤ NumberField.Units.torsionOrder K) := by
  classical
  -- `d := (I.den : 𝓞 K)` is nonzero, so clearing denominators is faithful.
  have hd_ne : ((I.den : 𝓞 K) : K) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero I.den)
  -- Clearing denominators: every nonzero `a ∈ I` has `d·a` integral
  -- (`FractionalIdeal.den_mul_self_eq_num`).
  have hden : ∀ a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
      ∃ b : 𝓞 K, (b : K) = ((I.den : 𝓞 K) : K) * a.1 := by
    intro a
    have hmem : I.den • a.1 ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← I.den_mul_self_eq_num]
      exact Submodule.smul_mem_pointwise_smul a.1 I.den _ a.2.1
    obtain ⟨b, -, hbeq⟩ := hmem
    refine ⟨b, ?_⟩
    rw [Algebra.linearMap_apply] at hbeq
    rw [show ((b : 𝓞 K) : K) = algebraMap (𝓞 K) K b from rfl, hbeq]
    simp [Submonoid.smul_def, Algebra.smul_def]
  choose bfun hbfun using hden
  -- The representatives are nonzero (`d ≠ 0`, `a ≠ 0`).
  have hbfun_ne : ∀ a, bfun a ≠ 0 := by
    intro a hzero
    have h := hbfun a
    rw [hzero, RingOfIntegers.coe_eq_algebraMap, map_zero] at h
    exact mul_ne_zero hd_ne a.2.2 h.symm
  -- The orbit-indexed principal ideal `ψ o = (bfun (out o))`.
  have hψ_ne : ∀ o : Quotient (MulAction.orbitRel
        (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
        {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
      Ideal.span {bfun (Quotient.out o)} ≠ 0 := by
    intro o
    simpa [Ideal.span_singleton_eq_bot] using hbfun_ne (Quotient.out o)
  let ψ : Quotient (MulAction.orbitRel
        (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
        {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) → NonzeroIdeal K :=
    fun o => ⟨Ideal.span {bfun (Quotient.out o)}, hψ_ne o⟩
  have hψval : ∀ o, ((ψ o : NonzeroIdeal K) : Ideal (𝓞 K))
      = Ideal.span {bfun (Quotient.out o)} := fun _ => rfl
  refine ⟨ψ, ?_, ?_, ?_⟩
  · -- Norm identity.
    intro o
    -- `𝔑((bfun (out o))) = N(σ d) · N(σ a₀)`.
    have key : (Ideal.absNorm (Ideal.span {bfun (Quotient.out o)}) : ℝ)
        = mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K))
          * mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) := by
      rw [← mixedEmbedding_norm_eq_absNorm_span_local (bfun (Quotient.out o)),
        hbfun (Quotient.out o)]
      simp only [mixedEmbedding.norm_eq_norm, map_mul]
    have hNd_nonneg : 0 ≤ mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)) := by
      rw [mixedEmbedding.norm_eq_norm]; positivity
    have hNd0 : mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)) ≠ 0 := by
      rw [mixedEmbedding.norm_eq_norm]
      exact_mod_cast abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hd_ne)
    have hNb_nonneg : (0 : ℝ)
        ≤ (Ideal.absNorm (Ideal.span {bfun (Quotient.out o)}) : ℝ) := Nat.cast_nonneg _
    have hNa : mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1)
        = (Ideal.absNorm (Ideal.span {bfun (Quotient.out o)}) : ℝ)
          * (mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)))⁻¹ := by
      rw [key, mul_comm (mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)))
          (mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1)),
        mul_assoc, mul_inv_cancel₀ hNd0, mul_one]
    rw [hψval, hNa, Real.mul_rpow hNb_nonneg (inv_nonneg.mpr hNd_nonneg),
      Real.inv_rpow hNd_nonneg, Real.rpow_neg hNd_nonneg, inv_inv, mul_comm]
  · -- Finite fibres: derived from the bounded-fibre injection below.
    intro J
    exact (orbitIdeal_fibre_aux K I bfun hbfun hd_ne ψ hψval J).1
  · -- Fibre cardinality bound `≤ w_K`.
    intro J
    exact (orbitIdeal_fibre_aux K I bfun hbfun hd_ne ψ hψval J).2

set_option maxHeartbeats 1000000 in
-- Higher heartbeat budget: the final `summable_of_bounded_fiber` application unifies a `Summable` goal over the orbit `Quotient` type, which is costly.
/-- **Summability of the orbit-indexed real norm-power family** (the genuine
`1 < Re t` convergence input for the fractional cone theta dominating series).
For `1 < t.re`, the nonnegative real family indexed by the `G`-orbits of the
nonzero elements of `I` (`G = Multiplicative (Fin (rank K) → ℤ)`, acting via
`coneFracSMul`) of `N(σ a₀)^{-Re t}` for orbit representatives `a₀` is summable.

Proof route: clear denominators of `I` via `d := (I.den : 𝓞 K)`
(`FractionalIdeal.den_mul_self_eq_num`), so for an orbit representative
`a₀ = (Quotient.out o).1 ∈ I` there is `b₀ : 𝓞 K`, `b₀ ≠ 0`, with
`(b₀ : K) = (d : K) * a₀`; by `mixedEmbedding.norm_eq_norm`, multiplicativity of
`Algebra.norm`, and the norm bridge `N(σ b) = 𝔑((b))`
(`mixedEmbedding_norm_eq_absNorm_span`, replicated locally),
`N(σ a₀)^{-Re t} = |N d|^{Re t} · 𝔑((b₀))^{-Re t}`. The map `o ↦ Ideal.span {b₀}`
sends the orbit index into `NonzeroIdeal K` with multiplicity bounded by the
finite torsion order `w_K = Units.torsionOrder K` (two reps generating the same
principal ideal differ by a unit, hence by a torsion factor modulo the free part
`coneUnitHom`; `coneUnitHom_mem_torsion_iff`). Comparison with the real family
`𝔑^{-Re t}` — summable as `summable_norm_iff.mpr (summable_absNorm_neg_cpow K
(s := t) ht)`, using `‖𝔑^{-t}‖ = 𝔑^{-Re t}` — then gives summability. -/
theorem summable_orbit_norm_neg_re
    (I : FractionalIdeal (𝓞 K)⁰ K) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun o : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) =>
        mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)) := by
  classical
  -- The genuine convergence content is packaged into two helper lemmas: the
  -- orbit principal-ideal representative with its norm identity and bounded
  -- finite fibres (`exists_orbitIdeal_norm_eq`), and the abstract bounded-fibre
  -- summability comparison (`summable_of_bounded_fiber`).
  obtain ⟨ψ, hval, hfin, hcard⟩ := exists_orbitIdeal_norm_eq K I (t := t)
  -- Summability of the real ideal-norm series `J ↦ 𝔑(J)^{-Re t}` for `1 < Re t`.
  have hh : Summable (fun J : NonzeroIdeal K =>
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-t.re)) := by
    have hc := summable_absNorm_neg_cpow K (s := t) ht
    refine (summable_norm_iff.mpr hc).congr (fun J => ?_)
    have hpos : 0 < Ideal.absNorm (J : Ideal (𝓞 K)) :=
      Nat.pos_of_ne_zero (fun hz => J.2 ((Ideal.absNorm_eq_zero_iff).mp hz))
    rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
  refine summable_of_bounded_fiber
    (c := mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)) ^ t.re)
    (h := fun J : NonzeroIdeal K => (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-t.re))
    (ψ := ψ) (N := NumberField.Units.torsionOrder K)
    hval ?_ hh ?_ hfin hcard
  · exact Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _
  · exact fun _ => Real.rpow_nonneg (by positivity) _

/-- **Finiteness of the orbit-indexed norm-power series** for the fractional cone
theta dominating series. For `1 < t.re`,
the `ℝ≥0∞`-valued series indexed by the `G`-orbits of the nonzero elements of `I`
(`G = Multiplicative (Fin (rank K) → ℤ)`, acting via `coneFracSMul`) of
`ofReal (N(σ a₀)^{-Re t})` for orbit representatives `a₀` is finite.

This is the genuine convergence threshold `Re t > 1`. Proof route:
clear denominators of `I` by `d : 𝓞 K`, `d ≠ 0` with `d • I ⊆ 𝓞 K`
(`FractionalIdeal.exists_eq_spanSingleton_mul`); for an orbit representative
`a₀ ∈ I`, `d·a₀ ∈ 𝓞 K` and by multiplicativity of the archimedean norm and the
norm bridge `N(σ b) = 𝔑((b))` (`mixedEmbedding_norm_eq_absNorm_span`, replicated
locally),
`N(σ a₀)^{-Re t} = |N d|^{Re t} · 𝔑((d·a₀))^{-Re t}`; the map
`o ↦ (d·a₀)` injects the orbit index (up to the finite torsion multiplicity
`w_K`) into `NonzeroIdeal K`, so the real series is summable by comparison with
the `Summable.of_norm` companion of `summable_absNorm_neg_cpow K (s := t) ht`,
and its `ENNReal.ofReal` tsum is `< ∞`. -/
theorem tsum_orbit_ofReal_norm_neg_re_ne_top
    (I : FractionalIdeal (𝓞 K)⁰ K) {t : ℂ} (ht : 1 < t.re) :
    (∑' o : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
        ENNReal.ofReal
          (mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)))
      ≠ ∞ := by
  -- Reduce the `ℝ≥0∞`-valued series to a nonnegative real `Summable` family:
  -- the summands are `ENNReal.ofReal` of `N(σ a₀)^{-Re t} ≥ 0`, so once the real
  -- family is summable, `ENNReal.ofReal_tsum_of_nonneg` collapses the `tsum` to
  -- `ENNReal.ofReal (∑' …)`, which is never `∞`. The genuine `1 < Re t`
  -- convergence input is `summable_orbit_norm_neg_re`.
  have hnn : ∀ o : Quotient (MulAction.orbitRel
        (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
        {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
      0 ≤ mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re) :=
    fun o => Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (summable_orbit_norm_neg_re K I ht)]
  exact ENNReal.ofReal_ne_top

/-- **Dominating finiteness for the fractional cone theta integrand**
(analytic core). For any fractional ideal `I` and
`1 < t.re`, the element-wise series (over the nonzero `a ∈ I`) of the cone
`lintegral`s of the `enorm` of the single shifted Minkowski Gaussian
`g(x·σ a)·N(x)^t` is finite.

This is the genuine convergence threshold (`Re t > 1`): grouping the `a` into
`𝓞ˣ`-orbits, each orbit's cone-lintegrals sum to the whole-space Mellin value
`𝔑((a))^{-Re t}·|I(Re t)|`, and `∑` over orbits converges by
`summable_absNorm_neg_cpow`. It mirrors the *integral*-ideal estimate
`GammaIntegral.tsum_lintegral_enorm_cone_mixedGaussian_ne_top`, but is needed here
(upstream of `GammaIntegral`) to feed the `Integrable` statement consumed by the
class-rescaling glue `dualIdeal_cone_integral_eq` in this module: the per-element
cone-Mellin estimate `GammaIntegral.mellin_mixedGaussian_mul_eq` and the
fundamental-cone collapse currently live *downstream* in `GammaIntegral`, which
`import`s this file, so they cannot be cited here and the estimate must be
re-established (or relocated) at this layer. -/
theorem tsum_lintegral_enorm_cone_mixedThetaKernel_summand_ne_top
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) (ht : 1 < t.re) :
    (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K a.1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K))
      ≠ ∞ := by
  -- Orbit-collapse reduction: the per-element series equals the base
  -- whole-space Gaussian Mellin `enorm`-lintegral `M` times the orbit-indexed
  -- norm-power series. `M ≠ ∞` (helper -3) and the orbit-indexed series is finite
  -- (the genuine `1 < Re t` convergence input), so the product is
  -- finite by `ENNReal.mul_ne_top`.
  rw [tsum_cone_lintegral_enorm_eq_mul_tsum_orbit K I t]
  exact ENNReal.mul_ne_top
    (lintegral_enorm_mixedGaussian_mul_norm_cpow_ne_top K ht)
    (tsum_orbit_ofReal_norm_neg_re_ne_top K I ht)

/-- **Integrability of the fractional theta cone integrand** for `1 < t.re`.
For any fractional ideal `I` and
`t : ℂ` with `1 < t.re`, the fundamental-cone indicator of the integrand
`y ↦ Θ(I, y)·N(y)^t` is `mixedMulHaar`-integrable.

This is the genuine analytic convergence of the cone Mellin integral. The
fundamental cone meets every archimedean-norm shell `N(y) ∈ (0, ∞)`; near
`N(y) → 0` the theta kernel diverges like `N(y)⁻¹` (the pole side of the
inversion law `Theta.mixedThetaKernel_inv_*`), so the radial Mellin integral
`∫ N^{t-2} dN` converges exactly when `Re t > 1`. The estimate is the same one
underlying the sum/integral interchange in the *integral* representative case
(`GammaIntegral.cone_integral_idealThetaKernel_eq_tsum`, Tonelli for the
nonnegative Gaussian dominated by `summable_absNorm_neg_cpow`); since
`Theta.idealThetaKernel K 𝔞 = Theta.mixedThetaKernel K (𝔞 : FractionalIdeal)`
(`Theta.idealThetaKernel_eq_mixed`) the bound transfers to coerced integral
ideals and, more generally, to any fractional ideal's lattice. -/
theorem integrable_indicator_mixedThetaKernel_mul_norm_cpow
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) (ht : 1 < t.re) :
    MeasureTheory.Integrable
      ((mixedEmbedding.fundamentalCone K).indicator
        (fun y => Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ t))
      (mixedMulHaar K) := by
  classical
  -- `K` is countable, hence so is the index set of the theta `∑'`; needed for
  -- `lintegral_tsum` below.
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  -- Measurability is already available; only `HasFiniteIntegral` remains.
  refine ⟨(aestronglyMeasurable_mixedThetaKernel_mul_norm_cpow K I t).indicator
    (mixedEmbedding.measurableSet_fundamentalCone K), ?_⟩
  -- Per-element cone-indicator integrand `F a`.
  set F : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}
      → mixedEmbedding.mixedSpace K → ℂ :=
    fun a x => (mixedEmbedding.fundamentalCone K).indicator
      (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K a.1) : ℂ)
        * (mixedEmbedding.norm y : ℂ) ^ t) x with hF
  -- Each `x ↦ ‖F a x‖ₑ` is measurable (enorm of a Borel indicator).
  have hFmeas : ∀ a, Measurable (fun x => ‖F a x‖ₑ) := by
    intro a
    refine Measurable.enorm ?_
    refine Measurable.indicator ?_ (mixedEmbedding.measurableSet_fundamentalCone K)
    refine Measurable.mul ?_ ?_
    · refine Complex.measurable_ofReal.comp ?_
      unfold Theta.mixedGaussian; fun_prop
    · exact (Complex.measurable_ofReal.comp
        (mixedEmbedding.continuous_norm K).measurable).pow_const t
  -- Pointwise: the enorm of the kernel-integrand cone indicator is dominated by
  -- the `∑'` of the per-element enorms (triangle inequality for `∑'`).
  have hbound : ∀ x,
      ‖(mixedEmbedding.fundamentalCone K).indicator
          (fun y => Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ
        ≤ ∑' a, ‖F a x‖ₑ := by
    intro x
    by_cases hx : x ∈ mixedEmbedding.fundamentalCone K
    · rw [Set.indicator_of_mem hx, Theta.mixedThetaKernel, ← tsum_mul_right]
      refine le_trans enorm_tsum_le_tsum_enorm (le_of_eq (tsum_congr (fun a => ?_)))
      simp only [hF, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; simp
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  calc ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
          (fun y => Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ
            ∂(mixedMulHaar K)
      ≤ ∫⁻ x, ∑' a, ‖F a x‖ₑ ∂(mixedMulHaar K) := MeasureTheory.lintegral_mono hbound
    _ = ∑' a, ∫⁻ x, ‖F a x‖ₑ ∂(mixedMulHaar K) :=
        MeasureTheory.lintegral_tsum (fun a => (hFmeas a).aemeasurable)
    _ < ∞ := (tsum_lintegral_enorm_cone_mixedThetaKernel_summand_ne_top K I t ht).lt_top


/-! ### About the omitted continuation / functional-equation layer

The raw cone integral `completedPartialZeta` is only used here on the convergence
strip `Re s > 1`. A faithful all-`s` functional equation would have to be stated
for a meromorphic continuation rather than for this raw Bochner integral (which
is undefined off its convergence range in the sense relevant to the analytic
argument). The upstream development had such continuation-facing material, but it
was pruned away from this repository because the sum-product proof only consumes
the strip-level pole/tail decomposition and the resulting residue inequality.
-/

/-! ## Agreement with Mathlib's `dedekindZeta` on `Re s > 1`

On the convergence strip `Re s > 1` the genuine completed object equals
`Z_∞(s) · ζ_K(s)` (the standard treatment). This is
`completedDedekindZeta_eq`, proved in `DedekindZeta/PerClass.lean` (it consumes
the per-class evaluation, whose proof needs the analytic identity in
`GammaIntegral.lean`, downstream of this module). -/

end

end DedekindZeta

/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: mathlib-initiative/sum_product at 80e4127a67742659d521466204c6d2d7e0ca2b3f.
- Formalization note: Lean 4.33.1 compatibility port with narrow imports for DedekindZeta.Statements.
- PROVENANCE-END
-/
