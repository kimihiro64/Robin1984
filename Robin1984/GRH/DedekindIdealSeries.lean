import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Robin1984.GRH.DedekindSeries

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The norm-fiber reindexing in the Formal Frontier sum_product Dedekind zeta development at 80e4127a67742659d521466204c6d2d7e0ca2b3f, and the Dirichlet class number estimate.
- Formalization note: The norm-count summability is reused to prove absolute summability over the actual nonzero ideals.
- PROVENANCE-END
-/

/-!
# Dedekind zeta as an absolutely convergent sum over ideals

The fiber at zero is empty among nonzero ideals. Each other norm fiber
has exactly the cardinality counted by the Mathlib Dirichlet coefficient.
-/

open NumberField

namespace Robin1984.GRH

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The nonzero integral ideals of a number field. -/
abbrev NonzeroIntegralIdeal :=
  {a : Ideal (RingOfIntegers K) // Not (a = 0)}

private noncomputable abbrev idealNorm (a : NonzeroIntegralIdeal K) := Ideal.absNorm a.val

private abbrev normFiber (n : Nat) := {a : NonzeroIntegralIdeal K // idealNorm K a = n}

private theorem normFiber_finite (n : Nat) : Finite (normFiber K n) := by
  let _ : Finite {a : Ideal (RingOfIntegers K) // Ideal.absNorm a = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  refine Finite.of_injective
    (f := fun x : normFiber K n =>
      (Subtype.mk x.val.val x.property : {a : Ideal (RingOfIntegers K) // Ideal.absNorm a = n})) ?_
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun t : {a : Ideal (RingOfIntegers K) // Ideal.absNorm a = n} => t.val) h

private theorem normFiber_zero_empty : IsEmpty (normFiber K 0) := by
  refine IsEmpty.mk (fun a => ?_)
  exact a.val.property (Ideal.absNorm_eq_zero_iff.mp a.property)

private noncomputable def normFiberEquiv (n : Nat) (hn : Not (n = 0)) :
    Equiv (normFiber K n) {a : Ideal (RingOfIntegers K) // Ideal.absNorm a = n} where
  toFun a := Subtype.mk a.val.val a.property
  invFun a := Subtype.mk (Subtype.mk a.val (fun ha =>
    hn (a.property.symm.trans (Ideal.absNorm_eq_zero_iff.mpr ha)))) a.property
  left_inv _a := Subtype.ext (Subtype.ext rfl)
  right_inv _a := Subtype.ext rfl

private theorem tsum_const_normFiber {A : Type*} [AddCommMonoid A] [TopologicalSpace A] [T2Space A]
    (n : Nat) (hn : Not (n = 0)) (z : A) :
    tsum (fun _ : normFiber K n => z) = SMul.smul (idealNormCount K n) z := by
  let _ : Finite (normFiber K n) := normFiber_finite K n
  let _ : Fintype (normFiber K n) := Fintype.ofFinite _
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, <- Nat.card_eq_fintype_card]
  exact congrArg (fun c : Nat => SMul.smul c z) (Nat.card_congr (normFiberEquiv K n hn))

private noncomputable def idealSeriesTerm (s : Complex) (a : NonzeroIntegralIdeal K) : Complex :=
  (idealNorm K a : Complex) ^ (-s)

private theorem normFiber_term_sum (s : Complex) (n : Nat) :
    tsum (fun a : normFiber K n => idealSeriesTerm K s a.val) =
      LSeries.term (fun k => (idealNormCount K k : Complex)) s n := by
  by_cases hn : n = 0
  case pos =>
    subst n
    let _ : IsEmpty (normFiber K 0) := normFiber_zero_empty K
    simp only [tsum_empty, LSeries.term_zero]
  case neg =>
    have hTerm (a : normFiber K n) : idealSeriesTerm K s a.val = (n : Complex) ^ (-s) := by
      unfold idealSeriesTerm
      rw [a.property]
    rw [tsum_congr hTerm, tsum_const_normFiber K n hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_neg, div_eq_mul_inv]
    exact nsmul_eq_mul _ _

private theorem normFiber_norm_term_sum (s : Complex) (n : Nat) :
    tsum (fun a : normFiber K n => norm (idealSeriesTerm K s a.val)) =
      norm (LSeries.term (fun k => (idealNormCount K k : Complex)) s n) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    let _ : IsEmpty (normFiber K 0) := normFiber_zero_empty K
    simp only [tsum_empty, LSeries.term_zero, norm_zero]
  case neg =>
    have hTerm (a : normFiber K n) : norm (idealSeriesTerm K s a.val) =
        norm ((n : Complex) ^ (-s)) := by
      unfold idealSeriesTerm
      rw [a.property]
    rw [tsum_congr hTerm, tsum_const_normFiber K n hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_neg, div_eq_mul_inv, norm_mul, Complex.norm_natCast]
    exact nsmul_eq_mul _ _

/-- The ideal-indexed Dedekind series is absolutely summable for real part greater than one. -/
theorem summable_norm_dedekindIdealTerm {s : Complex} (hs : 1 < s.re) :
    Summable (fun a : NonzeroIntegralIdeal K => norm ((Ideal.absNorm a.val : Complex) ^ (-s))) := by
  let ix := Equiv.sigmaFiberEquiv (idealNorm K)
  change Summable (fun a : NonzeroIntegralIdeal K => norm (idealSeriesTerm K s a))
  refine (ix.summable_iff).mp ?_
  change Summable (fun p : Sigma (normFiber K) => norm (idealSeriesTerm K s p.2.val))
  rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
  refine And.intro (fun n => ?hFiber) ?hOuter
  case hFiber =>
    let _ : Finite (normFiber K n) := normFiber_finite K n
    exact Summable.of_finite
  case hOuter =>
    have h := summable_norm_iff.mpr (dedekindZeta_series_summable K hs)
    exact h.congr (fun n => (normFiber_norm_term_sum K s n).symm)

/-- The Dedekind zeta Dirichlet series is the sum over nonzero integral ideals. -/
theorem dedekindZeta_eq_tsum_idealNorm {s : Complex} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s =
      tsum (fun a : NonzeroIntegralIdeal K => (Ideal.absNorm a.val : Complex) ^ (-s)) := by
  let ix := Equiv.sigmaFiberEquiv (idealNorm K)
  have h : Summable (idealSeriesTerm K s) :=
    Summable.of_norm (summable_norm_dedekindIdealTerm K hs)
  have hSigma : Summable (fun p : Sigma (normFiber K) => idealSeriesTerm K s p.2.val) :=
    (ix.summable_iff).mpr h
  change tsum (LSeries.term (fun k => (idealNormCount K k : Complex)) s) = tsum (idealSeriesTerm K s)
  rw [<- ix.tsum_eq (idealSeriesTerm K s)]
  change _ = tsum (fun p : Sigma (normFiber K) => idealSeriesTerm K s p.2.val)
  rw [hSigma.tsum_sigma' (fun n => by
    let _ : Finite (normFiber K n) := normFiber_finite K n
    exact Summable.of_finite)]
  exact tsum_congr (fun n => (normFiber_term_sum K s n).symm)

end Robin1984.GRH
