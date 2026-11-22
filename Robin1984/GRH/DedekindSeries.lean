import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Ideal counting in the Dirichlet class number formula and partial summation of an absolutely convergent Dirichlet series.
- Formalization note: The ideal-count coefficient estimate supplies the initial Mellin identity for the actual Mathlib Dedekind zeta function.
- PROVENANCE-END
-/

/-!
# The initial Mellin representation of Dedekind zeta

Summing the norm fibers counts ideals of bounded norm. The resulting linear
growth justifies partial summation on the initial half-plane of absolute
convergence.
-/

open Asymptotics Filter Ideal MeasureTheory

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

/-- The number of integral ideals of a specified norm. -/
noncomputable def idealNormCount (n : Nat) : Nat :=
  Nat.card {a : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm a = n}

private theorem sum_idealNormCount_eq_card (n : Nat) :
    (Finset.Icc 0 n).sum (idealNormCount K) =
      Nat.card {a : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm a <= n} := by
  unfold idealNormCount
  rw [<- Finset.card_preimage_eq_sum_card_image_eq (fun k _ =>
    finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

private theorem idealNormCount_growth :
    Asymptotics.IsBigO atTop
      (fun n : Nat => (Finset.Icc 1 n).sum (fun k => (idealNormCount K k : Real)))
      (fun n => (n : Real) ^ (1 : Real)) := by
  have hNat : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hLimit : Tendsto
      (fun n : Nat => (Finset.Icc 0 n).sum (fun k => (idealNormCount K k : Real)) /
        (n : Real) ^ (1 : Real)) atTop (nhds (NumberField.dedekindZeta_residue K)) := by
    refine ((NumberField.Ideal.tendsto_norm_le_div_atTop K).comp hNat).congr (fun n => ?_)
    simp only [Function.comp_apply, Nat.cast_le, Real.rpow_one, <- Nat.cast_sum,
      sum_idealNormCount_eq_card]
  refine (Asymptotics.isBigO_of_le _ (fun n => ?_)).trans
    (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow hLimit)
  have hSmall : 0 <= (Finset.Icc 1 n).sum (fun k => (idealNormCount K k : Real)) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hLarge : 0 <= (Finset.Icc 0 n).sum (fun k => (idealNormCount K k : Real)) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  rw [Real.norm_of_nonneg hSmall, Real.norm_of_nonneg hLarge]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => Finset.mem_Icc.mpr (And.intro (Nat.zero_le i) (Finset.mem_Icc.mp hi).2))
    (fun _ _ _ => Nat.cast_nonneg _)

/-- The norm-count Dirichlet series converges absolutely on the initial half-plane. -/
theorem dedekindZeta_series_summable {s : Complex} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (idealNormCount K n : Complex)) s := by
  simpa only [Complex.ofReal_natCast] using
    (LSeriesSummable_of_sum_norm_bigO_and_nonneg (idealNormCount_growth K)
      (fun _ => Nat.cast_nonneg _) zero_le_one hs)

/-- Partial summation of the Dedekind zeta Dirichlet series. -/
theorem dedekindZeta_eq_integral_normCounts {s : Complex} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s =
      s * MeasureTheory.integral (volume.restrict (Set.Ioi (1 : Real)))
        (fun t : Real =>
          (Finset.Icc 1 (Nat.floor t)).sum (fun n => (idealNormCount K n : Complex)) *
            (t : Complex) ^ (-(s + 1))) := by
  change LSeries (fun n => (idealNormCount K n : Complex)) s = _
  simpa only [Complex.ofReal_natCast] using
    (LSeries_eq_mul_integral_of_nonneg (fun n => (idealNormCount K n : Real))
      zero_le_one hs (idealNormCount_growth K) (fun _ => Nat.cast_nonneg _))

end Robin1984.GRH
