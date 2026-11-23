import Mathlib.NumberTheory.LSeries.SumCoeff
import Robin1984.GRH.DedekindMertensAbel
import Robin1984.GRH.DedekindMertensEulerLog

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Dirichlet-series Abel summation for the shifted logarithm of Dedekind zeta.
- Formalization note: Shift the evaluation point by one to obtain the finite Mertens weights and the Mellin kernel.
- PROVENANCE-END
-/

/-!
# The Abelian integral of the actual Dedekind Mertens sum

Shift the Dirichlet series of the logarithm of zeta by one. Its new
coefficients are exactly those in the finite Mertens sum.
-/

open Asymptotics Filter MeasureTheory NumberField Set

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

noncomputable def dedekindMertensAbelCoeff (n : Nat) : Real :=
  mertensPrimePowerWeight (n : Real) * dedekindNormCoeff K n

theorem dedekindMertensAbelCoeff_nonneg (n : Nat) : 0 <= dedekindMertensAbelCoeff K n := by
  unfold dedekindMertensAbelCoeff mertensPrimePowerWeight
  by_cases hn : n = 0
  case pos => simp [hn]
  case neg =>
    have hN : (1 : Real) <= n := by exact_mod_cast Nat.pos_of_ne_zero hn
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hN)))
      (dedekindNormCoeff_nonneg K n)

theorem sum_dedekindMertensAbelCoeff_Icc (x : Real) :
    (Finset.Icc 1 (Nat.floor x)).sum (dedekindMertensAbelCoeff K) =
      dedekindMertensPrimePowerSum K x := by
  change _ = (Finset.range (Nat.floor x + 1)).sum (dedekindMertensAbelCoeff K)
  refine Finset.sum_subset (fun n hn => Finset.mem_range.mpr
    (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)) ?_
  intro n hn hNot
  have hN : n < 1 := lt_of_not_ge (fun h =>
    hNot (Finset.mem_Icc.mpr (And.intro h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))))
  unfold dedekindMertensAbelCoeff
  rw [dedekindNormCoeff_eq_zero_of_le_one K hN.le, mul_zero]

private theorem hasSum_dedekindMertensAbelCoeff {r : Real} (hr : 0 < r) :
    LSeriesHasSum (fun n : Nat => (dedekindMertensAbelCoeff K n : Complex))
      (r : Complex) (Real.log (dedekindZeta K ((1 + r : Real) : Complex)).re : Complex) := by
  let a := fun n : Nat => (dedekindMertensAbelCoeff K n : Complex)
  let b := fun n : Nat => (dedekindNormCoeff K n : Complex) / (Real.log (n : Real) : Complex)
  have hOne : (1 : Real) < 1 + r := lt_add_of_pos_right 1 hr
  have hrC : Not ((r : Complex) = 0) := Complex.ofReal_ne_zero.mpr hr.ne'
  have hsC : Not (((1 + r : Real) : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hOne).ne'
  have hTerm : LSeries.term a (r : Complex) = LSeries.term b ((1 + r : Real) : Complex) := by
    funext n
    rw [LSeries.term_of_ne_zero' hrC, LSeries.term_of_ne_zero' hsC]
    by_cases hn : n = 0
    case pos => simp [hn, a, b, dedekindMertensAbelCoeff, mertensPrimePowerWeight]
    case neg =>
      have hnC : Not ((n : Complex) = 0) := Nat.cast_ne_zero.mpr hn
      have hPower : (n : Complex) ^ ((1 + r : Real) : Complex) =
          (n : Complex) * (n : Complex) ^ (r : Complex) := by
        rw [Complex.ofReal_add, Complex.ofReal_one, Complex.cpow_add 1 _ hnC, Complex.cpow_one]
      rw [hPower]
      simp only [a, b, dedekindMertensAbelCoeff, mertensPrimePowerWeight,
        Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
        div_eq_mul_inv, mul_inv_rev]
      ring
  change HasSum (LSeries.term a (r : Complex)) _
  rw [hTerm]
  exact hasSum_dedekindMertensLogCoeff K hOne

private theorem normSum_dedekindMertensAbelCoeff_isBigO {r : Real} (hr : 0 < r) :
    (fun n : Nat => (Finset.Icc 1 n).sum (fun k => (dedekindMertensAbelCoeff K k : Complex)))
      =O[atTop] (fun n : Nat => (n : Real) ^ r) := by
  let a := dedekindMertensAbelCoeff K
  let b := fun k : Nat => a k / (k : Real) ^ r
  have hb (k : Nat) : 0 <= b k :=
    div_nonneg (dedekindMertensAbelCoeff_nonneg K k) (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hrC : Not ((r : Complex) = 0) := Complex.ofReal_ne_zero.mpr hr.ne'
  have hEq : LSeries.term (fun k : Nat => (a k : Complex)) (r : Complex) =
      fun k : Nat => (b k : Complex) := by
    funext k
    rw [LSeries.term_of_ne_zero' hrC]
    change (a k : Complex) / (k : Complex) ^ (r : Complex) =
      ((a k / (k : Real) ^ r : Real) : Complex)
    rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg k), Complex.ofReal_natCast]
  have hSum := (hasSum_dedekindMertensAbelCoeff K hr).summable
  change Summable (LSeries.term (fun k : Nat => (a k : Complex)) (r : Complex)) at hSum
  rw [hEq] at hSum
  have hReal := Complex.summable_ofReal.mp hSum
  refine IsBigO.of_bound (tsum b) ?_
  filter_upwards [eventually_ge_atTop (1 : Nat)] with n hn
  have hN : 0 <= (n : Real) ^ r := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hNormSum : (Finset.Icc 1 n).sum (fun k => (a k : Complex)) =
      (((Finset.Icc 1 n).sum a : Real) : Complex) := (map_sum Complex.ofRealHom _ _).symm
  change norm ((Finset.Icc 1 n).sum (fun k => (a k : Complex))) <= tsum b * norm ((n : Real) ^ r)
  rw [hNormSum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg (fun k _ => dedekindMertensAbelCoeff_nonneg K k)),
    Real.norm_of_nonneg hN]
  calc
    _ <= (Finset.Icc 1 n).sum (fun k => b k * (n : Real) ^ r) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 := (Finset.mem_Icc.mp hk).1
      have hk2 := (Finset.mem_Icc.mp hk).2
      have hk0 : 0 < (k : Real) := by exact_mod_cast (zero_lt_one.trans_le hk1)
      have hKn : (k : Real) <= n := by exact_mod_cast hk2
      calc
        a k = b k * (k : Real) ^ r := by
          unfold b
          field_simp [(Real.rpow_pos_of_pos hk0 r).ne']
        _ <= b k * (n : Real) ^ r := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hk0.le hKn hr.le) (hb k)
    _ = ((Finset.Icc 1 n).sum b) * (n : Real) ^ r := (Finset.sum_mul _ _ _).symm
    _ <= _ := mul_le_mul_of_nonneg_right (hReal.sum_le_tsum _ (fun k _ => hb k)) hN

/-- The actual logarithm of the Dedekind zeta function is the Abelian
integral of the finite prime-power Mertens sum. -/
theorem log_dedekindZeta_eq_integral_mertens {u : Real} (hu : 0 < u) :
    Real.log (dedekindZeta K ((1 + u : Real) : Complex)).re =
      u * integral (volume.restrict (Ioi (1 : Real)))
        (fun x => dedekindMertensPrimePowerSum K x * x ^ (-(u + 1))) := by
  let f := fun n : Nat => (dedekindMertensAbelCoeff K n : Complex)
  have hHalf : u / 2 < (u : Complex).re := by
    rw [Complex.ofReal_re]
    linarith only [hu]
  have hSum := hasSum_dedekindMertensAbelCoeff K hu
  have hAbel := LSeries_eq_mul_integral f (half_pos hu).le hHalf hSum.summable
    (normSum_dedekindMertensAbelCoeff_isBigO K (half_pos hu))
  have hLeft : LSeries f (u : Complex) =
      (Real.log (dedekindZeta K ((1 + u : Real) : Complex)).re : Complex) := hSum.tsum_eq
  rw [hLeft] at hAbel
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, <- integral_complex_ofReal]
  refine hAbel.trans ?_
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans (show 1 < x from hx)
  have hSumCast : (Finset.Icc 1 (Nat.floor x)).sum f =
      (dedekindMertensPrimePowerSum K x : Complex) := by
    rw [<- sum_dedekindMertensAbelCoeff_Icc]
    exact (map_sum Complex.ofRealHom _ _).symm
  change (Finset.Icc 1 (Nat.floor x)).sum f * (x : Complex) ^ (-(u + 1 : Complex)) =
    ((dedekindMertensPrimePowerSum K x * x ^ (-(u + 1)) : Real) : Complex)
  rw [hSumCast, Complex.ofReal_mul, Complex.ofReal_cpow hx0.le,
    Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_one]

end Robin1984.GRH
