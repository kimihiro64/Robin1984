import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Rational logarithm certificates for the proved finite Robin range

These bounds use exact rational arithmetic. No floating-point evaluation is
part of the proof. Dyadic brackets allow the same small certificate to bound
the logarithm of a product with arbitrarily many digits.
-/

namespace Robin1984

def robinLogLower (q : Rat) (N : Nat) : Rat :=
  2 * Finset.sum (Finset.range N)
    (fun i => ((q - 1) / (q + 1))^(2 * i + 1) / (2 * i + 1 : Nat))

def robinLogUpper (q : Rat) (N : Nat) : Rat :=
  robinLogLower q N +
    2 * ((q - 1) / (q + 1))^(2 * N + 1) /
      (1 - ((q - 1) / (q + 1))^2)

theorem robinLogLower_le_log {q : Rat} (hq : 1 <= q) (N : Nat) :
    (robinLogLower q N : Real) <= Real.log (q : Real) := by
  have hqR : (1 : Real) <= q := by exact_mod_cast hq
  have hDen : (0 : Real) < (q : Real) + 1 := by linarith
  have hz0 : (0 : Real) <= ((q : Real) - 1) / ((q : Real) + 1) :=
    div_nonneg (by linarith) hDen.le
  have hz1 : ((q : Real) - 1) / ((q : Real) + 1) < 1 := by
    apply (div_lt_one hDen).mpr
    linarith
  have hRatio :
      (1 + ((q : Real) - 1) / ((q : Real) + 1)) /
        (1 - ((q : Real) - 1) / ((q : Real) + 1)) = (q : Real) := by
    field_simp
    ring
  have h := Real.sum_range_le_log_div hz0 hz1 N
  rw [hRatio] at h
  unfold robinLogLower
  push_cast
  linarith

theorem log_le_robinLogUpper {q : Rat} (hq : 1 <= q) (N : Nat) :
    Real.log (q : Real) <= (robinLogUpper q N : Real) := by
  have hqR : (1 : Real) <= q := by exact_mod_cast hq
  have hDen : (0 : Real) < (q : Real) + 1 := by linarith
  have hz0 : (0 : Real) <= ((q : Real) - 1) / ((q : Real) + 1) :=
    div_nonneg (by linarith) hDen.le
  have hz1 : ((q : Real) - 1) / ((q : Real) + 1) < 1 := by
    apply (div_lt_one hDen).mpr
    linarith
  have hRatio :
      (1 + ((q : Real) - 1) / ((q : Real) + 1)) /
        (1 - ((q : Real) - 1) / ((q : Real) + 1)) = (q : Real) := by
    field_simp
    ring
  have h := Real.log_div_le_sum_range_add hz0 hz1 N
  rw [hRatio] at h
  unfold robinLogUpper robinLogLower
  push_cast
  rw [mul_div_assoc]
  linarith

theorem robin_log_two_precise_bounds :
    And ((693147180559945309 / 1000000000000000000 : Real) <= Real.log 2)
      (Real.log 2 <= (693147180559945310 / 1000000000000000000 : Real)) := by
  have hLow := robinLogLower_le_log (q := 2) (by norm_num) 20
  have hHigh := log_le_robinLogUpper (q := 2) (by norm_num) 20
  norm_num [robinLogLower, robinLogUpper, Finset.sum_range_succ] at hLow hHigh
  constructor <;> linarith

theorem robin_log_bounds_of_dyadic_bracket
    {x : Real} {q r : Rat} (k N : Nat)
    (hq : 1 <= q) (hr : 1 <= r)
    (hLower : (2 : Real)^k * (q : Real) <= x)
    (hUpper : x <= (2 : Real)^k * (r : Real)) :
    And
      ((k : Real) * (693147180559945309 / 1000000000000000000) +
        (robinLogLower q N : Real) <= Real.log x)
      (Real.log x <=
        (k : Real) * (693147180559945310 / 1000000000000000000) +
          (robinLogUpper r N : Real)) := by
  have hqR : (0 : Real) < (q : Real) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) hq)
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) hr)
  have hBase : (0 : Real) < (2 : Real)^k := pow_pos (by norm_num) k
  have hx : 0 < x := (mul_pos hBase hqR).trans_le hLower
  have hL := Real.log_le_log (mul_pos hBase hqR) hLower
  have hU := Real.log_le_log hx hUpper
  rw [Real.log_mul hBase.ne' hqR.ne', Real.log_pow] at hL
  rw [Real.log_mul hBase.ne' hrR.ne', Real.log_pow] at hU
  have hTwoL := mul_le_mul_of_nonneg_left robin_log_two_precise_bounds.1 (Nat.cast_nonneg k : (0 : Real) <= k)
  have hTwoU := mul_le_mul_of_nonneg_left robin_log_two_precise_bounds.2 (Nat.cast_nonneg k : (0 : Real) <= k)
  constructor <;> linarith [robinLogLower_le_log hq N, log_le_robinLogUpper hr N]

end Robin1984
