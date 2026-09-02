import Robin1984.Mathlib.Analysis.SpecialFunctions.Log.RatBounds

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Rational logarithm certificates for the proved finite Robin range

The generic atanh-series bounds are maintained in the Mathlib candidate layer.
This module preserves the project API and proves the Robin-specific dyadic
constants and brackets.
-/

namespace Robin1984

/-- Compatibility alias for the generic rational logarithm lower bound. -/
abbrev robinLogLower : Rat -> Nat -> Rat := Rat.logSeriesLower

/-- Compatibility alias for the generic rational logarithm upper bound. -/
abbrev robinLogUpper : Rat -> Nat -> Rat := Rat.logSeriesUpper

/-- Compatibility theorem for the generic rational lower certificate. -/
theorem robinLogLower_le_log {q : Rat} (hq : 1 <= q) (N : Nat) :
    (robinLogLower q N : Real) <= Real.log (q : Real) :=
  Rat.logSeriesLower_le_log hq N

/-- Compatibility theorem for the generic rational upper certificate. -/
theorem log_le_robinLogUpper {q : Rat} (hq : 1 <= q) (N : Nat) :
    Real.log (q : Real) <= (robinLogUpper q N : Real) :=
  Rat.log_le_logSeriesUpper hq N

theorem robin_log_two_precise_bounds :
    And ((693147180559945309 / 1000000000000000000 : Real) <= Real.log 2)
      (Real.log 2 <= (693147180559945310 / 1000000000000000000 : Real)) := by
  have hLow := robinLogLower_le_log (q := 2) (by norm_num) 20
  have hHigh := log_le_robinLogUpper (q := 2) (by norm_num) 20
  norm_num [robinLogLower, robinLogUpper, Rat.logSeriesLower,
    Rat.logSeriesUpper, Finset.sum_range_succ] at hLow hHigh
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
  have hqR : (0 : Real) < (q : Real) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) hq)
  have hrR : (0 : Real) < (r : Real) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) hr)
  have hBase : (0 : Real) < (2 : Real)^k := pow_pos (by norm_num) k
  have hx : 0 < x := (mul_pos hBase hqR).trans_le hLower
  have hL := Real.log_le_log (mul_pos hBase hqR) hLower
  have hU := Real.log_le_log hx hUpper
  rw [Real.log_mul hBase.ne' hqR.ne', Real.log_pow] at hL
  rw [Real.log_mul hBase.ne' hrR.ne', Real.log_pow] at hU
  have hTwoL := mul_le_mul_of_nonneg_left robin_log_two_precise_bounds.1
    (Nat.cast_nonneg k : (0 : Real) <= k)
  have hTwoU := mul_le_mul_of_nonneg_left robin_log_two_precise_bounds.2
    (Nat.cast_nonneg k : (0 : Real) <= k)
  constructor <;>
    linarith [robinLogLower_le_log hq N, log_le_robinLogUpper hr N]

end Robin1984
