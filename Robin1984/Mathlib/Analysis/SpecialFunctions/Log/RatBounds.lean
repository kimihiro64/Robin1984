/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Rational certificates for logarithms

This file gives exact rational lower and upper bounds for the real logarithm
using finite truncations of the atanh series.
-/

@[expose] public section

namespace Rat

/-- The first `N` terms of the atanh-series lower bound for `log q`. -/
def logSeriesLower (q : Rat) (N : Nat) : Rat :=
  2 * Finset.sum (Finset.range N)
    (fun i => ((q - 1) / (q + 1)) ^ (2 * i + 1) / (2 * i + 1 : Nat))

/-- The atanh-series lower bound plus a geometric majorant for its tail. -/
def logSeriesUpper (q : Rat) (N : Nat) : Rat :=
  logSeriesLower q N +
    2 * ((q - 1) / (q + 1)) ^ (2 * N + 1) /
      (1 - ((q - 1) / (q + 1)) ^ 2)

/-- The rational lower certificate is at most the real logarithm. -/
theorem logSeriesLower_le_log {q : Rat} (hq : 1 ≤ q) (N : Nat) :
    (logSeriesLower q N : Real) ≤ Real.log (q : Real) := by
  have hqR : (1 : Real) ≤ q := by exact_mod_cast hq
  have hDen : (0 : Real) < (q : Real) + 1 := by linarith
  have hz0 : (0 : Real) ≤ ((q : Real) - 1) / ((q : Real) + 1) :=
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
  unfold logSeriesLower
  push_cast
  linarith

/-- The real logarithm is at most the rational upper certificate. -/
theorem log_le_logSeriesUpper {q : Rat} (hq : 1 ≤ q) (N : Nat) :
    Real.log (q : Real) ≤ (logSeriesUpper q N : Real) := by
  have hqR : (1 : Real) ≤ q := by exact_mod_cast hq
  have hDen : (0 : Real) < (q : Real) + 1 := by linarith
  have hz0 : (0 : Real) ≤ ((q : Real) - 1) / ((q : Real) + 1) :=
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
  unfold logSeriesUpper logSeriesLower
  push_cast
  rw [mul_div_assoc]
  linarith

end Rat
