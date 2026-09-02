/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.NumberTheory.Chebyshev

/-!
# Abel summation for the prime-log coefficient

This file defines the coefficient sequence whose partial sums are Chebyshev's
theta function and specializes Abel summation to that sequence.
-/

@[expose] public section

open Finset MeasureTheory

namespace Chebyshev

noncomputable section

/-- The logarithm of a natural number when it is prime, and zero otherwise. -/
noncomputable def primeLogCoeff (n : Nat) : Real :=
  if Nat.Prime n then Real.log (n : Real) else 0

/-- Partial sums of `primeLogCoeff` are exactly `Chebyshev.theta`. -/
theorem sum_primeLogCoeff_Icc_eq_theta (x : Real) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogCoeff n) = theta x := by
  rw [theta_eq_sum_Icc]
  simp [primeLogCoeff, Finset.sum_filter]

/-- Abel summation specialized to the prime-log coefficient. -/
theorem primeLogCoeff_abel
    {f : Real → Real} {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * primeLogCoeff k =
      f b * theta b - f a * theta a -
        ∫ t in Set.Ioc a b, deriv f t * theta t := by
  rw [sum_mul_eq_sub_sub_integral_mul primeLogCoeff ha hab hf_diff hf_int]
  rw [sum_primeLogCoeff_Icc_eq_theta b, sum_primeLogCoeff_Icc_eq_theta a]
  have hInt :
      ∫ t in Set.Ioc a b,
          deriv f t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogCoeff k) =
        ∫ t in Set.Ioc a b, deriv f t * theta t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t _ht
    change deriv f t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogCoeff k) =
      deriv f t * theta t
    rw [sum_primeLogCoeff_Icc_eq_theta t]
  rw [hInt]

end

end Chebyshev
