import Robin1984.NicolasLandau.ZeroConstantBound

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# Rational logarithm bounds for the explicit large-height estimate

This module proves the coarse rational enclosures for `log 2`, `log 10`,
`log 100000`, `log 4`, and `log (2 * pi)` used by later scalar comparisons.
All transcendental inputs are discharged by proved Mathlib inequalities and
exact rational arithmetic.
-/

namespace Robin1984

theorem robin_log_two_upper : Real.log 2 <= (69315 / 100000 : Real) := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem robin_log_ten_bounds :
    And ((23 / 10 : Real) <= Real.log 10) (Real.log 10 <= (288 / 125 : Real)) := by
  have hLow := Real.sum_range_le_log_div (x := (1 / 9 : Real)) (by norm_num) (by norm_num) 2
  have hHigh := Real.log_div_le_sum_range_add (x := (1 / 9 : Real)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hLow hHigh
  have hTen : Real.log (10 : Real) = 3 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (10 : Real) = 2^3 * (5 / 4) by norm_num,
      Real.log_mul (by norm_num : Not ((2 : Real)^3 = 0))
        (by norm_num : Not ((5 / 4 : Real) = 0)), Real.log_pow]
    norm_num
  constructor <;> linarith [robin_log_two_lower, robin_log_two_upper]

theorem robin_log_hundred_thousand_bounds :
    And ((23 / 2 : Real) <= Real.log 100000) (Real.log 100000 <= (288 / 25 : Real)) := by
  have hEq : Real.log (100000 : Real) = 5 * Real.log 10 := by
    rw [show (100000 : Real) = 10^5 by norm_num, Real.log_pow]
    norm_num
  constructor <;> linarith [robin_log_ten_bounds.1, robin_log_ten_bounds.2]

theorem robin_log_four_upper : Real.log 4 <= (7 / 5 : Real) := by
  have hEq : Real.log (4 : Real) = 2 * Real.log 2 := by
    rw [show (4 : Real) = 2^2 by norm_num, Real.log_pow]
    norm_num
  linarith [robin_log_two_upper]

theorem robin_log_two_pi_upper : Real.log (2 * Real.pi) <= (3 : Real) := by
  have h := Real.log_le_log (mul_pos (by norm_num) Real.pi_pos)
    (show 2 * Real.pi <= (8 : Real) by linarith [Real.pi_lt_four])
  have hEight : Real.log (8 : Real) = 3 * Real.log 2 := by
    rw [show (8 : Real) = 2^3 by norm_num, Real.log_pow]
    norm_num
  linarith [robin_log_two_upper]

end Robin1984
