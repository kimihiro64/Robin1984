import Robin1984.Equivalence.ExplicitLogBounds
import Robin1984.Equivalence.PrimePowerFirstWeightBounds
/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# Uniform scalar data above logarithmic height 74500

For every real `H >= 74500`, these lemmas control the logarithmic factors and
fractional powers appearing in the analytic error terms. The module also
records the rational square-root and fourth-root bounds needed to compare all
coefficients on one common scale.
-/

namespace Robin1984

noncomputable section

/-- Algebraic proof of the decreasing logarithmic power ratio after its maximum. -/
theorem robin_log_mul_rpow_neg_le
    {b x r : Real} (hb : 1 < b) (hbx : b <= x) (hr : 0 < r)
    (hStart : 1 <= r * Real.log b) :
    Real.log x * x^(-r) <= Real.log b * b^(-r) := by
  have hbPos : 0 < b := by linarith
  have hxPos : 0 < x := by linarith
  let t : Real := (x / b)^r
  have ht : 1 <= t := Real.one_le_rpow ((one_le_div hbPos).mpr hbx) hr.le
  have htPos : 0 < t := by linarith
  have hLogT : Real.log t = r * (Real.log x - Real.log b) := by
    dsimp [t]
    rw [Real.log_rpow (div_pos hxPos hbPos), Real.log_div hxPos.ne' hbPos.ne']
  have hLog := Real.log_le_sub_one_of_pos htPos
  have hFirst : Real.log x <= Real.log b * t := by nlinarith
  have hEq : t * x^(-r) = b^(-r) := by
    dsimp [t]
    rw [Real.div_rpow hxPos.le hbPos.le, Real.rpow_neg hxPos.le, Real.rpow_neg hbPos.le]
    have hXPow : Not (x^r = 0) := (Real.rpow_pos_of_pos hxPos r).ne'
    field_simp
  have h := mul_le_mul_of_nonneg_right hFirst (Real.rpow_nonneg hxPos.le (-r))
  calc
    _ <= (Real.log b * t) * x^(-r) := h
    _ = _ := by rw [mul_assoc, hEq]

theorem robin_74500_power_sixth :
    (74500 : Real)^(-(1 / 6 : Real)) <= (1549 / 10000 : Real) := by
  have h := robin_rpow_neg_div_le_of_pow (x := (74500 : Real)) (a := 1) (d := 6)
    (b := (1549 / 10000 : Real)) (by norm_num) (by norm_num) (by omega) (by norm_num)
  norm_num at h
  exact h

theorem robin_log_times_sixth_power_bound {H : Real} (hH : 74500 <= H) :
    Real.log H * H^(-(1 / 6 : Real)) <= (87 / 50 : Real) := by
  have hMono := robin_log_mul_rpow_neg_le (b := (74500 : Real)) (by norm_num) hH
    (r := (1 / 6 : Real)) (by norm_num)
    (by nlinarith [robin_log_74500_bounds.1])
  have hProduct : Real.log (74500 : Real) * (74500 : Real)^(-(1 / 6 : Real)) <=
      (1123 / 100 : Real) * (1549 / 10000 : Real) := by
    exact mul_le_mul robin_log_74500_bounds.2 robin_74500_power_sixth
      (Real.rpow_nonneg (by norm_num : (0 : Real) <= 74500) _)
      (by norm_num : (0 : Real) <= 1123 / 100)
  nlinarith

theorem robin_large_height_log_and_powers {H : Real} (hH : 74500 <= H) :
    And ((56 / 5 : Real) <= Real.log H)
      (And (H^(-(1 / 4 : Real)) <= (61 / 1000 : Real))
        (H^(-(1 / 2 : Real)) <= (1 / 272 : Real))) := by
  have hHPos : 0 < H := by linarith
  have hLog := Real.log_le_log (by norm_num : (0 : Real) < 74500) hH
  have hQuarter := robin_rpow_neg_div_le_of_pow (a := 1) (d := 4) (b := (61 / 1000 : Real))
    hHPos (by norm_num) (by omega) (by norm_num; linarith)
  have hHalf := robin_rpow_neg_div_le_of_pow (a := 1) (d := 2) (b := (1 / 272 : Real))
    hHPos (by norm_num) (by omega) (by norm_num; linarith)
  norm_num at hQuarter hHalf
  exact And.intro (robin_log_74500_bounds.1.trans hLog) (And.intro hQuarter hHalf)

theorem robin_sqrt_two_lower : (7071 / 5000 : Real) <= Real.sqrt 2 := by
  have hSquare := Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
  have hNonneg := Real.sqrt_nonneg (2 : Real)
  nlinarith

theorem robin_fourth_root_two_upper : (2 : Real)^(1 / 4 : Real) <= (119 / 100 : Real) := by
  apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0 : Real) < 4)).mp
  rw [<- Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
  norm_num [Real.rpow_natCast]

end

end Robin1984
