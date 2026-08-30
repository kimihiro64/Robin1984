import Robin1984.Finite.FiniteLogCertificate
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecificLimits.Basic

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# A rational lower bound for Euler's constant

The trapezoidal correction gives a monotone lower sequence with error of
order 1/n^2, so a small exact harmonic sum suffices for finite Robin bounds.
-/

namespace Robin1984

open Filter Topology

theorem robin_log_step_trapezoid {x : Real} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x <= (1 / x + 1 / (x + 1)) / 2 := by
  have hz0 : (0 : Real) <= 1 / (2 * x + 1) := by positivity
  have hz1 : 1 / (2 * x + 1) < (1 : Real) := by
    apply (div_lt_one (by positivity)).mpr
    linarith
  have h := Real.log_div_le_sum_range_add hz0 hz1 0
  simp only [Finset.range_zero, Finset.sum_empty, Nat.mul_zero,
    pow_one, zero_add] at h
  have hRatio : (1 + 1 / (2 * x + 1)) / (1 - 1 / (2 * x + 1)) = (x + 1) / x := by
    field_simp
    ring
  have hTail : 2 * (1 / (2 * x + 1) / (1 - (1 / (2 * x + 1))^2)) =
      (1 / x + 1 / (x + 1)) / 2 := by
    have hDen : 1 - (1 / (2 * x + 1))^2 = 4 * x * (x + 1) / (2 * x + 1)^2 := by
      field_simp
      ring
    rw [hDen]
    field_simp
    ring
  rw [hRatio, Real.log_div (by positivity) hx.ne'] at h
  linarith

noncomputable def robinEulerLowerSeq (n : Nat) : Real :=
  (harmonic (n + 1) : Real) - Real.log (n + 1 : Real) - 1 / (2 * (n + 1 : Real))

theorem robinEulerLowerSeq_monotone : Monotone robinEulerLowerSeq := by
  apply monotone_nat_of_le_succ
  intro n
  have h := robin_log_step_trapezoid (x := (n : Real) + 1) (by positivity)
  unfold robinEulerLowerSeq
  rw [harmonic_succ (n + 1)]
  push_cast
  have hHalf1 : 1 / (2 * ((n : Real) + 1)) = (1 / ((n : Real) + 1)) / 2 := by field_simp
  have hHalf2 : 1 / (2 * ((n : Real) + 1 + 1)) = (1 / ((n : Real) + 1 + 1)) / 2 := by field_simp
  rw [hHalf1, hHalf2]
  simp only [one_div] at h
  simp only [one_div]
  linarith

theorem robinEulerLowerSeq_tendsto :
    Tendsto robinEulerLowerSeq atTop (nhds Real.eulerMascheroniConstant) := by
  have hMain := (tendsto_add_atTop_iff_nat 1).2 Real.tendsto_harmonic_sub_log
  have hInv : Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hTail := hInv.div_const 2
  have h := hMain.sub hTail
  simp only [zero_div, sub_zero] at h
  convert h using 1
  ext n
  simp only [robinEulerLowerSeq, Nat.cast_add, Nat.cast_one]
  congr 1
  field_simp

theorem robinEulerLowerSeq_le (n : Nat) :
    robinEulerLowerSeq n <= Real.eulerMascheroniConstant :=
  robinEulerLowerSeq_monotone.ge_of_tendsto robinEulerLowerSeq_tendsto n

theorem robin_euler_constant_lower :
    (57721 / 100000 : Real) <= Real.eulerMascheroniConstant := by
  have h := robinEulerLowerSeq_le 255
  have hLog : Real.log (256 : Real) = 8 * Real.log 2 := by
    rw [show (256 : Real) = 2^8 by norm_num, Real.log_pow]
    norm_num
  unfold robinEulerLowerSeq at h
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h
  rw [hLog] at h
  have hHarm : (61243449 / 10000000 : Real) <= (harmonic 256 : Real) := by
    norm_num [harmonic]
  linarith [robin_log_two_precise_bounds.2]

end Robin1984
