import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# A rational upper bound for Robin's zero constant

All finite calculations are rational kernel-checked calculations. The
infinite Euler constant is bounded using its proved upper harmonic sequence.
-/

namespace Robin1984

theorem robin_log_two_lower : (69314 / 100000 : Real) <= Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem robin_log_four_pi_lower : (253 / 100 : Real) <= Real.log (4 * Real.pi) := by
  have hSmall := Real.sum_range_le_log_div (x := (57 / 257 : Real)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hSmall
  have hArg : (8 : Real) * (157 / 100) <= 4 * Real.pi := by linarith [Real.pi_gt_d2]
  have hLog := Real.log_le_log (by norm_num : (0 : Real) < 8 * (157 / 100)) hArg
  rw [Real.log_mul (by norm_num : Not ((8 : Real) = 0))
    (by norm_num : Not ((157 / 100 : Real) = 0))] at hLog
  have hEight : Real.log (8 : Real) = 3 * Real.log 2 := by
    rw [show (8 : Real) = 2^3 by norm_num, Real.log_pow]
    norm_num
  rw [hEight] at hLog
  linarith [robin_log_two_lower]

set_option maxRecDepth 2048 in
theorem robin_harmonic_256_upper : (harmonic 256 : Real) <= (15311 / 2500 : Real) := by
  have hRat : harmonic 256 <= (15311 / 2500 : Rat) := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hCast : (harmonic 256 : Real) <= ((15311 / 2500 : Rat) : Real) :=
    Rat.cast_mono hRat
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hCast
  exact hCast

theorem robin_zero_constant_le_one_twentieth :
    Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) <= (1 / 20 : Real) := by
  have hGamma := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  change Real.eulerMascheroniConstant < (harmonic 256 : Real) - Real.log (256 : Real) at hGamma
  have hLog256 : Real.log (256 : Real) = 8 * Real.log 2 := by
    rw [show (256 : Real) = 2^8 by norm_num, Real.log_pow]
    norm_num
  rw [hLog256] at hGamma
  linarith [robin_harmonic_256_upper, robin_log_two_lower, robin_log_four_pi_lower]

end Robin1984
