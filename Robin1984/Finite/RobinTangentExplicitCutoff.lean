import Robin1984.Arithmetic.Definitions
import Robin1984.Arithmetic.RobinBounds
import Robin1984.Equivalence.RobinTangentCoverageEquivalence
import Robin1984.Finite.RobinTangentStartup
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Explicit eventual endpoint for constructive tangent coverage

The endpoint `720720` is large enough for the Robin frontier cutoff to lie
strictly below the certified `5040 -> 55440` CA transition parameter.
-/

namespace Robin1984

noncomputable section

theorem rational_336_div_25_lt_log_720720 :
    (336 : Real) / 25 < Real.log (720720 : Real) := by
  have hPowNat : 2 ^ 97 < (720720 : Nat) ^ 5 := by
    norm_num
  have hPowReal : (2 : Real) ^ 97 < (720720 : Real) ^ 5 := by
    exact_mod_cast hPowNat
  have hLog :=
    Real.log_lt_log (pow_pos (by norm_num : (0 : Real) < 2) 97) hPowReal
  have hExpanded :
      (97 : Real) * Real.log 2 <
        5 * Real.log (720720 : Real) := by
    simpa [Real.log_pow] using hLog
  have hRational :
      5 * ((336 : Real) / 25) < (97 : Real) * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  nlinarith

theorem rational_129_div_50_lt_log_336_div_25 :
    (129 : Real) / 50 < Real.log ((336 : Real) / 25) := by
  have hPow :
      (2 : Real) ^ 67 < ((336 : Real) / 25) ^ 18 := by
    norm_num
  have hLog :=
    Real.log_lt_log (pow_pos (by norm_num : (0 : Real) < 2) 67) hPow
  have hExpanded :
      (67 : Real) * Real.log 2 <
        18 * Real.log ((336 : Real) / 25) := by
    simpa [Real.log_pow] using hLog
  have hRational :
      18 * ((129 : Real) / 50) < (67 : Real) * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  nlinarith

theorem rational_129_div_50_lt_log_log_720720 :
    (129 : Real) / 50 <
      Real.log (Real.log (720720 : Real)) := by
  have hApos : (0 : Real) < (336 : Real) / 25 := by norm_num
  have hMono :
      Real.log ((336 : Real) / 25) <
        Real.log (Real.log (720720 : Real)) :=
    Real.log_lt_log hApos rational_336_div_25_lt_log_720720
  exact lt_trans rational_129_div_50_lt_log_336_div_25 hMono

theorem thirty_four_lt_log_mul_log_log_720720 :
    (34 : Real) <
      Real.log (720720 : Real) *
        Real.log (Real.log (720720 : Real)) := by
  have hProduct :
      ((336 : Real) / 25) * ((129 : Real) / 50) <
        Real.log (720720 : Real) *
          Real.log (Real.log (720720 : Real)) :=
    mul_lt_mul rational_336_div_25_lt_log_720720
      (le_of_lt rational_129_div_50_lt_log_log_720720)
      (by norm_num : (0 : Real) < 129 / 50)
      (le_of_lt (lt_trans (by norm_num : (0 : Real) < 336 / 25)
        rational_336_div_25_lt_log_720720))
  have hThirtyFour :
      (34 : Real) < ((336 : Real) / 25) * ((129 : Real) / 50) := by
    norm_num
  exact lt_trans hThirtyFour hProduct

theorem robinFrontierCutoff_720720_lt_one_div_34 :
    robinFrontierCutoff 720720 < (1 : Real) / 34 := by
  have hInv :=
    one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 34)
      thirty_four_lt_log_mul_log_log_720720
  unfold robinFrontierCutoff
  simpa [one_div] using hInv

theorem robinFrontierCutoff_720720_lt_ca5040To55440Cutoff :
    robinFrontierCutoff 720720 < ca5040To55440Cutoff :=
  lt_trans robinFrontierCutoff_720720_lt_one_div_34
    ca5040To55440Cutoff_lower

theorem robinFrontierCutoff_lt_ca5040To55440Cutoff_of_720720_le
    {n : Nat} (hn : 720720 <= n) :
    robinFrontierCutoff n < ca5040To55440Cutoff := by
  have hAnti :
      robinFrontierCutoff n <= robinFrontierCutoff 720720 :=
    robinFrontierCutoff_antitone_above_cutoff
      (by norm_num : 5040 < 720720) hn
  exact lt_of_le_of_lt hAnti
    robinFrontierCutoff_720720_lt_ca5040To55440Cutoff

/-- Fully explicit R1 coverage equivalence: only the finite interval
`5040 < n < 720720` remains on the startup side. -/
theorem nativeRobinInequalityAll_iff_tangentCoverage_720720 :
    Robin1984.Core.NativeRobinInequalityAll <->
      RobinFiniteTangentCACoverage 720720 :=
  nativeRobinInequalityAll_iff_finiteTangentCACoverage
    (fun n hn =>
      robinFrontierCutoff_lt_ca5040To55440Cutoff_of_720720_le
        (n := n) hn)

end

end Robin1984
