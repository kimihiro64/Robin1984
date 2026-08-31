import Robin1984.Finite.RobinFiniteStartupCATangentEndpoints
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# The remaining common-CA startup tangent from 7560

The lower endpoint is sharpened from `10080` to `7560`.  This leaves the
finite arithmetic interval `5041 <= n < 7560`, where the exact factor
certificate uses the sharp bound `35 * sigma n <= 127 * n`.
-/

namespace Robin1984

noncomputable section

private theorem exp_one_lt_27183_div_10000 :
    Real.exp 1 < (27183 : Real) / 10000 := by
  refine lt_of_le_of_lt
    (Real.exp_bound' (x := (1 : Real)) (by norm_num) (by norm_num)
      (n := 12) (by norm_num)) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

private theorem exp_93_div_100_lt_507_div_200 :
    Real.exp ((93 : Real) / 100) < (507 : Real) / 200 := by
  refine lt_of_le_of_lt
    (Real.exp_bound' (x := (93 : Real) / 100) (by norm_num) (by norm_num)
      (n := 16) (by norm_num)) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

private theorem exp_3917_div_5000_lt_2189_div_1000 :
    Real.exp ((3917 : Real) / 5000) < (2189 : Real) / 1000 := by
  refine lt_of_le_of_lt
    (Real.exp_bound' (x := (3917 : Real) / 5000) (by norm_num) (by norm_num)
      (n := 16) (by norm_num)) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

private theorem exp_189_div_1000_lt_12081_div_10000 :
    Real.exp ((189 : Real) / 1000) < (12081 : Real) / 10000 := by
  refine lt_of_le_of_lt
    (Real.exp_bound' (x := (189 : Real) / 1000) (by norm_num) (by norm_num)
      (n := 10) (by norm_num)) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

private theorem exp_2189_div_1000_lt_893_div_100 :
    Real.exp ((2189 : Real) / 1000) < (893 : Real) / 100 := by
  calc
    Real.exp ((2189 : Real) / 1000) =
        Real.exp 1 ^ 2 * Real.exp ((189 : Real) / 1000) := by
      rw [show (2189 : Real) / 1000 = 2 * 1 + 189 / 1000 by norm_num,
        Real.exp_add]
      congr 1
      simpa only [Nat.cast_ofNat, mul_one] using
        (Real.exp_nat_mul (1 : Real) 2)
    _ < ((27183 : Real) / 10000) ^ 2 *
        Real.exp ((189 : Real) / 1000) := by
      gcongr
      exact exp_one_lt_27183_div_10000
    _ < ((27183 : Real) / 10000) ^ 2 *
        ((12081 : Real) / 10000) := by
      gcongr
      exact exp_189_div_1000_lt_12081_div_10000
    _ < (893 : Real) / 100 := by norm_num

private theorem exp_893_div_100_lt_7560 :
    Real.exp ((893 : Real) / 100) < 7560 := by
  calc
    Real.exp ((893 : Real) / 100) =
        Real.exp 1 ^ 8 * Real.exp ((93 : Real) / 100) := by
      rw [show (893 : Real) / 100 = 8 * 1 + 93 / 100 by norm_num,
        Real.exp_add]
      congr 1
      simpa only [Nat.cast_ofNat, mul_one] using
        (Real.exp_nat_mul (1 : Real) 8)
    _ < ((27183 : Real) / 10000) ^ 8 *
        Real.exp ((93 : Real) / 100) := by
      gcongr
      exact exp_one_lt_27183_div_10000
    _ < ((27183 : Real) / 10000) ^ 8 * ((507 : Real) / 200) := by
      gcongr
      exact exp_93_div_100_lt_507_div_200
    _ < 7560 := by norm_num

private theorem exp_3_div_50_lt_531_div_500 :
    Real.exp ((3 : Real) / 50) < (531 : Real) / 500 := by
  refine lt_of_le_of_lt
    (Real.exp_bound' (x := (3 : Real) / 50) (by norm_num) (by norm_num)
      (n := 8) (by norm_num)) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

private theorem exp_103_div_50_lt_eight :
    Real.exp ((103 : Real) / 50) < 8 := by
  calc
    Real.exp ((103 : Real) / 50) =
        Real.exp 1 ^ 2 * Real.exp ((3 : Real) / 50) := by
      rw [show (103 : Real) / 50 = 2 * 1 + 3 / 50 by norm_num,
        Real.exp_add]
      congr 1
      simpa only [Nat.cast_ofNat, mul_one] using
        (Real.exp_nat_mul (1 : Real) 2)
    _ < ((27183 : Real) / 10000) ^ 2 *
        Real.exp ((3 : Real) / 50) := by
      gcongr
      exact exp_one_lt_27183_div_10000
    _ < ((27183 : Real) / 10000) ^ 2 * ((531 : Real) / 500) := by
      gcongr
      exact exp_3_div_50_lt_531_div_500
    _ < 8 := by norm_num

private theorem exp_eight_lt_5041 :
    Real.exp 8 < 5041 := by
  calc
    Real.exp 8 = Real.exp 1 ^ 8 := by
      simpa only [Nat.cast_ofNat, mul_one] using
        (Real.exp_nat_mul (1 : Real) 8)
    _ < ((27183 : Real) / 10000) ^ 8 := by
      gcongr
      exact exp_one_lt_27183_div_10000
    _ < 5041 := by norm_num

private theorem log_three_halves_lt_203_div_500 :
    Real.log ((3 : Real) / 2) < (203 : Real) / 500 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : Real) < 3 / 2)]
  refine lt_of_lt_of_le ?_
    (Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : Real) <= 203 / 500) 6)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

theorem ca5040To55440Cutoff_mul_log_three_halves_lt_203_div_13500 :
    ca5040To55440Cutoff * Real.log ((3 : Real) / 2) <
      (203 : Real) / 13500 := by
  have hLogPos : 0 < Real.log ((3 : Real) / 2) :=
    Real.log_pos (by norm_num)
  calc
    ca5040To55440Cutoff * Real.log ((3 : Real) / 2) <
        ((1 : Real) / 27) * Real.log ((3 : Real) / 2) :=
      mul_lt_mul_of_pos_right ca5040To55440Cutoff_lt_one_div_27 hLogPos
    _ < ((1 : Real) / 27) * ((203 : Real) / 500) := by
      exact mul_lt_mul_of_pos_left log_three_halves_lt_203_div_500
        (by norm_num)
    _ = (203 : Real) / 13500 := by ring

set_option maxRecDepth 30000 in
theorem five_hundred_seventy_seven_div_1000_lt_eulerMascheroniConstant :
    (577 : Real) / 1000 < Real.eulerMascheroniConstant := by
  have hSeqLower :
      (577 : Real) / 1000 < Real.eulerMascheroniSeq 3000 := by
    unfold Real.eulerMascheroniSeq
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    have hLogUpper :
        Real.log 3001 < (harmonic 3000 : Real) - 577 / 1000 := by
      rw [Real.log_lt_iff_lt_exp (by positivity : (0 : Real) < 3001)]
      refine lt_of_lt_of_le ?_
        (Real.sum_le_exp_of_nonneg
          (by
            norm_num [harmonic] :
            (0 : Real) <= (harmonic 3000 : Real) - 577 / 1000)
          28)
      norm_num [harmonic, Finset.sum_range_succ, Nat.factorial_succ]
    linarith
  exact hSeqLower.trans
    (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 3000)

theorem log_log_log_7560_gt_3917_div_5000 :
    (3917 : Real) / 5000 <
      Real.log (Real.log (Real.log (7560 : Real))) := by
  have hLog : (893 : Real) / 100 < Real.log (7560 : Real) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : Real) < 7560)]
    exact exp_893_div_100_lt_7560
  have hLogPos : 0 < Real.log (7560 : Real) := by positivity
  have hLogLog :
      (2189 : Real) / 1000 < Real.log (Real.log (7560 : Real)) := by
    rw [Real.lt_log_iff_exp_lt hLogPos]
    exact exp_2189_div_1000_lt_893_div_100.trans hLog
  have hLogLogPos : 0 < Real.log (Real.log (7560 : Real)) := by
    positivity
  rw [Real.lt_log_iff_exp_lt hLogLogPos]
  exact exp_3917_div_5000_lt_2189_div_1000.trans hLogLog

theorem ca5040RobinLogTangentGapAtLog_7560_pos :
    0 < ca5040RobinLogTangentGapAtLog
      (Real.log (7560 : Real)) := by
  have hLogRatio :
      Real.log (7560 : Real) - Real.log (5040 : Real) =
        Real.log ((3 : Real) / 2) := by
    rw [show (7560 : Real) = 5040 * (3 / 2) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  unfold ca5040RobinLogTangentGapAtLog
  rw [hLogRatio]
  linarith [five_hundred_seventy_seven_div_1000_lt_eulerMascheroniConstant,
    log_log_log_7560_gt_3917_div_5000,
    log_abundancy_5040_lt_269_div_200,
    ca5040To55440Cutoff_mul_log_three_halves_lt_203_div_13500]

/-- The common CA tangent covers every startup integer from 7560 onward. -/
theorem nativeRobinInequality_startup_from_7560
    {n : Nat} (hLower : 7560 <= n) (hUpper : n < 720720) :
    Robin1984.Core.NativeRobinInequality n := by
  apply nativeRobinInequality_of_commonStartupTangentEndpoints
    (L := 7560) (U := 720720)
  . norm_num
  . norm_num
  . exact hLower
  . omega
  . exact ca5040RobinLogTangentGapAtLog_7560_pos
  . exact ca5040RobinLogTangentGapAtLog_720720_pos

theorem exp_eulerMascheroniConstant_gt_177_div_100 :
    (177 : Real) / 100 < Real.exp Real.eulerMascheroniConstant := by
  have hTaylor :
      (177 : Real) / 100 < Real.exp ((72 : Real) / 125) := by
    refine lt_of_lt_of_le ?_
      (Real.sum_le_exp_of_nonneg
        (by norm_num : (0 : Real) <= 72 / 125) 7)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  exact hTaylor.trans
    (Real.exp_lt_exp.mpr seventy_two_div_125_lt_eulerMascheroniConstant)

theorem one_hundred_three_div_50_lt_log_log_of_5041_le
    {n : Nat} (hLower : 5041 <= n) :
    (103 : Real) / 50 < Real.log (Real.log (n : Real)) := by
  have hLog5041 : (8 : Real) < Real.log (5041 : Real) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : Real) < 5041)]
    exact exp_eight_lt_5041
  have hLog5041Pos : 0 < Real.log (5041 : Real) := by positivity
  have hFixed :
      (103 : Real) / 50 < Real.log (Real.log (5041 : Real)) := by
    rw [Real.lt_log_iff_exp_lt hLog5041Pos]
    exact exp_103_div_50_lt_eight.trans hLog5041
  have hCast : (5041 : Real) <= (n : Real) := by exact_mod_cast hLower
  have hLogMono :
      Real.log (5041 : Real) <= Real.log (n : Real) :=
    Real.log_le_log (by norm_num) hCast
  have hLogLogMono :
      Real.log (Real.log (5041 : Real)) <=
        Real.log (Real.log (n : Real)) :=
    Real.log_le_log hLog5041Pos hLogMono
  exact hFixed.trans_le hLogLogMono

/-- The exact rational divisor-sum envelope closes Robin on the remaining
finite block. -/
theorem nativeRobinInequality_of_sigmaOneNat_le_127_div_35
    {n : Nat} (hLower : 5041 <= n)
    (hSigma : 35 * Robin1984.Core.sigmaOneNat n <= 127 * n) :
    Robin1984.Core.NativeRobinInequality n := by
  have hn : 0 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hSigmaCast :
      (35 : Real) * Robin1984.Core.sigmaOneNat n <=
        127 * (n : Real) := by
    exact_mod_cast hSigma
  have hSigmaLinear :
      (Robin1984.Core.sigmaOneNat n : Real) <=
        ((127 : Real) / 35) * n := by
    nlinarith
  have hAbundancy : abundancy n <= (127 : Real) / 35 := by
    unfold abundancy
    calc
      (Robin1984.Core.sigmaOneNat n : Real) / n <=
          (((127 : Real) / 35) * n) / n :=
        div_le_div_of_nonneg_right hSigmaLinear hnReal.le
      _ = (127 : Real) / 35 := by field_simp [hnReal.ne']
  have hExp := exp_eulerMascheroniConstant_gt_177_div_100
  have hLogLog := one_hundred_three_div_50_lt_log_log_of_5041_le hLower
  have hProduct :
      ((177 : Real) / 100) * ((103 : Real) / 50) <
        Real.exp Real.eulerMascheroniConstant *
          Real.log (Real.log (n : Real)) := by
    calc
      ((177 : Real) / 100) * ((103 : Real) / 50) <
          Real.exp Real.eulerMascheroniConstant * ((103 : Real) / 50) :=
        mul_lt_mul_of_pos_right hExp (by norm_num)
      _ < Real.exp Real.eulerMascheroniConstant *
          Real.log (Real.log (n : Real)) :=
        mul_lt_mul_of_pos_left hLogLog (Real.exp_pos _)
  have hBound : (127 : Real) / 35 < robinBoundRatio n := by
    unfold robinBoundRatio
    exact (by norm_num : (127 : Real) / 35 <
      (177 / 100) * (103 / 50)).trans hProduct
  exact (nativeRobinInequality_iff_abundancy_lt_bound hn).mpr
    (hAbundancy.trans_lt hBound)

end

end Robin1984
