import Robin1984.Finite.RobinFiniteStartupCATangent

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Explicit endpoint estimates for the common startup CA tangent

All transcendental comparisons in this module are reduced to rational Taylor
bounds for `Real.exp`.  They certify the two endpoints used by the concavity
theorem in `RobinFiniteStartupCATangent`.
-/

namespace Robin1984

noncomputable section

private theorem exp_one_lt_2719_div_1000 :
    Real.exp 1 < (2719 : Real) / 1000 := by
  refine lt_of_le_of_lt
    (Real.exp_bound' (x := (1 : Real)) (by norm_num) (by norm_num)
      (n := 9) (by norm_num)) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

private theorem exp_12_div_25_lt_1617_div_1000 :
    Real.exp ((12 : Real) / 25) < (1617 : Real) / 1000 := by
  refine lt_of_le_of_lt
    (Real.exp_bound' (x := (12 : Real) / 25) (by norm_num) (by norm_num)
      (n := 8) (by norm_num)) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

private theorem exp_3_div_5_lt_1823_div_1000 :
    Real.exp ((3 : Real) / 5) < (1823 : Real) / 1000 := by
  refine lt_of_le_of_lt
    (Real.exp_bound' (x := (3 : Real) / 5) (by norm_num) (by norm_num)
      (n := 9) (by norm_num)) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

private theorem exp_191_div_200_lt_13_div_5 :
    Real.exp ((191 : Real) / 200) < (13 : Real) / 5 := by
  refine lt_of_le_of_lt
    (Real.exp_bound' (x := (191 : Real) / 200) (by norm_num) (by norm_num)
      (n := 10) (by norm_num)) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]


theorem ca5040To55440Cutoff_lt_one_div_27 :
    ca5040To55440Cutoff < (1 : Real) / 27 := by
  rw [<- ca5040To55440Event_threshold_eq_cutoff]
  apply event_threshold_lt_one_div_nat_of_gainRatio_pow_lt_prime
    (e := ca5040To55440Event) (N := 27) (by norm_num)
  norm_num [ca5040To55440Event, Robin1984.layerEventOfPrime,
    Robin1984.eventGainRatio]


private theorem log_143_lt_five :
    Real.log 143 < 5 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : Real) < 143)]
  refine lt_of_lt_of_le ?_
    (Real.sum_le_exp_of_nonneg (by norm_num : (0 : Real) <= 5) 10)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]


theorem ca5040To55440Cutoff_mul_log_143_lt_five_div_27 :
    ca5040To55440Cutoff * Real.log 143 < (5 : Real) / 27 := by
  have hLogPos : 0 < Real.log (143 : Real) := Real.log_pos (by norm_num)
  calc
    ca5040To55440Cutoff * Real.log 143 <
        ((1 : Real) / 27) * Real.log 143 :=
      mul_lt_mul_of_pos_right ca5040To55440Cutoff_lt_one_div_27 hLogPos
    _ < ((1 : Real) / 27) * 5 := by
      exact mul_lt_mul_of_pos_left log_143_lt_five (by norm_num)
    _ = (5 : Real) / 27 := by ring

theorem sigmaOneNat_5040_eq_19344 :
    Robin1984.Core.sigmaOneNat 5040 = 19344 := by
  set_option maxRecDepth 100000 in
    decide

theorem abundancy_5040_eq_403_div_105 :
    abundancy 5040 = (403 : Real) / 105 := by
  unfold abundancy
  rw [sigmaOneNat_5040_eq_19344]
  norm_num

theorem log_abundancy_5040_lt_269_div_200 :
    Real.log (abundancy 5040) < (269 : Real) / 200 := by
  rw [abundancy_5040_eq_403_div_105]
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : Real) < 403 / 105)]
  refine lt_of_lt_of_le ?_
    (Real.sum_le_exp_of_nonneg (by norm_num : (0 : Real) <= 269 / 200) 11)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]


private theorem exp_337_div_25_lt_720720 :
    Real.exp ((337 : Real) / 25) < 720720 := by
  calc
    Real.exp ((337 : Real) / 25) =
        Real.exp 1 ^ 13 * Real.exp ((12 : Real) / 25) := by
      rw [show (337 : Real) / 25 = 13 * 1 + 12 / 25 by norm_num,
        Real.exp_add]
      congr 1
      simpa only [Nat.cast_ofNat, mul_one] using
        (Real.exp_nat_mul (1 : Real) 13)
    _ < ((2719 : Real) / 1000) ^ 13 * Real.exp ((12 : Real) / 25) := by
      gcongr
      exact exp_one_lt_2719_div_1000
    _ < ((2719 : Real) / 1000) ^ 13 * ((1617 : Real) / 1000) := by
      gcongr
      exact exp_12_div_25_lt_1617_div_1000
    _ < 720720 := by norm_num

private theorem exp_13_div_5_lt_337_div_25 :
    Real.exp ((13 : Real) / 5) < (337 : Real) / 25 := by
  calc
    Real.exp ((13 : Real) / 5) =
        Real.exp 1 ^ 2 * Real.exp ((3 : Real) / 5) := by
      rw [show (13 : Real) / 5 = 2 * 1 + 3 / 5 by norm_num,
        Real.exp_add]
      congr 1
      simpa only [Nat.cast_ofNat, mul_one] using
        (Real.exp_nat_mul (1 : Real) 2)
    _ < ((2719 : Real) / 1000) ^ 2 * Real.exp ((3 : Real) / 5) := by
      gcongr
      exact exp_one_lt_2719_div_1000
    _ < ((2719 : Real) / 1000) ^ 2 * ((1823 : Real) / 1000) := by
      gcongr
      exact exp_3_div_5_lt_1823_div_1000
    _ < (337 : Real) / 25 := by norm_num

theorem log_log_log_720720_gt_191_div_200 :
    (191 : Real) / 200 <
      Real.log (Real.log (Real.log (720720 : Real))) := by
  have hLog :
      (337 : Real) / 25 < Real.log (720720 : Real) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : Real) < 720720)]
    exact exp_337_div_25_lt_720720
  have hLogPos : 0 < Real.log (720720 : Real) := by positivity
  have hLogLog :
      (13 : Real) / 5 < Real.log (Real.log (720720 : Real)) := by
    rw [Real.lt_log_iff_exp_lt hLogPos]
    exact exp_13_div_5_lt_337_div_25.trans hLog
  have hLogLogPos : 0 < Real.log (Real.log (720720 : Real)) := by positivity
  rw [Real.lt_log_iff_exp_lt hLogLogPos]
  exact exp_191_div_200_lt_13_div_5.trans hLogLog

set_option maxRecDepth 10000 in
theorem seventy_two_div_125_lt_eulerMascheroniConstant :
    (72 : Real) / 125 < Real.eulerMascheroniConstant := by
  have hSeqLower :
      (72 : Real) / 125 < Real.eulerMascheroniSeq 1000 := by
    unfold Real.eulerMascheroniSeq
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    have hLogUpper :
        Real.log 1001 < (harmonic 1000 : Real) - 72 / 125 := by
      rw [Real.log_lt_iff_lt_exp (by positivity : (0 : Real) < 1001)]
      refine lt_of_lt_of_le ?_
        (Real.sum_le_exp_of_nonneg
          (by
            norm_num [harmonic] :
            (0 : Real) <= (harmonic 1000 : Real) - 72 / 125)
          25)
      norm_num [harmonic, Finset.sum_range_succ, Nat.factorial_succ]
    linarith
  exact hSeqLower.trans
    (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 1000)


theorem ca5040RobinLogTangentGapAtLog_720720_pos :
    0 < ca5040RobinLogTangentGapAtLog
      (Real.log (720720 : Real)) := by
  have hLogRatio :
      Real.log (720720 : Real) - Real.log (5040 : Real) = Real.log 143 := by
    rw [show (720720 : Real) = 5040 * 143 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  unfold ca5040RobinLogTangentGapAtLog
  rw [hLogRatio]
  linarith [seventy_two_div_125_lt_eulerMascheroniConstant,
    log_log_log_720720_gt_191_div_200,
    log_abundancy_5040_lt_269_div_200,
    ca5040To55440Cutoff_mul_log_143_lt_five_div_27]


end

end Robin1984
