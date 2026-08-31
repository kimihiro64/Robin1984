import Robin1984.Equivalence.PrimePowerFirstWeightBounds
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 analytic implication supplies the surrounding mathematical target.
- Formalization note: The exact coefficient normalization, explicit cutoff choices, and proof interfaces in this module are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Explicit complete second-weight tails above 366

These estimates supply the prime-square Abel integral. All root families and
their arithmetic errors are included before comparing scalar coefficients.
-/

namespace Robin1984

noncomputable section

theorem robin_log_ge_five {x : Real} (hx : 366 <= x) : 5 <= Real.log x := by
  have h : Real.log ((2 : Real)^8) <= Real.log x :=
    Real.log_le_log (by positivity) (by norm_num; linarith)
  rw [Real.log_pow] at h
  have hTwo := robin_log_two_lower
  norm_num at h
  linarith

theorem robin_root_error_upper_log_five
    {n k : Nat} (hn : 1 <= n) (hk : 2 <= k) {x : Real} (hx : 366 <= x) :
    Inv.inv (k : Real) * robinPsiWeightedErrorScalar (k * n) (x^(Inv.inv (k : Real))) <=
      (1 / 20 : Real) * x^((1 / 2 : Real) * Inv.inv (k : Real) - n) *
        Inv.inv (Real.log x) *
          (((k * n : Nat) : Real) + (k : Real) / 5 + 4 * (k : Real)^2 /
            (((2 * (k * n) - 1 : Nat) : Real) * 25)) := by
  have hxOne : 1 < x := by linarith
  have hLog := robin_log_ge_five hx
  have hLogPos := Real.log_pos hxOne
  have hq : Inv.inv (Real.log x) <= (1 / 5 : Real) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 5) hLog
  have hqNonneg : 0 <= Inv.inv (Real.log x) := inv_nonneg.mpr hLogPos.le
  have hkn : 1 <= k * n := by nlinarith
  have hOddNat : 0 < 2 * (k * n) - 1 := by omega
  have hOdd : (0 : Real) < ((2 * (k * n) - 1 : Nat) : Real) := by exact_mod_cast hOddNat
  have hBracket : ((k * n : Nat) : Real) + (k : Real) * Inv.inv (Real.log x) +
      4 * (k : Real)^2 * Inv.inv (((2 * (k * n) - 1 : Nat) : Real) * (Real.log x)^2) <=
      ((k * n : Nat) : Real) + (k : Real) / 5 + 4 * (k : Real)^2 /
        (((2 * (k * n) - 1 : Nat) : Real) * 25) := by
    rw [mul_inv, <- inv_pow]
    have hqSq : (Inv.inv (Real.log x))^2 <= (1 / 5 : Real)^2 := by gcongr
    calc
      _ <= ((k * n : Nat) : Real) + (k : Real) * (1 / 5 : Real) +
          4 * (k : Real)^2 * (Inv.inv (((2 * (k * n) - 1 : Nat) : Real)) * (1 / 5 : Real)^2) := by
        gcongr
      _ = _ := by field_simp; ring
  have hBracketNonneg : 0 <= ((k * n : Nat) : Real) + (k : Real) * Inv.inv (Real.log x) +
      4 * (k : Real)^2 * Inv.inv (((2 * (k * n) - 1 : Nat) : Real) * (Real.log x)^2) := by positivity
  rw [robin_root_error_scalar_eq hn hk hxOne]
  calc
    _ <= (1 / 20 : Real) * x^((1 / 2 : Real) * Inv.inv (k : Real) - n) *
        Inv.inv (Real.log x) *
        (((k * n : Nat) : Real) + (k : Real) * Inv.inv (Real.log x) +
          4 * (k : Real)^2 * Inv.inv (((2 * (k * n) - 1 : Nat) : Real) * (Real.log x)^2)) := by
      gcongr
      exact robin_zero_constant_le_one_twentieth
    _ <= _ := by gcongr

theorem robin_root_error_two_normalized
    {k : Nat} (hk : 2 <= k) {x b : Real} (hx : 366 <= x)
    (hPower : x^((1 / 2 : Real) * Inv.inv (k : Real) - 1 / 2) <= b) :
    Inv.inv (k : Real) * robinPsiWeightedErrorScalar (k * 2) (x^(Inv.inv (k : Real))) <=
      ((1 / 20 : Real) *
        (((k * 2 : Nat) : Real) + (k : Real) / 5 + 4 * (k : Real)^2 /
          (((2 * (k * 2) - 1 : Nat) : Real) * 25)) * b) *
            (x^(-(3 / 2 : Real)) * Inv.inv (Real.log x)) := by
  have hxOne : 1 < x := by linarith
  have hOddNat : 0 < 2 * (k * 2) - 1 := by omega
  have hOdd : (0 : Real) < ((2 * (k * 2) - 1 : Nat) : Real) := by exact_mod_cast hOddNat
  have hCoef : 0 <= (1 / 20 : Real) *
      (((k * 2 : Nat) : Real) + (k : Real) / 5 + 4 * (k : Real)^2 /
        (((2 * (k * 2) - 1 : Nat) : Real) * 25)) := by positivity
  have h := robin_scaled_rpow_log_le (r := -(3 / 2 : Real)) hxOne hCoef hPower
  have hExp : -(3 / 2 : Real) + ((1 / 2 : Real) * Inv.inv (k : Real) - 1 / 2) =
      (1 / 2 : Real) * Inv.inv (k : Real) - 2 := by ring
  rw [hExp] at h
  have hUpper := robin_root_error_upper_log_five (n := 2) (by omega) hk hx
  norm_num only [Nat.cast_ofNat] at hUpper
  nlinarith

theorem robin_second_weight_root_ratios {x : Real} (hx : 366 <= x) :
    And (x^(-(1 / 6 : Real)) <= 3 / 8)
      (And (x^(-(3 / 10 : Real)) <= 171 / 1000)
        (And (x^(-(1 / 4 : Real)) <= 229 / 1000)
          (And (x^(-(1 / 3 : Real)) <= 7 / 50)
            (x^(-(2 / 5 : Real)) <= 19 / 200)))) := by
  have hxPos : 0 < x := by linarith
  have hSix := robin_rpow_neg_div_le_of_pow (a := 1) (d := 6) (b := (3 / 8 : Real))
    hxPos (by norm_num) (by omega) (by norm_num; linarith)
  have hTen : x^(-(3 / 10 : Real)) <= 171 / 1000 := by
    apply robin_rpow_neg_div_le_of_pow (a := 3) (d := 10) hxPos (by norm_num) (by omega)
    have hPow : (366 : Real)^3 <= x^3 := by gcongr
    norm_num at hPow
    norm_num
    nlinarith
  have hFour := robin_rpow_neg_div_le_of_pow (a := 1) (d := 4) (b := (229 / 1000 : Real))
    hxPos (by norm_num) (by omega) (by norm_num; linarith)
  have hThree := robin_rpow_neg_div_le_of_pow (a := 1) (d := 3) (b := (7 / 50 : Real))
    hxPos (by norm_num) (by omega) (by norm_num; linarith)
  have hFive : x^(-(2 / 5 : Real)) <= 19 / 200 := by
    apply robin_rpow_neg_div_le_of_pow (a := 2) (d := 5) hxPos (by norm_num) (by omega)
    have hPow : (366 : Real)^2 <= x^2 := by gcongr
    norm_num at hPow
    norm_num
    nlinarith
  norm_num at hSix hFour hThree
  exact And.intro hSix (And.intro hTen (And.intro hFour (And.intro hThree hFive)))

theorem robinZeroKernel_fifth_two_upper {x : Real} (hx : 1 < x) :
    (robinZeroKernel 2 (1 / 5 : Complex) x).re <=
      (10 / 9 : Real) * x^(-(9 / 5 : Real)) * Inv.inv (Real.log x) := by
  have hF := robinZeroKernel_ofReal_eq_main_add_signed_tail 2
    (r := (1 / 5 : Real)) (by norm_num) hx
  have hNonneg := robinCpowLogTail_ofReal_re_nonneg (-(9 / 5 : Real)) 2 hx
  norm_num at hF hNonneg
  linarith

theorem robinPrimePowerWeightedTail_two_upper
    (hRH : RiemannHypothesis) {x : Real} (hx : 366 <= x) :
    robinPrimePowerWeightedTail 2 x <=
      (213 / 100 : Real) * (x^(-(3 / 2 : Real)) * Inv.inv (Real.log x)) := by
  have hxOne : 1 < x := by linarith
  have hLogPos := Real.log_pos hxOne
  have hScale : 0 <= x^(-(3 / 2 : Real)) * Inv.inv (Real.log x) := by positivity
  have hRatios := robin_second_weight_root_ratios hx
  have hHalf := (robinZeroKernel_half_two_bounds hxOne).2
  have hThird := robinZeroKernel_third_two_upper hxOne
  have hFifth := robinZeroKernel_fifth_two_upper hxOne
  have hThirdPower := robin_scaled_rpow_log_le (r := -(3 / 2 : Real)) hxOne
    (by norm_num : (0 : Real) <= 6 / 5) hRatios.1
  have hFifthPower := robin_scaled_rpow_log_le (r := -(3 / 2 : Real)) hxOne
    (by norm_num : (0 : Real) <= 10 / 9) hRatios.2.1
  norm_num at hThirdPower hFifthPower
  have hTwoError := robin_root_error_two_normalized (k := 2) (by omega) hx
    (b := (229 / 1000 : Real)) (by norm_num; exact hRatios.2.2.1)
  have hThreeError := robin_root_error_two_normalized (k := 3) (by omega) hx
    (b := (7 / 50 : Real)) (by norm_num; exact hRatios.2.2.2.1)
  have hFiveError := robin_root_error_two_normalized (k := 5) (by omega) hx
    (b := (19 / 200 : Real)) (by norm_num; exact hRatios.2.2.2.2)
  norm_num at hTwoError hThreeError hFiveError
  have hRoot := (robinPrimePowerWeightedTail_root_bounds hRH (n := 2) (by omega)
    (by linarith : 128 <= x)).2
  unfold robinRootPsiTailUpper at hRoot
  norm_num at hRoot
  linarith

theorem robinPsiWeightedErrorScalar_two_upper {x : Real} (hx : 366 <= x) :
    robinPsiWeightedErrorScalar 2 x <=
      (7 / 60 : Real) * (x^(-(3 / 2 : Real)) * Inv.inv (Real.log x)) := by
  have hxOne : 1 < x := by linarith
  have hLogPos := Real.log_pos hxOne
  have hq : Inv.inv (Real.log x) <= (1 / 5 : Real) := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : Real) < 5) (robin_log_ge_five hx)
  have hqNonneg : 0 <= Inv.inv (Real.log x) := inv_nonneg.mpr hLogPos.le
  have hqSq : (Inv.inv (Real.log x))^2 <= (1 / 5 : Real)^2 := by gcongr
  have hPoly : 2 + Inv.inv (Real.log x) + (4 / 3 : Real) * (Inv.inv (Real.log x))^2 <=
      (7 / 3 : Real) := by nlinarith
  have hPolyNonneg : 0 <= 2 + Inv.inv (Real.log x) + (4 / 3 : Real) * (Inv.inv (Real.log x))^2 := by positivity
  have hScale : 0 <= x^(-(3 / 2 : Real)) * Inv.inv (Real.log x) := by positivity
  have hEq : robinPsiWeightedErrorScalar 2 x =
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        (x^(-(3 / 2 : Real)) * Inv.inv (Real.log x)) *
          (2 + Inv.inv (Real.log x) + (4 / 3 : Real) * (Inv.inv (Real.log x))^2) := by
    unfold robinPsiWeightedErrorScalar
    norm_num
    field_simp [hLogPos.ne']
  rw [hEq]
  calc
    _ <= (1 / 20 : Real) * (x^(-(3 / 2 : Real)) * Inv.inv (Real.log x)) *
        (2 + Inv.inv (Real.log x) + (4 / 3 : Real) * (Inv.inv (Real.log x))^2) := by
      gcongr
      exact robin_zero_constant_le_one_twentieth
    _ <= (1 / 20 : Real) * (x^(-(3 / 2 : Real)) * Inv.inv (Real.log x)) * (7 / 3) := by gcongr
    _ = _ := by ring

theorem robin_second_theta_error_tail_lower
    (hRH : RiemannHypothesis) {x : Real} (hx : 366 <= x) :
    -(9 / 4 : Real) * x^(-(3 / 2 : Real)) * Inv.inv (Real.log x) -
        Real.log (2 * Real.pi) * x^(-(2 : Real)) * Inv.inv (Real.log x) <=
      robinPsiWeightedErrorIntegral 2 x - robinPrimePowerWeightedTail 2 x := by
  have hK := robinPrimePowerWeightedTail_two_upper hRH hx
  have hS := robinPsiWeightedErrorScalar_two_upper hx
  have hJ := (robinPsiWeightedErrorIntegral_bounds_all hRH (n := 2) (by omega)
    (by linarith : 2 <= x)).1
  have hScale : 0 <= x^(-(3 / 2 : Real)) * Inv.inv (Real.log x) := by
    have hxOne : 1 < x := by linarith
    exact mul_nonneg (Real.rpow_nonneg (by linarith : (0 : Real) <= x) _)
      (inv_nonneg.mpr (Real.log_pos hxOne).le)
  norm_num only [Nat.cast_ofNat] at hJ
  nlinarith

end

end Robin1984
