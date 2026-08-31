import Robin1984.Analytic.PrimeCostLowerBound
import Robin1984.Analytic.PrimeSquareAbelBound
import Robin1984.Equivalence.LargeHeightExplicitBounds
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 analytic implication supplies the surrounding mathematical target.
- Formalization note: The exact coefficient normalization, explicit cutoff choices, and proof interfaces in this module are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Final uniform coefficient for the complete minimum prime cost

This module normalizes the lower bound for the minimum prime cost at
logarithmic height `H >= 74500`. It combines the root geometry, logarithmic
ratios, and the cancellation-aware complete prime-square block, then proves
the explicit scalar lower bound consumed by the large-height comparison.
-/

namespace Robin1984

noncomputable section

theorem robin_large_log_ratios {H : Real} (hH : 74500 <= H) :
    And ((16 / 17 : Real) <= Real.log H / (Real.log H + Real.log 2))
      (And (Real.log H / (Real.log H + Real.log 2) <= 1)
        (And (Inv.inv (Real.log H + Real.log 2) <= (17 / 202 : Real))
          (Real.log H / (Real.log H - Real.log 2) <= (107 / 100 : Real)))) := by
  have hL := (robin_large_height_log_and_powers hH).1
  have hTwoLower : (69 / 100 : Real) <= Real.log 2 := by linarith [robin_log_two_lower]
  have hTwoUpper : Real.log 2 <= (7 / 10 : Real) := by linarith [robin_log_two_upper]
  have hPlus : 0 < Real.log H + Real.log 2 := by linarith
  have hMinus : 0 < Real.log H - Real.log 2 := by linarith
  have hUeq : (Real.log H / (Real.log H + Real.log 2)) *
      (Real.log H + Real.log 2) = Real.log H := by field_simp
  have hWeq : (Real.log H / (Real.log H - Real.log 2)) *
      (Real.log H - Real.log 2) = Real.log H := by field_simp
  have hUlo : (16 / 17 : Real) <= Real.log H / (Real.log H + Real.log 2) := by
    nlinarith
  have hUhi : Real.log H / (Real.log H + Real.log 2) <= 1 := by
    apply (div_le_one hPlus).mpr
    linarith
  have hV := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 202 / 17)
    (show (202 / 17 : Real) <= Real.log H + Real.log 2 by linarith)
  norm_num only [one_div, inv_div, inv_inv] at hV
  have hW : Real.log H / (Real.log H - Real.log 2) <= (107 / 100 : Real) := by
    nlinarith
  exact And.intro hUlo (And.intro hUhi (And.intro hV hW))

theorem robin_prime_cost_products {H : Real} (hH : 74500 <= H) :
    And
      (H^(-(1 / 4 : Real)) * (Real.log H / (Real.log H + Real.log 2)) <=
        (573 / 10000 : Real))
      (And
        (H^(-(1 / 2 : Real)) * (Real.log H / (Real.log H + Real.log 2)) <=
          (7 / 2000 : Real))
        (H^(-(1 / 2 : Real)) * (Real.log H / (Real.log H - Real.log 2)) <=
          (197 / 50000 : Real))) := by
  have hHPos : 0 < H := by linarith
  have hRatios := robin_large_log_ratios hH
  have hQuarterAtCutoff :
      (74500 : Real)^(-(1 / 4 : Real)) <= (303 / 5000 : Real) := by
    have h := robin_rpow_neg_div_le_of_pow
      (x := (74500 : Real)) (a := 1) (d := 4) (b := (303 / 5000 : Real))
      (by norm_num) (by norm_num) (by omega) (by norm_num)
    norm_num at h
    exact h
  have hQuarterMono := robin_log_mul_rpow_neg_le
    (b := (74500 : Real)) (by norm_num) hH
    (r := (1 / 4 : Real)) (by norm_num)
    (by nlinarith [robin_log_74500_bounds.1])
  have hQuarterNumerator : Real.log H * H^(-(1 / 4 : Real)) <=
      (1123 / 100 : Real) * (303 / 5000 : Real) := by
    have hAtCutoff : Real.log (74500 : Real) * (74500 : Real)^(-(1 / 4 : Real)) <=
        (1123 / 100 : Real) * (303 / 5000 : Real) := by
      exact mul_le_mul robin_log_74500_bounds.2 hQuarterAtCutoff
        (Real.rpow_nonneg (by norm_num : (0 : Real) <= 74500) _)
        (by norm_num : (0 : Real) <= 1123 / 100)
    exact hQuarterMono.trans hAtCutoff
  have hHalfMono := robin_log_mul_rpow_neg_le
    (b := (74500 : Real)) (by norm_num) hH
    (r := (1 / 2 : Real)) (by norm_num)
    (by nlinarith [robin_log_74500_bounds.1])
  have hHalfNumerator : Real.log H * H^(-(1 / 2 : Real)) <=
      (1123 / 100 : Real) * (1 / 272 : Real) := by
    have hAtCutoff : Real.log (74500 : Real) * (74500 : Real)^(-(1 / 2 : Real)) <=
        (1123 / 100 : Real) * (1 / 272 : Real) := by
      exact mul_le_mul robin_log_74500_bounds.2
        ((robin_large_height_log_and_powers (show (74500 : Real) <= 74500 by norm_num)).2.2)
        (Real.rpow_nonneg (by norm_num : (0 : Real) <= 74500) _)
        (by norm_num : (0 : Real) <= 1123 / 100)
    exact hHalfMono.trans hAtCutoff
  have hPlus : 0 < Real.log H + Real.log 2 := by
    nlinarith [(robin_large_height_log_and_powers hH).1, robin_log_two_lower]
  have hMinus : 0 < Real.log H - Real.log 2 := by
    nlinarith [(robin_large_height_log_and_powers hH).1, robin_log_two_upper]
  have hW : 0 <= Real.log H / (Real.log H - Real.log 2) := by
    exact div_nonneg (Real.log_nonneg (by linarith)) hMinus.le
  have hQuarterEq : H^(-(1 / 4 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) =
      (Real.log H * H^(-(1 / 4 : Real))) * Inv.inv (Real.log H + Real.log 2) := by
    field_simp
  have hHalfEq : H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) =
      (Real.log H * H^(-(1 / 2 : Real))) * Inv.inv (Real.log H + Real.log 2) := by
    field_simp
  have hQuarter : H^(-(1 / 4 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <= (573 / 10000 : Real) := by
    rw [hQuarterEq]
    calc
      _ <= ((1123 / 100 : Real) * (303 / 5000 : Real)) * (17 / 202 : Real) := by
        exact mul_le_mul hQuarterNumerator hRatios.2.2.1 (inv_nonneg.mpr hPlus.le)
          (by positivity)
      _ <= _ := by norm_num
  have hHalf : H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <= (7 / 2000 : Real) := by
    rw [hHalfEq]
    calc
      _ <= ((1123 / 100 : Real) * (1 / 272 : Real)) * (17 / 202 : Real) := by
        exact mul_le_mul hHalfNumerator hRatios.2.2.1 (inv_nonneg.mpr hPlus.le)
          (by positivity)
      _ <= _ := by norm_num
  have hFar : H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H - Real.log 2)) <= (197 / 50000 : Real) := by
    calc
      _ <= (1 / 272 : Real) * (107 / 100 : Real) := by
        exact mul_le_mul (robin_large_height_log_and_powers hH).2.2 hRatios.2.2.2
          hW (by norm_num)
      _ <= _ := by norm_num
  exact And.intro hQuarter (And.intro hHalf hFar)

def robinPrimeCostNormalized (H : Real) : Real :=
  2 * Real.sqrt 2 * (Real.log H / (Real.log H + Real.log 2)) *
      (1 - Inv.inv (Real.log H + Real.log 2)) -
    (9 / 4 : Real) * (2 : Real)^(1 / 4 : Real) * H^(-(1 / 4 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) -
    Real.log (2 * Real.pi) * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) -
    4 * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H - Real.log 2)) -
    (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
      (2 * Real.sqrt 2) * H^(-(1 : Real)) *
      (Real.log H / (Real.log H - Real.log 2)) *
      (2 + Inv.inv (Real.log H - Real.log 2) +
        (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2)

theorem robinPrimeCostNormalized_ge
    {H : Real} (hH : 74500 <= H) :
    (113 / 50 : Real) <= robinPrimeCostNormalized H := by
  have hHPos : 0 < H := by linarith
  have hData := robin_large_height_log_and_powers hH
  have hRatios := robin_large_log_ratios hH
  have hProducts := robin_prime_cost_products hH
  have hLogTwoPos : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hLogHPos : 0 < Real.log H := by linarith [hData.1]
  have hU : 0 <= Real.log H / (Real.log H + Real.log 2) := by positivity
  have hW : 0 <= Real.log H / (Real.log H - Real.log 2) := by
    have hMinus : 0 < Real.log H - Real.log 2 := by linarith [hData.1, robin_log_two_upper]
    positivity
  have hV : 0 <= 1 - Inv.inv (Real.log H + Real.log 2) := by linarith [hRatios.2.2.1]
  have hMain : 2 * (7071 / 5000 : Real) * (16 / 17 : Real) *
      (1 - (17 / 202 : Real)) <=
      2 * Real.sqrt 2 * (Real.log H / (Real.log H + Real.log 2)) *
        (1 - Inv.inv (Real.log H + Real.log 2)) := by
    have hOne := mul_le_mul_of_nonneg_left robin_sqrt_two_lower (by norm_num : (0 : Real) <= 2)
    have hTwo := mul_le_mul hOne hRatios.1 (by norm_num : (0 : Real) <= 16 / 17)
      (by positivity : (0 : Real) <= 2 * Real.sqrt 2)
    exact mul_le_mul hTwo (sub_le_sub_left hRatios.2.2.1 1)
      (by norm_num : (0 : Real) <= 1 - 17 / 202) (by positivity)
  have hRoot : (9 / 4 : Real) * (2 : Real)^(1 / 4 : Real) * H^(-(1 / 4 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <=
        (9 / 4 : Real) * (119 / 100 : Real) * (573 / 10000 : Real) := by
    calc
      _ = (9 / 4 : Real) * (2 : Real)^(1 / 4 : Real) *
          (H^(-(1 / 4 : Real)) * (Real.log H / (Real.log H + Real.log 2))) := by ring
      _ <= _ := by
        have hCoeff : (9 / 4 : Real) * (2 : Real)^(1 / 4 : Real) <=
            (9 / 4 : Real) * (119 / 100 : Real) :=
          mul_le_mul_of_nonneg_left robin_fourth_root_two_upper (by norm_num)
        exact mul_le_mul hCoeff hProducts.1
          (mul_nonneg (Real.rpow_nonneg hHPos.le _) hU)
          (by positivity)
  have hPi : Real.log (2 * Real.pi) * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <=
        (46 / 25 : Real) * (7 / 2000 : Real) := by
    calc
      _ = Real.log (2 * Real.pi) *
          (H^(-(1 / 2 : Real)) * (Real.log H / (Real.log H + Real.log 2))) := by ring
      _ <= _ := by
        exact mul_le_mul robin_log_two_pi_upper hProducts.2.1
          (mul_nonneg (Real.rpow_nonneg hHPos.le _) hU)
          (by norm_num)
  have hFar : 4 * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H - Real.log 2)) <=
        4 * (197 / 50000 : Real) := by nlinarith [hProducts.2.2]
  have hSqrtUpper : Real.sqrt 2 <= (3 / 2 : Real) := by
    have hSquare := Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
    have hNonneg := Real.sqrt_nonneg (2 : Real)
    nlinarith
  have hInvH : H^(-(1 : Real)) <= (1 / 74500 : Real) := by
    rw [Real.rpow_neg_one]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 74500) hH
  have hQMinus : Inv.inv (Real.log H - Real.log 2) <= (2 / 21 : Real) := by
    have hDen : (21 / 2 : Real) <= Real.log H - Real.log 2 := by
      nlinarith [hData.1, robin_log_two_upper]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 21 / 2) hDen
    norm_num only [one_div, inv_div, inv_inv] at h
    exact h
  have hQMinusNonneg : 0 <= Inv.inv (Real.log H - Real.log 2) := by
    exact inv_nonneg.mpr (by nlinarith [hData.1, robin_log_two_upper])
  have hQMinusSq : (Inv.inv (Real.log H - Real.log 2))^2 <= (2 / 21 : Real)^2 := by
    nlinarith [mul_self_le_mul_self hQMinusNonneg hQMinus]
  have hTailPoly : 2 + Inv.inv (Real.log H - Real.log 2) +
      (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2 <= (211 / 100 : Real) := by
    nlinarith
  have hTailPolyNonneg : 0 <= 2 + Inv.inv (Real.log H - Real.log 2) +
      (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2 := by positivity
  have hInvHNonneg : 0 <= H^(-(1 : Real)) :=
    Real.rpow_nonneg hHPos.le (-(1 : Real))
  have hTail :
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        (2 * Real.sqrt 2) * H^(-(1 : Real)) *
        (Real.log H / (Real.log H - Real.log 2)) *
        (2 + Inv.inv (Real.log H - Real.log 2) +
          (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2) <=
          (1 / 10000 : Real) := by
    have hFirst := mul_le_mul_of_nonneg_right robin_zero_constant_le_one_twentieth
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity : 0 <= 2 * Real.sqrt 2)
        hInvHNonneg) hW) hTailPolyNonneg)
    have hSqrtFactor : (1 / 20 : Real) * (2 * Real.sqrt 2) <=
        (1 / 20 : Real) * (2 * (3 / 2 : Real)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hSqrtUpper (by norm_num)) (by norm_num)
    have hWithH : (1 / 20 : Real) * (2 * Real.sqrt 2) * H^(-(1 : Real)) <=
        (1 / 20 : Real) * (2 * (3 / 2 : Real)) * (1 / 74500 : Real) := by
      exact mul_le_mul hSqrtFactor hInvH hInvHNonneg (by positivity)
    have hWithW : (1 / 20 : Real) * (2 * Real.sqrt 2) * H^(-(1 : Real)) *
        (Real.log H / (Real.log H - Real.log 2)) <=
        (1 / 20 : Real) * (2 * (3 / 2 : Real)) * (1 / 74500 : Real) *
          (107 / 100 : Real) := by
      exact mul_le_mul hWithH hRatios.2.2.2 hW (by positivity)
    have hWithPoly : (1 / 20 : Real) * (2 * Real.sqrt 2) * H^(-(1 : Real)) *
        (Real.log H / (Real.log H - Real.log 2)) *
        (2 + Inv.inv (Real.log H - Real.log 2) +
          (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2) <=
        (1 / 20 : Real) * (2 * (3 / 2 : Real)) * (1 / 74500 : Real) *
          (107 / 100 : Real) * (211 / 100 : Real) := by
      exact mul_le_mul hWithW hTailPoly hTailPolyNonneg (by positivity)
    calc
      _ <= (1 / 20 : Real) * (2 * Real.sqrt 2) * H^(-(1 : Real)) *
          (Real.log H / (Real.log H - Real.log 2)) *
          (2 + Inv.inv (Real.log H - Real.log 2) +
            (4 / 3 : Real) * (Inv.inv (Real.log H - Real.log 2))^2) := by
        simpa only [mul_assoc] using hFirst
      _ <= (1 / 20 : Real) * (2 * (3 / 2 : Real)) * (1 / 74500 : Real) *
          (107 / 100 : Real) * (211 / 100 : Real) := by
        exact hWithPoly
      _ <= _ := by norm_num
  unfold robinPrimeCostNormalized
  nlinarith

theorem robin_prime_cost_root_geometry {H : Real} (hH : 74500 <= H) :
    And (366 <= Real.sqrt (2 * H))
      (And (Real.sqrt (2 * H) <= H / 2)
        (H * Real.log H <=
          (Real.sqrt (2 * H))^2 * Real.log (Real.sqrt (2 * H)))) := by
  have hHPos : 0 < H := by linarith
  have hSq := Real.sq_sqrt (show 0 <= 2 * H by linarith)
  have hNonneg := Real.sqrt_nonneg (2 * H)
  have hRoot : 366 <= Real.sqrt (2 * H) := by nlinarith
  have hHalf : Real.sqrt (2 * H) <= H / 2 := by
    nlinarith [mul_nonneg hHPos.le (show 0 <= H - 8 by linarith)]
  have hLog : Real.log (Real.sqrt (2 * H)) =
      (1 / 2 : Real) * (Real.log H + Real.log 2) := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow (show 0 < 2 * H by linarith),
      Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hHPos.ne']
    ring
  have hDen : H * Real.log H <=
      (Real.sqrt (2 * H))^2 * Real.log (Real.sqrt (2 * H)) := by
    rw [hSq, hLog]
    nlinarith [mul_nonneg hHPos.le
      (Real.log_nonneg (by norm_num : (1 : Real) <= 2))]
  exact And.intro hRoot (And.intro hHalf hDen)

theorem robin_prime_cost_block_normalized {H : Real} (hH : 74500 <= H) :
    (let s := Real.sqrt (2 * H)
     let b := H / 2
     2 * s^(-(1 : Real)) * Inv.inv (Real.log s) -
       s^(-(1 : Real)) * Inv.inv ((Real.log s)^2) -
       (9 / 4 : Real) * s^(-(3 / 2 : Real)) * Inv.inv (Real.log s) -
       Real.log (2 * Real.pi) * s^(-(2 : Real)) * Inv.inv (Real.log s) -
       2 * b^(-(1 : Real)) * Inv.inv (Real.log b) -
       robinPsiWeightedErrorScalar 2 b) =
      (H^(-(1 / 2 : Real)) * Inv.inv (Real.log H)) *
        robinPrimeCostNormalized H := by
  have hHPos : 0 < H := by linarith
  have hLogHPos : 0 < Real.log H := Real.log_pos (by linarith)
  have hPlus : Not (Real.log H + Real.log 2 = 0) := by positivity
  have hMinus : Not (Real.log H - Real.log 2 = 0) := by
    have hL := (robin_large_height_log_and_powers hH).1
    have hU := robin_log_two_upper
    linarith
  have hRootPow (r : Real) : (Real.sqrt (2 * H))^r =
      (2 : Real)^(r / 2) * H^(r / 2) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_mul (show 0 <= 2 * H by linarith),
      show (1 / 2 : Real) * r = r / 2 by ring,
      Real.mul_rpow (by norm_num) hHPos.le]
  have hHalfTwo : (2 : Real)^(-(1 / 2 : Real)) = Real.sqrt 2 / 2 := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) <= 2), <- Real.sqrt_eq_rpow]
    have hSq := Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
    have hPos := Real.sqrt_pos.mpr (by norm_num : (0 : Real) < 2)
    field_simp
    nlinarith
  have hQuarterTwo : (2 : Real)^(-(3 / 4 : Real)) =
      (2 : Real)^(1 / 4 : Real) / 2 := by
    have h := Real.rpow_add (by norm_num : (0 : Real) < 2)
      (1 / 4 : Real) (-1 : Real)
    norm_num at h
    linarith
  have hThreeQuarter : H^(-(3 / 4 : Real)) =
      H^(-(1 / 2 : Real)) * H^(-(1 / 4 : Real)) := by
    rw [<- Real.rpow_add hHPos]
    norm_num
  have hFull : H^(-(1 : Real)) =
      H^(-(1 / 2 : Real)) * H^(-(1 / 2 : Real)) := by
    rw [<- Real.rpow_add hHPos]
    norm_num
  have hThreeFull : H^(-(3 / 2 : Real)) =
      H^(-(1 / 2 : Real)) * H^(-(1 : Real)) := by
    rw [<- Real.rpow_add hHPos]
    norm_num
  have hOne : (Real.sqrt (2 * H))^(-(1 : Real)) =
      (Real.sqrt 2 / 2) * H^(-(1 / 2 : Real)) := by
    have h := hRootPow (-1)
    rw [show (-1 : Real) / 2 = -(1 / 2 : Real) by norm_num, hHalfTwo] at h
    exact h
  have hThree : (Real.sqrt (2 * H))^(-(3 / 2 : Real)) =
      ((2 : Real)^(1 / 4 : Real) / 2) *
        (H^(-(1 / 2 : Real)) * H^(-(1 / 4 : Real))) := by
    have h := hRootPow (-(3 / 2 : Real))
    rw [show (-(3 / 2 : Real)) / 2 = -(3 / 4 : Real) by norm_num,
      hQuarterTwo, hThreeQuarter] at h
    exact h
  have hTwo : (Real.sqrt (2 * H))^(-(2 : Real)) =
      (1 / 2 : Real) * H^(-(1 : Real)) := by
    have h := hRootPow (-2)
    norm_num at h
    norm_num
    exact h
  have hB : (H / 2)^(-(1 : Real)) = 2 * H^(-(1 : Real)) := by
    rw [Real.div_rpow hHPos.le (by norm_num)]
    norm_num
    ring
  have hTwoScaled : (Real.sqrt (2 * H))^(-(2 : Real)) =
      (1 / 2 : Real) *
        (H^(-(1 / 2 : Real)) * H^(-(1 / 2 : Real))) := by
    rw [hTwo, hFull]
  have hBScaled : (H / 2)^(-(1 : Real)) =
      2 * (H^(-(1 / 2 : Real)) * H^(-(1 / 2 : Real))) := by
    rw [hB, hFull]
  have hTwoThree : (2 : Real)^(-(3 / 2 : Real)) = Real.sqrt 2 / 4 := by
    rw [show (-(3 / 2 : Real)) = -(1 / 2 : Real) + (-1 : Real) by ring,
      Real.rpow_add (by norm_num : (0 : Real) < 2), hHalfTwo]
    norm_num
    ring
  have hBThree : (H / 2)^(-(3 / 2 : Real)) =
      (2 * Real.sqrt 2) * (H^(-(1 / 2 : Real)) * H^(-(1 : Real))) := by
    rw [Real.div_rpow hHPos.le (by norm_num), hTwoThree, hThreeFull]
    have hSq := Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
    have hPos := Real.sqrt_pos.mpr (by norm_num : (0 : Real) < 2)
    field_simp
    nlinarith
  have hLogS : Real.log (Real.sqrt (2 * H)) =
      (1 / 2 : Real) * (Real.log H + Real.log 2) := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow (show 0 < 2 * H by linarith),
      Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hHPos.ne']
    ring
  have hLogB : Real.log (H / 2) = Real.log H - Real.log 2 :=
    Real.log_div hHPos.ne' (by norm_num)
  have hScalar : robinPsiWeightedErrorScalar 2 (H / 2) =
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        ((H / 2)^(-(3 / 2 : Real)) * Inv.inv (Real.log (H / 2)) *
          (2 + Inv.inv (Real.log (H / 2)) +
            4 * Inv.inv (3 * (Real.log (H / 2))^2))) := by
    unfold robinPsiWeightedErrorScalar
    norm_num
  dsimp only
  rw [hScalar, hOne, hThree, hTwoScaled, hBScaled, hBThree, hLogS, hLogB]
  unfold robinPrimeCostNormalized
  field_simp [hLogHPos.ne', hPlus, hMinus]
  ring

theorem robin_minimum_prime_cost_ge_large_scalar
    (hRH : RiemannHypothesis) {H : Real} (hH : 74500 <= H) :
    (113 / 50 : Real) *
        (H^(-(1 / 2 : Real)) * Inv.inv (Real.log H)) <=
      Finset.sum (Nat.primesLE (Nat.floor (H / 2)))
        (fun p => min (Real.log p / (H * Real.log H))
          ((Inv.inv (p : Real))^2)) := by
  have hGeometry := robin_prime_cost_root_geometry hH
  have hHOne : 1 < H := by linarith
  have hSOne : 1 < Real.sqrt (2 * H) := by linarith [hGeometry.1]
  have hBlock := robin_complete_prime_square_block_lower
    hRH hGeometry.1 hGeometry.2.1
  have hMin := robin_minimum_prime_cost_ge_block
    hHOne hSOne hGeometry.2.1 hGeometry.2.2
  have hNorm := robin_prime_cost_block_normalized hH
  dsimp only at hNorm
  rw [hNorm] at hBlock
  have hLogPos := Real.log_pos hHOne
  have hScale : 0 <= H^(-(1 / 2 : Real)) * Inv.inv (Real.log H) := by
    positivity
  have h := (mul_le_mul_of_nonneg_left
    (robinPrimeCostNormalized_ge hH) hScale).trans (hBlock.trans hMin)
  linarith

end

end Robin1984
