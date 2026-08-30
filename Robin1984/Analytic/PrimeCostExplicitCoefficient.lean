import Robin1984.Analytic.PrimeCostLowerBound
import Robin1984.Analytic.PrimeSquareAbelBound
import Robin1984.Equivalence.ExplicitLogBounds
import Robin1984.Equivalence.LargeHeightExplicitBounds
import Robin1984.NicolasLandau.ZeroConstantBound
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
logarithmic height `H >= 100000`. It combines the root geometry, logarithmic
ratios, and the complete prime-square block, then proves the explicit scalar
lower bound consumed by the large-height comparison.
-/

namespace Robin1984

noncomputable section

theorem robin_large_log_ratios {H : Real} (hH : 100000 <= H) :
    And ((115 / 122 : Real) <= Real.log H / (Real.log H + Real.log 2))
      (And (Real.log H / (Real.log H + Real.log 2) <= 1)
        (And (Inv.inv (Real.log H + Real.log 2) <= (100 / 1219 : Real))
          (Real.log H / (Real.log H - Real.log 2) <= (115 / 108 : Real)))) := by
  have hL := (robin_large_height_log_and_powers hH).1
  have hTwoLower : (69 / 100 : Real) <= Real.log 2 := by linarith [robin_log_two_lower]
  have hTwoUpper : Real.log 2 <= (7 / 10 : Real) := by linarith [robin_log_two_upper]
  have hPlus : 0 < Real.log H + Real.log 2 := by linarith
  have hMinus : 0 < Real.log H - Real.log 2 := by linarith
  have hUeq : (Real.log H / (Real.log H + Real.log 2)) * (Real.log H + Real.log 2) = Real.log H := by
    field_simp
  have hWeq : (Real.log H / (Real.log H - Real.log 2)) * (Real.log H - Real.log 2) = Real.log H := by
    field_simp
  have hUlo : (115 / 122 : Real) <= Real.log H / (Real.log H + Real.log 2) := by nlinarith
  have hUhi : Real.log H / (Real.log H + Real.log 2) <= 1 := by
    apply (div_le_one hPlus).mpr
    linarith
  have hV := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1219 / 100)
    (show (1219 / 100 : Real) <= Real.log H + Real.log 2 by linarith)
  norm_num only [one_div, inv_div, inv_inv] at hV
  have hW : Real.log H / (Real.log H - Real.log 2) <= (115 / 108 : Real) := by nlinarith
  exact And.intro hUlo (And.intro hUhi (And.intro hV hW))

def robinPrimeCostNormalized (H : Real) : Real :=
  2 * Real.sqrt 2 * (Real.log H / (Real.log H + Real.log 2)) *
      (1 - Inv.inv (Real.log H + Real.log 2)) -
    (9 / 4 : Real) * (2 : Real)^(1 / 4 : Real) * H^(-(1 / 4 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) -
    Real.log (2 * Real.pi) * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) -
    4 * Real.log 4 * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H - Real.log 2))

theorem robinPrimeCostNormalized_ge
    {H : Real} (hH : 100000 <= H) : (113 / 50 : Real) <= robinPrimeCostNormalized H := by
  have hHPos : 0 < H := by linarith
  have hData := robin_large_height_log_and_powers hH
  have hRatios := robin_large_log_ratios hH
  have hLogTwoPos : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hLogHPos : 0 < Real.log H := by linarith [hData.1]
  have hU : 0 <= Real.log H / (Real.log H + Real.log 2) := by positivity
  have hW : 0 <= Real.log H / (Real.log H - Real.log 2) := by
    have hMinus : 0 < Real.log H - Real.log 2 := by linarith [hData.1, robin_log_two_upper]
    positivity
  have hV : 0 <= 1 - Inv.inv (Real.log H + Real.log 2) := by linarith [hRatios.2.2.1]
  have hMain : 2 * (707 / 500 : Real) * (115 / 122 : Real) * (1 - (100 / 1219 : Real)) <=
      2 * Real.sqrt 2 * (Real.log H / (Real.log H + Real.log 2)) *
        (1 - Inv.inv (Real.log H + Real.log 2)) := by
    have hOne := mul_le_mul_of_nonneg_left robin_sqrt_two_lower (by norm_num : (0 : Real) <= 2)
    have hTwo := mul_le_mul hOne hRatios.1 (by norm_num : (0 : Real) <= 115 / 122)
      (by positivity : (0 : Real) <= 2 * Real.sqrt 2)
    exact mul_le_mul hTwo (sub_le_sub_left hRatios.2.2.1 1)
      (by norm_num : (0 : Real) <= 1 - 100 / 1219) (by positivity)
  have hRoot : (9 / 4 : Real) * (2 : Real)^(1 / 4 : Real) * H^(-(1 / 4 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <=
        (9 / 4 : Real) * (119 / 100 : Real) * (563 / 10000 : Real) := by
    calc
      _ <= (9 / 4 : Real) * (119 / 100 : Real) * (563 / 10000 : Real) * 1 := by
        gcongr
        . exact robin_fourth_root_two_upper
        . exact hData.2.1
        . exact hRatios.2.1
      _ = _ := by ring
  have hPiFirst : Real.log (2 * Real.pi) * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <=
        3 * H^(-(1 / 2 : Real)) * (Real.log H / (Real.log H + Real.log 2)) := by
    gcongr
    exact robin_log_two_pi_upper
  have hPi : Real.log (2 * Real.pi) * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H + Real.log 2)) <= (3 / 316 : Real) := by
    have hBound : 3 * H^(-(1 / 2 : Real)) * (Real.log H / (Real.log H + Real.log 2)) <=
        3 * (1 / 316 : Real) * 1 := by gcongr; exacts [hData.2.2, hRatios.2.1]
    linarith
  have hFar : 4 * Real.log 4 * H^(-(1 / 2 : Real)) *
      (Real.log H / (Real.log H - Real.log 2)) <=
        4 * (7 / 5 : Real) * (1 / 316 : Real) * (115 / 108 : Real) := by
    have hOne := mul_le_mul_of_nonneg_left robin_log_four_upper (by norm_num : (0 : Real) <= 4)
    have hTwo := mul_le_mul hOne hData.2.2 (Real.rpow_nonneg hHPos.le _)
      (by norm_num : (0 : Real) <= 4 * (7 / 5))
    exact mul_le_mul hTwo hRatios.2.2.2 hW (by norm_num)
  unfold robinPrimeCostNormalized
  linarith

theorem robin_prime_cost_root_geometry {H : Real} (hH : 100000 <= H) :
    And (400 <= Real.sqrt (2 * H))
      (And (Real.sqrt (2 * H) <= H / 2)
        (H * Real.log H <= (Real.sqrt (2 * H))^2 * Real.log (Real.sqrt (2 * H)))) := by
  have hHPos : 0 < H := by linarith
  have hSq := Real.sq_sqrt (show 0 <= 2 * H by linarith)
  have hNonneg := Real.sqrt_nonneg (2 * H)
  have hFour : 400 <= Real.sqrt (2 * H) := by nlinarith
  have hHalf : Real.sqrt (2 * H) <= H / 2 := by
    nlinarith [mul_nonneg hHPos.le (show 0 <= H - 8 by linarith)]
  have hLog : Real.log (Real.sqrt (2 * H)) = (1 / 2 : Real) * (Real.log H + Real.log 2) := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow (show 0 < 2 * H by linarith),
      Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hHPos.ne']
    ring
  have hDen : H * Real.log H <= (Real.sqrt (2 * H))^2 * Real.log (Real.sqrt (2 * H)) := by
    rw [hSq, hLog]
    nlinarith [mul_nonneg hHPos.le (Real.log_nonneg (by norm_num : (1 : Real) <= 2))]
  exact And.intro hFour (And.intro hHalf hDen)

theorem robin_prime_cost_block_normalized {H : Real} (hH : 100000 <= H) :
    (let s := Real.sqrt (2 * H)
     let b := H / 2
     2 * s^(-(1 : Real)) * Inv.inv (Real.log s) -
       s^(-(1 : Real)) * Inv.inv ((Real.log s)^2) -
       (9 / 4 : Real) * s^(-(3 / 2 : Real)) * Inv.inv (Real.log s) -
       Real.log (2 * Real.pi) * s^(-(2 : Real)) * Inv.inv (Real.log s) -
       2 * Real.log 4 * b^(-(1 : Real)) * Inv.inv (Real.log b)) =
      (H^(-(1 / 2 : Real)) * Inv.inv (Real.log H)) * robinPrimeCostNormalized H := by
  have hHPos : 0 < H := by linarith
  have hLogHPos : 0 < Real.log H := Real.log_pos (by linarith)
  have hLogTwoPos : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hPlus : Not (Real.log H + Real.log 2 = 0) := by positivity
  have hMinus : Not (Real.log H - Real.log 2 = 0) := by
    have hL := (robin_large_height_log_and_powers hH).1
    have hU := robin_log_two_upper
    linarith
  have hRootPow (r : Real) : (Real.sqrt (2 * H))^r = (2 : Real)^(r / 2) * H^(r / 2) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_mul (show 0 <= 2 * H by linarith),
      show (1 / 2 : Real) * r = r / 2 by ring, Real.mul_rpow (by norm_num) hHPos.le]
  have hHalfTwo : (2 : Real)^(-(1 / 2 : Real)) = Real.sqrt 2 / 2 := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) <= 2), <- Real.sqrt_eq_rpow]
    have hSq := Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
    have hPos := Real.sqrt_pos.mpr (by norm_num : (0 : Real) < 2)
    field_simp
    nlinarith
  have hQuarterTwo : (2 : Real)^(-(3 / 4 : Real)) = (2 : Real)^(1 / 4 : Real) / 2 := by
    have h := Real.rpow_add (by norm_num : (0 : Real) < 2) (1 / 4 : Real) (-1 : Real)
    norm_num at h
    linarith
  have hThreeQuarter : H^(-(3 / 4 : Real)) = H^(-(1 / 2 : Real)) * H^(-(1 / 4 : Real)) := by
    rw [<- Real.rpow_add hHPos]
    norm_num
  have hFull : H^(-(1 : Real)) = H^(-(1 / 2 : Real)) * H^(-(1 / 2 : Real)) := by
    rw [<- Real.rpow_add hHPos]
    norm_num
  have hOne : (Real.sqrt (2 * H))^(-(1 : Real)) = (Real.sqrt 2 / 2) * H^(-(1 / 2 : Real)) := by
    have h := hRootPow (-1)
    rw [show (-1 : Real) / 2 = -(1 / 2 : Real) by norm_num, hHalfTwo] at h
    exact h
  have hThree : (Real.sqrt (2 * H))^(-(3 / 2 : Real)) =
      ((2 : Real)^(1 / 4 : Real) / 2) * (H^(-(1 / 2 : Real)) * H^(-(1 / 4 : Real))) := by
    have h := hRootPow (-(3 / 2 : Real))
    rw [show (-(3 / 2 : Real)) / 2 = -(3 / 4 : Real) by norm_num, hQuarterTwo, hThreeQuarter] at h
    exact h
  have hTwo : (Real.sqrt (2 * H))^(-(2 : Real)) = (1 / 2 : Real) * H^(-(1 : Real)) := by
    have h := hRootPow (-2)
    norm_num at h
    norm_num
    exact h
  have hB : (H / 2)^(-(1 : Real)) = 2 * H^(-(1 : Real)) := by
    rw [Real.div_rpow hHPos.le (by norm_num)]
    norm_num
    ring
  have hLogS : Real.log (Real.sqrt (2 * H)) = (1 / 2 : Real) * (Real.log H + Real.log 2) := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow (show 0 < 2 * H by linarith),
      Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hHPos.ne']
    ring
  have hLogB : Real.log (H / 2) = Real.log H - Real.log 2 :=
    Real.log_div hHPos.ne' (by norm_num)
  dsimp only
  rw [hOne, hThree, hTwo, hB, hLogS, hLogB, hFull]
  unfold robinPrimeCostNormalized
  field_simp [hLogHPos.ne', hPlus, hMinus]
  ring

theorem robin_minimum_prime_cost_ge_large_scalar
    (hRH : RiemannHypothesis) {H : Real} (hH : 100000 <= H) :
    (113 / 50 : Real) * (H^(-(1 / 2 : Real)) * Inv.inv (Real.log H)) <=
      Finset.sum (Nat.primesLE (Nat.floor (H / 2)))
        (fun p => min (Real.log p / (H * Real.log H)) ((Inv.inv (p : Real))^2)) := by
  have hGeometry := robin_prime_cost_root_geometry hH
  have hHOne : 1 < H := by linarith
  have hSOne : 1 < Real.sqrt (2 * H) := by linarith [hGeometry.1]
  have hBlock := robin_complete_prime_square_block_lower hRH hGeometry.1 hGeometry.2.1
  have hMin := robin_minimum_prime_cost_ge_block hHOne hSOne hGeometry.2.1 hGeometry.2.2
  have hNorm := robin_prime_cost_block_normalized hH
  dsimp only at hNorm
  rw [hNorm] at hBlock
  have hLogPos := Real.log_pos hHOne
  have hScale : 0 <= H^(-(1 / 2 : Real)) * Inv.inv (Real.log H) := by positivity
  have h := (mul_le_mul_of_nonneg_left (robinPrimeCostNormalized_ge hH) hScale).trans (hBlock.trans hMin)
  linarith

end

end Robin1984
