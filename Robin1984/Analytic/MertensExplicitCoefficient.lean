import Robin1984.Equivalence.LargeHeightExplicitBounds
import Robin1984.NicolasLandau.MertensWeightedBound
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 analytic implication supplies the surrounding mathematical target.
- Formalization note: The exact coefficient normalization, explicit cutoff choices, and proof interfaces in this module are primarily project-authored.
- PROVENANCE-END
-/

/-!
# The final uniform Mertens scalar coefficient

The weighted Mertens error is divided by its natural large-height scale and
rewritten as a sum of the explicit psi error and prime-power contributions.
The final theorem proves the uniform rational bound `113 / 50` used in the
large-height Robin estimate.
-/

namespace Robin1984

noncomputable section

theorem robinMertensWeightedScalar_normalized {H : Real} (hH : 1 < H) :
    robinMertensWeightedScalar H = (H^(-(1 / 2 : Real)) * Inv.inv (Real.log H)) *
      ((2 + (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) +
        ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) - 2) * Inv.inv (Real.log H) +
        (8 + 4 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) * (Inv.inv (Real.log H))^2 +
        2 * H^(-(1 / 6 : Real)) + Real.log (2 * Real.pi) * H^(-(1 / 2 : Real))) := by
  have hHPos : 0 < H := by linarith
  have hThird : H^(-(2 / 3 : Real)) = H^(-(1 / 2 : Real)) * H^(-(1 / 6 : Real)) := by
    rw [<- Real.rpow_add hHPos]
    norm_num
  have hFull : H^(-(1 : Real)) = H^(-(1 / 2 : Real)) * H^(-(1 / 2 : Real)) := by
    rw [<- Real.rpow_add hHPos]
    norm_num
  unfold robinMertensWeightedScalar
  rw [hThird, hFull]
  simp only [<- inv_pow]
  ring

theorem robinMertensWeightedScalar_lt_113_div_50
    {H : Real} (hH : 74500 <= H) :
    robinMertensWeightedScalar H <
      (113 / 50 : Real) * (H^(-(1 / 2 : Real)) * Inv.inv (Real.log H)) := by
  have hHOne : 1 < H := by linarith
  have hHPos : 0 < H := by linarith
  have hLogPos := Real.log_pos hHOne
  have hData := robin_large_height_log_and_powers hH
  have hQ : Inv.inv (Real.log H) <= (5 / 56 : Real) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 56 / 5) hData.1
    norm_num only [one_div, inv_div, inv_inv] at h
    exact h
  have hQNonneg : 0 <= Inv.inv (Real.log H) := inv_nonneg.mpr hLogPos.le
  have hQSq : (Inv.inv (Real.log H))^2 <= (5 / 56 : Real)^2 := by gcongr
  have hLogQ : Real.log H * Inv.inv (Real.log H) = 1 := by field_simp
  have hSixth : H^(-(1 / 6 : Real)) <= (87 / 50 : Real) * Inv.inv (Real.log H) := by
    have h := mul_le_mul_of_nonneg_right (robin_log_times_sixth_power_bound hH) hQNonneg
    calc
      _ = (Real.log H * H^(-(1 / 6 : Real))) * Inv.inv (Real.log H) := by
        rw [mul_right_comm, hLogQ, one_mul]
      _ <= _ := h
  have hC := mul_le_mul_of_nonneg_right robin_zero_constant_le_one_twentieth
    (show 0 <= 1 + Inv.inv (Real.log H) + 4 * (Inv.inv (Real.log H))^2 by positivity)
  have hPi := mul_le_mul robin_log_two_pi_upper hData.2.2
    (Real.rpow_nonneg hHPos.le _) (by norm_num : (0 : Real) <= 46 / 25)
  have hPoly :
      (2 + (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) +
        ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) - 2) * Inv.inv (Real.log H) +
        (8 + 4 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) * (Inv.inv (Real.log H))^2 +
        2 * H^(-(1 / 6 : Real)) + Real.log (2 * Real.pi) * H^(-(1 / 2 : Real)) <
          (113 / 50 : Real) := by
    nlinarith
  rw [robinMertensWeightedScalar_normalized hHOne]
  have hScalePos : 0 < H^(-(1 / 2 : Real)) * Inv.inv (Real.log H) := by
    exact mul_pos (Real.rpow_pos_of_pos hHPos _) (inv_pos.mpr hLogPos)
  nlinarith [mul_lt_mul_of_pos_left hPoly hScalePos]

end

end Robin1984
