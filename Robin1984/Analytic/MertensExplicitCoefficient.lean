import Robin1984.Equivalence.ExplicitLogBounds
import Robin1984.Equivalence.LargeHeightExplicitBounds
import Robin1984.NicolasLandau.MertensWeightedBound
import Robin1984.NicolasLandau.ZeroConstantBound
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
The final theorem proves the uniform rational bound `9 / 4` used in the
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

theorem robinMertensWeightedScalar_lt_nine_quarters
    {H : Real} (hH : 100000 <= H) :
    robinMertensWeightedScalar H <
      (9 / 4 : Real) * (H^(-(1 / 2 : Real)) * Inv.inv (Real.log H)) := by
  have hHOne : 1 < H := by linarith
  have hHPos : 0 < H := by linarith
  have hLogPos := Real.log_pos hHOne
  have hData := robin_large_height_log_and_powers hH
  have hQ : Inv.inv (Real.log H) <= (2 / 23 : Real) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 23 / 2) hData.1
    norm_num only [one_div, inv_div, inv_inv] at h
    exact h
  have hQNonneg : 0 <= Inv.inv (Real.log H) := by positivity
  have hQSq : (Inv.inv (Real.log H))^2 <= (2 / 23 : Real)^2 := by gcongr
  have hLogQ : Real.log H * Inv.inv (Real.log H) = 1 := by field_simp
  have hSixth : H^(-(1 / 6 : Real)) <= (17 / 10 : Real) * Inv.inv (Real.log H) := by
    have h := mul_le_mul_of_nonneg_right (robin_log_times_sixth_power_bound hH) hQNonneg
    calc
      _ = (Real.log H * H^(-(1 / 6 : Real))) * Inv.inv (Real.log H) := by
        rw [mul_right_comm, hLogQ, one_mul]
      _ <= _ := h
  have hC := mul_le_mul_of_nonneg_right robin_zero_constant_le_one_twentieth
    (show 0 <= 1 + Inv.inv (Real.log H) + 4 * (Inv.inv (Real.log H))^2 by positivity)
  have hPi := mul_le_mul_of_nonneg_right robin_log_two_pi_upper
    (Real.rpow_nonneg hHPos.le (-(1 / 2 : Real)))
  have hPiBound : Real.log (2 * Real.pi) * H^(-(1 / 2 : Real)) <= (3 / 316 : Real) := by
    nlinarith [hData.2.2]
  have hPoly :
      (2 + (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) +
        ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) - 2) * Inv.inv (Real.log H) +
        (8 + 4 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) * (Inv.inv (Real.log H))^2 +
        2 * H^(-(1 / 6 : Real)) + Real.log (2 * Real.pi) * H^(-(1 / 2 : Real)) < (9 / 4 : Real) := by
    nlinarith
  rw [robinMertensWeightedScalar_normalized hHOne]
  have hScalePos : 0 < H^(-(1 / 2 : Real)) * Inv.inv (Real.log H) := by positivity
  nlinarith [mul_lt_mul_of_pos_left hPoly hScalePos]

end

end Robin1984
