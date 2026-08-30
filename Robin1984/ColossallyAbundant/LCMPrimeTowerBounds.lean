import Robin1984.ColossallyAbundant.CAProfile
import Mathlib.Analysis.PSeries

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Prime-tower decomposition above `lcmUpto`

For a terminal factorization packet `n`, the lower-layer quotient above
`lcmUpto P` is a disjoint union of contiguous prime-tower intervals.  This
module exposes that representation so the marginal gain and the contributions
from completed lower layers can be estimated tower by tower.
-/

namespace Robin1984

open MeasureTheory

noncomputable section


/-- An `lcmUpto P` prime tower has retired at most layer one exactly when its
square lies strictly beyond `P`. -/
theorem factorization_lcmUpto_le_one_iff_lt_sq
    {P p : Nat} (hp : Nat.Prime p) :
    (Nat.lcmUpto P).factorization p <= 1 ↔ P < p ^ 2 := by
  rw [Nat.factorization_lcmUpto P hp]
  constructor
  · intro hLog
    have hTop := Nat.lt_pow_succ_log_self hp.one_lt P
    exact lt_of_lt_of_le hTop
      (pow_le_pow_right' hp.one_lt.le (by omega))
  · intro hSq
    have hLog : p.log P < 2 :=
      Nat.log_lt_of_lt_pow' (by norm_num) hSq
    omega


/-- Elementary logarithmic envelope used uniformly for every retired tower
depth. -/
theorem neg_log_one_sub_le_two_mul
    {z : Real} (hzNonneg : 0 <= z) (hzHalf : z <= 1 / 2) :
    -Real.log (1 - z) <= 2 * z := by
  have hDenPos : 0 < 1 - z := by linarith
  have hLog :
      Real.log ((1 - z)⁻¹) <= (1 - z)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr hDenPos)
  have hLogEq : Real.log ((1 - z)⁻¹) = -Real.log (1 - z) := by
    rw [Real.log_inv]
  have hFrac : (1 - z)⁻¹ - 1 = z / (1 - z) := by
    field_simp [ne_of_gt hDenPos]
    ring
  have hTwoDen : 1 <= 2 * (1 - z) := by linarith
  have hScaled : z <= z * (2 * (1 - z)) := by
    simpa using mul_le_mul_of_nonneg_left hTwoDen hzNonneg
  have hRatio : z / (1 - z) <= 2 * z := by
    apply (div_le_iff₀ hDenPos).2
    nlinarith
  rw [hLogEq, hFrac] at hLog
  exact hLog.trans hRatio

/-- Every prime-tower top correction is at most twice its first omitted
geometric term. -/
theorem primeTowerTopCorrection_le_two_inv_pow_succ
    {p k : Nat} (hp : Nat.Prime p) :
    primeTowerTopCorrection p k <=
      2 * ((p : Real)⁻¹) ^ (k + 1) := by
  let x : Real := (p : Real)⁻¹
  let z : Real := x ^ (k + 1)
  have hpReal : 2 <= (p : Real) := by exact_mod_cast hp.two_le
  have hpPos : 0 < (p : Real) := by positivity
  have hxNonneg : 0 <= x := by dsimp [x]; positivity
  have hxHalf : x <= 1 / 2 := by
    dsimp [x]
    simpa [one_div] using (inv_le_inv₀ hpPos (by norm_num)).2 hpReal
  have hxOne : x <= 1 := hxHalf.trans (by norm_num)
  have hzNonneg : 0 <= z := by dsimp [z]; positivity
  have hzLeX : z <= x := by
    dsimp [z]
    simpa using
      (pow_le_pow_of_le_one hxNonneg hxOne (by omega : 1 <= k + 1))
  have hzHalf : z <= 1 / 2 := hzLeX.trans hxHalf
  have hLog := neg_log_one_sub_le_two_mul hzNonneg hzHalf
  unfold primeTowerTopCorrection
  have hExp : -((k : Int) + 1) = -((k + 1 : Nat) : Int) := by omega
  rw [hExp, zpow_neg, zpow_natCast]
  simpa [z, x, inv_pow] using hLog

/-- At the `lcmUpto P` retirement depth, the omitted geometric term is below
the reciprocal frontier. -/
theorem primeTowerTopCorrection_lcm_le_two_div_frontier
    {P p : Nat} (hP : 0 < P) (hp : Nat.Prime p) :
    primeTowerTopCorrection p ((Nat.lcmUpto P).factorization p) <=
      2 / (P : Real) := by
  let k := p.log P
  have hGeneric :=
    primeTowerTopCorrection_le_two_inv_pow_succ (p := p) (k := k) hp
  have hTop : P < p ^ (k + 1) := by
    simpa [k] using Nat.lt_pow_succ_log_self hp.one_lt P
  have hPRealPos : 0 < (P : Real) := by exact_mod_cast hP
  have hPowCast :
      ((p : Real)⁻¹) ^ (k + 1) =
        (((p ^ (k + 1) : Nat) : Real))⁻¹ := by
    rw [inv_pow]
    norm_cast
  have hInv :
      (((p ^ (k + 1) : Nat) : Real))⁻¹ <= (P : Real)⁻¹ :=
    inv_anti₀ hPRealPos (by exact_mod_cast hTop.le)
  rw [Nat.factorization_lcmUpto P hp]
  dsimp [k] at hGeneric hPowCast ⊢
  rw [hPowCast] at hGeneric
  exact hGeneric.trans (by simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : Real) <= 2))


end

end Robin1984
