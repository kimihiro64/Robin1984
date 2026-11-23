import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The logarithmic tangent upper bound and the positive square-root correction in the ideal Robin inequality.
- Formalization note: Apply the tangent inequality twice and compare the positive normalized denominator when the Chebyshev argument is at least half the cutoff.
- PROVENANCE-END
-/

/-!
# Taking logarithms in the ideal Robin converse

The iterated logarithm lies below its tangent. Applying that tangent
retains exactly the signed Chebyshev boundary term in the Mertens formula.
-/

namespace Robin1984.GRH

private theorem log_le_log_add_tangent {u v : Real} (hu : 0 < u) (hv : 0 < v) :
    Real.log u <= Real.log v + (u - v) / v := by
  have h := Real.log_le_sub_one_of_pos (div_pos hu hv)
  rw [Real.log_div hu.ne' hv.ne'] at h
  rw [sub_div, div_self hv.ne']
  linarith only [h]

/-- The logarithm of the corrected ideal threshold has the exact signed
linear term and a bounded inverse-square-root correction. -/
theorem log_correctedIdealThreshold_le {x t C : Real}
    (hx : 4 <= x) (ht : x / 2 <= t) (hC : 0 <= C) :
    Real.log (Real.log t + C / Real.sqrt t) <=
      Real.log (Real.log x) + (t - x) / (x * Real.log x) +
        4 * C / (Real.sqrt x * Real.log x) := by
  let y := Real.sqrt x
  let L := Real.log x
  let l := Real.log t
  let s := Real.sqrt t
  have hx0 : 0 < x := by linarith only [hx]
  have ht0 : 0 < t := by linarith only [hx, ht]
  have hL : 0 < L := Real.log_pos (by linarith only [hx])
  have hl : 0 < l := Real.log_pos (by linarith only [hx, ht])
  have hy : 0 < y := Real.sqrt_pos.mpr hx0
  have hs : 0 < s := Real.sqrt_pos.mpr ht0
  have hysq : y ^ (2 : Nat) = x := Real.sq_sqrt hx0.le
  have hyTwo : 2 <= y := by
    have hFour : (2 : Real) ^ (2 : Nat) = 4 := by norm_num
    have hAt : (2 : Real) ^ (2 : Nat) <= x := by simpa only [hFour] using hx
    have h := Real.sqrt_le_sqrt hAt
    rwa [Real.sqrt_sq (by norm_num : (0 : Real) <= 2)] at h
  have hyt : y <= t := by
    have h := mul_le_mul_of_nonneg_right hyTwo hy.le
    rw [<- pow_two, hysq] at h
    linarith only [h, ht]
  have hL2 : L / 2 <= l := by
    have h := Real.log_le_log hy hyt
    have heq : L = 2 * Real.log y := by
      change Real.log x = _
      rw [<- hysq, Real.log_pow]
      norm_num
    rw [heq]
    linarith only [h]
  have hy2 : y / 2 <= s := by
    have h : (y / 2) ^ (2 : Nat) <= t := by
      rw [div_pow, hysq]
      norm_num
      linarith only [hx, ht]
    have hyHalf : 0 <= y / 2 := div_nonneg hy.le (by norm_num)
    simpa only [Real.sqrt_sq hyHalf] using Real.sqrt_le_sqrt h
  have hDen : (y * L) / 4 <= s * l := calc
    _ = (y / 2) * (L / 2) := by ring
    _ <= _ := mul_le_mul hy2 hL2 (div_nonneg hL.le (by norm_num)) hs.le
  have hCorr : C / (s * l) <= 4 * C / (y * L) := calc
    _ = C * (1 / (s * l)) := by ring
    _ <= C * (1 / ((y * L) / 4)) :=
      mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (div_pos (mul_pos hy hL) (by norm_num)) hDen) hC
    _ = _ := by field_simp [hy.ne', hL.ne']
  have hSingle : l <= L + (t - x) / x := log_le_log_add_tangent ht0 hx0
  have hInner : Real.log l <= Real.log L + (t - x) / (x * L) := by
    apply (log_le_log_add_tangent hl hL).trans
    refine add_le_add (le_refl _) ?_
    rw [<- div_div]
    apply div_le_div_of_nonneg_right _ hL.le
    linarith only [hSingle]
  change Real.log (l + C / s) <= Real.log L + (t - x) / (x * L) + 4 * C / (y * L)
  calc
    _ <= Real.log l + (l + C / s - l) / l :=
      log_le_log_add_tangent (add_pos_of_pos_of_nonneg hl (div_nonneg hC hs.le)) hl
    _ = Real.log l + C / (s * l) := by rw [add_sub_cancel_left, div_div]
    _ <= _ := add_le_add hInner hCorr

end Robin1984.GRH
