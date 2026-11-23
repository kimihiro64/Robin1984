import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Robin1984.GRH.MertensWeightedTailIntegrability

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The derivative-weighted Mertens tail obtained by integration by parts.
- Formalization note: Pass an inverse-square-root bound for the primitive tail through the Mertens weight while retaining the leading coefficient.
- PROVENANCE-END
-/

/-!
# The forward estimate for a signed Mertens tail

An inverse-square-root bound on the absolute primitive tail gives the
same leading constant after multiplying by the Mertens weight. The
derivative integral contributes one further power of the logarithm.
-/

open MeasureTheory Set

namespace Robin1984.GRH

private theorem real_rpow_neg_threeHalves {t : Real} (ht : 0 < t) :
    t ^ (-(3 / 2) : Real) = Inv.inv (t * Real.sqrt t) := by
  rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  congr 1
  calc
    _ = t ^ ((1 : Real) + 1 / 2) := by norm_num
    _ = _ := by rw [Real.rpow_add ht, Real.rpow_one]

private theorem integral_rpow_neg_threeHalves {x : Real} (hx : 0 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real => t ^ (-(3 / 2) : Real)) =
      2 / Real.sqrt x := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : Real) < -1) hx]
  have hExp : -(3 / 2 : Real) + 1 = -(1 / 2 : Real) := by norm_num
  rw [hExp, Real.rpow_neg hx.le, <- Real.sqrt_eq_rpow]
  ring

private theorem neg_mertensTailSlope_le_inverseLogSquare {x t : Real}
    (hx : 1 < x) (hLog : 1 <= Real.log x) (hxt : x <= t) :
    -mertensTailSlope t <= 3 / (t * Real.log x ^ (2 : Nat)) := by
  have htx := hx.trans_le hxt
  have ht := zero_lt_one.trans htx
  have hL := Real.log_pos hx
  have hl := Real.log_pos htx
  have hMono := Real.log_le_log (zero_lt_one.trans hx) hxt
  have hOne := hLog.trans hMono
  have hSq : Real.log x ^ (2 : Nat) <= Real.log t ^ (2 : Nat) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hMono) (add_nonneg hl.le hL.le)]
  calc
    _ = (Real.log t + 2) / (t * Real.log t ^ (3 : Nat)) := by
      rw [mertensTailSlope, neg_div, neg_neg]
    _ <= (3 * Real.log t) / (t * Real.log t ^ (3 : Nat)) :=
      div_le_div_of_nonneg_right (by linarith only [hOne]) (mul_nonneg ht.le (pow_nonneg hl.le _))
    _ = 3 / (t * Real.log t ^ (2 : Nat)) := by field_simp [ht.ne', hl.ne']
    _ <= _ := div_le_div_of_nonneg_left (by norm_num) (mul_pos ht (pow_pos hL _))
      (mul_le_mul_of_nonneg_left hSq ht.le)

/-- A primitive tail with absolute bound `B / sqrt t` has a signed
weighted tail bounded by the same leading coefficient, with explicit
lower-order error `7 * B / (sqrt x * log x ^ 2)`. -/
theorem signed_mertensTail_le_of_abs_primitiveTail {T : Real -> Real} {x B : Real}
    (hx : 1 < x) (hLog : 1 <= Real.log x) (hB : 0 <= B)
    (hT : AEStronglyMeasurable T (volume.restrict (Ioi x)))
    (hBound : forall t : Real, x <= t -> abs (T t) <= B / Real.sqrt t) :
    -(T x * mertensTailWeight x) -
        integral (volume.restrict (Ioi x)) (fun t => T t * mertensTailSlope t) <=
      B / (Real.sqrt x * Real.log x) + 7 * B / (Real.sqrt x * Real.log x ^ (2 : Nat)) := by
  let y := Real.sqrt x
  let L := Real.log x
  let d := 3 * B / L ^ (2 : Nat)
  let mu := volume.restrict (Ioi x)
  let F (t : Real) := T t * mertensTailSlope t
  have hx0 := zero_lt_one.trans hx
  have hy : 0 < y := Real.sqrt_pos.mpr hx0
  have hL : 0 < L := Real.log_pos hx
  have hBounded (t : Real) (ht : Membership.mem (Ioi x) t) : norm (T t) <= B / y := by
    have hxt : x < t := ht
    rw [Real.norm_eq_abs]
    exact (hBound t hxt.le).trans
      (div_le_div_of_nonneg_left hB hy (Real.sqrt_le_sqrt hxt.le))
  have hF : Integrable F mu := (norm_integral_mul_mertensTailSlope_le hx hT hBounded).1
  have hDom : Integrable (fun t : Real => d * t ^ (-(3 / 2) : Real)) mu :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : Real) < -1) hx0).const_mul d
  have hPoint (t : Real) (ht : Membership.mem (Ioi x) t) :
      norm (F t) <= d * t ^ (-(3 / 2) : Real) := by
    have hxt : x < t := ht
    have ht1 := hx.trans hxt
    have ht0 := zero_lt_one.trans ht1
    have hts : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hSlope := neg_mertensTailSlope_le_inverseLogSquare hx hLog hxt.le
    have hSlopePos := neg_nonneg.mpr (mertensTailSlope_nonpos ht1)
    unfold F
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (mertensTailSlope_nonpos ht1)]
    calc
      _ <= B / Real.sqrt t * (3 / (t * L ^ (2 : Nat))) :=
        mul_le_mul (hBound t hxt.le) hSlope hSlopePos (div_nonneg hB hts.le)
      _ = _ := by
        rw [real_rpow_neg_threeHalves ht0]
        unfold d
        field_simp [ht0.ne', hL.ne', hts.ne']
  have hIntBound : norm (integral mu F) <= 6 * B / (y * L ^ (2 : Nat)) := calc
    _ <= integral mu (fun t => norm (F t)) := norm_integral_le_integral_norm _
    _ <= integral mu (fun t : Real => d * t ^ (-(3 / 2) : Real)) :=
      setIntegral_mono_on hF.norm hDom measurableSet_Ioi hPoint
    _ = _ := by
      rw [integral_const_mul, integral_rpow_neg_threeHalves hx0]
      unfold d
      field_simp [hL.ne', hy.ne']
      ring
  have hFirst : -(T x * mertensTailWeight x) <= (B / y) * mertensTailWeight x := by
    rw [<- neg_mul]
    exact mul_le_mul_of_nonneg_right
      ((neg_le_abs _).trans (hBound x le_rfl)) (mertensTailWeight_pos hx).le
  have hSecond : -integral mu F <= 6 * B / (y * L ^ (2 : Nat)) := calc
    _ <= norm (integral mu F) := by
      simpa only [Real.norm_eq_abs] using neg_le_abs (integral mu F)
    _ <= _ := hIntBound
  change -(T x * mertensTailWeight x) - integral mu F <=
    B / (y * L) + 7 * B / (y * L ^ (2 : Nat))
  rw [sub_eq_add_neg]
  calc
    _ <= B / y * mertensTailWeight x + 6 * B / (y * L ^ (2 : Nat)) :=
      add_le_add hFirst hSecond
    _ = _ := by
      change B / y * (Inv.inv L + (Inv.inv L) ^ (2 : Nat)) + 6 * B / (y * L ^ (2 : Nat)) = _
      field_simp [hL.ne', hy.ne'] <;> ring

end Robin1984.GRH
