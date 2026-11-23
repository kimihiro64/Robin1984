import Robin1984.GRH.DedekindMertensAbel

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The explicit real Mertens weight and its reciprocal.
- Formalization note: Differentiate the two weights and bound the reciprocal derivative on the positive domain.
- PROVENANCE-END
-/

/-!
# Weights for the signed Dedekind Mertens tail

The reciprocal weight has nonnegative slope bounded by the inverse of
the argument. This sign permits deweighting a one-sided error bound.
-/

open Filter Topology

namespace Robin1984.GRH

/-- The Abel kernel after taking the factor of the inverse square
into the Chebyshev error density. -/
noncomputable def mertensTailWeight (x : Real) : Real :=
  Inv.inv (Real.log x) + (Inv.inv (Real.log x)) ^ 2

/-- The reciprocal weight used to recover the unweighted tail. -/
noncomputable def mertensDeweight (x : Real) : Real :=
  Real.log x ^ 2 / (1 + Real.log x)

/-- The explicit derivative of the reciprocal weight. -/
noncomputable def mertensDeweightSlope (x : Real) : Real :=
  Inv.inv x * (Real.log x * (Real.log x + 2) / (1 + Real.log x) ^ 2)

theorem mertensTailWeight_eq_mul_kernel {x : Real} (hx : 1 < x) :
    mertensTailWeight x = x ^ 2 * mertensAbelKernel x := by
  have hLog := Real.log_pos hx
  have hx0 := zero_lt_one.trans hx
  unfold mertensTailWeight mertensAbelKernel
  field_simp [hLog.ne', hx0.ne']
  ring

theorem mertensTailWeight_pos {x : Real} (hx : 1 < x) : 0 < mertensTailWeight x := by
  unfold mertensTailWeight
  exact add_pos_of_pos_of_nonneg (inv_pos.mpr (Real.log_pos hx)) (sq_nonneg _)

theorem mertensDeweight_mul_tailWeight {x : Real} (hx : 1 < x) :
    mertensDeweight x * mertensTailWeight x = 1 := by
  have hLog := Real.log_pos hx
  have hDen : 0 < 1 + Real.log x := add_pos zero_lt_one hLog
  unfold mertensDeweight mertensTailWeight
  field_simp [hLog.ne', hDen.ne']
  ring

theorem tendsto_mertensTailWeight :
    Tendsto mertensTailWeight atTop (nhds 0) := by
  have h : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  unfold mertensTailWeight
  simpa only [zero_pow (by decide : Not ((2 : Nat) = 0)), add_zero] using h.add (h.pow 2)

theorem hasDerivAt_mertensTailWeight {x : Real} (hx : 1 < x) :
    HasDerivAt mertensTailWeight (-(Real.log x + 2) / (x * Real.log x ^ 3)) x := by
  have hLog := Real.log_pos hx
  have hx0 := zero_lt_one.trans hx
  have hInv := (Real.hasDerivAt_log hx0.ne').inv hLog.ne'
  refine (hInv.add (hInv.pow 2)).congr_deriv ?_
  change -Inv.inv x / Real.log x ^ 2 +
      (2 : Real) * (Inv.inv (Real.log x)) ^ ((2 : Nat) - 1) *
        (-Inv.inv x / Real.log x ^ 2) =
    -(Real.log x + 2) / (x * Real.log x ^ 3)
  norm_num only [Nat.reduceSub, pow_one]
  field_simp [hLog.ne', hx0.ne']
  ring

theorem hasDerivAt_mertensDeweight {x : Real} (hx : 1 < x) :
    HasDerivAt mertensDeweight (mertensDeweightSlope x) x := by
  have hLog := Real.log_pos hx
  have hx0 := zero_lt_one.trans hx
  have hDen : 0 < 1 + Real.log x := add_pos zero_lt_one hLog
  have hD := Real.hasDerivAt_log hx0.ne'
  have hDenD := (hasDerivAt_const x (1 : Real)).add hD
  refine ((hD.pow 2).div hDenD hDen.ne').congr_deriv ?_
  change (((2 : Real) * Real.log x ^ ((2 : Nat) - 1) * Inv.inv x) *
      (1 + Real.log x) - Real.log x ^ 2 * (0 + Inv.inv x)) /
      (1 + Real.log x) ^ 2 = mertensDeweightSlope x
  unfold mertensDeweightSlope
  norm_num only [Nat.reduceSub, pow_one, zero_add]
  field_simp [hDen.ne', hx0.ne']
  ring

/-- The sign and upper bound are uniform throughout the domain of the
Mertens tail. -/
theorem mertensDeweightSlope_bounds {x : Real} (hx : 1 < x) :
    And (0 <= mertensDeweightSlope x) (mertensDeweightSlope x <= Inv.inv x) := by
  have hx0 := zero_lt_one.trans hx
  have hLog := Real.log_pos hx
  have hDen : 0 < (1 + Real.log x) ^ 2 := pow_pos (add_pos zero_lt_one hLog) 2
  have hNum : Real.log x * (Real.log x + 2) <= (1 + Real.log x) ^ 2 := by nlinarith
  have hRatio := (div_le_div_of_nonneg_right hNum hDen.le).trans_eq (div_self hDen.ne')
  have hNonnegative : 0 <= mertensDeweightSlope x := by
    unfold mertensDeweightSlope
    positivity
  exact And.intro hNonnegative
    ((mul_le_mul_of_nonneg_left hRatio (inv_nonneg.mpr hx0.le)).trans_eq (mul_one _))

theorem mertensDeweight_le_log {x : Real} (hx : 1 < x) :
    mertensDeweight x <= Real.log x := by
  have hLog := Real.log_pos hx
  have hDen : 0 < 1 + Real.log x := add_pos zero_lt_one hLog
  have hNum : Real.log x ^ 2 <= Real.log x * (1 + Real.log x) := by nlinarith
  unfold mertensDeweight
  calc
    _ <= Real.log x * (1 + Real.log x) / (1 + Real.log x) :=
      div_le_div_of_nonneg_right hNum hDen.le
    _ = Real.log x := by field_simp [hDen.ne']

end Robin1984.GRH
