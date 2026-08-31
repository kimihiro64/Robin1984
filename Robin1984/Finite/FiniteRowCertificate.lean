import Robin1984.Analytic.EulerLower
import Robin1984.Finite.FiniteLayerChecks
import Robin1984.Finite.FinitePacketProducts
import Robin1984.Finite.RobinFiniteStartupCATangent
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# A rational certificate for one finite Robin interval

`RobinFiniteRow` stores an interval in `log n`, a tangent slope, prime-layer
cutoffs, exact product bounds, a height bound, and endpoint logarithm bounds.
Its three decidable checks certify the layer signs, the finite products, and
the two endpoint inequalities using rational arithmetic.

The soundness theorems translate each check to its real analytic statement and
show that a checked row proves Robin's inequality for every `n > 5040` whose
logarithm lies in that row.
-/

namespace Robin1984

def robinRatLogScale (q : Rat) : Nat := Nat.log2 (q.num.natAbs / q.den)

structure RobinFiniteRow where
  lo : Rat
  hi : Rat
  lambda : Rat
  cuts : List Nat
  gainUpper : Rat
  heightExponent : Nat
  heightMantissa : Rat
  logLoLower : Rat
  logHiLower : Rat

def robinFiniteRowHeightLower (r : RobinFiniteRow) : Rat :=
  (r.heightExponent : Rat) * (693147180559945309 / 1000000000000000000) +
    robinLogLower r.heightMantissa 20

def robinFiniteRowObjectiveUpper (r : RobinFiniteRow) : Rat :=
  robinLogScaledUpper r.gainUpper (robinRatLogScale r.gainUpper) 20 -
    r.lambda * robinFiniteRowHeightLower r

def RobinFiniteProductChecks (r : RobinFiniteRow) : Prop :=
  And (1 <= r.gainUpper)
    (And ((2 : Rat)^(robinRatLogScale r.gainUpper) <= r.gainUpper)
    (And (1 <= r.heightMantissa)
    (And ((robinBoxProduct r.cuts (fun v => v.1^(v.2 + 1) - 1) : Rat) <=
      r.gainUpper * (robinBoxProduct r.cuts (fun v => v.1 * (v.1^v.2 - 1)) : Rat))
      ((2 : Rat)^r.heightExponent * r.heightMantissa <=
        (robinBoxProduct r.cuts Prod.fst : Rat)))))

def RobinFiniteEndpointCheck (H ell lambda upper : Rat) : Prop :=
  And (1 < H) (And (1 <= ell)
    (And ((2 : Rat)^(robinRatLogScale H) <= H)
    (And (ell <= robinLogScaledLower H (robinRatLogScale H) 20)
    (And ((2 : Rat)^(robinRatLogScale ell) <= ell)
      (upper < 57721 / 100000 + robinLogScaledLower ell (robinRatLogScale ell) 20 - lambda * H)))))

def RobinFiniteRowChecks (r : RobinFiniteRow) : Prop :=
  And (RobinLayerChecks r.cuts r.lambda)
    (And (RobinFiniteProductChecks r)
    (And (RobinFiniteEndpointCheck r.lo r.logLoLower r.lambda (robinFiniteRowObjectiveUpper r))
      (RobinFiniteEndpointCheck r.hi r.logHiLower r.lambda (robinFiniteRowObjectiveUpper r))))

instance (r : RobinFiniteRow) : Decidable (RobinFiniteProductChecks r) :=
  inferInstanceAs (Decidable (And _ (And _ (And _ (And _ _)))))

instance (H ell lambda upper : Rat) : Decidable (RobinFiniteEndpointCheck H ell lambda upper) :=
  inferInstanceAs (Decidable (And _ (And _ (And _ (And _ (And _ _))))))

instance (r : RobinFiniteRow) : Decidable (RobinFiniteRowChecks r) :=
  inferInstanceAs (Decidable (And _ (And _ (And _ _))))


theorem RobinFiniteProductChecks.sound {r : RobinFiniteRow}
    (hlambda : 0 <= r.lambda) (h : RobinFiniteProductChecks r) :
    (robinLayerBox r.cuts).sum (robinRawEventWeight r.lambda) <=
      (robinFiniteRowObjectiveUpper r : Real) := by
  let A := robinBoxProduct r.cuts (fun v => v.1^(v.2 + 1) - 1)
  let B := robinBoxProduct r.cuts (fun v => v.1 * (v.1^v.2 - 1))
  let Q := robinBoxProduct r.cuts Prod.fst
  have hShape : forall v, Membership.mem (robinLayerBox r.cuts) v -> And (2 <= v.1) (0 < v.2) := by
    intro v hv
    have hm := robinLayerBox_mem.mp hv
    exact And.intro hm.2.2.1.two_le hm.1
  have hPos := robinPacketProducts_pos hShape
  unfold robinPacketNumerator robinPacketDenominator robinPacketBaseProduct at hPos
  rw [robinLayerBox_prod, robinLayerBox_prod, robinLayerBox_prod] at hPos
  have hA : (0 : Real) < A := by exact_mod_cast hPos.1
  have hB : (0 : Real) < B := by exact_mod_cast hPos.2.1
  have hQ : (0 : Real) < Q := by exact_mod_cast hPos.2.2
  have hGain : (A : Real) <= (r.gainUpper : Real) * B := by exact_mod_cast h.2.2.2.1
  have hRatio : (A : Real) / B <= (r.gainUpper : Real) := by
    calc
      (A : Real) / B <= ((r.gainUpper : Real) * B) / B :=
        div_le_div_of_nonneg_right hGain hB.le
      _ = r.gainUpper := by field_simp
  have hLogG := Real.log_le_log (div_pos hA hB) hRatio
  rw [Real.log_div hA.ne' hB.ne'] at hLogG
  have hGUpper := (robin_log_scaled_bounds
    (robinRatLogScale r.gainUpper) 20 h.2.1).2
  have hM : (0 : Real) < r.heightMantissa := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) h.2.2.1)
  have hHeight : (2 : Real)^r.heightExponent * (r.heightMantissa : Real) <= Q := by
    exact_mod_cast h.2.2.2.2
  have hLogQ := Real.log_le_log (mul_pos (pow_pos (by norm_num) _) hM) hHeight
  rw [Real.log_mul (by positivity) hM.ne', Real.log_pow] at hLogQ
  have hMLog := robinLogLower_le_log h.2.2.1 20
  have hLog2 := mul_le_mul_of_nonneg_left robin_log_two_precise_bounds.1
    (Nat.cast_nonneg r.heightExponent : (0 : Real) <= r.heightExponent)
  have hQLower : (robinFiniteRowHeightLower r : Real) <= Real.log Q := by
    unfold robinFiniteRowHeightLower
    push_cast
    linarith
  have hLam : (0 : Real) <= r.lambda := by exact_mod_cast hlambda
  have hPayment := mul_le_mul_of_nonneg_left hQLower hLam
  rw [robinRawEventWeight_sum_eq_box_products]
  change Real.log A - Real.log B - (r.lambda : Real) * Real.log Q <= _
  unfold robinFiniteRowObjectiveUpper
  push_cast
  linarith

theorem RobinFiniteEndpointCheck.sound {H ell lambda upper : Rat}
    (h : RobinFiniteEndpointCheck H ell lambda upper) :
    (upper : Real) < Real.eulerMascheroniConstant + Real.log (Real.log (H : Real)) -
      (lambda : Real) * H := by
  have hLog := (robin_log_scaled_bounds (robinRatLogScale H) 20 h.2.2.1).1
  have hEll : (ell : Real) <= (robinLogScaledLower H (robinRatLogScale H) 20 : Real) := by
    exact_mod_cast h.2.2.2.1
  have hEllPos : (0 : Real) < ell := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) h.2.1)
  have hLogLog := Real.log_le_log hEllPos (hEll.trans hLog)
  have hEllLog := (robin_log_scaled_bounds (robinRatLogScale ell) 20 h.2.2.2.2.1).1
  have hCmp : (upper : Real) < 57721 / 100000 +
      (robinLogScaledLower ell (robinRatLogScale ell) 20 : Real) - (lambda : Real) * H := by
    have hRaw : (upper : Real) <
        ((57721 / 100000 + robinLogScaledLower ell (robinRatLogScale ell) 20 - lambda * H : Rat) : Real) :=
      Rat.cast_lt.mpr h.2.2.2.2.2
    push_cast at hRaw
    exact hRaw
  linarith [robin_euler_constant_lower]

theorem RobinFiniteRowChecks.sound {r : RobinFiniteRow} (h : RobinFiniteRowChecks r)
    {n : Nat} (hn : 5040 < n)
    (hLo : (r.lo : Real) <= Real.log (n : Real))
    (hHi : Real.log (n : Real) <= (r.hi : Real)) :
    Robin1984.Core.NativeRobinInequality n := by
  have hnPos : 0 < n := by omega
  have hLam : (0 : Real) <= r.lambda := by exact_mod_cast h.1.1
  have hObj := robin_objective_le_finite_box h.1.sound hnPos
  have hProd := h.2.1.sound h.1.1
  have hLeft := h.2.2.1.sound
  have hRight := h.2.2.2.sound
  have hMin := min_logLogCATangentEndpoint_le hLam
    (by exact_mod_cast h.2.2.1.1) (hLo.trans hHi) (And.intro hLo hHi)
  have hMinBound : (robinFiniteRowObjectiveUpper r : Real) < Real.eulerMascheroniConstant +
      min (Real.log (Real.log (r.lo : Real)) - (r.lambda : Real) * r.lo)
        (Real.log (Real.log (r.hi : Real)) - (r.lambda : Real) * r.hi) := by
    rcases le_total
      (Real.log (Real.log (r.lo : Real)) - (r.lambda : Real) * r.lo)
      (Real.log (Real.log (r.hi : Real)) - (r.lambda : Real) * r.hi) with hLe | hLe
    . rw [min_eq_left hLe]
      linarith
    . rw [min_eq_right hLe]
      linarith
  have hLogBound : Real.log (abundancy n) < Real.log (robinBoundRatio n) := by
    rw [log_robinBoundRatio_eq_of_cutoff hn]
    linarith
  have hRatio := (Real.log_lt_log_iff (abundancy_pos hnPos) (robinBoundRatio_pos_of_cutoff hn)).mp hLogBound
  exact (nativeRobinInequality_iff_abundancy_lt_bound hnPos).mpr hRatio

end Robin1984
