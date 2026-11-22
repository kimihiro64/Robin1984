import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The supporting-line comparison in the project's corrected ideal Robin criterion and its weighted Hecke extension.
- Formalization note: The statements separate finite layer ownership, the logarithmic price, and exact cancellation of the Mertens boundary term.
- PROVENANCE-END
-/

/-!
# Finite support comparisons for the ideal Robin criterion

Buying levels at the frontier price gives a bound on any finite occupation
of prime-power levels. With the weighted norm budget, the boundary term in
the partial summation formula cancels in this bound.
-/

namespace Robin1984.GRH

/-- A finite frontier maximizes the surplus after subtracting a fixed price per unit of cost. -/
theorem finiteSupportingLine {I : Type*} [DecidableEq I]
    (occupied frontier : Finset I) (payoff cost : I -> Real) (price : Real)
    (inside : forall i, Membership.mem frontier i -> price * cost i <= payoff i)
    (outside : forall i, Membership.mem occupied i -> Not (Membership.mem frontier i) ->
      payoff i <= price * cost i) :
    occupied.sum payoff <= frontier.sum payoff + price * (occupied.sum cost - frontier.sum cost) := by
  let surplus := fun i => payoff i - price * cost i
  have dropOutside :
      (Inter.inter occupied frontier).sum (fun i => -surplus i) <=
        occupied.sum (fun i => -surplus i) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun i hi hnot =>
      neg_nonneg.mpr (sub_nonpos.mpr (outside i hi (fun hp =>
        hnot (Finset.mem_inter.mpr (And.intro hi hp))))))
  have enlargeInside : (Inter.inter occupied frontier).sum surplus <= frontier.sum surplus :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun i hi _ =>
      sub_nonneg.mpr (inside i hi))
  simp only [Finset.sum_neg_distrib] at dropOutside
  have comparison := (neg_le_neg_iff.mp dropOutside).trans enlargeInside
  simp only [surplus, Finset.sum_sub_distrib, <- Finset.mul_sum] at comparison
  rw [mul_sub]
  linarith only [comparison]

private theorem mul_log_le_mul_log {a b : Real} (ha : 1 < a) (hab : a <= b) :
    a * Real.log a <= b * Real.log b :=
  mul_le_mul hab ((Real.log_le_log_iff (zero_lt_one.trans ha)
    (zero_lt_one.trans (ha.trans_le hab))).mpr hab) (Real.log_nonneg ha.le)
    (zero_le_one.trans (ha.le.trans hab))

/-- Supporting-line bound for weighted prime powers with norm greater than one. -/
theorem weightedPrimePowerSupportingLine {I : Type*} [DecidableEq I]
    (occupied frontier : Finset I) (norm cost : I -> Real) (x : Real)
    (hx : 1 < x)
    (hnorm : forall i, Or (Membership.mem occupied i) (Membership.mem frontier i) -> 1 < norm i)
    (hcost : forall i, Or (Membership.mem occupied i) (Membership.mem frontier i) -> 0 <= cost i)
    (inside : forall i, Membership.mem frontier i -> norm i <= x)
    (outside : forall i, Membership.mem occupied i -> Not (Membership.mem frontier i) ->
      x <= norm i) :
    occupied.sum (fun i => cost i / (norm i * Real.log (norm i))) <=
      frontier.sum (fun i => cost i / (norm i * Real.log (norm i))) +
        (occupied.sum cost - frontier.sum cost) / (x * Real.log x) := by
  have hdenom {t : Real} (ht : 1 < t) : 0 < t * Real.log t :=
    mul_pos (zero_lt_one.trans ht) (Real.log_pos ht)
  have hInside (i : I) (hi : Membership.mem frontier i) :
      (1 / (x * Real.log x)) * cost i <= cost i / (norm i * Real.log (norm i)) := by
    have hq := hnorm i (Or.inr hi)
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
      (div_le_div_of_nonneg_left (hcost i (Or.inr hi)) (hdenom hq)
        (mul_log_le_mul_log hq (inside i hi)))
  have hOutside (i : I) (hi : Membership.mem occupied i) (hnot : Not (Membership.mem frontier i)) :
      cost i / (norm i * Real.log (norm i)) <= (1 / (x * Real.log x)) * cost i := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
      (div_le_div_of_nonneg_left (hcost i (Or.inl hi)) (hdenom hx)
        (mul_log_le_mul_log hx (outside i hi hnot)))
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
    (finiteSupportingLine occupied frontier
      (fun i => cost i / (norm i * Real.log (norm i))) cost
      (1 / (x * Real.log x)) hInside hOutside)

/-- Substitute the weighted frontier formula and cancel its first-order error exactly. -/
theorem weightedMertensBoundaryCancellation
    (payoff prefixPayoff budget prefixCost main error tail denominator : Real)
    (supporting : payoff <= prefixPayoff + (budget - prefixCost) / denominator)
    (costIdentity : prefixCost = budget + error)
    (prefixIdentity : prefixPayoff = main + error / denominator + tail) :
    payoff <= main + tail := by
  rw [costIdentity, prefixIdentity] at supporting
  have difference : budget - (budget + error) = -error := by linarith
  rw [difference, neg_div] at supporting
  linarith only [supporting]

end Robin1984.GRH
