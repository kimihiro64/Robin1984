import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Local orders of analytic functions, the analytic identity theorem, and the sign of a real Laplace or Mellin transform of a nonnegative function.
- Formalization note: These lemmas separate the zero and residue obstructions used in the converse to the generalized Robin criteria.
- PROVENANCE-END
-/

/-!
# Obstructions for a holomorphic logarithmic derivative

A holomorphic extension of a logarithmic derivative excludes zeros of the
underlying function. On a real ray, a nonnegative transform also excludes
a negative real residue at a putative convergence boundary.
-/

open Filter Set

namespace Robin1984.GRH

/-- An analytic logarithmic derivative on a connected open domain forces nonvanishing. -/
theorem ne_zero_of_analyticLogDerivative
    {domain : Set Complex} {f g : Complex -> Complex}
    (hOpen : IsOpen domain) (hConnected : IsPreconnected domain)
    (hf : AnalyticOnNhd Complex f domain) (hg : AnalyticOnNhd Complex g domain)
    (initial : exists w : Complex,
      And (Membership.mem domain w) (Filter.EventuallyEq (nhds w) (deriv f) (f * g)))
    (nonzero : exists w : Complex, And (Membership.mem domain w) (Not (f w = 0)))
    {z : Complex} (hz : Membership.mem domain z) :
    Not (f z = 0) := by
  choose base hbase using initial
  choose witness hwitness using nonzero
  have hDeriv : AnalyticOnNhd Complex (deriv f) domain :=
    fun w hw => (hf w hw).deriv
  have hMul : AnalyticOnNhd Complex (f * g) domain :=
    fun w hw => (hf w hw).mul (hg w hw)
  have hIdentity := hDeriv.eqOn_of_preconnected_of_eventuallyEq hMul hConnected hbase.1 hbase.2
  intro hZero
  have hFinite : Not (analyticOrderAt f z = (Top.top : ENat)) := by
    intro hTop
    have hLocalZero : Filter.EventuallyEq (nhds z) f (fun _ => (0 : Complex)) :=
      analyticOrderAt_eq_top.mp hTop
    have hConstant : AnalyticOnNhd Complex (fun _ : Complex => (0 : Complex)) domain :=
      fun _ _ => analyticAt_const
    have hAllZero := hf.eqOn_of_preconnected_of_eventuallyEq hConstant hConnected hz hLocalZero
    exact hwitness.2 (hAllZero hwitness.1)
  have hSubtract : (fun w => f w - f z) = f := by
    funext w
    rw [hZero, sub_zero]
  have hDomain : Filter.Eventually (fun w => Membership.mem domain w) (nhds z) :=
    hOpen.mem_nhds hz
  have hLocalIdentity : Filter.EventuallyEq (nhds z) (deriv f) (f * g) :=
    hDomain.mono (fun _ hw => hIdentity hw)
  have hOrder := (hf z hz).analyticOrderAt_deriv_add_one
  rw [hSubtract, analyticOrderAt_congr hLocalIdentity,
    analyticOrderAt_mul (hf z hz) (hg z hz), add_assoc] at hOrder
  have hZeroOrder : analyticOrderAt g z + 1 = 0 :=
    ENat.add_right_injective_of_ne_top hFinite (by simpa only [add_zero] using hOrder)
  simp at hZeroOrder

/-- A function nonnegative to the right of a real point has a nonnegative residue there. -/
theorem residue_nonneg_of_eventually_nonnegative
    {boundary residue : Real} {F : Real -> Real}
    (hPositive : Filter.Eventually (fun s => 0 <= F s) (nhdsWithin boundary (Set.Ioi boundary)))
    (hResidue : Filter.Tendsto (fun s => (s - boundary) * F s)
      (nhdsWithin boundary (Set.Ioi boundary)) (nhds residue)) :
    0 <= residue := by
  have hRight : Filter.Eventually (fun s => boundary < s) (nhdsWithin boundary (Set.Ioi boundary)) :=
    self_mem_nhdsWithin
  exact ge_of_tendsto hResidue ((hRight.and hPositive).mono (fun _ h =>
    mul_nonneg (sub_nonneg.mpr h.1.le) h.2))

end Robin1984.GRH
