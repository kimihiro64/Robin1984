import Robin1984.NicolasLandau.LandauMellinPrinciple

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# Nicolas-Landau convergence frontier

This file propagates a nonnegative exponential transform through every real
point at which its analytic continuation remains regular.  The proof keeps
the complete integrability set and uses its supremum; no local crossing is
mistaken for the global conclusion.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem mem_interior_integrableExpSet_of_two_sided
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    {l a r : Real}
    (hl : Membership.mem (integrableExpSet X mu) l)
    (hr : Membership.mem (integrableExpSet X mu) r)
    (hla : l < a) (har : a < r) :
    Membership.mem (interior (integrableExpSet X mu)) a := by
  rw [mem_interior_iff_mem_nhds]
  let eps : Real := min (a - l) (r - a) / 2
  have hMinPos : 0 < min (a - l) (r - a) :=
    lt_min (sub_pos.mpr hla) (sub_pos.mpr har)
  have hEpsPos : 0 < eps := by
    dsimp [eps]
    positivity
  apply mem_of_superset (Metric.ball_mem_nhds a hEpsPos)
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hEpsLeft : eps <= a - l := by
    dsimp [eps]
    have hMinLe := min_le_left (a - l) (r - a)
    linarith
  have hEpsRight : eps <= r - a := by
    dsimp [eps]
    have hMinLe := min_le_right (a - l) (r - a)
    linarith
  have hyLeft : l <= y := by
    have hyLower := (abs_lt.mp hy).1
    linarith
  have hyRight : y <= r := by
    have hyUpper := (abs_lt.mp hy).2
    linarith
  exact convex_integrableExpSet.ordConnected.out hl hr
    (And.intro hyLeft hyRight)

theorem Iio_subset_interior_integrableExpSet_of_analyticContinuation
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    {b : Real} {H : Real -> Real}
    (hX : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (hNeg : forall a : Real, a < 0 ->
      Membership.mem (interior (integrableExpSet X mu)) a)
    (hH : forall sigma : Real, sigma < b -> AnalyticAt Real H sigma)
    (hEqNeg : forall a : Real, a < 0 -> mgf X mu a = H a) :
    Iio b <= interior (integrableExpSet X mu) := by
  intro sigma hSigma
  let E : Set Real := integrableExpSet X mu
  let A : Set Real := Set.inter E (Iic sigma)
  let l0 : Real := min (-1) (sigma - 1)
  have hl0Neg : l0 < 0 := by
    dsimp [l0]
    exact lt_of_le_of_lt (min_le_left (-1 : Real) (sigma - 1)) (by norm_num)
  have hl0Sigma : l0 <= sigma := by
    dsimp [l0]
    have hLe := min_le_right (-1 : Real) (sigma - 1)
    linarith
  have hl0E : Membership.mem E l0 := by
    exact interior_subset (hNeg l0 hl0Neg)
  have hANonempty : A.Nonempty :=
    Exists.intro l0 (And.intro hl0E hl0Sigma)
  have hABdd : BddAbove A := by
    exact Exists.intro sigma (fun y hy => hy.2)
  let c : Real := sSup A
  have hcSigma : c <= sigma := by
    dsimp [c]
    exact csSup_le hANonempty (fun y hy => hy.2)
  have hcB : c < b := lt_of_le_of_lt hcSigma hSigma
  have hBelow : forall a : Real, a < c ->
      Membership.mem (interior E) a := by
    intro a ha
    choose r hrA har using (lt_csSup_iff hABdd hANonempty).1 ha
    let l : Real := min (a - 1) (-1)
    have hlNeg : l < 0 := by
      dsimp [l]
      exact lt_of_le_of_lt (min_le_right (a - 1) (-1 : Real)) (by norm_num)
    have hla : l < a := by
      dsimp [l]
      have hLe := min_le_left (a - 1) (-1 : Real)
      linarith
    have hlE : Membership.mem E l := interior_subset (hNeg l hlNeg)
    exact mem_interior_integrableExpSet_of_two_sided
      hlE hrA.1 hla har
  have hMgfAnalytic : AnalyticOnNhd Real (mgf X mu) (Iio c) := by
    intro a ha
    exact analyticAt_mgf (hBelow a ha)
  have hContinuationAnalytic : AnalyticOnNhd Real H (Iio c) := by
    intro a ha
    exact hH a (lt_trans ha hcB)
  let z0 : Real := min (-1) (c - 1)
  have hz0Neg : z0 < 0 := by
    dsimp [z0]
    exact lt_of_le_of_lt (min_le_left (-1 : Real) (c - 1)) (by norm_num)
  have hz0C : z0 < c := by
    dsimp [z0]
    have hLe := min_le_right (-1 : Real) (c - 1)
    linarith
  have hEqNhd : Filter.EventuallyEq (nhds z0) (mgf X mu) H := by
    filter_upwards [Iio_mem_nhds hz0Neg] with a ha
    exact hEqNeg a ha
  have hEqOn : EqOn (mgf X mu) H (Iio c) :=
    hMgfAnalytic.eqOn_of_preconnected_of_eventuallyEq
      hContinuationAnalytic (convex_Iio c).isPreconnected hz0C hEqNhd
  have hEqBelow : forall a : Real, a < c -> mgf X mu a = H a := by
    intro a ha
    exact hEqOn ha
  choose t hct htE using
    exists_integrableExpSet_gt_of_analyticContinuationAt
      hX hBelow (hH c hcB) hEqBelow
  by_cases hSigmaT : sigma < t
  . let l : Real := min (sigma - 1) (-1)
    have hlNeg : l < 0 := by
      dsimp [l]
      exact lt_of_le_of_lt
        (min_le_right (sigma - 1) (-1 : Real)) (by norm_num)
    have hlSigma : l < sigma := by
      dsimp [l]
      have hLe := min_le_left (sigma - 1) (-1 : Real)
      linarith
    have hlE : Membership.mem E l := interior_subset (hNeg l hlNeg)
    exact mem_interior_integrableExpSet_of_two_sided
      hlE htE hlSigma hSigmaT
  . have htSigma : t <= sigma := le_of_not_gt hSigmaT
    have htA : Membership.mem A t := And.intro htE htSigma
    have htc : t <= c := by
      dsimp [c]
      exact le_csSup hABdd htA
    exact (not_lt_of_ge htc hct).elim

end

end Robin1984
