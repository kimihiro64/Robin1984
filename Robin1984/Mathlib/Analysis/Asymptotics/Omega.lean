/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Omega-scale transfer in Robin's converse implication

This file isolates the exact global scale comparison used after Nicolas's
two-sided oscillation.  All excursions occur arbitrarily far out at `atTop`;
there is no fixed frontier or pointwise positivity hypothesis.
-/

@[expose] public section

namespace Asymptotics

open Asymptotics Filter

noncomputable section

/-- `g` has positive excursions of size at least a fixed positive multiple of
`h` arbitrarily far out. -/
def AtTopOmegaPlus (g h : Real -> Real) : Prop :=
  Exists fun c : Real =>
    0 < c /\
      forall X : Real, Exists fun x : Real => X <= x /\ c * h x <= g x

/-- `g` has negative excursions of size at least a fixed positive multiple of
`h` arbitrarily far out. -/
def AtTopOmegaMinus (g h : Real -> Real) : Prop :=
  AtTopOmegaPlus (fun x => -g x) h

/-- Adding an error that is little-o of a positive scale preserves positive
Omega excursions, with half of the original excursion constant. -/
theorem AtTopOmegaPlus.add_isLittleO
    {g e h : Real -> Real}
    (hg : AtTopOmegaPlus g h)
    (hPos : Filter.Eventually (fun x => 0 < h x) Filter.atTop)
    (he : Asymptotics.IsLittleO Filter.atTop e h) :
    AtTopOmegaPlus (fun x => g x + e x) h := by
  choose c hc hLarge using hg
  refine Exists.intro (c / 2) (And.intro (half_pos hc) ?_)
  intro X
  have hError : Filter.Eventually
      (fun x => |e x| <= (c / 2) * |h x|) Filter.atTop := by
    simpa only [Real.norm_eq_abs] using he.bound (half_pos hc)
  choose Y hY using Filter.eventually_atTop.mp (hError.and hPos)
  choose x hx hMain using hLarge (max X Y)
  refine Exists.intro x (And.intro (le_trans (le_max_left X Y) hx) ?_)
  have hxY : Y <= x := le_trans (le_max_right X Y) hx
  have hErrorX := (hY x hxY).1
  have hScaleX := (hY x hxY).2
  rw [abs_of_pos hScaleX] at hErrorX
  have hErrorLower : -(c / 2) * h x <= e x := by
    calc
      -(c / 2) * h x <= -|e x| := by linarith
      _ <= e x := neg_abs_le (e x)
  linarith

/-- Adding an error that is little-o of a positive scale preserves negative
Omega excursions, with half of the original excursion constant. -/
theorem AtTopOmegaMinus.add_isLittleO
    {g e h : Real -> Real}
    (hg : AtTopOmegaMinus g h)
    (hPos : Filter.Eventually (fun x => 0 < h x) Filter.atTop)
    (he : Asymptotics.IsLittleO Filter.atTop e h) :
    AtTopOmegaMinus (fun x => g x + e x) h := by
  unfold AtTopOmegaMinus at hg
  unfold AtTopOmegaMinus
  choose c hc hLarge using hg
  refine Exists.intro (c / 2) (And.intro (half_pos hc) ?_)
  intro X
  have hError : Filter.Eventually
      (fun x => |e x| <= (c / 2) * |h x|) Filter.atTop := by
    simpa only [Real.norm_eq_abs] using he.bound (half_pos hc)
  choose Y hY using Filter.eventually_atTop.mp (hError.and hPos)
  choose x hx hMain using hLarge (max X Y)
  refine Exists.intro x (And.intro (le_trans (le_max_left X Y) hx) ?_)
  have hxY : Y <= x := le_trans (le_max_right X Y) hx
  have hErrorX := (hY x hxY).1
  have hScaleX := (hY x hxY).2
  rw [abs_of_pos hScaleX] at hErrorX
  have hErrorUpper : e x <= (c / 2) * h x := by
    calc
      e x <= |e x| := le_abs_self (e x)
      _ <= (c / 2) * h x := hErrorX
  dsimp only
  linarith

/-- If `b < 1/2`, then the deterministic square-root scale is little-o of
the Nicolas scale `x^(-b)` at infinity. -/
theorem rpow_neg_oneHalf_isLittleO_rpow_neg
    {b : Real} (hb : b < 1 / 2) :
    Asymptotics.IsLittleO Filter.atTop
      (fun x : Real => x ^ (-(1 / 2 : Real)))
      (fun x : Real => x ^ (-b)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hDecay : Filter.Tendsto
      (fun x : Real => x ^ (-((1 / 2 : Real) - b)))
      Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hSmall : Filter.Eventually
      (fun x : Real => x ^ (-((1 / 2 : Real) - b)) < c)
      Filter.atTop := hDecay.eventually_lt_const hc
  filter_upwards [hSmall, Filter.eventually_gt_atTop (0 : Real)] with x hxSmall hxPos
  have hHalfPos : 0 < x ^ (-(1 / 2 : Real)) :=
    Real.rpow_pos_of_pos hxPos _
  have hMainPos : 0 < x ^ (-b) := Real.rpow_pos_of_pos hxPos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hHalfPos,
    abs_of_pos hMainPos]
  have hFactor :
      x ^ (-(1 / 2 : Real)) =
        x ^ (-b) * x ^ (-((1 / 2 : Real) - b)) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  rw [hFactor]
  calc
    x ^ (-b) * x ^ (-((1 / 2 : Real) - b)) <= x ^ (-b) * c :=
      mul_le_mul_of_nonneg_left hxSmall.le hMainPos.le
    _ = c * x ^ (-b) := by ring


end

end Asymptotics
