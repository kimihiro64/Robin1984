/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
module

public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Landau's positive-transform principle

This file isolates the strict convergence step in Landau's theorem.  A
nonnegative exponential transform whose moment series converges at a positive
increment is integrable at the correspondingly larger exponent.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- A point strictly between two exponential-integrability parameters lies in
the interior of the integrability set. -/
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

/-- If the Taylor series of a nonnegative moment-generating transform at an
interior point converges at a nonnegative increment, then the transform is
integrable at the strictly later exponent. -/
theorem mem_integrableExpSet_add_of_summable_moments
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega} {a d : Real}
    (hX : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (ha : Membership.mem
      (interior (ProbabilityTheory.integrableExpSet X mu)) a)
    (hd : 0 <= d)
    (hSummable : Summable (fun n : Nat =>
      (integral mu (fun w => X w ^ n * Real.exp (a * X w)) /
          (Nat.factorial n : Real)) * d ^ n)) :
    Membership.mem (ProbabilityTheory.integrableExpSet X mu) (a + d) := by
  let term : Nat -> Omega -> Real := fun n w =>
    (d ^ n / (Nat.factorial n : Real)) *
      (X w ^ n * Real.exp (a * X w))
  have hMomentIntegrable : forall n : Nat,
      Integrable (fun w => X w ^ n * Real.exp (a * X w)) mu := by
    intro n
    exact ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
      ha n
  have hTermIntegrable : forall n : Nat, Integrable (term n) mu := by
    intro n
    exact (hMomentIntegrable n).const_mul
      (d ^ n / (Nat.factorial n : Real))
  have hTermNonneg : forall n : Nat,
      Filter.Eventually (fun w => 0 <= term n w) (ae mu) := by
    intro n
    filter_upwards [hX] with w hw
    exact mul_nonneg
      (div_nonneg (pow_nonneg hd n) (Nat.cast_nonneg (Nat.factorial n)))
      (mul_nonneg (pow_nonneg hw n) (Real.exp_pos _).le)
  have hTermIntegral : forall n : Nat,
      integral mu (term n) =
        (integral mu (fun w => X w ^ n * Real.exp (a * X w)) /
          (Nat.factorial n : Real)) * d ^ n := by
    intro n
    dsimp [term]
    rw [integral_const_mul]
    ring
  have hTermSummable : forall w : Omega, Summable (fun n : Nat => term n w) := by
    intro w
    have hExp : Summable (fun n : Nat =>
        (d * X w) ^ n / (Nat.factorial n : Real)) :=
      NormedSpace.expSeries_div_summable (d * X w)
    have hScaled := hExp.mul_left (Real.exp (a * X w))
    apply hScaled.congr
    intro n
    dsimp [term]
    rw [mul_pow]
    ring
  have hPointwise : forall w : Omega,
      Real.exp ((a + d) * X w) = tsum (fun n : Nat => term n w) := by
    intro w
    calc
      Real.exp ((a + d) * X w) =
          Real.exp (a * X w) * Real.exp (d * X w) := by
        rw [add_mul, Real.exp_add]
      _ = Real.exp (a * X w) *
          tsum (fun n : Nat =>
            (d * X w) ^ n / (Nat.factorial n : Real)) := by
        have hExpTsum : Real.exp (d * X w) =
            tsum (fun n : Nat =>
              (d * X w) ^ n / (Nat.factorial n : Real)) := by
          apply Complex.ofReal_injective
          rw [Complex.ofReal_exp, Complex.exp]
          have hCast :
              ((tsum (fun n : Nat =>
                (d * X w) ^ n / (Nat.factorial n : Real)) : Real) : Complex) =
                tsum (fun n : Nat =>
                  ((d * X w : Real) : Complex) ^ n /
                    (Nat.factorial n : Complex)) := by
            rw [Complex.ofReal_tsum]
            apply tsum_congr
            intro n
            push_cast
            rfl
          rw [hCast]
          exact tendsto_nhds_unique
            (Complex.exp' (((d * X w : Real) : Complex))).tendsto_limit
            (NormedSpace.expSeries_div_summable
              (((d * X w : Real) : Complex))).hasSum.tendsto_sum_nat
        rw [hExpTsum]
      _ = tsum (fun n : Nat =>
          Real.exp (a * X w) *
            ((d * X w) ^ n / (Nat.factorial n : Real))) := by
        rw [<- (NormedSpace.expSeries_div_summable
          (d * X w)).tsum_mul_left]
      _ = tsum (fun n : Nat => term n w) := by
        apply tsum_congr
        intro n
        dsimp [term]
        rw [mul_pow]
        ring
  change Integrable (fun w => Real.exp ((a + d) * X w)) mu
  have hXMeasurable : AEMeasurable X mu :=
    ProbabilityTheory.aemeasurable_of_mem_interior_integrableExpSet ha
  refine And.intro
    ((Real.measurable_exp.comp_aemeasurable
      (hXMeasurable.const_mul (a + d))).aestronglyMeasurable) ?_
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun w => (Real.exp_pos _).le))]
  calc
    lintegral mu (fun w => ENNReal.ofReal (Real.exp ((a + d) * X w))) =
        lintegral mu (fun w => tsum (fun n : Nat =>
          ENNReal.ofReal (term n w))) := by
      apply lintegral_congr_ae
      filter_upwards [hX] with w hw
      rw [hPointwise w]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun n => by
          dsimp [term]
          exact mul_nonneg
            (div_nonneg (pow_nonneg hd n)
              (Nat.cast_nonneg (Nat.factorial n)))
            (mul_nonneg (pow_nonneg hw n) (Real.exp_pos _).le))
        (hTermSummable w)
    _ = tsum (fun n : Nat =>
        lintegral mu (fun w => ENNReal.ofReal (term n w))) := by
      rw [lintegral_tsum]
      intro n
      exact (hTermIntegrable n).aemeasurable.ennreal_ofReal
    _ = tsum (fun n : Nat => ENNReal.ofReal
        ((integral mu (fun w => X w ^ n * Real.exp (a * X w)) /
          (Nat.factorial n : Real)) * d ^ n)) := by
      apply tsum_congr
      intro n
      rw [<- ofReal_integral_eq_lintegral_ofReal
        (hTermIntegrable n) (hTermNonneg n), hTermIntegral]
    _ < Top.top := hSummable.tsum_ofReal_lt_top

/-- A regular analytic continuation transfers its larger power-series radius
to the explicit nonnegative moment series.  Consequently every nonnegative
increment lying in that analytic ball belongs to the true exponential
integrability set. -/
theorem mem_integrableExpSet_add_of_analyticContinuationOnBall
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega} {a d : Real}
    {H : Real -> Real} {p : FormalMultilinearSeries Real Real Real}
    {r : ENNReal}
    (hX : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (ha : Membership.mem
      (interior (ProbabilityTheory.integrableExpSet X mu)) a)
    (hH : HasFPowerSeriesOnBall H p a r)
    (hEq : Filter.EventuallyEq (nhds a) (ProbabilityTheory.mgf X mu) H)
    (hd : 0 <= d)
    (hdBall : Membership.mem (Metric.eball a r) (a + d)) :
    Membership.mem (ProbabilityTheory.integrableExpSet X mu) (a + d) := by
  let q : FormalMultilinearSeries Real Real Real :=
    FormalMultilinearSeries.ofScalars Real (fun n : Nat =>
      (integral mu (fun w => X w ^ n * Real.exp (a * X w)) /
        (Nat.factorial n : Real)))
  have hMgf : HasFPowerSeriesAt (ProbabilityTheory.mgf X mu) q a := by
    dsimp [q]
    exact ProbabilityTheory.hasFPowerSeriesAt_mgf ha
  have hHq : HasFPowerSeriesAt H q a := hMgf.congr hEq
  choose rq hHqBall using hHq
  have hTransferred : HasFPowerSeriesOnBall H q a r :=
    hHqBall.exchange_radius hH
  have hSeries := hTransferred.hasSum_sub hdBall
  have hSummable : Summable (fun n : Nat =>
      (integral mu (fun w => X w ^ n * Real.exp (a * X w)) /
        (Nat.factorial n : Real)) * d ^ n) := by
    apply hSeries.summable.congr
    intro n
    dsimp [q]
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [add_sub_cancel_left, smul_eq_mul]
  exact mem_integrableExpSet_add_of_summable_moments hX ha hd hSummable

/-- Recenter an analytic continuation from a frontier `sigma` to a genuinely
convergent point `a`.  If the continuation ball reaches a point strictly to
the right of `sigma`, then the nonnegative transform really converges there.
The returned conjunction records the strict crossing explicitly. -/
theorem integrableExpSet_strict_crossing_of_analyticContinuationOnBall
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    {a d sigma : Real} {H : Real -> Real}
    {p : FormalMultilinearSeries Real Real Real} {r : ENNReal}
    (hX : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (ha : Membership.mem
      (interior (ProbabilityTheory.integrableExpSet X mu)) a)
    (hH : HasFPowerSeriesOnBall H p sigma r)
    (haCenter : enorm (a - sigma) < r)
    (hEq : Filter.EventuallyEq (nhds a) (ProbabilityTheory.mgf X mu) H)
    (hd : 0 < d)
    (hCross : sigma < a + d)
    (hTarget : Membership.mem
      (Metric.eball a (r - enorm (a - sigma))) (a + d)) :
    And (sigma < a + d)
      (Membership.mem (ProbabilityTheory.integrableExpSet X mu) (a + d)) := by
  have hRecentered : HasFPowerSeriesOnBall H
      (p.changeOrigin (a - sigma)) a (r - enorm (a - sigma)) := by
    have hShift := hH.changeOrigin haCenter
    convert hShift using 1
    . ring
    . simp [enorm_eq_nnnorm]
  exact And.intro hCross
    (mem_integrableExpSet_add_of_analyticContinuationOnBall
      hX ha hRecentered hEq hd.le hTarget)

/-- Landau's strict local conclusion in frontier form.  If every real
exponent below `sigma` is a genuine convergence point and the transform has a
real-analytic continuation through `sigma`, then convergence holds at some
strictly larger real exponent. -/
theorem exists_integrableExpSet_gt_of_analyticContinuationAt
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    {sigma : Real} {H : Real -> Real}
    (hX : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (hBelow : forall a : Real, a < sigma ->
      Membership.mem
        (interior (ProbabilityTheory.integrableExpSet X mu)) a)
    (hH : AnalyticAt Real H sigma)
    (hEq : forall a : Real, a < sigma ->
      ProbabilityTheory.mgf X mu a = H a) :
    Exists fun t : Real => And (sigma < t)
      (Membership.mem (ProbabilityTheory.integrableExpSet X mu) t) := by
  choose p hp using hH
  choose r hBall using hp
  let r0 : ENNReal := min r 1
  have hr0Pos : 0 < r0 := by
    exact lt_min hBall.r_pos zero_lt_one
  have hr0Top : Not (r0 = Top.top) := by
    exact ne_of_lt (lt_of_le_of_lt (min_le_right r 1) ENNReal.one_lt_top)
  have hSmallBall : HasFPowerSeriesOnBall H p sigma r0 :=
    hBall.mono hr0Pos (min_le_left r 1)
  let R : Real := r0.toReal
  have hRPos : 0 < R := ENNReal.toReal_pos hr0Pos.ne' hr0Top
  have hRNonneg : 0 <= R := hRPos.le
  have hr0Eq : ENNReal.ofReal R = r0 := by
    exact ENNReal.ofReal_toReal hr0Top
  let eps : Real := R / 4
  let a : Real := sigma - eps
  let d : Real := 2 * eps
  have hEpsPos : 0 < eps := by
    dsimp [eps]
    positivity
  have hAPos : a < sigma := by
    dsimp [a]
    linarith
  have ha : Membership.mem
      (interior (ProbabilityTheory.integrableExpSet X mu)) a :=
    hBelow a hAPos
  have hEqNhd : Filter.EventuallyEq (nhds a)
      (ProbabilityTheory.mgf X mu) H := by
    filter_upwards [Iio_mem_nhds hAPos] with x hx
    exact hEq x hx
  have haCenter : enorm (a - sigma) < r0 := by
    rw [<- hr0Eq]
    rw [Real.enorm_eq_ofReal_abs]
    rw [ENNReal.ofReal_lt_ofReal_iff hRPos]
    dsimp [a, eps]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hdPos : 0 < d := by
    dsimp [d]
    positivity
  have hCross : sigma < a + d := by
    dsimp [a, d]
    linarith
  have hTarget : Membership.mem
      (Metric.eball a (r0 - enorm (a - sigma))) (a + d) := by
    rw [Metric.mem_eball, edist_dist]
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hdPos.le]
    rw [Real.enorm_eq_ofReal_abs]
    rw [abs_of_nonpos (by dsimp [a]; linarith : a - sigma <= 0)]
    rw [neg_sub]
    rw [<- hr0Eq, <- ENNReal.ofReal_sub R
      (by dsimp [a]; linarith : 0 <= sigma - a)]
    rw [ENNReal.ofReal_lt_ofReal_iff]
    . dsimp [a, d, eps]
      linarith
    . dsimp [a, eps]
      linarith
  have hStrict :=
    integrableExpSet_strict_crossing_of_analyticContinuationOnBall
      hX ha hSmallBall haCenter hEqNhd hdPos hCross hTarget
  exact Exists.intro (a + d) hStrict

end

end ProbabilityTheory
