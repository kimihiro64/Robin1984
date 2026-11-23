import Robin1984.GRH.MellinUniqueness
import Robin1984.GRH.ZeroSeriesSymmetry

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Mellin uniqueness for the triangular explicit formula and the square-root bound for a summable zero expansion.
- Formalization note: Equality of the known transforms is converted to an almost-everywhere equality and continuity of the remainder gives the pointwise bound.
- PROVENANCE-END
-/

/-!
# From the canonical zero transform to the triangular bound

The contour calculation is isolated as a transform identity. Its
zero terms determine the real-domain remainder by Mellin uniqueness.
-/

open Filter MeasureTheory Set

namespace Robin1984.GRH

/-- The integrand for the Mellin transform of a real function at s. -/
noncomputable def realMellinIntegrand (u : Real -> Real) (s : Complex) (x : Real) : Complex :=
  (u x : Complex) * (x : Complex) ^ (-s - 1)

/-- A continuous real function satisfies a square-root bound everywhere on
an open tail if it satisfies the bound almost everywhere there. -/
theorem pointwise_sqrtBound_of_ae {R : Real -> Real} {C : Real}
    (hContinuity : ContinuousOn R (Ioi 1))
    (hAE : Filter.Eventually (fun x => R x <= C * Real.sqrt x)
      (ae (volume.restrict (Ioi (1 : Real))))) {x : Real} (hx : 1 < x) :
    R x <= C * Real.sqrt x := by
  by_contra hBad
  have hCut : Membership.mem (Ioi (1 : Real)) x := hx
  have hInside : Membership.mem (nhds x) (Ioi (1 : Real)) := isOpen_Ioi.mem_nhds hCut
  have hR : ContinuousAt R x := (hContinuity x hCut).continuousAt hInside
  have hB : ContinuousAt (fun y : Real => C * Real.sqrt y) x :=
    continuousAt_const.mul Real.continuous_sqrt.continuousAt
  let U : Set Real := {y : Real | And (1 < y) (C * Real.sqrt y < R y)}
  have hEventually : Filter.Eventually (fun y : Real => 1 < y) (nhds x) := hInside
  have hU : Membership.mem (nhds x) U := hEventually.and
    (hB.eventually_lt hR (lt_of_not_ge hBad))
  choose eps heps using Metric.mem_nhds_iff.mp hU
  have hFull := (ae_restrict_iff' measurableSet_Ioi).mp hAE
  have hNull : volume U = 0 := measure_eq_zero_iff_ae_notMem.mpr
    (hFull.mono (fun y hy hyU => (not_lt_of_ge (hy hyU.1)) hyU.2))
  have hBall : Not (volume (Metric.ball x eps) = 0) :=
    Metric.isOpen_ball.measure_ne_zero (volume : Measure Real)
      (Set.nonempty_of_mem (Metric.mem_ball_self heps.1))
  exact hBall (measure_mono_null heps.2 hNull)

/-- An exact canonical zero expansion of the Mellin transform, with a
real zero sum and a controlled residual term, implies the triangular
square-root bound. -/
theorem triangularSquareRootBound_of_canonicalMellin
    {iota : Type*} [Countable iota] (rho : iota -> Complex) (e : Equiv iota iota)
    (hConj : forall i, rho (e i) = (starRingEnd Complex) (rho i))
    {R E : Real -> Real} (hRMeas : Measurable R) (hEMeas : Measurable E)
    (hRCont : ContinuousOn R (Ioi 1))
    (hRho : forall i, (rho i).re <= 1 / 2)
    (hRho0 : forall i, Not (rho i = 0)) (hRho1 : forall i, Not (rho i + 1 = 0))
    (hSummable : Summable (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)))
    (hRInt : forall s : Complex, 1 < s.re -> Integrable (realMellinIntegrand R s)
      (volume.restrict (Ioi (1 : Real))))
    (hEInt : forall s : Complex, 1 < s.re -> Integrable (realMellinIntegrand E s)
      (volume.restrict (Ioi (1 : Real))))
    (hEq : forall s : Complex, 1 < s.re ->
      integral (volume.restrict (Ioi (1 : Real))) (realMellinIntegrand R s) =
        integral (volume.restrict (Ioi (1 : Real))) (realMellinIntegrand E s) +
          tsum (fun i => 1 / (s - rho i) + 1 / rho i) / (s * (s + 1)))
    {C : Real} (hEBound : forall x : Real, 1 < x -> E x <= C * Real.sqrt x)
    {x : Real} (hx : 1 < x) :
    R x <= (C + 2 * tsum (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int))) *
      Real.sqrt x := by
  let mu := volume.restrict (Ioi (1 : Real))
  let S := fun x : Real => tsum (fun i => triangularZeroTerm (rho i) x)
  let U : Real -> Real := fun x => R x - E x - (S x).re
  have hUMeas : Measurable U :=
    (hRMeas.sub hEMeas).sub (measurable_re_triangularZeroSum rho)
  have hSModel (s : Complex) :
      Filter.EventuallyEq (ae mu) (realMellinIntegrand (fun x => (S x).re) s)
        (fun x => S x * (x : Complex) ^ (-s - 1)) := by
    have hTail : Filter.Eventually (fun x : Real => 1 < x) (ae mu) :=
      ae_restrict_mem measurableSet_Ioi
    refine hTail.mono (fun x hx => ?_)
    have hCast : ((S x).re : Complex) = S x := by
      apply Complex.ext
      exact Complex.ofReal_re _
      rw [Complex.ofReal_im, im_triangularZeroSum_eq_zero rho e hConj (zero_lt_one.trans hx)]
    change ((S x).re : Complex) * (x : Complex) ^ (-s - 1) =
      S x * (x : Complex) ^ (-s - 1)
    rw [hCast]
  have hUAll (s : Complex) (hs : 1 < s.re) :
      And (Integrable (realMellinIntegrand U s) mu) (integral mu (realMellinIntegrand U s) = 0) := by
    have hZeroSum := triangularZeroSeries_mellin rho hRho hRho0 hRho1 hSummable s hs
    have hSInt : Integrable (realMellinIntegrand (fun x => (S x).re) s) mu :=
      hZeroSum.1.congr (hSModel s).symm
    have hSValue := (integral_congr_ae (hSModel s)).trans hZeroSum.2
    have hSplit : realMellinIntegrand U s =
      fun x => realMellinIntegrand R s x - realMellinIntegrand E s x -
        realMellinIntegrand (fun y => (S y).re) s x := by
      funext x
      simp only [realMellinIntegrand, U, Complex.ofReal_sub, sub_mul]
    rw [hSplit]
    refine And.intro (((hRInt s hs).sub (hEInt s hs)).sub hSInt) ?_
    calc
      _ = integral mu (fun x => realMellinIntegrand R s x - realMellinIntegrand E s x) -
          integral mu (realMellinIntegrand (fun y => (S y).re) s) :=
        integral_sub ((hRInt s hs).sub (hEInt s hs)) hSInt
      _ = integral mu (realMellinIntegrand R s) - integral mu (realMellinIntegrand E s) -
          integral mu (realMellinIntegrand (fun y => (S y).re) s) := by
        rw [integral_sub (hRInt s hs) (hEInt s hs)]
      _ = 0 := by
        have hEqMu : integral mu (realMellinIntegrand R s) =
            integral mu (realMellinIntegrand E s) +
              tsum (fun i => 1 / (s - rho i) + 1 / rho i) / (s * (s + 1)) := hEq s hs
        rw [hEqMu, hSValue]
        ring
  have hTwo : 1 < (((2 : Real) : Complex)).re := by rw [Complex.ofReal_re]; exact one_lt_two
  have hWeight : Integrable (fun x : Real => U x * x ^ (-(2 : Real) - 1)) mu := by
    have hOfReal : IntegrableOn (fun x : Real =>
        (realMellinIntegrand U ((2 : Real) : Complex) x).re) (Ioi (1 : Real)) :=
      (hUAll ((2 : Real) : Complex) hTwo).1.re
    refine hOfReal.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := zero_lt_one.trans hx
    change ((U x : Complex) * (x : Complex) ^ (-((2 : Real) : Complex) - 1)).re =
      U x * x ^ (-(2 : Real) - 1)
    rw [show -((2 : Real) : Complex) - 1 = ((-(2 : Real) - 1 : Real) : Complex) by norm_cast,
      <- Complex.ofReal_cpow hx0.le, <- Complex.ofReal_mul, Complex.ofReal_re]
  have hVertical (t : Real) : integral mu (fun x : Real => (U x : Complex) *
      (x : Complex) ^ (-((2 : Real) : Complex) - 1 + (t : Complex) * Complex.I)) = 0 := by
    let s : Complex := ((2 : Real) : Complex) - (t : Complex) * Complex.I
    have hs : 1 < s.re := by
      simpa only [s, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] using (one_lt_two : (1 : Real) < 2)
    have hExponent : -((2 : Real) : Complex) - 1 + (t : Complex) * Complex.I = -s - 1 := by
      unfold s
      ring
    rw [hExponent]
    exact (hUAll s hs).2
  have hAE := ae_zero_of_verticalMellin_eq_zero hUMeas 2 hWeight hVertical
  have hTail : Filter.Eventually (fun x : Real => 1 < x) (ae mu) :=
    ae_restrict_mem measurableSet_Ioi
  apply pointwise_sqrtBound_of_ae hRCont _ hx
  filter_upwards [hAE, hTail] with y hy hyTail
  change R y - E y - (S y).re = 0 at hy
  have hNorm : norm (S y) <= (2 * Real.sqrt y) *
      tsum (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)) :=
    norm_tsum_triangularZeroTerm_le rho hRho hSummable hyTail.le
  have hReal := Complex.re_le_norm (S y)
  have hE := hEBound y hyTail
  have hStep :
      2 * Real.sqrt y * tsum (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)) =
        (2 * tsum (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int))) * Real.sqrt y := by ring
  rw [hStep] at hNorm
  rw [add_mul]
  linarith only [hy, hNorm, hReal, hE]

end Robin1984.GRH
