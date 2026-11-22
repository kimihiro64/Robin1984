import Mathlib.Probability.Moments.ComplexMGF
import Robin1984.GRH.LogDerivative
import Robin1984.GRH.LogDerivativeResidue

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Landau's nonnegative transform method applied to the logarithmic derivative with triangular smoothing.
- Formalization note: An actual zero yields a strictly negative real residue. A holomorphic transform on a half-plane then excludes complex zeros of the pole-removed function.
- PROVENANCE-END
-/

/-!
# The smoothed convergence obstruction

The kernel for triangular smoothing is the reciprocal of `s * (s + 1)`.
Its sign on the positive real axis gives the sign required at a zero.
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace Robin1984.GRH

/-- The real comparison transform at a positive zero has a strictly
negative residue for the triangular Mellin kernel. -/
theorem negative_residue_of_triangularLogDerivative
    {f A : Complex -> Complex} {beta : Real} (hBeta : 0 < beta)
    (hf : AnalyticAt Complex f (beta : Complex))
    (hZero : f (beta : Complex) = 0)
    (hGerm : Not (Filter.Eventually (fun w => f w = 0) (nhds (beta : Complex))))
    (hA : ContinuousAt A (beta : Complex)) :
    exists residue : Real, And (residue < 0)
      (Tendsto
        (fun s : Real => (s - beta) *
          (A (s : Complex) - logDeriv f (s : Complex) /
            ((s : Complex) * ((s : Complex) + 1))).re)
        (nhdsWithin beta (Ioi beta)) (nhds residue)) := by
  choose n hn using tendsto_scaled_logDeriv_at_zero hf hZero hGerm
  have hDenPos : 0 < beta * (beta + 1) := mul_pos hBeta (add_pos hBeta zero_lt_one)
  have hDen : Not ((beta : Complex) * ((beta : Complex) + 1) = 0) := by
    exact_mod_cast hDenPos.ne'
  have hIncl : Tendsto (fun s : Real => (s : Complex)) (nhdsWithin beta (Ioi beta))
      (nhdsWithin (beta : Complex) {w : Complex | Not (w = (beta : Complex))}) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine And.intro (Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) ?_
    have hRight : Filter.Eventually (fun s : Real => beta < s) (nhdsWithin beta (Ioi beta)) :=
      self_mem_nhdsWithin
    exact hRight.mono (fun s hs h => hs.ne (Complex.ofReal_injective h).symm)
  have hAnalyticPart : Tendsto
      (fun w : Complex => (w - (beta : Complex)) * A w) (nhds (beta : Complex)) (nhds 0) := by
    have hContinuous : ContinuousAt (fun w : Complex => (w - (beta : Complex)) * A w)
        (beta : Complex) := (continuousAt_id.sub continuousAt_const).mul hA
    simpa only [sub_self, zero_mul] using
      hContinuous.tendsto
  have hDenLimit : Tendsto (fun w : Complex => w * (w + 1)) (nhds (beta : Complex))
      (nhds ((beta : Complex) * ((beta : Complex) + 1))) :=
    (continuousAt_id.mul (continuousAt_id.add continuousAt_const)).tendsto
  have hLimit : Tendsto
      (fun w : Complex => (w - (beta : Complex)) *
        (A w - logDeriv f w / (w * (w + 1))))
      (nhdsWithin (beta : Complex) {w : Complex | Not (w = (beta : Complex))})
      (nhds (0 - (n : Complex) / ((beta : Complex) * ((beta : Complex) + 1)))) := by
    refine ((hAnalyticPart.mono_left nhdsWithin_le_nhds).sub
      (hn.2.div (hDenLimit.mono_left nhdsWithin_le_nhds) hDen)).congr' ?_
    exact Filter.Eventually.of_forall (fun w => by
      change (w - (beta : Complex)) * A w - (w - (beta : Complex)) * logDeriv f w / (w * (w + 1))
        = (w - (beta : Complex)) * (A w - logDeriv f w / (w * (w + 1)))
      rw [mul_sub, mul_div_assoc])
  have hReal := Complex.continuous_re.continuousAt.tendsto.comp (hLimit.comp hIncl)
  have hNum : 0 < (n : Real) := by exact_mod_cast hn.1
  refine Exists.intro (0 - (n : Real) / (beta * (beta + 1)))
    (And.intro (sub_neg.mpr (div_pos hNum hDenPos)) ?_)
  have hValue : (0 - (n : Complex) / ((beta : Complex) * ((beta : Complex) + 1))).re =
      0 - (n : Real) / (beta * (beta + 1)) := by
    norm_cast
  change Tendsto (fun s : Real => (((s : Complex) - (beta : Complex)) *
    (A (s : Complex) - logDeriv f (s : Complex) / ((s : Complex) * ((s : Complex) + 1)))).re)
      (nhdsWithin beta (Ioi beta)) _ at hReal
  simpa only [hValue, <- Complex.ofReal_sub, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hReal

/-- If the exponential moments converge throughout the required real
range, a complex Mellin representation gives a holomorphic logarithmic
derivative on the corresponding half-plane. -/
theorem ne_zero_of_mgf_logDerivative_on_halfPlane
    {Omega : Type*} [MeasurableSpace Omega] {X : Omega -> Real} {mu : Measure Omega}
    {f A B : Complex -> Complex} {centre edge : Real}
    (hExp : forall t : Real, t < centre - edge ->
      Membership.mem (integrableExpSet X mu) t)
    (hf : AnalyticOnNhd Complex f {z : Complex | edge < z.re})
    (hA : AnalyticOnNhd Complex A {z : Complex | edge < z.re})
    (hB : AnalyticOnNhd Complex B {z : Complex | edge < z.re})
    (hStart : exists z : Complex, And (edge < z.re)
      (Filter.EventuallyEq (nhds z) (deriv f)
        (f * fun w => A w + B w * complexMGF X mu ((centre : Complex) - w))))
    (hNonzero : exists z : Complex, And (edge < z.re) (Not (f z = 0)))
    {z : Complex} (hz : edge < z.re) :
    Not (f z = 0) := by
  let domain : Set Complex := {z : Complex | edge < z.re}
  have hOpen : IsOpen domain := isOpen_lt continuous_const Complex.continuous_re
  have hConnected : IsPreconnected domain := by
    change IsPreconnected (Set.preimage Complex.reLm (Ioi edge))
    exact ((convex_Ioi edge).linear_preimage Complex.reLm).isPreconnected
  have hMGF : AnalyticOnNhd Complex
      (fun w : Complex => complexMGF X mu ((centre : Complex) - w)) domain := by
    intro w hw
    have hEdge : edge < w.re := hw
    have hReal : ((centre : Complex) - w).re < centre - edge := by
      rw [Complex.sub_re, Complex.ofReal_re]
      exact sub_lt_sub_left hEdge centre
    have hInter : Membership.mem (interior (integrableExpSet X mu))
        ((centre : Complex) - w).re := mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Iio_mem_nhds hReal) (fun t ht => hExp t ht))
    exact (analyticAt_complexMGF hInter).comp (analyticAt_const.sub analyticAt_id)
  exact ne_zero_of_analyticLogDerivative hOpen hConnected hf
    (fun w hw => (hA w hw).add ((hB w hw).mul (hMGF w hw))) hStart hNonzero hz

end Robin1984.GRH
