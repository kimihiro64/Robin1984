import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Probability.Moments.ComplexMGF
import Robin1984.GRH.LandauFrontier
import Robin1984.GRH.SmoothedConverse

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Landau continuation for a nonnegative Mellin transform and the analytic identity theorem.
- Formalization note: The initial transform identity continues to the common domain and supplies the real comparison at the convergence boundary.
- PROVENANCE-END
-/

/-!
# Nonvanishing from the triangular comparison transform

The theorem uses the transform identity on its initial domain. At a
possible finite convergence boundary, analytic continuation or the
negative sign of the triangular residue forces convergence farther.
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace Robin1984.GRH

private theorem triangularDen_analyticAt (s : Complex) :
    AnalyticAt Complex (fun w : Complex => w * (w + 1)) s :=
  analyticAt_id.mul (analyticAt_id.add analyticAt_const)

private theorem triangularDen_ne_zero {s : Complex} (hs : 0 < s.re) :
    Not (s * (s + 1) = 0) := by
  have hs0 : Not (s = 0) := fun h => by simp [h] at hs
  have hOne : Not (s + 1 = 0) := fun h => by
    have hReal := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hReal
    exact (add_pos hs zero_lt_one).ne' hReal
  exact mul_ne_zero hs0 hOne

/-- For a nonnegative transform with the triangular logarithmic-derivative
identity on an initial open set, all zeros of the pole-removed function are
excluded to the right of the specified positive real edge. -/
theorem ne_zero_of_triangularTransform
    {Omega : Type*} [MeasurableSpace Omega] {X : Omega -> Real} {mu : Measure Omega}
    (hMeas : Measurable X)
    (hSupport : Filter.Eventually (fun x => 0 <= X x) (ae mu))
    {f A : Complex -> Complex} {edge : Real} (hEdge : 0 < edge)
    (hf : AnalyticOnNhd Complex f {z : Complex | edge < z.re})
    (hA : AnalyticOnNhd Complex A {z : Complex | edge < z.re})
    {base : Complex} (hBase : edge < base.re)
    (hBaseExp : Membership.mem (interior (integrableExpSet X mu)) (-base).re)
    (hBaseNonzero : Not (f base = 0))
    (hInitial : Filter.EventuallyEq (nhds base) (deriv f)
      (f * fun w => w * (w + 1) * (A w - complexMGF X mu (-w))))
    {z : Complex} (hz : edge < z.re) : Not (f z = 0) := by
  let half : Set Complex := {w : Complex | edge < w.re}
  let expDomain := interior (integrableExpSet X mu)
  let common : Set Complex := {w : Complex | And (edge < w.re) (Membership.mem expDomain (-w).re)}
  let G : Complex -> Complex := fun w => w * (w + 1) * (A w - complexMGF X mu (-w))
  let H : Real -> Real := fun t =>
    (A (-(t : Complex)) - logDeriv f (-(t : Complex)) /
      (-(t : Complex) * (-(t : Complex) + 1))).re
  have hHalfOpen : IsOpen half := isOpen_lt continuous_const Complex.continuous_re
  have hHalfConvex : Convex Real half := (convex_Ioi edge).linear_preimage Complex.reLm
  have hCommonOpen : IsOpen common :=
    hHalfOpen.inter (isOpen_interior.preimage (Complex.continuous_re.comp continuous_neg))
  have hCommonConnected : IsPreconnected common := by
    change IsPreconnected (Set.inter half (Set.preimage (-Complex.reLm) expDomain))
    exact (hHalfConvex.inter (convex_integrableExpSet.interior.linear_preimage
      (-Complex.reLm))).isPreconnected
  have hBaseCommon : Membership.mem common base := And.intro hBase hBaseExp
  have hfCommon : AnalyticOnNhd Complex f common := fun w hw => hf w hw.1
  have hGCommon : AnalyticOnNhd Complex G common := by
    intro w hw
    exact (triangularDen_analyticAt w).mul
      ((hA w hw.1).sub ((analyticAt_complexMGF hw.2).comp analyticAt_id.neg))
  have hDerivCommon : AnalyticOnNhd Complex (deriv f) common :=
    fun w hw => (hfCommon w hw).deriv
  have hMulCommon : AnalyticOnNhd Complex (f * G) common :=
    fun w hw => (hfCommon w hw).mul (hGCommon w hw)
  have hIdentity : EqOn (deriv f) (f * G) common :=
    hDerivCommon.eqOn_of_preconnected_of_eventuallyEq hMulCommon hCommonConnected
      hBaseCommon hInitial
  have hAgreement (t : Real) (ht : Membership.mem expDomain t) (htBound : t < -edge) :
      mgf X mu t = H t := by
    have hEdgeT : edge < (-(t : Complex)).re := by
      rw [Complex.neg_re, Complex.ofReal_re]
      exact lt_neg_of_lt_neg htBound
    have hTCommon : Membership.mem common (-(t : Complex)) := And.intro hEdgeT (by simpa)
    have hNonzero := ne_zero_of_analyticLogDerivative hCommonOpen hCommonConnected
      hfCommon hGCommon (Exists.intro base (And.intro hBaseCommon hInitial))
      (Exists.intro base (And.intro hBaseCommon hBaseNonzero)) hTCommon
    have hDen := triangularDen_ne_zero (hEdge.trans hEdgeT)
    have hD := hIdentity hTCommon
    change deriv f (-(t : Complex)) =
      f (-(t : Complex)) * (-(t : Complex) * (-(t : Complex) + 1) *
        (A (-(t : Complex)) - complexMGF X mu (-(-(t : Complex))))) at hD
    have hM : complexMGF X mu (t : Complex) =
        A (-(t : Complex)) - logDeriv f (-(t : Complex)) /
          (-(t : Complex) * (-(t : Complex) + 1)) := by
      have hLog : logDeriv f (-(t : Complex)) = -(t : Complex) * (-(t : Complex) + 1) *
          (A (-(t : Complex)) - complexMGF X mu (t : Complex)) := by
        rw [logDeriv_apply, div_eq_iff hNonzero, hD, neg_neg]
        exact mul_comm _ _
      have hQuot : (-(t : Complex) * (-(t : Complex) + 1) *
          (A (-(t : Complex)) - complexMGF X mu (t : Complex))) /
          (-(t : Complex) * (-(t : Complex) + 1)) =
          A (-(t : Complex)) - complexMGF X mu (t : Complex) :=
        (div_eq_iff hDen).2 (mul_comm _ _)
      rw [hLog, hQuot, sub_sub_cancel]
    simpa only [H, re_complexMGF_ofReal] using congrArg Complex.re hM
  have hBoundary (b : Real) (hb : b < -edge) : Or (AnalyticAt Real H b)
      (exists residue : Real, And (residue < 0)
        (Tendsto (fun t => (b - t) * H t) (nhdsWithin b (Iio b)) (nhds residue))) := by
    let beta : Real := -b
    have hbEdge : edge < (beta : Complex).re := by
      rw [Complex.ofReal_re]
      exact lt_neg_of_lt_neg hb
    have hfb := hf (beta : Complex) hbEdge
    have hAb := hA (beta : Complex) hbEdge
    by_cases hbZero : f (beta : Complex) = 0
    case pos =>
      have hGerm : Not (Filter.Eventually (fun w => f w = 0) (nhds (beta : Complex))) := by
        intro hLocal
        have hConst : AnalyticOnNhd Complex (fun _ : Complex => (0 : Complex)) half :=
          fun _ _ => analyticAt_const
        have hIdentityZero := hf.eqOn_of_preconnected_of_eventuallyEq hConst
          hHalfConvex.isPreconnected hbEdge hLocal
        exact hBaseNonzero (hIdentityZero hBase)
      choose residue hr using negative_residue_of_triangularLogDerivative
        (hEdge.trans (by simpa only [Complex.ofReal_re] using hbEdge)) hfb hbZero hGerm hAb.continuousAt
      have hNeg : Tendsto (fun x : Real => -x) (nhdsWithin b (Iio b))
          (nhdsWithin beta (Ioi beta)) := by
        refine tendsto_nhdsWithin_iff.mpr (And.intro
          (continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_)
        have hLeft : Filter.Eventually (fun x : Real => x < b) (nhdsWithin b (Iio b)) :=
          self_mem_nhdsWithin
        exact hLeft.mono (fun _ hx => neg_lt_neg hx)
      apply Or.inr
      refine Exists.intro residue (And.intro hr.1 ?_)
      simpa only [Function.comp_def, beta, neg_sub_neg, Complex.ofReal_neg, H] using
        hr.2.comp hNeg
    case neg =>
      have hLD : AnalyticAt Complex (logDeriv f) (beta : Complex) := hfb.deriv.div hfb hbZero
      have hLocal := hAb.sub
        (hLD.div (triangularDen_analyticAt (beta : Complex))
          (triangularDen_ne_zero (hEdge.trans hbEdge)))
      have hNegReal : AnalyticAt Real (fun x : Real => -(x : Complex)) b :=
        (Complex.ofRealCLM.analyticAt b).neg
      have hComplexForm : AnalyticAt Real
          (fun w : Complex => A w - logDeriv f w / (w * (w + 1))) (-(b : Complex)) := by
        have hRestricted : AnalyticAt Real
            (fun w : Complex => A w - logDeriv f w / (w * (w + 1))) (beta : Complex) :=
          hLocal.restrictScalars
        simpa only [beta, Complex.ofReal_neg] using hRestricted
      have hComposition := hComplexForm.comp (f := fun x : Real => -(x : Complex))
        (x := b) hNegReal
      exact Or.inl ((Complex.reCLM.analyticAt _).comp hComposition)
  have hExp t (ht : t < -edge) : Membership.mem (integrableExpSet X mu) t :=
    mem_expDomain_below_of_analytic_or_negativeResidue hMeas hSupport
      (Exists.intro (-base).re (interior_subset hBaseExp)) H (-edge) hAgreement hBoundary ht
  have hA2 : AnalyticOnNhd Complex (fun w : Complex => w * (w + 1) * A w) half :=
    fun w hw => (triangularDen_analyticAt w).mul (hA w hw)
  have hB2 : AnalyticOnNhd Complex (fun w : Complex => -(w * (w + 1))) half :=
    fun w _ => (triangularDen_analyticAt w).neg
  apply ne_zero_of_mgf_logDerivative_on_halfPlane
    (centre := 0) (by simpa only [zero_sub] using hExp) hf hA2 hB2
  exact Exists.intro base (And.intro hBase (by
    simpa only [Pi.mul_apply, Complex.ofReal_zero, sub_eq_add_neg, zero_add, mul_add, neg_mul,
      mul_neg]
      using hInitial))
  exact Exists.intro base (And.intro hBase hBaseNonzero)
  exact hz

end Robin1984.GRH
