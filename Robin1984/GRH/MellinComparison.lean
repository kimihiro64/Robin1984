import Robin1984.GRH.LandauFrontier
import Robin1984.GRH.SmoothedConverse

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Landau's real convergence boundary and the analytic identity theorem.
- Formalization note: An isolated removable real point is handled by continuity, so the logarithmic-derivative recovery can divide by a kernel that vanishes there.
- PROVENANCE-END
-/

/-!
# Recovering a Mellin comparison from a differential identity

The comparison may have a removable exceptional point on the real axis.
The differential identity itself is holomorphic through that point.
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace Robin1984.GRH

/-- The Landau continuation argument with a differential identity
`f' = f * (A + B * M)` and one removable point in the real recovery
of the nonnegative Mellin transform `M`. -/
theorem ne_zero_of_mgf_comparison
    {Omega : Type*} [MeasurableSpace Omega] {X : Omega -> Real} {mu : Measure Omega}
    (hMeas : Measurable X)
    (hSupport : Filter.Eventually (fun x => 0 <= X x) (ae mu))
    {f A B : Complex -> Complex} {edge exceptional : Real} {H : Real -> Real}
    (hf : AnalyticOnNhd Complex f {w : Complex | edge < w.re})
    (hA : AnalyticOnNhd Complex A {w : Complex | edge < w.re})
    (hB : AnalyticOnNhd Complex B {w : Complex | edge < w.re})
    {base : Complex} (hBase : edge < base.re)
    (hBaseExp : Membership.mem (interior (integrableExpSet X mu)) (-base).re)
    (hBaseNonzero : Not (f base = 0))
    (hInitial : Filter.EventuallyEq (nhds base) (deriv f)
      (f * fun w => A w + B w * complexMGF X mu (-w)))
    (hRecover : forall t : Real, t < -edge -> Not (t = exceptional) ->
      Not (f (-(t : Complex)) = 0) -> forall m : Complex,
      logDeriv f (-(t : Complex)) = A (-(t : Complex)) + B (-(t : Complex)) * m ->
        m.re = H t)
    (hExceptional : exceptional < -edge -> Not (f (-(exceptional : Complex)) = 0) ->
      ContinuousAt H exceptional)
    (hBoundary : forall b : Real, b < -edge -> Or (AnalyticAt Real H b)
      (exists residue : Real, And (residue < 0)
        (Tendsto (fun t => (b - t) * H t) (nhdsWithin b (Iio b)) (nhds residue))))
    {z : Complex} (hz : edge < z.re) :
    Not (f z = 0) := by
  let half : Set Complex := {w : Complex | edge < w.re}
  let expDomain := interior (integrableExpSet X mu)
  let common : Set Complex := {w : Complex | And (edge < w.re) (Membership.mem expDomain (-w).re)}
  let G : Complex -> Complex := fun w => A w + B w * complexMGF X mu (-w)
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
    exact (hA w hw.1).add ((hB w hw.1).mul
      ((analyticAt_complexMGF hw.2).comp analyticAt_id.neg))
  have hDerivCommon : AnalyticOnNhd Complex (deriv f) common :=
    fun w hw => (hfCommon w hw).deriv
  have hMulCommon : AnalyticOnNhd Complex (f * G) common :=
    fun w hw => (hfCommon w hw).mul (hGCommon w hw)
  have hIdentity : EqOn (deriv f) (f * G) common :=
    hDerivCommon.eqOn_of_preconnected_of_eventuallyEq hMulCommon hCommonConnected
      hBaseCommon hInitial
  have hRealMem (t : Real) (ht : Membership.mem expDomain t) (htBound : t < -edge) :
      Membership.mem common (-(t : Complex)) := by
    refine And.intro ?_ (by simpa)
    rw [Complex.neg_re, Complex.ofReal_re]
    exact lt_neg_of_lt_neg htBound
  have hNonzero t (ht : Membership.mem expDomain t) (htBound : t < -edge) :
      Not (f (-(t : Complex)) = 0) :=
    ne_zero_of_analyticLogDerivative hCommonOpen hCommonConnected
      hfCommon hGCommon (Exists.intro base (And.intro hBaseCommon hInitial))
      (Exists.intro base (And.intro hBaseCommon hBaseNonzero)) (hRealMem t ht htBound)
  have hOff (t : Real) (ht : Membership.mem expDomain t) (htBound : t < -edge)
      (hNe : Not (t = exceptional)) : mgf X mu t = H t := by
    have hLog : logDeriv f (-(t : Complex)) =
        A (-(t : Complex)) + B (-(t : Complex)) * complexMGF X mu (t : Complex) := by
      rw [logDeriv_apply, div_eq_iff (hNonzero t ht htBound), hIdentity (hRealMem t ht htBound)]
      simp only [Pi.mul_apply, G, neg_neg]
      exact mul_comm _ _
    simpa only [re_complexMGF_ofReal] using
      hRecover t htBound hNe (hNonzero t ht htBound) _ hLog
  have hAgreement (t : Real) (ht : Membership.mem expDomain t) (htBound : t < -edge) :
      mgf X mu t = H t := by
    by_cases hNe : t = exceptional
    case neg => exact hOff t ht htBound hNe
    case pos =>
      subst t
      have hExpNear : Membership.mem (nhds exceptional) expDomain :=
        isOpen_interior.mem_nhds ht
      have hEdgeNear : Membership.mem (nhds exceptional) (Iio (-edge)) := Iio_mem_nhds htBound
      have hLeft : Filter.Eventually (fun u : Real => u < exceptional)
          (nhdsWithin exceptional (Iio exceptional)) := self_mem_nhdsWithin
      have hFilter : nhdsWithin exceptional (Iio exceptional) <= nhds exceptional :=
        nhdsWithin_le_nhds
      have hExpNearLeft : Filter.Eventually (fun u => Membership.mem expDomain u)
          (nhdsWithin exceptional (Iio exceptional)) := hFilter hExpNear
      have hEdgeNearLeft : Filter.Eventually (fun u => u < -edge)
          (nhdsWithin exceptional (Iio exceptional)) := hFilter hEdgeNear
      have hEqual : Filter.EventuallyEq (nhdsWithin exceptional (Iio exceptional)) (mgf X mu) H :=
        (hLeft.and (hExpNearLeft.and hEdgeNearLeft)).mono
          (fun u hu => hOff u hu.2.1 hu.2.2 hu.1.ne)
      have hM := (analyticAt_mgf ht).continuousAt.tendsto.mono_left hFilter
      have hH := (hExceptional htBound (hNonzero exceptional ht htBound)).tendsto.mono_left hFilter
      exact tendsto_nhds_unique hM (hH.congr' hEqual.symm)
  have hExp t (ht : t < -edge) : Membership.mem (integrableExpSet X mu) t :=
    mem_expDomain_below_of_analytic_or_negativeResidue hMeas hSupport
      (Exists.intro (-base).re (interior_subset hBaseExp)) H (-edge) hAgreement hBoundary ht
  apply ne_zero_of_mgf_logDerivative_on_halfPlane
    (centre := 0) (by simpa only [zero_sub] using hExp) hf hA hB
  exact Exists.intro base (And.intro hBase
    (by simpa only [Complex.ofReal_zero, zero_sub] using hInitial))
  exact Exists.intro base (And.intro hBase hBaseNonzero)
  exact hz

end Robin1984.GRH
