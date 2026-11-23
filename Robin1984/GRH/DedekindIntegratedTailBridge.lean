import Robin1984.GRH.DedekindFunctionalBridge

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The one-sided Landau converse for the signed Dedekind Chebyshev primitive.
- Formalization note: From a Dedekind Chebyshev tail bound to Dedekind RH.
- PROVENANCE-END
-/

/-!
# From a Dedekind Chebyshev tail bound to Dedekind RH

The Mellin input in the abstract Landau argument is the prime-ideal
Chebyshev error formed from the actual Dedekind zeta logarithmic
derivative. This leaves real-variable integrability and the eventual
tail estimate as the arithmetic hypotheses.
-/

open Filter MeasureTheory NumberField Robin1984.GRH Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

theorem actualDedekindError_logDeriv_identity {s : Complex} (hs : 1 < s.re) :
    (-deriv (dedekindZeta K) s / dedekindZeta K s) / s - 1 / (s - 1) =
      -(logDeriv (entirePoleFreeDedekindZeta K) s + 1) / s := by
  have hs0 : Not (s = 0) := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact (not_lt_of_ge zero_le_one) hs
  have hs1 : Not (s = 1) := by
    intro h
    rw [h, Complex.one_re] at hs
    exact (lt_irrefl (1 : Real)) hs
  let U : Set Complex := {z | 1 < z.re}
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hNearZ : Filter.EventuallyEq (nhds s) (dedekindZetaContinuation K) (dedekindZeta K) := by
    filter_upwards [hOpen.mem_nhds (show Membership.mem U s from hs)] with z hz
    exact dedekindZetaContinuation_eq_series K hz
  have hNearF : Filter.EventuallyEq (nhds s) (entirePoleFreeDedekindZeta K)
      (fun z => (z - 1) * dedekindZeta K z) := by
    filter_upwards [hOpen.mem_nhds (show Membership.mem U s from hs)] with z hz
    have hf := entirePoleFreeDedekindZeta_eq_poleFree K (zero_lt_one.trans (show 1 < z.re from hz))
    exact hf.trans (poleFreeDedekindZeta_eq K hz)
  have hZD := (analyticAt_dedekindZetaContinuation K hs1).differentiableAt.hasDerivAt
  have hZDeriv := hZD.congr_of_eventuallyEq hNearZ.symm
  have hFDeriv := (((hasDerivAt_id s).sub_const 1).mul hZDeriv).congr_of_eventuallyEq hNearF
  have hDerivative : deriv (entirePoleFreeDedekindZeta K) s =
      dedekindZeta K s + (s - 1) * deriv (dedekindZeta K) s := by
    simp only [hFDeriv.deriv, hZDeriv.deriv, one_mul, id_eq]
  have hVal : entirePoleFreeDedekindZeta K s = (s - 1) * dedekindZeta K s :=
    hNearF.eq_of_nhds
  rw [logDeriv_apply, hDerivative, hVal]
  field_simp [hs0, sub_ne_zero.mpr hs1, dedekindZeta_ne_zero_of_one_lt_re K hs] <;> ring

/-- An integrable Chebyshev error weight and the signed integrated tail
bound imply Dedekind RH for the field. -/
theorem dedekindRH_of_integratedChebyshevTailBound
    (hInt : IntegrableOn (dedekindChebyshevErrorRatio K) (Ioi (1 : Real)))
    (hBound : exists C t : Real, forall x : Real, t < x ->
      -x * integratedTail (dedekindChebyshevErrorRatio K) x <= C * Real.sqrt x) :
    DedekindRH K := by
  rw [dedekindRH_iff_noZero_rightHalfStrip K]
  intro s hs hs1 hZero
  have hNoZero : Not (entirePoleFreeDedekindZeta K s = 0) :=
    ne_zero_of_eventual_integratedTailBound (measurable_dedekindChebyshevErrorRatio K) hInt
      (fun z _ => analyticAt_entirePoleFreeDedekindZeta K z)
      (fun b => entirePoleFreeDedekindZeta_ne_zero_of_real_one_le K (b := b))
      (fun z hz => (dedekindChebyshevErrorRatio_mellin K hz).trans
        (actualDedekindError_logDeriv_identity K hz)) hBound hs
  have hn1 : Not (s - 1 = 0) := by
    intro h
    rw [sub_eq_zero.mp h, Complex.one_re] at hs1
    exact (lt_irrefl (1 : Real)) hs1
  exact hNoZero ((div_eq_zero_iff.mp hZero).resolve_right hn1)

/-- The one-sided Chebyshev tail bound gives Dedekind RH when the
finite-interval primitive converges to the regularized transform at one. -/
theorem dedekindRH_of_primitiveChebyshevTailBound {a : Real}
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds a))
    (hAtOne : logDeriv (entirePoleFreeDedekindZeta K) 1 + 1 + (a : Complex) = 0)
    (hBound : exists C t : Real, forall x : Real, t < x ->
      -x * primitiveTail (dedekindChebyshevErrorRatio K) a x <= C * Real.sqrt x) :
    DedekindRH K := by
  rw [dedekindRH_iff_noZero_rightHalfStrip K]
  intro s hs hs1 hZero
  have hNoZero : Not (entirePoleFreeDedekindZeta K s = 0) :=
    ne_zero_of_eventual_primitiveTailBound (measurable_dedekindChebyshevErrorRatio K)
      (fun b _ => dedekindChebyshevErrorRatio_integrableOn_Ioo K b) hLimit
      (fun z _ => analyticAt_entirePoleFreeDedekindZeta K z)
      (fun b => entirePoleFreeDedekindZeta_ne_zero_of_real_one_le K (b := b)) hAtOne
      (fun z hz => by
        have h := dedekindChebyshevErrorRatio_mellin_and_integrable K hz
        exact And.intro h.1 (h.2.trans (actualDedekindError_logDeriv_identity K hz)))
      hBound hs
  have hn1 : Not (s - 1 = 0) := by
    intro h
    rw [sub_eq_zero.mp h, Complex.one_re] at hs1
    exact (lt_irrefl (1 : Real)) hs1
  exact hNoZero ((div_eq_zero_iff.mp hZero).resolve_right hn1)

end DedekindZeta
