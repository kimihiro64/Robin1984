import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Integration by parts for absolutely continuous primitives.
- Formalization note: Integration by parts for a signed primitive tail.
- PROVENANCE-END
-/

/-!
# Integration by parts for a signed primitive tail

The Chebyshev primitive need only have a locally integrable derivative.
The finite identity uses its absolutely continuous representative and
holds with the exact endpoint signs.
-/

open Filter MeasureTheory Set

namespace Robin1984.GRH

theorem intervalIntegral_mul_eq_primitiveTail_parts
    {a b c : Real} {g w dw : Real -> Real}
    (hg : IntervalIntegrable g volume a b)
    (hw : forall t : Real, Membership.mem (uIcc a b) t -> HasDerivAt w (dw t) t)
    (hdw : ContinuousOn dw (uIcc a b)) :
    let T := fun t : Real => c - intervalIntegral g a t volume
    intervalIntegral (fun t => g t * w t) a b volume =
      T a * w a - T b * w b + intervalIntegral (fun t => T t * dw t) a b volume := by
  let T := fun t : Real => c - intervalIntegral g a t volume
  change intervalIntegral (fun t => g t * w t) a b volume =
    T a * w a - T b * w b + intervalIntegral (fun t => T t * dw t) a b volume
  have hP := hg.absolutelyContinuousOnInterval_intervalIntegral' left_mem_uIcc
  have hConst : LipschitzWith 0 (fun _ : Real => c) := LipschitzWith.const c
  have hT : AbsolutelyContinuousOnInterval T a b :=
    hConst.lipschitzOnWith.absolutelyContinuousOnInterval.fun_sub hP
  have hwCont : ContinuousOn w (uIcc a b) :=
    fun t ht => (hw t ht).continuousAt.continuousWithinAt
  have hwAC : AbsolutelyContinuousOnInterval w a b :=
    hwCont.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable
      (s := {}) Set.countable_empty
      (fun t ht => hw t (And.intro ht.1.1.le ht.1.2.le)) hdw.intervalIntegrable
  have hProd : AbsolutelyContinuousOnInterval (fun t => T t * w t) a b :=
    hT.smul hwAC
  have hDer : Filter.Eventually
      (fun t : Real => Membership.mem (uIoc a b) t ->
        HasDerivAt (fun v => T v * w v) (T t * dw t - g t * w t) t) (ae volume) := by
    filter_upwards [hg.ae_hasDerivAt_integral] with t hPt ht
    have hIcc := uIoc_subset_uIcc ht
    have hTd : HasDerivAt T (-g t) t :=
      (hPt hIcc a left_mem_uIcc).const_sub c
    exact (hTd.mul (hw t hIcc)).congr_deriv (by ring)
  have hFTC := hProd.integral_eq_sub_of_ae_hasDerivAt hDer
  have hGw : IntervalIntegrable (fun t => g t * w t) volume a b := by
    apply intervalIntegrable_iff.mpr
    exact (intervalIntegrable_iff.mp hg).mul_continuousOn_of_subset hwCont
      measurableSet_uIoc isCompact_uIcc uIoc_subset_uIcc
  have hTInt : IntervalIntegrable T volume a b := hT.continuousOn'.intervalIntegrable
  have hTdw : IntervalIntegrable (fun t => T t * dw t) volume a b := by
    apply intervalIntegrable_iff.mpr
    exact (intervalIntegrable_iff.mp hTInt).mul_continuousOn_of_subset hdw
      measurableSet_uIoc isCompact_uIcc uIoc_subset_uIcc
  rw [intervalIntegral.integral_sub hTdw hGw] at hFTC
  linarith only [hFTC]

end Robin1984.GRH
