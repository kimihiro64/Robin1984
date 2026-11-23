import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Robin1984.GRH.MertensTailWeight

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The fundamental theorem of calculus on an improper interval.
- Formalization note: The negative derivative of the Mertens weight has mass equal to the weight at its lower endpoint.
- PROVENANCE-END
-/

/-!
# Absolute control of the derivative-weighted Dedekind tail

The negative derivative of the weight has mass equal to the weight at
the lower endpoint. Multiplying by a bounded primitive tail therefore
gives an absolutely integrable function with a local uniform estimate.
-/

open Filter MeasureTheory Set

namespace Robin1984.GRH

noncomputable def mertensTailSlope (x : Real) : Real :=
  -(Real.log x + 2) / (x * Real.log x ^ 3)

theorem mertensTailSlope_nonpos {x : Real} (hx : 1 < x) :
    mertensTailSlope x <= 0 := by
  have hLog := Real.log_pos hx
  have hx0 := zero_lt_one.trans hx
  unfold mertensTailSlope
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (add_nonneg hLog.le (by norm_num))) (mul_nonneg hx0.le (pow_nonneg hLog.le _))

theorem continuousOn_mertensTailSlope : ContinuousOn mertensTailSlope (Ioi (1 : Real)) := by
  have hLog : ContinuousOn Real.log (Ioi (1 : Real)) := fun _ ht =>
    (Real.continuousAt_log (zero_lt_one.trans ht).ne').continuousWithinAt
  exact ((hLog.add continuousOn_const).neg).div
    (continuousOn_id.mul (hLog.pow 3))
    (fun t ht => mul_ne_zero (zero_lt_one.trans ht).ne' (pow_ne_zero _ (Real.log_pos ht).ne'))

theorem integrableOn_mertensTailSlope {a : Real} (ha : 1 < a) :
    IntegrableOn mertensTailSlope (Ioi a) := by
  exact integrableOn_Ioi_deriv_of_nonpos'
    (fun t ht => hasDerivAt_mertensTailWeight (ha.trans_le ht))
    (fun t ht => mertensTailSlope_nonpos (ha.trans ht)) tendsto_mertensTailWeight

theorem integral_neg_mertensTailSlope {a : Real} (ha : 1 < a) :
    integral (volume.restrict (Ioi a)) (fun t => -mertensTailSlope t) = mertensTailWeight a := by
  have h := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun t ht => hasDerivAt_mertensTailWeight (ha.trans_le ht))
    (fun t ht => mertensTailSlope_nonpos (ha.trans ht)) tendsto_mertensTailWeight
  have h' : integral (volume.restrict (Ioi a)) mertensTailSlope = 0 - mertensTailWeight a := h
  rw [integral_neg, h', zero_sub, neg_neg]

/-- A uniformly bounded real tail against the weight derivative is
absolutely integrable. The bound scales with the weight at the endpoint. -/
theorem norm_integral_mul_mertensTailSlope_le {a M : Real} {T : Real -> Real}
    (ha : 1 < a) (hMeas : AEStronglyMeasurable T (volume.restrict (Ioi a)))
    (hBound : forall t : Real, Membership.mem (Ioi a) t -> norm (T t) <= M) :
    And (IntegrableOn (fun t => T t * mertensTailSlope t) (Ioi a))
      (norm (integral (volume.restrict (Ioi a)) (fun t => T t * mertensTailSlope t)) <=
        M * mertensTailWeight a) := by
  have hSlope : Integrable mertensTailSlope (volume.restrict (Ioi a)) :=
    integrableOn_mertensTailSlope ha
  have hControl : Integrable (fun t => M * (-mertensTailSlope t)) (volume.restrict (Ioi a)) :=
    hSlope.neg.const_mul M
  have hDom : Filter.Eventually
      (fun t : Real => norm (T t * mertensTailSlope t) <= M * (-mertensTailSlope t))
      (ae (volume.restrict (Ioi a))) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    apply Filter.Eventually.of_forall
    intro t ht
    have hNeg := mertensTailSlope_nonpos (ha.trans ht)
    rw [norm_mul, Real.norm_eq_abs (mertensTailSlope t), abs_of_nonpos hNeg]
    exact mul_le_mul_of_nonneg_right (hBound t ht) (neg_nonneg.mpr hNeg)
  have hI : Integrable (fun t => T t * mertensTailSlope t) (volume.restrict (Ioi a)) :=
    hControl.mono' (hMeas.mul hSlope.aestronglyMeasurable) hDom
  refine And.intro hI ?_
  calc
    _ <= integral (volume.restrict (Ioi a)) (fun t => norm (T t * mertensTailSlope t)) :=
      norm_integral_le_integral_norm _
    _ <= integral (volume.restrict (Ioi a)) (fun t => M * (-mertensTailSlope t)) :=
      integral_mono_ae hI.norm hControl hDom
    _ = _ := by rw [integral_const_mul, integral_neg_mertensTailSlope ha]

end Robin1984.GRH
