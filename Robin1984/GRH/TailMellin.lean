import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Fubini's theorem and the divided-difference formula for the Mellin transform of a tail integral.
- Formalization note: The lower endpoint is 1, the inner integration is on the strict triangular domain, and the resulting polar denominator is explicit.
- PROVENANCE-END
-/

/-!
# Mellin transform of a tail integral

This gives the divided difference used by the Dedekind comparison
transform, with absolute integrability on its initial half-plane.
-/

open Filter MeasureTheory Set

namespace Robin1984.GRH

private theorem integral_tail_mul_swap {f w : Real -> Complex}
    (hf : IntegrableOn f (Ioi (1 : Real))) (hw : IntegrableOn w (Ioi (1 : Real))) :
    integral (volume.restrict (Ioi (1 : Real)))
      (fun x => w x * integral (volume.restrict (Ioi x)) f) =
    integral (volume.restrict (Ioi (1 : Real)))
      (fun t => integral (volume.restrict (Ioo 1 t)) w * f t) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let D : Set (Prod Real Real) := {p : Prod Real Real | p.1 < p.2}
  let K : Prod Real Real -> Complex := D.indicator (fun p => w p.1 * f p.2)
  have hD : MeasurableSet D := (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hK : Integrable K (mu.prod mu) := (hw.mul_prod hf).indicator hD
  have hSwap := integral_integral_swap (f := fun x t => K (x, t)) hK
  have hTail : Filter.Eventually (fun x : Real => 1 < x) (ae mu) :=
    ae_restrict_mem measurableSet_Ioi
  calc
    _ = integral mu (fun x => integral mu (fun t => K (x, t))) := by
      apply integral_congr_ae
      filter_upwards [hTail] with x hx
      have hFun : (fun t => K (x, t)) = (Ioi x).indicator (fun t => w x * f t) := by
        funext t
        by_cases ht : x < t
        case pos =>
          change D.indicator _ (x, t) = (Ioi x).indicator _ t
          rw [indicator_of_mem (show Membership.mem D (x, t) from ht),
            indicator_of_mem (show Membership.mem (Ioi x) t from ht)]
        case neg =>
          change D.indicator _ (x, t) = (Ioi x).indicator _ t
          rw [indicator_of_notMem (show Not (Membership.mem D (x, t)) from ht),
            indicator_of_notMem (show Not (Membership.mem (Ioi x) t) from ht)]
      rw [hFun, integral_indicator measurableSet_Ioi]
      have hSub : Set.Subset (Ioi x) (Ioi (1 : Real)) := fun _ ht => hx.trans ht
      change w x * integral (volume.restrict (Ioi x)) f =
        integral ((volume.restrict (Ioi (1 : Real))).restrict (Ioi x)) (fun t => w x * f t)
      rw [Measure.restrict_restrict_of_subset hSub, integral_const_mul]
    _ = integral mu (fun t => integral mu (fun x => K (x, t))) := hSwap
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        have hFun : (fun x => K (x, t)) = (Iio t).indicator (fun x => w x * f t) := by
          funext x
          by_cases hx : x < t
          case pos =>
            change D.indicator _ (x, t) = (Iio t).indicator _ x
            rw [indicator_of_mem (show Membership.mem D (x, t) from hx),
              indicator_of_mem (show Membership.mem (Iio t) x from hx)]
          case neg =>
            change D.indicator _ (x, t) = (Iio t).indicator _ x
            rw [indicator_of_notMem (show Not (Membership.mem D (x, t)) from hx),
              indicator_of_notMem (show Not (Membership.mem (Iio t) x) from hx)]
        change integral mu (fun x => K (x, t)) =
          integral (volume.restrict (Ioo 1 t)) w * f t
        rw [hFun, integral_indicator measurableSet_Iio]
        change integral ((volume.restrict (Ioi (1 : Real))).restrict (Iio t)) (fun x => w x * f t) = _
        rw [Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio,
          integral_mul_const])

private theorem integral_cpow_Ioo_one (s : Complex) (hs : 1 < s.re) {t : Real} (ht : 1 < t) :
    integral (volume.restrict (Ioo (1 : Real) t)) (fun x : Real => (x : Complex) ^ (-s)) =
      ((t : Complex) ^ (1 - s) - 1) / (1 - s) := by
  rw [<- integral_Ioc_eq_integral_Ioo, <- intervalIntegral.integral_of_le ht.le]
  have hExp : Not (-s = (-1 : Complex)) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.one_re] at hRe
    linarith only [hs, hRe]
  have hZero : Not (Membership.mem (Set.uIcc (1 : Real) t) 0) := by
    rw [Set.uIcc_of_le ht.le]
    exact fun h => (not_le_of_gt (zero_lt_one : (0 : Real) < 1)) h.1
  rw [integral_cpow (Or.inr (And.intro hExp hZero)), Complex.ofReal_one, Complex.one_cpow]
  rw [show -s + 1 = 1 - s by ring]

/-- The tail Mellin transform is the divided difference of the weighted
integral at the right-half-plane parameter and its value at one. -/
theorem integral_tail_cpow_dividedDifference {f : Real -> Complex}
    (hf : IntegrableOn f (Ioi (1 : Real))) (s : Complex) (hs : 1 < s.re) :
    let mu := volume.restrict (Ioi (1 : Real))
    integral mu (fun x : Real => (x : Complex) ^ (-s) * integral (volume.restrict (Ioi x)) f) =
      (integral mu (fun t : Real => (t : Complex) ^ (1 - s) * f t) - integral mu f) / (1 - s) := by
  let mu := volume.restrict (Ioi (1 : Real))
  have hStrict : (-s).re < -1 := by rw [Complex.neg_re]; linarith only [hs]
  have hw := integrableOn_Ioi_cpow_of_lt hStrict zero_lt_one
  have hFold := integral_tail_mul_swap hf hw
  have hCpow : AEStronglyMeasurable (fun x : Real => (x : Complex) ^ (1 - s)) mu := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')).continuousWithinAt
  have hTail : Filter.Eventually (fun x : Real => 1 < x) (ae mu) :=
    ae_restrict_mem measurableSet_Ioi
  have hInt : Integrable (fun x : Real => (x : Complex) ^ (1 - s) * f x) mu := by
    have hNorm : Integrable (fun x => norm (f x)) mu := hf.norm
    apply hNorm.mono' (hCpow.mul hf.aestronglyMeasurable)
    filter_upwards [hTail] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    change norm ((x : Complex) ^ (1 - s) * f x) <= norm (f x)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hRe : (1 - s).re <= 0 := by simp only [Complex.sub_re, Complex.one_re]; linarith
    apply mul_le_of_le_one_left (norm_nonneg _)
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hx.le hRe
  change integral mu (fun x : Real => (x : Complex) ^ (-s) * integral (volume.restrict (Ioi x)) f) = _
  calc
    _ = integral mu (fun t => integral (volume.restrict (Ioo 1 t))
        (fun x : Real => (x : Complex) ^ (-s)) * f t) := hFold
    _ = integral mu (fun t : Real =>
        ((t : Complex) ^ (1 - s) * f t - f t) * (1 - s) ^ (-1 : Int)) := by
      apply integral_congr_ae
      filter_upwards [hTail] with t ht
      rw [integral_cpow_Ioo_one s hs ht, div_eq_mul_inv, zpow_neg_one]
      ring
    _ = _ := by
      rw [integral_mul_const, integral_sub hInt hf, zpow_neg_one, <- div_eq_mul_inv]

end Robin1984.GRH
