import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mellin transform of a primitive

Integrating a finite-interval primitive against a Mellin weight divides
the original transform by the Mellin parameter minus one. The Fubini
argument uses weighted integrability of the original function.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Fubini's theorem on a triangular domain and the Mellin transform of a primitive.
- Formalization note: Characterize integrability by the weighted slice norms, then evaluate the complex power integral on each slice.
- PROVENANCE-END
-/

open Filter MeasureTheory Set

namespace Robin1984.GRH

/-- The primitive on the finite interval from one to the cutoff. -/
noncomputable def primitiveFromOne (f : Real -> Complex) (x : Real) : Complex :=
  integral (volume.restrict (Ioo 1 x)) f

theorem integral_primitive_cpow {f : Real -> Complex} (hf : Measurable f)
    (s : Complex) (hs : 1 < s.re)
    (hWeight : IntegrableOn (fun t : Real => (t : Complex) ^ (1 - s) * f t) (Ioi (1 : Real))) :
    let mu := volume.restrict (Ioi (1 : Real))
    let H := fun x : Real => (x : Complex) ^ (-s) * primitiveFromOne f x
    And (Integrable H mu)
      (integral mu H =
        integral mu (fun t : Real => (t : Complex) ^ (1 - s) * f t) / (s - 1)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let w := fun x : Real => (x : Complex) ^ (-s)
  let D : Set (Prod Real Real) := {p : Prod Real Real | p.1 < p.2}
  let J : Prod Real Real -> Complex := D.indicator (fun p => f p.1 * w p.2)
  have hD : MeasurableSet D := (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hs' : (-s).re < -1 := by rw [Complex.neg_re]; linarith only [hs]
  have hw : Integrable w mu := integrableOn_Ioi_cpow_of_lt hs' zero_lt_one
  have hSlice (t : Real) :
      (fun x : Real => J (t, x)) = (Ioi t).indicator (fun x => f t * w x) := by
    funext x
    by_cases htx : t < x
    case pos =>
      change D.indicator _ (t, x) = (Ioi t).indicator _ x
      rw [indicator_of_mem (show Membership.mem D (t, x) from htx),
        indicator_of_mem (show Membership.mem (Ioi t) x from htx)]
    case neg =>
      change D.indicator _ (t, x) = (Ioi t).indicator _ x
      rw [indicator_of_notMem (show Not (Membership.mem D (t, x)) from htx),
        indicator_of_notMem (show Not (Membership.mem (Ioi t) x) from htx)]
  have hSliceInt (t : Real) : Integrable (fun x : Real => J (t, x)) mu := by
    rw [hSlice]
    exact (hw.const_mul (f t)).indicator measurableSet_Ioi
  have hMem : Filter.Eventually (fun t : Real => 1 < t) (ae mu) := ae_restrict_mem measurableSet_Ioi
  have hSliceNorm {t : Real} (ht : 1 < t) :
      integral mu (fun x : Real => norm (J (t, x))) =
        (-1 / (1 - s.re)) * norm ((t : Complex) ^ (1 - s) * f t) := by
    have hSub : Set.Subset (Ioi t) (Ioi (1 : Real)) := fun _ hx => ht.trans hx
    have hFn : (fun x : Real => norm (J (t, x))) =
        (Ioi t).indicator (fun x => norm (f t) * norm (w x)) := by
      funext x
      have hValue := congrFun (hSlice t) x
      change J (t, x) = (Ioi t).indicator (fun y => f t * w y) x at hValue
      rw [hValue]
      by_cases htx : Membership.mem (Ioi t) x
      case pos => rw [indicator_of_mem htx, indicator_of_mem htx, norm_mul]
      case neg => rw [indicator_of_notMem htx, indicator_of_notMem htx, norm_zero]
    rw [hFn, integral_indicator measurableSet_Ioi, Measure.restrict_restrict_of_subset hSub,
      integral_const_mul]
    have hW : integral (volume.restrict (Ioi t)) (fun x : Real => norm (w x)) =
        integral (volume.restrict (Ioi t)) (fun x : Real => x ^ (-s.re)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := zero_lt_one.trans (ht.trans hx)
      change norm ((x : Complex) ^ (-s)) = x ^ (-s.re)
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.neg_re]
    have hNeg : -s.re < -1 := by linarith only [hs]
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [hW, integral_Ioi_rpow_of_lt hNeg ht0, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
      Complex.sub_re, Complex.one_re, show -s.re + 1 = 1 - s.re by ring]
    ring
  have hAES : AEStronglyMeasurable J (mu.prod mu) :=
    ((hf.comp measurable_fst).aestronglyMeasurable.mul (hw.aestronglyMeasurable.comp_snd)).indicator hD
  have hJ : Integrable J (mu.prod mu) := by
    apply (integrable_prod_iff hAES).mpr
    refine And.intro (Filter.Eventually.of_forall hSliceInt) ?_
    exact (hWeight.norm.const_mul (-1 / (1 - s.re))).congr
      (hMem.mono (fun t ht => (hSliceNorm ht).symm))
  have hInnerLeft (x : Real) :
      integral mu (fun t : Real => J (t, x)) = w x * primitiveFromOne f x := by
    have hSlice' : (fun t : Real => J (t, x)) = (Iio x).indicator (fun t => f t * w x) := by
      funext t
      by_cases htx : t < x
      case pos =>
        change D.indicator _ (t, x) = (Iio x).indicator _ t
        rw [indicator_of_mem (show Membership.mem D (t, x) from htx),
          indicator_of_mem (show Membership.mem (Iio x) t from htx)]
      case neg =>
        change D.indicator _ (t, x) = (Iio x).indicator _ t
        rw [indicator_of_notMem (show Not (Membership.mem D (t, x)) from htx),
          indicator_of_notMem (show Not (Membership.mem (Iio x) t) from htx)]
    rw [hSlice', integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      inter_comm, Ioi_inter_Iio, integral_mul_const, primitiveFromOne, mul_comm]
  have hInnerRight {t : Real} (ht : 1 < t) :
      integral mu (fun x : Real => J (t, x)) = ((t : Complex) ^ (1 - s) * f t) / (s - 1) := by
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hSub : Set.Subset (Ioi t) (Ioi (1 : Real)) := fun _ hx => ht.trans hx
    rw [hSlice, integral_indicator measurableSet_Ioi, Measure.restrict_restrict_of_subset hSub,
      integral_const_mul]
    unfold w
    rw [integral_Ioi_cpow_of_lt hs' ht0, show -s + 1 = 1 - s by ring,
      show 1 - s = -(s - 1) by ring]
    rw [neg_div_neg_eq, mul_div_assoc', mul_comm (f t)]
  refine And.intro (hJ.integral_prod_right.congr (Filter.Eventually.of_forall hInnerLeft)) ?_
  calc
    integral mu (fun x : Real => w x * primitiveFromOne f x) =
        integral mu (fun x : Real => integral mu (fun t : Real => J (t, x))) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => (hInnerLeft x).symm))
    _ = integral mu (fun t : Real => integral mu (fun x : Real => J (t, x))) :=
      (integral_integral_swap (f := fun t x => J (t, x)) hJ).symm
    _ = integral mu (fun t : Real => ((t : Complex) ^ (1 - s) * f t) / (s - 1)) :=
      integral_congr_ae (hMem.mono (fun _ ht => hInnerRight ht))
    _ = _ := by simp only [div_eq_mul_inv, integral_mul_const, mu]

/-- Subtracting the primitive from an assigned endpoint value gives the
tail divided difference, even when the endpoint is an improper limit. -/
theorem integral_primitiveTail_cpow {f : Real -> Complex} (hf : Measurable f)
    (Fone s : Complex) (hs : 1 < s.re)
    (hWeight : IntegrableOn (fun t : Real => (t : Complex) ^ (1 - s) * f t) (Ioi (1 : Real))) :
    let mu := volume.restrict (Ioi (1 : Real))
    let T := fun x : Real => (x : Complex) ^ (-s) * (Fone - primitiveFromOne f x)
    And (Integrable T mu)
      (integral mu T =
        (integral mu (fun t : Real => (t : Complex) ^ (1 - s) * f t) - Fone) / (1 - s)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let w := fun x : Real => (x : Complex) ^ (-s)
  have hs' : (-s).re < -1 := by rw [Complex.neg_re]; linarith only [hs]
  have hw : Integrable w mu := integrableOn_Ioi_cpow_of_lt hs' zero_lt_one
  have hPrim := integral_primitive_cpow hf s hs hWeight
  have hInt : Integrable (fun x : Real => w x * Fone - w x * primitiveFromOne f x) mu :=
    (hw.mul_const Fone).sub hPrim.1
  refine And.intro (by simpa only [mul_sub] using hInt) ?_
  simp only [mul_sub]
  rw [integral_sub (hw.mul_const Fone) hPrim.1, hPrim.2, integral_mul_const]
  unfold w
  rw [integral_Ioi_cpow_of_lt hs' zero_lt_one, Complex.ofReal_one, Complex.one_cpow,
    show -s + 1 = 1 - s by ring]
  have hMinus : Not (s - 1 = 0) := Complex.ne_zero_of_re_pos (by
    simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hs)
  have hOther : Not (1 - s = 0) := sub_ne_zero.mpr (sub_ne_zero.mp hMinus).symm
  field_simp [hMinus, hOther]
  ring

end Robin1984.GRH
