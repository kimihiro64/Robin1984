import Robin1984.GRH.DedekindTailCriterion
import Robin1984.GRH.PrimitiveMellin

/-!
# The improper-tail Dedekind criterion

The Landau argument uses the convergent finite-interval primitive and
the weighted Mellin transform on the initial half-plane. The tail is
the limit of the primitive minus its value at the cutoff.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The signed tail argument using the divided-difference Mellin transform and Landau's theorem.
- Formalization note: Bound the real improper tail by combining convergence at infinity with local integrability, then pass its exact transform to the Dedekind comparison.
- PROVENANCE-END
-/

open Filter MeasureTheory Set

namespace Robin1984.GRH

/-- The finite-interval primitive of a real error density. -/
noncomputable def realPrimitiveFromOne (g : Real -> Real) (x : Real) : Real :=
  integral (volume.restrict (Ioo 1 x)) g

/-- The tail formed by subtracting the finite primitive from its limit. -/
noncomputable def primitiveTail (g : Real -> Real) (a x : Real) : Real :=
  a - realPrimitiveFromOne g x

private theorem measurable_realPrimitiveFromOne {g : Real -> Real} (hg : Measurable g) :
    Measurable (realPrimitiveFromOne g) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let D : Set (Prod Real Real) := {p | p.2 < p.1}
  have hD : MeasurableSet D := (isOpen_lt continuous_snd continuous_fst).measurableSet
  let K : Prod Real Real -> Real := D.indicator (fun p => g p.2)
  have hK : Measurable K := (hg.comp measurable_snd).indicator hD
  have hStrong : StronglyMeasurable (fun x : Real =>
      integral mu (fun t : Real => K (x, t))) := hK.stronglyMeasurable.integral_prod_right'
  have hEq : (fun x : Real => integral mu (fun t : Real => K (x, t))) = realPrimitiveFromOne g := by
    funext x
    have hSlice : (fun t : Real => K (x, t)) = (Iio x).indicator g := by
      funext t
      by_cases ht : t < x
      case pos =>
        change D.indicator _ (x, t) = (Iio x).indicator _ t
        rw [indicator_of_mem (show Membership.mem D (x, t) from ht),
          indicator_of_mem (show Membership.mem (Iio x) t from ht)]
      case neg =>
        change D.indicator _ (x, t) = (Iio x).indicator _ t
        rw [indicator_of_notMem (show Not (Membership.mem D (x, t)) from ht),
          indicator_of_notMem (show Not (Membership.mem (Iio x) t) from ht)]
    rw [hSlice, integral_indicator measurableSet_Iio]
    change integral ((volume.restrict (Ioi (1 : Real))).restrict (Iio x)) g = _
    rw [Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio, realPrimitiveFromOne]
  rw [<- hEq]
  exact hStrong.measurable

private theorem primitiveTail_norm_bounded {g : Real -> Real} {a : Real}
    (hLocal : forall b : Real, 1 < b -> IntegrableOn g (Ioo 1 b))
    (hLimit : Tendsto (realPrimitiveFromOne g) atTop (nhds a)) :
    exists M : Real, And (0 <= M) (forall x : Real, 1 < x -> norm (primitiveTail g a x) <= M) := by
  have hTail : Tendsto (primitiveTail g a) atTop (nhds (0 : Real)) := by
    have h : Tendsto (primitiveTail g a) atTop (nhds (a - a)) :=
      (tendsto_const_nhds : Tendsto (fun _ : Real => a) atTop (nhds a)).sub hLimit
    simpa only [sub_self] using h
  have hSmall : Filter.Eventually (fun x => norm (primitiveTail g a x) < 1) atTop := by
    have hNorm : Tendsto (fun x => norm (primitiveTail g a x)) atTop (nhds (0 : Real)) := by
      simpa only [norm_zero] using hTail.norm
    exact hNorm.eventually (Iio_mem_nhds zero_lt_one)
  choose b hb using eventually_atTop.mp hSmall
  let B := max 2 b
  let m := integral (volume.restrict (Ioo (1 : Real) B)) (fun t => norm (g t))
  have hB : 1 < B := (by norm_num : (1 : Real) < 2).trans_le (le_max_left _ _)
  refine Exists.intro (max 1 (norm a + m)) (And.intro (zero_le_one.trans (le_max_left _ _)) ?_)
  intro x hx
  by_cases hL : B <= x
  case pos =>
    exact (hb x ((le_max_right 2 b).trans hL)).le.trans (le_max_left _ _)
  case neg =>
    have hSub : Set.Subset (Ioo (1 : Real) x) (Ioo 1 B) := fun t ht =>
      And.intro ht.1 (ht.2.trans (lt_of_not_ge hL))
    have hPrim : norm (realPrimitiveFromOne g x) <= m :=
      (norm_integral_le_integral_norm g).trans
        (setIntegral_mono_set (hLocal B hB).norm
          (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (Filter.Eventually.of_forall (fun _ ht => hSub ht)))
    calc
      norm (primitiveTail g a x) <= norm a + norm (realPrimitiveFromOne g x) :=
        norm_sub_le a (realPrimitiveFromOne g x)
      _ <= norm a + m := add_le_add (le_refl _) hPrim
      _ <= max 1 (norm a + m) := le_max_right _ _

/-- The signed improper-tail bound implies nonvanishing in the open
right half-plane beyond one half. -/
theorem ne_zero_of_eventual_primitiveTailBound {g : Real -> Real} {f : Complex -> Complex} {a : Real}
    (hMeas : Measurable g)
    (hLocal : forall b : Real, 1 < b -> IntegrableOn g (Ioo 1 b))
    (hLimit : Tendsto (realPrimitiveFromOne g) atTop (nhds a))
    (hf : AnalyticOnNhd Complex f {z : Complex | (1 / 2 : Real) < z.re})
    (hNoRealHigh : forall b : Real, 1 <= b -> Not (f (b : Complex) = 0))
    (hAtOne : logDeriv f 1 + 1 + (a : Complex) = 0)
    (hSeries : forall s : Complex, 1 < s.re ->
      let mu := volume.restrict (Ioi (1 : Real))
      let W := fun t : Real => (t : Complex) ^ (1 - s) * (g t : Complex)
      And (Integrable W mu) (integral mu W = -(logDeriv f s + 1) / s))
    (hBound : exists C t : Real, forall x : Real, t < x -> -x * primitiveTail g a x <= C * Real.sqrt x)
    {z : Complex} (hz : (1 / 2 : Real) < z.re) : Not (f z = 0) := by
  have hTailMeas : Measurable (primitiveTail g a) :=
    measurable_const.sub (measurable_realPrimitiveFromOne hMeas)
  refine ne_zero_of_eventual_mellinTailBound hTailMeas
    (primitiveTail_norm_bounded hLocal hLimit) hf hNoRealHigh hAtOne ?_ hBound hz
  intro s hs
  have h := hSeries s hs
  let mu := volume.restrict (Ioi (1 : Real))
  let F := fun t : Real => (g t : Complex)
  let W := fun x : Real => (x : Complex) ^ (-s) * ((a : Complex) - primitiveFromOne F x)
  have hF : Measurable F := Complex.continuous_ofReal.measurable.comp hMeas
  have hMellin := integral_primitiveTail_cpow hF (a : Complex) s hs h.1
  have hEq (x : Real) : (primitiveTail g a x : Complex) =
      (a : Complex) - primitiveFromOne F x := by
    rw [primitiveTail, Complex.ofReal_sub, primitiveFromOne, integral_complex_ofReal, realPrimitiveFromOne]
  have hW : (fun x : Real => (x : Complex) ^ (-s) * (primitiveTail g a x : Complex)) = W := by
    funext x
    rw [hEq]
  change And (Integrable _ mu) (integral mu _ = _)
  refine And.intro (hMellin.1.congr (Filter.Eventually.of_forall (congrFun hW.symm))) ?_
  calc
    _ = integral mu W := congrArg (integral mu) hW
    _ = _ := hMellin.2.trans (by rw [h.2])

end Robin1984.GRH
