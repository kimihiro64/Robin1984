import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# Absolute reweighting of a complete tail

This Fubini identity transfers the already established weighted explicit
formula from n=2 to n=1. Both complete tails and the outgoing boundary are
retained.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

def robinTailTriangle (v : Real -> Real) (F : Real -> Complex)
    (a t : Real) : Complex :=
  if a <= t then (v a : Complex) * F t else 0

theorem integral_robinTailTriangle_left
    {x t : Real} (v : Real -> Real) (F : Real -> Complex) :
    integral (volume.restrict (Ioi x)) (fun a => robinTailTriangle v F a t) =
      ((integral (volume.restrict (Ioc x t)) v : Real) : Complex) * F t := by
  have hFunction : (fun a => robinTailTriangle v F a t) =
      (Iic t).indicator (fun a : Real => (v a : Complex) * F t) := by
    funext a
    simp [robinTailTriangle, Set.indicator]
  rw [hFunction, setIntegral_indicator measurableSet_Iic]
  have hSet : Set.inter (Ioi x) (Iic t) = Ioc x t := by
    ext a
    rfl
  change integral (volume.restrict (Set.inter (Ioi x) (Iic t)))
    (fun a : Real => (v a : Complex) * F t) = _
  rw [hSet, integral_mul_const, integral_complex_ofReal]

theorem integral_norm_robinTailTriangle_left
    {x t : Real} {v : Real -> Real} (F : Real -> Complex)
    (hv : forall a : Real, x < a -> 0 <= v a) :
    integral (volume.restrict (Ioi x)) (fun a => norm (robinTailTriangle v F a t)) =
      integral (volume.restrict (Ioc x t)) v * norm (F t) := by
  have hFunction : (fun a : Real => norm (robinTailTriangle v F a t)) =
      (Iic t).indicator (fun a : Real => norm (v a : Complex) * norm (F t)) := by
    funext a
    by_cases ha : a <= t <;> simp [robinTailTriangle, Set.indicator, ha, norm_mul]
  rw [hFunction, setIntegral_indicator measurableSet_Iic]
  have hSet : Set.inter (Ioi x) (Iic t) = Ioc x t := by
    ext a
    rfl
  change integral (volume.restrict (Set.inter (Ioi x) (Iic t)))
    (fun a : Real => norm (v a : Complex) * norm (F t)) = _
  rw [hSet, <- integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro a ha
  dsimp only
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv a ha.1)]

theorem integral_robinTailTriangle_right
    {x a : Real} (ha : x < a) (v : Real -> Real) (F : Real -> Complex) :
    integral (volume.restrict (Ioi x)) (fun t => robinTailTriangle v F a t) =
      (v a : Complex) * integral (volume.restrict (Ioi a)) F := by
  have hFunction : (fun t => robinTailTriangle v F a t) =
      (Ici a).indicator (fun t : Real => (v a : Complex) * F t) := by
    funext t
    simp [robinTailTriangle, Set.indicator]
  rw [hFunction, setIntegral_indicator measurableSet_Ici]
  have hSet : Set.inter (Ioi x) (Ici a) = Ici a := by
    apply inter_eq_right.mpr
    intro t ht
    exact lt_of_lt_of_le ha ht
  change integral (volume.restrict (Set.inter (Ioi x) (Ici a)))
    (fun t : Real => (v a : Complex) * F t) = _
  rw [hSet, integral_Ici_eq_integral_Ioi, integral_const_mul]

/-- Absolute Fubini transfers a complete tail to an increasing weight. The
integrability assumptions are the two actual tails, not a conditional
interchange or a discarded boundary. -/
theorem robin_complete_tail_reweight
    {x : Real} {h v : Real -> Real} {F : Real -> Complex}
    (hvMeas : Measurable v) (hFMeas : Measurable F)
    (hv : forall a : Real, x < a -> 0 <= v a)
    (hvInt : forall t : Real, x < t -> IntegrableOn v (Ioc x t))
    (hPrimitive : forall t : Real, x < t ->
      integral (volume.restrict (Ioc x t)) v = h t - h x)
    (hF : IntegrableOn F (Ioi x))
    (hWeighted : IntegrableOn (fun t : Real => (h t : Complex) * F t) (Ioi x)) :
    And (IntegrableOn (fun a : Real =>
        (v a : Complex) * integral (volume.restrict (Ioi a)) F) (Ioi x))
      (integral (volume.restrict (Ioi x)) (fun t : Real => (h t : Complex) * F t) =
        (h x : Complex) * integral (volume.restrict (Ioi x)) F +
          integral (volume.restrict (Ioi x)) (fun a : Real =>
            (v a : Complex) * integral (volume.restrict (Ioi a)) F)) := by
  let J : Prod Real Real -> Complex := fun z => robinTailTriangle v F z.1 z.2
  have hMeas : Measurable J := by
    unfold J robinTailTriangle
    apply Measurable.ite (measurableSet_le measurable_fst measurable_snd)
    . fun_prop
    . exact measurable_const
  have hLeftInt : forall t : Real, x < t ->
      IntegrableOn (fun a : Real => robinTailTriangle v F a t) (Ioi x) := by
    intro t ht
    have hFunction : (fun a => robinTailTriangle v F a t) =
        (Iic t).indicator (fun a : Real => (v a : Complex) * F t) := by
      funext a
      simp [robinTailTriangle, Set.indicator]
    rw [hFunction, integrableOn_indicator_iff measurableSet_Iic]
    have hSet : Set.inter (Iic t) (Ioi x) = Ioc x t := by
      ext a
      change And (a <= t) (x < a) <-> And (x < a) (a <= t)
      exact and_comm
    change IntegrableOn (fun a : Real => (v a : Complex) * F t)
      (Set.inter (Iic t) (Ioi x))
    rw [hSet]
    exact (hvInt t ht).ofReal.mul_const (F t)
  have hNormInt : IntegrableOn (fun t : Real =>
      integral (volume.restrict (Ioi x)) (fun a : Real => norm (J (a, t)))) (Ioi x) := by
    have hRaw := (hWeighted.sub (hF.const_mul (h x : Complex))).norm
    apply IntegrableOn.congr_fun hRaw _ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.sub_apply, J]
    rw [integral_norm_robinTailTriangle_left F hv, hPrimitive t ht]
    have hDiff : 0 <= h t - h x := by
      rw [<- hPrimitive t ht]
      apply setIntegral_nonneg measurableSet_Ioc
      intro a ha
      exact hv a ha.1
    rw [<- sub_mul, <- Complex.ofReal_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hDiff]
  have hJoint : Integrable J ((volume.restrict (Ioi x)).prod (volume.restrict (Ioi x))) := by
    apply (integrable_prod_iff' hMeas.aestronglyMeasurable).mpr
    refine And.intro ?_ hNormInt
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hLeftInt t ht
  have hRightInt : IntegrableOn (fun a : Real =>
      (v a : Complex) * integral (volume.restrict (Ioi a)) F) (Ioi x) := by
    apply IntegrableOn.congr_fun hJoint.integral_prod_left _ measurableSet_Ioi
    intro a ha
    exact integral_robinTailTriangle_right ha v F
  have hSwap := integral_integral_swap (f := robinTailTriangle v F) hJoint
  have hLeft : integral (volume.restrict (Ioi x)) (fun t : Real =>
      integral (volume.restrict (Ioi x)) (fun a : Real => J (a, t))) =
      integral (volume.restrict (Ioi x)) (fun t : Real => (h t : Complex) * F t) -
        (h x : Complex) * integral (volume.restrict (Ioi x)) F := by
    calc
      _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
          (h t : Complex) * F t - (h x : Complex) * F t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only [J]
        rw [integral_robinTailTriangle_left, hPrimitive t ht, Complex.ofReal_sub, sub_mul]
      _ = _ := by
        rw [integral_sub hWeighted (hF.const_mul (h x : Complex)), integral_const_mul]
  have hRight : integral (volume.restrict (Ioi x)) (fun a : Real =>
      integral (volume.restrict (Ioi x)) (fun t : Real => J (a, t))) =
      integral (volume.restrict (Ioi x)) (fun a : Real =>
        (v a : Complex) * integral (volume.restrict (Ioi a)) F) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro a ha
    exact integral_robinTailTriangle_right ha v F
  change integral (volume.restrict (Ioi x)) (fun a : Real =>
      integral (volume.restrict (Ioi x)) (fun t : Real => J (a, t))) =
    integral (volume.restrict (Ioi x)) (fun t : Real =>
      integral (volume.restrict (Ioi x)) (fun a : Real => J (a, t))) at hSwap
  rw [hLeft, hRight] at hSwap
  refine And.intro hRightInt ?_
  exact (sub_eq_iff_eq_add.mp hSwap.symm).trans (add_comm _ _)

end

end Robin1984
