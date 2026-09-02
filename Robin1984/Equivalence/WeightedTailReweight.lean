import Robin1984.Mathlib.MeasureTheory.Integral.IntervalIntegral.TailReweight

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# Absolute reweighting of a complete tail

Compatibility declarations for the project-independent complete-tail Fubini
identity maintained in the Mathlib candidate layer.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

/-- Compatibility alias for the upstream-ready triangular integrand. -/
abbrev robinTailTriangle :
    (Real -> Real) -> (Real -> Complex) -> Real -> Real -> Complex :=
  MeasureTheory.tailTriangle

/-- Compatibility theorem for integration in the triangle's left variable. -/
theorem integral_robinTailTriangle_left
    {x t : Real} (v : Real -> Real) (F : Real -> Complex) :
    integral (volume.restrict (Ioi x)) (fun a => robinTailTriangle v F a t) =
      ((integral (volume.restrict (Ioc x t)) v : Real) : Complex) * F t :=
  MeasureTheory.integral_tailTriangle_left v F

/-- Compatibility theorem for the norm integral in the left variable. -/
theorem integral_norm_robinTailTriangle_left
    {x t : Real} {v : Real -> Real} (F : Real -> Complex)
    (hv : forall a : Real, x < a -> 0 <= v a) :
    integral (volume.restrict (Ioi x)) (fun a => norm (robinTailTriangle v F a t)) =
      integral (volume.restrict (Ioc x t)) v * norm (F t) :=
  MeasureTheory.integral_norm_tailTriangle_left F hv

/-- Compatibility theorem for integration in the triangle's right variable. -/
theorem integral_robinTailTriangle_right
    {x a : Real} (ha : x < a) (v : Real -> Real) (F : Real -> Complex) :
    integral (volume.restrict (Ioi x)) (fun t => robinTailTriangle v F a t) =
      (v a : Complex) * integral (volume.restrict (Ioi a)) F :=
  MeasureTheory.integral_tailTriangle_right ha v F

/-- Compatibility theorem for absolute complete-tail reweighting. -/
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
            (v a : Complex) * integral (volume.restrict (Ioi a)) F)) :=
  MeasureTheory.complete_tail_reweight hvMeas hFMeas hv hvInt hPrimitive hF hWeighted

end

end Robin1984
