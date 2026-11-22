import Robin1984.Mathlib.Probability.Moments.MGFAnalyticContinuation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Landau's real convergence-abscissa argument for a nonnegative transform.
- Formalization note: The continuation branch uses the repository's analytic crossing theorem, and the real pole branch uses the sign of the residue.
- PROVENANCE-END
-/

/-!
# Landau's convergence argument with a signed real pole

For a nonnegative transform, a finite endpoint either admits analytic
continuation or has a nonnegative scaled limit from the convergent side.
This form allows a meromorphic comparison with negative real residues.
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace Robin1984.GRH

/-- Convergence holds below every point up to which the comparison is regular
or has only negative scaled limits approached from the left. -/
theorem mem_expDomain_below_of_analytic_or_negativeResidue
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    (hMeasurable : Measurable X)
    (hSupported : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (hStart : Set.Nonempty (integrableExpSet X mu))
    (H : Real -> Real) (target : Real)
    (hAgreement : forall a : Real, Membership.mem (interior (integrableExpSet X mu)) a ->
      a < target -> mgf X mu a = H a)
    (hBoundary : forall b : Real, b < target ->
      Or (AnalyticAt Real H b)
        (exists residue : Real, And (residue < 0)
          (Tendsto (fun a => (b - a) * H a) (nhdsWithin b (Iio b)) (nhds residue))))
    {t : Real} (ht : t < target) :
    Membership.mem (integrableExpSet X mu) t := by
  classical
  let domain := integrableExpSet X mu
  have downwards {a b : Real} (hab : a <= b) (hb : Membership.mem domain b) :
      Membership.mem domain a := by
    change Integrable (fun w => Real.exp (b * X w)) mu at hb
    change Integrable (fun w => Real.exp (a * X w)) mu
    exact hb.mono'
      (Real.continuous_exp.measurable.comp (measurable_const.mul hMeasurable)).aestronglyMeasurable
      (hSupported.mono (fun w hw => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hw)))
  change Membership.mem domain t
  by_contra hMissing
  have hUpper (b : Real) (hb : Membership.mem domain b) : b <= t :=
    le_of_not_gt (fun h => hMissing (downwards h.le hb))
  have hBounded : BddAbove domain := Exists.intro t (fun _ hb => hUpper _ hb)
  let edge : Real := sSup domain
  have hEdge : edge <= t := csSup_le hStart hUpper
  have hInterior (a : Real) (ha : a < edge) : Membership.mem (interior domain) a := by
    have hSome : exists b : Real, And (Membership.mem domain b) (a < b) := by
      by_contra hNone
      have hSmaller (x : Real) (hx : Membership.mem domain x) : x <= a :=
        le_of_not_gt (fun h => hNone (Exists.intro x (And.intro hx h)))
      exact (not_le_of_gt ha) (csSup_le hStart hSmaller)
    choose b hb using hSome
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Iio_mem_nhds hb.2) (fun _ hw => downwards hw.le hb.1)
  cases hBoundary edge (hEdge.trans_lt ht) with
  | inl hAnalytic =>
      choose b hb using exists_integrableExpSet_gt_of_analyticContinuationAt
        hSupported hInterior hAnalytic
        (fun a ha => hAgreement a (hInterior a ha) (ha.trans (hEdge.trans_lt ht)))
      exact (not_lt_of_ge (le_csSup hBounded hb.2)) hb.1
  | inr hSingular =>
      choose residue hResidue using hSingular
      have hLeft : Filter.Eventually (fun a => a < edge) (nhdsWithin edge (Iio edge)) :=
        self_mem_nhdsWithin
      have hPositive : Filter.Eventually (fun a => 0 <= (edge - a) * H a)
          (nhdsWithin edge (Iio edge)) :=
        hLeft.mono (fun a ha => by
          rw [<- hAgreement a (hInterior a ha) (ha.trans (hEdge.trans_lt ht))]
          exact mul_nonneg (sub_nonneg.mpr ha.le) mgf_nonneg)
      exact (not_le_of_gt hResidue.1) (ge_of_tendsto hResidue.2 hPositive)

end Robin1984.GRH
