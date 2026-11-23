import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Abelian limit of a normalized exponential average.
- Formalization note: Split the integrand into a finite initial part and a tail where the pointwise limit gives a uniform bound.
- PROVENANCE-END
-/

/-!
# The Abelian limit for the exponential average

Integrability on each finite initial interval and a limit at infinity
suffice for convergence of the normalized Laplace average as its positive
scale tends to zero.
-/

open Filter MeasureTheory Set Topology

namespace Robin1984.GRH

/-- The exponential probability average recovers the limit of a locally
integrable measurable real function at infinity. -/
theorem tendsto_mul_integral_exp_neg_of_tendsto {G : Real -> Real} {L : Real}
    (hMeas : Measurable G)
    (hLocal : forall a : Real, 0 < a -> IntegrableOn G (Ioc 0 a))
    (hLimit : Tendsto G atTop (nhds L)) :
    Tendsto (fun u : Real => u * integral (volume.restrict (Ioi (0 : Real)))
      (fun t => G t * Real.exp (-(u * t)))) (nhdsWithin 0 (Ioi (0 : Real))) (nhds L) := by
  apply Metric.tendsto_nhds.mpr
  intro eps hEps
  have hFar : Filter.Eventually (fun t : Real => norm (G t - L) < eps / 2) atTop := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hLimit (eps / 2) (half_pos hEps))
  let R := Classical.choose (eventually_atTop.mp hFar)
  have hR := Classical.choose_spec (eventually_atTop.mp hFar)
  let a := max 1 R
  have ha : 0 < a := zero_lt_one.trans_le (le_max_left _ _)
  have hA (t : Real) (ht : a < t) : norm (G t - L) <= eps / 2 :=
    (hR t ((le_max_right _ _).trans ht.le)).le
  let Head := (Ioc 0 a).indicator (fun t : Real => norm (G t - L))
  let M := integral (volume.restrict (Ioc (0 : Real) a)) (fun t => norm (G t - L))
  have hHeadPos (t : Real) : 0 <= Head t := by
    classical
    by_cases ht : Membership.mem (Ioc 0 a) t
    case pos => simp only [Head, Set.indicator_of_mem ht, norm_nonneg]
    case neg =>
      change 0 <= (Ioc 0 a).indicator (fun q : Real => norm (G q - L)) t
      rw [Set.indicator_of_notMem ht]
  have hLocalConst : IntegrableOn (fun _ : Real => L) (Icc 0 a) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hHeadI : Integrable Head volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (((hLocal a ha).sub (hLocalConst.mono_set Ioc_subset_Icc_self)).norm)
  have hM : 0 <= M := integral_nonneg (fun _ => norm_nonneg _)
  have hScaleDen : 0 < M + 1 := add_pos_of_nonneg_of_pos hM zero_lt_one
  let delta := (eps / 2) / (M + 1)
  have hDelta : 0 < delta := div_pos (half_pos hEps) hScaleDen
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hDelta)]
    with u hu hU
  change 0 < u at hu
  change u < delta at hU
  let mu := volume.restrict (Ioi (0 : Real))
  let Z := fun t : Real => Real.exp (-(u * t))
  let F := fun t : Real => (G t - L) * Z t
  have hZ : Integrable Z mu := by
    change IntegrableOn (fun t : Real => Real.exp (-(u * t))) (Ioi (0 : Real))
    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a := -u) (neg_lt_zero.mpr hu) 0
  have hMass : integral mu Z = Inv.inv u := by
    simpa only [mu, Z, neg_mul, mul_zero, Real.exp_zero, neg_div_neg_eq, one_div] using
      integral_exp_mul_Ioi (a := -u) (neg_lt_zero.mpr hu) (0 : Real)
  have hFMeas : AEStronglyMeasurable F mu :=
    ((hMeas.sub measurable_const).mul
      (Real.continuous_exp.measurable.comp ((measurable_const.mul measurable_id).neg))).aestronglyMeasurable
  have hHeadR : Integrable Head mu := hHeadI.integrableOn
  have hHeadMass : integral mu Head <= M := by
    have h := integral_mono_measure (Measure.restrict_le_self (s := Ioi (0 : Real)))
      (Filter.Eventually.of_forall hHeadPos) hHeadI
    have heq : integral volume Head = M := integral_indicator measurableSet_Ioc
    exact h.trans_eq heq
  have hC : Integrable (fun t => eps / 2 * Z t) mu := hZ.const_mul _
  have hCtrl : Integrable (fun t => Head t + eps / 2 * Z t) mu := hHeadR.add hC
  have hDom : Filter.Eventually (fun t : Real => norm (F t) <= Head t + eps / 2 * Z t) (ae mu) := by
    change Filter.Eventually (fun t : Real => norm (F t) <= Head t + eps / 2 * Z t)
      (ae (volume.restrict (Ioi (0 : Real))))
    rw [ae_restrict_iff' measurableSet_Ioi]
    apply Filter.Eventually.of_forall
    intro t ht
    have hZ0 : 0 < Z t := Real.exp_pos _
    have hZ1 : Z t <= 1 := Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hu.le (show 0 < t from ht).le))
    change norm ((G t - L) * Z t) <= _
    rw [norm_mul, Real.norm_of_nonneg hZ0.le]
    by_cases hta : t <= a
    case pos =>
      have hIoc : Membership.mem (Ioc 0 a) t := And.intro ht hta
      have hAt : Head t = norm (G t - L) := Set.indicator_of_mem hIoc _
      rw [hAt]
      exact (mul_le_of_le_one_right (norm_nonneg _) hZ1).trans
        (le_add_of_nonneg_right (mul_nonneg (half_pos hEps).le hZ0.le))
    case neg =>
      exact (mul_le_mul_of_nonneg_right (hA t (lt_of_not_ge hta)) hZ0.le).trans
        (le_add_of_nonneg_left (hHeadPos t))
  have hF : Integrable F mu := hCtrl.mono' hFMeas hDom
  have hNormF : norm (integral mu F) <= M + eps / 2 * Inv.inv u := by
    calc
      _ <= integral mu (fun t => norm (F t)) := norm_integral_le_integral_norm F
      _ <= integral mu (fun t => Head t + eps / 2 * Z t) := integral_mono_ae hF.norm hCtrl hDom
      _ = integral mu Head + eps / 2 * Inv.inv u := by
        rw [integral_add hHeadR hC, integral_const_mul, hMass]
      _ <= _ := add_le_add hHeadMass le_rfl
  have hRep : (fun t => G t * Z t) = fun t => F t + L * Z t := by
    funext t
    change G t * Z t = (G t - L) * Z t + L * Z t
    ring
  have hInv : u * Inv.inv u = 1 := by field_simp [hu.ne']
  have hCenter : u * integral mu (fun t => G t * Z t) - L = u * integral mu F := by
    rw [hRep, integral_add hF (hZ.const_mul L), integral_const_mul, hMass]
    calc
      _ = u * integral mu F + L * (u * Inv.inv u) - L := by ring
      _ = _ := by rw [hInv, mul_one]; ring
  have hSmall := mul_lt_mul_of_pos_right hU hScaleDen
  have hd : delta * (M + 1) = eps / 2 := by
    unfold delta
    field_simp [hScaleDen.ne']
  rw [hd] at hSmall
  change dist (u * integral mu (fun t => G t * Z t)) L < eps
  rw [dist_eq_norm, hCenter, norm_mul, Real.norm_of_nonneg hu.le]
  calc
    _ <= u * (M + eps / 2 * Inv.inv u) := mul_le_mul_of_nonneg_left hNormF hu.le
    _ = u * M + eps / 2 := by
      rw [show u * (M + eps / 2 * Inv.inv u) =
        u * M + eps / 2 * (u * Inv.inv u) by ring, hInv, mul_one]
    _ < eps := by nlinarith only [hSmall, hu]

end Robin1984.GRH
