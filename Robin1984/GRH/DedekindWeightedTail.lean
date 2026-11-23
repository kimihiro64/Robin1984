import Robin1984.GRH.DedekindPrimitiveConvergence
import Robin1984.GRH.MertensTailIntegrationByParts
import Robin1984.GRH.MertensWeightedTailIntegrability

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Integration by parts for the signed weighted Dedekind Mertens expansion.
- Formalization note: The weighted Dedekind Chebyshev tail.
- PROVENANCE-END
-/

/-!
# The weighted Dedekind Chebyshev tail

Finite integration by parts converts the locally integrable Chebyshev
error into an absolutely integrable derivative-weighted primitive.
-/

open Filter MeasureTheory NumberField Robin1984.GRH Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

private theorem intervalIntegrable_dedekindError {a b : Real} (ha : 1 <= a) (hab : a <= b) :
    IntervalIntegrable (dedekindChebyshevErrorRatio K) volume a b := by
  have hOne : IntegrableOn (dedekindChebyshevErrorRatio K) (Ioc 1 b) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact dedekindChebyshevErrorRatio_integrableOn_Ioo K b
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (hOne.mono_set (fun _ ht => And.intro (ha.trans_lt ht.1) ht.2))

private theorem intervalIntegral_dedekindError_one {b : Real} (hb : 1 <= b) :
    intervalIntegral (dedekindChebyshevErrorRatio K) 1 b volume =
      realPrimitiveFromOne (dedekindChebyshevErrorRatio K) b := by
  rw [intervalIntegral.integral_of_le hb, integral_Ioc_eq_integral_Ioo, realPrimitiveFromOne]

private theorem continuousOn_dedekindErrorPrimitive :
    ContinuousOn (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) (Ioi (1 : Real)) := by
  intro x hx
  have hxb : x < x + 1 := lt_add_of_pos_right x zero_lt_one
  have hb : 1 <= x + 1 := hx.le.trans hxb.le
  have hxC : Membership.mem (uIcc 1 (x + 1)) x := by
    rw [uIcc_of_le hb]
    exact And.intro hx.le hxb.le
  have h := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_dedekindError K le_rfl hb) left_mem_uIcc
  have hNear : Membership.mem (nhdsWithin x (Ioi (1 : Real))) (uIcc 1 (x + 1)) := by
    rw [uIcc_of_le hb]
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxb)] with y hy hy'
    exact And.intro hy.le hy'.le
  exact ((h x hxC).mono_of_mem_nhdsWithin hNear).congr
    (fun _ hy => (intervalIntegral_dedekindError_one K hy.le).symm)
    (intervalIntegral_dedekindError_one K hx.le).symm

private theorem intervalIntegral_dedekindError {x y : Real} (hx : 1 <= x) (hxy : x <= y) :
    intervalIntegral (dedekindChebyshevErrorRatio K) x y volume =
      realPrimitiveFromOne (dedekindChebyshevErrorRatio K) y -
        realPrimitiveFromOne (dedekindChebyshevErrorRatio K) x := by
  have hAdd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_dedekindError K le_rfl hx) (intervalIntegrable_dedekindError K hx hxy)
  rw [intervalIntegral_dedekindError_one K hx, intervalIntegral_dedekindError_one K (hx.trans hxy)] at hAdd
  linarith only [hAdd]

theorem intervalIntegral_dedekindWeightedError_parts {c x y : Real} (hx : 1 < x) (hxy : x <= y) :
    let g := dedekindChebyshevErrorRatio K
    let T := primitiveTail g c
    intervalIntegral (fun t => g t * mertensTailWeight t) x y volume =
      T x * mertensTailWeight x - T y * mertensTailWeight y +
        intervalIntegral (fun t => T t * mertensTailSlope t) x y volume := by
  let g := dedekindChebyshevErrorRatio K
  let T := primitiveTail g c
  let Tlocal := fun t : Real => T x - intervalIntegral g x t volume
  have hDomain : forall {t : Real}, Membership.mem (uIcc x y) t ->
      Membership.mem (Ioi (1 : Real)) t := by
    intro t ht
    rw [uIcc_of_le hxy] at ht
    exact hx.trans_le ht.1
  have hMatch : EqOn Tlocal T (uIcc x y) := by
    intro t ht
    rw [uIcc_of_le hxy] at ht
    change T x - intervalIntegral (dedekindChebyshevErrorRatio K) x t volume = T t
    rw [intervalIntegral_dedekindError K hx.le ht.1]
    simp only [T, primitiveTail, g]
    ring
  have hInt := intervalIntegrable_dedekindError K hx.le hxy
  have hPart := intervalIntegral_mul_eq_primitiveTail_parts (c := T x) hInt
    (fun t ht => hasDerivAt_mertensTailWeight (hDomain ht))
    (continuousOn_mertensTailSlope.mono (fun _ ht => hDomain ht))
  change intervalIntegral (fun t => g t * mertensTailWeight t) x y volume =
    Tlocal x * mertensTailWeight x - Tlocal y * mertensTailWeight y +
      intervalIntegral (fun t => Tlocal t * mertensTailSlope t) x y volume at hPart
  have hCon : intervalIntegral (fun t => Tlocal t * mertensTailSlope t) x y volume =
      intervalIntegral (fun t => T t * mertensTailSlope t) x y volume :=
    intervalIntegral.integral_congr (fun t ht => congrArg (fun v => v * mertensTailSlope t) (hMatch ht))
  rw [hMatch left_mem_uIcc, hMatch right_mem_uIcc, hCon] at hPart
  exact hPart

private theorem tendsto_dedekindPrimitiveTail {c : Real}
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    Tendsto (primitiveTail (dedekindChebyshevErrorRatio K) c) atTop (nhds 0) := by
  rw [<- sub_self c]
  exact tendsto_const_nhds.sub hLimit

/-- The limiting primitive tail is continuous above one. -/
theorem continuousOn_dedekindPrimitiveTail (c : Real) :
    ContinuousOn (primitiveTail (dedekindChebyshevErrorRatio K) c) (Ioi (1 : Real)) :=
  continuousOn_const.sub (continuousOn_dedekindErrorPrimitive K)

private theorem exists_bound_dedekindPrimitiveTail {c x : Real} (hx : 1 < x)
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    Exists (fun M : Real => forall t : Real, Membership.mem (Ioi x) t ->
      norm (primitiveTail (dedekindChebyshevErrorRatio K) c t) <= M) := by
  let T := primitiveTail (dedekindChebyshevErrorRatio K) c
  have hFar : Filter.Eventually (fun t : Real => norm (T t) < 1) atTop := by
    simpa only [dist_eq_norm, sub_zero] using
      (Metric.tendsto_nhds.mp (tendsto_dedekindPrimitiveTail K hLimit) 1 zero_lt_one)
  let R := Classical.choose (eventually_atTop.mp hFar)
  have hR := Classical.choose_spec (eventually_atTop.mp hFar)
  have hTC : ContinuousOn T (Icc x (max x R)) :=
    (continuousOn_dedekindPrimitiveTail K c).mono (fun _ ht => hx.trans_le ht.1)
  have hCompact := isCompact_Icc.exists_bound_of_continuousOn hTC
  let M := Classical.choose hCompact
  have hM := Classical.choose_spec hCompact
  refine Exists.intro (max M 1) ?_
  intro t ht
  by_cases hRt : R <= t
  case pos => exact (hR t hRt).le.trans (le_max_right _ _)
  case neg =>
    have htR : t <= max x R := (le_of_not_ge hRt).trans (le_max_right _ _)
    exact (hM t (And.intro ht.le htR)).trans (le_max_left _ _)

/-- The signed improper weighted tail, expressed through a convergent
ordinary integral of the primitive and the derivative of the weight. -/
noncomputable def dedekindMertensWeightedTail (c x : Real) : Real :=
  Neg.neg (primitiveTail (dedekindChebyshevErrorRatio K) c x * mertensTailWeight x) -
    integral (volume.restrict (Ioi x))
      (fun t => primitiveTail (dedekindChebyshevErrorRatio K) c t * mertensTailSlope t)

theorem tendsto_dedekindMertensWeightedTail_integrals {c x : Real} (hx : 1 < x)
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    Tendsto (fun y : Real => intervalIntegral
      (fun t => dedekindChebyshevErrorRatio K t * mertensTailWeight t) x y volume)
      atTop (nhds (-dedekindMertensWeightedTail K c x)) := by
  let T := primitiveTail (dedekindChebyshevErrorRatio K) c
  let D := fun t : Real => T t * mertensTailSlope t
  have hBounds := exists_bound_dedekindPrimitiveTail K hx hLimit
  have hMeas : AEStronglyMeasurable T (volume.restrict (Ioi x)) :=
    ((continuousOn_dedekindPrimitiveTail K c).mono (fun _ ht => hx.trans ht)).aestronglyMeasurable
      measurableSet_Ioi
  have hD : IntegrableOn D (Ioi x) :=
    (norm_integral_mul_mertensTailSlope_le hx hMeas (Classical.choose_spec hBounds)).1
  have hEndpoint : Tendsto (fun y : Real => T y * mertensTailWeight y) atTop (nhds 0) := by
    simpa only [zero_mul] using (tendsto_dedekindPrimitiveTail K hLimit).mul tendsto_mertensTailWeight
  have hIntegrals : Tendsto (fun y : Real => intervalIntegral D x y volume) atTop
      (nhds (integral (volume.restrict (Ioi x)) D)) :=
    intervalIntegral_tendsto_integral_Ioi x hD
      (tendsto_id : Tendsto (fun y : Real => y) atTop atTop)
  have hAux : Tendsto (fun y : Real =>
      T x * mertensTailWeight x - T y * mertensTailWeight y + intervalIntegral D x y volume)
      atTop (nhds (T x * mertensTailWeight x + integral (volume.restrict (Ioi x)) D)) := by
    have hConst : Tendsto (fun _ : Real => T x * mertensTailWeight x) atTop
        (nhds (T x * mertensTailWeight x)) := tendsto_const_nhds
    simpa only [sub_zero] using (hConst.sub hEndpoint).add hIntegrals
  have hEq : -(dedekindMertensWeightedTail K c x) =
      T x * mertensTailWeight x + integral (volume.restrict (Ioi x)) D := by
    unfold dedekindMertensWeightedTail
    dsimp [T, D]
    ring
  rw [hEq]
  refine hAux.congr' ?_
  filter_upwards [eventually_ge_atTop x] with y hy
  exact (intervalIntegral_dedekindWeightedError_parts K hx hy (c := c)).symm

/-- The weighted tail is little-o of the Abel weight. This boundary
estimate is needed for the inverse integration by parts. -/
theorem tendsto_dedekindMertensWeightedTail_mul_deweight {c : Real}
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    Tendsto (fun x : Real => dedekindMertensWeightedTail K c x * mertensDeweight x)
      atTop (nhds 0) := by
  let T := primitiveTail (dedekindChebyshevErrorRatio K) c
  apply Metric.tendsto_nhds.mpr
  intro eps hEps
  have hSmall : Filter.Eventually (fun t : Real => norm (T t) < eps / 2) atTop := by
    simpa only [dist_eq_norm, sub_zero] using
      (Metric.tendsto_nhds.mp (tendsto_dedekindPrimitiveTail K hLimit) (eps / 2) (half_pos hEps))
  let R := Classical.choose (eventually_atTop.mp hSmall)
  have hR := Classical.choose_spec (eventually_atTop.mp hSmall)
  filter_upwards [eventually_ge_atTop (max (2 : Real) R)] with x hx
  have hx1 : 1 < x := (show (1 : Real) < 2 by norm_num).trans_le ((le_max_left _ _).trans hx)
  have hxR : R <= x := (le_max_right _ _).trans hx
  have hX := hR x hxR
  let J := integral (volume.restrict (Ioi x)) (fun t => T t * mertensTailSlope t)
  have hMeas : AEStronglyMeasurable T (volume.restrict (Ioi x)) :=
    ((continuousOn_dedekindPrimitiveTail K c).mono (fun _ ht => hx1.trans ht)).aestronglyMeasurable
      measurableSet_Ioi
  have hJ : norm J <= eps / 2 * mertensTailWeight x :=
    (norm_integral_mul_mertensTailSlope_le hx1 hMeas
      (fun t ht => (hR t (hxR.trans ht.le)).le)).2
  have hInverse := mertensDeweight_mul_tailWeight hx1
  have hU : 0 <= mertensDeweight x :=
    div_nonneg (sq_nonneg _) (add_nonneg zero_le_one (Real.log_pos hx1).le)
  have hRew : dedekindMertensWeightedTail K c x * mertensDeweight x =
      -(T x + mertensDeweight x * J) := by
    change (-(T x * mertensTailWeight x) - J) * mertensDeweight x = _
    calc
      _ = -(T x * (mertensDeweight x * mertensTailWeight x) + mertensDeweight x * J) := by ring
      _ = _ := by rw [hInverse, mul_one]
  change dist (dedekindMertensWeightedTail K c x * mertensDeweight x) 0 < eps
  rw [dist_eq_norm, sub_zero, hRew, norm_neg]
  calc
    _ <= norm (T x) + mertensDeweight x * norm J := by
      calc
        _ <= norm (T x) + norm (mertensDeweight x * J) := norm_add_le _ _
        _ = _ := by rw [norm_mul, Real.norm_of_nonneg hU]
    _ <= norm (T x) + mertensDeweight x * (eps / 2 * mertensTailWeight x) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hJ hU)
    _ = norm (T x) + eps / 2 := by
      rw [show mertensDeweight x * (eps / 2 * mertensTailWeight x) =
        eps / 2 * (mertensDeweight x * mertensTailWeight x) by ring, hInverse, mul_one]
    _ < eps := by linarith only [hX]

theorem tendsto_dedekindMertensWeightedTail {c : Real}
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    Tendsto (dedekindMertensWeightedTail K c) atTop (nhds 0) := by
  have h : Tendsto (fun x : Real =>
      (dedekindMertensWeightedTail K c x * mertensDeweight x) * mertensTailWeight x)
      atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_dedekindMertensWeightedTail_mul_deweight K hLimit).mul tendsto_mertensTailWeight
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  rw [mul_assoc, mertensDeweight_mul_tailWeight ((show (1 : Real) < 2 by norm_num).trans_le hx), mul_one]

private theorem intervalIntegrable_dedekindWeightedError {x y : Real} (hx : 1 < x) (hxy : x <= y) :
    IntervalIntegrable (fun t => dedekindChebyshevErrorRatio K t * mertensTailWeight t) volume x y := by
  have hWeight : ContinuousOn mertensTailWeight (uIcc x y) := by
    intro t ht
    rw [uIcc_of_le hxy] at ht
    exact (hasDerivAt_mertensTailWeight (hx.trans_le ht.1)).continuousAt.continuousWithinAt
  apply intervalIntegrable_iff.mpr
  have hError : IntegrableOn (dedekindChebyshevErrorRatio K) (uIoc x y) :=
    intervalIntegrable_iff.mp (intervalIntegrable_dedekindError K hx.le hxy)
  exact hError.mul_continuousOn_of_subset hWeight measurableSet_uIoc isCompact_uIcc uIoc_subset_uIcc

private theorem intervalIntegral_dedekindWeightedError_eq_tail_sub {c x y : Real}
    (hx : 1 < x) (hxy : x <= y)
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    intervalIntegral (fun t => dedekindChebyshevErrorRatio K t * mertensTailWeight t) x y volume =
      dedekindMertensWeightedTail K c y - dedekindMertensWeightedTail K c x := by
  let weightedError := fun t : Real => dedekindChebyshevErrorRatio K t * mertensTailWeight t
  let A := intervalIntegral weightedError x y volume
  have hConst : Tendsto (fun _ : Real => A) atTop (nhds A) := tendsto_const_nhds
  have hY := tendsto_dedekindMertensWeightedTail_integrals K (hx.trans_le hxy) hLimit
  have hX := tendsto_dedekindMertensWeightedTail_integrals K hx hLimit
  have hEq : Filter.EventuallyEq atTop
      (fun z : Real => A + intervalIntegral weightedError y z volume)
      (fun z : Real => intervalIntegral weightedError x z volume) := by
    filter_upwards [eventually_ge_atTop y] with z hz
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_dedekindWeightedError K hx hxy)
      (intervalIntegrable_dedekindWeightedError K (hx.trans_le hxy) hz)
  have hAgreement := tendsto_nhds_unique ((hConst.add hY).congr' hEq) hX
  change A = _
  linarith only [hAgreement]

theorem continuousOn_dedekindMertensWeightedTail_Icc {c x y : Real}
    (hx : 1 < x) (hxy : x <= y)
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    ContinuousOn (dedekindMertensWeightedTail K c) (Icc x y) := by
  let H := dedekindMertensWeightedTail K c
  let W := fun t : Real => dedekindChebyshevErrorRatio K t * mertensTailWeight t
  rw [<- uIcc_of_le hxy]
  have hPrim := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_dedekindWeightedError K hx hxy) left_mem_uIcc
  have hLocal : ContinuousOn (fun t : Real => H x + intervalIntegral W x t volume) (uIcc x y) :=
    continuousOn_const.add hPrim
  refine hLocal.congr ?_
  intro t ht
  rw [uIcc_of_le hxy] at ht
  have h := intervalIntegral_dedekindWeightedError_eq_tail_sub K hx ht.1 hLimit
  change intervalIntegral W x t volume = H t - H x at h
  change H t = H x + intervalIntegral W x t volume
  linarith only [h]

theorem continuousOn_mertensDeweightSlope :
    ContinuousOn mertensDeweightSlope (Ioi (1 : Real)) := by
  have hLog : ContinuousOn Real.log (Ioi (1 : Real)) := fun _ ht =>
    (Real.continuousAt_log (zero_lt_one.trans ht).ne').continuousWithinAt
  have hDiv : ContinuousOn (fun t : Real => (1 : Real) / t) (Ioi (1 : Real)) :=
    continuousOn_const.div continuousOn_id (fun _ ht => (zero_lt_one.trans ht).ne')
  have hDen : ContinuousOn (fun t : Real => (1 + Real.log t) ^ 2) (Ioi (1 : Real)) :=
    (continuousOn_const.add hLog).pow 2
  have hFrac : ContinuousOn (fun t : Real =>
      Real.log t * (Real.log t + 2) / (1 + Real.log t) ^ 2) (Ioi (1 : Real)) :=
    (hLog.mul (hLog.add continuousOn_const)).div hDen
      (fun t ht => pow_ne_zero _ (add_pos zero_lt_one (Real.log_pos ht)).ne')
  have hInv : ContinuousOn (fun t : Real => Inv.inv t) (Ioi (1 : Real)) := by
    simpa only [one_div] using hDiv
  exact hInv.mul hFrac

/-- Exact finite inverse identity for the signed weighted tail. -/
theorem intervalIntegral_deweight_dedekindMertensTail {c x y : Real} (hx : 1 < x) (hxy : x <= y)
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    let T := primitiveTail (dedekindChebyshevErrorRatio K) c
    let H := dedekindMertensWeightedTail K c
    T y - T x = H x * mertensDeweight x - H y * mertensDeweight y +
      intervalIntegral (fun t => H t * mertensDeweightSlope t) x y volume := by
  let g := dedekindChebyshevErrorRatio K
  let T := primitiveTail g c
  let H := dedekindMertensWeightedTail K c
  let W := fun t : Real => g t * mertensTailWeight t
  let S := fun t : Real => -H x - intervalIntegral W x t volume
  have hDomain (t : Real) (ht : Membership.mem (uIcc x y) t) : 1 < t := by
    rw [uIcc_of_le hxy] at ht
    exact hx.trans_le ht.1
  have hLocal : EqOn S (fun t => -H t) (uIcc x y) := by
    intro t ht
    rw [uIcc_of_le hxy] at ht
    change -H x - intervalIntegral W x t volume = -H t
    have hDiff := intervalIntegral_dedekindWeightedError_eq_tail_sub K hx ht.1 hLimit
    change intervalIntegral W x t volume = H t - H x at hDiff
    rw [hDiff]
    ring
  have hPart := intervalIntegral_mul_eq_primitiveTail_parts (c := -H x)
    (intervalIntegrable_dedekindWeightedError K hx hxy)
    (fun t ht => hasDerivAt_mertensDeweight (hDomain t ht))
    (continuousOn_mertensDeweightSlope.mono (fun _ ht => hDomain _ ht))
  change intervalIntegral (fun t => W t * mertensDeweight t) x y volume =
    S x * mertensDeweight x - S y * mertensDeweight y +
      intervalIntegral (fun t => S t * mertensDeweightSlope t) x y volume at hPart
  have hLeft : intervalIntegral (fun t => W t * mertensDeweight t) x y volume = T x - T y := by
    calc
      _ = intervalIntegral g x y volume := by
        apply intervalIntegral.integral_congr
        intro t ht
        change g t * mertensTailWeight t * mertensDeweight t = g t
        rw [show g t * mertensTailWeight t * mertensDeweight t =
          g t * (mertensDeweight t * mertensTailWeight t) by ring,
          mertensDeweight_mul_tailWeight (hDomain t ht), mul_one]
      _ = _ := by
        rw [intervalIntegral_dedekindError K hx.le hxy]
        simp only [T, primitiveTail, g]
        ring
  have hRight : intervalIntegral (fun t => S t * mertensDeweightSlope t) x y volume =
      -(intervalIntegral (fun t => H t * mertensDeweightSlope t) x y volume) := by
    rw [<- intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    change S t * mertensDeweightSlope t = -(H t * mertensDeweightSlope t)
    rw [hLocal ht, neg_mul]
  rw [hLeft, hLocal left_mem_uIcc, hLocal right_mem_uIcc, hRight] at hPart
  change T y - T x = _
  linarith only [hPart]

/-- The additive constant from the signed improper Chebyshev primitive.
Its identification with Euler's constant plus the log residue uses
the Abelian zeta identity separately. -/
noncomputable def dedekindMertensConstantFromPrimitive (c a : Real) : Real :=
  Inv.inv (Real.log a) - Real.log (Real.log a) - dedekindMertensWeightedTail K c a

theorem dedekindMertensPrimePowerSum_eq_weightedTail {c a x : Real}
    (ha : 1 < a) (ha2 : a < 2) (hax : a <= x)
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    dedekindMertensPrimePowerSum K x =
      Real.log (Real.log x) + dedekindMertensConstantFromPrimitive K c a +
        mertensPrimePowerWeight x * (dedekindChebyshev K x - x) +
        dedekindMertensWeightedTail K c x := by
  have hChart : intervalIntegral (fun t => dedekindChebyshevErrorRatio K t * mertensTailWeight t)
      a x volume = integral (volume.restrict (Ioc a x))
        (fun t => (dedekindChebyshev K t - t) * mertensAbelKernel t) := by
    rw [intervalIntegral.integral_of_le hax]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht1 : 1 < t := ha.trans ht.1
    have ht0 : 0 < t := zero_lt_one.trans ht1
    change dedekindChebyshevErrorRatio K t * mertensTailWeight t =
      (dedekindChebyshev K t - t) * mertensAbelKernel t
    rw [mertensTailWeight_eq_mul_kernel ht1, dedekindChebyshevErrorRatio]
    field_simp [ht0.ne']
  rw [dedekindMertensPrimePowerSum_eq_normalized K ha ha2 hax, <- hChart,
    intervalIntegral_dedekindWeightedError_eq_tail_sub K ha hax hLimit,
    dedekindMertensConstantFromPrimitive]
  ring

private theorem tendsto_mertensAbel_boundary :
    Tendsto (fun x : Real => mertensPrimePowerWeight x * (dedekindChebyshev K x - x))
      atTop (nhds 0) := by
  have hQuot : Tendsto (fun x : Real => dedekindChebyshev K x / x - 1) atTop (nhds 0) := by
    have hOne : Tendsto (fun _ : Real => (1 : Real)) atTop (nhds 1) := tendsto_const_nhds
    simpa only [sub_self] using (dedekindChebyshev_div_tendsto_one K).sub hOne
  have hInv : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hProduct : Tendsto (fun x : Real =>
      (dedekindChebyshev K x / x - 1) * Inv.inv (Real.log x)) atTop (nhds 0) := by
    simpa only [zero_mul] using hQuot.mul hInv
  refine hProduct.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hx1 : 1 < x := (show (1 : Real) < 2 by norm_num).trans_le hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hLog := Real.log_pos hx1
  change (dedekindChebyshev K x / x - 1) * Inv.inv (Real.log x) =
    mertensPrimePowerWeight x * (dedekindChebyshev K x - x)
  unfold mertensPrimePowerWeight
  field_simp [hx0.ne', hLog.ne']

/-- The actual prime-power Mertens sum has a finite additive constant. -/
theorem tendsto_dedekindMertensPrimePowerSum_sub_loglog {c a : Real}
    (ha : 1 < a) (ha2 : a < 2)
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    Tendsto (fun x : Real => dedekindMertensPrimePowerSum K x - Real.log (Real.log x))
      atTop (nhds (dedekindMertensConstantFromPrimitive K c a)) := by
  let C := dedekindMertensConstantFromPrimitive K c a
  have hConst : Tendsto (fun _ : Real => C) atTop (nhds C) := tendsto_const_nhds
  have hTail := tendsto_dedekindMertensWeightedTail K hLimit
  have hSum : Tendsto (fun x : Real => C +
      mertensPrimePowerWeight x * (dedekindChebyshev K x - x) + dedekindMertensWeightedTail K c x)
      atTop (nhds C) := by
    simpa only [add_zero] using (hConst.add (tendsto_mertensAbel_boundary K)).add hTail
  refine hSum.congr' ?_
  filter_upwards [eventually_ge_atTop a] with x hx
  have h := dedekindMertensPrimePowerSum_eq_weightedTail K ha ha2 hx hLimit
  change C + mertensPrimePowerWeight x * (dedekindChebyshev K x - x) +
    dedekindMertensWeightedTail K c x =
      dedekindMertensPrimePowerSum K x - Real.log (Real.log x)
  change dedekindMertensPrimePowerSum K x = Real.log (Real.log x) + C +
    mertensPrimePowerWeight x * (dedekindChebyshev K x - x) + dedekindMertensWeightedTail K c x at h
  linarith only [h]

end DedekindZeta
