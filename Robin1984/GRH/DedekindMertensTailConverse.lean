import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Robin1984.GRH.DedekindWeightedTail

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The inverse-weight identity and its one-sided bound for the signed Dedekind primitive.
- Formalization note: The one-sided Mertens tail implies Dedekind RH.
- PROVENANCE-END
-/

/-!
# The one-sided Mertens tail implies Dedekind RH

The positive derivative of the reciprocal weight preserves the one-sided
estimate. The boundary and integral contributions give the explicit
constant three in the unweighted tail.
-/

open Filter MeasureTheory NumberField Robin1984.GRH Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

private theorem inv_sqrt_mul_eq_rpow {t : Real} (ht : 0 < t) :
    Inv.inv (Real.sqrt t * t) = t ^ (-(3 / 2 : Real)) := by
  rw [show (-(3 / 2 : Real)) = -(1 / 2 + 1) by norm_num,
    Real.rpow_neg ht.le, Real.rpow_add ht, <- Real.sqrt_eq_rpow, Real.rpow_one]

/-- An eventual upper estimate for the signed Mertens tail gives the
signed unweighted Chebyshev estimate with the same root scale. -/
theorem eventual_primitiveTail_le_of_weightedMertensTail {c C : Real}
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c))
    (hC : 0 <= C)
    (hBound : Filter.Eventually (fun x : Real => dedekindMertensWeightedTail K c x <=
      C / (Real.sqrt x * Real.log x)) atTop) :
    Filter.Eventually (fun x : Real => (-x) * primitiveTail (dedekindChebyshevErrorRatio K) c x <=
      (3 * C) * Real.sqrt x) atTop := by
  let T := primitiveTail (dedekindChebyshevErrorRatio K) c
  let H := dedekindMertensWeightedTail K c
  let R := Classical.choose (eventually_atTop.mp hBound)
  have hR := Classical.choose_spec (eventually_atTop.mp hBound)
  have hExp : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr (zero_lt_one : (0 : Real) < 1))
  filter_upwards [eventually_ge_atTop (max (Real.exp 1) R)] with x hx
  have hxE : Real.exp 1 <= x := (le_max_left _ _).trans hx
  have hxR : R <= x := (le_max_right _ _).trans hx
  have hx1 : 1 < x := hExp.trans_le hxE
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hxS := Real.sqrt_pos.mpr hx0
  have hxL := Real.log_pos hx1
  have hInv : 0 <= mertensDeweight x :=
    div_nonneg (sq_nonneg _) (add_nonneg zero_le_one hxL.le)
  have hBoundary : H x * mertensDeweight x <= C / Real.sqrt x := by
    calc
      _ <= (C / (Real.sqrt x * Real.log x)) * mertensDeweight x :=
        mul_le_mul_of_nonneg_right (hR x hxR) hInv
      _ <= (C / (Real.sqrt x * Real.log x)) * Real.log x :=
        mul_le_mul_of_nonneg_left (mertensDeweight_le_log hx1)
          (div_nonneg hC (mul_nonneg hxS.le hxL.le))
      _ = _ := by field_simp [hxS.ne', hxL.ne']
  let J := fun t : Real => C * t ^ (-(3 / 2 : Real))
  have hDom (t : Real) (ht : x <= t) : H t * mertensDeweightSlope t <= J t := by
    have ht1 := hx1.trans_le ht
    have ht0 := hx0.trans_le ht
    have hLog : 1 <= Real.log t := by
      have he := Real.log_le_log (Real.exp_pos 1) (hxE.trans ht)
      simpa only [Real.log_exp] using he
    have hSlope := mertensDeweightSlope_bounds ht1
    have hSmall : C / (Real.sqrt t * Real.log t) <= C / Real.sqrt t := by
      rw [<- div_div]
      exact div_le_self (div_nonneg hC (Real.sqrt_nonneg _)) hLog
    calc
      _ <= (C / (Real.sqrt t * Real.log t)) * mertensDeweightSlope t :=
        mul_le_mul_of_nonneg_right (hR t (hxR.trans ht)) hSlope.1
      _ <= (C / Real.sqrt t) * mertensDeweightSlope t :=
        mul_le_mul_of_nonneg_right hSmall hSlope.1
      _ <= (C / Real.sqrt t) * Inv.inv t :=
        mul_le_mul_of_nonneg_left hSlope.2 (div_nonneg hC (Real.sqrt_nonneg _))
      _ = J t := by
        change (C / Real.sqrt t) * Inv.inv t = C * t ^ (-(3 / 2 : Real))
        rw [<- inv_sqrt_mul_eq_rpow ht0]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hJ : IntegrableOn J (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : Real)) (by norm_num) hx0).const_mul C
  have hMass : integral (volume.restrict (Ioi x)) J = (2 * C) / Real.sqrt x := by
    change integral (volume.restrict (Ioi x)) (fun t => C * t ^ (-(3 / 2 : Real))) = _
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (a := -(3 / 2 : Real)) (by norm_num) hx0,
      show (-(3 / 2 : Real) + 1) = -(1 / 2) by norm_num,
      Real.rpow_neg hx0.le, <- Real.sqrt_eq_rpow]
    ring
  have hIntegral (y : Real) (hxy : x <= y) :
      intervalIntegral (fun t => H t * mertensDeweightSlope t) x y volume <=
        (2 * C) / Real.sqrt x := by
    have hHS : ContinuousOn (fun t => H t * mertensDeweightSlope t) (Icc x y) :=
      (continuousOn_dedekindMertensWeightedTail_Icc K hx1 hxy hLimit).mul
        (continuousOn_mertensDeweightSlope.mono (fun _ ht => hx1.trans_le ht.1))
    have hHInt : IntervalIntegrable (fun t => H t * mertensDeweightSlope t) volume x y :=
      hHS.intervalIntegrable_of_Icc hxy
    have hJInt : IntervalIntegrable J volume x y :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mpr (hJ.mono_set Ioc_subset_Ioi_self)
    have hMono := intervalIntegral.integral_mono_on hxy hHInt hJInt (fun t ht => hDom t ht.1)
    refine hMono.trans ?_
    rw [intervalIntegral.integral_of_le hxy, <- hMass]
    have hJPos : Filter.Eventually (fun t => 0 <= J t) (ae (volume.restrict (Ioi x))) := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall (fun t ht =>
        mul_nonneg hC (Real.rpow_nonneg (hx0.trans ht).le _))
    exact setIntegral_mono_set hJ hJPos Ioc_subset_Ioi_self.eventuallyLE
  have hFinite : Filter.Eventually
      (fun y : Real => T y - T x + H y * mertensDeweight y <= (3 * C) / Real.sqrt x) atTop := by
    filter_upwards [eventually_ge_atTop x] with y hy
    have h := intervalIntegral_deweight_dedekindMertensTail K hx1 hy hLimit
    have hI := hIntegral y hy
    change T y - T x = H x * mertensDeweight x - H y * mertensDeweight y +
      intervalIntegral (fun t => H t * mertensDeweightSlope t) x y volume at h
    change T y - T x + H y * mertensDeweight y <= (3 * C) / Real.sqrt x
    rw [h]
    calc
      _ <= C / Real.sqrt x + (2 * C) / Real.sqrt x := by linarith only [hBoundary, hI]
      _ = _ := by rw [<- add_div]; congr 1; ring
  have hT : Tendsto T atTop (nhds 0) := by
    rw [<- sub_self c]
    exact tendsto_const_nhds.sub hLimit
  have hConst : Tendsto (fun _ : Real => T x) atTop (nhds (T x)) := tendsto_const_nhds
  have hTail := tendsto_dedekindMertensWeightedTail_mul_deweight K hLimit
  have hFinal : Tendsto (fun y : Real => T y - T x + H y * mertensDeweight y)
      atTop (nhds (-T x)) := by
    simpa only [zero_sub, add_zero] using (hT.sub hConst).add hTail
  have hNeg := le_of_tendsto hFinal hFinite
  change (-x) * T x <= (3 * C) * Real.sqrt x
  calc
    _ = x * (-T x) := by ring
    _ <= x * ((3 * C) / Real.sqrt x) := mul_le_mul_of_nonneg_left hNeg hx0.le
    _ = _ := by
      calc
        _ = (Real.sqrt x * Real.sqrt x) * ((3 * C) / Real.sqrt x) := by
          rw [Real.mul_self_sqrt hx0.le]
        _ = _ := by field_simp [hxS.ne'] <;> ring

/-- Dedekind RH follows from the eventual upper estimate for the actual
weighted Mertens tail. -/
theorem dedekindRH_of_eventual_weightedMertensTailBound {c C : Real}
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c))
    (hC : 0 <= C)
    (hBound : Filter.Eventually (fun x : Real => dedekindMertensWeightedTail K c x <=
      C / (Real.sqrt x * Real.log x)) atTop) :
    DedekindRH K := by
  have hActual := exists_dedekindChebyshevPrimitiveLimit K
  let c0 := Classical.choose hActual
  have hc := Classical.choose_spec hActual
  have heq : c = c0 := tendsto_nhds_unique hLimit hc.1
  have hCValue : (c : Complex) = -(logDeriv (entirePoleFreeDedekindZeta K) 1 + 1) := by
    rw [heq]
    exact hc.2
  have hAtOne : logDeriv (entirePoleFreeDedekindZeta K) 1 + 1 + (c : Complex) = 0 := by
    rw [hCValue, add_neg_cancel]
  have hEventually := eventual_primitiveTail_le_of_weightedMertensTail K hLimit hC hBound
  let a := Classical.choose (eventually_atTop.mp hEventually)
  have ha := Classical.choose_spec (eventually_atTop.mp hEventually)
  exact dedekindRH_of_primitiveChebyshevTailBound K hLimit hAtOne
    (Exists.intro (3 * C) (Exists.intro a (fun x hx => ha x hx.le)))

end DedekindZeta
