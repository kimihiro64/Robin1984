import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.AbelSummation
import Robin1984.GRH.DedekindNormCoefficients

/-!
# Exact Abel summation for the Dedekind Mertens sum

The prime-power sum weighted by the inverse norm and inverse log norm
has an exact finite-interval identity in terms of the Chebyshev function.
The lower endpoint lies between one and the smallest possible prime norm.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Abel summation with the weight one over the norm times its logarithm.
- Formalization note: The norm coefficients at zero and one vanish. The derivative of the real weight supplies the signed integral in the finite identity.
- PROVENANCE-END
-/

open Filter MeasureTheory NumberField Set

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

/-- The weight applied to the norm-indexed Chebyshev coefficients. -/
noncomputable def mertensPrimePowerWeight (x : Real) : Real :=
  Inv.inv (x * Real.log x)

/-- The negative derivative of the Mertens prime-power weight. -/
noncomputable def mertensAbelKernel (x : Real) : Real :=
  (1 + Real.log x) / (x ^ 2 * Real.log x ^ 2)

/-- The prime-power Mertens sum obtained by weighting each norm fiber. -/
noncomputable def dedekindMertensPrimePowerSum (x : Real) : Real :=
  (Finset.range (Nat.floor x + 1)).sum
    (fun n => mertensPrimePowerWeight (n : Real) * dedekindNormCoeff K n)

private theorem hasDerivAt_mertensPrimePowerWeight {x : Real} (hx : 1 < x) :
    HasDerivAt mertensPrimePowerWeight (-mertensAbelKernel x) x := by
  have hx0 := zero_lt_one.trans hx
  have hLog := Real.log_pos hx
  have hD : HasDerivAt (fun t : Real => t * Real.log t)
      (1 * Real.log x + x * Inv.inv x) x :=
    (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0.ne')
  have hValue : 1 * Real.log x + x * Inv.inv x = 1 + Real.log x := by
    have hxInv : x * Inv.inv x = 1 := by field_simp [hx0.ne']
    rw [one_mul, hxInv, add_comm]
  rw [hValue] at hD
  have hDerivative : -(1 + Real.log x) / (x * Real.log x) ^ 2 = -mertensAbelKernel x := by
    rw [mertensAbelKernel, mul_pow, neg_div]
  rw [<- hDerivative]
  exact hD.inv (mul_ne_zero hx0.ne' hLog.ne')

private theorem continuousOn_mertensAbelKernel {a b : Real} (ha : 1 < a) :
    ContinuousOn mertensAbelKernel (Icc a b) := by
  have hx1 (t : Real) (ht : Membership.mem (Icc a b) t) : 1 < t := ha.trans_le ht.1
  have hLog : ContinuousOn Real.log (Icc a b) := fun t ht =>
    (Real.continuousAt_log (zero_lt_one.trans (hx1 t ht)).ne').continuousWithinAt
  exact (continuousOn_const.add hLog).div
    ((continuousOn_id.pow 2).mul (hLog.pow 2))
    (fun t ht => mul_ne_zero (pow_ne_zero _ (zero_lt_one.trans (hx1 t ht)).ne')
      (pow_ne_zero _ (Real.log_pos (hx1 t ht)).ne'))

private theorem range_succ_eq_Icc_zero (n : Nat) :
    Finset.range (n + 1) = Finset.Icc 0 n := by
  ext m
  simp only [Finset.mem_range, Finset.mem_Icc, Nat.zero_le, true_and, Nat.lt_succ_iff]

private theorem natFloor_le_one_of_lt_two {a : Real} (ha : 0 <= a) (ha2 : a < 2) :
    Nat.floor a <= 1 := by
  by_contra h
  have hNat : 2 <= Nat.floor a := Nat.succ_le_of_lt (lt_of_not_ge h)
  have hReal : (2 : Real) <= (Nat.floor a : Real) := by exact_mod_cast hNat
  exact (not_le_of_gt ha2) (hReal.trans (Nat.floor_le ha))

/-- Exact finite-interval Abel summation for the Dedekind Mertens
prime-power sum, with the signed derivative written as a positive kernel. -/
theorem dedekindMertensPrimePowerSum_eq_abel {a x : Real} (ha : 1 < a) (ha2 : a < 2) (hax : a <= x) :
    dedekindMertensPrimePowerSum K x =
      mertensPrimePowerWeight x * dedekindChebyshev K x +
        integral (volume.restrict (Ioc a x)) (fun t => mertensAbelKernel t * dedekindChebyshev K t) := by
  have ha0 := (zero_lt_one.trans ha).le
  have hLow := natFloor_le_one_of_lt_two ha0 ha2
  have hCheb (t : Real) : (Finset.Icc 0 (Nat.floor t)).sum (dedekindNormCoeff K) =
      dedekindChebyshev K t := by
    rw [dedekindChebyshev_eq_sum_normCoeff, range_succ_eq_Icc_zero]
  have hPsiZero : dedekindChebyshev K a = 0 := by
    rw [<- hCheb a]
    apply Finset.sum_eq_zero
    intro n hn
    exact dedekindNormCoeff_eq_zero_of_le_one K ((Finset.mem_Icc.mp hn).2.trans hLow)
  have hDifferentiable : forall t : Real, Membership.mem (Icc a x) t ->
      DifferentiableAt Real mertensPrimePowerWeight t :=
    fun _ ht => (hasDerivAt_mertensPrimePowerWeight (ha.trans_le ht.1)).differentiableAt
  have hDerivInt : IntegrableOn (deriv mertensPrimePowerWeight) (Icc a x) :=
    ((continuousOn_mertensAbelKernel ha).neg.integrableOn_compact isCompact_Icc).congr_fun
      (fun _ ht => (hasDerivAt_mertensPrimePowerWeight (ha.trans_le ht.1)).deriv.symm)
      measurableSet_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul (f := mertensPrimePowerWeight)
    (c := dedekindNormCoeff K) ha0 hax hDifferentiable hDerivInt
  simp only [hCheb, hPsiZero, mul_zero, sub_zero] at hAbel
  have hFinset :
      (Finset.Ioc (Nat.floor a) (Nat.floor x)).sum
        (fun n => mertensPrimePowerWeight (n : Real) * dedekindNormCoeff K n) =
          dedekindMertensPrimePowerSum K x := by
    rw [dedekindMertensPrimePowerSum, range_succ_eq_Icc_zero]
    refine Finset.sum_subset
      (fun n hn => Finset.mem_Icc.mpr (And.intro (Nat.zero_le _) (Finset.mem_Ioc.mp hn).2)) ?_
    intro n hn hOutside
    have hN : n <= Nat.floor a := le_of_not_gt (fun h =>
      hOutside (Finset.mem_Ioc.mpr (And.intro h (Finset.mem_Icc.mp hn).2)))
    rw [dedekindNormCoeff_eq_zero_of_le_one K (hN.trans hLow), mul_zero]
  have hIntegral :
      integral (volume.restrict (Ioc a x)) (fun t => deriv mertensPrimePowerWeight t * dedekindChebyshev K t) =
        -(integral (volume.restrict (Ioc a x)) (fun t => mertensAbelKernel t * dedekindChebyshev K t)) := by
    rw [<- integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv mertensPrimePowerWeight t * dedekindChebyshev K t =
      -(mertensAbelKernel t * dedekindChebyshev K t)
    rw [(hasDerivAt_mertensPrimePowerWeight (ha.trans ht.1)).deriv, neg_mul]
  rw [hFinset, hIntegral, sub_neg_eq_add] at hAbel
  exact hAbel

private theorem hasDerivAt_mertensMainPrimitive {x : Real} (hx : 1 < x) :
    HasDerivAt (fun t : Real => Real.log (Real.log t) - Inv.inv (Real.log t))
      (x * mertensAbelKernel x) x := by
  have hx0 := zero_lt_one.trans hx
  have hLog := Real.log_pos hx
  have hInner := Real.hasDerivAt_log hx0.ne'
  have hOuter := (Real.hasDerivAt_log hLog.ne').comp x hInner
  have hInverse := hInner.inv hLog.ne'
  have heq : Inv.inv (Real.log x) * Inv.inv x - (-Inv.inv x / Real.log x ^ 2) =
      x * mertensAbelKernel x := by
    unfold mertensAbelKernel
    field_simp [hx0.ne', hLog.ne']
    ring
  rw [<- heq]
  exact hOuter.sub hInverse

private theorem integral_mertensMainTerm {a x : Real} (ha : 1 < a) (hax : a <= x) :
    integral (volume.restrict (Ioc a x)) (fun t => t * mertensAbelKernel t) =
      (Real.log (Real.log x) - Inv.inv (Real.log x)) -
        (Real.log (Real.log a) - Inv.inv (Real.log a)) := by
  have hContinuous :=
    (continuousOn_id (s := Icc a x)).mul (continuousOn_mertensAbelKernel ha)
  have hIntegrable : IntervalIntegrable (fun t => t * mertensAbelKernel t) volume a x :=
    hContinuous.intervalIntegrable_of_Icc hax
  rw [<- intervalIntegral.integral_of_le hax]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => by
      rw [uIcc_of_le hax] at ht
      exact hasDerivAt_mertensMainPrimitive (ha.trans_le ht.1))
    hIntegrable

/-- Exact finite normalization of the Dedekind Mertens sum. Separating
the linear main term in the Chebyshev function leaves one boundary term
and one weighted integral of the actual Chebyshev error. -/
theorem dedekindMertensPrimePowerSum_eq_normalized {a x : Real}
    (ha : 1 < a) (ha2 : a < 2) (hax : a <= x) :
    dedekindMertensPrimePowerSum K x =
      Real.log (Real.log x) + (Inv.inv (Real.log a) - Real.log (Real.log a)) +
        mertensPrimePowerWeight x * (dedekindChebyshev K x - x) +
        integral (volume.restrict (Ioc a x))
          (fun t => (dedekindChebyshev K t - t) * mertensAbelKernel t) := by
  have hPsiInt : IntegrableOn (dedekindChebyshev K) (Icc a x) :=
    MonotoneOn.integrableOn_isCompact isCompact_Icc
      ((monotone_dedekindChebyshev K).monotoneOn (Icc a x))
  have hIdInt : IntegrableOn (fun t : Real => t) (Icc a x) :=
    continuousOn_id.integrableOn_compact isCompact_Icc
  have hC := continuousOn_mertensAbelKernel (b := x) ha
  have hErrorInt : IntegrableOn
      (fun t => (dedekindChebyshev K t - t) * mertensAbelKernel t) (Ioc a x) :=
    ((hPsiInt.sub hIdInt).mul_continuousOn hC isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hMainInt : IntegrableOn (fun t => t * mertensAbelKernel t) (Ioc a x) :=
    (hIdInt.mul_continuousOn hC isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hSplit : (fun t => mertensAbelKernel t * dedekindChebyshev K t) =
      (fun t => (dedekindChebyshev K t - t) * mertensAbelKernel t + t * mertensAbelKernel t) := by
    funext t
    ring
  have hBoundary : mertensPrimePowerWeight x * x = Inv.inv (Real.log x) := by
    have hx0 : 0 < x := zero_lt_one.trans (ha.trans_le hax)
    have hLog : 0 < Real.log x := Real.log_pos (ha.trans_le hax)
    unfold mertensPrimePowerWeight
    field_simp [hx0.ne', hLog.ne']
  have hRewrite : mertensPrimePowerWeight x * dedekindChebyshev K x =
      mertensPrimePowerWeight x * (dedekindChebyshev K x - x) + Inv.inv (Real.log x) := by
    rw [<- hBoundary]
    ring
  rw [dedekindMertensPrimePowerSum_eq_abel K ha ha2 hax, hSplit, integral_add hErrorInt hMainInt,
    integral_mertensMainTerm ha hax, hRewrite]
  ring

end Robin1984.GRH
