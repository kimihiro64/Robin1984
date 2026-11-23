import Mathlib.MeasureTheory.Function.JacobianOneDim
import Robin1984.GRH.DedekindMertensAbelTransform
import Robin1984.GRH.DedekindResidueLogLimit
import Robin1984.GRH.DedekindWeightedTail
import Robin1984.GRH.EulerMascheroniLaplaceMass
import Robin1984.GRH.MertensAbelianAverage

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Dedekind Mertens constant computed by Abelian averaging and the class number formula.
- Formalization note: The Dedekind Mertens constant.
- PROVENANCE-END
-/

/-!
# The Dedekind Mertens constant

The Abelian integral of the actual Euler coefficients and the class
number formula identify the signed Mertens constant exactly.
-/

open Filter MeasureTheory NumberField Robin1984.GRH Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

private theorem exp_image_positive : Real.exp '' Ioi (0 : Real) = Ioi (1 : Real) := by
  ext x
  constructor
  case mp =>
    intro h
    let t := Classical.choose h
    have ht := Classical.choose_spec h
    change 1 < x
    rw [<- ht.2, <- Real.exp_zero]
    exact Real.exp_lt_exp.mpr ht.1
  case mpr =>
    intro hx
    exact Exists.intro (Real.log x) (And.intro (Real.log_pos hx)
      (Real.exp_log (zero_lt_one.trans hx)))

private theorem log_dedekindZeta_eq_integral_mertens_exp {u : Real} (hu : 0 < u) :
    Real.log (dedekindZeta K ((1 + u : Real) : Complex)).re =
      u * integral (volume.restrict (Ioi (0 : Real)))
        (fun t => dedekindMertensPrimePowerSum K (Real.exp t) * Real.exp (-(u * t))) := by
  have hJ := integral_image_eq_integral_abs_deriv_smul
    (measurableSet_Ioi : MeasurableSet (Ioi (0 : Real)))
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn
    (fun x => dedekindMertensPrimePowerSum K x * x ^ (-(u + 1)))
  rw [exp_image_positive] at hJ
  rw [log_dedekindZeta_eq_integral_mertens K hu, hJ]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change abs (Real.exp t) * (dedekindMertensPrimePowerSum K (Real.exp t) *
      (Real.exp t) ^ (-(u + 1))) =
    dedekindMertensPrimePowerSum K (Real.exp t) * Real.exp (-(u * t))
  rw [abs_of_pos (Real.exp_pos t)]
  have hPow : Real.exp t * (Real.exp t) ^ (-(u + 1)) = Real.exp (-(u * t)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, <- Real.exp_add]
    congr 1
    ring
  rw [mul_left_comm, hPow]

private theorem monotone_dedekindMertensPrimePowerSum : Monotone (dedekindMertensPrimePowerSum K) := by
  intro x y hxy
  change (Finset.range (Nat.floor x + 1)).sum (dedekindMertensAbelCoeff K) <=
    (Finset.range (Nat.floor y + 1)).sum (dedekindMertensAbelCoeff K)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right (Nat.floor_le_floor hxy) 1))
    (fun n _ _ => dedekindMertensAbelCoeff_nonneg K n)

private theorem integrableOn_log_Ioc_zero (a : Real) : IntegrableOn Real.log (Ioc 0 a) := by
  have hWeight : Integrable (fun t => Real.log t * Real.exp (-t))
      (volume.restrict (Ioc (0 : Real) a)) :=
    integrableOn_log_mul_exp_neg.mono_set (fun _ ht => ht.1)
  have hMul := hWeight.norm.const_mul (Real.exp a)
  refine hMul.mono' Real.measurable_log.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  apply Filter.Eventually.of_forall
  intro t ht
  change norm (Real.log t) <= Real.exp a * norm (Real.log t * Real.exp (-t))
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos (-t)).le, mul_left_comm]
  have hE : 1 <= Real.exp a * Real.exp (-t) := by
    rw [<- Real.exp_add, <- Real.exp_zero]
    exact Real.exp_le_exp.mpr (by have h := ht.2; linarith)
  exact le_mul_of_one_le_right (norm_nonneg _) hE

/-- The constant read off the signed improper primitive is the standard
Euler--Mascheroni constant plus the logarithm of the Dedekind residue. -/
theorem dedekindMertensConstantFromPrimitive_eq_residue {c a : Real}
    (ha : 1 < a) (ha2 : a < 2)
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    dedekindMertensConstantFromPrimitive K c a =
      Real.eulerMascheroniConstant + Real.log (dedekindZeta_residue K) := by
  let A := dedekindMertensPrimePowerSum K
  let G := fun t : Real => A (Real.exp t) - Real.log t
  let C := dedekindMertensConstantFromPrimitive K c a
  let kap := Real.log (dedekindZeta_residue K)
  let gamma := Real.eulerMascheroniConstant
  let Z := fun u : Real => Real.log (dedekindZeta K ((1 + u : Real) : Complex)).re
  let right := nhdsWithin 0 (Ioi (0 : Real))
  have hMono : Monotone (fun t : Real => A (Real.exp t)) :=
    fun _ _ h => (monotone_dedekindMertensPrimePowerSum K) (Real.exp_le_exp.mpr h)
  have hGMeas : Measurable G := hMono.measurable.sub Real.measurable_log
  have hLocal (b : Real) (_ : 0 < b) : IntegrableOn G (Ioc 0 b) := by
    have hA : IntegrableOn (fun t : Real => A (Real.exp t)) (Icc 0 b) :=
      MonotoneOn.integrableOn_isCompact isCompact_Icc (hMono.monotoneOn (Icc 0 b))
    exact (hA.mono_set Ioc_subset_Icc_self).sub (integrableOn_log_Ioc_zero b)
  have hG : Tendsto G atTop (nhds C) := by
    simpa only [G, A, Function.comp_def, Real.log_exp] using
      (tendsto_dedekindMertensPrimePowerSum_sub_loglog K ha ha2 hLimit).comp Real.tendsto_exp_atTop
  have hAvg := tendsto_mul_integral_exp_neg_of_tendsto hGMeas hLocal hG
  have hPole : Tendsto (fun u : Real => Z u + Real.log u) right (nhds kap) :=
    tendsto_log_dedekindZeta_add_log_scale K
  have hBound : Filter.Eventually (fun u : Real => kap - 1 < Z u + Real.log u) right :=
    hPole.eventually (Ioi_mem_nhds (sub_lt_self _ zero_lt_one))
  let delta := min (Real.exp (kap - 1)) (Real.exp (-(gamma + 1)))
  have hD : 0 < delta := lt_min (Real.exp_pos _) (Real.exp_pos _)
  have hEq : Filter.EventuallyEq right
      (fun u : Real => Z u + Real.log u + gamma)
      (fun u : Real => u * integral (volume.restrict (Ioi (0 : Real)))
        (fun t => G t * Real.exp (-(u * t)))) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hD), hBound]
      with u hu hDelta hBoundU
    have hu0 : 0 < u := hu
    have hU : u < delta := hDelta
    have hLog1 : Real.log u < kap - 1 := by
      simpa only [Real.log_exp] using Real.log_lt_log hu0 (hU.trans_le (min_le_left _ _))
    have hLog2 : Real.log u < -(gamma + 1) := by
      simpa only [Real.log_exp] using Real.log_lt_log hu0 (hU.trans_le (min_le_right _ _))
    have hZPos : 0 < Z u := by linarith only [hBoundU, hLog1]
    have hGammaPos : 0 < -gamma - Real.log u := by linarith only [hLog2]
    let X := fun t : Real => A (Real.exp t) * Real.exp (-(u * t))
    let Y := fun t : Real => Real.log t * Real.exp (-(u * t))
    let mu := volume.restrict (Ioi (0 : Real))
    have hAB : Z u = u * integral mu X := log_dedekindZeta_eq_integral_mertens_exp K hu0
    have hGamma : u * integral mu Y = -gamma - Real.log u :=
      mul_integral_log_mul_exp_neg_scale hu0
    have hXI : Integrable X mu := by
      by_contra h
      rw [integral_undef h, mul_zero] at hAB
      exact (ne_of_gt hZPos) hAB
    have hYI : Integrable Y mu := by
      by_contra h
      rw [integral_undef h, mul_zero] at hGamma
      exact (ne_of_gt hGammaPos) hGamma.symm
    have hRep : (fun t => G t * Real.exp (-(u * t))) = fun t => X t - Y t := by
      funext t
      exact sub_mul _ _ _
    change Z u + Real.log u + gamma =
      u * integral mu (fun t => G t * Real.exp (-(u * t)))
    rw [hRep, integral_sub hXI hYI, mul_sub, <- hAB, hGamma]
    ring
  have hConst : Tendsto (fun _ : Real => gamma) right (nhds gamma) := tendsto_const_nhds
  have hActual := ((hPole.add hConst).congr' hEq)
  exact (tendsto_nhds_unique hAvg hActual).trans (add_comm _ _)

/-- Exact normalized Dedekind Mertens identity for the actual field. -/
theorem dedekindMertensPrimePowerSum_eq_residue_weightedTail {c a x : Real}
    (ha : 1 < a) (ha2 : a < 2) (hax : a <= x)
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c)) :
    dedekindMertensPrimePowerSum K x =
      Real.log (Real.log x) + (Real.eulerMascheroniConstant + Real.log (dedekindZeta_residue K)) +
        mertensPrimePowerWeight x * (dedekindChebyshev K x - x) +
        dedekindMertensWeightedTail K c x := by
  rw [dedekindMertensPrimePowerSum_eq_weightedTail K ha ha2 hax hLimit,
    dedekindMertensConstantFromPrimitive_eq_residue K ha ha2 hLimit]

end DedekindZeta
