import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Robin1984.GRH.TriangularMellin

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Termwise integration of the absolutely convergent Dirichlet series for the triangular Mellin transform.
- Formalization note: The integral norm of each truncated term is bounded by its absolute Dirichlet coefficient divided by the real part of the transform parameter.
- PROVENANCE-END
-/

/-!
# Termwise triangular Mellin integration

Absolute convergence of the Dirichlet series justifies exchange of its
countable sum and the triangular Mellin integral.
-/

open MeasureTheory Set

namespace Robin1984.GRH

/-- Summable integral norms justify a complex-valued countable sum as an
integrable function. -/
theorem integrable_tsum_complex_of_norm_integrals {iota : Type*} [Countable iota]
    {mu : Measure Real} {F : iota -> Real -> Complex}
    (hF : forall i, Integrable (F i) mu)
    (hIntSum : Summable (fun i => integral mu (fun x => norm (F i x)))) :
    Integrable (fun x => tsum (fun i => F i x)) mu := by
  have hNormSum : tsum (fun i => lintegral mu (fun x => enorm (F i x))) < Top.top := by
    let I (i : iota) : NNReal := (integral mu (fun x => norm (F i x))).toNNReal
    have hI (i : iota) : (I i : ENNReal) = lintegral mu (fun x => enorm (F i x)) :=
      ofReal_integral_norm_eq_lintegral_enorm (hF i)
    have hISum : Summable (fun i => (I i : Real)) := by
      convert hIntSum using 1
      funext i
      exact Real.coe_toNNReal _ (integral_nonneg (fun x => norm_nonneg (F i x)))
    simp_rw [<- hI]
    exact lt_top_iff_ne_top.mpr (ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hISum)
  have hIntegralBound :
      lintegral mu (fun x => enorm (tsum (fun i => F i x))) < Top.top := by
    refine lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)) ?_
    rw [lintegral_tsum (fun i => (hF i).aemeasurable.enorm)]
    exact hNormSum
  exact And.intro ((AEMeasurable.tsum fun i => (hF i).aemeasurable).aestronglyMeasurable)
    (hasFiniteIntegral_iff_enorm.mpr hIntegralBound)

private theorem norm_triangularWeight_le_one {a x : Real} (ha : 0 < a) (hx : a < x) :
    norm ((1 : Complex) - (a : Complex) / (x : Complex)) <= 1 := by
  have hx0 := ha.trans hx
  have hRe : 0 <= 1 - a / x := sub_nonneg.mpr ((div_le_one (by exact hx0)).mpr hx.le)
  rw [<- Complex.ofReal_div, <- Complex.ofReal_one, <- Complex.ofReal_sub,
    Complex.norm_real, Real.norm_of_nonneg hRe]
  exact sub_le_self _ (div_nonneg ha.le hx0.le)

/-- The countable triangular transform is the absolutely convergent
Dirichlet series multiplied by its common Mellin kernel. -/
theorem integrable_integral_tsum_triangularMellin {iota : Type*} [Countable iota]
    (a : iota -> Real) (b : iota -> Complex) (s : Complex) (hs : 0 < s.re)
    (hPos : forall i, 0 < a i)
    (hSummable : Summable (fun i => norm (b i) * (a i) ^ (-s.re))) :
    let T := fun x : Real => tsum (fun i =>
      (Ioi (a i)).indicator (fun x : Real =>
        b i * ((1 - (a i : Complex) / (x : Complex)) * (x : Complex) ^ (-s - 1))) x)
    And (Integrable T volume)
      (integral volume T = tsum (fun i => b i * (a i : Complex) ^ (-s)) / (s * (s + 1))) := by
  classical
  let F (i : iota) := (Ioi (a i)).indicator (fun x : Real =>
    b i * ((1 - (a i : Complex) / (x : Complex)) * (x : Complex) ^ (-s - 1)))
  let W (i : iota) := (Ioi (a i)).indicator (fun x : Real => norm (b i) * x ^ (-s.re - 1))
  have hRe : (-s.re - 1 : Real) < -1 := by linarith only [hs]
  have hComplexRe : (-s - 1).re < -1 := by
    simpa only [Complex.sub_re, Complex.neg_re, Complex.one_re] using hRe
  have hBoundLocal (i : iota) {x : Real} (hx : a i < x) :
      norm (b i * ((1 - (a i : Complex) / (x : Complex)) * (x : Complex) ^ (-s - 1))) <=
        norm (b i) * x ^ (-s.re - 1) := by
    have hPower : norm ((x : Complex) ^ (-s - 1)) = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ((hPos i).trans hx)]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    rw [norm_mul, norm_mul, <- hPower]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) (norm_triangularWeight_le_one (hPos i) hx))
      (norm_nonneg _)
  have hW (i : iota) : Integrable (W i) volume := by
    have hLocal : IntegrableOn (fun x : Real => norm (b i) * x ^ (-s.re - 1)) (Ioi (a i)) :=
      (integrableOn_Ioi_rpow_of_lt hRe (hPos i)).const_mul (norm (b i))
    exact hLocal.integrable_indicator measurableSet_Ioi
  have hF (i : iota) : Integrable (F i) volume := by
    have hPow := integrableOn_Ioi_cpow_of_lt hComplexRe (hPos i)
    have hWeight : Measurable (fun x : Real => (1 : Complex) - (a i : Complex) / (x : Complex)) :=
      measurable_const.sub (measurable_const.div Complex.continuous_ofReal.measurable)
    have hMeas : AEStronglyMeasurable
        (fun x : Real => b i * ((1 - (a i : Complex) / (x : Complex)) *
          (x : Complex) ^ (-s - 1))) (volume.restrict (Ioi (a i))) :=
      aestronglyMeasurable_const.mul
      (hWeight.aestronglyMeasurable.mul hPow.aestronglyMeasurable)
    have hLocal : IntegrableOn (fun x : Real =>
        b i * ((1 - (a i : Complex) / (x : Complex)) * (x : Complex) ^ (-s - 1))) (Ioi (a i)) :=
      ((integrableOn_Ioi_rpow_of_lt hRe (hPos i)).const_mul (norm (b i))).mono'
        hMeas (ae_restrict_of_forall_mem measurableSet_Ioi (fun _ hx => hBoundLocal i hx))
    exact hLocal.integrable_indicator measurableSet_Ioi
  have hBound (i : iota) (x : Real) : norm (F i x) <= W i x := by
    by_cases hx : Membership.mem (Ioi (a i)) x
    case pos =>
      simpa only [F, W, indicator_of_mem hx] using hBoundLocal i hx
    case neg =>
      simp only [F, W, indicator_of_notMem hx, norm_zero, le_refl]
  have hWIntegral (i : iota) :
      integral volume (W i) = (norm (b i) * (a i) ^ (-s.re)) / s.re := by
    change integral volume ((Ioi (a i)).indicator (fun x : Real =>
      norm (b i) * x ^ (-s.re - 1))) = _
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt hRe (hPos i)]
    have hExp : -s.re - 1 + 1 = -s.re := sub_add_cancel (-s.re) 1
    rw [hExp, neg_div_neg_eq, mul_div_assoc]
  have hIntSum : Summable (fun i => integral volume (fun x => norm (F i x))) := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg (F i x)))
      (fun i => ?_) (hSummable.div_const s.re)
    rw [<- hWIntegral i]
    exact integral_mono ((hF i).norm) (hW i) (hBound i)
  change And (Integrable (fun x => tsum (fun i => F i x)) volume)
    (integral volume (fun x => tsum (fun i => F i x)) = _)
  refine And.intro (integrable_tsum_complex_of_norm_integrals hF hIntSum) ?_
  rw [<- integral_tsum_of_summable_integral_norm hF hIntSum, <- tsum_div_const]
  apply tsum_congr
  intro i
  change integral volume ((Ioi (a i)).indicator (fun x : Real =>
    b i * ((1 - (a i : Complex) / (x : Complex)) * (x : Complex) ^ (-s - 1)))) = _
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    triangularMellin (a i) s (hPos i) hs, mul_div_assoc]

end Robin1984.GRH
