import Mathlib.MeasureTheory.Function.Floor
import Robin1984.GRH.DedekindLogDerivative
import Robin1984.GRH.PrimeIdealChebyshev
import Robin1984.GRH.TriangularSeries

/-!
# The Mellin transform of the prime-ideal Chebyshev function

Integrating the Chebyshev step functions over the half-line gives the
actual negative logarithmic derivative of Dedekind zeta divided by
the Mellin parameter.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Partial summation for the prime-power Dirichlet series of a Dedekind zeta function.
- Formalization note: The step integrals converge absolutely and the interchange is justified by the summable integral norms.
- PROVENANCE-END
-/

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped Real

namespace Robin1984.GRH

private theorem integrable_integral_tsum_stepMellin {I : Type*} [Countable I]
    (a : I -> Real) (b : I -> Complex) (s : Complex) (hs : 0 < s.re)
    (ha : forall i, 0 < a i)
    (hSummable : Summable (fun i => norm (b i) * (a i) ^ (-s.re))) :
    let T := fun x : Real => tsum (fun i =>
      (Ici (a i)).indicator (fun x : Real => b i * (x : Complex) ^ (-s - 1)) x)
    And (Integrable T volume)
      (integral volume T = tsum (fun i => b i * (a i : Complex) ^ (-s)) / s) := by
  classical
  let F (i : I) := (Ici (a i)).indicator (fun x : Real => b i * (x : Complex) ^ (-s - 1))
  let W (i : I) := (Ici (a i)).indicator (fun x : Real => norm (b i) * x ^ (-s.re - 1))
  have hRe : (-s.re - 1 : Real) < -1 := by linarith only [hs]
  have hComplexRe : (-s - 1).re < -1 := by
    simpa only [Complex.sub_re, Complex.neg_re, Complex.one_re] using hRe
  have hF (i : I) : Integrable (F i) volume := by
    have hMeasure : volume.restrict (Ici (a i)) = volume.restrict (Ioi (a i)) :=
      Measure.restrict_congr_set Ioi_ae_eq_Ici.symm
    have hLocal : IntegrableOn (fun x : Real => b i * (x : Complex) ^ (-s - 1)) (Ici (a i)) := by
      unfold IntegrableOn
      rw [hMeasure]
      exact (integrableOn_Ioi_cpow_of_lt hComplexRe (ha i)).const_mul (b i)
    exact hLocal.integrable_indicator measurableSet_Ici
  have hNormFun (i : I) : (fun x => norm (F i x)) = W i := by
    funext x
    by_cases hx : Membership.mem (Ici (a i)) x
    case pos =>
      simp only [F, W, indicator_of_mem hx, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ((ha i).trans_le hx),
        Complex.sub_re, Complex.neg_re, Complex.one_re]
    case neg =>
      simp only [F, W, indicator_of_notMem hx, norm_zero]
  have hNormIntegral (i : I) :
      integral volume (fun x => norm (F i x)) = (norm (b i) * (a i) ^ (-s.re)) / s.re := by
    rw [hNormFun i]
    change integral volume ((Ici (a i)).indicator (fun x : Real =>
      norm (b i) * x ^ (-s.re - 1))) = _
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt hRe (ha i), sub_add_cancel, neg_div_neg_eq, mul_div_assoc]
  have hIntSum : Summable (fun i => integral volume (fun x => norm (F i x))) :=
    (hSummable.div_const s.re).congr (fun i => (hNormIntegral i).symm)
  change And (Integrable (fun x => tsum (fun i => F i x)) volume)
    (integral volume (fun x => tsum (fun i => F i x)) = _)
  refine And.intro (integrable_tsum_complex_of_norm_integrals hF hIntSum) ?_
  rw [<- integral_tsum_of_summable_integral_norm hF hIntSum, <- tsum_div_const]
  apply tsum_congr
  intro i
  change integral volume ((Ici (a i)).indicator (fun x : Real =>
    b i * (x : Complex) ^ (-s - 1))) = _
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_Ioi_cpow_of_lt hComplexRe (ha i), sub_add_cancel, neg_div_neg_eq, mul_div_assoc]

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "PP" => Prod P Nat

private theorem countable_primePowerIndex : Countable PP := by
  refine Set.countable_univ_iff.mp ?_
  have hUnion : (Set.univ : Set PP) =
      iUnion (fun n : Nat => {pn : PP | dedekindPrimePowerNorm K pn <= n}) := by
    ext pn
    constructor
    case mp =>
      intro _
      refine mem_iUnion.mpr (Exists.intro (dedekindPrimePowerNorm K pn) ?_)
      change dedekindPrimePowerNorm K pn <= dedekindPrimePowerNorm K pn
      exact le_rfl
    case mpr =>
      intro _
      exact mem_univ pn
  rw [hUnion]
  exact Set.countable_iUnion (fun n => (finite_primePowerNorm_le K n).countable)

/-- The Mellin identity holds for the exact finite Chebyshev function and
Mathlib's Dedekind zeta series on `1 < s.re`. -/
theorem dedekindChebyshev_mellin {s : Complex} (hs : 1 < s.re) :
    let D := fun x : Real => (dedekindChebyshev K x : Complex) * (x : Complex) ^ (-s - 1)
    And (Integrable D (volume.restrict (Ioi (1 : Real))))
      (integral (volume.restrict (Ioi (1 : Real))) D =
        (-deriv (dedekindZeta K) s / dedekindZeta K s) / s) := by
  classical
  let _ : Countable PP := countable_primePowerIndex K
  let a (pn : PP) : Real := dedekindPrimePowerNorm K pn
  let b (pn : PP) : Complex := (Real.log (dedekindPrimeNorm K pn.1 : Real) : Complex)
  let F (pn : PP) := (Ici (a pn)).indicator (fun x : Real => b pn * (x : Complex) ^ (-s - 1))
  let T : Real -> Complex := fun x => tsum (fun pn => F pn x)
  let D : Real -> Complex := fun x => (dedekindChebyshev K x : Complex) * (x : Complex) ^ (-s - 1)
  have ha (pn : PP) : 1 < a pn := by
    have hq := one_lt_dedekindPrimeNorm K pn.1
    have hPow : dedekindPrimeNorm K pn.1 <= dedekindPrimePowerNorm K pn := by
      simpa only [dedekindPrimePowerNorm, pow_one] using
        Nat.pow_le_pow_right hq.le (Nat.succ_pos pn.2)
    change (1 : Real) < (dedekindPrimePowerNorm K pn : Real)
    exact_mod_cast hq.trans_le hPow
  have hDir (pn : PP) :
      b pn * (a pn : Complex) ^ (-s) = dedekindPrimePowerTerm K pn.1 pn.2 s := by
    dsimp [a, b]
    rw [Complex.ofReal_log (Nat.cast_nonneg _)]
    simp only [Complex.ofReal_natCast, dedekindPrimePowerTerm, dedekindPrimePowerNorm]
  have hSumNorm : Summable (fun pn : PP => norm (b pn) * (a pn) ^ (-s.re)) := by
    apply (summable_norm_dedekindPrimePowerTerm K hs).congr
    intro pn
    rw [<- hDir pn, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans (ha pn)),
      Complex.neg_re]
  have hT : And (Integrable T volume)
      (integral volume T = tsum (fun pn => b pn * (a pn : Complex) ^ (-s)) / s) :=
    integrable_integral_tsum_stepMellin a b s (zero_lt_one.trans hs)
      (fun pn => zero_lt_one.trans (ha pn)) hSumNorm
  have hTAt (x : Real) (hx : 1 < x) : T x = D x := by
    let S := primePowersUpTo K (Nat.floor x)
    have hx0 := (zero_lt_one.trans hx).le
    calc
      T x = S.sum (fun pn => F pn x) := by
        apply tsum_eq_sum
        intro pn hn
        have hNot : Not (Membership.mem (Ici (a pn)) x) := by
          intro h
          exact hn ((mem_primePowersUpTo K).mpr ((Nat.le_floor_iff hx0).mpr h))
        exact indicator_of_notMem hNot _
      _ = S.sum (fun pn => b pn * (x : Complex) ^ (-s - 1)) := by
        apply Finset.sum_congr rfl
        intro pn hp
        exact indicator_of_mem ((Nat.le_floor_iff hx0).mp ((mem_primePowersUpTo K).mp hp)) _
      _ = D x := by
        simp only [D, dedekindChebyshev, S, b, Complex.ofReal_sum, Finset.sum_mul]
  have hTIndicator : T = (Ioi (1 : Real)).indicator D := by
    funext x
    by_cases hx : Membership.mem (Ioi (1 : Real)) x
    case pos =>
      rw [indicator_of_mem hx]
      exact hTAt x hx
    case neg =>
      rw [indicator_of_notMem hx]
      change (tsum (fun pn => F pn x)) = 0
      rw [show (fun pn : PP => F pn x) = (fun _ : PP => (0 : Complex)) from funext (fun pn =>
        indicator_of_notMem (fun h => hx ((ha pn).trans_le h)) _), tsum_zero]
  have hZ : tsum (fun pn => b pn * (a pn : Complex) ^ (-s)) =
      -deriv (dedekindZeta K) s / dedekindZeta K s :=
    (tsum_congr hDir).trans (hasSum_dedekindPrimePowerTerm K hs).tsum_eq
  change And (Integrable D (volume.restrict (Ioi (1 : Real)))) _
  refine And.intro (hT.1.integrableOn.congr ?hOn) ?hIntegral
  case hOn =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hTAt x hx
  case hIntegral =>
    rw [<- integral_indicator measurableSet_Ioi, <- hTIndicator, hT.2, hZ]

/-- Subtracting the pole's linear main term gives the Mellin transform of
the Chebyshev error on the initial half-plane. -/
theorem dedekindChebyshevError_mellin {s : Complex} (hs : 1 < s.re) :
    let D := fun x : Real => ((dedekindChebyshev K x - x : Real) : Complex) *
      (x : Complex) ^ (-s - 1)
    And (Integrable D (volume.restrict (Ioi (1 : Real))))
      (integral (volume.restrict (Ioi (1 : Real))) D =
        (-deriv (dedekindZeta K) s / dedekindZeta K s) / s - 1 / (s - 1)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let F : Real -> Complex := fun x => (dedekindChebyshev K x : Complex) * (x : Complex) ^ (-s - 1)
  let L : Real -> Complex := fun x => (x : Complex) ^ (-s)
  let D : Real -> Complex := fun x => ((dedekindChebyshev K x - x : Real) : Complex) *
    (x : Complex) ^ (-s - 1)
  have hF : And (Integrable F mu) (integral mu F =
      (-deriv (dedekindZeta K) s / dedekindZeta K s) / s) :=
    dedekindChebyshev_mellin K hs
  have hRe : (-s).re < -1 := by
    rw [Complex.neg_re]
    exact neg_lt_neg hs
  have hL : Integrable L mu := integrableOn_Ioi_cpow_of_lt hRe zero_lt_one
  have hLValue : integral mu L = 1 / (s - 1) := by
    change integral (volume.restrict (Ioi (1 : Real))) (fun x : Real => (x : Complex) ^ (-s)) = _
    rw [integral_Ioi_cpow_of_lt hRe zero_lt_one, Complex.ofReal_one, Complex.one_cpow,
      show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  have hEq : Filter.EventuallyEq (ae mu) (fun x => F x - L x) D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (zero_lt_one.trans (show 1 < x from hx)).ne'
    have hLinear : (x : Complex) * (x : Complex) ^ (-s - 1) = (x : Complex) ^ (-s) := by
      calc
        _ = (x : Complex) ^ (1 : Complex) * (x : Complex) ^ (-s - 1) := by
          rw [Complex.cpow_one]
        _ = (x : Complex) ^ ((1 : Complex) + (-s - 1)) := (Complex.cpow_add _ _ hx0).symm
        _ = _ := by rw [show (1 : Complex) + (-s - 1) = -s by ring]
    dsimp [F, L, D]
    rw [Complex.ofReal_sub, sub_mul, hLinear]
  change And (Integrable D mu) _
  refine And.intro ((hF.1.sub hL).congr hEq) ?_
  calc
    integral mu D = integral mu (fun x => F x - L x) := (integral_congr_ae hEq).symm
    _ = _ := by rw [integral_sub hF.1 hL, hF.2, hLValue]

/-- The weight whose integrated tail enters the converse to the
fieldwise Robin criterion. -/
noncomputable def dedekindChebyshevErrorRatio (x : Real) : Real :=
  (dedekindChebyshev K x - x) / x ^ 2

theorem measurable_dedekindChebyshevErrorRatio : Measurable (dedekindChebyshevErrorRatio K) := by
  have hPsi : Measurable (dedekindChebyshev K) := by
    unfold dedekindChebyshev
    let F : Nat -> Real := fun n => (primePowersUpTo K n).sum
      (fun pn => Real.log (dedekindPrimeNorm K pn.1 : Real))
    exact (measurable_of_countable F).comp Nat.measurable_floor
  exact (hPsi.sub measurable_id).div (measurable_id.pow_const 2)

theorem dedekindChebyshevErrorRatio_mellin {s : Complex} (hs : 1 < s.re) :
    integral (volume.restrict (Ioi (1 : Real))) (fun x : Real =>
      (x : Complex) ^ (1 - s) * (dedekindChebyshevErrorRatio K x : Complex)) =
      (-deriv (dedekindZeta K) s / dedekindZeta K s) / s - 1 / (s - 1) := by
  refine (integral_congr_ae ?_).trans (dedekindChebyshevError_mellin K hs).2
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : Not ((x : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (zero_lt_one.trans (show 1 < x from hx)).ne'
  have hTwo : (x : Complex) ^ (2 : Complex) = (x : Complex) ^ (2 : Nat) := by
    simp
  have hInv : Inv.inv ((x : Complex) ^ (2 : Nat)) = (x : Complex) ^ (-(2 : Complex)) := by
    rw [Complex.cpow_neg, hTwo]
  unfold dedekindChebyshevErrorRatio
  rw [Complex.ofReal_div, Complex.ofReal_pow, div_eq_mul_inv, hInv]
  calc
    _ = ((dedekindChebyshev K x - x : Real) : Complex) *
        ((x : Complex) ^ (1 - s) * (x : Complex) ^ (-(2 : Complex))) := by ring
    _ = _ := by
      rw [<- Complex.cpow_add _ _ hx0, show (1 : Complex) - s + (-2) = -s - 1 by ring]

end Robin1984.GRH
