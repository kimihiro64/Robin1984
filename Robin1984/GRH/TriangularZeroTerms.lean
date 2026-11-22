import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Robin1984.GRH.TriangularSeries

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Bounds for the zero terms in the triangular explicit formula for a genus-one logarithmic derivative.
- Formalization note: The power term and its normalization are bounded together, with no requirement that all contributing zeros have equal real part.
- PROVENANCE-END
-/

/-!
# The zero contribution in the triangular explicit formula

The canonical genus-one summand contributes an elementary power minus
the normalization at exponent minus one. If the contributing zeros are
on or to the left of the critical line, the norm of the sum is at most
a constant times the square root.
-/

open MeasureTheory Set

namespace Robin1984.GRH

/-- The time-domain summand from a nonexceptional zero in the
genus-one logarithmic-derivative expansion. -/
noncomputable def triangularZeroTerm (rho : Complex) (x : Real) : Complex :=
  ((x : Complex) ^ rho - (x : Complex) ^ (-1 : Complex)) / (rho * (rho + 1))

/-- The real-part bound on one zero controls the complete normalized
triangular summand. -/
theorem norm_triangularZeroTerm_le {rho : Complex} (hRho : rho.re <= 1 / 2)
    {x : Real} (hx : 1 <= x) :
    norm (triangularZeroTerm rho x) <=
      (2 * Real.sqrt x) * (norm (rho * (rho + 1))) ^ (-1 : Int) := by
  have hx0 := zero_lt_one.trans_le hx
  have hPower : norm ((x : Complex) ^ rho) <= Real.sqrt x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx hRho
  have hInverse : norm ((x : Complex) ^ (-1 : Complex)) <= Real.sqrt x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.neg_re, Complex.one_re,
      Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  rw [triangularZeroTerm, norm_div, zpow_neg_one, <- div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (by linarith only [hPower, hInverse])

/-- A summable sequence of inverse denominators controls the whole series. -/
theorem norm_tsum_triangularZeroTerm_le {iota : Type*} (rho : iota -> Complex)
    (hRho : forall i, (rho i).re <= 1 / 2)
    (hSummable : Summable (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)))
    {x : Real} (hx : 1 <= x) :
    norm (tsum (fun i => triangularZeroTerm (rho i) x)) <=
      (2 * Real.sqrt x) * tsum (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)) := by
  have hMaj := hSummable.mul_left (2 * Real.sqrt x)
  have hBound := tsum_of_norm_bounded hMaj.hasSum
    (fun i => norm_triangularZeroTerm_le (hRho i) hx)
  simpa only [tsum_mul_left] using hBound

/-- The triangular summand is the inverse Mellin term of the canonical
genus-one logarithmic derivative divided by the triangular kernel. -/
theorem triangularZeroTerm_mellin (rho s : Complex) (hRho : rho.re <= 1 / 2)
    (hRho0 : Not (rho = 0)) (hRho1 : Not (rho + 1 = 0)) (hs : 1 < s.re) :
    let K := fun x : Real => triangularZeroTerm rho x * (x : Complex) ^ (-s - 1)
    And (Integrable K (volume.restrict (Ioi (1 : Real))))
      (integral (volume.restrict (Ioi (1 : Real))) K =
        (1 / (s - rho) + 1 / rho) / (s * (s + 1))) := by
  let F := fun x : Real => (x : Complex) ^ (rho + (-s - 1))
  let G := fun x : Real => (x : Complex) ^ ((-1 : Complex) + (-s - 1))
  let K := fun x : Real => triangularZeroTerm rho x * (x : Complex) ^ (-s - 1)
  let d := rho * (rho + 1)
  have hFRe : (rho + (-s - 1)).re < -1 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith only [hRho, hs]
  have hGRe : ((-1 : Complex) + (-s - 1)).re < -1 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith only [hs]
  have hF : IntegrableOn F (Ioi (1 : Real)) := integrableOn_Ioi_cpow_of_lt hFRe zero_lt_one
  have hG : IntegrableOn G (Ioi (1 : Real)) := integrableOn_Ioi_cpow_of_lt hGRe zero_lt_one
  have hEq : EqOn (fun x => d ^ (-1 : Int) * (F x - G x)) K (Ioi 1) := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hxn := Complex.ofReal_ne_zero.mpr hx0.ne'
    change d ^ (-1 : Int) *
      ((x : Complex) ^ (rho + (-s - 1)) -
        (x : Complex) ^ ((-1 : Complex) + (-s - 1))) =
      triangularZeroTerm rho x * (x : Complex) ^ (-s - 1)
    rw [Complex.cpow_add _ _ hxn, Complex.cpow_add _ _ hxn, <- sub_mul,
      triangularZeroTerm, zpow_neg_one, div_eq_mul_inv]
    simp only [d]
    ring
  have hCombined : IntegrableOn (fun x => d ^ (-1 : Int) * (F x - G x)) (Ioi (1 : Real)) :=
    (hF.sub hG).const_mul _
  refine And.intro (hCombined.congr_fun hEq measurableSet_Ioi) ?_
  let mu := volume.restrict (Ioi (1 : Real))
  calc
    integral mu K = d ^ (-1 : Int) * (integral mu F - integral mu G) := by
      change integral (volume.restrict (Ioi (1 : Real))) K = _
      rw [<- setIntegral_congr_fun measurableSet_Ioi hEq, integral_const_mul,
        integral_sub hF hG]
    _ = _ := by
      have hFInt : integral mu F = 1 / (s - rho) := by
        change integral (volume.restrict (Ioi (1 : Real))) (fun x : Real =>
          (x : Complex) ^ (rho + (-s - 1))) = _
        rw [integral_Ioi_cpow_of_lt hFRe zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
        rw [show rho + (-s - 1) + 1 = -(s - rho) by ring, neg_div_neg_eq]
      have hGInt : integral mu G = 1 / (s + 1) := by
        change integral (volume.restrict (Ioi (1 : Real))) (fun x : Real =>
          (x : Complex) ^ ((-1 : Complex) + (-s - 1))) = _
        rw [integral_Ioi_cpow_of_lt hGRe zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
        rw [show (-1 : Complex) + (-s - 1) + 1 = -(s + 1) by ring, neg_div_neg_eq]
      have hS : Not (s = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
      have hS1 : Not (s + 1 = 0) := Complex.ne_zero_of_re_pos (by
        simp only [Complex.add_re, Complex.one_re]
        linarith only [hs])
      have hSRho : Not (s - rho = 0) := Complex.ne_zero_of_re_pos (by
        simp only [Complex.sub_re]
        linarith only [hs, hRho])
      rw [hFInt, hGInt, zpow_neg_one]
      dsimp only [d]
      field_simp [hRho0, hRho1, hS, hS1, hSRho]; ring

/-- Summing the canonical zero terms commutes with the triangular Mellin
transform under absolute summability of the inverse denominators. -/
theorem triangularZeroSeries_mellin {iota : Type*} [Countable iota] (rho : iota -> Complex)
    (hRho : forall i, (rho i).re <= 1 / 2)
    (hRho0 : forall i, Not (rho i = 0)) (hRho1 : forall i, Not (rho i + 1 = 0))
    (hSummable : Summable (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int)))
    (s : Complex) (hs : 1 < s.re) :
    let K := fun x : Real =>
      tsum (fun i => triangularZeroTerm (rho i) x) * (x : Complex) ^ (-s - 1)
    And (Integrable K (volume.restrict (Ioi (1 : Real))))
      (integral (volume.restrict (Ioi (1 : Real))) K =
        tsum (fun i => 1 / (s - rho i) + 1 / rho i) / (s * (s + 1))) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let F := fun (i : iota) (x : Real) =>
    triangularZeroTerm (rho i) x * (x : Complex) ^ (-s - 1)
  let w := fun i : iota => (norm (rho i * (rho i + 1))) ^ (-1 : Int)
  let exponent : Real := -s.re - 1 / 2
  have hExp : exponent < -1 := by dsimp [exponent]; linarith only [hs]
  have hF (i : iota) : Integrable (F i) mu :=
    (triangularZeroTerm_mellin (rho i) s (hRho i) (hRho0 i) (hRho1 i) hs).1
  let B := fun (i : iota) (x : Real) => (2 * w i) * x ^ exponent
  have hB (i : iota) : Integrable (B i) mu :=
    (integrableOn_Ioi_rpow_of_lt hExp zero_lt_one).const_mul _
  have hNorm (i : iota) (x : Real) (hx : 1 < x) : norm (F i x) <= B i x := by
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hPow : norm ((x : Complex) ^ (-s - 1)) = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    change norm (triangularZeroTerm (rho i) x * (x : Complex) ^ (-s - 1)) <=
      (2 * w i) * x ^ exponent
    rw [norm_mul, hPow]
    calc
      _ <= (2 * Real.sqrt x * w i) * x ^ (-s.re - 1) :=
        mul_le_mul_of_nonneg_right (norm_triangularZeroTerm_le (hRho i) hx.le)
          (Real.rpow_nonneg hx0.le _)
      _ = (2 * w i) * (x ^ (1 / 2 : Real) * x ^ (-s.re - 1)) := by
        rw [Real.sqrt_eq_rpow]; ring
      _ = _ := by
        rw [<- Real.rpow_add hx0]
        unfold exponent
        congr 1
        ring
  have hBI (i : iota) : integral mu (B i) = (2 * w i) / (s.re - 1 / 2) := by
    change integral (volume.restrict (Ioi (1 : Real))) (fun x => (2 * w i) * x ^ exponent) = _
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hExp zero_lt_one, Real.one_rpow]
    rw [show exponent + 1 = -(s.re - 1 / 2) by dsimp [exponent]; ring,
      neg_div_neg_eq, mul_one_div]
  have hSum : Summable (fun i => integral mu (fun x => norm (F i x))) := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg (F i x)))
      (fun i => ?_) ((hSummable.mul_left 2).div_const (s.re - 1 / 2))
    rw [show 2 * w i / (s.re - 1 / 2) = integral mu (B i) from (hBI i).symm]
    exact integral_mono_ae (hF i).norm (hB i)
      (ae_restrict_of_forall_mem measurableSet_Ioi (hNorm i))
  have hPointwise (x : Real) : tsum (fun i => F i x) =
      tsum (fun i => triangularZeroTerm (rho i) x) * (x : Complex) ^ (-s - 1) := by
    exact tsum_mul_right
  simp_rw [<- hPointwise]
  refine And.intro (integrable_tsum_complex_of_norm_integrals hF hSum) ?_
  rw [<- integral_tsum_of_summable_integral_norm hF hSum, <- tsum_div_const]
  apply tsum_congr
  intro i
  exact (triangularZeroTerm_mellin (rho i) s (hRho i) (hRho0 i) (hRho1 i) hs).2

end Robin1984.GRH
