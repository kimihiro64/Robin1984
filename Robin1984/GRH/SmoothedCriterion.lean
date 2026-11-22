import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Robin1984.GRH.PositiveMellinMeasure
import Robin1984.GRH.TriangularConverse
import Robin1984.GRH.TriangularRemainder

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Landau's theorem applied to the complement of a one-sided triangular square-root bound.
- Formalization note: The real arithmetic comparison, its absolute-convergence half-plane, and the logarithmic derivative of the pole-removed function are joined in the same nonvanishing theorem.
- PROVENANCE-END
-/

/-!
# Nonvanishing from the triangular square-root bound

The coefficient sum is signed. Only its comparison against the
square-root bound needs to be nonnegative. The pole-removal terms combine
before applying the holomorphic continuation argument.
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace Robin1984.GRH

private noncomputable def triangularComparisonModel (m C : Real) (s : Complex) : Complex :=
  (C : Complex) / (s - ((1 / 2 : Real) : Complex)) -
    ((m / 2 : Real) : Complex) * (s + 2) / (s * (s + 1))

private theorem triangularComparisonModel_analytic (m C : Real) :
    AnalyticOnNhd Complex (triangularComparisonModel m C) {s : Complex | (1 / 2 : Real) < s.re} := by
  intro s hs
  have hHalf : (1 / 2 : Real) < s.re := hs
  have hPos : 0 < s.re := (by norm_num : 0 < (1 / 2 : Real)).trans hHalf
  have hD : Not (s * (s + 1) = 0) := mul_ne_zero (Complex.ne_zero_of_re_pos hPos)
    (Complex.ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.one_re]; linarith))
  have hH : Not (s - ((1 / 2 : Real) : Complex) = 0) := Complex.ne_zero_of_re_pos (by
    simpa only [Complex.sub_re, Complex.ofReal_re, sub_pos] using hHalf)
  exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hH).sub
    ((analyticAt_const.mul (analyticAt_id.add analyticAt_const)).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) hD)

/-- A one-sided triangular bound gives the zero-free right half of the
critical strip for any holomorphic pole-removed function with the stated
absolutely convergent logarithmic-derivative expansion. -/
theorem ne_zero_of_triangularSquareRootBound {iota : Type*} [Countable iota]
    (a b : iota -> Real) (m C : Real) (ha : forall i, 1 <= a i)
    (hSum : forall r : Real, 1 < r -> Summable (fun i => norm (b i) * (a i) ^ (-r)))
    {f : Complex -> Complex}
    (hf : AnalyticOnNhd Complex f {s : Complex | (1 / 2 : Real) < s.re})
    (hfTwo : Not (f ((2 : Real) : Complex) = 0))
    (hDirichlet : forall s : Complex, 1 < s.re ->
      logDeriv f s = (m : Complex) / (s - 1) -
        tsum (fun i => (b i : Complex) * (a i : Complex) ^ (-s)))
    (hBound : forall x : Real, 1 < x -> triangularRemainder a b m x <= C * Real.sqrt x)
    {z : Complex} (hz : (1 / 2 : Real) < z.re) : Not (f z = 0) := by
  let F : Real -> Real := fun x => C * Real.sqrt x - triangularRemainder a b m x
  let mu := positiveMellinMeasure F 1 0
  have hMeas : Measurable F :=
    (measurable_const.mul Real.continuous_sqrt.measurable).sub
      (measurable_triangularRemainder a b m)
  have hNonneg (x : Real) (hx : 1 < x) : 0 <= F x := sub_nonneg.mpr (hBound x hx)
  have hSupport := ae_nonneg_log_positiveMellinMeasure F (le_refl (1 : Real)) 0
  have hMoment (t : Real) (ht : t < -1) : Membership.mem (integrableExpSet Real.log mu) t := by
    apply (mem_integrableExpSet_positiveMellinMeasure_iff hMeas (le_refl (1 : Real))
      hNonneg 0 t).mpr
    have htRe : 1 < (-(t : Complex)).re := by
      rw [Complex.neg_re, Complex.ofReal_re]
      exact lt_neg_of_lt_neg ht
    have hC : IntegrableOn (fun x : Real => ((F x : Real) : Complex) *
        (x : Complex) ^ (-(-(t : Complex)) - 1)) (Ioi (1 : Real)) :=
      (triangularComparison_mellin a b m C (-(t : Complex)) htRe ha
        (hSum (-(t : Complex)).re htRe)).1
    have hR : IntegrableOn (fun x : Real => (((F x : Real) : Complex) *
        (x : Complex) ^ (-(-(t : Complex)) - 1)).re) (Ioi (1 : Real)) := hC.re
    refine hR.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : Real) <= x := zero_le_one.trans hx.le
    have hExp : -(-(t : Complex)) - 1 = ((t - 0 - 1 : Real) : Complex) := by
      simp only [neg_neg, sub_zero, Complex.ofReal_sub, Complex.ofReal_one]
    change (((F x : Real) : Complex) *
      (x : Complex) ^ (-(-(t : Complex)) - 1)).re = F x * x ^ (t - 0 - 1)
    rw [hExp, <- Complex.ofReal_cpow hx0, <- Complex.ofReal_mul, Complex.ofReal_re]
  have hModel := triangularComparisonModel_analytic m C
  have hBase : (1 / 2 : Real) < (((2 : Real) : Complex)).re := by
    rw [Complex.ofReal_re]
    norm_num
  have hBaseExp : Membership.mem (interior (integrableExpSet Real.log mu)) (-((2 : Real) : Complex)).re :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Iio_mem_nhds (by
        rw [Complex.neg_re, Complex.ofReal_re]
        norm_num : (-((2 : Real) : Complex)).re < -1)) (fun t ht => hMoment t ht))
  have hNear : Filter.Eventually (fun s : Complex => 1 < s.re) (nhds ((2 : Real) : Complex)) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      change 1 < (((2 : Real) : Complex)).re
      rw [Complex.ofReal_re]
      norm_num)
  have hNearNonzero : Filter.Eventually (fun s => Not (f s = 0)) (nhds ((2 : Real) : Complex)) :=
    (hf _ hBase).continuousAt.tendsto.eventually (isOpen_ne.mem_nhds hfTwo)
  apply ne_zero_of_triangularTransform Real.measurable_log hSupport
    (by norm_num : 0 < (1 / 2 : Real)) hf hModel hBase hBaseExp hfTwo
  filter_upwards [hNear, hNearNonzero] with s hs hsNonzero
  have hM : complexMGF Real.log mu (-s) =
      (C : Complex) / (s - ((1 / 2 : Real) : Complex)) -
        ((m / 2 : Real) : Complex) / (s - 1) +
        tsum (fun i => (b i : Complex) * (a i : Complex) ^ (-s)) / (s * (s + 1)) := by
    change complexMGF Real.log (positiveMellinMeasure F 1 0) (-s) = _
    rw [complexMGF_log_positiveMellinMeasure hMeas (le_refl (1 : Real)) hNonneg]
    simpa only [Complex.ofReal_zero, sub_zero] using
      (triangularComparison_mellin a b m C s hs ha (hSum s.re hs)).2
  have hPos := zero_lt_one.trans hs
  have hS := Complex.ne_zero_of_re_pos hPos
  have hSAdd : Not (s + 1 = 0) := Complex.ne_zero_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hSSub : Not (s - 1 = 0) := Complex.ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith)
  have hCancel :
      s * (s + 1) * (triangularComparisonModel m C s - complexMGF Real.log mu (-s)) =
        logDeriv f s := by
    rw [hM, hDirichlet s hs, triangularComparisonModel]
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    field_simp [hS, hSAdd, hSSub]; ring
  change deriv f s =
    f s * (s * (s + 1) * (triangularComparisonModel m C s - complexMGF Real.log mu (-s)))
  rw [hCancel, logDeriv_apply]
  field_simp [hsNonzero]
  exact hz

/-- An eventual triangular square-root bound excludes right-half-plane
zeros for locally finite coefficients with the stated pole-removed
logarithmic derivative. -/
theorem ne_zero_of_eventual_triangularSquareRootBound {iota : Type*} [Countable iota]
    (a b : iota -> Real) (m : Real) (ha : forall i, 1 <= a i)
    (hFinite : forall T : Real, Set.Finite {i : iota | a i < T})
    (hSum : forall r : Real, 1 < r -> Summable (fun i => norm (b i) * (a i) ^ (-r)))
    {f : Complex -> Complex}
    (hf : AnalyticOnNhd Complex f {s : Complex | (1 / 2 : Real) < s.re})
    (hfTwo : Not (f ((2 : Real) : Complex) = 0))
    (hDirichlet : forall s : Complex, 1 < s.re ->
      logDeriv f s = (m : Complex) / (s - 1) -
        tsum (fun i => (b i : Complex) * (a i : Complex) ^ (-s)))
    {T C : Real} (hT : 1 <= T)
    (hBound : forall x : Real, T <= x -> triangularRemainder a b m x <= C * Real.sqrt x)
    {z : Complex} (hz : (1 / 2 : Real) < z.re) : Not (f z = 0) := by
  choose D hD using exists_triangularSquareRootBound a b m ha hFinite hT hBound
  exact ne_zero_of_triangularSquareRootBound a b m D ha hSum hf hfTwo hDirichlet hD hz

end Robin1984.GRH
