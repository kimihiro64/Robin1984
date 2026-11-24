import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Robin1984.GRH.TriangularSeries

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The triangular comparison transform is the sum of the elementary main-term transforms and the transformed coefficient series.
- Formalization note: The comparison function is specified pointwise on the positive real tail, and the transform formula is accompanied by actual integrability.
- PROVENANCE-END
-/

/-!
# The triangular comparison transform

The pole contribution comes from the linear main term. The square-root
comparison contributes the pole at one half. Each weighted coefficient
contributes its Dirichlet term divided by the triangular Mellin kernel.
-/

open Filter MeasureTheory Set

namespace Robin1984.GRH

/-- The triangular coefficient sum, with the coefficient at the endpoint
given zero weight. -/
noncomputable def triangularCoefficientSum {iota : Type*}
    (a b : iota -> Real) (x : Real) : Real :=
  tsum (fun i => (Ioi (a i)).indicator (fun x => b i * (1 - a i / x)) x)

/-- The signed smoothed remainder for a main term of residue `m`. -/
noncomputable def triangularRemainder {iota : Type*} (a b : iota -> Real) (m x : Real) : Real :=
  m / 2 * x - triangularCoefficientSum a b x

theorem measurable_triangularRemainder {iota : Type*} [Countable iota]
    (a b : iota -> Real) (m : Real) : Measurable (triangularRemainder a b m) := by
  apply (measurable_const.mul measurable_id).sub
  exact Measurable.tsum (fun i => (measurable_const.mul
    (measurable_const.sub (measurable_const.div measurable_id))).indicator measurableSet_Ioi)

/-- An eventual square-root bound becomes a bound on the entire tail
above one when only finitely many coefficients occur below each cutoff. -/
theorem exists_triangularSquareRootBound {iota : Type*} (a b : iota -> Real) (m : Real)
    (ha : forall i, 1 <= a i)
    (hFinite : forall T : Real, Set.Finite {i : iota | a i < T})
    {T C : Real} (hT : 1 <= T)
    (hLarge : forall x : Real, T <= x -> triangularRemainder a b m x <= C * Real.sqrt x) :
    exists D : Real, forall x : Real, 1 < x -> triangularRemainder a b m x <= D * Real.sqrt x := by
  classical
  let S := (hFinite T).toFinset
  let B : Real := abs m / 2 * T + S.sum (fun i => abs (b i))
  have hB : 0 <= B := add_nonneg
    (mul_nonneg (div_nonneg (abs_nonneg m) (by norm_num)) (zero_le_one.trans hT))
    (Finset.sum_nonneg (fun i _ => abs_nonneg (b i)))
  refine Exists.intro (max B C) (fun x hx => ?_)
  by_cases hTx : T <= x
  case pos =>
    exact (hLarge x hTx).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg x))
  case neg =>
    have hxT : x < T := lt_of_not_ge hTx
    have hx0 : 0 < x := zero_lt_one.trans hx
    let term : iota -> Real :=
      fun i => (Ioi (a i)).indicator (fun y => b i * (1 - a i / y)) x
    have hSumEq : triangularCoefficientSum a b x = S.sum term := by
      apply tsum_eq_sum
      intro i hi
      have hTNorm : Not (a i < T) := fun h => hi ((hFinite T).mem_toFinset.mpr h)
      exact indicator_of_notMem (fun h => hTNorm (lt_trans h hxT)) _
    have hTerm (i : iota) : - abs (b i) <= term i := by
      by_cases hi : Membership.mem (Ioi (a i)) x
      case neg =>
        change -abs (b i) <= (Ioi (a i)).indicator (fun y => b i * (1 - a i / y)) x
        rw [indicator_of_notMem hi]
        exact neg_nonpos.mpr (abs_nonneg _)
      case pos =>
        change -abs (b i) <= (Ioi (a i)).indicator (fun y => b i * (1 - a i / y)) x
        rw [indicator_of_mem hi]
        have hWeight0 : 0 <= 1 - a i / x :=
          sub_nonneg.mpr ((div_le_one hx0).mpr hi.le)
        have hWeight1 : 1 - a i / x <= 1 :=
          sub_le_self _ (div_nonneg (zero_le_one.trans (ha i)) hx0.le)
        have hAbs : abs (b i * (1 - a i / x)) <= abs (b i) := by
          rw [abs_mul, abs_of_nonneg hWeight0]
          exact mul_le_of_le_one_right (abs_nonneg _) hWeight1
        exact (neg_le_neg hAbs).trans (neg_abs_le _)
    have hSumLower : -(S.sum (fun i => abs (b i))) <= triangularCoefficientSum a b x := by
      rw [hSumEq, <- Finset.sum_neg_distrib]
      exact Finset.sum_le_sum (fun i _ => hTerm i)
    have hLin : m / 2 * x <= abs m / 2 * T :=
      mul_le_mul (div_le_div_of_nonneg_right (le_abs_self m) (by norm_num))
        hxT.le hx0.le (div_nonneg (abs_nonneg _) (by norm_num))
    have hRem : triangularRemainder a b m x <= B := by
      unfold triangularRemainder
      change m / 2 * x - triangularCoefficientSum a b x <=
        abs m / 2 * T + S.sum (fun i => abs (b i))
      linarith only [hLin, hSumLower]
    have hSqrt : 1 <= Real.sqrt x := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx.le
    exact hRem.trans ((le_max_left _ _).trans
      (le_mul_of_one_le_right (hB.trans (le_max_left _ _)) hSqrt))

private theorem triangular_mellin_monomial (p c : Real) (s : Complex) (hs : p < s.re) :
    let K := fun x : Real => (c : Complex) * (x : Complex) ^ ((p : Complex) - s - 1)
    And (Integrable K (volume.restrict (Ioi (1 : Real))))
      (integral (volume.restrict (Ioi (1 : Real))) K = (c : Complex) / (s - (p : Complex))) := by
  have hExponent : ((p : Complex) - s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith only [hs]
  refine And.intro ((integrableOn_Ioi_cpow_of_lt hExponent zero_lt_one).const_mul _) ?_
  rw [integral_const_mul, integral_Ioi_cpow_of_lt hExponent zero_lt_one]
  have hAdd : (p : Complex) - s - 1 + 1 = -(s - (p : Complex)) := by ring
  rw [hAdd, Complex.ofReal_one, Complex.one_cpow, neg_div_neg_eq, mul_one_div]

private theorem cast_triangleSum_mul_cpow {iota : Type*} (a b : iota -> Real)
    (s : Complex) (x : Real) :
    (triangularCoefficientSum a b x : Complex) * (x : Complex) ^ (-s - 1) =
      tsum (fun i => (Ioi (a i)).indicator (fun x : Real =>
        (b i : Complex) * ((1 - (a i : Complex) / (x : Complex)) * (x : Complex) ^ (-s - 1))) x) := by
  rw [triangularCoefficientSum, Complex.ofReal_tsum, <- tsum_mul_right]
  apply tsum_congr
  intro i
  by_cases hx : Membership.mem (Ioi (a i)) x
  case pos =>
    simp only [indicator_of_mem hx, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_div, Complex.ofReal_mul, mul_assoc]
  case neg =>
    simp only [indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]

/-- The comparison against a square-root bound has a convergent Mellin
integral wherever the underlying Dirichlet series converges absolutely and
the real part exceeds one. -/
theorem triangularComparison_mellin {iota : Type*} [Countable iota]
    (a b : iota -> Real) (m C : Real) (s : Complex) (hs : 1 < s.re)
    (ha : forall i, 1 <= a i)
    (hSummable : Summable (fun i => norm (b i) * (a i) ^ (-s.re))) :
    let K := fun x : Real =>
      ((C * Real.sqrt x - triangularRemainder a b m x : Real) : Complex) *
        (x : Complex) ^ (-s - 1)
    And (Integrable K (volume.restrict (Ioi (1 : Real))))
      (integral (volume.restrict (Ioi (1 : Real))) K =
        (C : Complex) / (s - ((1 / 2 : Real) : Complex)) -
          ((m / 2 : Real) : Complex) / (s - 1) +
          tsum (fun i => (b i : Complex) * (a i : Complex) ^ (-s)) / (s * (s + 1))) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let P := fun x : Real => (C : Complex) * (x : Complex) ^ (((1 / 2 : Real) : Complex) - s - 1)
  let Q := fun x : Real => ((m / 2 : Real) : Complex) * (x : Complex) ^ (((1 : Real) : Complex) - s - 1)
  let T := fun x : Real => tsum (fun i =>
    (Ioi (a i)).indicator (fun x : Real =>
      (b i : Complex) * ((1 - (a i : Complex) / (x : Complex)) * (x : Complex) ^ (-s - 1))) x)
  let K := fun x : Real =>
    ((C * Real.sqrt x - triangularRemainder a b m x : Real) : Complex) *
      (x : Complex) ^ (-s - 1)
  have hP := triangular_mellin_monomial (1 / 2) C s
    ((by norm_num : (1 / 2 : Real) < 1).trans hs)
  have hQ := triangular_mellin_monomial 1 (m / 2) s hs
  have hT := integrable_integral_tsum_triangularMellin a (fun i => (b i : Complex)) s
    (zero_lt_one.trans hs) (fun i => zero_lt_one.trans_le (ha i))
    (by simpa only [Complex.norm_real] using hSummable)
  have hTInt : Integrable T mu := hT.1.integrableOn
  have hTVal : integral mu T =
      tsum (fun i => (b i : Complex) * (a i : Complex) ^ (-s)) / (s * (s + 1)) := by
    have hTWithin : (Ioi (1 : Real)).indicator T = T := by
      funext x
      by_cases hx : Membership.mem (Ioi (1 : Real)) x
      case pos => exact indicator_of_mem hx _
      case neg =>
        rw [indicator_of_notMem hx]
        have hx1 : x <= 1 := le_of_not_gt hx
        symm
        unfold T
        have hZero (i : iota) : Not (Membership.mem (Ioi (a i)) x) :=
          not_lt_of_ge (hx1.trans (ha i))
        simp only [indicator_of_notMem (hZero _), tsum_zero]
    change integral (volume.restrict (Ioi (1 : Real))) T = _
    rw [<- integral_indicator measurableSet_Ioi, hTWithin]
    exact hT.2
  have hEq : EqOn (fun x => P x - Q x + T x) K (Ioi 1) := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hxn : Not ((x : Complex) = 0) := Complex.ofReal_ne_zero.mpr hx0.ne'
    have hSqrt : (Real.sqrt x : Complex) * (x : Complex) ^ (-s - 1) =
        (x : Complex) ^ (((1 / 2 : Real) : Complex) - s - 1) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx0.le, <- Complex.cpow_add _ _ hxn]
      congr 1
      ring
    have hLin : (x : Complex) * (x : Complex) ^ (-s - 1) =
        (x : Complex) ^ (((1 : Real) : Complex) - s - 1) := by
      calc
        _ = (x : Complex) ^ (1 : Complex) * (x : Complex) ^ (-s - 1) := by
          rw [Complex.cpow_one]
        _ = (x : Complex) ^ (1 + (-s - 1)) := (Complex.cpow_add _ _ hxn).symm
        _ = _ := by rw [Complex.ofReal_one]; congr 1; ring
    have hTri := cast_triangleSum_mul_cpow a b s x
    change P x - Q x + T x =
      ((C * Real.sqrt x - (m / 2 * x - triangularCoefficientSum a b x) : Real) : Complex) *
        (x : Complex) ^ (-s - 1)
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, sub_mul, mul_assoc, hSqrt, hLin]
    rw [hTri]
    change P x - Q x + T x = P x - (Q x - T x)
    ring
  change And (Integrable K mu) (integral mu K = _)
  have hPInt : Integrable P mu := hP.1
  have hQInt : Integrable Q mu := hQ.1
  have hSumInt : IntegrableOn (fun x => P x - Q x + T x) (Ioi (1 : Real)) :=
    (hPInt.sub hQInt).add hTInt
  refine And.intro (hSumInt.congr_fun hEq measurableSet_Ioi) ?_
  calc
    integral mu K = integral mu (fun x => P x - Q x + T x) :=
      (setIntegral_congr_fun measurableSet_Ioi hEq).symm
    _ = integral mu (fun x => P x - Q x) + integral mu T :=
      integral_add (hPInt.sub hQInt) hTInt
    _ = integral mu P - integral mu Q + integral mu T := by rw [integral_sub hPInt hQInt]
    _ = _ := by
      rw [show integral mu P = _ from hP.2, show integral mu Q = _ from hQ.2, hTVal]
      simp only [Complex.ofReal_one]

/-- Local finiteness and the vanishing of each weight at its cutoff give
continuity of the signed triangular remainder on the positive tail. -/
theorem continuousOn_triangularRemainder {iota : Type*}
    (a b : iota -> Real) (m : Real)
    (hFinite : forall T : Real, Set.Finite {i : iota | a i < T}) :
    ContinuousOn (triangularRemainder a b m) (Ioi (1 : Real)) := by
  classical
  intro x hx
  let cutoff : Real := x + 1
  let S := (hFinite cutoff).toFinset
  let w (i : iota) (y : Real) := 1 - a i / y
  let g (i : iota) (y : Real) := b i * ((abs (w i y) + w i y) / 2)
  let R (y : Real) := m / 2 * y - S.sum (fun i => g i y)
  have hG (i : iota) : ContinuousOn (g i) (Ioi (1 : Real)) := by
    have hw : ContinuousOn (w i) (Ioi (1 : Real)) :=
      continuousOn_const.sub (continuousOn_const.div continuousOn_id
        (fun y hy => (zero_lt_one.trans hy).ne'))
    have hAbs : ContinuousOn (fun y => abs (w i y)) (Ioi (1 : Real)) :=
      continuous_abs.comp_continuousOn hw
    exact continuousOn_const.mul ((hAbs.add hw).div_const 2)
  have hR : ContinuousOn R (Ioi (1 : Real)) :=
    (continuousOn_const.mul continuousOn_id).sub (continuousOn_finsetSum S (fun i _ => hG i))
  have hEq : Filter.EventuallyEq (nhds x) (triangularRemainder a b m) R := by
    have hxCut : x < cutoff := lt_add_of_pos_right x zero_lt_one
    filter_upwards [isOpen_Ioo.mem_nhds (show Membership.mem (Ioo (1 : Real) cutoff) x
      from And.intro hx hxCut)] with y hy
    have hy0 : 0 < y := zero_lt_one.trans hy.1
    have hterm (i : iota) :
        (Ioi (a i)).indicator (fun z => b i * (1 - a i / z)) y = g i y := by
      by_cases h : a i < y
      case pos =>
        rw [indicator_of_mem (show Membership.mem (Ioi (a i)) y from h)]
        have hpos : 0 <= w i y := sub_nonneg.mpr ((div_le_one hy0).mpr h.le)
        dsimp only [g]
        rw [abs_of_nonneg hpos]
        dsimp [w]
        ring
      case neg =>
        rw [indicator_of_notMem (show Not (Membership.mem (Ioi (a i)) y) from h)]
        have hneg : w i y <= 0 := sub_nonpos.mpr ((one_le_div hy0).mpr (le_of_not_gt h))
        simp only [g, abs_of_nonpos hneg, neg_add_cancel, zero_div, mul_zero]
    let term : iota -> Real := fun i => (Ioi (a i)).indicator (fun z => b i * (1 - a i / z)) y
    have hSum : triangularCoefficientSum a b y = S.sum term := by
      apply tsum_eq_sum
      intro i hi
      have hiCut : Not (a i < cutoff) := fun h => hi ((hFinite cutoff).mem_toFinset.mpr h)
      exact indicator_of_notMem (fun h => hiCut (lt_trans h hy.2)) _
    simp only [triangularRemainder, R, hSum, term, hterm]
  have hAt : ContinuousAt (triangularRemainder a b m) x :=
    ((hR x hx).continuousAt (isOpen_Ioi.mem_nhds hx)).congr_of_eventuallyEq hEq
  exact hAt.continuousWithinAt

/-- The signed triangular prime-power remainder for complex coefficients. -/
noncomputable def complexTriangularRemainder {i : Type*}
    (a : i -> Real) (b : i -> Complex) (m x : Real) : Complex :=
  ((m / 2 : Real) : Complex) * (x : Complex) -
    tsum (fun j => (Ioi (a j)).indicator
      (fun u : Real => b j * (1 - (a j : Complex) / (u : Complex))) x)

theorem measurable_complexTriangularRemainder {i : Type*} [Countable i]
    (a : i -> Real) (b : i -> Complex) (m : Real) : Measurable (complexTriangularRemainder a b m) := by
  apply (measurable_const.mul Complex.continuous_ofReal.measurable).sub
  exact Measurable.tsum (fun i => (measurable_const.mul
    (measurable_const.sub (measurable_const.div Complex.continuous_ofReal.measurable))).indicator
      measurableSet_Ioi)

/-- The Mellin transform of the signed complex remainder is its residue
transform minus its prime-power transform. -/
theorem complexTriangularRemainder_mellin {i : Type*} [Countable i]
    (a : i -> Real) (b : i -> Complex) (m : Real) (s : Complex) (hs : 1 < s.re)
    (ha : forall j, 1 <= a j)
    (hSum : Summable (fun j => norm (b j) * (a j) ^ (-s.re))) :
    let K := fun x : Real => complexTriangularRemainder a b m x * (x : Complex) ^ (-s - 1)
    let mu := volume.restrict (Ioi (1 : Real))
    Integrable K mu /\
      integral mu K = ((m / 2 : Real) : Complex) / (s - 1) -
        tsum (fun j => b j * (a j : Complex) ^ (-s)) / (s * (s + 1)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let Q (x : Real) : Complex := ((m / 2 : Real) : Complex) *
    (x : Complex) ^ (((1 : Real) : Complex) - s - 1)
  let T (x : Real) : Complex := tsum (fun j =>
    (Ioi (a j)).indicator (fun u : Real =>
      b j * ((1 - (a j : Complex) / (u : Complex)) * (u : Complex) ^ (-s - 1))) x)
  let K := fun x : Real => complexTriangularRemainder a b m x * (x : Complex) ^ (-s - 1)
  have hQ := triangular_mellin_monomial 1 (m / 2) s hs
  have hT := integrable_integral_tsum_triangularMellin a b s
    (zero_lt_one.trans hs) (fun i => zero_lt_one.trans_le (ha i)) hSum
  have hQInt : Integrable Q mu := hQ.1
  have hTInt : Integrable T mu := hT.1.integrableOn
  have hTValue : integral mu T =
      tsum (fun j => b j * (a j : Complex) ^ (-s)) / (s * (s + 1)) := by
    have hTWithin : (Ioi (1 : Real)).indicator T = T := by
      funext x
      by_cases hx : Membership.mem (Ioi (1 : Real)) x
      case pos => exact indicator_of_mem hx T
      case neg =>
        rw [indicator_of_notMem hx]
        have hx1 : x <= 1 := le_of_not_gt hx
        symm
        unfold T
        have hZero (j : i) : Not (Membership.mem (Ioi (a j)) x) :=
          not_lt_of_ge (hx1.trans (ha j))
        simp only [indicator_of_notMem (hZero _), tsum_zero]
    change integral (volume.restrict (Ioi (1 : Real))) T = _
    rw [<- integral_indicator measurableSet_Ioi, hTWithin]
    exact hT.2
  have hEq : EqOn (fun x => Q x - T x) K (Ioi (1 : Real)) := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hxn : Not ((x : Complex) = 0) := Complex.ofReal_ne_zero.mpr hx0.ne'
    have hLin : (x : Complex) * (x : Complex) ^ (-s - 1) =
        (x : Complex) ^ (((1 : Real) : Complex) - s - 1) := by
      calc
        _ = (x : Complex) ^ (1 : Complex) * (x : Complex) ^ (-s - 1) := by
          rw [Complex.cpow_one]
        _ = (x : Complex) ^ (1 + (-s - 1)) := (Complex.cpow_add _ _ hxn).symm
        _ = _ := by rw [Complex.ofReal_one]; congr 1; ring
    have hTriangle :
        tsum (fun j => (Ioi (a j)).indicator
          (fun u : Real => b j * (1 - (a j : Complex) / (u : Complex))) x) *
          (x : Complex) ^ (-s - 1) = T x := by
      unfold T
      rw [<- tsum_mul_right]
      refine tsum_congr ?_
      intro j
      by_cases h : Membership.mem (Ioi (a j)) x
      case pos => simp only [indicator_of_mem h, mul_assoc]
      case neg => simp only [indicator_of_notMem h, zero_mul]
    unfold K complexTriangularRemainder
    rw [sub_mul, mul_assoc, hLin, hTriangle]
  change And (Integrable K mu) (integral mu K = _)
  have hQSubT : IntegrableOn (fun x => Q x - T x) (Ioi (1 : Real)) := hQInt.sub hTInt
  refine And.intro (hQSubT.congr_fun hEq measurableSet_Ioi) ?_
  calc
    integral mu K = integral mu (fun x => Q x - T x) :=
      (setIntegral_congr_fun measurableSet_Ioi hEq).symm
    _ = integral mu Q - integral mu T := integral_sub hQInt hTInt
    _ = _ := by rw [show integral mu Q = _ from hQ.2, hTValue, Complex.ofReal_one]

/-- The complex arithmetic remainder is the Mellin input for the logarithmic
derivative of an individual pole-cleared L-function. -/
theorem complexTriangularRemainder_mellin_of_logDeriv {i : Type*} [Countable i]
    (a : i -> Real) (b : i -> Complex) (m : Real) (F : Complex -> Complex)
    (ha : forall j, 1 <= a j) (s : Complex) (hs : 1 < s.re)
    (hSum : Summable (fun j => norm (b j) * (a j) ^ (-s.re)))
    (hEuler : logDeriv F s = (m : Complex) / (s - 1) -
      tsum (fun j => b j * (a j : Complex) ^ (-s))) :
    let K := fun x : Real => complexTriangularRemainder a b m x * (x : Complex) ^ (-s - 1)
    let mu := volume.restrict (Ioi (1 : Real))
    Integrable K mu /\
      integral mu K = (logDeriv F s + (m : Complex) / 2 * (s + 2)) / (s * (s + 1)) := by
  have h := complexTriangularRemainder_mellin a b m s hs ha hSum
  refine And.intro h.1 ?_
  rw [h.2, hEuler]
  push_cast
  have hA : Not (s - 1 = 0) := Complex.ne_zero_of_re_pos (by rwa [Complex.sub_re, Complex.one_re, sub_pos])
  have hS : Not (s = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hB : Not (s + 1 = 0) := Complex.ne_zero_of_re_pos (by
    rw [Complex.add_re, Complex.one_re]
    linarith only [hs])
  field_simp [hA, hS, hB]
  ring

/-- The vanishing weight at the prime-power cutoff makes the complex
triangular remainder continuous on the open positive tail. -/
theorem continuousOn_complexTriangularRemainder {iota : Type*}
    (a : iota -> Real) (b : iota -> Complex) (m : Real)
    (hFinite : forall T : Real, Set.Finite {i : iota | a i < T}) :
    ContinuousOn (complexTriangularRemainder a b m) (Ioi (1 : Real)) := by
  classical
  intro x hx
  let cutoff : Real := x + 1
  let S := (hFinite cutoff).toFinset
  let w (i : iota) (y : Real) : Real := 1 - a i / y
  let g (i : iota) (y : Real) : Complex :=
    b i * (((abs (w i y) + w i y) / 2 : Real) : Complex)
  let R (y : Real) : Complex := ((m / 2 : Real) : Complex) * (y : Complex) -
    S.sum (fun i => g i y)
  have hG (i : iota) : ContinuousOn (g i) (Ioi (1 : Real)) := by
    have hw : ContinuousOn (w i) (Ioi (1 : Real)) :=
      continuousOn_const.sub (continuousOn_const.div continuousOn_id
        (fun y hy => (zero_lt_one.trans hy).ne'))
    have hAbs : ContinuousOn (fun y => abs (w i y)) (Ioi (1 : Real)) :=
      continuous_abs.comp_continuousOn hw
    exact continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn ((hAbs.add hw).div_const 2))
  have hR : ContinuousOn R (Ioi (1 : Real)) :=
    (continuousOn_const.mul Complex.continuous_ofReal.continuousOn).sub
      (continuousOn_finsetSum S (fun i _ => hG i))
  have hEq : Filter.EventuallyEq (nhds x) (complexTriangularRemainder a b m) R := by
    have hxCut : x < cutoff := lt_add_of_pos_right x zero_lt_one
    filter_upwards [isOpen_Ioo.mem_nhds (show Membership.mem (Ioo (1 : Real) cutoff) x
      from And.intro hx hxCut)] with y hy
    have hy0 : 0 < y := zero_lt_one.trans hy.1
    let term (i : iota) : Complex := (Ioi (a i)).indicator
      (fun z : Real => b i * (1 - (a i : Complex) / (z : Complex))) y
    have hterm (i : iota) : term i = g i y := by
      by_cases h : a i < y
      case pos =>
        unfold term
        rw [indicator_of_mem (show Membership.mem (Ioi (a i)) y from h)]
        have hpos : 0 <= w i y := sub_nonneg.mpr ((div_le_one hy0).mpr h.le)
        have hhalf : (w i y + w i y) / 2 = w i y := by ring
        dsimp only [g]
        rw [abs_of_nonneg hpos, hhalf]
        simp only [w, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div]
      case neg =>
        unfold term
        rw [indicator_of_notMem (show Not (Membership.mem (Ioi (a i)) y) from h)]
        have hneg : w i y <= 0 := sub_nonpos.mpr ((one_le_div hy0).mpr (le_of_not_gt h))
        simp only [g, abs_of_nonpos hneg, neg_add_cancel, zero_div, Complex.ofReal_zero, mul_zero]
    have hSum : tsum term = S.sum term := by
      apply tsum_eq_sum
      intro i hi
      have hiCut : Not (a i < cutoff) := fun h => hi ((hFinite cutoff).mem_toFinset.mpr h)
      exact indicator_of_notMem (fun h => hiCut (lt_trans h hy.2)) _
    change ((m / 2 : Real) : Complex) * (y : Complex) - tsum term = R y
    simp only [R, hSum, hterm]
  have hAt : ContinuousAt (complexTriangularRemainder a b m) x :=
    ((hR x hx).continuousAt (isOpen_Ioi.mem_nhds hx)).congr_of_eventuallyEq hEq
  exact hAt.continuousWithinAt

end Robin1984.GRH
