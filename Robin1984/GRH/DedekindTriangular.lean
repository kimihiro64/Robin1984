import Robin1984.GRH.DedekindRobinReverse
import Robin1984.GRH.DedekindRobinSpectralForward

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Triangular prime-power smoothing and the primitive-tail bound for the Dedekind Chebyshev error.
- Formalization note: The two directions use the existing Landau converse and integration by parts on the actual prime-ideal coefficients.
- PROVENANCE-END
-/

/-!
# The triangular Robin criterion for Dedekind zeta

The smoothed sum uses the actual prime-ideal powers of a number field.
The Dedekind primitive-tail estimate gives the upper bound, and the
Landau criterion gives the converse. The two Robin criteria therefore
test the same fieldwise zero condition.
-/

set_option autoImplicit false

open DedekindZeta Filter IsDedekindDomain MeasureTheory NumberField Set

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "PP" => Prod P Nat

private noncomputable def dedekindTriangularNorm (pn : PP) : Real := dedekindPrimePowerNorm K pn

private noncomputable def dedekindTriangularCoefficient (pn : PP) : Real :=
  Real.log (dedekindPrimeNorm K pn.1 : Real)

/-- The triangular prime-ideal remainder with the pole of Dedekind zeta
subtracted. All primes of a given norm are counted separately. -/
noncomputable def dedekindTriangularRemainder (x : Real) : Real :=
  triangularRemainder (dedekindTriangularNorm K) (dedekindTriangularCoefficient K) 1 x

/-- The signed triangular remainder for a field has an eventual
square-root upper bound. -/
def DedekindTriangularRobin : Prop :=
  exists cutoff C : Real, 1 <= cutoff /\
    forall x : Real, cutoff <= x -> dedekindTriangularRemainder K x <= C * Real.sqrt x

private theorem countable_dedekindTriangularIndex : Countable PP := by
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

private theorem one_le_dedekindTriangularNorm (pn : PP) : 1 <= dedekindTriangularNorm K pn := by
  have hp := one_lt_dedekindPrimeNorm K pn.1
  unfold dedekindTriangularNorm dedekindPrimePowerNorm
  exact_mod_cast Nat.one_le_pow (pn.2 + 1) (dedekindPrimeNorm K pn.1) hp.le

private theorem finite_dedekindTriangularNorm_lt (T : Real) :
    Set.Finite {pn : PP | dedekindTriangularNorm K pn < T} := by
  apply (finite_primePowerNorm_le K (Nat.ceil T)).subset
  intro pn hp
  have h : ((dedekindPrimePowerNorm K pn : Nat) : Real) <= (Nat.ceil T : Real) :=
    le_trans (show dedekindTriangularNorm K pn <= T from hp.le) (Nat.le_ceil T)
  exact_mod_cast h

private theorem dedekindPrimePowerTerm_eq_triangularTerm (pn : PP) (s : Complex) :
    dedekindPrimePowerTerm K pn.1 pn.2 s =
      (dedekindTriangularCoefficient K pn : Complex) * (dedekindTriangularNorm K pn : Complex) ^ (-s) := by
  unfold dedekindPrimePowerTerm dedekindTriangularCoefficient dedekindTriangularNorm dedekindPrimePowerNorm
  rw [Complex.ofReal_log (by positivity), Complex.ofReal_natCast, Complex.ofReal_natCast]

private theorem summable_dedekindTriangularCoefficient (r : Real) (hr : 1 < r) :
    Summable (fun pn : PP =>
      norm (dedekindTriangularCoefficient K pn) * (dedekindTriangularNorm K pn) ^ (-r)) := by
  have hs : 1 < (r : Complex).re := by simpa only [Complex.ofReal_re] using hr
  refine (summable_norm_dedekindPrimePowerTerm K hs).congr ?_
  intro pn
  have hPos := zero_lt_one.trans_le (one_le_dedekindTriangularNorm K pn)
  rw [dedekindPrimePowerTerm_eq_triangularTerm K, norm_mul, Complex.norm_real,
    Complex.norm_cpow_eq_rpow_re_of_pos hPos, Complex.neg_re, Complex.ofReal_re]

private theorem logDeriv_dedekindTriangular (s : Complex) (hs : 1 < s.re) :
    logDeriv (entirePoleFreeDedekindZeta K) s =
      ((1 : Real) : Complex) / (s - 1) -
        tsum (fun pn : PP => (dedekindTriangularCoefficient K pn : Complex) *
          (dedekindTriangularNorm K pn : Complex) ^ (-s)) := by
  have hv : Filter.EventuallyEq (nhds s) (entirePoleFreeDedekindZeta K)
      (fun z : Complex => (z - 1) * dedekindZeta K z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    rw [entirePoleFreeDedekindZeta_eq_poleFree K (zero_lt_one.trans hz), poleFreeDedekindZeta_eq K hz]
  have hS : Not (s - 1 = 0) := Complex.ne_zero_of_re_pos (by rwa [Complex.sub_re, Complex.one_re, sub_pos])
  have hNear : Filter.EventuallyEq (nhds s) (dedekindZeta K) (dedekindZetaContinuation K) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact (dedekindZetaContinuation_eq_series K hz).symm
  have hD : DifferentiableAt Complex (dedekindZeta K) s :=
    (analyticAt_dedekindZetaContinuation K (sub_ne_zero.mp hS)).differentiableAt.congr_of_eventuallyEq hNear
  rw [(logDeriv_congr_nhds hv).eq_of_nhds,
    logDeriv_mul (f := fun z : Complex => z - 1) (g := dedekindZeta K)
      s hS (dedekindZeta_ne_zero_of_one_lt_re K hs)
      (differentiableAt_id.sub_const _) hD, logDeriv_apply, logDeriv_apply]
  simp_rw [<- dedekindPrimePowerTerm_eq_triangularTerm K]
  rw [(hasSum_dedekindPrimePowerTerm K hs).tsum_eq]
  have hh : HasDerivAt (fun z : Complex => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
  rw [hh.deriv, Complex.ofReal_one, neg_div, sub_neg_eq_add]

/-- The triangular prime-power bound for a number field forces Dedekind
RH for that field. -/
theorem dedekindRH_of_dedekindTriangularRobin (hB : DedekindTriangularRobin K) : DedekindRH K := by
  let hCount : Countable PP := countable_dedekindTriangularIndex K
  choose T C hCut using hB
  apply (dedekindRH_iff_noZero_rightHalfStrip K).mpr
  intro s hs hs1 hz
  have hAnalytic : AnalyticOnNhd Complex (entirePoleFreeDedekindZeta K)
      {z : Complex | (1 / 2 : Real) < z.re} :=
    fun z _ => analyticAt_entirePoleFreeDedekindZeta K z
  have hTwo : Not (entirePoleFreeDedekindZeta K 2 = 0) :=
    entirePoleFreeDedekindZeta_ne_zero_of_one_lt_re K (by norm_num)
  have hBound (x : Real) (hx : T <= x) :
      triangularRemainder (dedekindTriangularNorm K) (dedekindTriangularCoefficient K) 1 x <=
        C * Real.sqrt x := hCut.2 x hx
  have hRight := ne_zero_of_eventual_triangularSquareRootBound
    (dedekindTriangularNorm K) (dedekindTriangularCoefficient K) 1
    (one_le_dedekindTriangularNorm K) (finite_dedekindTriangularNorm_lt K)
    (summable_dedekindTriangularCoefficient K) hAnalytic hTwo (logDeriv_dedekindTriangular K)
    hCut.1 hBound hs
  have hn : Not (s - 1 = 0) := sub_ne_zero.mpr (fun he => by simp [he] at hs1)
  exact hRight ((div_eq_zero_iff.mp hz).resolve_right hn)

private theorem dedekindChebyshev_interval_integral (x : Real) (hx : 1 <= x) :
    intervalIntegral (dedekindChebyshev K) 1 x volume =
      x * triangularCoefficientSum (dedekindTriangularNorm K) (dedekindTriangularCoefficient K) x := by
  classical
  let S := (finite_primePowerNorm_le K (Nat.floor x)).toFinset
  let a := dedekindTriangularNorm K
  let b := dedekindTriangularCoefficient K
  let mu := volume.restrict (Icc (1 : Real) x)
  let H (i : PP) : Real -> Real := (Ici (a i)).indicator (fun _ => b i)
  have hMem (i : PP) : Membership.mem S i <-> a i <= x :=
    ((finite_primePowerNorm_le K (Nat.floor x)).mem_toFinset).trans (Nat.le_floor_iff (zero_le_one.trans hx))
  have he (t : Real) (ht : Membership.mem (Icc (1 : Real) x) t) :
      dedekindChebyshev K t = S.sum (fun i => H i t) := by
    rw [dedekindChebyshev_eq_tsum K (zero_le_one.trans ht.1)]
    have hCut (i : PP) (hi : Not (Membership.mem S i)) : Not (a i <= t) :=
      fun h => hi ((hMem i).mpr (h.trans ht.2))
    have hFit (i : PP) : (if a i <= t then b i else 0) = H i t := rfl
    calc
      _ = S.sum (fun i => if a i <= t then b i else 0) := by
        apply tsum_eq_sum
        intro i hi
        exact if_neg (hCut i hi)
      _ = _ := Finset.sum_congr rfl (fun i _ => hFit i)
  have hI (i : PP) : Integrable (H i) mu := by
    have h : Integrable (fun _ : Real => b i) mu := integrable_const _
    exact h.indicator measurableSet_Ici
  have hIntegrate (i : PP) :
      integral mu (H i) = b i * max (x - a i) 0 := by
    have hA : 1 <= a i := one_le_dedekindTriangularNorm K i
    have hSet : (Ici (a i)).inter (Icc (1 : Real) x) = Icc (a i) x := by
      ext t
      constructor
      case mp =>
        intro h
        exact And.intro h.1 h.2.2
      case mpr =>
        intro h
        exact And.intro h.1 (And.intro (hA.trans h.1) h.2)
    unfold H
    rw [integral_indicator measurableSet_Ici]
    change integral ((volume.restrict (Icc (1 : Real) x)).restrict (Ici (a i)))
      (fun _ : Real => b i) = _
    rw [Measure.restrict_restrict measurableSet_Ici]
    change integral (volume.restrict ((Ici (a i)).inter (Icc (1 : Real) x)))
      (fun _ : Real => b i) = _
    rw [hSet, integral_const]
    change ((volume.restrict (Icc (a i) x)) univ).toReal * b i = _
    rw [Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal']
    simp [mul_comm, max_comm]
  have hTriangle : triangularCoefficientSum a b x =
      S.sum (fun i => (Ioi (a i)).indicator (fun y => b i * (1 - a i / y)) x) := by
    apply tsum_eq_sum
    intro i hi
    exact indicator_of_notMem (fun h => hi ((hMem i).mpr h.le)) _
  have hWeight (i : PP) :
      x * (Ioi (a i)).indicator (fun y => b i * (1 - a i / y)) x =
        b i * max (x - a i) 0 := by
    by_cases h : a i < x
    case pos =>
      rw [indicator_of_mem (show Membership.mem (Ioi (a i)) x from h), max_eq_left (sub_nonneg.mpr h.le)]
      have hx0 : Not (x = 0) := (zero_lt_one.trans_le hx).ne'
      field_simp [hx0]
    case neg =>
      rw [indicator_of_notMem (show Not (Membership.mem (Ioi (a i)) x) from h),
        max_eq_right (sub_nonpos.mpr (le_of_not_gt h)), mul_zero, mul_zero]
  rw [intervalIntegral.integral_of_le hx, <- integral_Icc_eq_integral_Ioc]
  change integral mu (dedekindChebyshev K) = x * triangularCoefficientSum a b x
  rw [setIntegral_congr_fun measurableSet_Icc he, integral_finsetSum S (fun i _ => hI i),
    hTriangle, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => (hIntegrate i).trans (hWeight i).symm)

private theorem dedekindTriangularRemainder_eq_integratedError (x : Real) (hx : 1 <= x) :
    dedekindTriangularRemainder K x =
      1 / (2 * x) - intervalIntegral (fun t => dedekindChebyshev K t - t) 1 x volume / x := by
  let g := dedekindChebyshevErrorRatio K
  let w := fun t : Real => g t * t ^ (2 : Nat)
  have hg : IntervalIntegrable g volume 1 x := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact dedekindChebyshevErrorRatio_integrableOn_Ioo K x
  have hw : IntervalIntegrable w volume 1 x := by
    apply intervalIntegrable_iff.mpr
    exact (intervalIntegrable_iff.mp hg).mul_continuousOn_of_subset
      (continuous_id.pow _).continuousOn measurableSet_uIoc isCompact_uIcc uIoc_subset_uIcc
  have he : EqOn w (fun t => dedekindChebyshev K t - t) (uIcc 1 x) := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 := (zero_lt_one.trans_le ht.1).ne'
    dsimp only [w, g, dedekindChebyshevErrorRatio]
    exact div_mul_cancel_of_imp (fun h => False.elim ((pow_ne_zero 2 ht0) h))
  have he' : EqOn (dedekindChebyshev K) (fun t => w t + t) (uIcc 1 x) := by
    intro t ht
    change dedekindChebyshev K t = w t + t
    rw [he ht, sub_add_cancel]
  have hid : IntervalIntegrable (fun t : Real => t) volume 1 x :=
    continuous_id.continuousOn.intervalIntegrable
  have hInt : intervalIntegral (dedekindChebyshev K) 1 x volume =
      intervalIntegral (fun t => dedekindChebyshev K t - t) 1 x volume + (x ^ (2 : Nat) - 1) / 2 := by
    rw [intervalIntegral.integral_congr he', intervalIntegral.integral_add hw hid,
      intervalIntegral.integral_congr he, integral_id, one_pow]
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hCoef : triangularCoefficientSum (dedekindTriangularNorm K) (dedekindTriangularCoefficient K) x =
      (intervalIntegral (fun t => dedekindChebyshev K t - t) 1 x volume + (x ^ (2 : Nat) - 1) / 2) / x := by
    apply (eq_div_iff hx0.ne').mpr
    rw [mul_comm]
    exact (dedekindChebyshev_interval_integral K x hx).symm.trans hInt
  unfold dedekindTriangularRemainder triangularRemainder
  rw [hCoef]
  field_simp [hx0.ne']
  ring

private theorem dedekindTriangularRobin_of_integratedChebyshevBound
    {X C : Real} (hX : 1 <= X)
    (hC : forall x : Real, X <= x ->
      -(intervalIntegral (fun t => dedekindChebyshev K t - t) 1 x volume) <= C * x * Real.sqrt x) :
    DedekindTriangularRobin K := by
  refine Exists.intro X (Exists.intro (C + 1) (And.intro hX ?_))
  intro x hx
  have hx1 := hX.trans hx
  have hx0 := zero_lt_one.trans_le hx1
  have hErr : -(intervalIntegral (fun t => dedekindChebyshev K t - t) 1 x volume) / x <=
      C * Real.sqrt x := by
    apply le_of_mul_le_mul_right ?_ hx0
    rw [div_mul_cancel_of_imp (fun h => False.elim (hx0.ne' h))]
    calc
      _ <= C * x * Real.sqrt x := hC x hx
      _ = (C * Real.sqrt x) * x := by ring
  have hSmall : 1 / (2 * x) <= Real.sqrt x :=
    ((div_le_one (by positivity)).mpr (by linarith only [hx1])).trans (Real.one_le_sqrt.mpr hx1)
  rw [dedekindTriangularRemainder_eq_integratedError K x hx1, add_mul, one_mul]
  rw [neg_div] at hErr
  linarith only [hErr, hSmall]

/-- A square-root primitive-tail estimate bounds the integrated
Chebyshev error on the scale x^(3/2). -/
private theorem dedekindIntegratedChebyshev_lower_of_primitiveTail
    {c B X : Real} (hB : 0 <= B) (hX : 1 <= X)
    (hT : forall t : Real, X <= t ->
      abs (primitiveTail (dedekindChebyshevErrorRatio K) c t) <= B / Real.sqrt t) :
    exists C : Real, forall x : Real, X <= x ->
      -(intervalIntegral (fun t => dedekindChebyshev K t - t) 1 x volume) <=
        C * x * Real.sqrt x := by
  let g := dedekindChebyshevErrorRatio K
  let Q := primitiveTail g c
  let f := fun t : Real => Q t * (2 * t)
  let A := abs c + abs (intervalIntegral f 1 X volume)
  refine Exists.intro (3 * B + A) ?_
  intro x hx
  have hx1 := hX.trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hG (y : Real) (hy : 1 <= y) : IntervalIntegrable g volume 1 y := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact dedekindChebyshevErrorRatio_integrableOn_Ioo K y
  have hMatch (t : Real) (ht : 1 <= t) :
      c - intervalIntegral g 1 t volume = Q t := by
    change c - intervalIntegral g 1 t volume = primitiveTail g c t
    rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo,
      primitiveTail, realPrimitiveFromOne]
  have hMatch' : EqOn (fun t => c - intervalIntegral g 1 t volume) Q (uIcc 1 x) := by
    intro t ht
    rw [uIcc_of_le hx1] at ht
    exact hMatch t ht.1
  have hQCont : ContinuousOn Q (uIcc 1 x) := by
    have hP := (hG x hx1).absolutelyContinuousOnInterval_intervalIntegral' left_mem_uIcc
    exact (continuousOn_const.sub hP.continuousOn').congr hMatch'.symm
  have hFCont : ContinuousOn f (uIcc 1 x) :=
    hQCont.mul (continuousOn_const.mul continuousOn_id)
  have hSub (a b : Real) (ha : 1 <= a) (hab : a <= b) (hb : b <= x) :
      Set.Subset (uIcc a b) (uIcc 1 x) := by
    intro z hz
    rw [uIcc_of_le hab] at hz
    rw [uIcc_of_le hx1]
    exact And.intro (ha.trans hz.1) (hz.2.trans hb)
  have hLeft : IntervalIntegrable f volume 1 X :=
    (hFCont.mono (hSub 1 X le_rfl hX hx)).intervalIntegrable
  have hRight : IntervalIntegrable f volume X x :=
    (hFCont.mono (hSub X x hX hx le_rfl)).intervalIntegrable
  have hParts := intervalIntegral_mul_eq_primitiveTail_parts (c := c) (hG x hx1)
    (w := fun t : Real => t ^ (2 : Nat)) (dw := fun t => 2 * t)
    (fun t _ => by
      have hd := (hasDerivAt_id t).pow (2 : Nat)
      change HasDerivAt (fun u : Real => u ^ (2 : Nat)) _ t at hd
      simpa using hd)
    (continuousOn_const.mul continuousOn_id)
  have hEq : EqOn (fun t => g t * t ^ (2 : Nat)) (fun t => dedekindChebyshev K t - t)
      (uIcc 1 x) := by
    intro t ht
    rw [uIcc_of_le hx1] at ht
    have ht0 := (zero_lt_one.trans_le ht.1).ne'
    dsimp only [g, dedekindChebyshevErrorRatio]
    exact div_mul_cancel_of_imp (fun h => False.elim ((pow_ne_zero 2 ht0) h))
  have hPartInt : intervalIntegral (fun t => (c - intervalIntegral g 1 t volume) * (2 * t))
      1 x volume = intervalIntegral f 1 x volume :=
    intervalIntegral.integral_congr (fun t ht => congrArg (fun a : Real => a * (2 * t)) (hMatch' ht))
  have hOne : c - intervalIntegral g 1 1 volume = c := by simp
  dsimp only at hParts
  rw [intervalIntegral.integral_congr hEq, hOne, hMatch x hx1, hPartInt, one_pow, mul_one,
    <- intervalIntegral.integral_add_adjacent_intervals hLeft hRight] at hParts
  have hDiv (t : Real) (ht : 0 < t) : t / Real.sqrt t = Real.sqrt t :=
    (div_eq_iff (Real.sqrt_pos.mpr ht).ne').mpr
      (by simpa only [pow_two] using (Real.sq_sqrt ht.le).symm)
  have hPoint (t : Real) (ht : Membership.mem (Icc X x) t) : -f t <= 2 * B * Real.sqrt x := by
    have ht0 := zero_lt_one.trans_le (hX.trans ht.1)
    calc
      -f t <= abs (f t) := neg_le_abs _
      _ = abs (Q t) * (2 * t) := by
        change abs (Q t * (2 * t)) = _
        rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) ht0.le)]
      _ <= (B / Real.sqrt t) * (2 * t) :=
        mul_le_mul_of_nonneg_right (hT t ht.1) (mul_nonneg (by norm_num) ht0.le)
      _ = (2 * B) * (t / Real.sqrt t) := by ring
      _ <= (2 * B) * Real.sqrt x := by
        rw [hDiv t ht0]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.2) (by positivity)
  have hIntegral := intervalIntegral.integral_mono_on hx hRight.neg intervalIntegrable_const hPoint
  change intervalIntegral (fun t => -f t) X x volume <=
    intervalIntegral (fun _ => 2 * B * Real.sqrt x) X x volume at hIntegral
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const, smul_eq_mul] at hIntegral
  have hWeighted : (x - X) * (2 * B * Real.sqrt x) <= 2 * B * x * Real.sqrt x := by
    calc
      _ <= x * (2 * B * Real.sqrt x) :=
        mul_le_mul_of_nonneg_right (sub_le_self _ (zero_le_one.trans hX)) (by positivity)
      _ = _ := by ring
  have hQAbs : Q x <= B / Real.sqrt x := (le_abs_self _).trans (hT x hx)
  have hQx : Q x * x ^ (2 : Nat) <= B * x * Real.sqrt x := by
    calc
      _ <= B / Real.sqrt x * x ^ (2 : Nat) := mul_le_mul_of_nonneg_right hQAbs (sq_nonneg x)
      _ = (B * x) * (x / Real.sqrt x) := by ring
      _ = _ := by rw [hDiv x hx0]
  have hA : 0 <= A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hGrow : 1 <= x * Real.sqrt x := one_le_mul_of_one_le_of_one_le hx1 (Real.one_le_sqrt.mpr hx1)
  have hA' : A <= A * (x * Real.sqrt x) := le_mul_of_one_le_right hA hGrow
  have h0 : -c - intervalIntegral f 1 X volume <= A := by
    exact sub_le_iff_le_add.mpr (by
      dsimp only [A]
      linarith only [neg_le_abs c, neg_le_abs (intervalIntegral f 1 X volume)])
  nlinarith only [hParts, hIntegral, hWeighted, hQx, hA', h0]


/-- For every number field, Dedekind RH implies the triangular square-root
bound for its actual prime-ideal powers. -/
theorem dedekindTriangularRobin_of_dedekindRH (hRH : DedekindRH K) :
    DedekindTriangularRobin K := by
  choose c B X h using exists_dedekindChebyshevPrimitiveTailBound K hRH
  choose C hC using dedekindIntegratedChebyshev_lower_of_primitiveTail K h.2.1 h.1.le
    h.2.2.2.2
  exact dedekindTriangularRobin_of_integratedChebyshevBound K h.1.le hC

/-- Dedekind RH for a field is equivalent to the triangular bound for its
prime-ideal powers. -/
theorem dedekindRH_iff_dedekindTriangularRobin :
    DedekindRH K <-> DedekindTriangularRobin K :=
  Iff.intro (dedekindTriangularRobin_of_dedekindRH K) (dedekindRH_of_dedekindTriangularRobin K)

/-- The triangular and corrected ideal inequalities are equivalent for
each number field. -/
theorem dedekindTriangularRobin_iff_correctedIdealRobin :
    DedekindTriangularRobin K <-> CorrectedIdealRobin K :=
  (dedekindRH_iff_dedekindTriangularRobin K).symm.trans
    (Iff.intro (correctedIdealRobin_of_dedekindRH K) (dedekindRH_of_correctedIdealRobin K))

end Robin1984.GRH
