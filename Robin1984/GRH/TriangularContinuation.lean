import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.MellinTransform
import Robin1984.GRH.TriangularRemainder

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Cauchy primitives, exponential integration of a logarithmic derivative, and bounds for Mellin transforms of the triangular remainder.
- Formalization note: A uniform square-root bound constructs a holomorphic nonvanishing continuation on the right half-plane without assuming prior continuation of the starting function.
- PROVENANCE-END
-/

/-!
# Continuation from a triangular remainder bound

The Mellin transform of a square-root-bounded triangular remainder gives
the logarithmic derivative of the original function on its initial
half-plane. A normalized primitive on the larger half-plane constructs
the nonvanishing extension by exponentiation.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open Set

/-- An extension of the logarithmic derivative with a primitive gives a
holomorphic nonvanishing extension of the original function. -/
private theorem exists_nonvanishingContinuation_of_logDeriv_primitive
    (alpha sigma : Real) (hAlpha : alpha <= sigma)
    (F H : Complex -> Complex)
    (hExact : Complex.IsExactOn H {z : Complex | alpha < z.re})
    (hF : DifferentiableOn Complex F {z : Complex | sigma < z.re})
    (hNZ : forall z : Complex, sigma < z.re -> Not (F z = 0))
    (hLog : forall z : Complex, sigma < z.re -> logDeriv F z = H z) :
    exists G : Complex -> Complex,
      DifferentiableOn Complex G {z : Complex | alpha < z.re} /\
      (forall z : Complex, alpha < z.re -> Not (G z = 0)) /\
      Set.EqOn G F {z : Complex | sigma < z.re} := by
  let U : Set Complex := {z : Complex | sigma < z.re}
  let z0 : Complex := ((sigma + 1 : Real) : Complex)
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hConnected : IsPreconnected U :=
    (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear sigma).isPreconnected
  have hz0 : Membership.mem U z0 := by
    change sigma < (((sigma + 1 : Real) : Complex)).re
    rw [Complex.ofReal_re]
    exact lt_add_of_pos_right sigma zero_lt_one
  choose A hA using hExact
  let D (z : Complex) := F z / Complex.exp (A z)
  let k : Complex := D z0
  have hD (z : Complex) (hz : Membership.mem U z) : HasDerivAt D 0 z := by
    have hOld : sigma < z.re := hz
    have hNew : alpha < z.re := lt_of_le_of_lt hAlpha hOld
    have hfz := (hF z hz).differentiableAt (hU.mem_nhds hz)
    have he := (Complex.hasDerivAt_exp (A z)).comp z (hA z hNew)
    have hDeriv : deriv F z = H z * F z := by
      apply (div_eq_iff (hNZ z hOld)).mp
      exact hLog z hOld
    have hQuot := hfz.hasDerivAt.div he (Complex.exp_ne_zero (A z))
    simp only [Function.comp_apply] at hQuot
    rw [hDeriv, show H z * F z * Complex.exp (A z) -
        F z * (Complex.exp (A z) * H z) = 0 from by ring, zero_div] at hQuot
    exact hQuot
  have hEqual : Set.EqOn D (fun _ : Complex => k) U := by
    apply hU.eqOn_of_deriv_eq hConnected
      (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
      (differentiableOn_const k)
    next =>
      intro z hz
      rw [(hD z hz).deriv, deriv_const]
    next =>
      exact hz0
    next =>
      rfl
  have hk : Not (k = 0) := div_ne_zero (hNZ z0 hz0) (Complex.exp_ne_zero _)
  let G (z : Complex) := k * Complex.exp (A z)
  refine Exists.intro G (And.intro ?_ (And.intro ?_ ?_))
  next =>
    intro z hz
    exact (((Complex.hasDerivAt_exp (A z)).comp z (hA z hz)).const_mul k).differentiableAt.differentiableWithinAt
  next =>
    intro z hz
    exact mul_ne_zero hk (Complex.exp_ne_zero (A z))
  next =>
    intro z hz
    have hZ := hEqual hz
    exact ((div_eq_iff (Complex.exp_ne_zero (A z))).mp hZ).symm


/-- A holomorphic function on an open right half-plane has a primitive. -/
theorem rightHalfPlane_isExactOn (alpha : Real) (H : Complex -> Complex)
    (hH : DifferentiableOn Complex H {z : Complex | alpha < z.re}) :
    Complex.IsExactOn H {z : Complex | alpha < z.re} := by
  classical
  let U : Set Complex := {z : Complex | alpha < z.re}
  let B (n : Nat) : Set Complex :=
    Metric.ball ((alpha + (n : Real) + 1 : Real) : Complex) ((n : Real) + 1)
  let b : Complex := ((alpha + 1 : Real) : Complex)
  have hOpen (n : Nat) : IsOpen (B n) := Metric.isOpen_ball
  have hBall (n : Nat) : Set.Subset (B n) U := by
    intro z hz
    have hd := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at hd
    have hre := (Complex.abs_re_le_norm
      (z - ((alpha + (n : Real) + 1 : Real) : Complex))).trans_lt hd
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    have hlo := (abs_lt.mp hre).1
    change alpha < z.re
    linarith
  have hBase (n : Nat) : Membership.mem (B n) b := by
    apply Metric.mem_ball.mpr
    dsimp [b, B]
    rw [dist_eq_norm, <- Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [show alpha + 1 - (alpha + (n : Real) + 1) = -(n : Real) by ring,
      abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    linarith
  have hNested (n m : Nat) (hnm : n <= m) : Set.Subset (B n) (B m) := by
    intro z hz
    let c (j : Nat) : Complex := ((alpha + (j : Real) + 1 : Real) : Complex)
    have hnmR : (n : Real) <= (m : Real) := by exact_mod_cast hnm
    have hd : dist (c n) (c m) = (m : Real) - (n : Real) := by
      dsimp [c]
      rw [dist_eq_norm, <- Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos (by linarith)]
      ring
    have hzR : dist z (c n) < (n : Real) + 1 := Metric.mem_ball.mp hz
    apply Metric.mem_ball.mpr
    change dist z (c m) < (m : Real) + 1
    linarith [dist_triangle z (c n) (c m)]
  have hCover (z : Complex) (hz : Membership.mem U z) : exists n : Nat, Membership.mem (B n) z := by
    let x : Real := z.re - alpha
    have hzR : alpha < z.re := hz
    have hx : 0 < x := sub_pos.mpr hzR
    choose n hn using exists_nat_gt ((x ^ 2 + z.im ^ 2) / x)
    refine Exists.intro n (Metric.mem_ball.mpr ?_)
    let d : Complex := z - ((alpha + (n : Real) + 1 : Real) : Complex)
    have hProd : x ^ 2 + z.im ^ 2 < (n : Real) * x := by
      calc
        x ^ 2 + z.im ^ 2 = ((x ^ 2 + z.im ^ 2) / x) * x := by field_simp [ne_of_gt hx]
        _ < (n : Real) * x := mul_lt_mul_of_pos_right hn hx
    have hSquare : norm d ^ 2 = (x - ((n : Real) + 1)) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [d, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, sub_zero]
      dsimp [x]
      ring
    have hRad : 0 < (n : Real) + 1 := by positivity
    have hStrict : norm d ^ 2 < ((n : Real) + 1) ^ 2 := by
      nlinarith [mul_pos hx hRad]
    change dist z (((alpha + (n : Real) + 1 : Real) : Complex)) < (n : Real) + 1
    rw [dist_eq_norm]
    change norm d < (n : Real) + 1
    by_contra! hnlt
    have hSqLe := mul_self_le_mul_self (le_of_lt hRad) hnlt
    nlinarith
  have hPrim (n : Nat) : exists A : Complex -> Complex,
      A b = 0 /\ forall z : Complex, Membership.mem (B n) z -> HasDerivAt A (H z) z :=
    ((hH.mono (hBall n)).isExactOn_ball).with_val_at b 0
  choose A hA using hPrim
  have hAgree (n m : Nat) (hnm : n <= m) : Set.EqOn (A n) (A m) (B n) := by
    have hConvex : Convex Real (B n) := convex_ball _ _
    apply (hOpen n).eqOn_of_deriv_eq hConvex.isPreconnected
      (fun z hz => ((hA n).2 z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => ((hA m).2 z (hNested n m hnm hz)).differentiableAt.differentiableWithinAt)
    next =>
      intro z hz
      rw [((hA n).2 z hz).deriv, ((hA m).2 z (hNested n m hnm hz)).deriv]
    next =>
      exact hBase n
    next =>
      rw [(hA n).1, (hA m).1]
  let P (z : Complex) : Complex :=
    if hz : Membership.mem U z then A (Classical.choose (hCover z hz)) z else 0
  have hLocal (n : Nat) : Set.EqOn (A n) P (B n) := by
    intro z hz
    have hzU := hBall n hz
    let m := Classical.choose (hCover z hzU)
    have hm : Membership.mem (B m) z := Classical.choose_spec (hCover z hzU)
    change A n z = (if hz' : Membership.mem U z then A (Classical.choose (hCover z hz')) z else 0)
    rw [dif_pos hzU]
    exact (hAgree n (max n m) (le_max_left n m) hz).trans
      (hAgree m (max n m) (le_max_right n m) hm).symm
  refine Exists.intro P ?_
  intro z hz
  choose n hn using hCover z hz
  exact ((hA n).2 z hn).congr_of_eventuallyEq
    (Filter.mem_of_superset ((hOpen n).mem_nhds hn) (fun w hw => (hLocal n hw).symm))

/-- Holomorphic continuation of the logarithmic derivative to a right
half-plane gives holomorphic and nonvanishing continuation of the function. -/
theorem exists_nonvanishingContinuation_of_logDeriv
    (alpha sigma : Real) (hAlpha : alpha <= sigma)
    (F H : Complex -> Complex)
    (hH : DifferentiableOn Complex H {z : Complex | alpha < z.re})
    (hF : DifferentiableOn Complex F {z : Complex | sigma < z.re})
    (hNZ : forall z : Complex, sigma < z.re -> Not (F z = 0))
    (hLog : forall z : Complex, sigma < z.re -> logDeriv F z = H z) :
    exists G : Complex -> Complex,
      DifferentiableOn Complex G {z : Complex | alpha < z.re} /\
      (forall z : Complex, alpha < z.re -> Not (G z = 0)) /\
      Set.EqOn G F {z : Complex | sigma < z.re} :=
  exists_nonvanishingContinuation_of_logDeriv_primitive alpha sigma hAlpha F H
    (rightHalfPlane_isExactOn alpha H hH) hF hNZ hLog

open MeasureTheory Filter

private theorem mellin_tail_eq (R : Real -> Complex) (s : Complex) :
    mellin ((Ioi (1 : Real)).indicator R) (-s) =
      integral (volume.restrict (Ioi (1 : Real)))
        (fun x : Real => R x * (x : Complex) ^ (-s - 1)) := by
  let K (x : Real) : Complex := R x * (x : Complex) ^ (-s - 1)
  change integral (volume.restrict (Ioi (0 : Real)))
    (fun x : Real => (x : Complex) ^ (-s - 1) * (Ioi (1 : Real)).indicator R x) = _
  have hPoint : (fun x : Real =>
      (x : Complex) ^ (-s - 1) * (Ioi (1 : Real)).indicator R x) =
      (Ioi (1 : Real)).indicator K := by
    funext x
    by_cases hx : Membership.mem (Ioi (1 : Real)) x
    next =>
      simp [indicator_of_mem hx, K, mul_comm]
    next =>
      simp [indicator_of_notMem hx]
  have hPos : Set.Subset (Ioi (1 : Real)) (Ioi (0 : Real)) :=
    Ioi_subset_Ioi (by norm_num)
  rw [hPoint, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset hPos]

private theorem differentiableOn_squareRootMellin (R : Real -> Complex)
    (hMeas : Measurable R) (C : Real) (hC : 0 <= C)
    (hBound : forall x : Real, 1 < x -> norm (R x) <= C * x ^ (1 / 2 : Real)) :
    DifferentiableOn Complex
      (fun s : Complex => integral (volume.restrict (Ioi (1 : Real)))
        (fun x : Real => R x * (x : Complex) ^ (-s - 1)))
      {s : Complex | 1 / 2 < s.re} := by
  let f : Real -> Complex := (Ioi (1 : Real)).indicator R
  have hMeasF : Measurable f := hMeas.indicator measurableSet_Ioi
  have hMajor : Continuous (fun x : Real => C * x) := continuous_const.mul continuous_id
  have hDom (x : Real) : norm (f x) <= norm (C * x) := by
    by_cases hx : 1 < x
    next =>
      rw [show f x = R x from indicator_of_mem hx R, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hC (by linarith))]
      refine (hBound x hx).trans (mul_le_mul_of_nonneg_left ?_ hC)
      calc
        x ^ (1 / 2 : Real) <= x ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (le_of_lt hx) (by norm_num)
        _ = x := Real.rpow_one x
    next =>
      rw [show f x = 0 from indicator_of_notMem hx R, norm_zero]
      exact norm_nonneg _
  have hLoc : LocallyIntegrableOn f (Ioi (0 : Real)) :=
    (hMajor.continuousOn.locallyIntegrableOn measurableSet_Ioi).mono
      hMeasF.aestronglyMeasurable
      (Filter.Eventually.of_forall hDom)
  have hTop : Asymptotics.IsBigO Filter.atTop f (fun x : Real => x ^ (1 / 2 : Real)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    rw [show f x = R x from indicator_of_mem hx R, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact hBound x hx
  have hBot (b : Real) : Asymptotics.IsBigO (nhdsWithin (0 : Real) (Ioi 0))
      f (fun x : Real => x ^ (-b)) := by
    apply Asymptotics.IsBigO.of_bound 0
    have hNear : Membership.mem (nhdsWithin (0 : Real) (Ioi 0)) (Iio (1 : Real)) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [hNear] with x hx
    have hx' : Not (Membership.mem (Ioi (1 : Real)) x) := by
      change Not (1 < x)
      exact not_lt_of_ge (le_of_lt (show x < 1 from hx))
    rw [show f x = 0 from indicator_of_notMem hx' R, norm_zero, zero_mul]
  have hEq : (fun s : Complex => mellin f (-s)) =
      (fun s : Complex => integral (volume.restrict (Ioi (1 : Real)))
        (fun x : Real => R x * (x : Complex) ^ (-s - 1))) :=
    funext (mellin_tail_eq R)
  rw [<- hEq]
  intro s hs
  have hsR : (1 / 2 : Real) < s.re := hs
  have hAt : DifferentiableAt Complex (mellin f) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      (a := -(1 / 2 : Real)) (b := (-s).re - 1) hLoc
    next =>
      simpa only [neg_neg] using hTop
    next =>
      rw [Complex.neg_re]
      linarith
    next =>
      exact hBot _
    next =>
      linarith
  exact (hAt.comp s (differentiableAt_id.neg)).differentiableWithinAt

/-- A square-root bound on the triangular prime-power remainder constructs
a holomorphic, nonvanishing extension to the right of the critical line.
The starting function has the logarithmic derivative with the stated pole
correction on the original absolute-convergence half-plane. -/
theorem exists_nonvanishingContinuation_of_complexTriangularRemainder
    {i : Type*} [Countable i] (a : i -> Real) (b : i -> Complex)
    (m sigma : Real) (hSigma : 1 <= sigma) (F : Complex -> Complex)
    (ha : forall j, 1 <= a j)
    (hF : DifferentiableOn Complex F {s : Complex | sigma < s.re})
    (hNZ : forall s : Complex, sigma < s.re -> Not (F s = 0))
    (hSum : forall s : Complex, sigma < s.re ->
      Summable (fun j => norm (b j) * (a j) ^ (-s.re)))
    (hEuler : forall s : Complex, sigma < s.re ->
      logDeriv F s = (m : Complex) / (s - 1) -
        tsum (fun j => b j * (a j : Complex) ^ (-s)))
    (C : Real) (hC : 0 <= C)
    (hR : forall x : Real, 1 < x ->
      norm (complexTriangularRemainder a b m x) <= C * x ^ (1 / 2 : Real)) :
    exists G : Complex -> Complex,
      DifferentiableOn Complex G {s : Complex | 1 / 2 < s.re} /\
      (forall s : Complex, 1 / 2 < s.re -> Not (G s = 0)) /\
      Set.EqOn G F {s : Complex | sigma < s.re} := by
  let M (s : Complex) : Complex := integral (volume.restrict (Ioi (1 : Real)))
    (fun x : Real => complexTriangularRemainder a b m x * (x : Complex) ^ (-s - 1))
  let H (s : Complex) : Complex := s * (s + 1) * M s - (m : Complex) / 2 * (s + 2)
  have hM : DifferentiableOn Complex M {s : Complex | 1 / 2 < s.re} :=
    differentiableOn_squareRootMellin _ (measurable_complexTriangularRemainder a b m) C hC hR
  have hH : DifferentiableOn Complex H {s : Complex | 1 / 2 < s.re} := by
    dsimp [H]
    exact ((differentiableOn_id.mul (differentiableOn_id.add
      (differentiableOn_const 1))).mul hM).sub
      ((differentiableOn_const _).mul (differentiableOn_id.add (differentiableOn_const 2)))
  refine exists_nonvanishingContinuation_of_logDeriv (1 / 2) sigma
    (by linarith) F H hH hF hNZ ?_
  intro s hs
  have hs1 := lt_of_le_of_lt hSigma hs
  have hEq := (complexTriangularRemainder_mellin_of_logDeriv
    a b m F ha s hs1 (hSum s hs) (hEuler s hs)).2
  have h0 : Not (s = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs1)
  have h1 : Not (s + 1 = 0) := Complex.ne_zero_of_re_pos (by
    rw [Complex.add_re, Complex.one_re]
    linarith)
  change logDeriv F s = s * (s + 1) * M s - (m : Complex) / 2 * (s + 2)
  change M s = _ at hEq
  rw [hEq]
  field_simp [h0, h1]
  ring

end Robin1984.GRH
