import Robin1984.NicolasLandau.NicolasLandauPositiveTail
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# Nicolas-Landau compact continuation block

This module proves the analytic continuation of the remaining parameter block
`0 < u <= 1`.  The noncompact block `u > 1` is already analytic in the
imported module.
-/

namespace Robin1984

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def nicolasFilledOneRadius : Real :=
  Classical.choose
    exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one

theorem nicolasFilledOneRadius_pos : 0 < nicolasFilledOneRadius :=
  (Classical.choose_spec
    exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one).1

theorem nicolasFilledOneRadius_analytic
    {s : Complex}
    (hs : Membership.mem
      (Metric.ball (1 : Complex) nicolasFilledOneRadius) s) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s :=
  (Classical.choose_spec
    exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one).2 s hs

def nicolasCompactZRadius : Real :=
  min (nicolasFilledOneRadius / 16) (1 / 64)

theorem nicolasCompactZRadius_pos : 0 < nicolasCompactZRadius := by
  unfold nicolasCompactZRadius
  exact lt_min (div_pos nicolasFilledOneRadius_pos (by norm_num))
    (by norm_num)

theorem nicolasCompactZRadius_le_oneRadius_div_sixteen :
    nicolasCompactZRadius <= nicolasFilledOneRadius / 16 := by
  unfold nicolasCompactZRadius
  exact min_le_left _ _

theorem nicolasCompactZRadius_le_one_sixty_four :
    nicolasCompactZRadius <= 1 / 64 := by
  unfold nicolasCompactZRadius
  exact min_le_right _ _

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_compact_base
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled
      (((u + 1 : Real) : Complex)) := by
  by_cases huZero : u = 0
  case pos =>
    subst u
    simpa using nicolasPsiMellinTailContinuationFilled_analyticAt_one
  case neg =>
    apply nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re
    simp only [Complex.ofReal_re]
    have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm huZero)
    linarith

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_compact_shift
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : norm z < 4 * nicolasCompactZRadius) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled
      (((u + 1 : Real) : Complex) - z) := by
  have hRadius := nicolasFilledOneRadius_pos
  have hFourRadius :
      4 * nicolasCompactZRadius <= nicolasFilledOneRadius / 4 := by
    calc
      4 * nicolasCompactZRadius <=
          4 * (nicolasFilledOneRadius / 16) :=
        mul_le_mul_of_nonneg_left
          nicolasCompactZRadius_le_oneRadius_div_sixteen (by norm_num)
      _ = nicolasFilledOneRadius / 4 := by ring
  have hzRadius : norm z < nicolasFilledOneRadius / 4 :=
    hz.trans_le hFourRadius
  by_cases huSmall : u < nicolasFilledOneRadius / 2
  case pos =>
    apply nicolasFilledOneRadius_analytic
    rw [Metric.mem_ball, dist_eq_norm]
    have hDifference :
        (((u + 1 : Real) : Complex) - z) - (1 : Complex) =
          (u : Complex) - z := by
      push_cast
      ring
    rw [hDifference]
    calc
      norm ((u : Complex) - z) <= norm (u : Complex) + norm z :=
        norm_sub_le _ _
      _ = u + norm z := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
      _ < nicolasFilledOneRadius / 2 +
          nicolasFilledOneRadius / 4 := add_lt_add huSmall hzRadius
      _ < nicolasFilledOneRadius := by linarith
  case neg =>
    apply nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re
    have hzRe : z.re <= norm z := Complex.re_le_norm z
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith

theorem nicolasJShiftNumeratorFilled_analyticAt_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : norm z < 4 * nicolasCompactZRadius) :
    AnalyticAt Complex (nicolasJShiftNumeratorFilled u) z := by
  let s : Complex := ((u + 1 : Real) : Complex)
  have hTailShift : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled (s - z) := by
    dsimp [s]
    exact nicolasPsiMellinTailContinuationFilled_analyticAt_compact_shift
      hu hz
  have hAffine : AnalyticAt Complex (fun w : Complex => s - w) z :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s - w)) z := by
    have hComp := hTailShift.comp_of_eq hAffine rfl
    apply hComp.congr
    exact Eventually.of_forall (fun _ => rfl)
  have hPowerDifferentiable : Differentiable Complex
      (fun w : Complex => (3 : Complex) ^ w) := by
    intro w
    exact DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (by norm_num))
  have hPower : AnalyticAt Complex
      (fun w : Complex => (3 : Complex) ^ w) z :=
    hPowerDifferentiable.analyticAt z
  have hTailBase : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s := by
    dsimp [s]
    exact nicolasPsiMellinTailContinuationFilled_analyticAt_compact_base hu
  have hTailConst : AnalyticAt Complex (fun _ : Complex =>
      nicolasPsiMellinTailContinuationFilled s) z := analyticAt_const
  unfold nicolasJShiftNumeratorFilled
  change AnalyticAt Complex (fun w : Complex =>
    nicolasPsiMellinTailContinuationFilled (s - w) -
      (3 : Complex) ^ w * nicolasPsiMellinTailContinuationFilled s) z
  exact hShift.sub (hPower.mul hTailConst)

def nicolasCompactNumeratorDomain : Set (Prod Real Complex) :=
  Set.prod (Icc (0 : Real) 1)
    (Metric.closedBall (0 : Complex) (3 * nicolasCompactZRadius))

theorem nicolasJShiftNumeratorFilled_continuousOn_compact :
    ContinuousOn (fun p : Prod Real Complex =>
      nicolasJShiftNumeratorFilled p.1 p.2)
      nicolasCompactNumeratorDomain := by
  intro p hp
  have hu : Membership.mem (Icc (0 : Real) 1) p.1 := hp.1
  have hzClosed : Membership.mem
      (Metric.closedBall (0 : Complex) (3 * nicolasCompactZRadius)) p.2 :=
    hp.2
  have hzNorm : norm p.2 <= 3 * nicolasCompactZRadius := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hzClosed
  have hzStrict : norm p.2 < 4 * nicolasCompactZRadius := by
    have hRadius := nicolasCompactZRadius_pos
    linarith
  let s0 : Prod Real Complex -> Complex := fun q =>
    (((q.1 + 1 : Real) : Complex))
  let s1 : Prod Real Complex -> Complex := fun q => s0 q - q.2
  have hs0Continuous : ContinuousAt s0 p := by
    dsimp [s0]
    fun_prop
  have hs1Continuous : ContinuousAt s1 p := by
    dsimp [s1]
    exact hs0Continuous.sub continuousAt_snd
  have hTailBase : ContinuousAt
      (fun q : Prod Real Complex =>
        nicolasPsiMellinTailContinuationFilled (s0 q)) p := by
    exact
      (nicolasPsiMellinTailContinuationFilled_analyticAt_compact_base hu).continuousAt.comp_of_eq
        hs0Continuous rfl
  have hTailShift : ContinuousAt
      (fun q : Prod Real Complex =>
        nicolasPsiMellinTailContinuationFilled (s1 q)) p := by
    exact
      (nicolasPsiMellinTailContinuationFilled_analyticAt_compact_shift
        hu hzStrict).continuousAt.comp_of_eq hs1Continuous rfl
  have hPower : ContinuousAt
      (fun q : Prod Real Complex => (3 : Complex) ^ q.2) p := by
    exact continuousAt_snd.const_cpow (Or.inl (by norm_num))
  unfold nicolasJShiftNumeratorFilled
  change ContinuousWithinAt (fun q : Prod Real Complex =>
    nicolasPsiMellinTailContinuationFilled (s1 q) -
      (3 : Complex) ^ q.2 *
        nicolasPsiMellinTailContinuationFilled (s0 q))
    nicolasCompactNumeratorDomain p
  exact (hTailShift.sub (hPower.mul hTailBase)).continuousWithinAt

theorem nicolasCompactNumeratorDomain_isCompact :
    IsCompact nicolasCompactNumeratorDomain := by
  unfold nicolasCompactNumeratorDomain
  exact isCompact_Icc.prod (isCompact_closedBall _ _)

theorem exists_nicolasCompactNumeratorBound :
    Exists fun C : Real =>
      forall u : Real,
        Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem
            (Metric.closedBall (0 : Complex)
              (3 * nicolasCompactZRadius)) z ->
          norm (nicolasJShiftNumeratorFilled u z) <= C := by
  let f : Prod Real Complex -> Real := fun p =>
    norm (nicolasJShiftNumeratorFilled p.1 p.2)
  have hf : ContinuousOn f nicolasCompactNumeratorDomain := by
    dsimp [f]
    exact nicolasJShiftNumeratorFilled_continuousOn_compact.norm
  have hBound : BddAbove (f '' nicolasCompactNumeratorDomain) :=
    nicolasCompactNumeratorDomain_isCompact.bddAbove_image
      hf
  choose C hC using hBound
  refine Exists.intro C ?_
  intro u hu z hz
  have hMember : Membership.mem (f '' nicolasCompactNumeratorDomain)
      (f (u, z)) := by
    apply mem_image_of_mem
    change And
      (Membership.mem (Icc (0 : Real) 1) u)
      (Membership.mem
        (Metric.closedBall (0 : Complex) (3 * nicolasCompactZRadius)) z)
    exact And.intro hu hz
  have hValue := hC hMember
  dsimp [f] at hValue
  exact hValue

def nicolasCompactNumeratorBound : Real :=
  max (Classical.choose exists_nicolasCompactNumeratorBound) 0

theorem nicolasCompactNumeratorBound_nonneg :
    0 <= nicolasCompactNumeratorBound := by
  unfold nicolasCompactNumeratorBound
  exact le_max_right _ _

theorem norm_nicolasJShiftNumeratorFilled_le_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      nicolasCompactNumeratorBound := by
  have hChosen :=
    (Classical.choose_spec exists_nicolasCompactNumeratorBound) u hu z hz
  exact hChosen.trans (le_max_left _ _)

theorem nicolasJShiftNumeratorFilled_differentiableOn_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u) :
    DifferentiableOn Complex (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) := by
  intro z hz
  have hzNorm : norm z < 3 * nicolasCompactZRadius := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzFour : norm z < 4 * nicolasCompactZRadius := by
    have hRadius := nicolasCompactZRadius_pos
    linarith
  exact
    (nicolasJShiftNumeratorFilled_analyticAt_compact hu hzFour).differentiableAt.differentiableWithinAt

theorem norm_nicolasJMellinShiftIntegrandFilled_le_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      2 * (nicolasCompactNumeratorBound /
        (3 * nicolasCompactZRadius)) := by
  let R : Real := 3 * nicolasCompactZRadius
  let M : Real := nicolasCompactNumeratorBound
  have hRPos : 0 < R := by
    dsimp [R]
    exact mul_pos (by norm_num) nicolasCompactZRadius_pos
  have hMNonneg : 0 <= M := by
    dsimp [M]
    exact nicolasCompactNumeratorBound_nonneg
  have hMaps : MapsTo (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) R)
      (Metric.closedBall (nicolasJShiftNumeratorFilled u 0) M) := by
    intro w hw
    rw [nicolasJShiftNumeratorFilled_zero]
    rw [Metric.mem_closedBall, dist_zero_right]
    apply norm_nicolasJShiftNumeratorFilled_le_compact hu
    exact Metric.ball_subset_closedBall hw
  have hDslope := Complex.norm_dslope_le_div_of_mapsTo_ball
    (nicolasJShiftNumeratorFilled_differentiableOn_compact hu)
    hMaps hz
  have huOnePos : 0 < u + 1 := by linarith [hu.1]
  have huOneLe : u + 1 <= 2 := by linarith [hu.2]
  have hQuotientNonneg : 0 <= M / R := div_nonneg hMNonneg hRPos.le
  unfold nicolasJMellinShiftIntegrandFilled
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huOnePos]
  calc
    (u + 1) * norm (dslope (nicolasJShiftNumeratorFilled u) 0 z) <=
        (u + 1) * (M / R) :=
      mul_le_mul_of_nonneg_left hDslope huOnePos.le
    _ <= 2 * (M / R) :=
      mul_le_mul_of_nonneg_right huOneLe hQuotientNonneg
    _ = 2 * (nicolasCompactNumeratorBound /
        (3 * nicolasCompactZRadius)) := by
      dsimp [M, R]

def nicolasCompactIntegrandBound : Real :=
  2 * (nicolasCompactNumeratorBound /
    (3 * nicolasCompactZRadius))


theorem nicolasJMellinShiftIntegrandFilled_differentiableOn_compact
    {u : Real} (hu : Membership.mem (Ioc (0 : Real) 1) u) :
    DifferentiableOn Complex
      (fun z : Complex => nicolasJMellinShiftIntegrandFilled z u)
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) := by
  have huClosed : Membership.mem (Icc (0 : Real) 1) u :=
    And.intro hu.1.le hu.2
  intro z hz
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      hu.1).differentiableAt.differentiableWithinAt
  case neg =>
    have hNumeratorAt : DifferentiableAt Complex
        (nicolasJShiftNumeratorFilled u) z :=
      (nicolasJShiftNumeratorFilled_differentiableOn_compact
        huClosed z hz).differentiableAt
          (Metric.isOpen_ball.mem_nhds hz)
    have hDslopeAt : DifferentiableAt Complex
        (dslope (nicolasJShiftNumeratorFilled u) 0) z :=
      (differentiableAt_dslope_of_ne hzZero).2 hNumeratorAt
    unfold nicolasJMellinShiftIntegrandFilled
    exact (analyticAt_const.differentiableAt.mul hDslopeAt).differentiableWithinAt

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le_compact
    {u : Real} (hu : Membership.mem (Ioc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <=
      (2 * nicolasCompactIntegrandBound) /
        nicolasCompactZRadius := by
  let f : Complex -> Complex := fun w : Complex =>
    nicolasJMellinShiftIntegrandFilled w u
  let R : Real := nicolasCompactZRadius
  let M : Real := nicolasCompactIntegrandBound
  have hRPos : 0 < R := by
    dsimp [R]
    exact nicolasCompactZRadius_pos
  have hSmallSubset : Metric.ball z R <=
      Metric.ball (0 : Complex) (3 * R) := by
    intro w hw
    rw [Metric.mem_ball] at hw hz
    rw [Metric.mem_ball]
    calc
      dist w 0 <= dist w z + dist z 0 := dist_triangle w z 0
      _ < R + R := add_lt_add hw hz
      _ < 3 * R := by linarith
  have hzLarge : Membership.mem
      (Metric.ball (0 : Complex) (3 * R)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self hRPos
  have hDiff : DifferentiableOn Complex f (Metric.ball z R) :=
    (nicolasJMellinShiftIntegrandFilled_differentiableOn_compact hu).mono
      hSmallSubset
  have hMaps : MapsTo f (Metric.ball z R)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwLarge := hSmallSubset hw
    have hwBound : norm (f w) <= M := by
      dsimp [f, M, R] at hwLarge
      dsimp [f, M]
      simpa [nicolasCompactIntegrandBound] using
        norm_nicolasJMellinShiftIntegrandFilled_le_compact
          (And.intro hu.1.le hu.2) hwLarge
    have hzBound : norm (f z) <= M := by
      dsimp [f, M, R] at hzLarge
      dsimp [f, M]
      simpa [nicolasCompactIntegrandBound] using
        norm_nicolasJMellinShiftIntegrandFilled_le_compact
          (And.intro hu.1.le hu.2) hzLarge
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps hRPos
  change norm (deriv f z) <= (2 * M) / R
  exact hCauchy

theorem nicolasJShiftNumeratorFilled_continuousOn_compact_u
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z) :
    ContinuousOn (fun u : Real => nicolasJShiftNumeratorFilled u z)
      (Icc (0 : Real) 1) := by
  intro u hu
  have hJoint :=
    nicolasJShiftNumeratorFilled_continuousOn_compact (u, z)
      (And.intro hu hz)
  have hPair : ContinuousWithinAt (fun v : Real => (v, z))
      (Icc (0 : Real) 1) u :=
    (continuousAt_id.prodMk continuousAt_const).continuousWithinAt
  have hMaps : MapsTo (fun v : Real => (v, z))
      (Icc (0 : Real) 1) nicolasCompactNumeratorDomain := by
    intro v hv
    exact And.intro hv hz
  have hComp := ContinuousWithinAt.comp
    (f := fun v : Real => (v, z))
    (g := fun p : Prod Real Complex =>
      nicolasJShiftNumeratorFilled p.1 p.2)
    hJoint hPair hMaps
  simpa [Function.comp_def] using hComp

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_compact_u_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z)
    (hzZero : Not (z = 0)) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (Icc (0 : Real) 1) := by
  have hZeroMem : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) (0 : Complex) := by
    rw [Metric.mem_closedBall, dist_self]
    exact (mul_pos (by norm_num) nicolasCompactZRadius_pos).le
  have hNumeratorZ :=
    nicolasJShiftNumeratorFilled_continuousOn_compact_u hz
  have hNumeratorZero :=
    nicolasJShiftNumeratorFilled_continuousOn_compact_u hZeroMem
  have hU : Continuous (fun u : Real => ((u + 1 : Real) : Complex)) := by
    fun_prop
  have hInv : Continuous (fun _ : Real => Inv.inv (z - 0)) :=
    continuous_const
  have hEq : (fun u : Real => nicolasJMellinShiftIntegrandFilled z u) =
      (fun u : Real => ((u + 1 : Real) : Complex) *
        Inv.inv (z - 0) *
          (nicolasJShiftNumeratorFilled u z -
            nicolasJShiftNumeratorFilled u 0)) := by
    funext u
    unfold nicolasJMellinShiftIntegrandFilled
    rw [dslope_of_ne _ hzZero]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    ring
  rw [hEq]
  exact (hU.continuousOn.mul hInv.continuousOn).mul
    (hNumeratorZ.sub hNumeratorZero)

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z)
    (hzZero : Not (z = 0)) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  have hContinuous :=
    nicolasJMellinShiftIntegrandFilled_continuousOn_compact_u_of_ne
      hz hzZero
  have hSubset : Ioc (0 : Real) 1 <= Icc (0 : Real) 1 := by
    intro u hu
    exact And.intro hu.1.le hu.2
  exact (hContinuous.mono hSubset).aestronglyMeasurable measurableSet_Ioc

def nicolasCompactDerivativeStep (n : Nat) : Complex :=
  (((nicolasCompactZRadius / 2) *
    ((1 : Real) / ((n : Real) + 1)) : Real) : Complex)

theorem nicolasCompactDerivativeStep_ne_zero (n : Nat) :
    Not (nicolasCompactDerivativeStep n = 0) := by
  unfold nicolasCompactDerivativeStep
  apply Complex.ofReal_ne_zero.mpr
  exact mul_ne_zero
    (div_ne_zero (ne_of_gt nicolasCompactZRadius_pos) (by norm_num))
    (div_ne_zero (by norm_num) (by positivity))

theorem norm_nicolasCompactDerivativeStep_lt (n : Nat) :
    norm (nicolasCompactDerivativeStep n) < nicolasCompactZRadius := by
  have hRadius := nicolasCompactZRadius_pos
  have hRecipPos : 0 < (1 : Real) / ((n : Real) + 1) := by
    positivity
  have hRecipLe : (1 : Real) / ((n : Real) + 1) <= 1 := by
    apply (div_le_one (by positivity)).2
    norm_num
  unfold nicolasCompactDerivativeStep
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (div_pos hRadius (by norm_num)) hRecipPos)]
  calc
    nicolasCompactZRadius / 2 * ((1 : Real) / ((n : Real) + 1)) <=
        nicolasCompactZRadius / 2 * 1 :=
      mul_le_mul_of_nonneg_left hRecipLe
        (div_nonneg hRadius.le (by norm_num))
    _ < nicolasCompactZRadius := by linarith

theorem nicolasCompactDerivativeStep_tendsto_zero :
    Tendsto nicolasCompactDerivativeStep atTop (nhds (0 : Complex)) := by
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (nicolasCompactZRadius / 2) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((nicolasCompactZRadius / 2) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hScaled
  have hFunctions :
      Function.comp Complex.ofReal (fun n : Nat =>
        (nicolasCompactZRadius / 2) *
          ((1 : Real) / ((n : Real) + 1))) =
        nicolasCompactDerivativeStep := by
    funext n
    rfl
  have hTarget : Tendsto
      (Function.comp Complex.ofReal (fun n : Nat =>
        (nicolasCompactZRadius / 2) *
          ((1 : Real) / ((n : Real) + 1))))
      atTop (nhds (0 : Complex)) := by
    simpa using hCast
  rw [hFunctions] at hTarget
  exact hTarget

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_zero :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled 0 u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  have hZMem : forall n : Nat,
      Membership.mem
        (Metric.closedBall (0 : Complex)
          (3 * nicolasCompactZRadius))
        (nicolasCompactDerivativeStep n) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have hStep := norm_nicolasCompactDerivativeStep_lt n
    have hRadius := nicolasCompactZRadius_pos
    linarith
  have hMeas : forall n : Nat, AEMeasurable
      (fun u : Real => nicolasJMellinShiftIntegrandFilled
        (nicolasCompactDerivativeStep n) u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    intro n
    exact
      (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_of_ne
        (hZMem n) (nicolasCompactDerivativeStep_ne_zero n)).aemeasurable
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto
        (fun n : Nat => nicolasJMellinShiftIntegrandFilled
          (nicolasCompactDerivativeStep n) u)
        atTop (nhds (nicolasJMellinShiftIntegrandFilled 0 u)))
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      hu.1).continuousAt.tendsto.comp
        nicolasCompactDerivativeStep_tendsto_zero
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_zero
  case neg =>
    exact
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_of_ne
        hz hzZero

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_compact
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioc (0 : Real) 1) := by
  have hMajorant : IntegrableOn
      (fun _ : Real => nicolasCompactIntegrandBound)
      (Ioc (0 : Real) 1) := integrableOn_const measure_Ioc_lt_top.ne
  apply Integrable.mono' hMajorant
    (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
      (Metric.ball_subset_closedBall hz))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  simpa [nicolasCompactIntegrandBound] using
    norm_nicolasJMellinShiftIntegrandFilled_le_compact
      (And.intro hu.1.le hu.2) hz

def nicolasCompactDerivativeMajorant : Real :=
  (2 * nicolasCompactIntegrandBound) /
    nicolasCompactZRadius


theorem nicolasCompactDerivativeMajorant_integrableOn :
    IntegrableOn (fun _ : Real => nicolasCompactDerivativeMajorant)
      (Ioc (0 : Real) 1) :=
  integrableOn_const measure_Ioc_lt_top.ne

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasCompactDerivativeStep n)
  have hzNorm : norm z < nicolasCompactZRadius := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzLarge : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hRadius := nicolasCompactZRadius_pos
    linarith
  have hShiftLarge : forall n : Nat,
      Membership.mem
        (Metric.closedBall (0 : Complex)
          (3 * nicolasCompactZRadius))
        (z + nicolasCompactDerivativeStep n) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (calc
        norm (z + nicolasCompactDerivativeStep n) <=
            norm z + norm (nicolasCompactDerivativeStep n) := norm_add_le _ _
        _ < nicolasCompactZRadius + nicolasCompactZRadius :=
          add_lt_add hzNorm (norm_nicolasCompactDerivativeStep_lt n)
        _ < 3 * nicolasCompactZRadius := by
          linarith [nicolasCompactZRadius_pos]).le
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    intro n
    have hShift :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
        (hShiftLarge n)
    have hBase :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
        hzLarge
    have hEq : slopeSeq n = fun u : Real =>
        Inv.inv ((z + nicolasCompactDerivativeStep n) - z) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasCompactDerivativeStep n) u -
            nicolasJMellinShiftIntegrandFilled z u) := by
      funext u
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub]
    rw [hEq]
    exact ((hShift.sub hBase).const_mul
      (Inv.inv ((z + nicolasCompactDerivativeStep n) - z))).aemeasurable
  have hStepWithin : Tendsto nicolasCompactDerivativeStep atTop
      (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro nicolasCompactDerivativeStep_tendsto_zero
      (Eventually.of_forall (fun n : Nat =>
        Set.mem_compl_singleton_iff.mpr
          (nicolasCompactDerivativeStep_ne_zero n)))
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
        (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)))
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hzLargeBall : Membership.mem
        (Metric.ball (0 : Complex)
          (3 * nicolasCompactZRadius)) z := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith [nicolasCompactZRadius_pos]
    have hDiffAt : DifferentiableAt Complex
        (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) z :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_compact
        hu z hzLargeBall).differentiableAt
          (Metric.isOpen_ball.mem_nhds hzLargeBall)
    have hSlope := hDiffAt.hasDerivAt.tendsto_slope_zero.comp hStepWithin
    change Tendsto (fun n : Nat =>
      Inv.inv (nicolasCompactDerivativeStep n) *
        (nicolasJMellinShiftIntegrandFilled
            (z + nicolasCompactDerivativeStep n) u -
          nicolasJMellinShiftIntegrandFilled z u))
      atTop (nhds (deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
    dsimp [slopeSeq]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
    exact hSlope
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

def nicolasJShiftedComplexContinuationFilledCompact (z : Complex) : Complex :=
  integral (volume.restrict (Ioc (0 : Real) 1))
    (nicolasJMellinShiftIntegrandFilled z)

theorem nicolasJShiftedComplexContinuationFilledCompact_hasDerivAt
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    HasDerivAt nicolasJShiftedComplexContinuationFilledCompact
      (integral (volume.restrict (Ioc (0 : Real) 1)) (fun u : Real =>
        deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) z := by
  let s : Set Complex :=
    Metric.ball (0 : Complex) nicolasCompactZRadius
  let F : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    nicolasJMellinShiftIntegrandFilled w u
  let F' : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
  have hsNhd : Membership.mem (nhds z) s := by
    dsimp [s]
    exact Metric.isOpen_ball.mem_nhds hz
  have hFMeas : Filter.Eventually
      (fun w : Complex => AEStronglyMeasurable (F w)
        (volume.restrict (Ioc (0 : Real) 1))) (nhds z) := by
    filter_upwards [hsNhd] with w hw
    have hwLarge : Membership.mem
        (Metric.closedBall (0 : Complex)
          (3 * nicolasCompactZRadius)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith [nicolasCompactZRadius_pos]
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
      hwLarge
  have hzLarge : Membership.mem
      (Metric.ball (0 : Complex)
        (3 * nicolasCompactZRadius)) z := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith [nicolasCompactZRadius_pos]
  have hFInt : Integrable (F z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    exact nicolasJMellinShiftIntegrandFilled_integrableOn_compact hzLarge
  have hF'Meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    exact deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
      hz
  have hBound : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        norm (F' w u) <= nicolasCompactDerivativeMajorant)
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    intro w hw
    dsimp [F', s] at hw
    dsimp [F']
    unfold nicolasCompactDerivativeMajorant
    exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le_compact hu hw
  have hDiff : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        HasDerivAt (fun v : Complex => F v u) (F' w u) w)
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    intro w hw
    have hwLarge : Membership.mem
        (Metric.ball (0 : Complex)
          (3 * nicolasCompactZRadius)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith [nicolasCompactZRadius_pos]
    have hAt : DifferentiableAt Complex
        (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_compact
        hu w hwLarge).differentiableAt
          (Metric.isOpen_ball.mem_nhds hwLarge)
    dsimp [F, F']
    exact hAt.hasDerivAt
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F')
    (bound := fun _ : Real => nicolasCompactDerivativeMajorant)
    hsNhd hFMeas hFInt hF'Meas hBound
    nicolasCompactDerivativeMajorant_integrableOn hDiff
  unfold nicolasJShiftedComplexContinuationFilledCompact
  simpa [F, F'] using hMain.2

theorem nicolasJShiftedComplexContinuationFilledCompact_differentiableOn :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilledCompact
      (Metric.ball (0 : Complex) nicolasCompactZRadius) := by
  intro z hz
  exact
    (nicolasJShiftedComplexContinuationFilledCompact_hasDerivAt
      hz).differentiableAt.differentiableWithinAt


theorem nicolasJShiftedComplexContinuationFilled_eq_compact_add_large
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    nicolasJShiftedComplexContinuationFilled z =
      nicolasJShiftedComplexContinuationFilledCompact z +
        nicolasJShiftedComplexContinuationFilledLarge z := by
  have hzNorm : norm z < nicolasCompactZRadius := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzCompact : Membership.mem
      (Metric.ball (0 : Complex)
        (3 * nicolasCompactZRadius)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [nicolasCompactZRadius_pos]
  have hzLarge : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    have hRadiusBound := nicolasCompactZRadius_le_one_sixty_four
    linarith
  have hCompactInt :=
    nicolasJMellinShiftIntegrandFilled_integrableOn_compact hzCompact
  have hLargeInt :=
    nicolasJMellinShiftIntegrandFilled_integrableOn_large hzLarge
  unfold nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedComplexContinuationFilledCompact
    nicolasJShiftedComplexContinuationFilledLarge
  rw [<- Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) <= 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hCompactInt
  . exact hLargeInt

theorem nicolasJShiftedComplexContinuationFilled_differentiableOn_compactRadius :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilled
      (Metric.ball (0 : Complex) nicolasCompactZRadius) := by
  have hLargeSubset : Metric.ball (0 : Complex) nicolasCompactZRadius <=
      Metric.ball (0 : Complex) (1 / 8 : Real) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have hRadiusBound := nicolasCompactZRadius_le_one_sixty_four
    linarith
  have hSum : DifferentiableOn Complex
      (fun z : Complex =>
        nicolasJShiftedComplexContinuationFilledCompact z +
          nicolasJShiftedComplexContinuationFilledLarge z)
      (Metric.ball (0 : Complex) nicolasCompactZRadius) :=
    nicolasJShiftedComplexContinuationFilledCompact_differentiableOn.add
      (nicolasJShiftedComplexContinuationFilledLarge_differentiableOn.mono
        hLargeSubset)
  exact hSum.congr (fun z hz =>
    nicolasJShiftedComplexContinuationFilled_eq_compact_add_large hz)

theorem nicolasJShiftedComplexContinuationFilled_analyticAt_zero :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilled 0 := by
  apply
    nicolasJShiftedComplexContinuationFilled_differentiableOn_compactRadius.analyticAt
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self nicolasCompactZRadius_pos)

def nicolasJComplexMellinStartup (X : Real) (s : Complex) : Complex :=
  integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
    (x : Complex) ^ (s - 1) * (nicolasJ x : Complex))

theorem nicolasJComplexMellinStartup_differentiableAt
    {X : Real} (hX : 3 <= X) (s0 : Complex) :
    DifferentiableAt Complex (nicolasJComplexMellinStartup X) s0 := by
  let F : Complex -> Real -> Complex := fun s x =>
    (x : Complex) ^ (s - 1) * (nicolasJ x : Complex)
  let F' : Complex -> Real -> Complex := fun s x =>
    ((Real.log x : Real) : Complex) * F s x
  let base : Real -> Complex := fun x =>
    (x : Complex) ^ (-3 : Complex) * (nicolasJ x : Complex)
  let ratio : Complex -> Real -> Complex := fun s x =>
    (x : Complex) ^ (s + 2)
  let majorant : Real -> Real := fun x =>
    norm (base x) * X ^ (abs s0.re + 4)
  have hRealBase : IntegrableOn (fun x : Real =>
      x ^ (-3 : Real) * nicolasJ x) (Ioc (3 : Real) X) := by
    have h := nicolasJ_realMellin_integrableOn_Ioi_three
      (a := (-2 : Real)) (by norm_num)
    have hRestricted := h.mono_set
      (show Ioc (3 : Real) X <= Ioi 3 from Ioc_subset_Ioi_self)
    apply hRestricted.congr_fun
    . intro x hx
      congr 2
      norm_num
    . exact measurableSet_Ioc
  have hCastBase : IntegrableOn (fun x : Real =>
      ((x ^ (-3 : Real) * nicolasJ x : Real) : Complex))
      (Ioc (3 : Real) X) :=
    Complex.ofRealCLM.integrable_comp hRealBase
  have hBaseIntegrable : Integrable base
      (volume.restrict (Ioc (3 : Real) X)) := by
    apply hCastBase.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    dsimp [base]
    rw [show (-3 : Complex) = ((-3 : Real) : Complex) by norm_num,
      <- Complex.ofReal_cpow hxPos.le]
    push_cast
    rfl
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hMajorantIntegrable : Integrable majorant
      (volume.restrict (Ioc (3 : Real) X)) := by
    have h := hBaseIntegrable.norm.const_mul
      (X ^ (abs s0.re + 4))
    simpa [majorant, mul_comm] using h
  have hMeasurable : forall s : Complex, AEStronglyMeasurable (F s)
      (volume.restrict (Ioc (3 : Real) X)) := by
    intro s
    have hRatioContinuous : ContinuousOn (ratio s) (Ioc (3 : Real) X) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      dsimp [ratio]
      have hxPos : 0 < x := lt_trans (by norm_num) hx.1
      exact (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 hxPos)).comp
          Complex.continuous_ofReal.continuousAt
    have hProduct := hBaseIntegrable.aestronglyMeasurable.mul
      (hRatioContinuous.aestronglyMeasurable measurableSet_Ioc)
    apply hProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hPower : (x : Complex) ^ (-3 : Complex) *
        (x : Complex) ^ (s + 2) = (x : Complex) ^ (s - 1) := by
      rw [<- Complex.cpow_add _ _ hxZero]
      congr 1
      ring
    dsimp [F, base, ratio]
    calc
      (x : Complex) ^ (-3 : Complex) * (nicolasJ x : Complex) *
          (x : Complex) ^ (s + 2) =
          ((x : Complex) ^ (-3 : Complex) *
            (x : Complex) ^ (s + 2)) * (nicolasJ x : Complex) := by ring
      _ = (x : Complex) ^ (s - 1) * (nicolasJ x : Complex) := by
        rw [hPower]
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall x : Real, 3 < x -> x <= X ->
        norm (F s x) <= majorant x := by
    intro s hs x hxThree hxX
    have hDist : norm (s - s0) < 1 := by
      simpa [dist_eq_norm] using hs
    have hReAbs : abs (s.re - s0.re) <= norm (s - s0) := by
      simpa using Complex.abs_re_le_norm (s - s0)
    have hReUpper : s.re < s0.re + 1 := by
      have hAbsLt : abs (s.re - s0.re) < 1 := lt_of_le_of_lt hReAbs hDist
      linarith [(abs_lt.mp hAbsLt).2]
    have hxPos : 0 < x := lt_trans (by norm_num) hxThree
    have hxOne : 1 <= x := by linarith
    have hExponent : s.re + 2 <= abs s0.re + 4 := by
      have hPosPart : s0.re <= abs s0.re := le_abs_self s0.re
      linarith
    have hExponentNonneg : 0 <= abs s0.re + 4 := by positivity
    have hRatioBound : norm (ratio s x) <=
        X ^ (abs s0.re + 4) := by
      dsimp [ratio]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
      calc
        x ^ (s.re + 2) <= x ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow_of_exponent_le hxOne hExponent
        _ <= X ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow hxPos.le hxX hExponentNonneg
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hFactor : F s x = base x * ratio s x := by
      have hPower : (x : Complex) ^ (-3 : Complex) *
          (x : Complex) ^ (s + 2) = (x : Complex) ^ (s - 1) := by
        rw [<- Complex.cpow_add _ _ hxZero]
        congr 1
        ring
      dsimp [F, base, ratio]
      calc
        (x : Complex) ^ (s - 1) * (nicolasJ x : Complex) =
            ((x : Complex) ^ (-3 : Complex) *
              (x : Complex) ^ (s + 2)) * (nicolasJ x : Complex) := by
          rw [hPower]
        _ = ((x : Complex) ^ (-3 : Complex) *
            (nicolasJ x : Complex)) * (x : Complex) ^ (s + 2) := by ring
    rw [hFactor, norm_mul]
    dsimp [majorant]
    exact mul_le_mul_of_nonneg_left hRatioBound (norm_nonneg (base x))
  have hFIntegrable : Integrable (F s0)
      (volume.restrict (Ioc (3 : Real) X)) := by
    apply Integrable.mono hMajorantIntegrable (hMeasurable s0)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hMajorantNonneg : 0 <= majorant x := by
      dsimp [majorant]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hMajorantNonneg]
    exact hBound s0 (by simp [dist_self]) x hx.1 hx.2
  have hDerivativeMeasurable : AEStronglyMeasurable (F' s0)
      (volume.restrict (Ioc (3 : Real) X)) := by
    have hRealLogOn : ContinuousOn (fun x : Real => Real.log x)
        (Ioc (3 : Real) X) := by
      apply Real.continuousOn_log.mono
      intro x hx
      exact Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (lt_trans (by norm_num) hx.1))
    have hRealLog : AEStronglyMeasurable (fun x : Real => Real.log x)
        (volume.restrict (Ioc (3 : Real) X)) :=
      hRealLogOn.aestronglyMeasurable measurableSet_Ioc
    have hLog : AEStronglyMeasurable
        (fun x : Real => ((Real.log x : Real) : Complex))
        (volume.restrict (Ioc (3 : Real) X)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hRealLog
    exact hLog.mul (hMeasurable s0)
  have hDerivativeBound : Filter.Eventually
      (fun x : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        norm (F' s x) <= X * majorant x)
      (ae (volume.restrict (Ioc (3 : Real) X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro s hs
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxOne : 1 <= x := by linarith [hx.1]
    have hLogNonneg : 0 <= Real.log x := Real.log_nonneg hxOne
    have hLogBound : Real.log x <= X := by
      have hLogSub := Real.log_le_sub_one_of_pos hxPos
      linarith [hx.2]
    have hFBound : norm (F s x) <= majorant x :=
      hBound s (by simpa [Metric.mem_ball] using hs) x hx.1 hx.2
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hLogNonneg]
    exact mul_le_mul hLogBound hFBound (norm_nonneg _) hXPos.le
  have hDerivativeIntegrable : Integrable (fun x : Real => X * majorant x)
      (volume.restrict (Ioc (3 : Real) X)) :=
    hMajorantIntegrable.const_mul X
  have hDerivative : Filter.Eventually
      (fun x : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        HasDerivAt (fun z : Complex => F z x) (F' s x) s)
      (ae (volume.restrict (Ioc (3 : Real) X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro s hs
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hExponent : HasDerivAt (fun z : Complex => z - 1) 1 s :=
      (hasDerivAt_id' s).sub_const 1
    have hPower := hExponent.const_cpow (Or.inl hxZero)
    have hProduct := hPower.mul_const (nicolasJ x : Complex)
    dsimp [F, F']
    apply hProduct.congr_deriv
    rw [Complex.ofReal_log hxPos.le]
    ring
  unfold nicolasJComplexMellinStartup
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s0 zero_lt_one)
    (Eventually.of_forall hMeasurable) hFIntegrable
    hDerivativeMeasurable hDerivativeBound hDerivativeIntegrable hDerivative
  exact hMain.2.differentiableAt

theorem nicolasJComplexMellinStartup_analyticAt
    {X : Real} (hX : 3 <= X) (s0 : Complex) :
    AnalyticAt Complex (nicolasJComplexMellinStartup X) s0 := by
  have hDifferentiable : Differentiable Complex
      (nicolasJComplexMellinStartup X) := by
    intro s
    exact nicolasJComplexMellinStartup_differentiableAt hX s
  exact hDifferentiable.analyticAt s0

theorem realAnalyticAt_re_comp_of_complexAnalyticAt
    {f : Complex -> Complex} {a : Real}
    (hf : AnalyticAt Complex f (a : Complex)) :
    AnalyticAt Real (fun x : Real => Complex.re (f (x : Complex))) a := by
  have hRestricted : AnalyticAt Real f (a : Complex) :=
    hf.restrictScalars
  have hInput : AnalyticAt Real
      (Function.comp f Complex.ofRealCLM) a :=
    hRestricted.compContinuousLinearMap
  change AnalyticAt Real
    (Function.comp Complex.reCLM
      (Function.comp f Complex.ofRealCLM)) a
  choose p hp using hInput
  choose r hr using hp
  refine Exists.intro (Complex.reCLM.compFormalMultilinearSeries p) ?_
  exact Exists.intro r (Complex.reCLM.comp_hasFPowerSeriesOnBall hr)

theorem nicolasJShiftedRealContinuationFilled_analyticAt_zero :
    AnalyticAt Real nicolasJShiftedRealContinuationFilled 0 := by
  unfold nicolasJShiftedRealContinuationFilled
  exact realAnalyticAt_re_comp_of_complexAnalyticAt
    nicolasJShiftedComplexContinuationFilled_analyticAt_zero

def nicolasLandauPositiveMellinContinuationFilled
    (X b a : Real) : Real :=
  nicolasJShiftedRealContinuationFilled a -
    Complex.re (nicolasJComplexMellinStartup X (a : Complex)) +
      nicolasLandauRpowMellinContinuation X b a

theorem nicolasLandauPositiveMellinContinuationFilled_analyticAt_zero
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) :
    AnalyticAt Real (nicolasLandauPositiveMellinContinuationFilled X b) 0 := by
  have hStartup : AnalyticAt Real
      (fun a : Real =>
        Complex.re (nicolasJComplexMellinStartup X (a : Complex))) 0 :=
    realAnalyticAt_re_comp_of_complexAnalyticAt
      (nicolasJComplexMellinStartup_analyticAt hX 0)
  have hRpow := nicolasLandauRpowMellinContinuation_analyticAt
    (X := X) (b := b) (sigma := (0 : Real))
    (lt_of_lt_of_le (by norm_num) hX) hb
  unfold nicolasLandauPositiveMellinContinuationFilled
  exact nicolasJShiftedRealContinuationFilled_analyticAt_zero.sub
    hStartup |>.add hRpow

theorem re_nicolasJComplexMellinStartup_eq_real_of_neg
    {X a : Real} (hX : 3 <= X) (ha : a < 0) :
    Complex.re (nicolasJComplexMellinStartup X (a : Complex)) =
      nicolasJRealMellinStartup X a := by
  have hReal : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasJ x) (Ioc (3 : Real) X) :=
    (nicolasJ_realMellin_integrableOn_Ioi_three ha).mono_set
      Ioc_subset_Ioi_self
  have hCast : IntegrableOn (fun x : Real =>
      ((x ^ (a - 1) * nicolasJ x : Real) : Complex))
      (Ioc (3 : Real) X) :=
    Complex.ofRealCLM.integrable_comp hReal
  have hComplex : IntegrableOn (fun x : Real =>
      (x : Complex) ^ ((a : Complex) - 1) * (nicolasJ x : Complex))
      (Ioc (3 : Real) X) := by
    apply hCast.congr_fun
    . intro x hx
      have hxPos : 0 < x := lt_trans (by norm_num) hx.1
      change ((x ^ (a - 1) * nicolasJ x : Real) : Complex) =
        (x : Complex) ^ ((a : Complex) - 1) * (nicolasJ x : Complex)
      rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
        push_cast
        rfl]
      rw [<- Complex.ofReal_cpow hxPos.le (a - 1)]
      push_cast
      rfl
    . exact measurableSet_Ioc
  have hRe := integral_re hComplex
  unfold nicolasJComplexMellinStartup nicolasJRealMellinStartup
  calc
    Complex.re (integral (volume.restrict (Ioc (3 : Real) X))
        (fun x : Real =>
          (x : Complex) ^ ((a : Complex) - 1) * (nicolasJ x : Complex))) =
        integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
          Complex.re ((x : Complex) ^ ((a : Complex) - 1) *
            (nicolasJ x : Complex))) := hRe.symm
    _ = integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
          x ^ (a - 1) * nicolasJ x) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have hxPos : 0 < x := lt_trans (by norm_num) hx.1
      rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
        push_cast
        rfl]
      have hPoint :
          (x : Complex) ^ ((a - 1 : Real) : Complex) *
              (nicolasJ x : Complex) =
            ((x ^ (a - 1) * nicolasJ x : Real) : Complex) := by
        calc
          (x : Complex) ^ ((a - 1 : Real) : Complex) *
                (nicolasJ x : Complex) =
              ((x ^ (a - 1) : Real) : Complex) *
                (nicolasJ x : Complex) := by
            congr 1
            exact (Complex.ofReal_cpow hxPos.le (a - 1)).symm
          _ = ((x ^ (a - 1) * nicolasJ x : Real) : Complex) := by
            push_cast
            rfl
      change Complex.re
          ((x : Complex) ^ ((a - 1 : Real) : Complex) *
            (nicolasJ x : Complex)) =
        x ^ (a - 1) * nicolasJ x
      rw [hPoint]
      simp

theorem nicolasLandauPositiveMellinContinuationFilled_eq_raw_of_neg
    {X b a : Real} (hX : 3 <= X) (ha : a < 0) :
    nicolasLandauPositiveMellinContinuationFilled X b a =
      nicolasLandauPositiveMellinContinuation X b a := by
  unfold nicolasLandauPositiveMellinContinuationFilled
    nicolasLandauPositiveMellinContinuation
  rw [nicolasJShiftedRealContinuationFilled_eq_raw ha,
    re_nicolasJComplexMellinStartup_eq_real_of_neg hX ha]


end

end Robin1984
