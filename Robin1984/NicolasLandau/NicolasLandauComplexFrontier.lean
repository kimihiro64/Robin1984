import Robin1984.NicolasLandau.NicolasLandauPositiveStrip

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# Nicolas-Landau complex convergence frontier

This file transports the proved real convergence frontier to the complex
moment-generating function of the positive Nicolas tail.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem nicolasLandauComplexMGF_analyticAt_of_positive
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    {z : Complex} (hz : z.re < b) :
    AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b)) z := by
  apply analyticAt_complexMGF
  exact Iio_subset_interior_integrableExpSet_nicolasLandau_of_positive
    hX hb hbHalf hPos hz


theorem exists_nicolasLandauComplexMGF_analytic_halfPlane_of_not_omegaMinus
    {b : Real} (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hNot : Not (AtTopOmegaMinus nicolasJ
      (fun x : Real => x ^ (-b)))) :
    Exists fun X : Real => And (3 <= X)
      (And (forall x : Real, X < x ->
        0 <= nicolasLandauPositiveTail b x)
        (forall z : Complex, z.re < b ->
          AnalyticAt Complex
            (complexMGF (fun x : Real => Real.log x)
              (nicolasLandauPositiveMeasure X b)) z)) := by
  choose X hX hPos using exists_nicolasLandauPositiveTail_start hNot
  exact Exists.intro X (And.intro hX (And.intro hPos (fun z hz =>
    nicolasLandauComplexMGF_analyticAt_of_positive
      hX hb hbHalf hPos hz)))

theorem riemannZeta_zero_im_ne_zero_of_re_mem_Ioo
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRePos : 0 < rho.re) (hReLt : rho.re < 1) :
    Not (rho.im = 0) := by
  intro hIm
  have hEq : rho = (rho.re : Complex) := by
    apply Complex.ext
    . simp
    . simpa using hIm
  rw [hEq] at hZero
  exact (riemannZeta_real_ne_zero_of_mem_Ioo_zero_one
    (And.intro hRePos hReLt)) hZero

theorem exists_rightmost_horizontal_riemannZeta_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1) :
    Exists fun rhoMax : Complex =>
      And (riemannZeta rhoMax = 0)
        (And ((1 / 2 : Real) < rhoMax.re)
          (And (rhoMax.re < 1)
            (And (rhoMax.im = rho.im)
              (forall v : Real, 0 < v ->
                Not (riemannZeta (rhoMax + (v : Complex)) = 0))))) := by
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOne
  let linePoint : Real -> Complex := fun r : Real =>
    (r : Complex) + (rho.im : Complex) * Complex.I
  let S : Set Real := Set.inter (Icc rho.re 1)
    {r : Real | nicolasZetaPoleFactor (linePoint r) = 0}
  have hLineContinuous : Continuous linePoint := by
    dsimp [linePoint]
    fun_prop
  have hFactorContinuous : Continuous
      (fun r : Real => nicolasZetaPoleFactor (linePoint r)) :=
    nicolasZetaPoleFactor_differentiable.continuous.comp hLineContinuous
  have hZeroClosed : IsClosed
      {r : Real | nicolasZetaPoleFactor (linePoint r) = 0} :=
    isClosed_eq hFactorContinuous continuous_const
  have hCompact : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.inter_right hZeroClosed
  have hRhoLine : linePoint rho.re = rho := by
    dsimp [linePoint]
    apply Complex.ext
    . simp
    . simp
  have hRhoNeOne : Not (rho = 1) := by
    intro hEq
    rw [hEq] at hOne
    norm_num at hOne
  have hFactorRho : nicolasZetaPoleFactor rho = 0 := by
    have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hRhoNeOne
    rw [hZero] at hIdentity
    have hDen : Not (rho - 1 = 0) := sub_ne_zero.mpr hRhoNeOne
    simpa [hDen] using hIdentity.symm
  have hNonempty : S.Nonempty := by
    refine Exists.intro rho.re ?_
    dsimp [S]
    refine And.intro (And.intro le_rfl hOne.le) ?_
    change nicolasZetaPoleFactor (linePoint rho.re) = 0
    rw [hRhoLine]
    exact hFactorRho
  choose rMax hrMax using hCompact.exists_isGreatest hNonempty
  let rhoMax : Complex := linePoint rMax
  have hrMem : Membership.mem S rMax := hrMax.1
  have hrBounds : Membership.mem (Icc rho.re 1) rMax := by
    exact hrMem.1
  have hrFactor : nicolasZetaPoleFactor rhoMax = 0 := by
    exact hrMem.2
  have hMaxIm : rhoMax.im = rho.im := by
    dsimp [rhoMax, linePoint]
    simp
  have hMaxRe : rhoMax.re = rMax := by
    dsimp [rhoMax, linePoint]
    simp
  have hMaxNeOne : Not (rhoMax = 1) := by
    intro hEq
    have hZeroIm : rhoMax.im = 0 := by rw [hEq]; simp
    exact hIm (hMaxIm.symm.trans hZeroIm)
  have hMaxZero : riemannZeta rhoMax = 0 := by
    rw [riemannZeta_eq_nicolasZetaPoleFactor_div hMaxNeOne, hrFactor,
      zero_div]
  have hMaxHalf : (1 / 2 : Real) < rhoMax.re := by
    rw [hMaxRe]
    exact hHalf.trans_le hrBounds.1
  have hMaxLtOne : rhoMax.re < 1 := by
    rw [hMaxRe]
    apply lt_of_le_of_ne hrBounds.2
    intro hrEq
    have hReOne : (1 : Real) <= rhoMax.re := by rw [hMaxRe, hrEq]
    exact (riemannZeta_ne_zero_of_one_le_re hReOne) hMaxZero
  refine Exists.intro rhoMax (And.intro hMaxZero
    (And.intro hMaxHalf (And.intro hMaxLtOne
      (And.intro hMaxIm ?_))))
  intro v hv
  by_cases hRight : 1 <= (rhoMax + (v : Complex)).re
  . exact riemannZeta_ne_zero_of_one_le_re hRight
  . intro hShiftZero
    have hShiftNeOne : Not (rhoMax + (v : Complex) = 1) := by
      intro hEq
      have hZeroIm : (rhoMax + (v : Complex)).im = 0 := by rw [hEq]; simp
      have hShiftIm : (rhoMax + (v : Complex)).im = rho.im := by
        simp [hMaxIm]
      exact hIm (hShiftIm.symm.trans hZeroIm)
    have hShiftFactor :
        nicolasZetaPoleFactor (rhoMax + (v : Complex)) = 0 := by
      have hIdentity :=
        riemannZeta_eq_nicolasZetaPoleFactor_div hShiftNeOne
      rw [hShiftZero] at hIdentity
      have hDen : Not (rhoMax + (v : Complex) - 1 = 0) :=
        sub_ne_zero.mpr hShiftNeOne
      simpa [hDen] using hIdentity.symm
    have hShiftLine : linePoint (rMax + v) = rhoMax + (v : Complex) := by
      dsimp [linePoint, rhoMax]
      push_cast
      ring
    have hShiftMem : S (rMax + v) := by
      dsimp [S]
      refine And.intro ?_ ?_
      . constructor
        . linarith [hrBounds.1]
        . rw [Complex.add_re, Complex.ofReal_re, hMaxRe] at hRight
          exact (lt_of_not_ge hRight).le
      . change nicolasZetaPoleFactor (linePoint (rMax + v)) = 0
        rw [hShiftLine]
        exact hShiftFactor
    have hMaximal : rMax + v <= rMax := hrMax.2 hShiftMem
    linarith


theorem nicolasJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
    {center : Complex} {R : Real} (hRPos : 0 < R)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (Not (z = 0))
          (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
            And (Not ((((u + 1 : Real) : Complex) - z) = 0))
              (Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0)))) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledCompact
      center := by
  let K : Set (Prod Real Complex) := fun p =>
    And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem (Metric.closedBall center (R / 2)) p.2)
  let F : Prod Real Complex -> Complex := fun p =>
    nicolasJMellinShiftIntegrandFilled p.2 p.1
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) 1)).prod
      (isCompact_closedBall center (R / 2))
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), center) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl zero_le_one)
      (Metric.mem_closedBall_self (by linarith))
  have hContinuous : ContinuousOn F K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    change And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem (Metric.closedBall center (R / 2)) p.2) at hp
    have hpBall : Membership.mem (Metric.ball center R) p.2 := by
      rw [Metric.mem_closedBall] at hp
      rw [Metric.mem_ball]
      linarith
    have hpGood := hGood p.2 hpBall
    exact nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      hp.1.1 hpGood.1 (hpGood.2 p.1 hp.1).1 (hpGood.2 p.1 hp.1).2
  choose p hpK hpMax using hKCompact.exists_isMaxOn hKNonempty hContinuous.norm
  let M : Real := norm (F p)
  have hMNonneg : 0 <= M := norm_nonneg _
  have hKernelBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.closedBall center (R / 2)) z ->
            norm (nicolasJMellinShiftIntegrandFilled z u) <= M := by
    intro u hu z hz
    have hPair : K (u, z) := by
      dsimp [K]
      exact And.intro hu hz
    simpa [M, F] using hpMax hPair
  have hContinuousU : forall z : Complex,
      Membership.mem (Metric.closedBall center (R / 2)) z ->
        ContinuousOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    intro z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGood := hGood z hzBall
    intro u hu
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      hu.1 hzGood.1 (hzGood.2 u hu).1 (hzGood.2 u hu).2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hAnalytic : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.closedBall center (R / 2)) z ->
            AnalyticAt Complex (fun w : Complex =>
              nicolasJMellinShiftIntegrandFilled w u) z := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGood := hGood z hzBall
    exact
      nicolasJMellinShiftIntegrandFilled_analyticAt_of_ne_zero_of_factor_ne_zero
        hu.1 hzGood.1 (hzGood.2 u hu).1 (hzGood.2 u hu).2
  have hDerivativeMeasurable : forall z : Complex,
      Membership.mem (Metric.ball center (R / 4)) z ->
        AEStronglyMeasurable (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)
          (volume.restrict (Ioc (0 : Real) 1)) := by
    intro z hz
    let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
      slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
        z (z + nicolasCompactStripDerivativeStep R n)
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      linarith
    have hShiftClosed : forall n : Nat,
        Membership.mem (Metric.closedBall center (R / 2))
          (z + nicolasCompactStripDerivativeStep R n) := by
      intro n
      rw [Metric.mem_closedBall]
      calc
        dist (z + nicolasCompactStripDerivativeStep R n) center <=
            dist (z + nicolasCompactStripDerivativeStep R n) z +
              dist z center := dist_triangle _ z _
        _ = norm (nicolasCompactStripDerivativeStep R n) +
              dist z center := by rw [dist_eq_norm]; simp
        _ <= R / 8 + R / 4 :=
          (add_lt_add_of_le_of_lt
            (norm_nicolasCompactStripDerivativeStep_le hRPos n) hzDist).le
        _ <= R / 2 := by linarith
    have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      intro n
      have hShift := (hContinuousU _ (hShiftClosed n)).mono
        Ioc_subset_Icc_self
      have hBase := (hContinuousU z hzClosed).mono Ioc_subset_Icc_self
      have hShiftMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled
            (z + nicolasCompactStripDerivativeStep R n) u)
          (volume.restrict (Ioc (0 : Real) 1)) :=
        hShift.aestronglyMeasurable measurableSet_Ioc
      have hBaseMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled z u)
          (volume.restrict (Ioc (0 : Real) 1)) :=
        hBase.aestronglyMeasurable measurableSet_Ioc
      have hEq : slopeSeq n = fun u : Real =>
          Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z) *
            (nicolasJMellinShiftIntegrandFilled
                (z + nicolasCompactStripDerivativeStep R n) u -
              nicolasJMellinShiftIntegrandFilled z u) := by
        funext u
        dsimp [slopeSeq]
        unfold slope
        simp only [smul_eq_mul, vsub_eq_sub]
      rw [hEq]
      exact ((hShiftMeas.sub hBaseMeas).const_mul
        (Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z))).aemeasurable
    have hStepWithin : Tendsto (nicolasCompactStripDerivativeStep R) atTop
        (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact And.intro (nicolasCompactStripDerivativeStep_tendsto_zero R)
        (Eventually.of_forall (fun n : Nat =>
          Set.mem_compl_singleton_iff.mpr
            (nicolasCompactStripDerivativeStep_ne_zero hRPos n)))
    have hTendsto : Filter.Eventually
        (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
          (nhds (deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)))
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have huIcc : Membership.mem (Icc (0 : Real) 1) u :=
        Ioc_subset_Icc_self hu
      have hSlope := (hAnalytic u huIcc z hzClosed).differentiableAt.hasDerivAt
        |>.tendsto_slope_zero.comp hStepWithin
      change Tendsto (fun n : Nat =>
        Inv.inv (nicolasCompactStripDerivativeStep R n) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasCompactStripDerivativeStep R n) u -
            nicolasJMellinShiftIntegrandFilled z u))
        atTop (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
      exact hSlope
    exact (aemeasurable_of_tendsto_metrizable_ae'
      hMeas hTendsto).aestronglyMeasurable
  have hDerivativeBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.ball center (R / 4)) z ->
            norm (deriv (fun w : Complex =>
              nicolasJMellinShiftIntegrandFilled w u) z) <= 8 * M / R := by
    intro u hu z hz
    let f : Complex -> Complex := fun w =>
      nicolasJMellinShiftIntegrandFilled w u
    let r : Real := R / 4
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hSmallSubset : Metric.ball z r <=
        Metric.closedBall center (R / 2) := by
      intro w hw
      rw [Metric.mem_ball] at hw
      rw [Metric.mem_closedBall]
      calc
        dist w center <= dist w z + dist z center := dist_triangle _ z _
        _ <= R / 4 + R / 4 := by
          dsimp [r] at hw
          exact (add_lt_add hw hzDist).le
        _ <= R / 2 := by linarith
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      apply hSmallSubset
      exact Metric.mem_ball_self (by dsimp [r]; linarith)
    have hDiff : DifferentiableOn Complex f (Metric.ball z r) := by
      intro w hw
      exact (hAnalytic u hu w (hSmallSubset hw)).differentiableAt.differentiableWithinAt
    have hMaps : MapsTo f (Metric.ball z r)
        (Metric.closedBall (f z) (2 * M)) := by
      intro w hw
      have hwBound : norm (f w) <= M := hKernelBound u hu w (hSmallSubset hw)
      have hzBound : norm (f z) <= M := hKernelBound u hu z hzClosed
      rw [Metric.mem_closedBall]
      calc
        dist (f w) (f z) <= norm (f w) + norm (f z) := by
          simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
        _ <= M + M := add_le_add hwBound hzBound
        _ = 2 * M := by ring
    have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
      hDiff hMaps (by dsimp [r]; linarith)
    change norm (deriv f z) <= 8 * M / R
    calc
      norm (deriv f z) <= (2 * M) / r := hCauchy
      _ = 8 * M / R := by
        dsimp [r]
        field_simp [hRPos.ne']
        ring
  let s : Set Complex := Metric.ball center (R / 4)
  have hHasDeriv : forall z : Complex, Membership.mem s z ->
      HasDerivAt nicolasJShiftedComplexContinuationFilledCompact
        (integral (volume.restrict (Ioc (0 : Real) 1)) (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)) z := by
    intro z hz
    let G : Complex -> Real -> Complex := fun w => fun u =>
      nicolasJMellinShiftIntegrandFilled w u
    let G' : Complex -> Real -> Complex := fun w => fun u =>
      deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
    have hsNhd : Membership.mem (nhds z) s :=
      Metric.isOpen_ball.mem_nhds hz
    have hGMeas : Filter.Eventually
        (fun w : Complex => AEStronglyMeasurable (G w)
          (volume.restrict (Ioc (0 : Real) 1))) (nhds z) := by
      filter_upwards [hsNhd] with w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [G]
      exact ((hContinuousU w hwClosed).mono Ioc_subset_Icc_self)
        |>.aestronglyMeasurable measurableSet_Ioc
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      have hzDist : dist z center < R / 4 := by
        simpa [s, Metric.mem_ball] using hz
      linarith
    have hGInt : Integrable (G z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      have hInt : IntegrableOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact hContinuousU z hzClosed
      exact hInt.mono_set Ioc_subset_Icc_self
    have hG'Meas : AEStronglyMeasurable (G' z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      dsimp [G']
      exact hDerivativeMeasurable z hz
    have hBound : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          norm (G' w u) <= 8 * M / R)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      exact hDerivativeBound u (Ioc_subset_Icc_self hu) w hw
    have hBoundInt : IntegrableOn (fun _ : Real => 8 * M / R)
        (Ioc (0 : Real) 1) := by
      have hInt : IntegrableOn (fun _ : Real => 8 * M / R)
          (Icc (0 : Real) 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact continuousOn_const
      exact hInt.mono_set Ioc_subset_Icc_self
    have hDiff : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          HasDerivAt (fun v : Complex => G v u) (G' w u) w)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [G, G']
      exact (hAnalytic u (Ioc_subset_Icc_self hu) w hwClosed)
        |>.differentiableAt.hasDerivAt
    have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := G) (F' := G') (bound := fun _ : Real => 8 * M / R)
      hsNhd hGMeas hGInt hG'Meas hBound hBoundInt hDiff
    unfold nicolasJShiftedComplexContinuationFilledCompact
    simpa [G, G'] using hMain.2
  have hDiffOn : DifferentiableOn Complex
      nicolasJShiftedComplexContinuationFilledCompact s := by
    intro z hz
    exact (hHasDeriv z hz).differentiableAt.differentiableWithinAt
  apply hDiffOn.analyticAt
  dsimp [s]
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith : 0 < R / 4))

theorem exists_nicolasRightmostRayCompactTubeRadius
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Exists fun R : Real => And (0 < R)
      (forall z : Complex,
        Membership.mem
          (Metric.ball ((1 - rho) - (eps : Complex)) R) z ->
          And (Not (z = 0))
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              And (Not ((((u + 1 : Real) : Complex) - z) = 0))
                (Not (nicolasZetaPoleFactor
                  (((u + 1 : Real) : Complex) - z) = 0)))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOne
  have hCenterIm : center.im = -rho.im := by
    dsimp [center]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    exact hIm (neg_eq_zero.mp (hCenterIm.symm.trans hZeroIm))
  have hZeroNhd : Filter.Eventually (fun z : Complex => Not (z = 0))
      (nhds center) := continuousAt_id.eventually_ne hCenterNe
  have hShiftNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not ((((u + 1 : Real) : Complex) - z) = 0))
      (nhds center) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    have hShiftIm :
        ((((u + 1 : Real) : Complex) - center)).im = rho.im := by
      rw [Complex.sub_im, Complex.ofReal_im, hCenterIm]
      ring
    have hShiftNe : Not ((((u + 1 : Real) : Complex) - center) = 0) := by
      intro hEq
      have hZeroIm : ((((u + 1 : Real) : Complex) - center)).im = 0 := by
        rw [hEq]
        simp
      exact hIm (hShiftIm.symm.trans hZeroIm)
    let G : Prod Complex Real -> Complex := fun p =>
      ((p.2 + 1 : Real) : Complex) - p.1
    have hContinuous : Continuous G := by
      dsimp [G]
      fun_prop
    have hAt : Not (G (center, u) = 0) := by
      simpa [G] using hShiftNe
    exact hContinuous.continuousAt.eventually_ne hAt
  have hFactorNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not (nicolasZetaPoleFactor
          (((u + 1 : Real) : Complex) - z) = 0))
      (nhds center) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    let s : Complex := rho + ((eps + u : Real) : Complex)
    have hShift : (((u + 1 : Real) : Complex) - center) = s := by
      dsimp [center, s]
      push_cast
      ring
    have hZeta : Not (riemannZeta s = 0) := by
      dsimp [s]
      exact hRay (eps + u) (by linarith [hu.1])
    have hFactor : Not (nicolasZetaPoleFactor s = 0) := by
      by_cases hsOne : s = 1
      . rw [hsOne, nicolasZetaPoleFactor_one]
        norm_num
      . intro hFactorZero
        have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hsOne
        rw [hFactorZero, zero_div] at hIdentity
        exact hZeta hIdentity
    let G : Prod Complex Real -> Complex := fun p =>
      nicolasZetaPoleFactor (((p.2 + 1 : Real) : Complex) - p.1)
    have hAffine : Continuous (fun p : Prod Complex Real =>
        (((p.2 + 1 : Real) : Complex) - p.1)) := by
      fun_prop
    have hContinuous : Continuous G := by
      dsimp [G]
      exact nicolasZetaPoleFactor_differentiable.continuous.comp hAffine
    have hAt : Not (nicolasZetaPoleFactor
        (((u + 1 : Real) : Complex) - center) = 0) := by
      rw [hShift]
      exact hFactor
    have hPairAt : Not (G (center, u) = 0) := by
      simpa [G] using hAt
    exact hContinuous.continuousAt.eventually_ne hPairAt
  have hAll := hZeroNhd.and (hShiftNhd.and hFactorNhd)
  choose R hRPos hR using Metric.mem_nhds_iff.1 hAll
  refine Exists.intro R (And.intro hRPos ?_)
  intro z hz
  have hzGood := hR hz
  exact And.intro hzGood.1 (fun u hu =>
    And.intro (hzGood.2.1 u hu) (hzGood.2.2 u hu))

theorem nicolasJShiftedComplexContinuationFilledCompact_analyticAt_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledCompact
      ((1 - rho) - (eps : Complex)) := by
  choose R hRPos hGood using
    exists_nicolasRightmostRayCompactTubeRadius
      hZero hHalf hOne hRay hEps
  exact nicolasJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
    hRPos hGood

theorem norm_nicolasJShiftNumeratorFilled_le_of_re_le_threeQuarter
    {u : Real} (hu : 1 < u) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hDen1 : (1 / 4 : Real) < s1.re - 1 := by
    dsimp [s1, s0]
    linarith
  have hShiftRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs1
  have hShiftNumerator : (3 : Real) ^ (1 - s1.re) <=
      (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [s1, s0]
    linarith
  have hShiftPowerNonneg : 0 <= (3 : Real) ^ (1 - s1.re) :=
    Real.rpow_nonneg (by norm_num) _
  have hShiftFraction : (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
      4 * (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
          (3 : Real) ^ (1 - s1.re) / (1 / 4 : Real) :=
        div_le_div_of_nonneg_left hShiftPowerNonneg (by norm_num) hDen1.le
      _ = 4 * (3 : Real) ^ (1 - s1.re) := by ring
      _ <= 4 * (3 : Real) ^ (-u + (3 / 4 : Real)) :=
        mul_le_mul_of_nonneg_left hShiftNumerator (by norm_num)
  have hShift : norm (nicolasPsiMellinTailContinuationFilled s1) <=
      4 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      norm (nicolasPsiMellinTailContinuationFilled s1) <=
          (Real.log 4 + 5) *
            ((3 : Real) ^ (1 - s1.re) / (s1.re - 1)) := hShiftRaw
      _ <= (Real.log 4 + 5) *
          (4 * (3 : Real) ^ (-u + (3 / 4 : Real))) :=
        mul_le_mul_of_nonneg_left hShiftFraction (by positivity)
      _ = 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring
  have hBaseRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs0
  have hBase : norm (nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) * (3 : Real) ^ (-u) := by
    have hPowNonneg : 0 <= (3 : Real) ^ (-u) :=
      Real.rpow_nonneg (by norm_num) _
    have hS0Exponent : 1 - s0.re = -u := by
      dsimp [s0]
      ring
    have hS0Denominator : s0.re - 1 = u := by
      dsimp [s0]
      ring
    rw [hS0Exponent, hS0Denominator] at hBaseRaw
    calc
      norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (Real.log 4 + 5) * ((3 : Real) ^ (-u) / u) := hBaseRaw
      _ <= (Real.log 4 + 5) * ((3 : Real) ^ (-u) / 1) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hPowNonneg zero_lt_one hu.le)
          (by positivity)
      _ = (Real.log 4 + 5) * (3 : Real) ^ (-u) := by ring
  have hPowerNorm : norm ((3 : Complex) ^ z) =
      (3 : Real) ^ z.re := by
    change norm (((3 : Real) : Complex) ^ z) = (3 : Real) ^ z.re
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hPowerProduct : norm ((3 : Complex) ^ z *
      nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    rw [norm_mul, hPowerNorm]
    calc
      (3 : Real) ^ z.re *
          norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (3 : Real) ^ z.re *
            ((Real.log 4 + 5) * (3 : Real) ^ (-u)) :=
        mul_le_mul_of_nonneg_left hBase
          (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.log 4 + 5) *
          ((3 : Real) ^ z.re * (3 : Real) ^ (-u)) := by ring
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re + (-u)) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 3)]
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re - u) := by
        congr 2
      _ <= (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
  unfold nicolasJShiftNumeratorFilled
  change norm (nicolasPsiMellinTailContinuationFilled s1 -
      (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <= _
  calc
    norm (nicolasPsiMellinTailContinuationFilled s1 -
        (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <=
        norm (nicolasPsiMellinTailContinuationFilled s1) +
          norm ((3 : Complex) ^ z *
            nicolasPsiMellinTailContinuationFilled s0) := norm_sub_le _ _
    _ <= 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) +
        (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) :=
      add_le_add hShift hPowerProduct
    _ = 5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring

def nicolasJLargeMajorantAtDistance (d u : Real) : Real :=
  (5 / d) * (Real.log 4 + 5) * (u + 1) *
    (3 : Real) ^ (-u + (3 / 4 : Real))

theorem nicolasJLargeMajorantAtDistance_integrableOn
    {d : Real} (hd : 0 < d) :
    IntegrableOn (nicolasJLargeMajorantAtDistance d) (Ioi (1 : Real)) := by
  have hScaled := nicolasJLargeMajorantHalf_integrableOn.const_mul
    (3 / (4 * d))
  apply hScaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  unfold nicolasJLargeMajorantAtDistance nicolasJLargeMajorantHalf
  field_simp [hd.ne']
  ring

theorem norm_nicolasJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
    {d u : Real} (hd : 0 < d) (hu : 1 < u) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) (hzNorm : d <= norm z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      nicolasJLargeMajorantAtDistance d u := by
  have hzNe : Not (z = 0) := by
    intro hEq
    rw [hEq, norm_zero] at hzNorm
    linarith
  have hNumerator :=
    norm_nicolasJShiftNumeratorFilled_le_of_re_le_threeQuarter hu hzRe
  have hInv : norm (Inv.inv z) <= 1 / d := by
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le hd hzNorm
  have huPos : 0 < u + 1 := by linarith
  unfold nicolasJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzNe]
  unfold slope
  rw [nicolasJShiftNumeratorFilled_zero]
  simp only [smul_eq_mul, vsub_eq_sub, sub_zero]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huPos,
    norm_mul]
  calc
    (u + 1) * (norm (Inv.inv z) *
        norm (nicolasJShiftNumeratorFilled u z)) <=
        (u + 1) * ((1 / d) *
          (5 * (Real.log 4 + 5) *
            (3 : Real) ^ (-u + (3 / 4 : Real)))) := by
      apply mul_le_mul_of_nonneg_left _ huPos.le
      exact mul_le_mul hInv hNumerator (norm_nonneg _)
        (by positivity)
    _ = nicolasJLargeMajorantAtDistance d u := by
      unfold nicolasJLargeMajorantAtDistance
      field_simp [hd.ne']

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    {center : Complex} {R d : Real} (hRPos : 0 < R) (hd : 0 < d)
    (hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z)) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      center := by
  have hPointData : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          And (Not (z = 0))
            (And (Not ((((u + 1 : Real) : Complex) - z) = 0))
              (Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0))) := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGeometry := hGeometry z hzBall
    have hzNe : Not (z = 0) := by
      intro hEq
      rw [hEq, norm_zero] at hzGeometry
      linarith
    have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [hzGeometry.1]
    have hsZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hsOne : Not ((((u + 1 : Real) : Complex) - z) = 1) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hZeta : Not (riemannZeta
        (((u + 1 : Real) : Complex) - z) = 0) :=
      riemannZeta_ne_zero_of_one_lt_re hsRe
    have hFactor : Not (nicolasZetaPoleFactor
        (((u + 1 : Real) : Complex) - z) = 0) :=
      nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
    exact And.intro hzNe (And.intro hsZero hFactor)
  have hKernelBound : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          norm (nicolasJMellinShiftIntegrandFilled z u) <=
            nicolasJLargeMajorantAtDistance d u := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGeometry := hGeometry z hzBall
    exact norm_nicolasJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
      hd hu hzGeometry.1 hzGeometry.2
  have hContinuousU : forall z : Complex,
      Membership.mem (Metric.closedBall center (R / 2)) z ->
        ContinuousOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
    intro z hz u hu
    have hData := hPointData u (mem_Ioi.mp hu) z hz
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      (by linarith [mem_Ioi.mp hu] : 0 <= u)
      hData.1 hData.2.1 hData.2.2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hAnalytic : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          AnalyticAt Complex (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z := by
    intro u hu z hz
    have hData := hPointData u hu z hz
    exact
      nicolasJMellinShiftIntegrandFilled_analyticAt_of_ne_zero_of_factor_ne_zero
        (by linarith [hu] : 0 <= u) hData.1 hData.2.1 hData.2.2
  have hDerivativeMeasurable : forall z : Complex,
      Membership.mem (Metric.ball center (R / 4)) z ->
        AEStronglyMeasurable (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)
          (volume.restrict (Ioi (1 : Real))) := by
    intro z hz
    let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
      slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
        z (z + nicolasCompactStripDerivativeStep R n)
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      linarith
    have hShiftClosed : forall n : Nat,
        Membership.mem (Metric.closedBall center (R / 2))
          (z + nicolasCompactStripDerivativeStep R n) := by
      intro n
      rw [Metric.mem_closedBall]
      calc
        dist (z + nicolasCompactStripDerivativeStep R n) center <=
            dist (z + nicolasCompactStripDerivativeStep R n) z +
              dist z center := dist_triangle _ z _
        _ = norm (nicolasCompactStripDerivativeStep R n) +
              dist z center := by rw [dist_eq_norm]; simp
        _ <= R / 8 + R / 4 :=
          (add_lt_add_of_le_of_lt
            (norm_nicolasCompactStripDerivativeStep_le hRPos n) hzDist).le
        _ <= R / 2 := by linarith
    have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
        (volume.restrict (Ioi (1 : Real))) := by
      intro n
      have hShift := hContinuousU _ (hShiftClosed n)
      have hBase := hContinuousU z hzClosed
      have hShiftMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled
            (z + nicolasCompactStripDerivativeStep R n) u)
          (volume.restrict (Ioi (1 : Real))) :=
        hShift.aestronglyMeasurable measurableSet_Ioi
      have hBaseMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled z u)
          (volume.restrict (Ioi (1 : Real))) :=
        hBase.aestronglyMeasurable measurableSet_Ioi
      have hEq : slopeSeq n = fun u : Real =>
          Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z) *
            (nicolasJMellinShiftIntegrandFilled
                (z + nicolasCompactStripDerivativeStep R n) u -
              nicolasJMellinShiftIntegrandFilled z u) := by
        funext u
        dsimp [slopeSeq]
        unfold slope
        simp only [smul_eq_mul, vsub_eq_sub]
      rw [hEq]
      exact ((hShiftMeas.sub hBaseMeas).const_mul
        (Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z))).aemeasurable
    have hStepWithin : Tendsto (nicolasCompactStripDerivativeStep R) atTop
        (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact And.intro (nicolasCompactStripDerivativeStep_tendsto_zero R)
        (Eventually.of_forall (fun n : Nat =>
          Set.mem_compl_singleton_iff.mpr
            (nicolasCompactStripDerivativeStep_ne_zero hRPos n)))
    have hTendsto : Filter.Eventually
        (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
          (nhds (deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)))
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hSlope := (hAnalytic u hu z hzClosed).differentiableAt.hasDerivAt
        |>.tendsto_slope_zero.comp hStepWithin
      change Tendsto (fun n : Nat =>
        Inv.inv (nicolasCompactStripDerivativeStep R n) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasCompactStripDerivativeStep R n) u -
            nicolasJMellinShiftIntegrandFilled z u))
        atTop (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
      exact hSlope
    exact (aemeasurable_of_tendsto_metrizable_ae'
      hMeas hTendsto).aestronglyMeasurable
  have hDerivativeBound : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.ball center (R / 4)) z ->
          norm (deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z) <=
              (8 / R) * nicolasJLargeMajorantAtDistance d u := by
    intro u hu z hz
    let f : Complex -> Complex := fun w =>
      nicolasJMellinShiftIntegrandFilled w u
    let r : Real := R / 4
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hSmallSubset : Metric.ball z r <=
        Metric.closedBall center (R / 2) := by
      intro w hw
      rw [Metric.mem_ball] at hw
      rw [Metric.mem_closedBall]
      calc
        dist w center <= dist w z + dist z center := dist_triangle _ z _
        _ <= R / 4 + R / 4 := by
          dsimp [r] at hw
          exact (add_lt_add hw hzDist).le
        _ <= R / 2 := by linarith
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      apply hSmallSubset
      exact Metric.mem_ball_self (by dsimp [r]; linarith)
    have hDiff : DifferentiableOn Complex f (Metric.ball z r) := by
      intro w hw
      exact (hAnalytic u hu w (hSmallSubset hw)).differentiableAt.differentiableWithinAt
    have hMaps : MapsTo f (Metric.ball z r)
        (Metric.closedBall (f z)
          (2 * nicolasJLargeMajorantAtDistance d u)) := by
      intro w hw
      have hwBound := hKernelBound u hu w (hSmallSubset hw)
      have hzBound := hKernelBound u hu z hzClosed
      rw [Metric.mem_closedBall]
      calc
        dist (f w) (f z) <= norm (f w) + norm (f z) := by
          simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
        _ <= nicolasJLargeMajorantAtDistance d u +
            nicolasJLargeMajorantAtDistance d u :=
          add_le_add hwBound hzBound
        _ = 2 * nicolasJLargeMajorantAtDistance d u := by ring
    have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
      hDiff hMaps (by dsimp [r]; linarith)
    change norm (deriv f z) <=
      (8 / R) * nicolasJLargeMajorantAtDistance d u
    calc
      norm (deriv f z) <=
          (2 * nicolasJLargeMajorantAtDistance d u) / r := hCauchy
      _ = (8 / R) * nicolasJLargeMajorantAtDistance d u := by
        dsimp [r]
        field_simp [hRPos.ne']
        ring
  let s : Set Complex := Metric.ball center (R / 4)
  have hHasDeriv : forall z : Complex, Membership.mem s z ->
      HasDerivAt nicolasJShiftedComplexContinuationFilledLarge
        (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)) z := by
    intro z hz
    let F : Complex -> Real -> Complex := fun w => fun u =>
      nicolasJMellinShiftIntegrandFilled w u
    let F' : Complex -> Real -> Complex := fun w => fun u =>
      deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
    have hsNhd : Membership.mem (nhds z) s :=
      Metric.isOpen_ball.mem_nhds hz
    have hFMeas : Filter.Eventually
        (fun w : Complex => AEStronglyMeasurable (F w)
          (volume.restrict (Ioi (1 : Real)))) (nhds z) := by
      filter_upwards [hsNhd] with w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [F]
      exact (hContinuousU w hwClosed).aestronglyMeasurable measurableSet_Ioi
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      have hzDist : dist z center < R / 4 := by
        simpa [s, Metric.mem_ball] using hz
      linarith
    have hFInt : Integrable (F z)
        (volume.restrict (Ioi (1 : Real))) := by
      apply Integrable.mono'
        (nicolasJLargeMajorantAtDistance_integrableOn hd)
        ((hContinuousU z hzClosed).aestronglyMeasurable measurableSet_Ioi)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hKernelBound u hu z hzClosed
    have hF'Meas : AEStronglyMeasurable (F' z)
        (volume.restrict (Ioi (1 : Real))) := by
      dsimp [F']
      exact hDerivativeMeasurable z hz
    have hBound : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          norm (F' w u) <=
            (8 / R) * nicolasJLargeMajorantAtDistance d u)
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      exact hDerivativeBound u hu w hw
    have hBoundInt : IntegrableOn
        (fun u : Real => (8 / R) * nicolasJLargeMajorantAtDistance d u)
        (Ioi (1 : Real)) :=
      (nicolasJLargeMajorantAtDistance_integrableOn hd).const_mul (8 / R)
    have hDiff : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          HasDerivAt (fun v : Complex => F v u) (F' w u) w)
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [F, F']
      exact (hAnalytic u hu w hwClosed).differentiableAt.hasDerivAt
    have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F')
      (bound := fun u : Real =>
        (8 / R) * nicolasJLargeMajorantAtDistance d u)
      hsNhd hFMeas hFInt hF'Meas hBound hBoundInt hDiff
    unfold nicolasJShiftedComplexContinuationFilledLarge
    simpa [F, F'] using hMain.2
  have hDiffOn : DifferentiableOn Complex
      nicolasJShiftedComplexContinuationFilledLarge s := by
    intro z hz
    exact (hHasDeriv z hz).differentiableAt.differentiableWithinAt
  apply hDiffOn.analyticAt
  dsimp [s]
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith : 0 < R / 4))

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_large_of_geometry
    {d : Real} (hd : 0 < d) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) (hzNorm : d <= norm z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hzNe : Not (z = 0) := by
    intro hEq
    rw [hEq, norm_zero] at hzNorm
    linarith
  have hContinuous : ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
    intro u hu
    have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [hzRe, mem_Ioi.mp hu]
    have hsZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hsOne : Not ((((u + 1 : Real) : Complex) - z) = 1) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hZeta : Not (riemannZeta
        (((u + 1 : Real) : Complex) - z) = 0) :=
      riemannZeta_ne_zero_of_one_lt_re hsRe
    have hFactor : Not (nicolasZetaPoleFactor
        (((u + 1 : Real) : Complex) - z) = 0) :=
      nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      (by linarith [mem_Ioi.mp hu] : 0 <= u) hzNe hsZero hFactor
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  apply Integrable.mono'
    (nicolasJLargeMajorantAtDistance_integrableOn hd)
    (hContinuous.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_nicolasJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
    hd hu hzRe hzNorm

theorem exists_nicolasRightmostRayLargeGeometry
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {eps : Real} (hEps : 0 < eps) :
    Exists fun d : Real => Exists fun R : Real =>
      And (0 < d) (And (0 < R)
        (forall z : Complex,
          Membership.mem
            (Metric.ball ((1 - rho) - (eps : Complex)) R) z ->
            And (z.re <= (3 / 4 : Real)) (d <= norm z))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOne
  have hCenterIm : center.im = -rho.im := by
    dsimp [center]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    exact hIm (neg_eq_zero.mp (hCenterIm.symm.trans hZeroIm))
  have hCenterNorm : 0 < norm center := norm_pos_iff.mpr hCenterNe
  have hCenterRe : center.re = 1 - rho.re - eps := by
    dsimp [center]
  have hReMargin : 0 < (3 / 4 : Real) - center.re := by
    rw [hCenterRe]
    linarith
  let d : Real := norm center / 2
  let R : Real := min (norm center / 2)
    (((3 / 4 : Real) - center.re) / 2)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hRPos : 0 < R := by
    dsimp [R]
    exact lt_min (by positivity) (by positivity)
  have hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z) := by
    intro z hz
    have hzDist : dist z center < R := by
      simpa [Metric.mem_ball] using hz
    have hDistNorm : dist z center < norm center / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_left _ _)
    have hDistRe : dist z center <
        ((3 / 4 : Real) - center.re) / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_right _ _)
    have hReDiff : z.re - center.re <= dist z center := by
      calc
        z.re - center.re <= abs (z.re - center.re) := le_abs_self _
        _ = abs ((z - center).re) :=
          congrArg abs (Complex.sub_re z center).symm
        _ <= norm (z - center) := Complex.abs_re_le_norm _
        _ = dist z center := by rw [dist_eq_norm]
    have hTriangle : norm center <= dist center z + norm z := by
      have h := dist_triangle center z 0
      simpa [dist_zero_right] using h
    have hNorm : d <= norm z := by
      dsimp [d]
      rw [dist_comm center z] at hTriangle
      linarith
    exact And.intro (by linarith) hNorm
  exact Exists.intro d (Exists.intro R
    (And.intro hd (And.intro hRPos (by simpa [center] using hGeometry))))

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      ((1 - rho) - (eps : Complex)) := by
  choose d R hd hRPos hGeometry using
    exists_nicolasRightmostRayLargeGeometry hZero hHalf hOne hEps
  exact nicolasJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    hRPos hd hGeometry

theorem eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Filter.Eventually (fun z : Complex =>
      IntegrableOn (fun u : Real =>
        nicolasJMellinShiftIntegrandFilled z u) (Ioc (0 : Real) 1))
      (nhds ((1 - rho) - (eps : Complex))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  choose R hRPos hGood using
    exists_nicolasRightmostRayCompactTubeRadius
      hZero hHalf hOne hRay hEps
  have hBall : Membership.mem (nhds center)
      (Metric.ball center (R / 2)) :=
    Metric.ball_mem_nhds _ (by linarith)
  filter_upwards [hBall] with z hz
  have hzClosed : Membership.mem
      (Metric.closedBall center (R / 2)) z :=
    Metric.ball_subset_closedBall hz
  have hzBall : Membership.mem (Metric.ball center R) z := by
    rw [Metric.mem_closedBall] at hzClosed
    rw [Metric.mem_ball]
    linarith
  have hzGood := hGood z (by simpa [center] using hzBall)
  have hContinuous : ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    intro u hu
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      hu.1 hzGood.1 (hzGood.2 u hu).1 (hzGood.2 u hu).2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hInt : IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hContinuous
  exact hInt.mono_set Ioc_subset_Icc_self

theorem eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_large_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {eps : Real} (hEps : 0 < eps) :
    Filter.Eventually (fun z : Complex =>
      IntegrableOn (fun u : Real =>
        nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)))
      (nhds ((1 - rho) - (eps : Complex))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  choose d R hd hRPos hGeometry using
    exists_nicolasRightmostRayLargeGeometry hZero hHalf hOne hEps
  have hBall : Membership.mem (nhds center) (Metric.ball center R) :=
    Metric.ball_mem_nhds _ hRPos
  filter_upwards [hBall] with z hz
  have hzGeometry := hGeometry z (by simpa [center] using hz)
  exact nicolasJMellinShiftIntegrandFilled_integrableOn_large_of_geometry
    hd hzGeometry.1 hzGeometry.2

theorem eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Filter.EventuallyEq (nhds ((1 - rho) - (eps : Complex)))
      nicolasJShiftedComplexContinuationFilled
      (fun z : Complex =>
        nicolasJShiftedComplexContinuationFilledCompact z +
          nicolasJShiftedComplexContinuationFilledLarge z) := by
  have hCompact :=
    eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
      hZero hHalf hOne hRay hEps
  have hLarge :=
    eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_large_rightmostRay
      hZero hHalf hOne hEps
  filter_upwards [hCompact, hLarge] with z hCompactInt hLargeInt
  unfold nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedComplexContinuationFilledCompact
    nicolasJShiftedComplexContinuationFilledLarge
  rw [<- Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) <= 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hCompactInt
  . exact hLargeInt

theorem nicolasJShiftedComplexContinuationFilled_analyticAt_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilled
      ((1 - rho) - (eps : Complex)) := by
  have hCompact :=
    nicolasJShiftedComplexContinuationFilledCompact_analyticAt_rightmostRay
      hZero hHalf hOne hRay hEps
  have hLarge :=
    nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRay
      hZero hHalf hOne hEps
  have hSum : AnalyticAt Complex (fun z : Complex =>
      nicolasJShiftedComplexContinuationFilledCompact z +
        nicolasJShiftedComplexContinuationFilledLarge z)
      ((1 - rho) - (eps : Complex)) := hCompact.add hLarge
  have hEq :=
    eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
      hZero hHalf hOne hRay hEps
  exact (analyticAt_congr hEq).mpr hSum

end

end Robin1984
