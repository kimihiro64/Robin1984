import Robin1984.GRH.GodementJacquetThetaWeightedCancellation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and integration over a measurable fundamental domain.
- Formalization note: Restricts a fundamental domain to a measurable orbit cover. Proves the denominator and integrability inputs for simultaneous cancellation of singular terms in the primal and dual theta integrals.
- PROVENANCE-END
-/

/-!
# Theta cancellation on a measurable reduction set

A measurable orbit cover gives a fundamental domain inside the cover. Compact
finite matrix projections, bounded weighted cusp values and finite measure there
give the four integrability inputs for the two theta cancellations.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

/-- A measurable set that meets every left orbit contains a measurable
fundamental domain. Select the first translate into that set from each
point of an existing measurable fundamental domain. -/
theorem exists_measurableFundamentalRepresentatives_subset_of_orbitCover
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) [Countable H] (D S : Set G)
    (hD : MeasurableSet D) (hS : MeasurableSet S)
    (hUnique : forall x : G, ExistsUnique (fun h : H => Membership.mem D (h.val * x)))
    (hCover : forall x : G, Exists (fun h : H => Membership.mem S (h.val * x))) :
    Exists (fun E : Set G => And (MeasurableSet E) (And (Set.Subset E S)
      (forall x : G, ExistsUnique (fun h : H => Membership.mem E (h.val * x))))) := by
  choose e he using exists_surjective_nat H
  let A (j : Nat) := Set.preimage (fun x : G => (e j).val * x) S
  let U (j : Nat) := Set.iUnion (fun i : Nat => Set.iUnion (fun _ : i < j => A i))
  let W (j : Nat) := Set.preimage (fun x : G => Inv.inv (e j).val * x)
    (SDiff.sdiff (Set.inter D (A j)) (U j))
  let E : Set G := Set.iUnion W
  have hA (j : Nat) : MeasurableSet (A j) := (continuous_const_mul (e j).val).measurable hS
  have hU (j : Nat) : MeasurableSet (U j) :=
    MeasurableSet.iUnion (fun _ => MeasurableSet.iUnion (fun _ => hA _))
  have hW (j : Nat) : MeasurableSet (W j) :=
    (continuous_const_mul (Inv.inv (e j).val)).measurable ((hD.inter (hA j)).diff (hU j))
  have hWS (j : Nat) : Set.Subset (W j) S := by
    intro y hy
    have hyA : Membership.mem (A j) (Inv.inv (e j).val * y) := hy.1.2
    change Membership.mem S ((e j).val * (Inv.inv (e j).val * y)) at hyA
    rwa [<- mul_assoc, mul_inv_cancel, one_mul] at hyA
  refine Exists.intro E (And.intro (MeasurableSet.iUnion hW) (And.intro ?_ ?_))
  . intro y hy
    choose j hj using Set.mem_iUnion.mp hy
    exact hWS j hj
  . have hMeet (y : G) : Exists (fun i => Membership.mem (A i) y) := by
      choose a ha using hCover y
      choose i hi using he a
      refine Exists.intro i ?_
      change Membership.mem S ((e i).val * y)
      rwa [hi]
    intro x
    choose a ha using hUnique x
    let y := a.val * x
    let i := Nat.find (hMeet y)
    let b := e i * a
    have hx (j : Nat) (g : H) :
        Inv.inv (e j).val * (g.val * x) = (Inv.inv (e j) * g).val * x := by
      change Inv.inv (e j).val * (g.val * x) = (Inv.inv (e j).val * g.val) * x
      exact (mul_assoc _ _ _).symm
    have hb : Inv.inv (e i) * b = a := inv_mul_cancel_left (e i) a
    have hAi : Membership.mem (A i) y := Nat.find_spec (hMeet y)
    have hUi : Not (Membership.mem (U i) y) := by
      intro h
      choose j hj using Set.mem_iUnion.mp h
      choose hji hAj using Set.mem_iUnion.mp hj
      exact (not_lt_of_ge (Nat.find_min' (hMeet y) hAj)) hji
    refine Exists.intro b (And.intro ?_ ?_)
    . apply Set.mem_iUnion.mpr
      refine Exists.intro i ?_
      change Membership.mem (SDiff.sdiff (Set.inter D (A i)) (U i))
        (Inv.inv (e i).val * (b.val * x))
      rw [hx i b, hb]
      exact And.intro (And.intro ha.1 hAi) hUi
    . intro b' hb'
      choose j hj using Set.mem_iUnion.mp hb'
      have hLand : Membership.mem (SDiff.sdiff (Set.inter D (A j)) (U j))
          ((Inv.inv (e j) * b').val * x) := by
        rw [<- hx j b']
        exact hj
      have hEq : Inv.inv (e j) * b' = a := ha.2 _ hLand.1.1
      rw [hEq] at hLand
      have hij : i <= j := Nat.find_min' (hMeet y) hLand.1.2
      have hji : j <= i := by
        apply le_of_not_gt
        intro hlt
        exact hLand.2 (Set.mem_iUnion.mpr (Exists.intro i
          (Set.mem_iUnion.mpr (Exists.intro hlt hAi))))
      have hjiEq : j = i := le_antisymm hji hij
      calc
        b' = e j * (Inv.inv (e j) * b') := (mul_inv_cancel_left _ _).symm
        _ = b := by rw [hEq, hjiEq]

private abbrev ReductionHeightFinite (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K
private abbrev ReductionHeightGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker
private abbrev ReductionHeightDenom (K : Type*) [Field K] [NumberField K] :=
  Subtype (fun d : RingOfIntegers K => Not (d = 0))

/-- A compact finite-entry cover of a reduction set lets one choose the
two denominator functions to be constant on that set. -/
theorem exists_godementJacquetDenominators_constant_on_finiteEntryCover
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (S : Set (ReductionHeightGroup K n)) (U : Set (ReductionHeightFinite K))
    (hU : IsCompact U)
    (hLeft : forall A : ReductionHeightGroup K n, Membership.mem S A ->
      forall i j, Membership.mem U (A.val.val i j).2)
    (hRight : forall B : ReductionHeightGroup K n, Membership.mem S B ->
      forall i j, Membership.mem U (B.val.inv i j).2) :
    let R := RingOfIntegers K
    let q := (algebraMap K (ReductionHeightFinite K)).comp (algebraMap R K)
    Exists (fun d : ReductionHeightDenom K =>
      Exists (fun deltaLeft : ReductionHeightGroup K n -> ReductionHeightDenom K =>
        Exists (fun deltaRight : ReductionHeightGroup K n -> ReductionHeightDenom K =>
          And (forall A i j, Membership.mem (heckeIntegralFiniteAdeles (K := K))
            (q (deltaLeft A).val * (A.val.val i j).2))
          (And (forall B i j, Membership.mem (heckeIntegralFiniteAdeles (K := K))
            (q (deltaRight B).val * (B.val.inv i j).2))
            (forall A, Membership.mem S A -> And (deltaLeft A = d) (deltaRight A = d)))))) := by
  let R := RingOfIntegers K
  let q := (algebraMap K (ReductionHeightFinite K)).comp (algebraMap R K)
  let G := ReductionHeightGroup K n
  choose d hd using exists_commonDenominator_of_isCompact_finiteAdeles U hU
  let fixed : ReductionHeightDenom K := Subtype.mk d hd.1
  choose eL heL using fun A : G => exists_godementJacquetMatrix_finiteDenominator K n A.val.val
  choose eR heR using fun B : G => exists_godementJacquetMatrix_finiteDenominator K n B.val.inv
  let L (A : G) : ReductionHeightDenom K :=
    if Membership.mem S A then fixed else Subtype.mk (eL A) (heL A).1
  let P (B : G) : ReductionHeightDenom K :=
    if Membership.mem S B then fixed else Subtype.mk (eR B) (heR B).1
  have hClear (x : ReductionHeightFinite K) (hx : Membership.mem U x) :
      Membership.mem (heckeIntegralFiniteAdeles (K := K)) (q d * x) := by
    intro v
    change Membership.mem (v.adicCompletionIntegers K) ((q d) v * x v)
    have hq : (q d) v = algebraMap R (v.adicCompletion K) d :=
      (IsScalarTower.algebraMap_apply R K (v.adicCompletion K) d).symm
    rw [hq, mul_comm]
    exact hd.2 x hx v
  refine Exists.intro fixed (Exists.intro L (Exists.intro P (And.intro ?_ (And.intro ?_ ?_))))
  . intro A i j
    by_cases hA : Membership.mem S A
    . have hLA : L A = fixed := if_pos hA
      change Membership.mem (heckeIntegralFiniteAdeles (K := K)) (q (L A).val * (A.val.val i j).2)
      rw [hLA]
      exact hClear _ (hLeft A hA i j)
    . have hLA : L A = Subtype.mk (eL A) (heL A).1 := if_neg hA
      change Membership.mem (heckeIntegralFiniteAdeles (K := K)) (q (L A).val * (A.val.val i j).2)
      rw [hLA]
      exact (heL A).2 i j
  . intro B i j
    by_cases hB : Membership.mem S B
    . have hPB : P B = fixed := if_pos hB
      change Membership.mem (heckeIntegralFiniteAdeles (K := K)) (q (P B).val * (B.val.inv i j).2)
      rw [hPB]
      exact hClear _ (hRight B hB i j)
    . have hPB : P B = Subtype.mk (eR B) (heR B).1 := if_neg hB
      change Membership.mem (heckeIntegralFiniteAdeles (K := K)) (q (P B).val * (B.val.inv i j).2)
      rw [hPB]
      exact (heR B).2 i j
  . intro A hA
    exact And.intro (if_pos hA) (if_pos hA)

private abbrev ReductionArchAdele (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K
private abbrev ReductionArchVector (K : Type*) [Field K] (I : Type*) :=
  PiLp 2 (fun _ : I => DedekindZeta.Theta.minkowskiSpace K)

/-- The joint archimedean Minkowski coordinates depend continuously on
an adelic vector. -/
theorem continuous_heckeAdeleMinkowskiVector
    (K : Type*) [Field K] [NumberField K] (I : Type*) [Fintype I] :
    Continuous (heckeAdeleMinkowskiVector K I) := by
  let E := PiLp.continuousLinearEquiv 2 Real (fun _ : I => DedekindZeta.Theta.minkowskiSpace K)
  have hMix : Continuous (heckeAdeleMixedCoordinate K) := by
    change Continuous (fun x : ReductionArchAdele K => InfiniteAdeleRing.ringEquiv_mixedSpace K x.1)
    exact (continuous_heckeInfiniteAdele_mixedSpace (K := K)).comp continuous_fst
  change Continuous (fun x : I -> ReductionArchAdele K =>
    E.symm (fun i => DedekindZeta.Theta.toMinkowski K (heckeAdeleMixedCoordinate K (x i))))
  apply E.symm.continuous.comp
  apply continuous_pi
  intro i
  exact (DedekindZeta.Theta.toMinkowski K).continuous.comp (hMix.comp (continuous_apply i))

set_option maxHeartbeats 700000 in
/-- Archimedean dilation is continuous in the operator norm whenever the
underlying adelic matrix varies continuously. -/
theorem continuous_heckeAdeleArchimedeanMatrixDilation_toContinuousLinearMap
    (K : Type*) [Field K] [NumberField K] (I : Type*) [Fintype I] [DecidableEq I]
    (X : Type*) [TopologicalSpace X]
    (M : X -> Matrix.GeneralLinearGroup I (ReductionArchAdele K))
    (hM : Continuous (fun x => (M x).val)) :
    Continuous (fun x => (heckeAdeleArchimedeanMatrixDilation K I (M x)).toContinuousLinearMap) := by
  let V := ReductionArchVector K I
  let E := PiLp.continuousLinearEquiv 2 Real (fun _ : I => DedekindZeta.Theta.minkowskiSpace K)
  let T (x : X) := (heckeAdeleArchimedeanMatrixDilation K I (M x)).toContinuousLinearMap
  have hPoint (v : V) : Continuous (fun x => T x v) := by
    let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
    let m := DedekindZeta.Theta.toMinkowski K
    let g (i : I) : ReductionArchAdele K := Prod.mk (e.symm (m.symm (v i))) 0
    have hLift : heckeAdeleMinkowskiVector K I g = v := by
      apply E.injective
      funext i
      change m (e (e.symm (m.symm (v i)))) = v i
      rw [RingEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    have hEq (x : X) : T x v = heckeAdeleMinkowskiVector K I ((M x).val.mulVec g) := by
      have h := (heckeAdeleMinkowskiVector_mulVec K I (M x) g).symm
      rw [hLift] at h
      exact h
    rw [funext hEq]
    exact (continuous_heckeAdeleMinkowskiVector K I).comp (hM.matrix_mulVec continuous_const)
  let b := Module.finBasis Real V
  let L (i : Fin (Module.finrank Real V)) :=
    ContinuousLinearMap.smulRightL Real V V (b.coord i).toContinuousLinearMap
  have hDecomp (x : X) : T x = Finset.univ.sum (fun i => L i (T x (b i))) := by
    apply ContinuousLinearMap.ext
    intro v
    rw [_root_.sum_apply]
    change T x v = Finset.univ.sum (fun i => HSMul.hSMul (b.repr v i) (T x (b i)))
    calc
      _ = T x (Finset.univ.sum (fun i => HSMul.hSMul (b.repr v i) (b i))) :=
        congrArg (fun v => T x v) (b.sum_repr v).symm
      _ = _ := by simp only [map_sum, map_smul]
  change Continuous T
  rw [funext hDecomp]
  exact continuous_finsetSum Finset.univ (fun i _ => (L i).continuous.comp (hPoint (b i)))

/-- The scalar height used in the full theta majorant is continuous in
both adelic matrices. -/
theorem continuous_godementJacquetFullTheta_archimedeanHeight
    (K : Type*) [Field K] [NumberField K] (n : Nat) :
    Continuous (fun q : Prod (AdelicGeneralLinearGroup K n) (AdelicGeneralLinearGroup K n) =>
      godementJacquetFullTheta_archimedeanHeight K n q.1 q.2) := by
  let G := AdelicGeneralLinearGroup K n
  let X := Prod G G
  let I := Prod (Fin n) (Fin n)
  let D := ReductionArchAdele K
  let A : G -> Matrix (Fin n) (Fin n) D := Units.val
  have hA : Continuous A := Units.continuous_val
  have hL (i j : Fin n) : Continuous (fun q : X => A q.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (hA.comp continuous_fst))
  have hR (i j : Fin n) : Continuous (fun q : X => A q.2 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (hA.comp continuous_snd))
  let U (q : X) := godementJacquetMatrixDilation q.1 q.2
  have hU : Continuous (fun q => (U q).val) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun q : X => A q.2 j.1 i.1 * A q.1 i.2 j.2)
    exact (hR j.1 i.1).mul (hL i.2 j.2)
  exact continuous_const.max
    (continuous_heckeAdeleArchimedeanMatrixDilation_toContinuousLinearMap K I X U hU).norm

set_option maxHeartbeats 1200000 in
/-- On a finite-measure reduction set where the denominator functions
are constant, pointwise bounds for the two weighted cusp values supply
the exact weighted integrability used in theta cancellation. -/
theorem integrableOn_godementJacquetThetaWeights_of_boundedOn_reductionSet
    (K : Type*) [Field K] [NumberField K] (n m : Nat)
    [MeasurableSpace (ReductionHeightGroup K n)] [BorelSpace (ReductionHeightGroup K n)]
    (mu : Measure (ReductionHeightGroup K n))
    (S : Set (ReductionHeightGroup K n)) (hS : MeasurableSet S) (hFin : mu S < Top.top)
    (d : ReductionHeightDenom K)
    (dLeft dRight : ReductionHeightGroup K n -> ReductionHeightDenom K)
    (hConst : forall A, Membership.mem S A -> And (dLeft A = d) (dRight A = d))
    (c : ReductionHeightGroup K n -> Complex) (hc : Measurable c) (M : Real) :
    let s (e : ReductionHeightDenom K) :=
      godementJacquetFullTheta_principalScalarMatrixUnit K n e.val e.property
    let H := godementJacquetFullTheta_archimedeanHeight K n
    (forall A, Membership.mem S A ->
      And (norm (c A) * H (s d * A.val) 1 ^ m <= M)
        (norm (c A) * H 1 (Inv.inv A.val * s d) ^ m <= M)) ->
    And (IntegrableOn (fun A => norm (c A) * H (s (dLeft A) * A.val) 1 ^ m) S mu)
      (IntegrableOn (fun A => norm (c A) * H 1 (Inv.inv A.val * s (dRight A)) ^ m) S mu) := by
  intro s H hBound
  let G := ReductionHeightGroup K n
  let L (A : G) : Real := H (s d * A.val) 1
  let R (A : G) : Real := H 1 (Inv.inv A.val * s d)
  let nu := mu.restrict S
  let : IsFiniteMeasure nu :=
    { measure_univ_lt_top := by
        change mu.restrict S Set.univ < Top.top
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact hFin }
  let G0 := AdelicGeneralLinearGroup K n
  let LPair (A : G) : Prod G0 G0 := Prod.mk (s d * A.val) 1
  let RPair (A : G) : Prod G0 G0 := Prod.mk 1 (Inv.inv A.val * s d)
  have hVal : Continuous (fun A : G => A.val) := continuous_subtype_val
  have hInv : Continuous (fun A : G => Inv.inv A.val) := continuous_inv.comp hVal
  have hLPair : Continuous LPair := (continuous_const.mul hVal).prodMk continuous_const
  have hRPair : Continuous RPair := continuous_const.prodMk (hInv.mul continuous_const)
  have hH : Continuous (fun q : Prod G0 G0 => H q.1 q.2) :=
    continuous_godementJacquetFullTheta_archimedeanHeight K n
  have hL : Continuous L := by
    change Continuous (Function.comp (fun q : Prod G0 G0 => H q.1 q.2) LPair)
    exact hH.comp hLPair
  have hR : Continuous R := by
    change Continuous (Function.comp (fun q : Prod G0 G0 => H q.1 q.2) RPair)
    exact hH.comp hRPair
  have hNonneg (a b : AdelicGeneralLinearGroup K n) : 0 <= H a b :=
    zero_le_one.trans (le_max_left _ _)
  have hConstInt : Integrable (fun _ : G => M) nu := integrable_const M
  have hIL : Integrable (fun A : G => norm (c A) * L A ^ m) nu := by
    have hF : Measurable (fun A : G => norm (c A) * L A ^ m) :=
      hc.norm.mul (hL.pow m).measurable
    refine hConstInt.mono' hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS] with A hA
    have hP : 0 <= norm (c A) * L A ^ m :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (hNonneg (s d * A.val) 1) _)
    rw [Real.norm_of_nonneg hP]
    exact (hBound A hA).1
  have hIR : Integrable (fun A : G => norm (c A) * R A ^ m) nu := by
    have hF : Measurable (fun A : G => norm (c A) * R A ^ m) :=
      hc.norm.mul (hR.pow m).measurable
    refine hConstInt.mono' hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS] with A hA
    have hP : 0 <= norm (c A) * R A ^ m :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (hNonneg 1 (Inv.inv A.val * s d)) _)
    rw [Real.norm_of_nonneg hP]
    exact (hBound A hA).2
  constructor
  . refine hIL.congr ?_
    filter_upwards [ae_restrict_mem hS] with A hA
    exact congrArg (fun e : ReductionHeightDenom K => norm (c A) * H (s e * A.val) 1 ^ m)
      ((hConst A hA).1).symm
  . refine hIR.congr ?_
    filter_upwards [ae_restrict_mem hS] with A hA
    exact congrArg (fun e : ReductionHeightDenom K => norm (c A) * H 1 (Inv.inv A.val * s e) ^ m)
      ((hConst A hA).2).symm

set_option maxHeartbeats 1500000 in
/-- A finite-measure reduction set with compact finite entries and bounded
weighted cusp values contains a fundamental domain on which the primal and
Fourier-dual singular terms cancel. -/
theorem exists_godementJacquetDoubleThetaCancellation_of_reductionSet
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (ReductionHeightFinite K)] [BorelSpace (ReductionHeightFinite K)]
    [MeasurableSpace (ReductionHeightGroup K n)] [BorelSpace (ReductionHeightGroup K n)]
    [MeasurableSpace (Matrix (Fin n) (Fin n) (ReductionArchAdele K))]
    [BorelSpace (Matrix (Fin n) (Fin n) (ReductionArchAdele K))]
    (mu : Measure (ReductionHeightGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (D0 S : Set (ReductionHeightGroup K n)) (hD0 : MeasurableSet D0) (hS : MeasurableSet S)
    (hUnique0 : forall A : ReductionHeightGroup K n, ExistsUnique
      (fun gamma : (adelicPrincipalDeterminantOne K n).range => Membership.mem D0 (gamma.val * A)))
    (hCover : forall A : ReductionHeightGroup K n, Exists
      (fun gamma : (adelicPrincipalDeterminantOne K n).range => Membership.mem S (gamma.val * A)))
    (hFin : mu S < Top.top) (U : Set (ReductionHeightFinite K)) (hU : IsCompact U)
    (hLeft : forall A : ReductionHeightGroup K n, Membership.mem S A ->
      forall i j, Membership.mem U (A.val.val i j).2)
    (hRight : forall B : ReductionHeightGroup K n, Membership.mem S B ->
      forall i j, Membership.mem U (B.val.inv i j).2)
    (a : Prod (Fin n) (Fin n) -> ReductionHeightFinite K) (b : RingOfIntegers K)
    (hb : Not (b = 0))
    (phi : SchwartzMap (ReductionArchVector K (Prod (Fin n) (Fin n))) Complex)
    (c f : ReductionHeightGroup K n -> Complex) (hc : Measurable c) (hf : Measurable f)
    (hInvariantC : forall gamma : (adelicPrincipalDeterminantOne K n).range, forall A,
      c (gamma.val * A) = c A)
    (hInvariantF : forall gamma : (adelicPrincipalDeterminantOne K n).range, forall A,
      f (gamma.val * A) = f A)
    (hPeriodsC : HasGodementJacquetVanishingUnipotentPeriods c)
    (hPeriodsF : HasGodementJacquetVanishingUnipotentPeriods f)
    (hMeanC : integral (mu.restrict D0) c = 0) (hMeanF : integral (mu.restrict D0) f = 0)
    (m : Nat) (hm : Module.finrank Real (ReductionArchVector K (Prod (Fin n) (Fin n))) < m)
    (hBound : forall e : ReductionHeightDenom K,
      let s := godementJacquetFullTheta_principalScalarMatrixUnit K n e.val e.property
      let H := godementJacquetFullTheta_archimedeanHeight K n
      Exists (fun M : Real => forall A : ReductionHeightGroup K n, Membership.mem S A ->
        And (norm (c A) * H (s * A.val) 1 ^ m <= M)
          (And (norm (c A) * H 1 (Inv.inv A.val * s) ^ m <= M)
            (And (norm (f A) * H (s * A.val) 1 ^ m <= M)
              (norm (f A) * H 1 (Inv.inv A.val * s) ^ m <= M))))) :
    let Phi := godementJacquetMatrixRectangle K a b phi
    let Psi := godementJacquetSelfDualMatrixFourier K Phi
    Exists (fun D : Set (ReductionHeightGroup K n) => And (MeasurableSet D)
      (And (Set.Subset D S)
        (And (forall A : ReductionHeightGroup K n, ExistsUnique
          (fun gamma : (adelicPrincipalDeterminantOne K n).range => Membership.mem D (gamma.val * A)))
          (forall t : Real, And
            (godementJacquetDoubleThetaIntegral K n (mu.restrict D) Phi c f t =
              godementJacquetInvertibleDoubleThetaIntegral K n (mu.restrict D) Phi c f t)
            (godementJacquetDoubleThetaIntegral K n (mu.restrict D) Psi f c t =
              godementJacquetInvertibleDoubleThetaIntegral K n (mu.restrict D) Psi f c t))))) := by
  let Gamma := (adelicPrincipalDeterminantOne K n).range
  let : Countable Gamma := countable_adelicPrincipalDeterminantOne K n
  choose D hD using exists_measurableFundamentalRepresentatives_subset_of_orbitCover
    Gamma D0 S hD0 hS hUnique0 hCover
  have hFD0 : IsFundamentalDomain Gamma D0 mu :=
    IsFundamentalDomain.mk' hD0.nullMeasurableSet hUnique0
  have hFD : IsFundamentalDomain Gamma D mu :=
    IsFundamentalDomain.mk' hD.1.nullMeasurableSet hD.2.2
  have hCZero : integral (mu.restrict D) c = 0 := (hFD.setIntegral_eq hFD0 hInvariantC).trans hMeanC
  have hFZero : integral (mu.restrict D) f = 0 := (hFD.setIntegral_eq hFD0 hInvariantF).trans hMeanF
  choose d L R hDen using exists_godementJacquetDenominators_constant_on_finiteEntryCover K n S U hU hLeft hRight
  choose M hM using hBound d
  have hCW := integrableOn_godementJacquetThetaWeights_of_boundedOn_reductionSet K n m
    mu S hS hFin d L R hDen.2.2 c hc M (fun A hA => And.intro (hM A hA).1 (hM A hA).2.1)
  have hFW := integrableOn_godementJacquetThetaWeights_of_boundedOn_reductionSet K n m
    mu S hS hFin d L R hDen.2.2 f hf M (fun A hA => (hM A hA).2.2)
  refine Exists.intro D (And.intro hD.1 (And.intro hD.2.1 (And.intro hD.2.2 ?_)))
  exact godementJacquetDoubleThetaIntegrals_eq_invertible_of_weightedRectangles
    K n hn mu D hD.1 hD.2.2 a b hb phi c f hc hf
    hInvariantC hInvariantF hPeriodsC hPeriodsF hCZero hFZero m hm L R hDen.1 hDen.2.1
    (hCW.1.mono_set hD.2.1) (hFW.2.mono_set hD.2.1)
    (hFW.1.mono_set hD.2.1) (hCW.2.mono_set hD.2.1)

end Robin1984.GRH
