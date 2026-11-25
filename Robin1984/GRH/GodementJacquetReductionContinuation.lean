import Robin1984.GRH.GodementJacquetHaarUnimodularity
import Robin1984.GRH.GodementJacquetReductionWeights

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and finite-covolume quotients of locally compact groups.
- Formalization note: Derives square integrability and right Haar invariance for representatives inside a finite-measure reduction cover and applies the checked theta cancellation and Mellin continuation.
- PROVENANCE-END
-/

/-!
# Entire theta Mellins from a reduction cover

Choose representatives in the finite-measure cover. The weighted bounds
imply square integrability and give cancellation of the singular terms.
Positive finite covolume gives right invariance for the Haar measure.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

private abbrev ContinuationReductionFinite (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev ContinuationReductionGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker

private abbrev ContinuationReductionDenom (K : Type*) [Field K] [NumberField K] :=
  Subtype (fun d : RingOfIntegers K => Not (d = 0))

private abbrev ContinuationArchAdele (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

private abbrev ContinuationArchVector (K : Type*) [Field K] (I : Type*) :=
  PiLp 2 (fun _ : I => DedekindZeta.Theta.minkowskiSpace K)

set_option maxHeartbeats 1700000 in
/-- A finite-measure reduction cover and bounded weighted cusp values
supply the two cancellation identities and the square-integrability
inputs for entire continuation and reflection of the theta Mellins. -/
theorem exists_godementJacquetEntireMellin_of_reductionSet
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    [T2Space (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace (AdelicGeneralLinearGroup K (n + 1))]
    [BorelSpace (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableMul (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableMul (ContinuationReductionGroup K (n + 1))]
    [MeasurableInv (ContinuationReductionGroup K (n + 1))]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (ContinuationReductionFinite K)] [BorelSpace (ContinuationReductionFinite K)]
    [MeasurableSpace (ContinuationReductionGroup K (n + 1))] [BorelSpace (ContinuationReductionGroup K (n + 1))]
    [MeasurableSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) (ContinuationArchAdele K))]
    [BorelSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) (ContinuationArchAdele K))]
    (mu : Measure (ContinuationReductionGroup K (n + 1))) [SFinite mu] [mu.IsHaarMeasure]
    [Measure.InnerRegular mu]
    (hMul : Measurable (fun p : Prod (ContinuationReductionGroup K (n + 1))
      (ContinuationReductionGroup K (n + 1)) => p.1 * p.2))
    (D0 S : Set (ContinuationReductionGroup K (n + 1))) (hD0 : MeasurableSet D0) (hS : MeasurableSet S)
    (hUnique0 : forall A : ContinuationReductionGroup K (n + 1), ExistsUnique
      (fun gamma : (adelicPrincipalDeterminantOne K (n + 1)).range => Membership.mem D0 (gamma.val * A)))
    (hCover : forall A : ContinuationReductionGroup K (n + 1), Exists
      (fun gamma : (adelicPrincipalDeterminantOne K (n + 1)).range => Membership.mem S (gamma.val * A)))
    (hFin : mu S < Top.top) (U : Set (ContinuationReductionFinite K)) (hU : IsCompact U)
    (hLeft : forall A : ContinuationReductionGroup K (n + 1), Membership.mem S A ->
      forall i j, Membership.mem U (A.val.val i j).2)
    (hRight : forall B : ContinuationReductionGroup K (n + 1), Membership.mem S B ->
      forall i j, Membership.mem U (B.val.inv i j).2)
    (a : Prod (Fin (n + 1)) (Fin (n + 1)) -> ContinuationReductionFinite K) (b : RingOfIntegers K)
    (hb : Not (b = 0))
    (phi : SchwartzMap (ContinuationArchVector K (Prod (Fin (n + 1)) (Fin (n + 1)))) Complex)
    (c f : ContinuationReductionGroup K (n + 1) -> Complex) (hc : Measurable c) (hf : Measurable f)
    (hInvariantC : forall gamma : (adelicPrincipalDeterminantOne K (n + 1)).range, forall A,
      c (gamma.val * A) = c A)
    (hInvariantF : forall gamma : (adelicPrincipalDeterminantOne K (n + 1)).range, forall A,
      f (gamma.val * A) = f A)
    (hPeriodsC : HasGodementJacquetVanishingUnipotentPeriods c)
    (hPeriodsF : HasGodementJacquetVanishingUnipotentPeriods f)
    (hMeanC : integral (mu.restrict D0) c = 0) (hMeanF : integral (mu.restrict D0) f = 0)
    (m : Nat) (hm : Module.finrank Real (ContinuationArchVector K (Prod (Fin (n + 1)) (Fin (n + 1)))) < m)
    (hBound : forall e : ContinuationReductionDenom K,
      let s := godementJacquetFullTheta_principalScalarMatrixUnit K (n + 1) e.val e.property
      let H := godementJacquetFullTheta_archimedeanHeight K (n + 1)
      Exists (fun M : Real => forall A : ContinuationReductionGroup K (n + 1), Membership.mem S A ->
        And (norm (c A) * H (s * A.val) 1 ^ m <= M)
          (And (norm (c A) * H 1 (Inv.inv A.val * s) ^ m <= M)
            (And (norm (f A) * H (s * A.val) 1 ^ m <= M)
              (norm (f A) * H 1 (Inv.inv A.val * s) ^ m <= M))))) :
    let Phi := godementJacquetMatrixRectangle K a b phi
    let Psi := godementJacquetSelfDualMatrixFourier K Phi
    Exists (fun D : Set (ContinuationReductionGroup K (n + 1)) =>
      let F t := godementJacquetInvertibleDoubleThetaIntegral K (n + 1) (mu.restrict D) Phi c f t
      let G t := godementJacquetInvertibleDoubleThetaIntegral K (n + 1) (mu.restrict D) Psi f c t
      And (MeasurableSet D)
        (And (Set.Subset D S)
          (And (IsFundamentalDomain (adelicPrincipalDeterminantOne K (n + 1)).range D mu)
            (And (Differentiable Complex (godementJacquetLogMellin (n + 1) F))
              (forall s : Complex, godementJacquetLogMellin (n + 1) F s =
                godementJacquetLogMellin (n + 1) G (1 - s)))))) := by
  let k := n + 1
  let G : Type _ := ContinuationReductionGroup K k
  let Gamma := (adelicPrincipalDeterminantOne K k).range
  let : Countable Gamma := countable_adelicPrincipalDeterminantOne K k
  have hk : 0 < k := Nat.zero_lt_succ n
  choose D hD using exists_godementJacquetDoubleThetaCancellation_of_reductionSet K k hk
    mu D0 S hD0 hS hUnique0 hCover hFin U hU hLeft hRight a b hb phi c f hc hf
    hInvariantC hInvariantF hPeriodsC hPeriodsF hMeanC hMeanF m hm hBound
  have hMeas : MeasurableSet D := hD.1
  have hSub : Set.Subset D S := hD.2.1
  have hUnique : forall A : G, ExistsUnique
      (fun gamma : Gamma => Membership.mem D (gamma.val * A)) := hD.2.2.1
  have hFD : IsFundamentalDomain Gamma D mu :=
    IsFundamentalDomain.mk' hMeas.nullMeasurableSet hUnique
  have hMU : Not (mu = 0) := NeZero.ne mu
  have hDpos : 0 < mu D := pos_iff_ne_zero.mpr (hFD.measure_ne_zero hMU)
  have hDfin : mu D < Top.top := (measure_mono hSub).trans_lt hFin
  let V := InfiniteAdeleRing K
  let F0 := ContinuationReductionFinite K
  let mixed : Homeomorph V (mixedEmbedding.mixedSpace K) :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
      continuous_toFun := continuous_heckeInfiniteAdele_mixedSpace (K := K)
      continuous_invFun := continuous_heckeInfiniteAdele_mixedSpace_symm K }
  let : T2Space V := T2Space.of_injective_continuous mixed.injective mixed.continuous
  let : LocallyCompactSpace V := mixed.isClosedEmbedding.locallyCompactSpace
  let : T2Space F0 := by
    let projection (x : F0) (p : HeightOneSpectrum (RingOfIntegers K)) := x p
    exact T2Space.of_injective_continuous
      (show Function.Injective projection from DFunLike.coe_injective)
      (continuous_pi (fun p => RestrictedProduct.continuous_eval p))
  let : LocallyCompactSpace F0 := locallyCompactSpace_heckeFiniteAdeles
  let A := AdeleRing (RingOfIntegers K) K
  let : T2Space A := inferInstanceAs (T2Space (Prod V F0))
  let : LocallyCompactSpace A := inferInstanceAs (LocallyCompactSpace (Prod V F0))
  let J := Matrix (Fin k) (Fin k) A
  let : T2Space J := inferInstanceAs (T2Space (Fin k -> Fin k -> A))
  let : LocallyCompactSpace J := inferInstanceAs (LocallyCompactSpace (Fin k -> Fin k -> A))
  let o : Homeomorph (MulOpposite J) J := MulOpposite.opHomeomorph.symm
  let : LocallyCompactSpace (MulOpposite J) := o.isClosedEmbedding.locallyCompactSpace
  have hUnits : Topology.IsClosedEmbedding (Units.embedProduct J) := Units.isClosedEmbedding_embedProduct
  let : LocallyCompactSpace (AdelicGeneralLinearGroup K k) := hUnits.locallyCompactSpace
  let : LocallyCompactSpace G := (isClosed_adelicDeterminantNormOne K k).locallyCompactSpace
  let : mu.IsMulRightInvariant :=
    isMulRightInvariant_of_measurableFundamentalRepresentatives_finiteMass
      mu Gamma D hMeas hUnique hDpos hDfin
  let e : ContinuationReductionDenom K := Subtype.mk 1 one_ne_zero
  let z := godementJacquetFullTheta_principalScalarMatrixUnit K k e.val e.property
  let H := godementJacquetFullTheta_archimedeanHeight K k
  choose M hM using hBound e
  let C := max M 0
  have hC : 0 <= C := le_max_right _ _
  have hPow (x : G) : 1 <= H (z * x.val) 1 ^ m := by
    rw [<- Real.rpow_natCast]
    exact Real.one_le_rpow (le_max_left _ _) (Nat.cast_nonneg m)
  have hNorm (g : G -> Complex) (hg : forall x : G, Membership.mem D x -> norm (g x) <= C) :
      lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (g x) ^ 2)) < Top.top := by
    have hAE : Filter.Eventually (fun x : G =>
        ENNReal.ofReal (norm (g x) ^ 2) <= ENNReal.ofReal (C ^ 2)) (ae (mu.restrict D)) := by
      filter_upwards [ae_restrict_mem hMeas] with x hx
      apply ENNReal.ofReal_le_ofReal
      rw [pow_two, pow_two]
      exact mul_le_mul (hg x hx) (hg x hx) (norm_nonneg _) hC
    refine (lintegral_mono_ae hAE).trans_lt ?_
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDfin
  have hcI := hNorm c (fun x hx =>
    ((le_mul_of_one_le_right (norm_nonneg (c x)) (hPow x)).trans
      (hM x (hSub hx)).1).trans (le_max_left _ _))
  have hfI := hNorm f (fun x hx =>
    ((le_mul_of_one_le_right (norm_nonneg (f x)) (hPow x)).trans
      (hM x (hSub hx)).2.2.1).trans (le_max_left _ _))
  refine Exists.intro D (And.intro hMeas (And.intro hSub (And.intro hFD ?_)))
  exact godementJacquetInvertibleThetaMellin_entire_and_reflection_of_thetaCancellation
    K n mu D hMeas hUnique hMul a b hb phi c f hc hf hInvariantC hInvariantF hcI hfI
    (fun t => (hD.2.2.2 t).1) (fun t => (hD.2.2.2 t).2)

end Robin1984.GRH
