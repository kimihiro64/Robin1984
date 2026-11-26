import Robin1984.GRH.GodementJacquetHaarVolume
import Robin1984.GRH.GodementJacquetThetaKernel

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and the square-integrability bound on the unfolded quotient integral.
- Formalization note: Proves rapid positive-time decay of the invertible theta integral for a Schwartz rectangle and square-integrable quotient functions.
- PROVENANCE-END
-/

/-!
# Positive-time theta decay for square-integrable quotient functions

The dyadic Haar volume bound makes sufficiently high reciprocal powers of the archimedean radius integrable on a finite rectangle. Unfolding the time-zero lattice sum and using square-integrability of the quotient functions gives rapid positive-time decay for the invertible theta integral.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

private abbrev VolumeArchSpace (K : Type*) [Field K] (n : Nat) :=
  PiLp 2 (fun _ : Prod (Fin n) (Fin n) => DedekindZeta.Theta.minkowskiSpace K)

private abbrev VolumeNormOne (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker

/-- The archimedean matrix coordinates depend continuously on the
adelic matrix in its unit-group topology. -/
theorem continuous_godementJacquetArchMatrixVector
    (K : Type*) [Field K] [NumberField K] (n : Nat) :
    Continuous (godementJacquetArchMatrixVector K n) := by
  let G := AdelicGeneralLinearGroup K n
  let A := AdeleRing (RingOfIntegers K) K
  let I := Prod (Fin n) (Fin n)
  let f (x : A) := DedekindZeta.Theta.toMinkowski K (heckeAdeleMixedCoordinate K x)
  have hF : Continuous f := (DedekindZeta.Theta.toMinkowski K).continuous.comp
    ((continuous_heckeInfiniteAdele_mixedSpace (K := K)).comp continuous_fst)
  have hVal : Continuous (fun g : G => (g.val : Matrix (Fin n) (Fin n) A)) :=
    @Units.continuous_val (Matrix (Fin n) (Fin n) A) _ _
  have hEntry (i : I) : Continuous (fun g : G => g.val i.2 i.1) :=
    (continuous_apply i.1).comp ((continuous_apply i.2).comp hVal)
  have hV : Continuous (fun g : G => fun i : I => f (g.val i.2 i.1)) :=
    continuous_pi (fun i => hF.comp (hEntry i))
  exact (PiLp.continuousLinearEquiv 2 Real (fun _ : I => DedekindZeta.Theta.minkowskiSpace K)).symm.continuous.comp hV

private theorem measurableSet_normOneThetaFiniteSupport
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    [MeasurableSpace (VolumeNormOne K n)] [BorelSpace (VolumeNormOne K n)]
    (a : Prod (Fin n) (Fin n) -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) :
    MeasurableSet (Set.ofPred (fun g : VolumeNormOne K n =>
      Membership.mem (finiteAdelePrincipalRectangle K (Prod (Fin n) (Fin n)) a
        (algebraMap (RingOfIntegers K) K d)) (fun i => (g.val.val.vec i).2))) := by
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let G := VolumeNormOne K n
  let I := Prod (Fin n) (Fin n)
  let P := HeightOneSpectrum (RingOfIntegers K)
  let projection (v : F) (p : P) : p.adicCompletion K := v p
  have hinj : Function.Injective projection := DFunLike.coe_injective
  have hc : Continuous projection := continuous_pi (fun p => RestrictedProduct.continuous_eval p)
  let _ : T2Space F := T2Space.of_injective_continuous hinj hc
  let A := AdeleRing (RingOfIntegers K) K
  let f (g : G) (i : I) : F := (g.val.val.vec i).2
  have hVal : Continuous (fun g : G => (g.val.val : Matrix (Fin n) (Fin n) A)) :=
    (@Units.continuous_val (Matrix (Fin n) (Fin n) A) _ _).comp continuous_subtype_val
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    change Continuous (fun g : G => (g.val.val i.2 i.1).2)
    exact continuous_snd.comp ((continuous_apply i.1).comp
      ((continuous_apply i.2).comp hVal))
  have hClosed := (isCompact_finiteAdelePrincipalRectangle K I a (algebraMap (RingOfIntegers K) K d)).isClosed
  exact (hClosed.preimage hf).measurableSet

/-- Every sufficiently high reciprocal power of the archimedean radius
is integrable against Haar measure on the fixed finite support. -/
theorem exists_godementJacquetThetaGroupWeight_integrabilityThreshold
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    [T2Space (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace (AdelicGeneralLinearGroup K (n + 1))]
    [BorelSpace (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableMul (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace (VolumeNormOne K (n + 1))] [BorelSpace (VolumeNormOne K (n + 1))]
    (mu : Measure (VolumeNormOne K (n + 1))) [mu.IsHaarMeasure] [SFinite mu]
    (a : Prod (Fin (n + 1)) (Fin (n + 1)) -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) :
    Exists (fun m0 : Nat => forall m : Nat, m0 <= m ->
      And (Measurable (godementJacquetThetaGroupWeight K (n + 1) m a d))
        (lintegral mu (godementJacquetThetaGroupWeight K (n + 1) m a d) < (Top.top : ENNReal))) := by
  let k := n + 1
  let G := VolumeNormOne K k
  let I := Prod (Fin k) (Fin k)
  let S := Set.ofPred (fun g : G => Membership.mem
    (finiteAdelePrincipalRectangle K I a (algebraMap (RingOfIntegers K) K d)) (fun i => (g.val.val.vec i).2))
  let r (g : G) := norm (godementJacquetArchMatrixVector K k g.val)
  have hS : MeasurableSet S := measurableSet_normOneThetaFiniteSupport K k a d
  have hr : Measurable r :=
    ((continuous_godementJacquetArchMatrixVector K k).comp continuous_subtype_val).norm.measurable
  choose B q hB using exists_godementJacquetNormOneThetaBall_dyadicHaarBound K n mu a d
  have hVol (l : Nat) :
      mu (S.inter (Set.preimage r (Set.Iic ((2 : Real) ^ (l + 1))))) <= ENNReal.ofReal (B * q ^ l) := by
    have he : S.inter (Set.preimage r (Set.Iic ((2 : Real) ^ (l + 1)))) =
        godementJacquetNormOneThetaBall K k a d ((2 : Real) ^ (l + 1)) := by
      ext g
      exact and_comm
    rw [he]
    exact hB.2.2 l
  choose m0 hm0 using pow_unbounded_of_one_lt q (by norm_num : (1 : Real) < 2)
  refine Exists.intro m0 (fun m hm => ?_)
  have hRatio : q / (2 : Real) ^ m < 1 := by
    have h2 : (1 : Real) <= 2 := by norm_num
    have hpow : (2 : Real) ^ m0 <= (2 : Real) ^ m := by gcongr
    exact (div_lt_one (by positivity)).mpr (hm0.trans_le hpow)
  refine And.intro ?_
    (lintegral_godementJacquetThetaGroupWeight_lt_top_of_dyadicVolumeBound K k m mu a d B q
      hB.1 hB.2.1 hRatio hS hr hVol)
  change Measurable (fun g : G => ENNReal.ofReal (if Membership.mem S g then
    Inv.inv (max 1 (r g) ^ m) else 0))
  exact (Measurable.ite hS (((measurable_const.max hr).pow_const m).inv) measurable_const).ennreal_ofReal

/-- The positive-time invertible theta integral decays at every
exponential rate for square-integrable quotient functions and a Schwartz
rectangle, using Haar measure on the norm-one group. -/
theorem exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_squareIntegrable
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    [T2Space (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace (AdelicGeneralLinearGroup K (n + 1))]
    [BorelSpace (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableMul (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace (VolumeNormOne K (n + 1))] [BorelSpace (VolumeNormOne K (n + 1))]
    [MeasurableMul (VolumeNormOne K (n + 1))] [MeasurableInv (VolumeNormOne K (n + 1))]
    (mu : Measure (VolumeNormOne K (n + 1))) [mu.IsHaarMeasure] [SFinite mu] [mu.IsMulRightInvariant]
    (D : Set (VolumeNormOne K (n + 1))) (hD : MeasurableSet D)
    (hUnique : forall x : VolumeNormOne K (n + 1),
      ExistsUnique (fun gamma : (adelicPrincipalDeterminantOne K (n + 1)).range =>
        Membership.mem D (gamma.val * x)))
    (hMul : Measurable (fun p : Prod (VolumeNormOne K (n + 1)) (VolumeNormOne K (n + 1)) => p.1 * p.2))
    (a : Prod (Fin (n + 1)) (Fin (n + 1)) -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (hd : Not (d = 0))
    (phi : SchwartzMap (VolumeArchSpace K (n + 1)) Complex)
    (c f : VolumeNormOne K (n + 1) -> Complex) (hc : Measurable c) (hf : Measurable f)
    (hInv : forall (gamma : (adelicPrincipalDeterminantOne K (n + 1)).range) x, f (gamma.val * x) = f x)
    (hcI : lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (c x) ^ 2)) < (Top.top : ENNReal))
    (hfI : lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (f x) ^ 2)) < (Top.top : ENNReal))
    (b : Real) :
    Exists (fun M : Real => forall t : Real, 0 <= t ->
      norm (godementJacquetInvertibleDoubleThetaIntegral K (n + 1) (mu.restrict D)
        (godementJacquetMatrixRectangle K a d phi) c f t) <= M * Real.exp (-(b * t))) := by
  let k := n + 1
  let E := VolumeArchSpace K k
  choose m0 hm0 using exists_godementJacquetThetaGroupWeight_integrabilityThreshold K n mu a d
  let m := max m0 (Module.finrank Real E + 1)
  have hm : Module.finrank Real E < m :=
    (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  have hw := hm0 m (le_max_left _ _)
  have hI := integrable_godementJacquetInvertibleThetaTimeZeroWeight_of_groupWeight K k
    (Nat.zero_lt_succ _) mu D hD hUnique hMul a d hd m hm hw.1 hw.2 c f hc hf hInv hcI hfI
  exact exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_integrable_timeZeroWeight K k
    (Nat.zero_lt_succ _) (mu.restrict D) a d hd phi c f m hm hI b

end Robin1984.GRH
