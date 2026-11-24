import Robin1984.GRH.GodementJacquetThetaDualDecay

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and Mellin transforms of exponentially decaying theta integrals.
- Formalization note: Proves continuity of the dual rectangle, measurability of the theta curve, and entire Mellin continuation with reflection under the two theta cancellation identities.
- PROVENANCE-END
-/

/-!
# Analytic continuation of the adelic theta Mellin integral

Joint continuity of the matrix argument and summability of its rational
terms make the quotient theta curve measurable. Poisson reflection and
rapid decay of the two invertible curves give entire Mellin continuation
when the full and invertible theta integrals agree on both sides.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

private abbrev TestFinite (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev TestIndex (n : Nat) := Prod (Fin n) (Fin n)

/-- The self-dual Fourier transform of an adelic Schwartz rectangle is continuous. -/
theorem continuous_godementJacquetSelfDualMatrixFourier_rectangle
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (TestFinite K)] [BorelSpace (TestFinite K)]
    (a : TestIndex n -> TestFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (PiLp 2 (fun _ : TestIndex n => DedekindZeta.Theta.minkowskiSpace K)) Complex) :
    Continuous (godementJacquetSelfDualMatrixFourier K (godementJacquetMatrixRectangle K a d f)) := by
  choose b hb using exists_godementJacquetSelfDualMatrixFourier_rectangle_eq_sum K n a d hd f
  choose T hT using hb.2
  choose center hc using hT
  choose F hF using hc
  rw [funext hF]
  exact continuous_finsetSum T (fun S _ => continuous_godementJacquetMatrixRectangle K (n := n) (center S) b hb.1 (F S))

private theorem measurable_complex_tsum_of_summable
    {X I : Type*} [MeasurableSpace X] [Countable I]
    (a : I -> X -> Complex) (ha : forall i, Measurable (a i))
    (hs : forall x, Summable (fun i => a i x)) :
    Measurable (fun x => tsum (fun i => a i x)) := by
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset I))
    (fun s => Finset.measurable_sum s (fun i _ => ha i)) ?_
  apply tendsto_pi_nhds.mpr
  intro x
  exact (hs x).hasSum

private abbrev CurveMatrix (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K)

private abbrev CurveGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker

private theorem secondCountableTopology_adelicMatrix
    (K : Type*) [Field K] [NumberField K] (n : Nat) :
    SecondCountableTopology (CurveMatrix K n) := by
  let e : Homeomorph (InfiniteAdeleRing K) (NumberField.mixedEmbedding.mixedSpace K) :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
      continuous_toFun := continuous_heckeInfiniteAdele_mixedSpace (K := K)
      continuous_invFun := continuous_heckeInfiniteAdele_mixedSpace_symm K }
  let : SecondCountableTopology (InfiniteAdeleRing K) := e.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (TestFinite K) := secondCountableTopology_heckeFiniteAdeles K
  exact inferInstanceAs
    (SecondCountableTopology (Fin n -> Fin n -> Prod (InfiniteAdeleRing K) (TestFinite K)))

set_option maxHeartbeats 450000 in
/-- The time-parameter integral of a countably indexed matrix theta
series is measurable when the terms are summable and the data are measurable. -/
theorem measurable_godementJacquetThetaCurve
    (K : Type*) [Field K] [NumberField K] (n : Nat) (I : Type*) [Countable I]
    [MeasurableSpace (CurveGroup K n)] [BorelSpace (CurveGroup K n)]
    [MeasurableSpace (CurveMatrix K n)] [BorelSpace (CurveMatrix K n)]
    (nu : Measure (CurveGroup K n)) [SFinite nu]
    (P : I -> Matrix (Fin n) (Fin n) K)
    (Phi : CurveMatrix K n -> Complex) (hPhi : Measurable Phi)
    (c f : CurveGroup K n -> Complex) (hc : Measurable c) (hf : Measurable f)
    (hs : forall t A B, Summable (fun i : I => godementJacquetDoubleThetaTerm K n Phi t A B (P i))) :
    Measurable (fun t : Real => integral (nu.prod nu)
      (fun p : Prod (CurveGroup K n) (CurveGroup K n) =>
        tsum (fun i : I => godementJacquetDoubleThetaTerm K n Phi t p.1 p.2 (P i)) * (c p.1 * f p.2))) := by
  let A := AdeleRing (RingOfIntegers K) K
  let G := CurveGroup K n
  let M := CurveMatrix K n
  let X := Prod Real (Prod G G)
  let val : AdelicGeneralLinearGroup K n -> M := Units.val
  have hVal : Continuous val := @Units.continuous_val (Matrix (Fin n) (Fin n) A) _ _
  let : SecondCountableTopology M := secondCountableTopology_adelicMatrix K n
  let : SecondCountableTopology (MulOpposite M) :=
    (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (AdelicGeneralLinearGroup K n) :=
    (Units.isEmbedding_embedProduct (M := M)).secondCountableTopology
  have hSub : Topology.IsEmbedding (Subtype.val : G -> AdelicGeneralLinearGroup K n) :=
    Topology.IsEmbedding.subtypeVal
  let : SecondCountableTopology G := hSub.secondCountableTopology
  have hL : Continuous (fun x : G => val (Inv.inv x.val)) :=
    hVal.comp (continuous_inv.comp continuous_subtype_val)
  have hR : Continuous (fun x : G => val x.val) := hVal.comp continuous_subtype_val
  have hZ : Continuous (fun t : Real => val (adelicDeterminantSection K n (Multiplicative.ofAdd t))) :=
    hVal.comp (continuous_adelicDeterminantSection K n)
  let Z (i : I) (q : X) := godementJacquetDoubleThetaTerm K n Phi q.1 q.2.1 q.2.2 (P i)
  have hT (i : I) : Measurable (Z i) := by
    let W (q : X) : M :=
      val (Inv.inv q.2.1.val) * val (adelicDeterminantSection K n (Multiplicative.ofAdd q.1)) *
        (P i).map (algebraMap K A) * val q.2.2.val
    have hLeft : Continuous (fun q : X => val (Inv.inv q.2.1.val)) :=
      hL.comp (continuous_fst.comp continuous_snd)
    have hRight : Continuous (fun q : X => val q.2.2.val) :=
      hR.comp (continuous_snd.comp continuous_snd)
    have hTime : Continuous (fun q : X => val (adelicDeterminantSection K n (Multiplicative.ofAdd q.1))) :=
      hZ.comp continuous_fst
    have hW : Continuous W :=
      ((hLeft.mul hTime).mul continuous_const).mul hRight
    change Measurable (Function.comp Phi W)
    exact hPhi.comp hW.measurable
  have hSum : Measurable (fun q : X => tsum (fun i : I => Z i q)) :=
    measurable_complex_tsum_of_summable Z hT (fun q => hs q.1 q.2.1 q.2.2)
  let B (q : X) := tsum (fun i : I => Z i q) * (c q.2.1 * f q.2.2)
  have hB : Measurable B :=
    hSum.mul ((hc.comp (measurable_fst.comp measurable_snd)).mul
      (hf.comp (measurable_snd.comp measurable_snd)))
  have hInt : StronglyMeasurable (fun t : Real => integral (nu.prod nu)
      (fun p : Prod G G => B (Prod.mk t p))) := hB.stronglyMeasurable.integral_prod_right'
  exact hInt.measurable

set_option maxHeartbeats 1000000 in
/-- The Mellin transform of the invertible theta integral of a Schwartz
rectangle is entire and satisfies the Poisson reflection once the full
theta integrals agree with their invertible parts on both sides. -/
theorem godementJacquetInvertibleThetaMellin_entire_and_reflection_of_thetaCancellation
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    [T2Space (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace (AdelicGeneralLinearGroup K (n + 1))]
    [BorelSpace (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableMul (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace (CurveGroup K (n + 1))] [BorelSpace (CurveGroup K (n + 1))]
    [MeasurableMul (CurveGroup K (n + 1))] [MeasurableInv (CurveGroup K (n + 1))]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [MeasurableSpace (CurveMatrix K (n + 1))] [BorelSpace (CurveMatrix K (n + 1))]
    (mu : Measure (CurveGroup K (n + 1))) [mu.IsHaarMeasure] [SFinite mu] [mu.IsMulRightInvariant]
    (D : Set (CurveGroup K (n + 1))) (hD : MeasurableSet D)
    (hUnique : forall x : CurveGroup K (n + 1),
      ExistsUnique (fun gamma : (adelicPrincipalDeterminantOne K (n + 1)).range =>
        Membership.mem D (gamma.val * x)))
    (hMul : Measurable (fun p : Prod (CurveGroup K (n + 1)) (CurveGroup K (n + 1)) => p.1 * p.2))
    (a : Prod (Fin (n + 1)) (Fin (n + 1)) -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (hd : Not (d = 0))
    (phi : SchwartzMap (PiLp 2 (fun _ : TestIndex (n + 1) => DedekindZeta.Theta.minkowskiSpace K)) Complex)
    (c f : CurveGroup K (n + 1) -> Complex) (hc : Measurable c) (hf : Measurable f)
    (hInvC : forall (gamma : (adelicPrincipalDeterminantOne K (n + 1)).range) x, c (gamma.val * x) = c x)
    (hInvF : forall (gamma : (adelicPrincipalDeterminantOne K (n + 1)).range) x, f (gamma.val * x) = f x)
    (hcI : lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (c x) ^ 2)) < (Top.top : ENNReal))
    (hfI : lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (f x) ^ 2)) < (Top.top : ENNReal))
    (hPrimal : forall t : Real,
      let Phi := godementJacquetMatrixRectangle K a d phi
      godementJacquetDoubleThetaIntegral K (n + 1) (mu.restrict D) Phi c f t =
        godementJacquetInvertibleDoubleThetaIntegral K (n + 1) (mu.restrict D) Phi c f t)
    (hDual : forall t : Real,
      let Psi := godementJacquetSelfDualMatrixFourier K (godementJacquetMatrixRectangle K a d phi)
      godementJacquetDoubleThetaIntegral K (n + 1) (mu.restrict D) Psi f c t =
        godementJacquetInvertibleDoubleThetaIntegral K (n + 1) (mu.restrict D) Psi f c t) :
    let Phi := godementJacquetMatrixRectangle K a d phi
    let Psi := godementJacquetSelfDualMatrixFourier K Phi
    let F t := godementJacquetInvertibleDoubleThetaIntegral K (n + 1) (mu.restrict D) Phi c f t
    let G t := godementJacquetInvertibleDoubleThetaIntegral K (n + 1) (mu.restrict D) Psi f c t
    And (Differentiable Complex (godementJacquetLogMellin (n + 1) F))
      (forall s : Complex, godementJacquetLogMellin (n + 1) F s =
        godementJacquetLogMellin (n + 1) G (1 - s)) := by
  let k := n + 1
  let G0 := CurveGroup K k
  let Gamma := Matrix.GeneralLinearGroup (Fin k) K
  let nu := mu.restrict D
  let Phi := godementJacquetMatrixRectangle K a d phi
  let Psi := godementJacquetSelfDualMatrixFourier K Phi
  let F t := godementJacquetInvertibleDoubleThetaIntegral K k nu Phi c f t
  let G t := godementJacquetInvertibleDoubleThetaIntegral K k nu Psi f c t
  have hk : 0 < k := Nat.zero_lt_succ n
  let P (g : Gamma) : Matrix (Fin k) (Fin k) K := g.val
  have hP : Function.Injective P := Units.val_injective
  let : Countable K := (Module.finBasis Rat K).equivFun.injective.countable
  let : Countable (Matrix (Fin k) (Fin k) K) :=
    inferInstanceAs (Countable (Fin k -> Fin k -> K))
  let : Countable Gamma := hP.countable
  have hSP (t : Real) (A B : G0) :
      Summable (fun g : Gamma => godementJacquetDoubleThetaTerm K k Phi t A B (P g)) :=
    (godementJacquetMatrixRectangle_thetaReflection K k hk (Multiplicative.ofAdd t) A B a d hd phi).1.comp_injective hP
  have hSQ (t : Real) (A B : G0) :
      Summable (fun g : Gamma => godementJacquetDoubleThetaTerm K k Psi t A B (P g)) := by
    have h := (godementJacquetMatrixRectangle_thetaReflection K k hk (Multiplicative.ofAdd (-t)) B A a d hd phi).2.1
    change Summable (godementJacquetDoubleThetaTerm K k Psi (-(-t)) A B) at h
    rw [neg_neg] at h
    exact h.comp_injective hP
  have hPhi : Measurable Phi := (continuous_godementJacquetMatrixRectangle K (n := k) a d hd phi).measurable
  have hPsi : Measurable Psi := (continuous_godementJacquetSelfDualMatrixFourier_rectangle K k a d hd phi).measurable
  have hF : Measurable F := measurable_godementJacquetThetaCurve K k Gamma nu P Phi hPhi c f hc hf hSP
  have hG : Measurable G := measurable_godementJacquetThetaCurve K k Gamma nu P Psi hPsi f c hf hc hSQ
  have hRef (t : Real) : F t = ((Real.exp (-((k : Real) * t)) : Real) : Complex) * G (-t) := by
    calc
      _ = godementJacquetDoubleThetaIntegral K k nu Phi c f t := (hPrimal t).symm
      _ = ((Real.exp (-((k : Real) * t)) : Real) : Complex) *
          godementJacquetDoubleThetaIntegral K k nu Psi f c (-t) :=
        godementJacquetDoubleThetaIntegral_reflection K k nu hk t a d hd phi c f
      _ = _ := congrArg
        (fun z : Complex => ((Real.exp (-((k : Real) * t)) : Real) : Complex) * z) (hDual (-t))
  change And (Differentiable Complex (godementJacquetLogMellin k F))
    (forall s : Complex, godementJacquetLogMellin k F s = godementJacquetLogMellin k G (1 - s))
  apply godementJacquetLogMellin_entire_and_reflection_of_decay k F G hF hG hRef
  . intro beta _
    simpa only [neg_mul] using
      exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_squareIntegrable K n
        mu D hD hUnique hMul a d hd phi c f hc hf hInvF hcI hfI beta
  . intro beta _
    simpa only [neg_mul] using
      exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_selfDualFourier_of_squareIntegrable K n
        mu D hD hUnique hMul a d hd phi f c hf hc hInvC hfI hcI beta

end Robin1984.GRH
