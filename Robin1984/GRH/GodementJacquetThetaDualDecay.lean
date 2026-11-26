import Robin1984.GRH.GodementJacquetFiniteRectangleFourier
import Robin1984.GRH.GodementJacquetThetaL2Decay

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Fourier closure of adelic Schwartz functions and the positive-time theta estimates in Godement and Jacquet, Zeta Functions of Simple Algebras.
- Formalization note: Proves that the self-dual Fourier transform of a Schwartz rectangle is a finite sum of such rectangles and gives rapid positive-time decay of its invertible theta integral.
- PROVENANCE-END
-/

/-!
# Fourier closure and decay of adelic matrix theta integrals

The Fourier transform of a Schwartz rectangle is a finite sum of Schwartz
rectangles. The archimedean factor uses transpose and conjugation for the
trace pairing, and the finite factor is constant on principal cosets.
Summing the time-zero weight bounds gives rapid positive-time decay of
the dual invertible theta integral for square-integrable quotient functions.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform

section FourierClosure

private abbrev FourierMinkowski (K : Type*) [Field K] := DedekindZeta.Theta.minkowskiSpace K
private abbrev FourierMatrixIndex (n : Nat) := Prod (Fin n) (Fin n)
private abbrev FourierArchVector (K : Type*) [Field K] (n : Nat) := PiLp 2 (fun _ : FourierMatrixIndex n => FourierMinkowski K)

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local instance : SecondCountableTopology (FourierMinkowski K) :=
  (DedekindZeta.Theta.toMinkowski K).symm.toHomeomorph.isEmbedding.secondCountableTopology

local instance : BorelSpace (FourierArchVector K n) := by
  let h : forall _ : FourierMatrixIndex n, BorelSpace (FourierMinkowski K) := fun _ => inferInstance
  let t : forall _ : FourierMatrixIndex n, SecondCountableTopology (FourierMinkowski K) := fun _ => inferInstance
  exact PiLp.borelSpace (p := 2) (X := fun _ : FourierMatrixIndex n => FourierMinkowski K)

/-- The archimedean frequency change for the matrix trace pairing. -/
private def godementJacquetArchFourierSymmetry :
    ContinuousLinearEquiv (RingHom.id Real) (FourierArchVector K n) (FourierArchVector K n) :=
  let e := PiLp.continuousLinearEquiv 2 Real (fun _ : FourierMatrixIndex n => FourierMinkowski K)
  let p := ContinuousLinearEquiv.piCongrLeft Real (fun _ : FourierMatrixIndex n => FourierMinkowski K)
    (Equiv.prodComm (Fin n) (Fin n))
  let c := ContinuousLinearEquiv.piCongrRight (fun _ : FourierMatrixIndex n => DedekindZeta.Theta.conjMink K)
  e.trans (p.trans (c.trans e.symm))

/-- The archimedean factor of the adelic Fourier transform is Schwartz
after the transpose and conjugation in the trace pairing. -/
private theorem exists_godementJacquetArchFourierSchwartz
    (f : SchwartzMap (FourierArchVector K n) Complex) :
    Exists (fun F : SchwartzMap (FourierArchVector K n) Complex =>
      forall Y : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K),
        F (heckeAdeleMinkowskiVector K (FourierMatrixIndex n) Y.vec) =
          FourierTransform.fourier (f : FourierArchVector K n -> Complex)
            (heckeConjMinkowskiVector K (FourierMatrixIndex n)
              (WithLp.toLp 2 (fun i : FourierMatrixIndex n => DedekindZeta.Theta.toMinkowski K
                (InfiniteAdeleRing.ringEquiv_mixedSpace K (Y.vec i.swap).1))))) := by
  refine Exists.intro (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (godementJacquetArchFourierSymmetry K n) (FourierTransform.fourier f)) ?_
  intro Y
  rfl
private abbrev ClosureAdele (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

private abbrev ClosureFinite (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private theorem matrixRectangle_eq_finiteIndicator
    (a : FourierMatrixIndex n -> ClosureFinite K) (d : RingOfIntegers K)
    (f : SchwartzMap (FourierArchVector K n) Complex)
    (Y : Matrix (Fin n) (Fin n) (ClosureAdele K)) :
    godementJacquetMatrixRectangle K a d f Y =
      (finiteAdelePrincipalRectangle K (FourierMatrixIndex n) a (algebraMap (RingOfIntegers K) K d)).indicator
        (fun _ => f (heckeAdeleMinkowskiVector K (FourierMatrixIndex n) Y.vec)) (fun i => (Y.vec i).2) := by
  let e := algebraMap (RingOfIntegers K) K
  let v (i : FourierMatrixIndex n) := (Y.vec i).2
  let C (i : FourierMatrixIndex n) := heckeFiniteAdelePrincipalCoset (a i) (e d)
  let S := finiteAdelePrincipalRectangle K (FourierMatrixIndex n) a (e d)
  let z := f (heckeAdeleMinkowskiVector K (FourierMatrixIndex n) Y.vec)
  let P (i : FourierMatrixIndex n) := (C i).indicator (fun _ => (1 : Complex)) (v i)
  change z * Finset.univ.prod P = S.indicator (fun _ => z) v
  have hRec := mem_finiteAdelePrincipalRectangle_iff K (FourierMatrixIndex n) a v (e d)
  by_cases hv : Membership.mem S v
  . have hP (i : FourierMatrixIndex n) : P i = 1 := Set.indicator_of_mem (hRec.mp hv i) _
    have hProd : Finset.univ.prod P = 1 := by
      calc
        _ = Finset.univ.prod (fun _ : FourierMatrixIndex n => (1 : Complex)) :=
          Finset.prod_congr rfl (fun i _ => hP i)
        _ = _ := Finset.prod_const_one
    rw [hProd, Set.indicator_of_mem hv, mul_one]
  . choose i hi using not_forall.mp (fun h => hv (hRec.mpr h))
    have hP : P i = 0 := Set.indicator_of_notMem hi _
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hP, Set.indicator_of_notMem hv, mul_zero]

variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  [MeasurableSpace (ClosureFinite K)] [BorelSpace (ClosureFinite K)]

/-- The self-dual Fourier transform of a Schwartz rectangle is a finite
sum of Schwartz rectangles with a common nonzero finite modulus. -/
theorem exists_godementJacquetSelfDualMatrixFourier_rectangle_eq_sum
    (a : FourierMatrixIndex n -> ClosureFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (FourierArchVector K n) Complex) :
    Exists (fun b : RingOfIntegers K => And (Not (b = 0))
      (Exists (fun T : Finset (Set (FourierMatrixIndex n -> ClosureFinite K)) =>
        Exists (fun center : Set (FourierMatrixIndex n -> ClosureFinite K) -> FourierMatrixIndex n -> ClosureFinite K =>
          Exists (fun F : Set (FourierMatrixIndex n -> ClosureFinite K) -> SchwartzMap (FourierArchVector K n) Complex =>
            forall Y : Matrix (Fin n) (Fin n) (ClosureAdele K),
              godementJacquetSelfDualMatrixFourier K (godementJacquetMatrixRectangle K a d f) Y =
                T.sum (fun C => godementJacquetMatrixRectangle K (center C) b (F C) Y)))))) := by
  let e := algebraMap (RingOfIntegers K) K
  let C (i : FourierMatrixIndex n) := heckeFiniteAdelePrincipalCoset (a i) (e d)
  let mu := heckeFiniteAdeleHaar (K := K)
  let : LocallyCompactSpace (ClosureFinite K) := locallyCompactSpace_heckeFiniteAdeles
  let : mu.IsAddHaarMeasure := by
    change (heckeFiniteAdeleHaar (K := K)).IsAddHaarMeasure
    unfold heckeFiniteAdeleHaar
    infer_instance
  let G (i : FourierMatrixIndex n) (y : ClosureFinite K) :=
    heckeFiniteFourierIntegral mu ((C i).indicator (fun _ => (1 : Complex))) y
  let P (y : FourierMatrixIndex n -> ClosureFinite K) := Finset.univ.prod (fun i => G i (-(y i.swap)))
  let scale := (Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex)) ^ Fintype.card (FourierMatrixIndex n)
  choose g hg using exists_godementJacquetArchFourierSchwartz K n f
  choose b hb using exists_finiteFourierRectangle_indicator_expansion K (FourierMatrixIndex n)
    mu a d hd (Equiv.prodComm (Fin n) (Fin n))
  choose T hT using hb.2
  choose center hc using hT
  let F (S : Set (FourierMatrixIndex n -> ClosureFinite K)) := HSMul.hSMul (scale * P (center S)) g
  refine Exists.intro b (And.intro hb.1 (Exists.intro T (Exists.intro center (Exists.intro F ?_))))
  intro Y
  let v (i : FourierMatrixIndex n) : ClosureFinite K := (Y.vec i).2
  let w := heckeAdeleMinkowskiVector K (FourierMatrixIndex n) Y.vec
  rw [godementJacquetSelfDualMatrixFourier_rectangle_apply, <- hg Y]
  change (scale * g w) * P v = T.sum (fun S => godementJacquetMatrixRectangle K (center S) b (F S) Y)
  have hP : P v = T.sum (fun S => S.indicator (fun _ => P (center S)) v) := hc.2 v
  rw [hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [matrixRectangle_eq_finiteIndicator K n]
  let Q := finiteAdelePrincipalRectangle K (FourierMatrixIndex n) (center S) (e b)
  have hInd : S.indicator (fun _ => P (center S)) v =
      Q.indicator (fun _ => P (center S)) v :=
    congrArg (fun U : Set (FourierMatrixIndex n -> ClosureFinite K) => U.indicator (fun _ => P (center S)) v) (hc.1 S hS)
  rw [hInd]
  change (scale * g w) * Q.indicator (fun _ => P (center S)) v =
    Q.indicator (fun _ => F S w) v
  by_cases hv : Membership.mem Q v
  . rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
    change (scale * g w) * P (center S) = (scale * P (center S)) * g w
    ring
  . rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, mul_zero]

end FourierClosure

private abbrev VolumeArchSpace (K : Type*) [Field K] (n : Nat) :=
  PiLp 2 (fun _ : Prod (Fin n) (Fin n) => DedekindZeta.Theta.minkowskiSpace K)

private abbrev VolumeNormOne (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker

/-- A finite sum of Schwartz rectangles has rapid positive-time decay in
the invertible theta integral for square-integrable quotient functions. -/
theorem exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_finite_rectangle_sum
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
    {J : Type*} (T : Finset J)
    (a : J -> Prod (Fin (n + 1)) (Fin (n + 1)) -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (hd : Not (d = 0))
    (phi : J -> SchwartzMap (VolumeArchSpace K (n + 1)) Complex)
    (c f : VolumeNormOne K (n + 1) -> Complex) (hc : Measurable c) (hf : Measurable f)
    (hInv : forall (gamma : (adelicPrincipalDeterminantOne K (n + 1)).range) x, f (gamma.val * x) = f x)
    (hcI : lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (c x) ^ 2)) < (Top.top : ENNReal))
    (hfI : lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (f x) ^ 2)) < (Top.top : ENNReal))
    (b : Real) :
    Exists (fun M : Real => forall t : Real, 0 <= t ->
      norm (godementJacquetInvertibleDoubleThetaIntegral K (n + 1) (mu.restrict D)
        (fun X => T.sum (fun i => godementJacquetMatrixRectangle K (a i) d (phi i) X)) c f t) <=
        M * Real.exp (-(b * t))) := by
  let k := n + 1
  let G := VolumeNormOne K k
  let E := VolumeArchSpace K k
  let nu := mu.restrict D
  let nu2 := nu.prod nu
  let F (j : J) := godementJacquetMatrixRectangle K (a j) d (phi j)
  let Fsum X := T.sum (fun j => F j X)
  let W (p : Prod G G) := norm (c p.1 * f p.2)
  let hK : 0 < k := Nat.zero_lt_succ _
  choose m0 hm0 using fun j : J =>
    exists_godementJacquetThetaGroupWeight_integrabilityThreshold K n mu (a j) d
  let m (j : J) := max (m0 j) (Module.finrank Real E + 1)
  have hm (j : J) : Module.finrank Real E < m j :=
    (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  let w (j : J) (p : Prod G G) :=
    godementJacquetInvertibleThetaTimeZeroWeight K k (m j) (a j) d p.1 p.2
  let z (j : J) (t : Real) (p : Prod G G) (P : Matrix.GeneralLinearGroup (Fin k) K) :=
    godementJacquetDoubleThetaTerm K k (F j) t p.1 p.2 P.val
  choose Q hQ using fun j : J =>
    exists_godementJacquetMatrixRectangle_le_archWeight K k hK (a j) d (phi j) (m j) b
  let H (j : J) (p : Prod G G) := Q j * (tsum (w j p) * W p)
  have hI (j : J) : Integrable (H j) nu2 := by
    have hw := hm0 j (m j) (le_max_left _ _)
    exact (integrable_godementJacquetInvertibleThetaTimeZeroWeight_of_groupWeight K k
      hK mu D hD hUnique hMul (a j) d hd (m j) (hm j) hw.1 hw.2 c f hc hf hInv hcI hfI).const_mul (Q j)
  let U (p : Prod G G) := T.sum (fun j => H j p)
  have hU : Integrable U nu2 := integrable_finsetSum T (fun j _ => hI j)
  have hEach (j : J) (t : Real) (ht : 0 <= t) (p : Prod G G) :
      And (Summable (z j t p))
        (norm (tsum (z j t p)) <= Real.exp (-(b * t)) * (Q j * tsum (w j p))) := by
    let L := Q j * Real.exp (-(b * t))
    have hL : 0 <= L := mul_nonneg (hQ j).1 (Real.exp_nonneg _)
    have hw : Summable (w j p) :=
      summable_godementJacquetInvertibleThetaTimeZeroWeight K k hK (a j) d hd (m j) (hm j) p.1 p.2
    have hPoint (P : Matrix.GeneralLinearGroup (Fin k) K) :
        norm (z j t p P) <= L * w j p P :=
      ((hQ j).2 t ht p.1 p.2 P).trans
        (mul_le_mul_of_nonneg_left
          (godementJacquetInvertibleThetaArchWeight_le_timeZeroWeight K k (m j) (a j) d
            (phi j) t ht p.1 p.2 P) hL)
    have hwL : Summable (fun P => L * w j p P) := hw.mul_left L
    have hz : Summable (fun P => norm (z j t p P)) :=
      Summable.of_nonneg_of_le (fun P => norm_nonneg (z j t p P)) hPoint hwL
    refine And.intro hz.of_norm ?_
    calc
      _ <= tsum (fun P => norm (z j t p P)) := norm_tsum_le_tsum_norm hz
      _ <= tsum (fun P => L * w j p P) := hz.tsum_le_tsum hPoint hwL
      _ = L * tsum (w j p) := tsum_mul_left
      _ = _ := by simp only [L]; ring
  refine Exists.intro (integral nu2 U) ?_
  intro t ht
  let e := Real.exp (-(b * t))
  have hBound (p : Prod G G) :
      norm (godementJacquetInvertibleDoubleThetaSeries K k Fsum t p.1 p.2 *
        (c p.1 * f p.2)) <= e * U p := by
    have hEq : godementJacquetInvertibleDoubleThetaSeries K k Fsum t p.1 p.2 =
        T.sum (fun j => tsum (z j t p)) := by
      change tsum (fun P => T.sum (fun j => z j t p P)) = _
      exact Summable.tsum_finsetSum (fun j _ => (hEach j t ht p).1)
    rw [hEq, norm_mul]
    calc
      _ <= T.sum (fun j => norm (tsum (z j t p))) * W p :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
      _ = T.sum (fun j => norm (tsum (z j t p)) * W p) := Finset.sum_mul _ _ _
      _ <= T.sum (fun j => e * H j p) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ <= (e * (Q j * tsum (w j p))) * W p :=
            mul_le_mul_of_nonneg_right (hEach j t ht p).2 (norm_nonneg _)
          _ = _ := by simp only [H]; ring
      _ = e * U p := (Finset.mul_sum _ _ _).symm
  calc
    _ <= integral nu2 (fun p => e * U p) :=
      norm_integral_le_of_norm_le (hU.const_mul e) (Filter.Eventually.of_forall hBound)
    _ = e * integral nu2 U := integral_const_mul _ _
    _ = _ := mul_comm _ _

/-- The invertible theta integral of the self-dual Fourier transform of
a Schwartz rectangle decays at every positive-time exponential rate for
square-integrable quotient functions. -/
theorem exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_selfDualFourier_of_squareIntegrable
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    [T2Space (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace (AdelicGeneralLinearGroup K (n + 1))]
    [BorelSpace (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableMul (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace (VolumeNormOne K (n + 1))] [BorelSpace (VolumeNormOne K (n + 1))]
    [MeasurableMul (VolumeNormOne K (n + 1))] [MeasurableInv (VolumeNormOne K (n + 1))]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
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
        (godementJacquetSelfDualMatrixFourier K (godementJacquetMatrixRectangle K a d phi)) c f t) <= M * Real.exp (-(b * t))) := by
  choose d' hd' using exists_godementJacquetSelfDualMatrixFourier_rectangle_eq_sum K (n + 1) a d hd phi
  choose T hT using hd'.2
  choose a' ha' using hT
  choose phi' hphi' using ha'
  rw [funext hphi']
  exact exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_finite_rectangle_sum K n
    mu D hD hUnique hMul T a' d' hd'.1 phi' c f hc hf hInv hcI hfI b

end Robin1984.GRH
