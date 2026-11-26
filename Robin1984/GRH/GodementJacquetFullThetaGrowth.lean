import Robin1984.GRH.GodementJacquetThetaDualDecay

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and lattice point bounds for adelic Schwartz functions.
- Formalization note: Supplies a polynomial majorant for the full rational theta series by clearing finite denominators and controlling the archimedean action separately in each variable.
- PROVENANCE-END
-/

/-!
# Growth of the full adelic matrix theta series

The full rational matrix sum includes matrices of every rank. A fixed
Schwartz rectangle gives a uniform finite denominator for its nonzero
values. Transport to the integral lattice bounds the series in terms of
three archimedean dilation norms, one for each of the two quotient
variables and one for the logarithmic determinant parameter.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

private abbrev FullThetaIndex (n : Nat) := Prod (Fin n) (Fin n)
private abbrev FullThetaAdele (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K
private abbrev FullThetaFinite (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K
private abbrev FullThetaGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker
private abbrev FullThetaArchVector (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  PiLp 2 (fun _ : FullThetaIndex n => DedekindZeta.Theta.minkowskiSpace K)

set_option maxHeartbeats 800000 in
/-- Finite denominators for the left coordinate, the test matrix and the
inverse right coordinate give an integral lattice point after multiplying
the rational matrix by their product. This includes singular matrices. -/
theorem godementJacquetFullTheta_integralTransport_of_finiteDenominators
    (K : Type*) [Field K] [NumberField K] (n : Nat) (t : Real)
    (A B : FullThetaGroup K n) (P : Matrix (Fin n) (Fin n) K)
    (dA dX dB : RingOfIntegers K) :
    let e := algebraMap (RingOfIntegers K) K
    let q := (algebraMap K (FullThetaFinite K)).comp e
    let X := (Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t)).val *
      P.map (algebraMap K (FullThetaAdele K)) * B.val.val
    (forall i j : Fin n, Membership.mem (heckeIntegralFiniteAdeles (K := K))
      (q dA * (A.val.val i j).2)) ->
    (forall i j : Fin n, Membership.mem (heckeIntegralFiniteAdeles (K := K))
      (q dX * (X i j).2)) ->
    (forall i j : Fin n, Membership.mem (heckeIntegralFiniteAdeles (K := K))
      (q dB * (B.val.inv i j).2)) ->
    forall i : Prod (Fin n) (Fin n),
      InFiniteAdelePrincipalCoset (0 : FullThetaFinite K) (e 1)
        (e (dA * dX * dB) * P.vec i) := by
  let D := FullThetaAdele K
  let F := FullThetaFinite K
  let R := RingOfIntegers K
  let H := heckeIntegralFiniteAdeles (K := K)
  let e := algebraMap R K
  let f := algebraMap K F
  let p := algebraMap K D
  let q := f.comp e
  let gg : RingHom D F := RingHom.snd (InfiniteAdeleRing K) F
  let Mat := Matrix (Fin n) (Fin n) F
  let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let X := (Inv.inv A.val * z).val * P.map p * B.val.val
  let U := A.val.val.map gg
  let V := B.val.inv.map gg
  let W := X.map gg
  let Q := P.map f
  change (forall i j, Membership.mem H (q dA * U i j)) ->
    (forall i j, Membership.mem H (q dX * W i j)) ->
    (forall i j, Membership.mem H (q dB * V i j)) -> _
  intro hA hX hB
  have hz : z.val.map gg = (1 : Mat) :=
    congrArg (fun Y : Matrix.GeneralLinearGroup (Fin n) F => Y.val)
      (adelicDeterminantSection_map_finite K n t)
  have hW : W = (A.val.inv.map gg) * Q * (B.val.val.map gg) := by
    change (A.val.inv * z.val * P.map p * B.val.val).map gg = _
    simp only [Matrix.map_mul, hz, mul_one, Matrix.map_map]
    rfl
  have hUA : U * (A.val.inv.map gg) = 1 := by
    change A.val.val.map gg * A.val.inv.map gg = _
    rw [<- Matrix.map_mul, A.val.val_inv, Matrix.map_one gg (map_zero gg) (map_one gg)]
  have hBV : (B.val.val.map gg) * V = 1 := by
    change B.val.val.map gg * B.val.inv.map gg = _
    rw [<- Matrix.map_mul, B.val.val_inv, Matrix.map_one gg (map_zero gg) (map_one gg)]
  have hRecover : U * W * V = Q := by
    rw [hW]
    calc
      _ = (U * A.val.inv.map gg) * Q * (B.val.val.map gg * V) := by simp only [mul_assoc]
      _ = _ := by rw [hUA, hBV, one_mul, mul_one]
  let scale (d : R) (Y : Mat) : Mat := HSMul.hSMul (q d) Y
  have hScale : scale dA U * scale dX W * scale dB V = scale (dA * dX * dB) Q := by
    dsimp only [scale]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hRecover, map_mul,
      mul_left_comm, mul_comm]
  let ev (v : HeightOneSpectrum R) : RingHom F (v.adicCompletion K) :=
    { toFun := fun y => y v
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hClosed (Y Z : Mat)
      (hY : forall i j, Membership.mem H (Y i j))
      (hZ : forall i j, Membership.mem H (Z i j))
      (i j : Fin n) : Membership.mem H ((Y * Z) i j) := by
    intro v
    change Membership.mem (v.adicCompletionIntegers K) (ev v ((Y * Z) i j))
    rw [Matrix.mul_apply, map_sum]
    apply (v.adicCompletionIntegers K).toSubring.sum_mem
    intro k _
    rw [map_mul]
    exact (v.adicCompletionIntegers K).toSubring.mul_mem (hY i k v) (hZ k j v)
  have hIntegral (i j : Fin n) : Membership.mem H (scale (dA * dX * dB) Q i j) := by
    rw [<- hScale]
    exact hClosed _ _ (hClosed _ _ hA hX) hB i j
  intro i v
  have h := hIntegral i.2 i.1 v
  let a := algebraMap K (v.adicCompletion K)
  change Membership.mem (v.adicCompletionIntegers K)
    (a (e (dA * dX * dB)) * a (P.vec i)) at h
  rw [<- map_mul] at h
  change Membership.mem (v.adicCompletionIntegers K) ((0 - a (e (dA * dX * dB) * P.vec i)) / a (e 1))
  rw [zero_sub, map_one e, map_one a, div_one]
  exact (v.adicCompletionIntegers K).toSubring.neg_mem h

/-- The finite entries of any adelic matrix admit one common integral
denominator. -/
theorem exists_godementJacquetMatrix_finiteDenominator
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (Y : Matrix (Fin n) (Fin n) (FullThetaAdele K)) :
    let q := (algebraMap K (FullThetaFinite K)).comp (algebraMap (RingOfIntegers K) K)
    Exists (fun d : RingOfIntegers K => And (Not (d = 0))
      (forall i j, Membership.mem (heckeIntegralFiniteAdeles (K := K)) (q d * (Y i j).2))) := by
  choose d hd using exists_principalIntegralMultiple_finiteAdeles K (Prod (Fin n) (Fin n))
    (fun k => (Y.vec k).2)
  exact Exists.intro d (And.intro hd.1 (fun i j => hd.2 (Prod.mk j i)))

/-- Nonzero values of a principal Schwartz rectangle impose a uniform
finite denominator on every entry of the input matrix. -/
theorem exists_godementJacquetMatrixRectangle_finiteDenominator
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (a : Prod (Fin n) (Fin n) -> FullThetaFinite K) (d : RingOfIntegers K)
    (f : SchwartzMap (PiLp 2 (fun _ : Prod (Fin n) (Fin n) =>
      DedekindZeta.Theta.minkowskiSpace K)) Complex) :
    let q := (algebraMap K (FullThetaFinite K)).comp (algebraMap (RingOfIntegers K) K)
    Exists (fun b : RingOfIntegers K => And (Not (b = 0))
      (forall Y : Matrix (Fin n) (Fin n) (FullThetaAdele K),
        Not (godementJacquetMatrixRectangle K a d f Y = 0) ->
        forall i j, Membership.mem (heckeIntegralFiniteAdeles (K := K)) (q b * (Y i j).2))) := by
  let I := Prod (Fin n) (Fin n)
  let F := FullThetaFinite K
  let R := RingOfIntegers K
  let e := algebraMap R K
  let q := (algebraMap K F).comp e
  let T := finiteAdelePrincipalRectangle K I a (e d)
  let S := Set.iUnion (fun i : I => Set.image (fun v : I -> F => v i) T)
  have hS : IsCompact S := isCompact_iUnion fun i : I =>
    (isCompact_finiteAdelePrincipalRectangle K I a (e d)).image (continuous_apply i)
  choose b hb using exists_commonDenominator_of_isCompact_finiteAdeles S hS
  refine Exists.intro b (And.intro hb.1 ?_)
  intro Y hY i j
  let v (k : I) : F := (Y.vec k).2
  let c (k : I) : Set F := heckeFiniteAdelePrincipalCoset (a k) (e d)
  have hv (k : I) : Membership.mem (c k) (v k) := by
    by_contra h
    apply hY
    change f (heckeAdeleMinkowskiVector K I Y.vec) * Finset.prod Finset.univ
      (fun k : I => (c k).indicator (fun _ => (1 : Complex)) (v k)) = 0
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (Set.indicator_of_notMem h _), mul_zero]
  have hT : Membership.mem T v := (mem_finiteAdelePrincipalRectangle_iff K I a v (e d)).mpr hv
  have hMem : Membership.mem S (v (Prod.mk j i)) :=
    Set.mem_iUnion.mpr (Exists.intro (Prod.mk j i) (Exists.intro v (And.intro hT rfl)))
  intro p
  change Membership.mem (p.adicCompletionIntegers K) ((q b) p * v (Prod.mk j i) p)
  have hQ : (q b) p = algebraMap R (p.adicCompletion K) b :=
    (IsScalarTower.algebraMap_apply R K (p.adicCompletion K) b).symm
  rw [hQ, mul_comm]
  exact hb.2 _ hMem p

/-- The principal scalar matrix unit associated to a nonzero integer of K. -/
def godementJacquetFullTheta_principalScalarMatrixUnit
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (d : RingOfIntegers K) (hd : Not (d = 0)) : AdelicGeneralLinearGroup K n :=
  let e := algebraMap (RingOfIntegers K) K
  let p := algebraMap K (FullThetaAdele K)
  let u := Units.mk0 (e d) ((map_ne_zero_iff e
    (FaithfulSMul.algebraMap_injective (RingOfIntegers K) K)).mpr hd)
  Matrix.GeneralLinearGroup.scalar (Fin n) (Units.map p.toMonoidHom u)

/-- The operator norm of an archimedean matrix dilation, bounded below by one. -/
def godementJacquetFullTheta_archimedeanHeight
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (a b : AdelicGeneralLinearGroup K n) : Real :=
  max 1 (norm (heckeAdeleArchimedeanMatrixDilation K (FullThetaIndex n)
    (godementJacquetMatrixDilation a b)).toContinuousLinearMap)

set_option maxHeartbeats 800000 in
/-- Scaling a rational matrix into the integral lattice costs a product of
three archimedean operator norms. The three factors depend separately on the
left and right matrices and the logarithmic determinant parameter. -/
theorem godementJacquetFullTheta_archNorm_le_of_archFactors
    (K : Type*) [Field K] [NumberField K] (n : Nat) (t : Real)
    (A B : FullThetaGroup K n) (P : Matrix (Fin n) (Fin n) K)
    (dA dX dB : RingOfIntegers K)
    (hdA : Not (dA = 0)) (hdX : Not (dX = 0)) (hdB : Not (dB = 0)) :
    let e := algebraMap (RingOfIntegers K) K
    let p := algebraMap K (FullThetaAdele K)
    let sA := godementJacquetFullTheta_principalScalarMatrixUnit K n dA hdA
    let sX := godementJacquetFullTheta_principalScalarMatrixUnit K n dX hdX
    let sB := godementJacquetFullTheta_principalScalarMatrixUnit K n dB hdB
    let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
    let X := (Inv.inv A.val * z).val * P.map p * B.val.val
    let H := godementJacquetFullTheta_archimedeanHeight K n
    norm (heckePrincipalMinkowskiVector K (FullThetaIndex n)
      (fun i => e (dA * dX * dB) * P.vec i)) <=
      (H (sX * Inv.inv z) 1 * H (sA * A.val) 1 * H 1 (Inv.inv B.val * sB)) *
        norm (heckeAdeleMinkowskiVector K (FullThetaIndex n) X.vec) := by
  let R := RingOfIntegers K
  let D := FullThetaAdele K
  let I := FullThetaIndex n
  let e := algebraMap R K
  let p := algebraMap K D
  let sA := godementJacquetFullTheta_principalScalarMatrixUnit K n dA hdA
  let sX := godementJacquetFullTheta_principalScalarMatrixUnit K n dX hdX
  let sB := godementJacquetFullTheta_principalScalarMatrixUnit K n dB hdB
  let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let Y := P.map p
  let X := (Inv.inv A.val * z).val * Y * B.val.val
  let H := godementJacquetFullTheta_archimedeanHeight K n
  let U := sA * A.val
  let V := Inv.inv B.val * sB
  let Z := sX * Inv.inv z
  let F (Q : Matrix (Fin n) (Fin n) D) := heckeAdeleMinkowskiVector K I Q.vec
  have hScalar (d : R) (hd : Not (d = 0)) (Q : Matrix (Fin n) (Fin n) D) :
      (godementJacquetFullTheta_principalScalarMatrixUnit K n d hd).val * Q =
        HSMul.hSMul (p (e d)) Q := by
    change Matrix.scalar (Fin n) (p (e d)) * Q = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hScalarComm (d : R) (hd : Not (d = 0)) (Q : Matrix (Fin n) (Fin n) D) :
      Q * (godementJacquetFullTheta_principalScalarMatrixUnit K n d hd).val =
        (godementJacquetFullTheta_principalScalarMatrixUnit K n d hd).val * Q :=
    (Matrix.scalar_commute (p (e d)) (Commute.all _) Q).eq.symm
  have hXY : A.val.val * (X * B.val.inv) = z.val * Y := by
    change A.val.val * (A.val.inv * z.val * Y * B.val.val * B.val.inv) = _
    calc
      _ = (A.val.val * A.val.inv) * z.val * Y * (B.val.val * B.val.inv) := by
        simp only [mul_assoc]
      _ = _ := by rw [A.val.val_inv, B.val.val_inv, one_mul, mul_one]
  have hInner : z.inv * (sA.val * (z.val * Y)) = sA.val * Y := by
    calc
      _ = (z.inv * sA.val) * (z.val * Y) := (mul_assoc _ _ _).symm
      _ = _ := by
        rw [hScalarComm dA hdA z.inv]
        rw [mul_assoc, <- mul_assoc z.inv, z.inv_val, one_mul]
  have hRecover : Z.val * (U.val * (X * V.val)) =
      P.map (fun x => p (e (dA * dX * dB) * x)) := by
    calc
      _ = sX.val * (z.inv * (sA.val * (A.val.val * (X * B.val.inv))) * sB.val) := by
        simp only [Z, U, V, Units.val_mul, mul_assoc]
        rfl
      _ = sX.val * ((sA.val * Y) * sB.val) := by rw [hXY, hInner]
      _ = sX.val * (sB.val * (sA.val * Y)) := by rw [hScalarComm dB hdB]
      _ = _ := by
        rw [hScalar dA hdA, hScalar dB hdB, hScalar dX hdX, smul_smul, smul_smul]
        apply Matrix.ext
        intro i j
        change (p (e dX) * p (e dB) * p (e dA)) * p (P i j) =
          p (e (dA * dX * dB) * P i j)
        simp only [map_mul, mul_left_comm, mul_comm]
  have hPrincipal : F (P.map (fun x => p (e (dA * dX * dB) * x))) =
      heckePrincipalMinkowskiVector K I (fun i => e (dA * dX * dB) * P.vec i) := by
    apply (PiLp.continuousLinearEquiv 2 Real (fun _ : I => DedekindZeta.Theta.minkowskiSpace K)).injective
    funext i
    let x := e (dA * dX * dB) * P.vec i
    change DedekindZeta.Theta.toMinkowski K
      (InfiniteAdeleRing.ringEquiv_mixedSpace K (algebraMap K (InfiniteAdeleRing K) x)) =
      DedekindZeta.Theta.toMinkowski K (mixedEmbedding K x)
    exact congrArg (DedekindZeta.Theta.toMinkowski K)
      (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := K) (x := x)).symm
  have hBound (a b : AdelicGeneralLinearGroup K n) (Q : Matrix (Fin n) (Fin n) D) :
      norm (F (a.val * Q * b.val)) <= H a b * norm (F Q) := by
    let T := heckeAdeleArchimedeanMatrixDilation K I (godementJacquetMatrixDilation a b)
    have h : F (a.val * Q * b.val) = T (F Q) := by
      change heckeAdeleMinkowskiVector K I (a.val * Q * b.val).vec = _
      rw [<- godementJacquetMatrixDilation_vec a b Q, heckeAdeleMinkowskiVector_mulVec]
    rw [h]
    exact (ContinuousLinearMap.le_opNorm T.toContinuousLinearMap
      (F Q)).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hH (a b : AdelicGeneralLinearGroup K n) : 0 <= H a b :=
    zero_le_one.trans (le_max_left _ _)
  change _ <= (H Z 1 * H U 1 * H 1 V) * norm (F X)
  rw [<- hPrincipal, <- hRecover]
  calc
    _ <= H Z 1 * norm (F (U.val * (X * V.val))) := by
      simpa only [Units.val_one, mul_one] using hBound Z 1 (U.val * (X * V.val))
    _ <= H Z 1 * (H U 1 * norm (F (X * V.val))) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [Units.val_one, mul_one] using hBound U 1 (X * V.val)) (hH _ _)
    _ <= H Z 1 * (H U 1 * (H 1 V * norm (F X))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (by simpa only [Units.val_one, one_mul] using hBound 1 V X) (hH _ _)) (hH _ _)
    _ = _ := by simp only [mul_assoc]

set_option maxHeartbeats 800000 in
/-- An integral-lattice transport with archimedean distortion bound
gives a polynomial absolute bound on the full rational matrix sum,
including singular matrices. The constant is independent of the transport. -/
theorem tsum_ofReal_norm_godementJacquetMatrixRectangle_le_of_integralTransport
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (a : FullThetaIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (f : SchwartzMap (FullThetaArchVector K n) Complex)
    (m : Nat) (hm : Module.finrank Real (FullThetaArchVector K n) < m) :
    Exists (fun C : ENNReal => And (C < Top.top)
      (forall (X : Matrix (Fin n) (Fin n) K -> Matrix (Fin n) (Fin n) (FullThetaAdele K))
        (delta : K) (_ : Not (delta = 0)) (L : Real) (_ : 1 <= L),
        (forall P, Not (godementJacquetMatrixRectangle K a d f (X P) = 0) ->
          forall i : FullThetaIndex n, InFiniteAdelePrincipalCoset
            (0 : FiniteAdeleRing (RingOfIntegers K) K)
            (algebraMap (RingOfIntegers K) K 1) (delta * P.vec i)) ->
        (forall P, Not (godementJacquetMatrixRectangle K a d f (X P) = 0) ->
          norm (heckePrincipalMinkowskiVector K (FullThetaIndex n) (fun i => delta * P.vec i)) <=
            L * norm (heckeAdeleMinkowskiVector K (FullThetaIndex n) (X P).vec)) ->
        tsum (fun P => ENNReal.ofReal (norm (godementJacquetMatrixRectangle K a d f (X P)))) <=
          ENNReal.ofReal (L ^ m) * C)) := by
  let I := FullThetaIndex n
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let e := algebraMap (RingOfIntegers K) K
  let S : Set (I -> K) := Set.ofPred (fun v => forall i : I,
    InFiniteAdelePrincipalCoset (0 : F) (e 1) (v i))
  have hZero (i : I) : InFiniteAdelePrincipalCoset (0 : F) (e 1) ((0 : I -> K) i) := by
    intro p
    change Membership.mem (p.adicCompletionIntegers K)
      ((0 - algebraMap K (p.adicCompletion K) 0) / algebraMap K (p.adicCompletion K) (e 1))
    rw [map_zero, sub_zero, zero_div]
    exact (p.adicCompletionIntegers K).zero_mem
  let zeroS : S := Subtype.mk 0 hZero
  let r (v : I -> K) := norm (heckePrincipalMinkowskiVector K I v)
  let w (v : I -> K) := Inv.inv (max 1 (r v) ^ m)
  let T := S.indicator (fun v => ENNReal.ofReal (w v))
  let q (v : S) := Inv.inv (r v.val) ^ m
  have hq : Summable q :=
    summable_finiteAdelePrincipalVectorCoset_invNormPow K I (fun _ => (0 : F))
      1 one_ne_zero 0 hZero m hm
  have hPos (v : S) (hv : Not (v = zeroS)) : 0 < r v.val := by
    apply norm_pos_iff.mpr
    intro hz
    apply hv
    apply Subtype.ext
    funext i
    have he := congrArg (fun z : FullThetaArchVector K n => z i) hz
    change DedekindZeta.Theta.eEmb K (v.val i) = 0 at he
    have hEmb : Function.Injective (DedekindZeta.Theta.eEmb K) :=
      (DedekindZeta.Theta.toMinkowski K).injective.comp (mixedEmbedding K).injective
    exact hEmb (he.trans (map_zero (DedekindZeta.Theta.eEmbHom K)).symm)
  have hT : tsum T < (Top.top : ENNReal) := by
    let : DecidableEq S := fun x y => Classical.propDecidable (x = y)
    change tsum (S.indicator (fun v => ENNReal.ofReal (w v))) < _
    rw [<- tsum_subtype, ENNReal.tsum_eq_add_tsum_ite zeroS]
    have hz : ENNReal.ofReal (w zeroS.val) <= 1 := by
      have hBase : 1 <= max 1 (r zeroS.val) := le_max_left _ _
      have h : (1 : Real) ^ m <= max 1 (r zeroS.val) ^ m := by gcongr
      rw [one_pow] at h
      rw [<- ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      change Inv.inv (max 1 (r zeroS.val) ^ m) <= 1
      simpa only [one_div, div_one] using one_div_le_one_div_of_le zero_lt_one h
    have hRest (v : S) : (if v = zeroS then 0 else ENNReal.ofReal (w v.val)) <= ENNReal.ofReal (q v) := by
      by_cases hv : v = zeroS
      . simp only [if_pos hv, zero_le]
      . rw [if_neg hv]
        apply ENNReal.ofReal_le_ofReal
        have hp := hPos v hv
        have hMax : r v.val <= max 1 (r v.val) := le_max_right _ _
        have hPower : r v.val ^ m <= max 1 (r v.val) ^ m := by gcongr
        change Inv.inv (max 1 (r v.val) ^ m) <= Inv.inv (r v.val) ^ m
        rw [inv_pow]
        simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hp m) hPower
    have hSum : tsum (fun v : S => if v = zeroS then 0 else ENNReal.ofReal (w v.val)) <=
        ENNReal.ofReal (tsum q) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _) hq]
      exact ENNReal.tsum_le_tsum hRest
    exact (add_le_add hz hSum).trans_lt (ENNReal.add_lt_top.mpr
      (And.intro ENNReal.one_lt_top ENNReal.ofReal_lt_top))
  let A := max (SchwartzMap.seminorm Real 0 0 f) (SchwartzMap.seminorm Real m 0 f)
  have hA : 0 <= A := (apply_nonneg (SchwartzMap.seminorm Real 0 0) f).trans (le_max_left _ _)
  let C := ENNReal.ofReal A * tsum T
  refine Exists.intro C (And.intro (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT) ?_)
  intro X delta hDelta L hL hSupport hArch
  let y (P : Matrix (Fin n) (Fin n) K) : I -> K := fun i => delta * P.vec i
  have hy : Function.Injective y := by
    intro P Q h
    apply Matrix.vec_inj.mp
    funext i
    have hi : delta * P.vec i = delta * Q.vec i := congrFun h i
    have hz : delta * (P.vec i - Q.vec i) = 0 := by rw [mul_sub, hi, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hDelta)
  let J := ENNReal.ofReal (L ^ m) * ENNReal.ofReal A
  have hPt (P : Matrix (Fin n) (Fin n) K) :
      ENNReal.ofReal (norm (godementJacquetMatrixRectangle K a d f (X P))) <= J * T (y P) := by
    let z := godementJacquetMatrixRectangle K a d f (X P)
    let x := heckeAdeleMinkowskiVector K I (X P).vec
    let R := max 1 (r (y P))
    let Q := max 1 (norm x)
    by_cases hz : z = 0
    . simp only [show godementJacquetMatrixRectangle K a d f (X P) = 0 from hz, norm_zero,
        ENNReal.ofReal_zero, zero_le]
    have hYP : Membership.mem S (y P) := hSupport P hz
    have hRQ : R <= L * Q := max_le
      (hL.trans (le_mul_of_one_le_right (zero_le_one.trans hL) (le_max_left 1 (norm x))))
      ((hArch P hz).trans (mul_le_mul_of_nonneg_left (le_max_right 1 (norm x)) (zero_le_one.trans hL)))
    have hPow : R ^ m <= L ^ m * Q ^ m := by rw [<- mul_pow]; gcongr
    have hS : Q ^ m * norm z <= A := by
      calc
        _ <= Q ^ m * norm (f x) :=
          mul_le_mul_of_nonneg_left (norm_godementJacquetMatrixRectangle_le_arch K n a d f (X P)) (by positivity)
        _ <= _ := by
          by_cases hsmall : norm x <= 1
          . change max 1 (norm x) ^ m * norm (f x) <= A
            rw [max_eq_left hsmall, one_pow, one_mul]
            have h0 : norm (f x) <= SchwartzMap.seminorm Real 0 0 f := by
              simpa only [pow_zero, one_mul] using SchwartzMap.norm_pow_mul_le_seminorm Real f 0 x
            exact h0.trans (le_max_left _ _)
          . change max 1 (norm x) ^ m * norm (f x) <= A
            rw [max_eq_right (le_of_not_ge hsmall)]
            exact (SchwartzMap.norm_pow_mul_le_seminorm Real f m x).trans (le_max_right _ _)
    have hBound : norm z * R ^ m <= L ^ m * A := by
      calc
        _ <= norm z * (L ^ m * Q ^ m) := mul_le_mul_of_nonneg_left hPow (norm_nonneg _)
        _ = L ^ m * (Q ^ m * norm z) := by ring
        _ <= _ := mul_le_mul_of_nonneg_left hS (by positivity)
    have hR : R ^ m > 0 := pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _
    have hV : norm z <= (L ^ m * A) * Inv.inv (R ^ m) := by
      calc
        _ = (norm z * R ^ m) * Inv.inv (R ^ m) := by field_simp [hR.ne']
        _ <= _ := mul_le_mul_of_nonneg_right hBound (inv_nonneg.mpr hR.le)
    change ENNReal.ofReal (norm z) <= J * S.indicator (fun v => ENNReal.ofReal (w v)) (y P)
    rw [Set.indicator_of_mem hYP]
    have hLM : 0 <= L ^ m := pow_nonneg (zero_le_one.trans hL) _
    simpa only [J, w, ENNReal.ofReal_mul (mul_nonneg hLM hA), ENNReal.ofReal_mul hLM] using
      ENNReal.ofReal_le_ofReal hV
  calc
    _ <= tsum (fun P => J * T (y P)) := ENNReal.tsum_le_tsum hPt
    _ = J * tsum (fun P => T (y P)) := ENNReal.tsum_mul_left
    _ <= J * tsum T := by
      have h := ENNReal.tsum_comp_le_tsum_of_injective hy T
      gcongr
    _ = _ := mul_assoc _ _ _

set_option maxHeartbeats 800000 in
/-- The absolute sum over all rational matrices has a product majorant
in the two norm-one quotient variables, with a separate determinant factor.
The test rectangle contributes one finite denominator and a finite lattice
constant. Each variable contributes an integral denominator of its own. -/
theorem tsum_ofReal_norm_godementJacquetFullTheta_le_of_finiteDenominators
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (a : FullThetaIndex n -> FullThetaFinite K)
    (d : RingOfIntegers K) (f : SchwartzMap (FullThetaArchVector K n) Complex)
    (m : Nat) (hm : Module.finrank Real (FullThetaArchVector K n) < m) :
    let e := algebraMap (RingOfIntegers K) K
    let p := algebraMap K (FullThetaAdele K)
    let q := (algebraMap K (FullThetaFinite K)).comp e
    let H := godementJacquetFullTheta_archimedeanHeight K n
    let IntDen := Subtype (fun b : RingOfIntegers K => Not (b = 0))
    let s (b : IntDen) := godementJacquetFullTheta_principalScalarMatrixUnit K n b.val b.property
    Exists (fun C : ENNReal => And (C < Top.top) (Exists (fun dX : IntDen =>
      forall (t : Real) (A B : FullThetaGroup K n) (dA dB : IntDen),
        let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
        (forall i j, Membership.mem (heckeIntegralFiniteAdeles (K := K))
          (q dA.val * (A.val.val i j).2)) ->
        (forall i j, Membership.mem (heckeIntegralFiniteAdeles (K := K))
          (q dB.val * (B.val.inv i j).2)) ->
        tsum (fun P : Matrix (Fin n) (Fin n) K =>
          ENNReal.ofReal (norm (godementJacquetMatrixRectangle K a d f
            ((Inv.inv A.val * z).val * P.map p * B.val.val)))) <=
          ENNReal.ofReal ((H (s dX * Inv.inv z) 1 * H (s dA * A.val) 1 *
            H 1 (Inv.inv B.val * s dB)) ^ m) * C))) := by
  choose C hC using tsum_ofReal_norm_godementJacquetMatrixRectangle_le_of_integralTransport K n a d f m hm
  choose dX hdX using exists_godementJacquetMatrixRectangle_finiteDenominator K n a d f
  refine Exists.intro C (And.intro hC.1 (Exists.intro (Subtype.mk dX hdX.1) ?_))
  intro t A B dA dB z hA hB
  let e := algebraMap (RingOfIntegers K) K
  let p := algebraMap K (FullThetaAdele K)
  let H := godementJacquetFullTheta_archimedeanHeight K n
  let sA := godementJacquetFullTheta_principalScalarMatrixUnit K n dA.val dA.property
  let sX := godementJacquetFullTheta_principalScalarMatrixUnit K n dX hdX.1
  let sB := godementJacquetFullTheta_principalScalarMatrixUnit K n dB.val dB.property
  let L := H (sX * Inv.inv z) 1 * H (sA * A.val) 1 * H 1 (Inv.inv B.val * sB)
  let X (P : Matrix (Fin n) (Fin n) K) := (Inv.inv A.val * z).val * P.map p * B.val.val
  have hL1 (U V : AdelicGeneralLinearGroup K n) : 1 <= H U V := le_max_left _ _
  have hL : 1 <= L := by
    change 1 <= H (sX * Inv.inv z) 1 * H (sA * A.val) 1 * H 1 (Inv.inv B.val * sB)
    calc
      1 <= H (sX * Inv.inv z) 1 := hL1 _ _
      _ <= _ * H (sA * A.val) 1 :=
        le_mul_of_one_le_right (zero_le_one.trans (hL1 _ _)) (hL1 _ _)
      _ <= _ * H 1 (Inv.inv B.val * sB) :=
        le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans (hL1 _ _))
          (zero_le_one.trans (hL1 _ _))) (hL1 _ _)
  have hDelta : Not (e (dA.val * dX * dB.val) = 0) :=
    (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective (RingOfIntegers K) K)).mpr
      (mul_ne_zero (mul_ne_zero dA.property hdX.1) dB.property)
  refine hC.2 X (e (dA.val * dX * dB.val)) hDelta L hL ?_ ?_
  . intro P hP
    exact godementJacquetFullTheta_integralTransport_of_finiteDenominators K n t A B P
      dA.val dX dB.val hA (hdX.2 (X P) hP) hB
  . intro P _
    exact godementJacquetFullTheta_archNorm_le_of_archFactors K n t A B P
      dA.val dX dB.val dA.property hdX.1 dB.property

end Robin1984.GRH
