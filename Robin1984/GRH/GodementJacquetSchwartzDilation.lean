import Mathlib.LinearAlgebra.Matrix.ToLin
import Robin1984.GRH.GodementJacquetFiniteRectangleDilation
import Robin1984.GRH.GodementJacquetMatrixPoisson

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Schwartz-Bruhat test functions and the Fourier transformation of the theta kernel in Godement and Jacquet, Zeta Functions of Simple Algebras.
- Formalization note: Decomposes an invertible adelic matrix pullback of a Schwartz rectangle into finitely many rectangles and proves the trace-dual transformation with reversed determinant time.
- PROVENANCE-END
-/

/-!
# Schwartz rectangles and the trace-dual dilation

An invertible adelic matrix pulls the joint archimedean Schwartz
factor back along a real continuous linear equivalence. The finite
part decomposes into finitely many disjoint principal rectangles
with one common modulus.

The normalized matrix Fourier transform interchanges the two
determinant-one variables and reverses logarithmic determinant time.
Its measure factor in rank n is exp(-n t).
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K] (I : Type*) [Fintype I]

private abbrev GlobalAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

private abbrev Mixed (K : Type*) [Field K] := mixedEmbedding.mixedSpace K
private abbrev Arch (K : Type*) [Field K] := DedekindZeta.Theta.minkowskiSpace K
private abbrev ArchVector := PiLp 2 (fun _ : I => Arch K)

/-- Send an adele to its mixed archimedean coordinates. -/
def heckeAdeleMixedCoordinate : RingHom (GlobalAdeles K) (Mixed K) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (RingOfIntegers K) K))

/-- The Minkowski coordinates of a vector over the adeles. -/
def heckeAdeleMinkowskiVector (v : I -> GlobalAdeles K) : ArchVector K I :=
  WithLp.toLp 2 (fun i => DedekindZeta.Theta.toMinkowski K (heckeAdeleMixedCoordinate K (v i)))

variable [DecidableEq I]

private def mixedMatrixMulVecCLE (M : Matrix.GeneralLinearGroup I (Mixed K)) :
    ContinuousLinearEquiv (RingHom.id Real) (I -> Mixed K) (I -> Mixed K) where
  toLinearEquiv :=
    { toFun := M.val.mulVec
      invFun := M.inv.mulVec
      left_inv := fun x => by rw [Matrix.mulVec_mulVec, M.inv_val, Matrix.one_mulVec]
      right_inv := fun x => by rw [Matrix.mulVec_mulVec, M.val_inv, Matrix.one_mulVec]
      map_add' := Matrix.mulVec_add M.val
      map_smul' := fun r v => (M.val.mulVecLin.restrictScalars Real).map_smul r v }
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

private def archVectorMixedCoordinates :
    ContinuousLinearEquiv (RingHom.id Real) (ArchVector K I) (I -> Mixed K) :=
  (PiLp.continuousLinearEquiv 2 Real (fun _ : I => Arch K)).trans
    (ContinuousLinearEquiv.piCongrRight (fun _ : I => (DedekindZeta.Theta.toMinkowski K).symm))

/-- An invertible adelic matrix acts by a real continuous linear
equivalence on the joint archimedean Minkowski coordinates. -/
def heckeAdeleArchimedeanMatrixDilation (M : Matrix.GeneralLinearGroup I (GlobalAdeles K)) :
    ContinuousLinearEquiv (RingHom.id Real) (ArchVector K I) (ArchVector K I) :=
  let E := archVectorMixedCoordinates K I
  E.trans ((mixedMatrixMulVecCLE K I (Matrix.GeneralLinearGroup.map (heckeAdeleMixedCoordinate K) M)).trans E.symm)

theorem heckeAdeleMinkowskiVector_mulVec
    (M : Matrix.GeneralLinearGroup I (GlobalAdeles K)) (v : I -> GlobalAdeles K) :
    heckeAdeleMinkowskiVector K I (M.val.mulVec v) =
      heckeAdeleArchimedeanMatrixDilation K I M (heckeAdeleMinkowskiVector K I v) := by
  let e := heckeAdeleMixedCoordinate K
  let T := DedekindZeta.Theta.toMinkowski K
  have h (i : I) :
      e ((M.val.mulVec v) i) = (M.val.map e).mulVec (fun j => e (v j)) i :=
    RingHom.map_mulVec e M.val v i
  apply (PiLp.continuousLinearEquiv 2 Real (fun _ : I => Arch K)).injective
  funext i
  change T (e ((M.val.mulVec v) i)) =
    T ((M.val.map e).mulVec (fun j => (T.symm (T (e (v j))))) i)
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg T (h i)

/-- The archimedean Schwartz factor is closed under an invertible
adelic matrix dilation. -/
def heckeAdeleArchimedeanSchwartzDilation
    (M : Matrix.GeneralLinearGroup I (GlobalAdeles K))
    (f : SchwartzMap (ArchVector K I) Complex) :
    SchwartzMap (ArchVector K I) Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex (heckeAdeleArchimedeanMatrixDilation K I M) f

theorem heckeAdeleArchimedeanSchwartzDilation_apply
    (M : Matrix.GeneralLinearGroup I (GlobalAdeles K))
    (f : SchwartzMap (ArchVector K I) Complex) (v : I -> GlobalAdeles K) :
    heckeAdeleArchimedeanSchwartzDilation K I M f (heckeAdeleMinkowskiVector K I v) =
      f (heckeAdeleMinkowskiVector K I (M.val.mulVec v)) := by
  exact congrArg (f : ArchVector K I -> Complex) (heckeAdeleMinkowskiVector_mulVec K I M v).symm

private theorem indicator_eq_sum_of_disjoint_cover {J X : Type*} [Fintype J]
    (S : Set X) (C : J -> Set X)
    (hCover : S = Set.iUnion C)
    (hDis : forall i j, Not (i = j) -> Disjoint (C i) (C j))
    (x : X) (z : Complex) :
    S.indicator (fun _ => z) x = Finset.univ.sum (fun i => (C i).indicator (fun _ => z) x) := by
  by_cases hx : Membership.mem S x
  case pos =>
    have hu : Membership.mem (Set.iUnion C) x := by rw [<- hCover]; exact hx
    choose i hi using Set.mem_iUnion.mp hu
    rw [Set.indicator_of_mem hx, Finset.sum_eq_single i]
    . rw [Set.indicator_of_mem hi]
    . intro j _ hj
      exact Set.indicator_of_notMem (fun h => Set.disjoint_left.mp (hDis j i hj) h hi) _
    . intro hn
      exact False.elim (hn (Finset.mem_univ i))
  case neg =>
    rw [Set.indicator_of_notMem hx]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i _
    exact Set.indicator_of_notMem (fun h => hx (by
      rw [hCover]
      exact Set.mem_iUnion.mpr (Exists.intro i h))) _

private abbrev FiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev MatrixEntryIndex (n : Nat) := Prod (Fin n) (Fin n)

private theorem godementJacquetMatrixRectangle_eq_indicator {n : Nat}
    (a : MatrixEntryIndex n -> FiniteAdeles K) (d : RingOfIntegers K)
    (f : SchwartzMap (ArchVector K (MatrixEntryIndex n)) Complex)
    (X : Matrix (Fin n) (Fin n) (GlobalAdeles K)) :
    let dd := algebraMap (RingOfIntegers K) K d
    let v := fun i : MatrixEntryIndex n => (X.vec i).2
    godementJacquetMatrixRectangle K a d f X =
      (finiteAdelePrincipalRectangle K (MatrixEntryIndex n) a dd).indicator
        (fun _ => f (heckeAdeleMinkowskiVector K (MatrixEntryIndex n) X.vec)) v := by
  let J := MatrixEntryIndex n
  let dd := algebraMap (RingOfIntegers K) K d
  let v := fun i : J => (X.vec i).2
  let S := finiteAdelePrincipalRectangle K J a dd
  let C (i : J) := heckeFiniteAdelePrincipalCoset (a i) dd
  let g := f (heckeAdeleMinkowskiVector K J X.vec)
  let p (i : J) := (C i).indicator (fun _ => (1 : Complex)) (v i)
  change g * Finset.univ.prod p = S.indicator (fun _ => g) v
  have hx : Membership.mem S v <-> forall i, Membership.mem (C i) (v i) :=
    mem_finiteAdelePrincipalRectangle_iff K J a v dd
  by_cases h : Membership.mem S v
  case pos =>
    have hp (i : J) : p i = 1 := Set.indicator_of_mem (hx.mp h i) _
    rw [Set.indicator_of_mem h]
    simp only [hp, Finset.prod_const_one, mul_one]
  case neg =>
    choose i hi using not_forall.mp (fun hAll => h (hx.mpr hAll))
    have hz : p i = 0 := Set.indicator_of_notMem hi _
    have hp : Finset.univ.prod p = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [Set.indicator_of_notMem h, hp, mul_zero]

/-- An invertible matrix acting on the adelic entry vector carries a
Schwartz rectangle to a finite sum of Schwartz rectangles. The
summands have one common modulus and one joint archimedean factor. -/
theorem exists_godementJacquetMatrixRectangle_dilate_sum {n : Nat}
    (M : Matrix.GeneralLinearGroup (MatrixEntryIndex n) (GlobalAdeles K))
    (a : MatrixEntryIndex n -> FiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (ArchVector K (MatrixEntryIndex n)) Complex) :
    Exists (fun b : RingOfIntegers K => And (Not (b = 0))
      (Exists (fun r : Nat => Exists (fun c : Fin r -> MatrixEntryIndex n -> FiniteAdeles K =>
        Exists (fun g : SchwartzMap (ArchVector K (MatrixEntryIndex n)) Complex =>
          forall X : Matrix (Fin n) (Fin n) (GlobalAdeles K),
            godementJacquetMatrixRectangle K a d f
              (godementJacquetMatrixFromVec (M.val.mulVec X.vec)) =
                Finset.univ.sum (fun i => godementJacquetMatrixRectangle K (c i) b g X)))))) := by
  let J := MatrixEntryIndex n
  let : Fintype J := inferInstanceAs (Fintype (MatrixEntryIndex n))
  let : DecidableEq J := inferInstanceAs (DecidableEq (MatrixEntryIndex n))
  let e := algebraMap (RingOfIntegers K) K
  let q := RingHom.snd (InfiniteAdeleRing K) (FiniteAdeles K)
  let D := Matrix.GeneralLinearGroup.map q M
  let S := Set.preimage D.val.mulVec (finiteAdelePrincipalRectangle K J a (e d))
  choose b hb using exists_disjoint_principalRectangles_mulVec_preimage K J D a d hd
  choose T hT using hb.2
  let r := Fintype.card T
  let E : Equiv (Fin r) T := (Fintype.equivFin T).symm
  choose c hc using fun C : T => hT.1 C.val C.property
  let g := heckeAdeleArchimedeanSchwartzDilation K J M f
  let C (i : Fin r) := (E i).val
  have hUnion : S = Set.iUnion (fun A : Set (J -> FiniteAdeles K) =>
      Set.iUnion (fun _ : Membership.mem T A => A)) := hT.2.2
  have hCover : S = Set.iUnion C := by
    rw [hUnion]
    apply Set.ext
    intro y
    constructor
    . intro hy
      choose A hA using Set.mem_iUnion.mp hy
      choose hAT hyA using Set.mem_iUnion.mp hA
      let t : T := Subtype.mk A hAT
      refine Set.mem_iUnion.mpr (Exists.intro (E.symm t) ?_)
      change Membership.mem ((E (E.symm t)).val) y
      rw [E.apply_symm_apply]
      exact hyA
    . intro hy
      choose i hi using Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr (Exists.intro (E i).val (Set.mem_iUnion.mpr
        (Exists.intro (E i).property hi)))
  have hDis (i j : Fin r) (hij : Not (i = j)) : Disjoint (C i) (C j) :=
    hT.2.1 (E i).val (E i).property (E j).val (E j).property
      (fun h => hij (E.injective (Subtype.ext h)))
  refine Exists.intro b (And.intro hb.1 (Exists.intro r (Exists.intro (fun i => c (E i)) (Exists.intro g ?_))))
  intro X
  let v := fun i : J => (X.vec i).2
  let z := g (heckeAdeleMinkowskiVector K J X.vec)
  let Y := godementJacquetMatrixFromVec (M.val.mulVec X.vec)
  have hY : Y.vec = M.val.mulVec X.vec := godementJacquetMatrixFromVec_vec _
  have hArch : f (heckeAdeleMinkowskiVector K J Y.vec) = z := by
    rw [hY]
    exact (heckeAdeleArchimedeanSchwartzDilation_apply K J M f X.vec).symm
  have hFin : (fun i : J => (Y.vec i).2) = D.val.mulVec v := by
    rw [hY]
    funext i
    exact RingHom.map_mulVec q M.val X.vec i
  have hL : godementJacquetMatrixRectangle K a d f Y = S.indicator (fun _ => z) v := by
    let P := finiteAdelePrincipalRectangle K J a (e d)
    have h := godementJacquetMatrixRectangle_eq_indicator K a d f Y
    have hArch' := congrArg (fun w : Complex => P.indicator (fun _ => w) (fun i : J => (Y.vec i).2)) hArch
    have hFin' := congrArg (P.indicator (fun _ => z)) hFin
    exact h.trans (hArch'.trans hFin')
  have hTerm (i : Fin r) :
      godementJacquetMatrixRectangle K (c (E i)) b g X = (C i).indicator (fun _ => z) v :=
    (godementJacquetMatrixRectangle_eq_indicator K (c (E i)) b g X).trans
      (congrArg (fun U : Set (J -> FiniteAdeles K) => U.indicator (fun _ => z) v) (hc (E i)).2.symm)
  exact hL.trans ((indicator_eq_sum_of_disjoint_cover S C hCover hDis v z).trans
    (Finset.sum_congr rfl (fun i _ => (hTerm i).symm)))

section FourierCovariance

variable (n : Nat)

private abbrev NormOneGroup :=
  (adelicDeterminantLogNorm K n).ker

/-- Under the matrix trace pairing, inversion of the left and right
dilations interchanges the norm-one elements and reverses logarithmic
determinant time. -/
theorem godementJacquetTraceDualDilation_eq_swap_time
    (t : Multiplicative Real) (a b : NormOneGroup K n)
    (Y : Matrix (Fin n) (Fin n) (GlobalAdeles K)) :
    b.val.inv * Y * (Inv.inv a.val * adelicDeterminantSection K n t).inv =
      (Inv.inv b.val * adelicDeterminantSection K n (Inv.inv t)).val * Y * a.val.val := by
  let z := adelicDeterminantSection K n (Inv.inv t)
  have hInv : (Inv.inv a.val * adelicDeterminantSection K n t).inv = z.val * a.val.val := by
    have hz : z.val = (adelicDeterminantSection K n t).inv :=
      congrArg (fun g : AdelicGeneralLinearGroup K n => g.val)
        (map_inv (adelicDeterminantSection K n) t)
    exact congrArg (fun M => M * a.val.val) hz.symm
  let c := (heckeIdelicExpSection K (Multiplicative.toAdd (Inv.inv t) / (n : Real))).val
  have hComm : Y * z.val = z.val * Y :=
    (Matrix.scalar_commute c (fun w => mul_comm c w) Y).eq.symm
  rw [hInv, <- mul_assoc, mul_assoc b.val.inv Y, hComm, <- mul_assoc]
  rfl

variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
  [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]

/-- The self-dual matrix Fourier transform under determinant-coordinate
dilation. The trace-dual action interchanges the two norm-one elements
and reverses logarithmic determinant time. -/
theorem godementJacquetSelfDualMatrixFourier_thetaDilation
    (hn : 0 < n) (t : Multiplicative Real) (a b : NormOneGroup K n)
    (phi : Matrix (Fin n) (Fin n) (GlobalAdeles K) -> Complex) (hphi : Continuous phi)
    (Y : Matrix (Fin n) (Fin n) (GlobalAdeles K)) :
    let u := Inv.inv a.val * adelicDeterminantSection K n t
    let v := Inv.inv b.val * adelicDeterminantSection K n (Inv.inv t)
    godementJacquetSelfDualMatrixFourier K (fun X => phi (u.val * X * b.val.val)) Y =
      HSMul.hSMul (Real.toNNReal (Real.exp (-((n : Real) * Multiplicative.toAdd t))))
        (godementJacquetSelfDualMatrixFourier K phi (v.val * Y * a.val.val)) := by
  let u := Inv.inv a.val * adelicDeterminantSection K n t
  let v := Inv.inv b.val * adelicDeterminantSection K n (Inv.inv t)
  let r := Real.toNNReal (Real.exp (-((n : Real) * Multiplicative.toAdd t)))
  let c := (Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex)) ^
    Fintype.card (Prod (Fin n) (Fin n))
  have h := godementJacquetMatrixFourier_thetaDilation K hn t a b phi hphi Y
  change godementJacquetMatrixFourier K (fun X => phi (u.val * X * b.val.val)) Y =
    HSMul.hSMul r (godementJacquetMatrixFourier K phi (b.val.inv * Y * u.inv)) at h
  have he : b.val.inv * Y * u.inv = v.val * Y * a.val.val :=
    godementJacquetTraceDualDilation_eq_swap_time K n t a b Y
  have h' : godementJacquetMatrixFourier K (fun X => phi (u.val * X * b.val.val)) Y =
      HSMul.hSMul r (godementJacquetMatrixFourier K phi (v.val * Y * a.val.val)) :=
    h.trans (congrArg (fun X => HSMul.hSMul r (godementJacquetMatrixFourier K phi X)) he)
  change c * godementJacquetMatrixFourier K (fun X => phi (u.val * X * b.val.val)) Y =
    HSMul.hSMul r (c * godementJacquetMatrixFourier K phi (v.val * Y * a.val.val))
  exact (congrArg (fun z : Complex => c * z) h').trans (mul_smul_comm _ _ _)

end FourierCovariance

end Robin1984.GRH
