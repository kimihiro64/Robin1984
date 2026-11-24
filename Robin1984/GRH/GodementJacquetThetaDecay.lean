import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finite.Perm
import Robin1984.GRH.GodementJacquetSchwartzDilation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and Schwartz decay of the adelic matrix theta kernel.
- Formalization note: Bounds archimedean and finite determinant norms and derives uniform weighted decay for each invertible term of a Schwartz rectangle.
- PROVENANCE-END
-/

/-!
# Pointwise decay of the invertible Godement-Jacquet theta terms

The determinant of the normalized theta argument has idelic norm exp t.
A compact finite rectangle gives one finite idele bounding all entries
on its support. The archimedean determinant estimate then converts the
Schwartz seminorms into arbitrary exponential decay in t >= 0 with a
prescribed polynomial weight for the archimedean matrix norm.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain
open scoped Classical

private theorem norm_godementJacquet_detTerm_le_pow
    {R : Type*} [NormedField R] (n : Nat) (M : Matrix (Fin n) (Fin n) R)
    (B : Real) (hEntry : forall i j : Fin n, norm (M i j) <= B)
    (p : Equiv.Perm (Fin n)) :
    norm (((Equiv.Perm.sign p : Int) : R) *
      Finset.prod Finset.univ (fun i : Fin n => M (p i) i)) <= B ^ n := by
  have hSign : norm ((Equiv.Perm.sign p : Int) : R) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp
    . simp [hp]
    . simp [hp]
  rw [norm_mul, hSign, one_mul, norm_prod]
  calc
    _ <= Finset.prod Finset.univ (fun _ : Fin n => B) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hEntry (p i) i)
    _ = _ := by simp

/-- The determinant of an n by n matrix is bounded by n! times the nth
power of an upper bound for all its entries. -/
theorem norm_godementJacquet_det_le_factorial_mul_pow
    {R : Type*} [NormedField R] (n : Nat) (M : Matrix (Fin n) (Fin n) R)
    (B : Real) (hEntry : forall i j : Fin n, norm (M i j) <= B) :
    norm M.det <= (Nat.factorial n : Real) * B ^ n := by
  rw [Matrix.det_apply']
  refine (norm_sum_le _ _).trans ?_
  calc
    _ <= Finset.sum Finset.univ (fun _ : Equiv.Perm (Fin n) => B ^ n) :=
      Finset.sum_le_sum (fun p _ => norm_godementJacquet_detTerm_le_pow n M B hEntry p)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, <- Nat.card_eq_fintype_card,
        Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- At infinity the determinant bound is multiplied over places, with the
normalized real and complex exponents. -/
theorem heckeInfiniteIdeleNorm_det_le_of_entryBounds
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (M : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K))
    (B : Real)
    (hEntry : forall (w : InfinitePlace K) (i j : Fin n), norm (M.val i j w) <= B) :
    heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det M) <=
      ((Nat.factorial n : Real) * B ^ n) ^
        Finset.sum Finset.univ (fun w : InfinitePlace K => w.mult) := by
  let D := (Nat.factorial n : Real) * B ^ n
  have hLocal (w : InfinitePlace K) :
      norm ((Matrix.GeneralLinearGroup.det M).val w) <= D := by
    let e : RingHom (InfiniteAdeleRing K) w.Completion :=
      Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w
    have hMap := Matrix.GeneralLinearGroup.map_det e M
    change norm ((Units.map e.toMonoidHom (Matrix.GeneralLinearGroup.det M)).val) <= D
    calc
      _ = norm ((Matrix.GeneralLinearGroup.det ((Matrix.GeneralLinearGroup.map e) M)).val) :=
        congrArg (fun u : Units w.Completion => norm u.val) hMap.symm
      _ <= D := norm_godementJacquet_det_le_factorial_mul_pow n _ B (hEntry w)
  change Finset.prod Finset.univ
    (fun w : InfinitePlace K => norm ((Matrix.GeneralLinearGroup.det M).val w) ^ w.mult) <= _
  calc
    _ <= Finset.prod Finset.univ (fun w : InfinitePlace K => D ^ w.mult) :=
      Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _)
        (fun w _ => by
          have hle := hLocal w
          gcongr)
    _ = _ := Finset.prod_pow_eq_pow_sum Finset.univ (fun w : InfinitePlace K => w.mult) D

/-- Over an ultrametric field the largest determinant term bounds the
determinant, without an archimedean counting factor. -/
theorem norm_godementJacquet_det_le_pow_of_isUltrametricDist
    {R : Type*} [NormedField R] [IsUltrametricDist R]
    (n : Nat) (M : Matrix (Fin n) (Fin n) R)
    (B : Real) (hB : 0 <= B) (hEntry : forall i j : Fin n, norm (M i j) <= B) :
    norm M.det <= B ^ n := by
  rw [Matrix.det_apply']
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hB n)
    (fun p _ => norm_godementJacquet_detTerm_le_pow n M B hEntry p)

/-- The finite determinant norm is bounded by the nth power of any idele
that bounds the local norms of all entries. -/
theorem heckeFiniteIdeleNorm_det_le_of_entryBounds
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (M : Matrix.GeneralLinearGroup (Fin n) (FiniteAdeleRing (RingOfIntegers K) K))
    (u : Units (FiniteAdeleRing (RingOfIntegers K) K))
    (hEntry : forall (p : HeightOneSpectrum (RingOfIntegers K)) (i j : Fin n),
      norm (M.val i j p) <= norm (u.val p)) :
    heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det M) <= heckeFiniteIdeleNorm u ^ n := by
  let D := Matrix.GeneralLinearGroup.det M
  have hLocal (p : HeightOneSpectrum (RingOfIntegers K)) :
      norm (D.val p) <= norm ((u ^ n).val p) := by
    let e : RingHom (FiniteAdeleRing (RingOfIntegers K) K) (p.adicCompletion K) :=
      RestrictedProduct.evalRingHom (fun q : HeightOneSpectrum (RingOfIntegers K) => q.adicCompletion K) p
    have hMap := Matrix.GeneralLinearGroup.map_det e M
    have hp : ((u ^ n).val p) = (u.val p) ^ n := by
      change e (u.val ^ n) = (e u.val) ^ n
      exact map_pow e u.val n
    have hEval : norm (D.val p) =
        norm ((Matrix.GeneralLinearGroup.det ((Matrix.GeneralLinearGroup.map e) M)).val) := by
      change norm ((Units.map e.toMonoidHom D).val) =
        norm ((Matrix.GeneralLinearGroup.det ((Matrix.GeneralLinearGroup.map e) M)).val)
      exact congrArg (fun z : Units (p.adicCompletion K) => norm z.val) hMap.symm
    calc
      _ = _ := hEval
      _ <= norm (u.val p) ^ n :=
        norm_godementJacquet_det_le_pow_of_isUltrametricDist n _ _ (norm_nonneg _) (hEntry p)
      _ = _ := by rw [hp, norm_pow]
  change finprod (fun p : HeightOneSpectrum (RingOfIntegers K) => norm (D.val p)) <= _
  calc
    _ <= finprod (fun p : HeightOneSpectrum (RingOfIntegers K) => norm ((u ^ n).val p)) :=
      finprod_le_finprod (finiteSupport_heckeFiniteIdeleFactors D) (fun _ => norm_nonneg _)
        (finiteSupport_heckeFiniteIdeleFactors (u ^ n)) hLocal
    _ = _ := map_pow heckeFiniteIdeleNorm u n

/-- Each archimedean entry is bounded by its Minkowski coordinate norm. -/
theorem norm_infiniteAdele_apply_le_minkowski
    (K : Type*) [Field K] [NumberField K] (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    norm (x w) <= norm (DedekindZeta.Theta.toMinkowski K (InfiniteAdeleRing.ringEquiv_mixedSpace K x)) := by
  let y := InfiniteAdeleRing.ringEquiv_mixedSpace K x
  have hNorm : mixedEmbedding.normAtPlace w y = norm (x w) := by
    by_cases h : w.IsReal
    . rw [mixedEmbedding.normAtPlace_apply_of_isReal h]
      have hDist := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).dist_eq (x w) 0
      simpa only [y, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, map_zero, dist_zero_right] using hDist
    . have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
      have hDist := (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq (x w) 0
      simpa only [y, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, map_zero, dist_zero_right] using hDist
  have hMult : (1 : Real) <= (w.mult : Real) := by
    by_cases h : w.IsReal
    . have hm : w.mult = 1 := InfinitePlace.mult_isReal (Subtype.mk w h)
      rw [hm]
      norm_num
    . have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
      have hm : w.mult = 2 := InfinitePlace.mult_isComplex (Subtype.mk w hc)
      rw [hm]
      norm_num
  have hSq : norm (x w) ^ 2 <= norm (DedekindZeta.Theta.toMinkowski K y) ^ 2 := by
    rw [DedekindZeta.Theta.norm_toMinkowski_sq]
    calc
      _ = 1 * mixedEmbedding.normAtPlace w y ^ 2 := by rw [hNorm, one_mul]
      _ <= (w.mult : Real) * mixedEmbedding.normAtPlace w y ^ 2 :=
        mul_le_mul_of_nonneg_right hMult (sq_nonneg _)
      _ <= Finset.sum Finset.univ (fun v : InfinitePlace K =>
          (v.mult : Real) * mixedEmbedding.normAtPlace v y ^ 2) :=
        Finset.single_le_sum
          (fun v _ => mul_nonneg (Nat.cast_nonneg v.mult) (sq_nonneg (mixedEmbedding.normAtPlace v y)))
          (Finset.mem_univ w)
  simpa only [abs_of_nonneg (norm_nonneg _)] using (sq_le_sq.mp hSq)

/-- The full determinant norm is bounded by the archimedean matrix norm
and the nth power of a finite idele dominating the finite entries. -/
theorem adelicDeterminantNorm_le_of_finiteEntryBounds
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (M : AdelicGeneralLinearGroup K n) (u : Units (FiniteAdeleRing (RingOfIntegers K) K))
    (hEntry : forall (p : HeightOneSpectrum (RingOfIntegers K)) (i j : Fin n),
      norm ((M.val i j).2 p) <= norm (u.val p)) :
    adelicDeterminantNorm K n M <=
      ((Nat.factorial n : Real) *
        norm (heckeAdeleMinkowskiVector K (Prod (Fin n) (Fin n)) M.val.vec) ^ n) ^
        Finset.sum Finset.univ (fun w : InfinitePlace K => w.mult) * heckeFiniteIdeleNorm u ^ n := by
  let I := InfiniteAdeleRing K
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let f : RingHom (AdeleRing (RingOfIntegers K) K) I := RingHom.fst I F
  let g : RingHom (AdeleRing (RingOfIntegers K) K) F := RingHom.snd I F
  let B := norm (heckeAdeleMinkowskiVector K (Prod (Fin n) (Fin n)) M.val.vec)
  let C := ((Nat.factorial n : Real) * B ^ n) ^
    Finset.sum Finset.univ (fun w : InfinitePlace K => w.mult)
  have hArch : heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det ((Matrix.GeneralLinearGroup.map f) M)) <= C := by
    apply heckeInfiniteIdeleNorm_det_le_of_entryBounds K n _ B
    intro w i j
    change norm ((M.val i j).1 w) <= B
    exact (norm_infiniteAdele_apply_le_minkowski K (M.val i j).1 w).trans
      (PiLp.norm_apply_le (heckeAdeleMinkowskiVector K (Prod (Fin n) (Fin n)) M.val.vec) (Prod.mk j i))
  have hFinite := heckeFiniteIdeleNorm_det_le_of_entryBounds K n ((Matrix.GeneralLinearGroup.map g) M) u hEntry
  have hDetF := Matrix.GeneralLinearGroup.map_det f M
  have hDetG := Matrix.GeneralLinearGroup.map_det g M
  have hC : 0 <= C := pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (norm_nonneg _) _)) _
  change heckeInfiniteIdeleNorm (Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det M)) *
    heckeFiniteIdeleNorm (Units.map g.toMonoidHom (Matrix.GeneralLinearGroup.det M)) <= C * _
  calc
    _ = heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det ((Matrix.GeneralLinearGroup.map f) M)) *
        heckeFiniteIdeleNorm (Units.map g.toMonoidHom (Matrix.GeneralLinearGroup.det M)) :=
      congrArg (fun x : Real => x *
        heckeFiniteIdeleNorm (Units.map g.toMonoidHom (Matrix.GeneralLinearGroup.det M)))
        (congrArg heckeInfiniteIdeleNorm hDetF.symm)
    _ = heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det ((Matrix.GeneralLinearGroup.map f) M)) *
        heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det ((Matrix.GeneralLinearGroup.map g) M)) :=
      congrArg (fun y : Real =>
        heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det ((Matrix.GeneralLinearGroup.map f) M)) * y)
        (congrArg heckeFiniteIdeleNorm hDetG.symm)
    _ <= C * heckeFiniteIdeleNorm u ^ n :=
      (mul_le_mul_of_nonneg_right hArch (heckeFiniteIdeleNorm_pos _).le).trans
        (mul_le_mul_of_nonneg_left hFinite hC)

/-- The norm of the matrix in an invertible theta term is exactly exp t. -/
theorem adelicDeterminantNorm_thetaArgument
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n) (t : Real)
    (A B : (adelicDeterminantLogNorm K n).ker) (P : Matrix.GeneralLinearGroup (Fin n) K) :
    adelicDeterminantNorm K n
      (Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t) *
        adelicPrincipalGeneralLinear K n P * B.val) = Real.exp t := by
  let f := adelicDeterminantNorm K n
  have hOne (Q : (adelicDeterminantLogNorm K n).ker) : f Q.val = 1 := by
    have hLog : Real.log (f Q.val) = 0 := Q.property
    calc
      _ = Real.exp (Real.log (f Q.val)) := (Real.exp_log (adelicDeterminantNorm_pos K n Q.val)).symm
      _ = 1 := by rw [hLog, Real.exp_zero]
  change f (Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t) *
      adelicPrincipalGeneralLinear K n P * B.val) = Real.exp t
  simp only [map_mul]
  rw [show f (Inv.inv A.val) = 1 from hOne (Inv.inv A), hOne B,
    show f (adelicDeterminantSection K n (Multiplicative.ofAdd t)) = Real.exp t from
      adelicDeterminantNorm_section K n hn (Multiplicative.ofAdd t),
    show f (adelicPrincipalGeneralLinear K n P) = 1 from adelicDeterminantNorm_principal K n P,
    one_mul, mul_one, mul_one]

/-- A compact family of finite adeles admits one finite idele dominating
all of its local norms. -/
theorem exists_finiteIdele_dominating_compact
    (K : Type*) [Field K] [NumberField K]
    (S : Set (FiniteAdeleRing (RingOfIntegers K) K)) (hS : IsCompact S) :
    Exists (fun u : Units (FiniteAdeleRing (RingOfIntegers K) K) =>
      forall x : FiniteAdeleRing (RingOfIntegers K) K, Membership.mem S x ->
        forall p : HeightOneSpectrum (RingOfIntegers K), norm (x p) <= norm (u.val p)) := by
  let R := RingOfIntegers K
  let F := FiniteAdeleRing R K
  choose d hd using exists_commonDenominator_of_isCompact_finiteAdeles S hS
  have hdK : Not (algebraMap R K d = 0) := by
    intro h
    exact hd.1 ((FaithfulSMul.algebraMap_injective R K) (h.trans (map_zero _).symm))
  let v : Units F := Units.map (algebraMap K F).toMonoidHom (Units.mk0 (algebraMap R K d) hdK)
  refine Exists.intro (Inv.inv v) ?_
  intro x hx p
  have hComp : v.val p = algebraMap R (p.adicCompletion K) d := by
    change algebraMap K (p.adicCompletion K) (algebraMap R K d) = _
    exact (IsScalarTower.algebraMap_apply R K (p.adicCompletion K) d).symm
  have hInt := hd.2 x hx p
  have hSmall : norm (x p * v.val p) <= 1 := by
    rw [hComp]
    exact Valued.toNormedField.norm_le_one_iff.mpr hInt
  have hInv : v.val p * (Inv.inv v).val p = 1 :=
    congrArg (fun w : Units F => w.val p) (mul_inv_cancel v)
  calc
    norm (x p) = norm ((x p * v.val p) * (Inv.inv v).val p) := by
      rw [mul_assoc, hInv, mul_one]
    _ = norm (x p * v.val p) * norm ((Inv.inv v).val p) := norm_mul _ _
    _ <= _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hSmall (norm_nonneg _)

private abbrev MatrixRectangleIndex (n : Nat) := Prod (Fin n) (Fin n)

/-- All nonzero evaluations of a fixed Schwartz rectangle share one
finite idele dominating the local norms of every finite matrix entry. -/
theorem exists_finiteIdele_dominating_godementJacquetMatrixRectangle
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (a : MatrixRectangleIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K)
    (f : SchwartzMap (PiLp 2 (fun _ : MatrixRectangleIndex n => DedekindZeta.Theta.minkowskiSpace K)) Complex) :
    Exists (fun u : Units (FiniteAdeleRing (RingOfIntegers K) K) =>
      forall M : AdelicGeneralLinearGroup K n,
        Not (godementJacquetMatrixRectangle K a d f M.val = 0) ->
        forall (p : HeightOneSpectrum (RingOfIntegers K)) (i j : Fin n),
          norm ((M.val i j).2 p) <= norm (u.val p)) := by
  let I := MatrixRectangleIndex n
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let e := algebraMap (RingOfIntegers K) K
  let T := finiteAdelePrincipalRectangle K I a (e d)
  let S := Set.iUnion (fun i : I => Set.image (fun v : I -> F => v i) T)
  have hS : IsCompact S := isCompact_iUnion fun i : I =>
    (isCompact_finiteAdelePrincipalRectangle K I a (e d)).image (continuous_apply i)
  choose u hu using exists_finiteIdele_dominating_compact K S hS
  refine Exists.intro u ?_
  intro M hM p i j
  let v (k : I) : F := (M.val.vec k).2
  let c (k : I) : Set F := heckeFiniteAdelePrincipalCoset (a k) (e d)
  have hv (k : I) : Membership.mem (c k) (v k) := by
    by_contra h
    apply hM
    change f (heckeAdeleMinkowskiVector K I M.val.vec) * Finset.prod Finset.univ
      (fun k : I => (c k).indicator (fun _ => (1 : Complex)) (v k)) = 0
    have hZero : Finset.prod Finset.univ
        (fun k : I => (c k).indicator (fun _ => (1 : Complex)) (v k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (Set.indicator_of_notMem h _)
    rw [hZero, mul_zero]
  have hT : Membership.mem T v := (mem_finiteAdelePrincipalRectangle_iff K I a v (e d)).mpr hv
  have hMember : Membership.mem S (v (Prod.mk j i)) :=
    Set.mem_iUnion.mpr (Exists.intro (Prod.mk j i) (Exists.intro v (And.intro hT rfl)))
  exact hu (v (Prod.mk j i)) hMember p

/-- The finite rectangle indicator can only reduce the norm of its
archimedean Schwartz factor. -/
theorem norm_godementJacquetMatrixRectangle_le_arch
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (a : MatrixRectangleIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K)
    (f : SchwartzMap (PiLp 2 (fun _ : MatrixRectangleIndex n => DedekindZeta.Theta.minkowskiSpace K)) Complex)
    (X : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K)) :
    norm (godementJacquetMatrixRectangle K a d f X) <=
      norm (f (heckeAdeleMinkowskiVector K (MatrixRectangleIndex n) X.vec)) := by
  let C (i : MatrixRectangleIndex n) := heckeFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d)
  let P (i : MatrixRectangleIndex n) := (C i).indicator (fun _ => (1 : Complex)) (X.vec i).2
  let y := heckeAdeleMinkowskiVector K (MatrixRectangleIndex n) X.vec
  change norm (f y * Finset.prod Finset.univ P) <= norm (f y)
  rw [norm_mul, norm_prod]
  have h (i : MatrixRectangleIndex n) : norm (P i) <= 1 := by
    by_cases hi : Membership.mem (C i) (X.vec i).2
    . have hEq : P i = 1 := Set.indicator_of_mem hi _
      rw [hEq, norm_one]
    . have hEq : P i = 0 := Set.indicator_of_notMem hi _
      rw [hEq, norm_zero]
      exact zero_le_one
  have hProd : Finset.prod Finset.univ (fun i : MatrixRectangleIndex n => norm (P i)) <= 1 := by
    simpa only [Finset.prod_const_one] using
      Finset.prod_le_prod (s := (Finset.univ : Finset (MatrixRectangleIndex n)))
        (g := fun _ => (1 : Real)) (fun _ _ => norm_nonneg _) (fun i _ => h i)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hProd (norm_nonneg (f y))

/-- Each invertible theta term of a fixed Schwartz rectangle has arbitrary
exponential decay in positive logarithmic determinant time, with any
prescribed polynomial weight in its archimedean matrix norm. -/
theorem exists_godementJacquetMatrixRectangle_weightedDecay
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    (a : MatrixRectangleIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K)
    (f : SchwartzMap (PiLp 2 (fun _ : MatrixRectangleIndex n => DedekindZeta.Theta.minkowskiSpace K)) Complex)
    (m : Nat) (b : Real) :
    Exists (fun C : Real => And (0 <= C)
      (forall t : Real, 0 <= t ->
        forall (A B : (adelicDeterminantLogNorm K n).ker) (P : Matrix.GeneralLinearGroup (Fin n) K),
        let X := Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t) *
          adelicPrincipalGeneralLinear K n P * B.val
        norm (godementJacquetMatrixRectangle K a d f X.val) *
          norm (heckeAdeleMinkowskiVector K (MatrixRectangleIndex n) X.val.vec) ^ m *
          Real.exp (b * t) <= C)) := by
  choose u hu using exists_finiteIdele_dominating_godementJacquetMatrixRectangle K n a d f
  choose k hk using exists_nat_ge b
  let D := Finset.sum Finset.univ (fun w : InfinitePlace K => w.mult)
  let N := n * D
  let L := (Nat.factorial n : Real) ^ D * heckeFiniteIdeleNorm u ^ n
  let S := SchwartzMap.seminorm Real (N * k + m) 0 f
  have hS : 0 <= S := apply_nonneg _ _
  have hL : 0 <= L := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (heckeFiniteIdeleNorm_pos u).le _)
  have hC : 0 <= L ^ k * S := mul_nonneg (pow_nonneg hL _) hS
  refine Exists.intro (L ^ k * S) (And.intro hC ?_)
  intro t ht A B P
  let X := Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t) *
    adelicPrincipalGeneralLinear K n P * B.val
  let x := heckeAdeleMinkowskiVector K (MatrixRectangleIndex n) X.val.vec
  let r := norm x
  let v := godementJacquetMatrixRectangle K a d f X.val
  change norm v * r ^ m * Real.exp (b * t) <= L ^ k * S
  by_cases hz : v = 0
  . simpa only [hz, norm_zero, zero_mul] using hC
  have hExp : Real.exp t <= L * r ^ N := by
    calc
      _ = adelicDeterminantNorm K n X := (adelicDeterminantNorm_thetaArgument K n hn t A B P).symm
      _ <= ((Nat.factorial n : Real) * r ^ n) ^ D * heckeFiniteIdeleNorm u ^ n :=
        adelicDeterminantNorm_le_of_finiteEntryBounds K n X u (hu X hz)
      _ = _ := by
        simp only [L, N, pow_mul, mul_pow]
        ring
  have hExpK : Real.exp (b * t) <= (L * r ^ N) ^ k := by
    calc
      _ <= Real.exp ((k : Real) * t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk ht)
      _ = Real.exp t ^ k := Real.exp_nat_mul t k
      _ <= _ := by gcongr
  have hArch : norm v <= norm (f x) := norm_godementJacquetMatrixRectangle_le_arch K n a d f X.val
  calc
    _ <= norm v * r ^ m * (L * r ^ N) ^ k :=
      mul_le_mul_of_nonneg_left hExpK (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    _ = L ^ k * (r ^ (N * k + m) * norm v) := by
      simp only [pow_add, pow_mul, mul_pow]
      ring
    _ <= L ^ k * (r ^ (N * k + m) * norm (f x)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hArch (pow_nonneg (norm_nonneg _) _)) (pow_nonneg hL _)
    _ <= L ^ k * S :=
      mul_le_mul_of_nonneg_left (SchwartzMap.norm_pow_mul_le_seminorm Real f (N * k + m) x) (pow_nonneg hL _)

private abbrev SectionAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K
private abbrev SectionFiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

/-- The logarithmic determinant section has trivial finite matrix component. -/
theorem adelicDeterminantSection_map_finite
    (K : Type*) [Field K] [NumberField K] (n : Nat) (t : Real) :
    Matrix.GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (SectionFiniteAdeles K))
      (adelicDeterminantSection K n (Multiplicative.ofAdd t)) = 1 := by
  let u := heckeIdelicExpSection K (t / (n : Real))
  let g : RingHom (SectionAdeles K) (SectionFiniteAdeles K) :=
    RingHom.snd (InfiniteAdeleRing K) (SectionFiniteAdeles K)
  apply Units.ext
  change (Matrix.scalar (Fin n) u.val).map g = 1
  rw [Matrix.scalar_apply]
  apply Matrix.ext
  intro i j
  change g (Matrix.diagonal (fun _ : Fin n => u.val) i j) =
    (1 : Matrix (Fin n) (Fin n) (SectionFiniteAdeles K)) i j
  by_cases h : i = j
  . subst j
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rfl
  . rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, map_zero]

/-- The archimedean matrix coordinates are multiplied by the exact
central scale of the determinant section. -/
theorem heckeAdeleMinkowskiVector_adelicDeterminantSection_mul
    (K : Type*) [Field K] [NumberField K] (n : Nat) (t : Real)
    (M : AdelicGeneralLinearGroup K n) :
    heckeAdeleMinkowskiVector K (MatrixRectangleIndex n)
      (adelicDeterminantSection K n (Multiplicative.ofAdd t) * M).val.vec =
      HSMul.hSMul (Real.exp ((t / (n : Real)) / (Module.finrank Rat K : Real)))
        (heckeAdeleMinkowskiVector K (MatrixRectangleIndex n) M.val.vec) := by
  let c := Real.exp ((t / (n : Real)) / (Module.finrank Rat K : Real))
  let T := DedekindZeta.Theta.toMinkowski K
  let e := heckeAdeleMixedCoordinate K
  let u := heckeIdelicExpSection K (t / (n : Real))
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let J := MatrixRectangleIndex n
  have hArch : e u.val = algebraMap Real (mixedEmbedding.mixedSpace K) c := by
    change E (E.symm (algebraMap Real (mixedEmbedding.mixedSpace K) c)) = _
    exact E.apply_symm_apply _
  apply (PiLp.continuousLinearEquiv 2 Real (fun _ : J => DedekindZeta.Theta.minkowskiSpace K)).injective
  funext i
  change T (e ((Matrix.scalar (Fin n) u.val * M.val) i.2 i.1)) =
    HSMul.hSMul c (T (e (M.val i.2 i.1)))
  have hEntry :
      e ((Matrix.scalar (Fin n) u.val * M.val) i.2 i.1) =
        HSMul.hSMul c (e (M.val i.2 i.1)) := by
    rw [Matrix.scalar_apply, Matrix.diagonal_mul]
    change e (u.val * M.val i.2 i.1) = _
    rw [map_mul, hArch]
    exact (Algebra.smul_def c (e (M.val i.2 i.1))).symm
  exact (congrArg T hEntry).trans (map_smul T _ _)

/-- Moving the positive central scalar to the front isolates all time
dependence from the finite component of an invertible theta argument. -/
theorem godementJacquetThetaArgument_center
    (K : Type*) [Field K] [NumberField K] (n : Nat) (t : Real)
    (A B : (adelicDeterminantLogNorm K n).ker) (P : Matrix.GeneralLinearGroup (Fin n) K) :
    Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t) *
        adelicPrincipalGeneralLinear K n P * B.val =
      adelicDeterminantSection K n (Multiplicative.ofAdd t) *
        (Inv.inv A.val * adelicPrincipalGeneralLinear K n P * B.val) := by
  rw [(adelicDeterminantSection_commute K n (Multiplicative.ofAdd t) (Inv.inv A.val)).eq.symm]
  simp only [mul_assoc]

/-- The finite matrix argument is independent of logarithmic determinant time. -/
theorem godementJacquetThetaArgument_map_finite
    (K : Type*) [Field K] [NumberField K] (n : Nat) (t : Real)
    (A B : (adelicDeterminantLogNorm K n).ker) (P : Matrix.GeneralLinearGroup (Fin n) K) :
    let g : RingHom (SectionAdeles K) (SectionFiniteAdeles K) :=
      RingHom.snd (InfiniteAdeleRing K) (SectionFiniteAdeles K)
    Matrix.GeneralLinearGroup.map g
        (Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t) *
          adelicPrincipalGeneralLinear K n P * B.val) =
      Matrix.GeneralLinearGroup.map g (Inv.inv A.val * adelicPrincipalGeneralLinear K n P * B.val) := by
  let g : RingHom (SectionAdeles K) (SectionFiniteAdeles K) :=
    RingHom.snd (InfiniteAdeleRing K) (SectionFiniteAdeles K)
  let G := Matrix.GeneralLinearGroup.map (n := Fin n) g
  let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let Y := Inv.inv A.val * adelicPrincipalGeneralLinear K n P * B.val
  have hz : G z = 1 := adelicDeterminantSection_map_finite K n t
  change G (Inv.inv A.val * z * adelicPrincipalGeneralLinear K n P * B.val) = G Y
  calc
    _ = G (z * Y) := congrArg G (godementJacquetThetaArgument_center K n t A B P)
    _ = G z * G Y := map_mul G _ _
    _ = G Y := (congrArg (fun x => x * G Y) hz).trans (one_mul _)

/-- At nonnegative time the archimedean norm is at least its value
with the central scalar removed. -/
theorem norm_godementJacquetThetaArgument_ge_base
    (K : Type*) [Field K] [NumberField K] (n : Nat) (t : Real) (ht : 0 <= t)
    (A B : (adelicDeterminantLogNorm K n).ker) (P : Matrix.GeneralLinearGroup (Fin n) K) :
    norm (heckeAdeleMinkowskiVector K (MatrixRectangleIndex n)
      (Inv.inv A.val * adelicPrincipalGeneralLinear K n P * B.val).val.vec) <=
    norm (heckeAdeleMinkowskiVector K (MatrixRectangleIndex n)
      (Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t) *
          adelicPrincipalGeneralLinear K n P * B.val).val.vec) := by
  rw [godementJacquetThetaArgument_center K n t A B P,
    heckeAdeleMinkowskiVector_adelicDeterminantSection_mul K n t, norm_smul,
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hScale : 1 <= Real.exp ((t / (n : Real)) / (Module.finrank Rat K : Real)) :=
    Real.one_le_exp_iff.mpr (div_nonneg (div_nonneg ht (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hScale (norm_nonneg _)

end Robin1984.GRH
