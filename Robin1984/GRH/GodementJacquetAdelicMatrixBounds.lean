import Robin1984.GRH.GodementJacquetFiniteMatrixDenominator
import Robin1984.GRH.GodementJacquetThetaDecay

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Finite determinant norms, adjugate bounds, and compact covering arguments in the Godement--Jacquet setting.
- Formalization note: Bounds finite inverse denominators and archimedean inverse entries by the archimedean radius and supplies compact matrix sets and finite dyadic covers.
- PROVENANCE-END
-/

/-!
# Matrix bounds for adelic volume estimates

A lower bound on the total determinant norm and fixed finite support give
a positive lower bound on the archimedean determinant norm and a
polynomial bound on a finite inverse denominator. The inverse matrix
entries at the infinite places are controlled by the minors and the
archimedean determinant bound. Compact bounds on a matrix and its inverse
and dyadic covers of a compact unit ball provide the covering sets.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain
open scoped Classical

private abbrev ScalarsAtFinitePlaces (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

/-- Scale the finite component by the inverse of a unit bounding its entries. -/
def godementJacquetScaledFiniteComponent
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (u : Units (ScalarsAtFinitePlaces K)) (g : AdelicGeneralLinearGroup K n) :
    Matrix.GeneralLinearGroup (Fin n) (ScalarsAtFinitePlaces K) :=
  Matrix.GeneralLinearGroup.scalar (Fin n) (Inv.inv u) *
    Matrix.GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (ScalarsAtFinitePlaces K)) g

/-- Finite support and a lower bound of one for the total determinant
norm give an archimedean lower determinant bound and a polynomial bound
for the inverse denominator of the integral scaled finite component. -/
theorem exists_scaledFiniteInverseDenominator_le_archNorm
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (u : Units (ScalarsAtFinitePlaces K)) (g : AdelicGeneralLinearGroup K n)
    (B : Real)
    (hEntry : forall (p : HeightOneSpectrum (RingOfIntegers K)) (i j : Fin n),
      norm ((g.val i j).2 p) <= norm (u.val p))
    (hArch : norm (heckeAdeleMinkowskiVector K (Prod (Fin n) (Fin n)) g.val.vec) <= B)
    (hNorm : 1 <= adelicDeterminantNorm K n g) :
    let Gf := godementJacquetScaledFiniteComponent K n u g
    let Ga := Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (ScalarsAtFinitePlaces K)) g
    let C := heckeFiniteIdeleNorm u ^ n
    Exists (fun N : Nat => And (0 < N) (And (Membership.mem (finiteAdeleMatrixDenominatorSet K n N) Gf)
      (And ((N : Real) <= C * ((Nat.factorial n : Real) * B ^ n) ^
        Finset.sum Finset.univ (fun w : InfinitePlace K => w.mult))
      (Inv.inv C <= heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det Ga))))) := by
  let F := ScalarsAtFinitePlaces K
  let pf : RingHom (AdeleRing (RingOfIntegers K) K) F := RingHom.snd (InfiniteAdeleRing K) F
  let pa : RingHom (AdeleRing (RingOfIntegers K) K) (InfiniteAdeleRing K) :=
    RingHom.fst (InfiniteAdeleRing K) F
  let gf := Matrix.GeneralLinearGroup.map pf g
  let ga := Matrix.GeneralLinearGroup.map pa g
  let Gf := godementJacquetScaledFiniteComponent K n u g
  let A := heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det ga)
  let Fnorm := heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det gf)
  let W := heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det Gf)
  let C := heckeFiniteIdeleNorm u ^ n
  have hC : 0 < C := pow_pos (heckeFiniteIdeleNorm_pos u) _
  have hA : 0 < A := heckeInfiniteIdeleNorm_pos _
  have hW : 0 < W := heckeFiniteIdeleNorm_pos _
  have hU : forall p : HeightOneSpectrum (RingOfIntegers K), norm ((Inv.inv u).val p) * norm (u.val p) = 1 := by
    intro p
    have he : (Inv.inv u).val p * u.val p = 1 :=
      congrArg (fun a : Units F => a.val p) (inv_mul_cancel u)
    rw [<- norm_mul, he, norm_one]
  have hVal : Gf.val = HSMul.hSMul (Inv.inv u).val gf.val := by
    change Matrix.scalar (Fin n) (Inv.inv u).val * gf.val = _
    rw [Matrix.scalar_apply, <- Matrix.smul_eq_diagonal_mul]
  have hSmall (p : HeightOneSpectrum (RingOfIntegers K)) (i j : Fin n) :
      norm (Gf.val i j p) <= 1 := by
    rw [hVal]
    change norm ((Inv.inv u).val p * (g.val i j).2 p) <= 1
    rw [norm_mul, <- hU p]
    exact mul_le_mul_of_nonneg_left (hEntry p i j) (norm_nonneg _)
  have hInt : Membership.mem (integralFiniteAdeleSubring K).matrix Gf.val :=
    fun i j p => Valued.toNormedField.norm_le_one_iff.mp (hSmall p i j)
  choose N hN using exists_finiteAdeleMatrixDenominatorSet_of_integral K n Gf hInt
  have hUinv : heckeFiniteIdeleNorm (Inv.inv u) = Inv.inv (heckeFiniteIdeleNorm u) := by
    have h := congrArg heckeFiniteIdeleNorm (mul_inv_cancel u)
    rw [map_mul, map_one] at h
    have he : heckeFiniteIdeleNorm (Inv.inv u) = 1 / heckeFiniteIdeleNorm u :=
      (eq_div_iff (ne_of_gt (heckeFiniteIdeleNorm_pos u))).mpr ((mul_comm _ _).trans h)
    simpa only [one_div] using he
  have hScale : W = Inv.inv C * Fnorm := by
    change heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin n) (Inv.inv u) * gf)) = _
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, map_pow, hUinv, inv_pow]
  have hRel : W * C = Fnorm := by
    rw [hScale]
    field_simp [ne_of_gt hC]
  have hWle : W <= 1 := by
    have h := heckeFiniteIdeleNorm_det_le_of_entryBounds K n Gf 1 (fun p i j => by
      change norm (Gf.val i j p) <= norm (1 : p.adicCompletion K)
      rw [norm_one]
      exact hSmall p i j)
    simpa only [W, map_one, one_pow] using h
  have hFle : Fnorm <= C := by
    rw [<- hRel]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hWle hC.le
  have hAD : A * Fnorm = adelicDeterminantNorm K n g := by
    change heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det ga) *
        heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det gf) = _
    rw [Matrix.GeneralLinearGroup.map_det pa g, Matrix.GeneralLinearGroup.map_det pf g]
    rfl
  have hLower : Inv.inv C <= A := by
    have hAC : 1 <= A * C :=
      (hNorm.trans_eq hAD.symm).trans (mul_le_mul_of_nonneg_left hFle hA.le)
    have hP := mul_le_mul_of_nonneg_right hAC (inv_nonneg.mpr hC.le)
    have hInv : C * Inv.inv C = 1 := by field_simp [ne_of_gt hC]
    rwa [one_mul, mul_assoc, hInv, mul_one] at hP
  have hNmul : (N : Real) * W = 1 := by
    rw [hN.2.1]
    change Inv.inv W * W = 1
    field_simp [ne_of_gt hW]
  have hNle : (N : Real) <= A * C := by
    calc
      _ <= (A * Fnorm) * (N : Real) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (hNorm.trans_eq hAD.symm) (Nat.cast_nonneg N)
      _ = A * C * ((N : Real) * W) := by rw [<- hRel]; ring
      _ = _ := by rw [hNmul, mul_one]
  have hAUp : A <= ((Nat.factorial n : Real) * B ^ n) ^
      Finset.sum Finset.univ (fun w : InfinitePlace K => w.mult) := by
    apply heckeInfiniteIdeleNorm_det_le_of_entryBounds K n ga B
    intro w i j
    change norm ((g.val i j).1 w) <= B
    exact ((norm_infiniteAdele_apply_le_minkowski K (g.val i j).1 w).trans
      (PiLp.norm_apply_le (heckeAdeleMinkowskiVector K (Prod (Fin n) (Fin n)) g.val.vec) (Prod.mk j i))).trans hArch
  refine Exists.intro N (And.intro hN.1 (And.intro hN.2.2 (And.intro ?_ hLower)))
  exact hNle.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hAUp hC.le)

/-- An inverse matrix entry is bounded by its determinant inverse times
the factorial bound for the corresponding minor. -/
theorem norm_godementJacquet_matrixInv_entry_le
    {F : Type*} [NormedField F] (n : Nat)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (B : Real)
    (hEntry : forall i j : Fin (n + 1), norm (g.val i j) <= B) (i j : Fin (n + 1)) :
    norm (g.inv i j) <=
      norm (Matrix.GeneralLinearGroup.det g).inv * ((Nat.factorial n : Real) * B ^ n) := by
  let u := Matrix.GeneralLinearGroup.det g
  have hAdjEq : g.val.adjugate = HSMul.hSMul u.val g.inv := by
    calc
      _ = g.inv * (g.val * g.val.adjugate) := by rw [<- mul_assoc, g.inv_val, one_mul]
      _ = _ := by
        rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one]
        rfl
  have hInvEq : g.inv = HSMul.hSMul u.inv g.val.adjugate := by
    rw [hAdjEq, smul_smul, u.inv_val, one_smul]
  have hE : g.inv i j = u.inv * g.val.adjugate i j :=
    congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) F => M i j) hInvEq
  have hMinor : norm (g.val.adjugate i j) <= (Nat.factorial n : Real) * B ^ n := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact norm_godementJacquet_det_le_factorial_mul_pow n
      (g.val.submatrix j.succAbove i.succAbove) B (fun a b => hEntry _ _)
  rw [hE, norm_mul]
  exact mul_le_mul_of_nonneg_left hMinor (norm_nonneg _)

/-- A positive lower bound for the global archimedean norm and an upper
bound on all local factors control each local inverse. -/
theorem norm_infiniteIdele_inv_apply_le_of_normBounds
    (K : Type*) [Field K] [NumberField K] (u : Units (InfiniteAdeleRing K))
    (C R : Real) (hC : 0 < C) (hR : 1 <= R)
    (hNorm : C <= heckeInfiniteIdeleNorm u)
    (hUpper : forall v : InfinitePlace K, norm (u.val v) <= R) (w : InfinitePlace K) :
    norm (u.inv w) <= max 1 (Inv.inv C * R ^ Finset.sum Finset.univ (fun v : InfinitePlace K => v.mult)) := by
  let b (v : InfinitePlace K) := norm (u.val v)
  let r := norm (u.inv w)
  let D := Finset.sum Finset.univ (fun v : InfinitePlace K => v.mult)
  let T := Finset.univ.erase w
  let P := Finset.prod T (fun v => b v ^ v.mult)
  let Q := Finset.prod T (fun v : InfinitePlace K => R ^ v.mult)
  have hr : 0 <= r := norm_nonneg _
  have hR0 : 0 <= R := zero_le_one.trans hR
  have hUnit : b w * r = 1 := by
    have he : u.val w * u.inv w = 1 :=
      congrArg (fun a : InfiniteAdeleRing K => a w) u.val_inv
    exact (norm_mul _ _).symm.trans (congrArg norm he |>.trans norm_one)
  by_cases hw : 1 <= b w
  . have hle : r <= b w * r := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw hr
    exact (hle.trans_eq hUnit).trans (le_max_left _ _)
  have hw' : b w <= 1 := (lt_of_not_ge hw).le
  have hP : P <= Q := by
    apply Finset.prod_le_prod (fun v _ => pow_nonneg (norm_nonneg _) _)
    intro v hv
    change b v ^ v.mult <= R ^ v.mult
    have hb : b v <= R := hUpper v
    have hb0 : 0 <= b v := norm_nonneg _
    gcongr
  have hQ : Q <= R ^ D := by
    have hPow (k : Nat) : 1 <= R ^ k := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ]
        exact ih.trans (le_mul_of_one_le_right (pow_nonneg hR0 _) hR)
    calc
      _ <= Q * R ^ w.mult :=
        le_mul_of_one_le_right (Finset.prod_nonneg (fun _ _ => pow_nonneg hR0 _)) (hPow _)
      _ = Finset.prod Finset.univ (fun v : InfinitePlace K => R ^ v.mult) :=
        Finset.prod_erase_mul _ _ (Finset.mem_univ w)
      _ = _ := Finset.prod_pow_eq_pow_sum Finset.univ (fun v : InfinitePlace K => v.mult) R
  have hLocal : b w ^ w.mult <= b w := by
    by_cases hReal : w.IsReal
    . rw [InfinitePlace.mult_isReal (Subtype.mk w hReal), pow_one]
    . have hc := InfinitePlace.not_isReal_iff_isComplex.mp hReal
      rw [InfinitePlace.mult_isComplex (Subtype.mk w hc), pow_two]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hw' (norm_nonneg (u.val w))
  have hProd : P * b w ^ w.mult = heckeInfiniteIdeleNorm u :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ w)
  have hCw : C <= R ^ D * b w := by
    calc
      _ <= P * b w ^ w.mult := hNorm.trans_eq hProd.symm
      _ <= R ^ D * b w ^ w.mult :=
        mul_le_mul_of_nonneg_right (hP.trans hQ) (pow_nonneg (norm_nonneg _) _)
      _ <= _ := mul_le_mul_of_nonneg_left hLocal (pow_nonneg hR0 _)
  have hCr : C * r <= R ^ D := by
    calc
      _ <= (R ^ D * b w) * r := mul_le_mul_of_nonneg_right hCw hr
      _ = _ := by rw [mul_assoc, hUnit, mul_one]
  calc
    r = Inv.inv C * (C * r) := by field_simp [ne_of_gt hC]
    _ <= Inv.inv C * R ^ D := mul_le_mul_of_nonneg_left hCr (inv_nonneg.mpr hC.le)
    _ <= _ := le_max_right _ _

/-- A lower bound for the archimedean determinant norm gives a uniform
polynomial estimate for every local entry of the matrix inverse. -/
theorem norm_godementJacquet_adelicInverse_archEntry_le
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (g : AdelicGeneralLinearGroup K (n + 1)) (B C : Real)
    (hB : 1 <= B) (hC : 0 < C)
    (hArch : norm (heckeAdeleMinkowskiVector K (Prod (Fin (n + 1)) (Fin (n + 1))) g.val.vec) <= B)
    (hDet : C <= heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K)
        (FiniteAdeleRing (RingOfIntegers K) K)) g)))
    (w : InfinitePlace K) (i j : Fin (n + 1)) :
    let D := Finset.sum Finset.univ (fun v : InfinitePlace K => v.mult)
    norm ((g.inv i j).1 w) <=
      ((1 + Inv.inv C * (Nat.factorial (n + 1) : Real) ^ D) * (Nat.factorial n : Real)) *
        B ^ ((n + 1) * D + n) := by
  let I := InfiniteAdeleRing K
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let Ga := Matrix.GeneralLinearGroup.map (RingHom.fst I F) g
  let u := Matrix.GeneralLinearGroup.det Ga
  let E (v : InfinitePlace K) : RingHom I v.Completion :=
    Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) v
  let G (v : InfinitePlace K) := Matrix.GeneralLinearGroup.map (E v) Ga
  let T := (Nat.factorial (n + 1) : Real)
  let R := T * B ^ (n + 1)
  let D := Finset.sum Finset.univ (fun v : InfinitePlace K => v.mult)
  let S := (Nat.factorial n : Real) * B ^ n
  have hB0 : 0 <= B := zero_le_one.trans hB
  have hBPow (k : Nat) : 1 <= B ^ k := by
    calc
      1 = (1 : Real) ^ k := (one_pow _).symm
      _ <= _ := by gcongr
  have hT : (1 : Real) <= T := by
    dsimp only [T]
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (n + 1))
  have hR : 1 <= R := by
    change (1 : Real) <= T * B ^ (n + 1)
    calc
      _ <= B ^ (n + 1) := hBPow _
      _ <= _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hT (pow_nonneg hB0 _)
  have hL (v : InfinitePlace K) (a b : Fin (n + 1)) : norm ((G v).val a b) <= B := by
    change norm ((g.val a b).1 v) <= B
    exact ((norm_infiniteAdele_apply_le_minkowski K (g.val a b).1 v).trans
      (PiLp.norm_apply_le (heckeAdeleMinkowskiVector K (Prod (Fin (n + 1)) (Fin (n + 1))) g.val.vec)
        (Prod.mk b a))).trans hArch
  have hMap (v : InfinitePlace K) :
      Matrix.GeneralLinearGroup.det (G v) = Units.map (E v).toMonoidHom u :=
    Matrix.GeneralLinearGroup.map_det (E v) Ga
  have hUpper (v : InfinitePlace K) : norm (u.val v) <= R := by
    have h := norm_godementJacquet_det_le_factorial_mul_pow (n + 1) (G v).val B (hL v)
    change norm (Matrix.GeneralLinearGroup.det (G v)).val <= R at h
    rw [hMap v] at h
    exact h
  have hInv := norm_infiniteIdele_inv_apply_le_of_normBounds K u C R hC hR hDet hUpper w
  have hLocal : norm ((g.inv i j).1 w) <= norm (u.inv w) * S := by
    have h := norm_godementJacquet_matrixInv_entry_le n (G w) B (hL w) i j
    rw [hMap w] at h
    exact h
  have hPoly : R ^ D = T ^ D * B ^ ((n + 1) * D) := by
    dsimp only [R]
    rw [mul_pow, <- pow_mul]
  have hMax : max 1 (Inv.inv C * R ^ D) <=
      (1 + Inv.inv C * T ^ D) * B ^ ((n + 1) * D) := by
    have hCT : 0 <= Inv.inv C * T ^ D :=
      mul_nonneg (inv_nonneg.mpr hC.le) (pow_nonneg (zero_le_one.trans hT) _)
    rw [hPoly]
    apply max_le
    . calc
        _ <= B ^ ((n + 1) * D) := hBPow _
        _ <= _ := by
          have hOne : (1 : Real) <= 1 + Inv.inv C * T ^ D := by linarith
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hOne (pow_nonneg hB0 _)
    . rw [<- mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hB0 _)
  have hS : 0 <= S := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB0 _)
  calc
    _ <= norm (u.inv w) * S := hLocal
    _ <= ((1 + Inv.inv C * T ^ D) * B ^ ((n + 1) * D)) * S :=
      mul_le_mul_of_nonneg_right (hInv.trans hMax) hS
    _ = _ := by
      dsimp only [S, T]
      rw [pow_add]
      ring

private abbrev MatrixPartAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

/-- Entry bounds for the archimedean components and integrality of the
finite components describe a compact subset of the adelic matrix algebra. -/
def godementJacquetBoundedIntegralMatrices
    (K : Type*) [Field K] [NumberField K] (n : Nat) (B : Real) :
    Set (Matrix (Fin n) (Fin n) (MatrixPartAdeles K)) :=
  Set.ofPred (fun M => forall i j : Fin n,
    And (forall w : InfinitePlace K, norm ((M i j).1 w) <= B)
      (forall p : HeightOneSpectrum (RingOfIntegers K),
        Membership.mem (p.adicCompletionIntegers K) ((M i j).2 p)))

/-- Bounding both the matrix and its inverse gives a compact part of the
adelic general linear group. -/
def godementJacquetBoundedIntegralMatrixUnits
    (K : Type*) [Field K] [NumberField K] (n : Nat) (B : Real) : Set (AdelicGeneralLinearGroup K n) :=
  Set.ofPred (fun g =>
    And (Membership.mem (godementJacquetBoundedIntegralMatrices K n B) g.val)
      (Membership.mem (godementJacquetBoundedIntegralMatrices K n B) g.inv))

theorem isCompact_godementJacquetBoundedIntegralMatrices
    (K : Type*) [Field K] [NumberField K] (n : Nat) (B : Real) :
    IsCompact (godementJacquetBoundedIntegralMatrices K n B) := by
  let A := MatrixPartAdeles K
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let P := HeightOneSpectrum (RingOfIntegers K)
  let C (w : InfinitePlace K) : Set w.Completion := Set.ofPred (fun x => norm x <= B)
  have hC (w : InfinitePlace K) : IsCompact (C w) := by
    let f := InfinitePlace.Completion.extensionEmbedding w
    have hF : Topology.IsClosedEmbedding f := (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding
    have hEq : C w = Set.preimage f (Metric.closedBall (0 : Complex) B) := by
      ext x
      change norm x <= B <-> dist (f x) (0 : Complex) <= B
      have hd := (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq x 0
      change dist (f x) (f 0) = dist x 0 at hd
      rw [map_zero] at hd
      rw [hd, dist_zero_right]
    rw [hEq]
    exact hF.isCompact_preimage (isCompact_closedBall _ _)
  let I := Set.pi Set.univ C
  let O : Set F := Set.ofPred (fun a => forall p : P, Membership.mem (p.adicCompletionIntegers K) (a p))
  have hI : IsCompact I := isCompact_univ_pi hC
  have hO : IsCompact O := isCompact_integralFiniteAdeles
  let S : Set A := I.prod O
  have hS : IsCompact S := hI.prod hO
  let T := Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => S))
  have hT : IsCompact T := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => hS))
  have hEq : godementJacquetBoundedIntegralMatrices K n B = T := by
    ext M
    constructor
    . intro h i hi j hj
      exact And.intro (fun w _ => (h i j).1 w) ((h i j).2)
    . intro h i j
      have hEntry := h i (Set.mem_univ i) j (Set.mem_univ j)
      exact And.intro (fun w => hEntry.1 w (Set.mem_univ w)) hEntry.2
  rw [hEq]
  exact hT

theorem isCompact_godementJacquetBoundedIntegralMatrixUnits
    (K : Type*) [Field K] [NumberField K] (n : Nat) (B : Real) :
    IsCompact (godementJacquetBoundedIntegralMatrixUnits K n B) := by
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let P := HeightOneSpectrum (RingOfIntegers K)
  let projection (a : F) (p : P) : p.adicCompletion K := a p
  have hInj : Function.Injective projection := DFunLike.coe_injective
  have hCont : Continuous projection := continuous_pi (fun p => RestrictedProduct.continuous_eval p)
  let _ : T2Space F := T2Space.of_injective_continuous hInj hCont
  let _ : T2Space (InfiniteAdeleRing K) :=
    inferInstanceAs (T2Space (forall w : InfinitePlace K, w.Completion))
  let _ : T2Space (MatrixPartAdeles K) := inferInstanceAs (T2Space (Prod (InfiniteAdeleRing K) F))
  let S := godementJacquetBoundedIntegralMatrices K n B
  have hS := isCompact_godementJacquetBoundedIntegralMatrices K n B
  let O := Set.preimage MulOpposite.unop S
  have hO : IsCompact O := MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hS
  have hProd : IsCompact (S.prod O) := hS.prod hO
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage hProd

/-- Reusing a half-radius cover of a compact unit ball gives a geometric
bound on the number of balls needed at every dyadic radius. -/
theorem exists_unitBall_dyadicCover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [ProperSpace E] :
    Exists (fun N : Nat => forall j : Nat,
      Exists (fun centers : (Fin j -> Fin N) -> E => forall x : E,
        norm x <= 1 -> Exists (fun i => norm (x - centers i) <= (1 / 2 : Real) ^ j))) := by
  let U (c : E) := Metric.ball c (1 / 2 : Real)
  have hCover : Metric.closedBall (0 : E) 1 <= Set.iUnion U := by
    intro x hx
    exact Set.mem_iUnion.mpr (Exists.intro x (Metric.mem_ball_self (by norm_num)))
  choose T hT using (isCompact_closedBall (0 : E) 1).elim_finite_subcover U
    (fun _ => Metric.isOpen_ball) hCover
  let I := {x : E // Membership.mem T x}
  let N := Fintype.card I
  let e : Equiv I (Fin N) := Fintype.equivFin I
  let c (i : Fin N) : E := (e.symm i).val
  have hHalf (x : E) (hx : norm x <= 1) :
      Exists (fun i : Fin N => norm (x - c i) <= (1 / 2 : Real)) := by
    have hMem : Membership.mem (Metric.closedBall (0 : E) 1) x := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx
    choose y hy using Set.mem_iUnion.mp (hT hMem)
    choose hyT hyIn using Set.mem_iUnion.mp hy
    let i := e (Subtype.mk y hyT)
    have hi : c i = y := congrArg Subtype.val (e.symm_apply_apply (Subtype.mk y hyT))
    refine Exists.intro i ?_
    rw [hi]
    exact ((dist_eq_norm x y).symm.trans_lt (Metric.mem_ball.mp hyIn)).le
  refine Exists.intro N (fun j => ?_)
  induction j with
  | zero =>
      refine Exists.intro (fun _ => 0) (fun x hx => Exists.intro (fun i => Fin.elim0 i) ?_)
      simpa only [sub_zero, pow_zero] using hx
  | succ j ih =>
      choose D hD using ih
      refine Exists.intro (fun a => c (a 0) + HSMul.hSMul (1 / 2 : Real) (D (Fin.tail a))) ?_
      intro x hx
      choose i hi using hHalf x hx
      let y := HSMul.hSMul (2 : Real) (x - c i)
      have hy : norm y <= 1 := by
        dsimp only [y]
        rw [norm_smul, show norm (2 : Real) = 2 by norm_num]
        linarith
      choose a ha using hD y hy
      refine Exists.intro (Fin.cons i a) ?_
      simp only [Fin.cons_zero, Fin.tail_cons]
      have hDiff : x - (c i + HSMul.hSMul (1 / 2 : Real) (D a)) =
          HSMul.hSMul (1 / 2 : Real) (y - D a) := by
        dsimp only [y]
        rw [smul_sub, smul_smul, show (1 / 2 : Real) * 2 = 1 by norm_num, one_smul]
        abel
      rw [hDiff, norm_smul, show norm (1 / 2 : Real) = (1 / 2 : Real) by norm_num, pow_succ']
      exact mul_le_mul_of_nonneg_left ha (by norm_num)

end Robin1984.GRH
