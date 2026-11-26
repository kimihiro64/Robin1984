import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Gram-Schmidt orthonormalization and archimedean Iwasawa factorization for general linear groups over the real or complex field.
- Formalization note: Factors an invertible matrix into a positive-diagonal upper-triangular matrix and a unitary matrix, and proves uniqueness.
- PROVENANCE-END
-/

/-!
# Positive triangular factors over the real and complex fields

Gram-Schmidt gives a unitary matrix and an upper-triangular matrix
whose diagonal entries are the positive norms of the residual vectors.
Reversing the adjoint factorization puts the unitary factor on the
right, as required in the archimedean zeta integral. These two factors
are unique.
-/

set_option autoImplicit false

open InnerProductSpace Module

namespace Robin1984.GRH

private theorem orthonormalBasis_positiveTriangularTransition
    {F E : Type*} [RCLike F] [NormedAddCommGroup E] [InnerProductSpace F E]
    [FiniteDimensional F E] {n : Nat}
    (base : OrthonormalBasis (Fin n) F E) (b : Basis (Fin n) F E) :
    exists Q R : Matrix (Fin n) (Fin n) F,
      And (Membership.mem (Matrix.unitaryGroup (Fin n) F) Q)
        (And R.IsUpperTriangular
          (And (forall i, exists x : Real, And (0 < x) (R i i = (x : F)))
            (Q * R = base.toBasis.toMatrix b))) := by
  classical
  have hdim : finrank F E = Fintype.card (Fin n) := finrank_eq_card_basis b
  let u := gramSchmidtOrthonormalBasis hdim b
  let g := gramSchmidt F b
  let Q := base.toBasis.toMatrix u
  let R := u.toBasis.toMatrix b
  have hUnitary : Membership.mem (Matrix.unitaryGroup (Fin n) F) Q :=
    base.toMatrix_orthonormalBasis_mem_unitary u
  have hTriangle : R.IsUpperTriangular :=
    gramSchmidtOrthonormalBasis_inv_isUpperTriangular hdim b
  have hFactor : Q * R = base.toBasis.toMatrix b :=
    base.toBasis.toMatrix_mul_toMatrix u.toBasis b
  refine Exists.intro Q (Exists.intro R (And.intro hUnitary
    (And.intro hTriangle (And.intro ?_ hFactor))))
  intro i
  have hG : Not (g i = 0) := gramSchmidt_ne_zero i b.linearIndependent
  have hNorm : 0 < norm (g i) := norm_pos_iff.mpr hG
  refine Exists.intro (norm (g i)) (And.intro hNorm ?_)
  have hProj (j : Fin n) (hj : Membership.mem (Finset.Iio i) j) :
      inner F (g i) (g j) = 0 :=
    gramSchmidt_orthogonal F b (ne_of_gt (Finset.mem_Iio.mp hj))
  have hS : inner F (g i) (b i) = inner F (g i) (g i) := by
    let w (j : Fin n) := HSMul.hSMul
      (inner F (g j) (b i) / (norm (g j) : F) ^ 2) (g j)
    have hB : b i = g i + (Finset.Iio i).sum w := gramSchmidt_def'' F b i
    calc
      _ = inner F (g i) (g i + (Finset.Iio i).sum w) :=
        congrArg (fun z : E => inner F (g i) z) hB
      _ = _ := by
        rw [inner_add_right, inner_sum]
        have h0 : (Finset.Iio i).sum (fun j => inner F (g i) (w j)) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [show w j = HSMul.hSMul
            (inner F (g j) (b i) / (norm (g j) : F) ^ 2) (g j) from rfl,
            inner_smul_right, hProj j hj, mul_zero]
        rw [h0, add_zero]
  have hu : u i = HSMul.hSMul (Inv.inv (norm (g i) : F)) (g i) := by
    change gramSchmidtOrthonormalBasis hdim b i = gramSchmidtNormed F b i
    exact gramSchmidtOrthonormalBasis_apply hdim
      ((gramSchmidtNormed_linearIndependent b.linearIndependent).ne_zero i)
  have hD : R i i = inner F (u i) (b i) := by
    unfold R
    rw [Basis.toMatrix_apply]
    exact u.repr_apply_apply (b i) i
  have hNN : Not ((norm (g i) : F) = 0) := by
    simpa only [RCLike.ofReal_eq_zero] using (ne_of_gt hNorm)
  rw [hD, hu, inner_smul_left, hS, inner_self_eq_norm_sq_to_K, RCLike.conj_inv, RCLike.conj_ofReal]
  simp [pow_two, hNN]

/-- An invertible real or complex matrix has a QR factorization whose
upper-triangular factor has positive real diagonal entries. -/
theorem exists_positiveQR_of_matrix_unit
    {F : Type*} [RCLike F] {n : Nat} (g : Units (Matrix (Fin n) (Fin n) F)) :
    exists Q R : Matrix (Fin n) (Fin n) F,
      And (Membership.mem (Matrix.unitaryGroup (Fin n) F) Q)
        (And R.IsUpperTriangular
          (And (forall i, exists x : Real, And (0 < x) (R i i = (x : F)))
            (Q * R = g.val))) := by
  classical
  let E := EuclideanSpace F (Fin n)
  let base : OrthonormalBasis (Fin n) F E := EuclideanSpace.basisFun (Fin n) F
  let L := Matrix.toLinAlgEquiv base.toBasis
  let u : Units (Module.End F E) := by
    exact Units.map L.toRingEquiv.toMonoidHom g
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv u
  let b := base.toBasis.map e
  have hM : base.toBasis.toMatrix b = g.val := by
    have hr : LinearMap.toMatrixAlgEquiv base.toBasis (L g.val) = g.val :=
      LinearMap.toMatrixAlgEquiv_toLinAlgEquiv base.toBasis g.val
    rw [<- hr]
    ext i j
    rw [Basis.toMatrix_apply, LinearMap.toMatrixAlgEquiv_apply]
    change base.toBasis.repr ((base.toBasis.map e) j) i = _
    rw [Basis.map_apply]
    rfl
  simpa only [hM] using orthonormalBasis_positiveTriangularTransition base b

/-- An invertible real or complex matrix is a positive-diagonal upper
triangular matrix times a unitary matrix. -/
theorem exists_positive_upperTriangular_mul_unitary
    {F : Type*} [RCLike F] {n : Nat} (g : Units (Matrix (Fin n) (Fin n) F)) :
    exists R Q : Matrix (Fin n) (Fin n) F,
      And R.IsUpperTriangular
        (And (forall i, exists x : Real, And (0 < x) (R i i = (x : F)))
          (And (Membership.mem (Matrix.unitaryGroup (Fin n) F) Q) (R * Q = g.val))) := by
  let e : Equiv.Perm (Fin n) := Fin.revPerm
  let flip (M : Matrix (Fin n) (Fin n) F) := (Matrix.conjTranspose M).submatrix e e
  have hOne : flip 1 = 1 := by
    unfold flip
    rw [Matrix.conjTranspose_one, Matrix.submatrix_one_equiv]
  have hMul (A B : Matrix (Fin n) (Fin n) F) : flip (A * B) = flip B * flip A := by
    unfold flip
    rw [Matrix.conjTranspose_mul]
    exact (Matrix.submatrix_mul_equiv (Matrix.conjTranspose B) (Matrix.conjTranspose A) e e e).symm
  have hInv (A : Matrix (Fin n) (Fin n) F) : flip (flip A) = A := by
    ext i j
    change star (star (A (Fin.rev (Fin.rev i)) (Fin.rev (Fin.rev j)))) = A i j
    rw [Fin.rev_rev, Fin.rev_rev, star_star]
  have hStar (A : Matrix (Fin n) (Fin n) F) : star (flip A) = flip (star A) := by
    ext i j
    rfl
  let h : Units (Matrix (Fin n) (Fin n) F) :=
    { val := flip g.val
      inv := flip (Inv.inv g).val
      val_inv := by rw [<- hMul, Units.inv_mul, hOne]
      inv_val := by rw [<- hMul, Units.mul_inv, hOne] }
  choose Q R hQR using exists_positiveQR_of_matrix_unit h
  refine Exists.intro (flip R) (Exists.intro (flip Q) (And.intro ?_
    (And.intro ?_ (And.intro ?_ ?_))))
  . intro i j hij
    change star (R (Fin.rev j) (Fin.rev i)) = 0
    have hLt : Fin.rev i < Fin.rev j := Fin.rev_lt_rev.mpr hij
    have hZero : R (Fin.rev j) (Fin.rev i) = 0 := hQR.2.1 hLt
    exact (congrArg star hZero).trans (star_zero F)
  . intro i
    choose x hx using hQR.2.2.1 (Fin.rev i)
    refine Exists.intro x (And.intro hx.1 ?_)
    change star (R (Fin.rev i) (Fin.rev i)) = (x : F)
    rw [hx.2]
    exact RCLike.conj_ofReal x
  . apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [hStar, <- hMul, Matrix.mem_unitaryGroup_iff.mp hQR.1, hOne]
  . have he := congrArg flip hQR.2.2.2
    change flip (Q * R) = flip (flip g.val) at he
    rwa [hMul, hInv] at he

private theorem eq_diagonal_of_unitary_upperTriangular
    {F : Type*} [RCLike F] {n : Nat} (U : Matrix (Fin n) (Fin n) F)
    (hU : Membership.mem (Matrix.unitaryGroup (Fin n) F) U)
    (hTri : U.IsUpperTriangular) :
    U = Matrix.diagonal (fun i => U i i) := by
  classical
  let _ : Invertible U :=
    { invOf := star U
      invOf_mul_self := Matrix.mem_unitaryGroup_iff'.mp hU
      mul_invOf_self := Matrix.mem_unitaryGroup_iff.mp hU }
  have hInv : Inv.inv U = star U := (Matrix.invOf_eq_nonsing_inv U).symm
  have hTriInv : (Inv.inv U).IsUpperTriangular :=
    Matrix.blockTriangular_inv_of_blockTriangular hTri
  have hTriStar : (star U).IsUpperTriangular := by simpa only [hInv] using hTriInv
  ext i j
  by_cases h : i = j
  . subst j
    rw [Matrix.diagonal_apply_eq]
  . rw [Matrix.diagonal_apply_ne _ h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    . have hZero : star (U i j) = 0 := hTriStar hlt
      exact star_injective (hZero.trans (star_zero F).symm)
    . exact hTri hgt

/-- A positive-diagonal upper-triangular factor and a right unitary
factor are uniquely determined by their product. -/
theorem positiveUpperTriangular_unitary_factors_unique
    {F : Type*} [RCLike F] {n : Nat} (R S Q V : Matrix (Fin n) (Fin n) F)
    (hR : R.IsUpperTriangular) (hS : S.IsUpperTriangular)
    (hpR : forall i, exists x : Real, And (0 < x) (R i i = (x : F)))
    (hpS : forall i, exists x : Real, And (0 < x) (S i i = (x : F)))
    (hQ : Membership.mem (Matrix.unitaryGroup (Fin n) F) Q)
    (hV : Membership.mem (Matrix.unitaryGroup (Fin n) F) V)
    (hFactor : R * Q = S * V) :
    And (R = S) (Q = V) := by
  classical
  have hd : IsUnit R.det := by
    rw [Matrix.det_of_isUpperTriangular hR]
    apply isUnit_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    choose x hx using hpR i
    rw [hx.2]
    exact fun h => (ne_of_gt hx.1) (RCLike.ofReal_eq_zero.mp h)
  let _ : Invertible R := Matrix.invertibleOfIsUnitDet R hd
  have hInvR : Inv.inv R * R = 1 := by
    rw [<- Matrix.invOf_eq_nonsing_inv]
    exact invOf_mul_self R
  have hRInv : R * Inv.inv R = 1 := by
    rw [<- Matrix.invOf_eq_nonsing_inv]
    exact mul_invOf_self R
  let X := Inv.inv R * S
  have hTri : X.IsUpperTriangular :=
    (Matrix.blockTriangular_inv_of_blockTriangular hR).mul hS
  have hVstar : Membership.mem (Matrix.unitaryGroup (Fin n) F) (star V) := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [star_star]
    exact Matrix.mem_unitaryGroup_iff.mp hV
  have hVX : X = Q * star V := by
    calc
      _ = (Inv.inv R * S) * (V * star V) := by
        rw [Matrix.mem_unitaryGroup_iff.mp hV, mul_one]
      _ = Inv.inv R * (S * V) * star V := by simp only [mul_assoc]
      _ = Inv.inv R * (R * Q) * star V := by rw [<- hFactor]
      _ = _ := by rw [<- mul_assoc (Inv.inv R) R Q, hInvR, one_mul]
  have hX : Membership.mem (Matrix.unitaryGroup (Fin n) F) X := by
    rw [hVX]
    exact (Matrix.unitaryGroup (Fin n) F).mul_mem hQ hVstar
  have hXd := eq_diagonal_of_unitary_upperTriangular X hX hTri
  have hRS : R * X = S := by
    unfold X
    rw [<- mul_assoc, hRInv, one_mul]
  have hXi (i : Fin n) : X i i = 1 := by
    choose a ha using hpR i
    choose b hb using hpS i
    have hA : Not ((a : F) = 0) := by simpa only [RCLike.ofReal_eq_zero] using ne_of_gt ha.1
    have hProd : R i i * X i i = S i i := by
      calc
        _ = (R * Matrix.diagonal (fun j => X j j)) i i :=
          (Matrix.mul_diagonal (fun j => X j j) R i i).symm
        _ = (R * X) i i := congrArg (fun M : Matrix (Fin n) (Fin n) F => (R * M) i i) hXd.symm
        _ = _ := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i i) hRS
    rw [ha.2, hb.2] at hProd
    have hPos : X i i = ((b / a : Real) : F) := by
      rw [RCLike.ofReal_div]
      exact (eq_div_iff hA).mpr ((mul_comm _ _).trans hProd)
    have hU := Matrix.mem_unitaryGroup_iff'.mp hX
    have hStar : star (Matrix.diagonal (fun j => X j j)) *
        Matrix.diagonal (fun j => X j j) = 1 := by
      exact (congrArg (fun M : Matrix (Fin n) (Fin n) F => star M * M) hXd).symm.trans hU
    have hUnit : star (X i i) * X i i = 1 := by
      change Matrix.conjTranspose (Matrix.diagonal (fun j => X j j)) *
        Matrix.diagonal (fun j => X j j) = 1 at hStar
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at hStar
      have he := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i i) hStar
      simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply] using he
    rw [hPos] at hUnit
    change (starRingEnd F) ((b / a : Real) : F) * ((b / a : Real) : F) = 1 at hUnit
    rw [RCLike.conj_ofReal, <- RCLike.ofReal_mul, <- RCLike.ofReal_one] at hUnit
    have hsq : (b / a) ^ 2 = 1 := by
      rw [pow_two]
      exact RCLike.ofReal_injective hUnit
    have hp : b / a = 1 :=
      (pow_eq_one_iff_of_nonneg (div_nonneg hb.1.le ha.1.le)
        (ne_of_gt (Nat.zero_lt_succ 1))).mp hsq
    rw [hPos, hp, RCLike.ofReal_one]
  have hXOne : X = 1 := by
    rw [hXd]
    simp only [hXi, Matrix.diagonal_one]
  have hEqR : R = S := by rwa [hXOne, mul_one] at hRS
  refine And.intro hEqR ?_
  rw [<- hEqR] at hFactor
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) F => Inv.inv R * M) hFactor
  simpa only [<- mul_assoc, hInvR, one_mul] using he

end Robin1984.GRH
