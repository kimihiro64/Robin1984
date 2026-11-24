import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and the rank decomposition of the singular-matrix terms.
- Formalization note: Identifies the upper unipotent stabilizers of rank projections and transports them to singular rational matrices after scalar extension.
- PROVENANCE-END
-/

/-!
# Singular-matrix orbits in the Godement-Jacquet zeta integral

An upper unipotent block subgroup fixes the rank projection on the left.
A two-sided rational change of basis carries the stabilizer to any
singular orbit. The upper unipotent factor has determinant one over every
scalar extension. The full rational stabilizer includes its general
linear Levi factor.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

variable {R : Type*} [CommRing R] {r k : Nat}

private abbrev BlockIndex (r k : Nat) := Sum (Fin r) (Fin k)

/-- The standard rank projection with an identity block and a zero block. -/
def godementJacquetRankProjection (R : Type*) [CommRing R] (r k : Nat) :
    Matrix (BlockIndex r k) (BlockIndex r k) R :=
  Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) R) 0 0 0

/-- An upper unipotent block matrix with its inverse. -/
def godementJacquetUpperUnipotent (B : Matrix (Fin r) (Fin k) R) :
    Matrix.GeneralLinearGroup (BlockIndex r k) R where
  val := Matrix.fromBlocks 1 B 0 1
  inv := Matrix.fromBlocks 1 (-B) 0 1
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]

/-- The off-diagonal additive block as a subgroup of the general linear group. -/
def godementJacquetUpperUnipotentHom :
    MonoidHom (Multiplicative (Matrix (Fin r) (Fin k) R))
      (Matrix.GeneralLinearGroup (BlockIndex r k) R) where
  toFun B := godementJacquetUpperUnipotent (Multiplicative.toAdd B)
  map_one' := by
    apply Units.ext
    exact Matrix.fromBlocks_one
  map_mul' B C := by
    apply Units.ext
    change Matrix.fromBlocks 1 (Multiplicative.toAdd B + Multiplicative.toAdd C) 0 1 =
      Matrix.fromBlocks 1 (Multiplicative.toAdd B) 0 1 *
      Matrix.fromBlocks 1 (Multiplicative.toAdd C) 0 1
    rw [Matrix.fromBlocks_multiply]
    simp [add_comm]

theorem godementJacquetUpperUnipotent_injective :
    Function.Injective (godementJacquetUpperUnipotent (R := R) (r := r) (k := k)) := by
  intro B C h
  ext i j
  exact congrArg (fun g : Matrix.GeneralLinearGroup (BlockIndex r k) R =>
    g.val (Sum.inl i) (Sum.inr j)) h

/-- The upper unipotent subgroup has determinant one. -/
theorem godementJacquetUpperUnipotent_det (B : Matrix (Fin r) (Fin k) R) :
    Matrix.GeneralLinearGroup.det (godementJacquetUpperUnipotent B) = 1 := by
  apply Units.ext
  change (Matrix.fromBlocks 1 B 0 1).det = 1
  simp

/-- Upper unipotent multiplication fixes the rank projection on the left. -/
theorem godementJacquetUpperUnipotent_mul_rankProjection (B : Matrix (Fin r) (Fin k) R) :
    (godementJacquetUpperUnipotent B).val * godementJacquetRankProjection R r k =
      godementJacquetRankProjection R r k := by
  unfold godementJacquetUpperUnipotent godementJacquetRankProjection
  rw [Matrix.fromBlocks_multiply]
  simp

private theorem godementJacquetUpperUnipotent_inv (B : Matrix (Fin r) (Fin k) R) :
    Inv.inv (godementJacquetUpperUnipotent B) = godementJacquetUpperUnipotent (-B) :=
  Units.ext rfl

/-- Unipotent change of the left input leaves the test-function kernel unchanged. -/
theorem godementJacquetSingularKernel_left_invariant
    {V : Type*} (Phi : Matrix (BlockIndex r k) (BlockIndex r k) R -> V)
    (a : Units R) (g h : Matrix.GeneralLinearGroup (BlockIndex r k) R)
    (B : Matrix (Fin r) (Fin k) R) :
    Phi ((Inv.inv (godementJacquetUpperUnipotent B * g)).val *
       (Matrix.GeneralLinearGroup.scalar (BlockIndex r k) a).val *
       godementJacquetRankProjection R r k * h.val) =
    Phi ((Inv.inv g).val * (Matrix.GeneralLinearGroup.scalar (BlockIndex r k) a).val *
       godementJacquetRankProjection R r k * h.val) := by
  have hc := congrArg Units.val (Matrix.GeneralLinearGroup.scalar_commute
    a (godementJacquetUpperUnipotent (-B))).symm
  simp only [Units.val_mul] at hc
  rw [mul_inv_rev, godementJacquetUpperUnipotent_inv, Units.val_mul]
  apply congrArg Phi
  let z := (Matrix.GeneralLinearGroup.scalar (BlockIndex r k) a).val
  let u := (godementJacquetUpperUnipotent (-B)).val
  let E := godementJacquetRankProjection R r k
  change (g.inv * u) * z * E * h.val = g.inv * z * E * h.val
  calc
    (g.inv * u) * z * E * h.val = g.inv * ((u * z) * E) * h.val := by
      simp only [mul_assoc]
    _ = g.inv * ((z * u) * E) * h.val := by rw [hc]
    _ = g.inv * (z * (u * E)) * h.val := by rw [mul_assoc z u E]
    _ = g.inv * z * E * h.val := by
      change g.inv * (z * ((godementJacquetUpperUnipotent (-B)).val *
        godementJacquetRankProjection R r k)) * h.val = _
      rw [godementJacquetUpperUnipotent_mul_rankProjection]
      simp only [mul_assoc, E]

/-- A singular matrix lies in the orbit of a rank projection with a
nonempty complementary block. -/
theorem exists_godementJacquetSingularOrbit
    {F m : Type*} [Field F] [Fintype m] [DecidableEq m]
    (A : Matrix m m F) (hA : A.det = 0) :
    0 < Fintype.card m - A.rank /\
      exists e : Equiv m (BlockIndex A.rank (Fintype.card m - A.rank)),
      exists a b : Matrix.GeneralLinearGroup m F,
        a.val * A * b.val =
          (godementJacquetRankProjection F A.rank (Fintype.card m - A.rank)).submatrix e e := by
  have hRank : A.rank < Fintype.card m := by
    refine lt_of_le_of_ne A.rank_le_card_width ?_
    intro hr
    have hdim := A.mulVecLin.finrank_range_add_finrank_ker
    change A.rank + Module.finrank F (LinearMap.ker A.mulVecLin) =
      Module.finrank F (m -> F) at hdim
    rw [hr, Module.finrank_pi] at hdim
    have hker : Module.finrank F (LinearMap.ker A.mulVecLin) = 0 :=
      Nat.add_left_cancel (hdim.trans (Nat.add_zero _).symm)
    have hInjective : Function.Injective A.mulVec :=
      LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
    exact ((Matrix.isUnit_iff_isUnit_det A).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hInjective)).ne_zero hA
  choose V U e h using Matrix.exists_rank_normal_form A
  let a := h.1.unit
  let b := h.2.1.unit
  refine And.intro (Nat.sub_pos_of_lt hRank)
    (Exists.intro e (Exists.intro a (Exists.intro b ?_)))
  change a.val * A * b.val = _
  rw [h.1.unit_spec, h.2.1.unit_spec]
  exact h.2.2

/-- Transport the upper unipotent stabilizer from the rank projection to
a matrix in its two-sided orbit, preserving determinant one. -/
theorem exists_godementJacquetSingularStabilizer
    {m : Type*} [Fintype m] [DecidableEq m]
    (P : Matrix m m R) (e : Equiv m (BlockIndex r k))
    (a b : Matrix.GeneralLinearGroup m R)
    (h : a.val * P * b.val = (godementJacquetRankProjection R r k).submatrix e e) :
    exists U : MonoidHom (Multiplicative (Matrix (Fin r) (Fin k) R))
        (Matrix.GeneralLinearGroup m R),
      Function.Injective U /\
        (forall B, Matrix.GeneralLinearGroup.det (U B) = 1) /\
        (forall B, (U B).val * P = P) := by
  let reindexing := Matrix.reindexRingEquiv (R := R) e.symm
  let reindexUnits := Units.mapEquiv reindexing.toMulEquiv
  let upper := godementJacquetUpperUnipotentHom (R := R) (r := r) (k := k)
  let conjugate := MulAut.conj (Inv.inv a)
  let U := conjugate.toMonoidHom.comp (reindexUnits.toMonoidHom.comp upper)
  have hU (B : Multiplicative (Matrix (Fin r) (Fin k) R)) :
      U B = Inv.inv a * reindexUnits (upper B) * a := by
    change conjugate (reindexUnits (upper B)) = _
    rw [show conjugate = MulAut.conj (Inv.inv a) from rfl, MulAut.conj_apply, inv_inv]
  have hDet (B : Multiplicative (Matrix (Fin r) (Fin k) R)) :
      Matrix.GeneralLinearGroup.det (reindexUnits (upper B)) = 1 := by
    apply Units.ext
    change ((upper B).val.submatrix e e).det = 1
    rw [Matrix.det_submatrix_equiv_self]
    exact congrArg Units.val (godementJacquetUpperUnipotent_det (Multiplicative.toAdd B))
  refine Exists.intro U (And.intro ?_ (And.intro ?_ ?_))
  . exact conjugate.injective.comp (reindexUnits.injective.comp
      godementJacquetUpperUnipotent_injective)
  . intro B
    rw [hU, map_mul, map_mul, map_inv, hDet, mul_one, inv_mul_cancel]
  . intro B
    let p := godementJacquetRankProjection R r k
    let u := reindexUnits (upper B)
    have hFix : u.val * (a.val * P * b.val) = a.val * P * b.val := by
      rw [h]
      change reindexing (upper B).val * reindexing p = reindexing p
      rw [<- map_mul]
      exact congrArg reindexing
        (godementJacquetUpperUnipotent_mul_rankProjection (Multiplicative.toAdd B))
    have hFixRight : u.val * (a.val * P) = a.val * P := by
      have hh := congrArg (fun X : Matrix m m R => X * b.inv) hFix
      simpa only [mul_assoc, b.val_inv, mul_one] using hh
    rw [hU, Units.val_mul, Units.val_mul]
    change (a.inv * u.val * a.val) * P = P
    calc
      (a.inv * u.val * a.val) * P = a.inv * (u.val * (a.val * P)) := by
        simp only [mul_assoc]
      _ = a.inv * (a.val * P) := by rw [hFixRight]
      _ = P := by rw [<- mul_assoc, a.inv_val, one_mul]

/-- The stabilizer of a singular rational matrix after extension of
scalars, in particular over the adeles of a number field. -/
theorem exists_godementJacquetSingularStabilizer_map
    {F m : Type*} [Field F] [Fintype m] [DecidableEq m]
    (f : RingHom F R) (P : Matrix m m F) (hP : P.det = 0) :
    0 < Fintype.card m - P.rank /\
      exists U : MonoidHom (Multiplicative
          (Matrix (Fin P.rank) (Fin (Fintype.card m - P.rank)) R))
          (Matrix.GeneralLinearGroup m R),
        Function.Injective U /\
          (forall B, Matrix.GeneralLinearGroup.det (U B) = 1) /\
          (forall B, (U B).val * P.map f = P.map f) := by
  have hOrbit := exists_godementJacquetSingularOrbit P hP
  choose e a b hab using hOrbit.2
  let c := Matrix.GeneralLinearGroup.map f a
  let d := Matrix.GeneralLinearGroup.map f b
  let liftMatrix : RingHom (Matrix m m F) (Matrix m m R) := RingHom.mapMatrix f
  have hMapped := congrArg (fun X => liftMatrix X) hab
  simp only [map_mul] at hMapped
  change c.val * P.map f * d.val =
    ((godementJacquetRankProjection F P.rank (Fintype.card m - P.rank)).submatrix e e).map f
    at hMapped
  have hProjection :
      (godementJacquetRankProjection F P.rank (Fintype.card m - P.rank)).map f =
        godementJacquetRankProjection R P.rank (Fintype.card m - P.rank) := by
    simp [godementJacquetRankProjection, Matrix.fromBlocks_map]
  have hOver :
      c.val * P.map f * d.val =
        (godementJacquetRankProjection R P.rank (Fintype.card m - P.rank)).submatrix e e := by
    rw [hMapped]
    exact congrArg (fun Q => Q.submatrix e e) hProjection
  exact And.intro hOrbit.1 (exists_godementJacquetSingularStabilizer (P.map f) e c d hOver)

/-- A matrix fixes the rank projection on the left exactly when its
first block column is the first block column of the identity. -/
theorem godementJacquetRankProjection_leftStabilizer_iff
    (X : Matrix (BlockIndex r k) (BlockIndex r k) R) :
    X * godementJacquetRankProjection R r k = godementJacquetRankProjection R r k <->
      Exists (fun B : Matrix (Fin r) (Fin k) R =>
        Exists (fun D : Matrix (Fin k) (Fin k) R => X = Matrix.fromBlocks 1 B 0 D)) := by
  let A := X.submatrix Sum.inl Sum.inl
  let B := X.submatrix Sum.inl Sum.inr
  let C := X.submatrix Sum.inr Sum.inl
  let D := X.submatrix Sum.inr Sum.inr
  have hX : X = Matrix.fromBlocks A B C D := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  have hMul : X * godementJacquetRankProjection R r k = Matrix.fromBlocks A 0 C 0 := calc
    _ = Matrix.fromBlocks A B C D * godementJacquetRankProjection R r k :=
      congrArg (fun M => M * godementJacquetRankProjection R r k) hX
    _ = _ := by
      rw [godementJacquetRankProjection, Matrix.fromBlocks_multiply]
      simp
  constructor
  . intro h
    have hz : Matrix.fromBlocks A 0 C 0 = godementJacquetRankProjection R r k := hMul.symm.trans h
    have hA : A = 1 := Matrix.ext (fun i j =>
      congrArg (fun M : Matrix (BlockIndex r k) (BlockIndex r k) R => M (Sum.inl i) (Sum.inl j)) hz)
    have hC : C = 0 := Matrix.ext (fun i j =>
      congrArg (fun M : Matrix (BlockIndex r k) (BlockIndex r k) R => M (Sum.inr i) (Sum.inl j)) hz)
    exact Exists.intro B (Exists.intro D (by simpa only [hA, hC] using hX))
  . intro h
    choose H V hY using h
    rw [hY, godementJacquetRankProjection, Matrix.fromBlocks_multiply]
    simp

/-- The lower-right general linear group in the left stabilizer of the rank projection. -/
def godementJacquetBlockLevi (V : Matrix.GeneralLinearGroup (Fin k) R) :
    Matrix.GeneralLinearGroup (BlockIndex r k) R where
  val := Matrix.fromBlocks 1 0 0 V.val
  inv := Matrix.fromBlocks 1 0 0 V.inv
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]

/-- Conjugating by a lower-right Levi block acts on the upper
unipotent coordinates by right multiplication by its inverse. -/
theorem godementJacquetBlockLevi_upperUnipotent_conj
    (V : Matrix.GeneralLinearGroup (Fin k) R) (B : Matrix (Fin r) (Fin k) R) :
    godementJacquetBlockLevi (r := r) V * godementJacquetUpperUnipotent B *
        Inv.inv (godementJacquetBlockLevi (r := r) V) =
      godementJacquetUpperUnipotent (B * V.inv) := by
  apply Units.ext
  change Matrix.fromBlocks 1 0 0 V.val * Matrix.fromBlocks 1 B 0 1 *
      Matrix.fromBlocks 1 0 0 V.inv = Matrix.fromBlocks 1 (B * V.inv) 0 1
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Every invertible left stabilizer factors through the upper unipotent and
lower-right Levi blocks. Its determinant is the determinant of that Levi block. -/
theorem exists_godementJacquetRankProjection_stabilizer_factorization
    (X : Matrix.GeneralLinearGroup (BlockIndex r k) R)
    (h : X.val * godementJacquetRankProjection R r k = godementJacquetRankProjection R r k) :
    Exists (fun B : Matrix (Fin r) (Fin k) R =>
      Exists (fun V : Matrix.GeneralLinearGroup (Fin k) R =>
        And (X = godementJacquetUpperUnipotent B * godementJacquetBlockLevi (r := r) V)
          (Matrix.GeneralLinearGroup.det V = Matrix.GeneralLinearGroup.det X))) := by
  choose C D hX using (godementJacquetRankProjection_leftStabilizer_iff X.val).mp h
  have hDet : X.val.det = D.det := by
    rw [hX]
    simp
  have hUnit : IsUnit D.det := by
    rw [<- hDet]
    exact (Matrix.isUnit_iff_isUnit_det X.val).mp X.isUnit
  have hDU : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr hUnit
  let V := hDU.unit
  have hV : V.val = D := hDU.unit_spec
  have hC : (C * V.inv) * V.val = C := by rw [Matrix.mul_assoc, V.inv_val, Matrix.mul_one]
  refine Exists.intro (C * V.inv) (Exists.intro V (And.intro ?_ ?_))
  . apply Units.ext
    change X.val = Matrix.fromBlocks 1 (C * V.inv) 0 1 * Matrix.fromBlocks 1 0 0 V.val
    rw [hX, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, hC]
    rw [hV]
  . apply Units.ext
    change V.val.det = X.val.det
    rw [hV, hDet]

section RankProjectionStabilizer

variable (R r k)

private abbrev BlockGL := Matrix.GeneralLinearGroup (Sum (Fin r) (Fin k)) R
private abbrev LeviGL := Matrix.GeneralLinearGroup (Fin k) R

/-- The embedded lower-right general linear group. -/
def godementJacquetBlockLeviHom : MonoidHom (LeviGL R k) (BlockGL R r k) where
  toFun := godementJacquetBlockLevi
  map_one' := by
    apply Units.ext
    exact Matrix.fromBlocks_one
  map_mul' A B := by
    apply Units.ext
    change Matrix.fromBlocks 1 0 0 (A.val * B.val) =
      Matrix.fromBlocks 1 0 0 A.val * Matrix.fromBlocks 1 0 0 B.val
    rw [Matrix.fromBlocks_multiply]
    simp

/-- The unipotent factor of the rank-projection stabilizer. -/
def godementJacquetProjectionUnipotent : Subgroup (BlockGL R r k) :=
  (godementJacquetUpperUnipotentHom (R := R) (r := r) (k := k)).range

/-- The full lower-right Levi factor of the rank-projection stabilizer. -/
def godementJacquetProjectionLevi : Subgroup (BlockGL R r k) :=
  (godementJacquetBlockLeviHom R r k).range

/-- The left stabilizer of the rank projection in the general linear group. -/
def godementJacquetProjectionStabilizer : Subgroup (BlockGL R r k) where
  carrier := Set.ofPred (fun A =>
    A.val * godementJacquetRankProjection R r k = godementJacquetRankProjection R r k)
  one_mem' := by
    change (1 : Matrix (Sum (Fin r) (Fin k)) (Sum (Fin r) (Fin k)) R) *
      godementJacquetRankProjection R r k = godementJacquetRankProjection R r k
    rw [Matrix.one_mul]
  mul_mem' := by
    intro A B hA hB
    let P := godementJacquetRankProjection R r k
    change A.val * P = P at hA
    change B.val * P = P at hB
    change (A.val * B.val) * P = P
    rw [Matrix.mul_assoc, hB, hA]
  inv_mem' := by
    intro A hA
    let P := godementJacquetRankProjection R r k
    change A.val * P = P at hA
    change A.inv * P = P
    calc
      A.inv * P = A.inv * (A.val * P) := congrArg (fun M => A.inv * M) hA.symm
      _ = P := by rw [<- Matrix.mul_assoc, A.inv_val, Matrix.one_mul]

theorem godementJacquetProjectionUnipotent_le_stabilizer :
    godementJacquetProjectionUnipotent R r k <= godementJacquetProjectionStabilizer R r k := by
  intro A hA
  change Exists (fun B : Multiplicative (Matrix (Fin r) (Fin k) R) =>
    godementJacquetUpperUnipotent (Multiplicative.toAdd B) = A) at hA
  choose B hB using hA
  rw [<- hB]
  exact godementJacquetUpperUnipotent_mul_rankProjection _

theorem godementJacquetProjectionLevi_le_stabilizer :
    godementJacquetProjectionLevi R r k <= godementJacquetProjectionStabilizer R r k := by
  intro A hA
  change Exists (fun V : LeviGL R k => godementJacquetBlockLevi (r := r) V = A) at hA
  choose V hV using hA
  rw [<- hV]
  change Matrix.fromBlocks 1 0 0 V.val * godementJacquetRankProjection R r k =
    godementJacquetRankProjection R r k
  rw [godementJacquetRankProjection, Matrix.fromBlocks_multiply]
  simp

private theorem upperMulBlockLevi_val (B : Matrix (Fin r) (Fin k) R) (V : LeviGL R k) :
    (godementJacquetUpperUnipotent B * godementJacquetBlockLevi (r := r) V).val =
      Matrix.fromBlocks 1 (B * V.val) 0 V.val := by
  change Matrix.fromBlocks 1 B 0 1 * Matrix.fromBlocks 1 0 0 V.val = _
  rw [Matrix.fromBlocks_multiply]
  simp

private theorem upperMulBlockLevi_inj
    (A B : Matrix (Fin r) (Fin k) R) (U V : LeviGL R k)
    (h : godementJacquetUpperUnipotent A * godementJacquetBlockLevi (r := r) U =
      godementJacquetUpperUnipotent B * godementJacquetBlockLevi (r := r) V) :
    And (A = B) (U = V) := by
  have hM := congrArg (fun A : BlockGL R r k => A.val) h
  rw [upperMulBlockLevi_val, upperMulBlockLevi_val] at hM
  have hUV : U.val = V.val := Matrix.ext (fun i j =>
    congrArg (fun T : Matrix (Sum (Fin r) (Fin k)) (Sum (Fin r) (Fin k)) R => T (Sum.inr i) (Sum.inr j)) hM)
  have hU : U = V := Units.ext hUV
  have hAB : A * U.val = B * V.val := Matrix.ext (fun i j =>
    congrArg (fun T : Matrix (Sum (Fin r) (Fin k)) (Sum (Fin r) (Fin k)) R => T (Sum.inl i) (Sum.inr j)) hM)
  rw [<- hU] at hAB
  refine And.intro ?_ hU
  have h := congrArg (fun C : Matrix (Fin r) (Fin k) R => C * U.inv) hAB
  simpa only [Matrix.mul_assoc, U.val_inv, Matrix.mul_one] using h

/-- The Levi subgroup normalizes the unipotent subgroup. -/
theorem godementJacquetProjectionLevi_normalizes_unipotent
    (l : godementJacquetProjectionLevi R r k) (u : godementJacquetProjectionUnipotent R r k) :
    Membership.mem (godementJacquetProjectionUnipotent R r k) (l.val * u.val * Inv.inv l.val) := by
  have hL := l.property
  have hU := u.property
  change Exists (fun V : LeviGL R k => godementJacquetBlockLevi (r := r) V = l.val) at hL
  change Exists (fun B : Multiplicative (Matrix (Fin r) (Fin k) R) =>
    godementJacquetUpperUnipotent (Multiplicative.toAdd B) = u.val) at hU
  choose V hV using hL
  choose B hB using hU
  change Exists (fun D : Multiplicative (Matrix (Fin r) (Fin k) R) =>
    godementJacquetUpperUnipotent (Multiplicative.toAdd D) = l.val * u.val * Inv.inv l.val)
  refine Exists.intro (Multiplicative.ofAdd (Multiplicative.toAdd B * V.inv)) ?_
  rw [<- hV, <- hB]
  exact (godementJacquetBlockLevi_upperUnipotent_conj V (Multiplicative.toAdd B)).symm

/-- The full left stabilizer is exactly the product of its
unipotent and Levi factors, with unique coordinates. -/
theorem exists_godementJacquetProjectionStabilizer_split :
    let U := godementJacquetProjectionUnipotent R r k
    let L := godementJacquetProjectionLevi R r k
    let H := godementJacquetProjectionStabilizer R r k
    Exists (fun e : Equiv (Prod U L) H => forall p, (e p).val = p.1.val * p.2.val) := by
  let U := godementJacquetProjectionUnipotent R r k
  let L := godementJacquetProjectionLevi R r k
  let H := godementJacquetProjectionStabilizer R r k
  let f (p : Prod U L) : H := Subtype.mk (p.1.val * p.2.val)
    (H.mul_mem (godementJacquetProjectionUnipotent_le_stabilizer R r k p.1.property)
      (godementJacquetProjectionLevi_le_stabilizer R r k p.2.property))
  have hSurj : Function.Surjective f := by
    intro x
    have hx := x.property
    change x.val.val * godementJacquetRankProjection R r k =
      godementJacquetRankProjection R r k at hx
    choose B V hV using exists_godementJacquetRankProjection_stabilizer_factorization x.val hx
    let u : U := Subtype.mk (godementJacquetUpperUnipotent B)
      (Exists.intro (Multiplicative.ofAdd B) rfl)
    let l : L := Subtype.mk (godementJacquetBlockLevi (r := r) V)
      (Exists.intro V rfl)
    exact Exists.intro (Prod.mk u l) (Subtype.ext hV.1.symm)
  have hInj : Function.Injective f := by
    intro x y h
    have hUX := x.1.property
    have hLX := x.2.property
    have hUY := y.1.property
    have hLY := y.2.property
    change Exists (fun B : Multiplicative (Matrix (Fin r) (Fin k) R) =>
      godementJacquetUpperUnipotent (Multiplicative.toAdd B) = x.1.val) at hUX
    change Exists (fun B : Multiplicative (Matrix (Fin r) (Fin k) R) =>
      godementJacquetUpperUnipotent (Multiplicative.toAdd B) = y.1.val) at hUY
    change Exists (fun V : LeviGL R k => godementJacquetBlockLevi (r := r) V = x.2.val) at hLX
    change Exists (fun V : LeviGL R k => godementJacquetBlockLevi (r := r) V = y.2.val) at hLY
    choose A hA using hUX
    choose B hB using hUY
    choose P hP using hLX
    choose Q hQ using hLY
    have hProd := congrArg (fun z : H => z.val) h
    change x.1.val * x.2.val = y.1.val * y.2.val at hProd
    rw [<- hA, <- hP, <- hB, <- hQ] at hProd
    have he := upperMulBlockLevi_inj R r k _ _ P Q hProd
    apply Prod.ext
    . apply Subtype.ext
      rw [<- hA, <- hB, he.1]
    . apply Subtype.ext
      rw [<- hP, <- hQ, he.2]
  exact Exists.intro (Equiv.ofBijective f (And.intro hInj hSurj)) (fun _ => rfl)

end RankProjectionStabilizer

section RankTransport

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Reindex the rank coordinates and conjugate back to the rational matrix. -/
def godementJacquetRankTransport (e : Equiv m (Sum (Fin r) (Fin k)))
    (a : Matrix.GeneralLinearGroup m R) :
    MulEquiv (BlockGL R r k) (Matrix.GeneralLinearGroup m R) :=
  (Units.mapEquiv (Matrix.reindexRingEquiv (R := R) e.symm).toMulEquiv).trans
    (MulAut.conj (Inv.inv a))

/-- Transport identifies the entire left stabilizer of a rank projection. -/
theorem godementJacquetRankTransport_mul_eq_iff
    (P : Matrix m m R) (e : Equiv m (Sum (Fin r) (Fin k)))
    (a b : Matrix.GeneralLinearGroup m R)
    (h : a.val * P * b.val =
      (godementJacquetRankProjection R r k).submatrix e e)
    (u : BlockGL R r k) :
    (godementJacquetRankTransport e a u).val * P = P <->
      u.val * godementJacquetRankProjection R r k = godementJacquetRankProjection R r k := by
  let reindexing := Matrix.reindexRingEquiv (R := R) e.symm
  let t := godementJacquetRankTransport e a u
  have ht : t.val = a.inv * reindexing u.val * a.val := by
    change ((MulAut.conj (Inv.inv a))
      ((Units.mapEquiv reindexing.toMulEquiv) u)).val = _
    rw [MulAut.conj_apply, inv_inv]
    rfl
  have hcomm : a.val * t.val = reindexing u.val * a.val := by
    rw [ht, <- Matrix.mul_assoc a.val, <- Matrix.mul_assoc a.val, a.val_inv,
      Matrix.one_mul]
  rw [<- reindexing.injective.eq_iff]
  change t.val * P = P <->
    reindexing (u.val * godementJacquetRankProjection R r k) =
      reindexing (godementJacquetRankProjection R r k)
  rw [map_mul]
  change t.val * P = P <->
    reindexing u.val * ((godementJacquetRankProjection R r k).submatrix e e) =
      (godementJacquetRankProjection R r k).submatrix e e
  rw [<- h]
  have hcombine : a.val * (t.val * P) * b.val =
      reindexing u.val * (a.val * P * b.val) := by
    rw [<- Matrix.mul_assoc a.val t.val, hcomm]
    simp only [Matrix.mul_assoc]
  constructor
  . intro hf
    rw [<- hcombine, hf]
  . intro hf
    rw [<- hcombine] at hf
    have hh := congrArg (fun Q : Matrix m m R => a.inv * Q * b.inv) hf
    simpa only [Matrix.mul_assoc, b.val_inv, Matrix.mul_one,
      <- Matrix.mul_assoc a.inv a.val, a.inv_val, Matrix.one_mul] using hh

/-- Injective homomorphisms preserve the full split stabilizer and its
normalizer action. -/
theorem exists_godementJacquetProjectionStabilizer_map_split
    {G : Type*} [Group G] (f : MonoidHom (BlockGL R r k) G) (hf : Function.Injective f) :
    let U := (godementJacquetProjectionUnipotent R r k).map f
    let L := (godementJacquetProjectionLevi R r k).map f
    let H := (godementJacquetProjectionStabilizer R r k).map f
    (Exists (fun e : Equiv (Prod U L) H => forall p, (e p).val = p.1.val * p.2.val)) /\
      (forall (l : L) (u : U), Membership.mem U (l.val * u.val * Inv.inv l.val)) := by
  let U := godementJacquetProjectionUnipotent R r k
  let L := godementJacquetProjectionLevi R r k
  let H := godementJacquetProjectionStabilizer R r k
  let eu := Subgroup.equivMapOfInjective U f hf
  let el := Subgroup.equivMapOfInjective L f hf
  let eh := Subgroup.equivMapOfInjective H f hf
  choose t ht using exists_godementJacquetProjectionStabilizer_split R r k
  refine And.intro (Exists.intro
    ((Equiv.prodCongr eu.symm.toEquiv el.symm.toEquiv).trans (t.trans eh.toEquiv)) ?_) ?_
  . intro p
    change f (t (Prod.mk (eu.symm p.1) (el.symm p.2))).val = p.1.val * p.2.val
    rw [ht, map_mul]
    have hu : f (eu.symm p.1).val = p.1.val :=
      congrArg Subtype.val (eu.apply_symm_apply p.1)
    have hl : f (el.symm p.2).val = p.2.val :=
      congrArg Subtype.val (el.apply_symm_apply p.2)
    rw [hu, hl]
  . intro l u
    let lv := el.symm l
    let uv := eu.symm u
    have hl : f lv.val = l.val := congrArg Subtype.val (el.apply_symm_apply l)
    have hu : f uv.val = u.val := congrArg Subtype.val (eu.apply_symm_apply u)
    refine Exists.intro (lv.val * uv.val * Inv.inv lv.val)
      (And.intro (godementJacquetProjectionLevi_normalizes_unipotent R r k lv uv) ?_)
    rw [map_mul, map_mul, map_inv, hl, hu]

end RankTransport

end Robin1984.GRH
