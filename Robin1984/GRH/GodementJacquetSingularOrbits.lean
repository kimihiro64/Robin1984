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
singular orbit. The stabilizer has determinant one over every scalar
extension, including the adele ring.
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

end Robin1984.GRH
