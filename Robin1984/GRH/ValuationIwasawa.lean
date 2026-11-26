import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Valuation.Integers

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The algebraic Iwasawa decomposition for the local unramified calculation in Goldfeld and Jacquet, Automorphic Representations and L-functions for GL(n), Section 2.4.
- Formalization note: Proves the upper-triangular factorization by integral column elimination and extracts the diagonal and upper unitriangular factors.
- PROVENANCE-END
-/

/-!
# Triangular decomposition over a valued field

Integral column elimination gives the factorization into diagonal,
upper unitriangular and invertible integral factors at every rank.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

/-- A row pivot of maximal valuation can be used to clear every other
column by an invertible matrix over the valuation ring. -/
theorem exists_valuationIntegerColumnElimination
    {F V I : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    [Fintype I] [DecidableEq I] (v : Valuation F V) (x : I -> F) (p : I)
    (hp : Not (x p = 0)) (hMax : forall j : I, v (x j) <= v (x p)) :
    Exists (fun k : Units (Matrix I I v.integer) => forall j : I,
      Matrix.vecMul x (v.integer.subtype.mapMatrix k.val) j =
        if j = p then x p else 0) := by
  let O := v.integer
  have hv : Not (v (x p) = 0) := (map_ne_zero v).mpr hp
  have hRat (j : I) : Membership.mem O (x j / x p) := by
    change v (x j / x p) <= 1
    rw [v.map_div]
    calc
      _ <= v (x p) / v (x p) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hMax j) zero_le
      _ = 1 := div_self hv
  let c (j : I) : O := if j = p then 0 else Subtype.mk (x j / x p) (hRat j)
  have hc0 : c p = 0 := if_pos rfl
  let E (i j : I) : O := if i = p then c j else 0
  let M : Matrix I I O := E
  have hNil : M * M = 0 := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a = p
    . subst a
      simp [M, E, hc0]
    . simp [M, E, ha]
  let k : Units (Matrix I I O) :=
    { val := 1 - M
      inv := 1 + M
      val_inv := by rw [sub_mul, one_mul, mul_add, mul_one, hNil, add_zero, add_sub_cancel_right]
      inv_val := by rw [mul_sub, mul_one, add_mul, one_mul, hNil, add_zero, add_sub_cancel_right] }
  let lift : RingHom (Matrix I I O) (Matrix I I F) := v.integer.subtype.mapMatrix
  have hK : lift k.val = 1 - lift M := by
    change lift (1 - M) = 1 - lift M
    rw [map_sub, map_one]
  have hRow (j : I) : Matrix.vecMul x (lift M) j = x p * (c j : F) := by
    change Finset.univ.sum (fun a : I => x a * (M a j : F)) = _
    calc
      _ = x p * (M p j : F) :=
        Finset.sum_eq_single p (fun a _ ha => by simp [M, E, ha])
          (fun hn => False.elim (hn (Finset.mem_univ p)))
      _ = _ := by simp [M, E]
  refine Exists.intro k (fun j => ?_)
  change Matrix.vecMul x (lift k.val) j = _
  rw [hK, Matrix.vecMul_sub, Matrix.vecMul_one]
  change x j - Matrix.vecMul x (lift M) j = _
  rw [hRow]
  by_cases hj : j = p
  . subst j
    simp [hc0]
  . rw [if_neg hj]
    have hc : (c j : F) = x j / x p := by simp [c, hj]
    rw [hc]
    have h : x j = (x j / x p) * x p :=
      (div_eq_iff hp).mp rfl
    exact sub_eq_zero.mpr (h.trans (mul_comm _ _))

/-- Integral column operations move a nonzero row to a row supported in
any prescribed column. The last-column case is used in the triangular
decomposition over a valuation ring. -/
theorem exists_valuationIntegerRowSupportedInColumn
    {F V I : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    [Fintype I] [DecidableEq I] (v : Valuation F V) (x : I -> F) (q : I)
    (hNonzero : Exists (fun j : I => Not (x j = 0))) :
    Exists (fun k : Units (Matrix I I v.integer) => Exists (fun a : F =>
      And (Not (a = 0)) (forall j : I,
        Matrix.vecMul x (v.integer.subtype.mapMatrix k.val) j =
          if j = q then a else 0))) := by
  choose j0 hj0 using hNonzero
  have hUniv : (Finset.univ : Finset I).Nonempty := Exists.intro j0 (Finset.mem_univ _)
  choose p hP using Finset.exists_max_image (Finset.univ : Finset I) (fun j => v (x j)) hUniv
  have hMax (j : I) : v (x j) <= v (x p) := hP.2 j (Finset.mem_univ _)
  have hp0 : Not (x p = 0) := by
    intro hz
    have h := hMax j0
    rw [hz, map_zero] at h
    exact ((map_ne_zero v).mpr hj0) (le_antisymm h zero_le)
  choose k hk using exists_valuationIntegerColumnElimination v x p hp0 hMax
  let O := v.integer
  let s := Equiv.swap p q
  let u : Units (Matrix I I O) :=
    { val := s.permMatrix O
      inv := (Inv.inv s).permMatrix O
      val_inv := by rw [<- Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
      inv_val := by rw [<- Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one] }
  let lift : RingHom (Matrix I I O) (Matrix I I F) := v.integer.subtype.mapMatrix
  have hLift : lift u.val = s.permMatrix F := by
    apply Matrix.ext
    intro i j
    change ((s.permMatrix O i j : O) : F) = s.permMatrix F i j
    by_cases h : s i = j
    . simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.toPEquiv_apply, h]
    . simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.toPEquiv_apply, h]
  have hs : s p = q := Equiv.swap_apply_left p q
  refine Exists.intro (k * u) (Exists.intro (x p) (And.intro hp0 ?_))
  intro j
  change Matrix.vecMul x (lift (k.val * u.val)) j = _
  rw [map_mul, hLift, <- Matrix.vecMul_vecMul, Matrix.vecMul_permMatrix]
  change Matrix.vecMul x (v.integer.subtype.mapMatrix k.val) (s.symm j) = _
  have hEq : s.symm j = p <-> j = q := (Equiv.symm_apply_eq s).trans (by rw [hs])
  rw [hk]
  simp only [hEq]

/-- If the last row of an invertible matrix is supported in its last
column with a nonzero entry, the upper-left corner is invertible. -/
theorem exists_unitUpperLeftCorner_of_lastRow
    {F : Type*} [Field F] (n : Nat)
    (g : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (hZero : forall j : Fin n, g.val (Fin.last n) j.castSucc = 0)
    (hPivot : Not (g.val (Fin.last n) (Fin.last n) = 0)) :
    Exists (fun B : Units (Matrix (Fin n) (Fin n) F) => forall i j : Fin n,
      B.val i j = g.val i.castSucc j.castSucc) := by
  have hInv (j : Fin n) : g.inv (Fin.last n) j.castSucc = 0 := by
    have h := congrArg
      (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) F => M (Fin.last n) j.castSucc) g.val_inv
    have hr : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j.castSucc = 0 :=
      Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm
    change (g.val * g.inv) (Fin.last n) j.castSucc = _ at h
    rw [hr, Matrix.mul_apply, Fin.sum_univ_castSucc] at h
    simp only [hZero, zero_mul, Finset.sum_const_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left hPivot
  let J (i j : Fin n) := g.val i.castSucc j.castSucc
  let K (i j : Fin n) := g.inv i.castSucc j.castSucc
  let B : Matrix (Fin n) (Fin n) F := J
  let C : Matrix (Fin n) (Fin n) F := K
  have hId (i j : Fin n) :
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i.castSucc j.castSucc =
        (1 : Matrix (Fin n) (Fin n) F) i j := by
    simp only [Matrix.one_apply, Fin.castSucc_inj]
  have hBC : B * C = 1 := by
    apply Matrix.ext
    intro i j
    have h := congrArg
      (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) F => M i.castSucc j.castSucc) g.val_inv
    change (g.val * g.inv) i.castSucc j.castSucc = _ at h
    rw [hId, Matrix.mul_apply, Fin.sum_univ_castSucc, hInv, mul_zero, add_zero] at h
    exact h
  have hCB : C * B = 1 := by
    apply Matrix.ext
    intro i j
    have h := congrArg
      (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) F => M i.castSucc j.castSucc) g.inv_val
    change (g.inv * g.val) i.castSucc j.castSucc = _ at h
    rw [hId, Matrix.mul_apply, Fin.sum_univ_castSucc, hZero, mul_zero, add_zero] at h
    exact h
  let U : Units (Matrix (Fin n) (Fin n) F) :=
    { val := B, inv := C, val_inv := hBC, inv_val := hCB }
  exact Exists.intro U (fun _ _ => rfl)

private def valuationBlockPad {R : Type*} [Zero R] [One R] {n : Nat}
    (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

private def valuationBlockPadHom {R : Type*} [Semiring R] (n : Nat) :
    MonoidHom (Matrix (Fin n) (Fin n) R) (Matrix (Fin (n + 1)) (Fin (n + 1)) R) where
  toFun := valuationBlockPad
  map_one' := by
    apply Matrix.ext
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    . refine Fin.lastCases ?_ (fun j => ?_) j
      . simp [valuationBlockPad]
      . simp [valuationBlockPad, Matrix.one_apply, (Fin.castSucc_ne_last j).symm]
    . refine Fin.lastCases ?_ (fun j => ?_) j
      . simp [valuationBlockPad, Matrix.one_apply, Fin.castSucc_ne_last i]
      . simp [valuationBlockPad, Matrix.one_apply]
  map_mul' A B := by
    apply Matrix.ext
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;>
      refine Fin.lastCases ?_ (fun j => ?_) j <;>
        simp [valuationBlockPad, Matrix.mul_apply, Fin.sum_univ_castSucc]

private theorem map_valuationBlockPad {R S : Type*} [Semiring R] [Semiring S]
    (f : RingHom R S) {n : Nat} (A : Matrix (Fin n) (Fin n) R) :
    f.mapMatrix (valuationBlockPad A) = valuationBlockPad (f.mapMatrix A) := by
  apply Matrix.ext
  intro i j
  change f (valuationBlockPad A i j) = valuationBlockPad (f.mapMatrix A) i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [valuationBlockPad]

/-- Every invertible matrix over the valued field becomes upper triangular
after right multiplication by an invertible integral matrix. This is the
algebraic triangular decomposition used in the local Iwasawa integral. -/
theorem exists_valuationIntegerRightUpperTriangular
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V] (v : Valuation F V)
    (n : Nat) (g : Units (Matrix (Fin n) (Fin n) F)) :
    Exists (fun k : Units (Matrix (Fin n) (Fin n) v.integer) => forall i j : Fin n,
      j < i -> (g.val * v.integer.subtype.mapMatrix k.val) i j = 0) := by
  induction n with
  | zero =>
    refine Exists.intro 1 (fun i => Fin.elim0 i)
  | succ n ih =>
    let x (j : Fin (n + 1)) := g.val (Fin.last n) j
    have hNZ : Exists (fun j : Fin (n + 1) => Not (x j = 0)) := by
      by_contra h
      have hz (j : Fin (n + 1)) : g.val (Fin.last n) j = 0 :=
        Classical.byContradiction (fun hj => h (Exists.intro j hj))
      have hv := congrArg
        (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) F => M (Fin.last n) (Fin.last n)) g.val_inv
      change (g.val * g.inv) (Fin.last n) (Fin.last n) = _ at hv
      simp only [Matrix.mul_apply, hz, zero_mul, Finset.sum_const_zero, Matrix.one_apply] at hv
      exact zero_ne_one hv
    choose k1 a hA using exists_valuationIntegerRowSupportedInColumn v x (Fin.last n) hNZ
    have ha : Not (a = 0) := hA.1
    have hRow := hA.2
    let lift : RingHom (Matrix (Fin (n + 1)) (Fin (n + 1)) v.integer)
        (Matrix (Fin (n + 1)) (Fin (n + 1)) F) := v.integer.subtype.mapMatrix
    let g1 := g * Units.map lift.toMonoidHom k1
    have hG1 (j : Fin (n + 1)) : g1.val (Fin.last n) j = if j = Fin.last n then a else 0 := by
      change Matrix.vecMul x (v.integer.subtype.mapMatrix k1.val) j = _
      exact hRow j
    have hZero (j : Fin n) : g1.val (Fin.last n) j.castSucc = 0 := by
      rw [hG1, if_neg (Fin.castSucc_ne_last j)]
    have hPivot : Not (g1.val (Fin.last n) (Fin.last n) = 0) := by
      rw [hG1, if_pos rfl]
      exact ha
    choose B hB using exists_unitUpperLeftCorner_of_lastRow n g1 hZero hPivot
    choose k0 hk0 using ih B
    let k2 := Units.map (valuationBlockPadHom (R := v.integer) n) k0
    have hK2 : lift k2.val = valuationBlockPad (v.integer.subtype.mapMatrix k0.val) :=
      map_valuationBlockPad v.integer.subtype k0.val
    have hg : g.val * lift (k1 * k2).val = g1.val * lift k2.val := by
      change g.val * lift (k1.val * k2.val) = (g.val * lift k1.val) * lift k2.val
      rw [map_mul, mul_assoc]
    refine Exists.intro (k1 * k2) ?_
    change forall i j : Fin (n + 1), j < i -> (g.val * lift (k1 * k2).val) i j = 0
    rw [hg, hK2]
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    . intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      . intro h
        exact False.elim (lt_irrefl _ h)
      . intro _
        rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
        simp [valuationBlockPad, hZero]
    . intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      . intro h
        exact False.elim (not_lt_of_ge (Fin.le_last _) h)
      . intro h
        have hj : j < i := h
        rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
        simp [valuationBlockPad]
        have hMap (u : Fin n) :
            v.integer.subtype.mapMatrix k0.val u j = ((k0.val u j : v.integer) : F) := rfl
        simpa only [Matrix.mul_apply, hB, hMap] using hk0 i j hj

/-- An invertible matrix factors as a diagonal matrix, an upper
unitriangular matrix and an invertible integral matrix. The order of
these factors gives the diagonal and unipotent coordinates in the
local zeta integral. -/
theorem exists_valuationIwasawaFactors
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V] (v : Valuation F V)
    (n : Nat) (g : Units (Matrix (Fin n) (Fin n) F)) :
    Exists (fun a : Fin n -> Units F =>
      Exists (fun u : Units (Matrix (Fin n) (Fin n) F) =>
        Exists (fun k : Units (Matrix (Fin n) (Fin n) v.integer) =>
          And u.val.IsUpperTriangular
            (And (forall i : Fin n, u.val i i = 1)
              (g.val = Matrix.diagonal (fun i => (a i).val) * u.val *
                v.integer.subtype.mapMatrix k.val))))) := by
  choose k hk using exists_valuationIntegerRightUpperTriangular v n g
  let L : RingHom (Matrix (Fin n) (Fin n) v.integer) (Matrix (Fin n) (Fin n) F) :=
    v.integer.subtype.mapMatrix
  let b := g * Units.map L.toMonoidHom k
  have hb : b.val.IsUpperTriangular := by
    intro i j hij
    exact hk i j hij
  have hDet : Not (b.val.det = 0) :=
    (b.isUnit.map (Matrix.detMonoidHom : MonoidHom (Matrix (Fin n) (Fin n) F) F)).ne_zero
  have hd (i : Fin n) : Not (b.val i i = 0) := by
    intro hi
    apply hDet
    rw [Matrix.det_of_isUpperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  let a (i : Fin n) := Units.mk0 (b.val i i) (hd i)
  let D : Units (Matrix (Fin n) (Fin n) F) :=
    { val := Matrix.diagonal (fun i => (a i).val)
      inv := Matrix.diagonal (fun i => (a i).inv)
      val_inv := by simp [Matrix.diagonal_mul_diagonal]
      inv_val := by simp [Matrix.diagonal_mul_diagonal] }
  let u := Inv.inv D * b
  have hEntry (i j : Fin n) : u.val i j = (a i).inv * b.val i j :=
    Matrix.diagonal_mul _ _ i j
  have hu : u.val.IsUpperTriangular := by
    intro i j hij
    rw [hEntry, hb hij, mul_zero]
  have huDiag (i : Fin n) : u.val i i = 1 := by
    rw [hEntry]
    exact (a i).inv_val
  refine Exists.intro a (Exists.intro u (Exists.intro (Inv.inv k)
    (And.intro hu (And.intro huDiag ?_))))
  change g.val = D.val * u.val * L k.inv
  have hD : D.val * u.val = b.val := by
    change D.val * (D.inv * b.val) = b.val
    rw [<- mul_assoc, D.val_inv, one_mul]
  have hK : L k.val * L k.inv = 1 := by
    rw [<- map_mul, k.val_inv, map_one]
  rw [hD]
  change g.val = (g.val * L k.val) * L k.inv
  rw [mul_assoc, hK, mul_one]

end Robin1984.GRH
