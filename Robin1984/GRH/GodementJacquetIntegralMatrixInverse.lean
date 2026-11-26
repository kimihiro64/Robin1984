import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.Group.Units

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The adjugate identity and the norm of multiplication by an integral element.
- Formalization note: Clears all matrix inverses with bounded nonzero determinant norm using a single factorial denominator and proves compactness from separate bounds on matrices and inverses.
- PROVENANCE-END
-/

/-! # Integral matrix inverses with one scalar denominator -/

set_option autoImplicit false

namespace Robin1984.GRH

variable {R S I : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype I] [DecidableEq I]

/-- The norm of multiplication by x belongs to the principal ideal (x).
The adjugate of multiplication, applied to the coordinate vector of one,
gives the integral quotient. -/
theorem dvd_algebraMap_norm_of_basis (b : Module.Basis I R S) (x : S) :
    Dvd.dvd x (algebraMap R S (Algebra.norm R x)) := by
  let A := Algebra.leftMulMatrix b x
  let u := b.equivFun 1
  let y := b.equivFun.symm (A.adjugate.mulVec u)
  have hMul (z : S) : A.mulVec (b.equivFun z) = b.equivFun (x * z) :=
    LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft R x) z
  refine Exists.intro y ?_
  apply b.equivFun.injective
  calc
    b.equivFun (algebraMap R S (Algebra.norm R x)) = HSMul.hSMul A.det u := by
      rw [Algebra.norm_eq_matrix_det b, Algebra.algebraMap_eq_smul_one, map_smul]
    _ = (A * A.adjugate).mulVec u := by
      rw [Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = A.mulVec (A.adjugate.mulVec u) := by rw [Matrix.mulVec_mulVec]
    _ = b.equivFun (x * y) := by
      rw [<- hMul y]
      change _ = A.mulVec (b.equivFun (b.equivFun.symm _))
      rw [LinearEquiv.apply_symm_apply]

/-- If a ground-ring scalar is divisible by the norm of a matrix determinant,
one integral matrix clears that scalar denominator in a right inverse. -/
theorem exists_integralMatrix_mul_eq_scalar_of_norm_det_dvd
    {J : Type*} [Fintype J] [DecidableEq J]
    (b : Module.Basis I R S) (A : Matrix J J S) (c : R)
    (hc : Dvd.dvd (Algebra.norm R A.det) c) :
    exists B : Matrix J J S, A * B = HSMul.hSMul (algebraMap R S c) (1 : Matrix J J S) := by
  have hNorm := dvd_algebraMap_norm_of_basis b A.det
  choose z hz using hNorm
  choose r hr using hc
  let t := z * algebraMap R S r
  have ht : algebraMap R S c = A.det * t := by
    rw [hr, map_mul, hz, mul_assoc]
  refine Exists.intro (HSMul.hSMul t A.adjugate) ?_
  rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm t, <- ht]


/-- A determinant with nonzero integral norm of absolute value at most M
has an integral right inverse after multiplying it by M factorial. -/
theorem exists_integralMatrix_mul_eq_factorial_of_norm_det_le
    {T J : Type*} [CommRing T] [IsDomain T] [Fintype J] [DecidableEq J]
    (b : Module.Basis I Int T) (A : Matrix J J T) (M : Nat)
    (hDet : Not (A.det = 0)) (hNorm : (Algebra.norm Int A.det).natAbs <= M) :
    exists B : Matrix J J T,
      A * B = HSMul.hSMul (algebraMap Int T (Int.ofNat M.factorial)) (1 : Matrix J J T) := by
  have hN : Not (Algebra.norm Int A.det = 0) :=
    (Algebra.norm_ne_zero_iff_of_basis b).mpr hDet
  apply exists_integralMatrix_mul_eq_scalar_of_norm_det_dvd b A
  rw [<- Int.natAbs_dvd]
  exact Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial (Int.natAbs_pos.mpr hN) hNorm)

section CompactUnitMatrixBox

variable {T : Type*} [Monoid T] [TopologicalSpace T] [T1Space T] [ContinuousMul T]

/-- Separate compact bounds on a matrix and its inverse give a compact
set in the topology of the units. -/
theorem isCompact_units_of_compact_val_and_inv (C D : Set T)
    (hC : IsCompact C) (hD : IsCompact D) :
    IsCompact {u : Units T | And (C.Mem u.val) (D.Mem u.inv)} := by
  let E : Units T -> Prod T (MulOpposite T) := Units.embedProduct T
  let op : Homeomorph T (MulOpposite T) := MulOpposite.opHomeomorph
  have hCompact : IsCompact (Set.prod C (Set.image op D)) :=
    hC.prod (hD.image op.continuous)
  have hEmb : Topology.IsEmbedding E := Units.isEmbedding_embedProduct
  have hRange : Set.range E = {p : Prod T (MulOpposite T) |
      And (p.1 * MulOpposite.unop p.2 = 1) (MulOpposite.unop p.2 * p.1 = 1)} := by
    ext p
    constructor
    . intro h
      choose u hu using h
      rw [<- hu]
      exact And.intro u.val_inv u.inv_val
    . intro h
      let u : Units T :=
        { val := p.1, inv := MulOpposite.unop p.2, val_inv := h.1, inv_val := h.2 }
      exact Exists.intro u (Prod.ext rfl (MulOpposite.op_unop _))
  have hClosed : IsClosed (Set.range E) := by
    rw [hRange]
    have hUnop : Continuous (fun p : Prod T (MulOpposite T) => MulOpposite.unop p.2) :=
      op.symm.continuous.comp continuous_snd
    have hOne : IsClosed (Set.singleton (1 : T)) := isClosed_singleton
    exact (hOne.preimage (continuous_fst.mul hUnop)).inter
      (hOne.preimage (hUnop.mul continuous_fst))
  have hPre : IsCompact (Set.preimage E (Set.prod C (Set.image op D))) :=
    hEmb.isInducing.isCompact_preimage hClosed hCompact
  convert hPre using 1
  ext u
  change And (C.Mem u.val) (D.Mem u.inv) <-> And (C.Mem u.val) ((Set.image op D).Mem (op u.inv))
  constructor
  . intro h
    exact And.intro h.1 (Exists.intro u.inv (And.intro h.2 rfl))
  . intro h
    choose y hy using h.2
    have he : y = u.inv := op.injective hy.2
    exact And.intro h.1 (by rw [<- he]; exact hy.1)

end CompactUnitMatrixBox

end Robin1984.GRH
