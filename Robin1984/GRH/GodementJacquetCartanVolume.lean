import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.OpenSubgroup
import Robin1984.GRH.GodementJacquetCartanIntegral

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Compact open subgroup double cosets, left Haar invariance, and the determinant criterion for invertible matrices.
- Formalization note: Computes the Haar volume of a Cartan double coset by a finite index and describes the stabilizer by entrywise valuation bounds.
- PROVENANCE-END
-/

/-!
# Haar volume of Cartan double cosets

The left translates of the integral subgroup inside a double coset are
indexed by the quotient by the conjugation stabilizer. Their disjoint
union gives the Haar volume. A diagonal conjugation preserves determinant
valuation, so membership in the stabilizer is an entrywise condition.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

open MeasureTheory

/-- The subgroup of the left integral factor that preserves the right
coset of the diagonal representative. -/
def cartanLeftCosetStabilizer {G : Type*} [Group G] (K : Subgroup G) (d : G) :
    Subgroup K :=
  K.comap ((MulAut.conj (Inv.inv d)).toMonoidHom.comp K.subtype)

private theorem cartanLeftCosetStabilizer_rel_iff
    {G : Type*} [Group G] (K : Subgroup G) (d : G) (l m : K) :
    QuotientGroup.leftRel (cartanLeftCosetStabilizer K d) l m <->
      Membership.mem K (Inv.inv (l.val * d) * (m.val * d)) := by
  rw [QuotientGroup.leftRel_apply]
  change Membership.mem K (MulAut.conj (Inv.inv d) (Inv.inv l.val * m.val)) <-> _
  simp only [MulAut.conj_apply, inv_inv, mul_inv_rev, mul_assoc]

private theorem cartanDoubleCoset_leftTranslate_partition
    {G : Type*} [Group G] (K : Subgroup G) (d : G) :
    let J := cartanLeftCosetStabilizer K d
    let Q := Quotient (QuotientGroup.leftRel J)
    let T (q : Q) :=
      Set.preimage (fun g : G => Inv.inv (q.out.val * d) * g) (K : Set G)
    And (Set.iUnion T = DoubleCoset.doubleCoset d (K : Set G) (K : Set G))
      (Pairwise (fun q q' : Q => Disjoint (T q) (T q'))) := by
  intro J Q T
  constructor
  . ext g
    rw [Set.mem_iUnion, DoubleCoset.mem_doubleCoset]
    constructor
    . intro hg
      choose q hq using hg
      let h : G := Inv.inv (q.out.val * d) * g
      have hMem : Membership.mem K h := hq
      refine Exists.intro q.out.val (And.intro q.out.property
        (Exists.intro h (And.intro hMem ?_)))
      change g = (q.out.val * d) * (Inv.inv (q.out.val * d) * g)
      simp [<- mul_assoc]
    . intro hg
      choose l hl r hr hEq using hg
      let m : K := Subtype.mk l hl
      let q : Q := Quotient.mk (QuotientGroup.leftRel J) m
      have hRel : QuotientGroup.leftRel J q.out m :=
        Quotient.exact (Quotient.out_eq q)
      have hLink := (cartanLeftCosetStabilizer_rel_iff K d q.out m).mp hRel
      refine Exists.intro q ?_
      change Membership.mem K (Inv.inv (q.out.val * d) * g)
      have hEq' : g = m.val * d * r := hEq
      rw [hEq', <- mul_assoc]
      exact K.mul_mem hLink hr
  . intro q q' hne
    apply Set.disjoint_left.mpr
    intro g hg hg'
    change Membership.mem K (Inv.inv (q.out.val * d) * g) at hg
    change Membership.mem K (Inv.inv (q'.out.val * d) * g) at hg'
    have hMul := K.mul_mem hg (K.inv_mem hg')
    have hLink : Membership.mem K (Inv.inv (q.out.val * d) * (q'.out.val * d)) := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using hMul
    have hRel := (cartanLeftCosetStabilizer_rel_iff K d q.out q'.out).mpr hLink
    have hEq := Quotient.sound hRel
    exact hne ((Quotient.out_eq q).symm.trans (hEq.trans (Quotient.out_eq q')))

private theorem isOpen_cartanLeftCosetStabilizer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (d : G) (hK : IsOpen (K : Set G)) :
    IsOpen (cartanLeftCosetStabilizer K d : Set K) := by
  change IsOpen (Set.preimage (fun k : K => MulAut.conj (Inv.inv d) k.val) (K : Set G))
  simp only [MulAut.conj_apply, inv_inv]
  exact hK.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

/-- The left Haar measure of a compact open subgroup's double coset is
its subgroup measure times the index of the left translate stabilizer. -/
theorem measure_cartanDoubleCoset_of_isCompact_isOpen
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (K : Subgroup G) (hCompact : IsCompact (K : Set G)) (hOpen : IsOpen (K : Set G))
    (d : G) :
    mu (DoubleCoset.doubleCoset d (K : Set G) (K : Set G)) =
      (Nat.card (Quotient (QuotientGroup.leftRel (cartanLeftCosetStabilizer K d))) : ENNReal) *
        mu (K : Set G) := by
  classical
  let J := cartanLeftCosetStabilizer K d
  let Q := Quotient (QuotientGroup.leftRel J)
  let T (q : Q) := Set.preimage (fun g : G => Inv.inv (q.out.val * d) * g) (K : Set G)
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hCompact
  let _ : Finite Q := J.quotient_finite_of_isOpen (isOpen_cartanLeftCosetStabilizer K d hOpen)
  let _ : Fintype Q := Fintype.ofFinite Q
  change mu (DoubleCoset.doubleCoset d (K : Set G) (K : Set G)) =
    (Nat.card Q : ENNReal) * mu (K : Set G)
  have hSplit := cartanDoubleCoset_leftTranslate_partition K d
  change And (Set.iUnion T = _) (Pairwise (fun q q' : Q => Disjoint (T q) (T q'))) at hSplit
  have hMeas (q : Q) : MeasurableSet (T q) :=
    (hOpen.preimage (continuous_const.mul continuous_id)).measurableSet
  have hMass (q : Q) : mu (T q) = mu (K : Set G) := by
    apply ((forall_measure_preimage_mul_iff mu).mpr inferInstance)
    exact hOpen.measurableSet
  rw [<- hSplit.1, measure_iUnion hSplit.2 hMeas]
  simp only [hMass, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, nsmul_eq_mul]

/-- A Cartan stratum has Haar volume given by its integral subgroup
conjugation index. -/
theorem measure_valuationIntegralDiagonalDoubleCoset
    {F W : Type*} [Field F] [TopologicalSpace F] [T2Space F] [IsTopologicalRing F]
    [LinearOrderedCommGroupWithZero W] (v : Valuation F W) (n : Nat)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) F))]
    [OpensMeasurableSpace (Units (Matrix (Fin n) (Fin n) F))]
    [MeasurableMul (Units (Matrix (Fin n) (Fin n) F))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) F))) [mu.IsMulLeftInvariant]
    (a : Units (Fin n -> F)) (hCompact : IsCompact (v.integer : Set F))
    (hOpen : IsOpen (v.integer : Set F)) :
    let K := valuationIntegralMatrixSubgroup v n
    let d := (valuationDiagonalSection F n a).val
    mu (valuationIntegralDiagonalDoubleCoset v n a) =
      (Nat.card (Quotient (QuotientGroup.leftRel (cartanLeftCosetStabilizer K d))) : ENNReal) *
        mu (K : Set (Units (Matrix (Fin n) (Fin n) F))) := by
  intro K d
  have hSet : valuationIntegralDiagonalDoubleCoset v n a =
      DoubleCoset.doubleCoset d (K : Set (Units (Matrix (Fin n) (Fin n) F)))
        (K : Set (Units (Matrix (Fin n) (Fin n) F))) := by
    ext g
    rw [DoubleCoset.mem_doubleCoset]
    change (exists l r : K, g = l.val * d * r.val) <-> _
    constructor
    . intro hg
      choose l r h using hg
      exact Exists.intro l.val (And.intro l.property (Exists.intro r.val (And.intro r.property h)))
    . intro hg
      choose l hl r hr h using hg
      exact Exists.intro (Subtype.mk l hl) (Exists.intro (Subtype.mk r hr) h)
  rw [hSet]
  exact measure_cartanDoubleCoset_of_isCompact_isOpen mu K
    (isCompact_valuationIntegralMatrixSubgroup v n hCompact)
    (isOpen_valuationIntegralMatrixSubgroup v n hOpen) d

private theorem mem_valuationIntegralMatrixSubgroup_of_valuation_det_one
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (g : Units (Matrix (Fin n) (Fin n) F))
    (hEntries : forall i j, v (g.val i j) <= 1) (hDet : v g.val.det = 1) :
    Membership.mem (valuationIntegralMatrixSubgroup v n) g := by
  let O := v.integer
  let A : Matrix (Fin n) (Fin n) O :=
    Matrix.of (fun i j => Subtype.mk (g.val i j) (hEntries i j))
  let f : RingHom (Matrix (Fin n) (Fin n) O) (Matrix (Fin n) (Fin n) F) :=
    O.subtype.mapMatrix
  have hMap : f A = g.val := by ext i j; rfl
  have hDetMap : (A.det : F) = g.val.det := by
    change O.subtype A.det = g.val.det
    rw [RingHom.map_det O.subtype A, show O.subtype.mapMatrix A = g.val from hMap]
  have hDetInv : v g.inv.det = 1 := by
    have h := congrArg (fun X : Matrix (Fin n) (Fin n) F => v X.det) g.val_inv
    simpa only [Matrix.det_mul, Matrix.det_one, v.map_mul, v.map_one, hDet, one_mul] using h
  let u : Units O :=
    { val := A.det
      inv := Subtype.mk g.inv.det hDetInv.le
      val_inv := by
        apply Subtype.ext
        change (A.det : F) * g.inv.det = 1
        rw [hDetMap, <- Matrix.det_mul, g.val_inv, Matrix.det_one]
      inv_val := by
        apply Subtype.ext
        change g.inv.det * (A.det : F) = 1
        rw [hDetMap, <- Matrix.det_mul, g.inv_val, Matrix.det_one] }
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr u.isUnit
  choose P hP using hA
  change Membership.mem (Units.map f.toMonoidHom).range g
  apply MonoidHom.mem_range.mpr
  refine Exists.intro P (Units.ext ?_)
  change f P.val = g.val
  rw [hP, hMap]

/-- The left translate stabilizer is cut out by the entry bounds for the
diagonal conjugate. The determinant of the conjugate already has
valuation one, so its inverse imposes no further bounds. -/
theorem mem_cartanLeftCosetStabilizer_iff_valuation_entries
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (a : Units (Fin n -> F))
    (g : valuationIntegralMatrixSubgroup v n) :
    Membership.mem (cartanLeftCosetStabilizer (valuationIntegralMatrixSubgroup v n)
      (valuationDiagonalSection F n a).val) g <->
    forall i j, v (a.inv i) * v (g.val.val i j) * v (a.val j) <= 1 := by
  let K := valuationIntegralMatrixSubgroup v n
  let d := (valuationDiagonalSection F n a).val
  let G := Units (Matrix (Fin n) (Fin n) F)
  let k : G := Inv.inv d * g.val * d
  change Membership.mem K (MulAut.conj (Inv.inv d) g.val) <-> _
  simp only [MulAut.conj_apply, inv_inv]
  change Membership.mem K k <-> _
  have hEntry (i j : Fin n) : k.val i j = a.inv i * g.val.val i j * a.val j := by
    change (Matrix.diagonal a.inv * g.val.val * Matrix.diagonal a.val) i j = _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hDet : v k.val.det = 1 := by
    have hD : d.inv.det * d.val.det = 1 := by
      rw [<- Matrix.det_mul, d.inv_val, Matrix.det_one]
    have hK : k.val.det = g.val.val.det := by
      change (d.inv * g.val.val * d.val).det = _
      rw [Matrix.det_mul, Matrix.det_mul]
      calc
        _ = (d.inv.det * d.val.det) * g.val.val.det := by ac_rfl
        _ = _ := by rw [hD, one_mul]
    rw [hK]
    exact valuation_det_integralMatrixUnit v n g.val g.property
  constructor
  . intro hk i j
    have h := ((mem_valuationIntegralMatrixSubgroup_iff v n k).mp hk).1 i j
    change v (k.val i j) <= 1 at h
    rw [hEntry, v.map_mul, v.map_mul] at h
    exact h
  . intro h
    apply mem_valuationIntegralMatrixSubgroup_of_valuation_det_one v n k _ hDet
    intro i j
    rw [hEntry, v.map_mul, v.map_mul]
    exact h i j

end Robin1984.GRH
