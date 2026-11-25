import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.OpenSubgroup
import Robin1984.GRH.GodementJacquetCartanIntegral

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Compact open subgroup double cosets, left Haar invariance, and the determinant criterion for invertible matrices.
- Formalization note: Computes Cartan double-coset volume from the Haar mass of the stabilizer and gives explicit uniformizer-power bounds for its matrix entries.
- PROVENANCE-END
-/

/-!
# Haar volume of Cartan double cosets

The left translates inside a double coset are indexed by the quotient
by the conjugation stabilizer. The double-coset mass times the stabilizer
mass is the square of the integral subgroup's mass. A diagonal conjugation
preserves determinant valuation. For an ordered uniformizer diagonal,
only strictly upper-triangular entries have additional bounds.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

open MeasureTheory

/-- The subgroup of the left factor preserving the right coset of a
double-coset representative. -/
def doubleCosetLeftStabilizer {G : Type*} [Group G]
    (K U : Subgroup G) (d : G) : Subgroup K :=
  U.comap ((MulAut.conj (Inv.inv d)).toMonoidHom.comp K.subtype)

/-- The subgroup of the left integral factor that preserves the right
coset of the diagonal representative. -/
def cartanLeftCosetStabilizer {G : Type*} [Group G] (K : Subgroup G) (d : G) :
    Subgroup K :=
  doubleCosetLeftStabilizer K K d

private theorem doubleCosetLeftStabilizer_rel_iff
    {G : Type*} [Group G] (K U : Subgroup G) (d : G) (l m : K) :
    QuotientGroup.leftRel (doubleCosetLeftStabilizer K U d) l m <->
      Membership.mem U (Inv.inv (l.val * d) * (m.val * d)) := by
  rw [QuotientGroup.leftRel_apply]
  change Membership.mem U (MulAut.conj (Inv.inv d) (Inv.inv l.val * m.val)) <-> _
  simp only [MulAut.conj_apply, inv_inv, mul_inv_rev, mul_assoc]

private theorem doubleCoset_leftTranslate_partition
    {G : Type*} [Group G] (K U : Subgroup G) (d : G) :
    let J := doubleCosetLeftStabilizer K U d
    let Q := Quotient (QuotientGroup.leftRel J)
    let T (q : Q) :=
      Set.preimage (fun g : G => Inv.inv (q.out.val * d) * g) (U : Set G)
    And (Set.iUnion T = DoubleCoset.doubleCoset d (K : Set G) (U : Set G))
      (Pairwise (fun q q' : Q => Disjoint (T q) (T q'))) := by
  intro J Q T
  constructor
  . ext g
    rw [Set.mem_iUnion, DoubleCoset.mem_doubleCoset]
    constructor
    . intro hg
      choose q hq using hg
      let h : G := Inv.inv (q.out.val * d) * g
      have hMem : Membership.mem U h := hq
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
      have hLink := (doubleCosetLeftStabilizer_rel_iff K U d q.out m).mp hRel
      refine Exists.intro q ?_
      change Membership.mem U (Inv.inv (q.out.val * d) * g)
      have hEq' : g = m.val * d * r := hEq
      rw [hEq', <- mul_assoc]
      exact U.mul_mem hLink hr
  . intro q q' hne
    apply Set.disjoint_left.mpr
    intro g hg hg'
    change Membership.mem U (Inv.inv (q.out.val * d) * g) at hg
    change Membership.mem U (Inv.inv (q'.out.val * d) * g) at hg'
    have hMul := U.mul_mem hg (U.inv_mem hg')
    have hLink : Membership.mem U (Inv.inv (q.out.val * d) * (q'.out.val * d)) := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using hMul
    have hRel := (doubleCosetLeftStabilizer_rel_iff K U d q.out q'.out).mpr hLink
    have hEq := Quotient.sound hRel
    exact hne ((Quotient.out_eq q).symm.trans (hEq.trans (Quotient.out_eq q')))

private theorem isOpen_doubleCosetLeftStabilizer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K U : Subgroup G) (d : G) (hU : IsOpen (U : Set G)) :
    IsOpen (doubleCosetLeftStabilizer K U d : Set K) := by
  change IsOpen (Set.preimage (fun k : K => MulAut.conj (Inv.inv d) k.val) (U : Set G))
  simp only [MulAut.conj_apply, inv_inv]
  exact hU.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

/-- The measure of a double coset with compact left factor and open right
factor equals the right subgroup measure times the left stabilizer index. -/
theorem measure_doubleCoset_of_left_isCompact_right_isOpen
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (K U : Subgroup G) (hCompact : IsCompact (K : Set G)) (hOpen : IsOpen (U : Set G))
    (d : G) :
    mu (DoubleCoset.doubleCoset d (K : Set G) (U : Set G)) =
      (Nat.card (Quotient (QuotientGroup.leftRel (doubleCosetLeftStabilizer K U d))) : ENNReal) *
        mu (U : Set G) := by
  classical
  let J := doubleCosetLeftStabilizer K U d
  let Q := Quotient (QuotientGroup.leftRel J)
  let T (q : Q) := Set.preimage (fun g : G => Inv.inv (q.out.val * d) * g) (U : Set G)
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hCompact
  let _ : Finite Q := J.quotient_finite_of_isOpen (isOpen_doubleCosetLeftStabilizer K U d hOpen)
  let _ : Fintype Q := Fintype.ofFinite Q
  change mu (DoubleCoset.doubleCoset d (K : Set G) (U : Set G)) =
    (Nat.card Q : ENNReal) * mu (U : Set G)
  have hSplit := doubleCoset_leftTranslate_partition K U d
  change And (Set.iUnion T = _) (Pairwise (fun q q' : Q => Disjoint (T q) (T q'))) at hSplit
  have hMeas (q : Q) : MeasurableSet (T q) :=
    (hOpen.preimage (continuous_const.mul continuous_id)).measurableSet
  have hMass (q : Q) : mu (T q) = mu (U : Set G) := by
    apply ((forall_measure_preimage_mul_iff mu).mpr inferInstance)
    exact hOpen.measurableSet
  rw [<- hSplit.1, measure_iUnion hSplit.2 hMeas]
  simp only [hMass, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, nsmul_eq_mul]

/-- Integrate over a double coset by summing the integrals on its disjoint
left translates of the right subgroup. -/
theorem hasSum_integral_doubleCoset_leftTranslate
    {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (C U : Subgroup G) (hCompact : IsCompact (C : Set G)) (hOpen : IsOpen (U : Set G))
    (d : G) (f : G -> E) :
    let D := DoubleCoset.doubleCoset d (C : Set G) (U : Set G)
    let J := doubleCosetLeftStabilizer C U d
    let Q := Quotient (QuotientGroup.leftRel J)
    IntegrableOn f D mu ->
    HasSum (fun q : Q => integral (mu.restrict (U : Set G)) (fun x => f (q.out.val * d * x)))
      (integral (mu.restrict D) f) := by
  intro D J Q hInt
  let T (q : Q) := Set.preimage (fun g : G => Inv.inv (q.out.val * d) * g) (U : Set G)
  let _ : CompactSpace C := isCompact_iff_compactSpace.mp hCompact
  let _ : Finite Q := J.quotient_finite_of_isOpen (isOpen_doubleCosetLeftStabilizer C U d hOpen)
  have hSplit := doubleCoset_leftTranslate_partition C U d
  change And (Set.iUnion T = D) (Pairwise (fun q q' : Q => Disjoint (T q) (T q'))) at hSplit
  have hMeas (q : Q) : MeasurableSet (T q) :=
    (hOpen.preimage (continuous_const.mul continuous_id)).measurableSet
  have hIntUnion : IntegrableOn f (Set.iUnion T) mu := by rw [hSplit.1]; exact hInt
  have hSum := hasSum_integral_iUnion hMeas hSplit.2 hIntUnion
  rw [hSplit.1] at hSum
  have hTerm (q : Q) : integral (mu.restrict (T q)) f =
      integral (mu.restrict (U : Set G)) (fun x => f (q.out.val * d * x)) := by
    let g := q.out.val * d
    let e := MeasurableEquiv.mulLeft g
    have hPre : Set.preimage e (T q) = (U : Set G) := by
      ext x
      change Membership.mem U (Inv.inv g * (g * x)) <-> Membership.mem U x
      simp
    have h := (measurePreserving_mul_left mu g).restrict_preimage_emb e.measurableEmbedding (T q)
    change MeasurePreserving e (mu.restrict (Set.preimage e (T q))) (mu.restrict (T q)) at h
    rw [hPre] at h
    exact (h.integral_comp e.measurableEmbedding f).symm
  simpa only [hTerm] using hSum

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
  exact measure_doubleCoset_of_left_isCompact_right_isOpen mu K K hCompact hOpen d

/-- A compact subgroup has measure equal to the mass of an open
subgroup times its index. The open subgroup is viewed in the ambient group. -/
theorem measure_subgroup_eq_index_mul_subgroupMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (K : Subgroup G) (H : Subgroup K) (hCompact : IsCompact (K : Set G))
    (hOpen : IsOpen (H.map K.subtype : Set G)) :
    mu (K : Set G) =
      (Nat.card (Quotient (QuotientGroup.leftRel H)) : ENNReal) *
        mu (H.map K.subtype : Set G) := by
  let U := H.map K.subtype
  have hLie : U <= K := by
    intro x hx
    choose h hh using (Subgroup.mem_map.mp hx)
    have hx' : h.val = x := hh.2
    rw [<- hx']
    exact h.property
  have hCoset : DoubleCoset.doubleCoset (1 : G) (K : Set G) (U : Set G) = (K : Set G) := by
    ext x
    rw [DoubleCoset.mem_doubleCoset]
    constructor
    . intro hx
      choose k hk u hu he using hx
      rw [he, mul_one]
      exact K.mul_mem hk (hLie hu)
    . intro hx
      exact Exists.intro x (And.intro hx (Exists.intro 1 (And.intro U.one_mem (by simp))))
  have hStab : doubleCosetLeftStabilizer K U (1 : G) = H := by
    ext k
    change Membership.mem U (MulAut.conj (Inv.inv (1 : G)) k.val) <-> _
    simp only [inv_one, MulAut.conj_apply, one_mul, mul_one]
    change Membership.mem (H.map K.subtype) k.val <-> Membership.mem H k
    rw [Subgroup.mem_map]
    constructor
    . intro hk
      choose a ha using hk
      have hEq : a = k := Subtype.ext ha.2
      simpa only [hEq] using ha.1
    . intro hk
      exact Exists.intro k (And.intro hk rfl)
  have h := measure_doubleCoset_of_left_isCompact_right_isOpen mu K U hCompact hOpen 1
  rw [hCoset, hStab] at h
  exact h

private theorem isOpen_map_cartanLeftCosetStabilizer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hOpen : IsOpen (K : Set G)) (d : G) :
    IsOpen ((cartanLeftCosetStabilizer K d).map K.subtype : Set G) := by
  let H := cartanLeftCosetStabilizer K d
  have hEq : (H.map K.subtype : Set G) =
      Set.inter (K : Set G) (Set.preimage (fun g : G => MulAut.conj (Inv.inv d) g) (K : Set G)) := by
    ext g
    change Membership.mem (H.map K.subtype) g <->
      And (Membership.mem K g) (Membership.mem K (MulAut.conj (Inv.inv d) g))
    rw [Subgroup.mem_map]
    constructor
    . intro hg
      choose k hk using hg
      have he : k.val = g := hk.2
      rw [<- he]
      exact And.intro k.property hk.1
    . intro hg
      exact Exists.intro (Subtype.mk g hg.1) (And.intro hg.2 rfl)
  change IsOpen (H.map K.subtype : Set G)
  rw [hEq]
  apply hOpen.inter
  apply hOpen.preimage
  simp only [MulAut.conj_apply]
  exact (continuous_const.mul continuous_id).mul continuous_const

/-- Multiplying the Cartan double-coset mass by the stabilizer mass gives
the square of the compact open subgroup's mass. -/
theorem measure_cartanDoubleCoset_mul_stabilizerMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (K : Subgroup G) (hCompact : IsCompact (K : Set G)) (hOpen : IsOpen (K : Set G))
    (d : G) :
    mu (DoubleCoset.doubleCoset d (K : Set G) (K : Set G)) *
        mu ((cartanLeftCosetStabilizer K d).map K.subtype : Set G) =
      mu (K : Set G) ^ 2 := by
  let H := cartanLeftCosetStabilizer K d
  have hIdx := measure_subgroup_eq_index_mul_subgroupMeasure mu K H hCompact
    (isOpen_map_cartanLeftCosetStabilizer K hOpen d)
  rw [measure_cartanDoubleCoset_of_isCompact_isOpen mu K hCompact hOpen d, pow_two]
  change ((Nat.card (Quotient (QuotientGroup.leftRel H)) : ENNReal) * mu (K : Set G)) *
      mu (H.map K.subtype : Set G) = _
  calc
    _ = mu (K : Set G) * ((Nat.card (Quotient (QuotientGroup.leftRel H)) : ENNReal) *
        mu (H.map K.subtype : Set G)) := by ac_rfl
    _ = _ := by rw [<- hIdx]

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

private theorem valuation_diagonalCoordinate_mul_inv
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (a : Units (Fin n -> F)) (i : Fin n) :
    v (a.val i) * v (a.inv i) = 1 := by
  have h : a.val i * a.inv i = 1 := congrFun a.val_inv i
  rw [<- v.map_mul, h, v.map_one]

private theorem mem_cartanLeftCosetStabilizer_iff_upper_valuation_entries
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (a : Units (Fin n -> F))
    (ha : Monotone (fun i => v (a.val i)))
    (g : valuationIntegralMatrixSubgroup v n) :
    Membership.mem (cartanLeftCosetStabilizer (valuationIntegralMatrixSubgroup v n)
      (valuationDiagonalSection F n a).val) g <->
    forall i j, i < j -> v (g.val.val i j) * v (a.val j) <= v (a.val i) := by
  rw [mem_cartanLeftCosetStabilizer_iff_valuation_entries v n a g]
  have hProd := valuation_diagonalCoordinate_mul_inv v n a
  have hScale (i j : Fin n) :
      v (a.inv i) * v (g.val.val i j) * v (a.val j) <= 1 <->
      v (g.val.val i j) * v (a.val j) <= v (a.val i) := by
    constructor
    . intro h
      have hL := mul_le_mul' (le_refl (v (a.val i))) h
      have hEq : v (a.val i) * (v (a.inv i) * v (g.val.val i j) * v (a.val j)) =
          v (g.val.val i j) * v (a.val j) := by
        calc
          _ = (v (a.val i) * v (a.inv i)) * (v (g.val.val i j) * v (a.val j)) := by ac_rfl
          _ = _ := by rw [hProd, one_mul]
      simpa only [hEq, mul_one] using hL
    . intro h
      have hR := mul_le_mul' (le_refl (v (a.inv i))) h
      have hInv : v (a.inv i) * v (a.val i) = 1 := (mul_comm _ _).trans (hProd i)
      simpa only [<- mul_assoc, hInv] using hR
  constructor
  . intro h i j _
    exact (hScale i j).mp (h i j)
  . intro h i j
    apply (hScale i j).mpr
    by_cases hij : i < j
    . exact h i j hij
    . have hv := ((mem_valuationIntegralMatrixSubgroup_iff v n g.val).mp g.property).1 i j
      calc
        _ <= 1 * v (a.val j) := mul_le_mul' hv (le_refl _)
        _ = v (a.val j) := one_mul _
        _ <= _ := ha (le_of_not_gt hij)

/-- Membership in the ambient integral stabilizer is determined by
unit determinant, integral entries, and one uniformizer-power bound for
each strictly upper-triangular entry. -/
theorem mem_map_cartanLeftCosetStabilizer_uniformizerGapDiagonal_iff
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (pi : Units F) (hPi : v pi.val <= 1)
    (gaps : Fin n -> Nat) (g : Units (Matrix (Fin n) (Fin n) F)) :
    let a := valuationUniformizerGapDiagonal n pi gaps
    let K := valuationIntegralMatrixSubgroup v n
    let d := (valuationDiagonalSection F n a).val
    let e := orderedValuationConeExponents n gaps
    Membership.mem ((cartanLeftCosetStabilizer K d).map K.subtype) g <->
      And (v g.val.det = 1)
        (And (forall i j, v (g.val i j) <= 1)
          (forall i j, i < j -> v (g.val i j) <= v pi.val ^ (e i - e j))) := by
  intro a K d e
  let dirs := valuationUniformizerConeDirections v n pi hPi
  let b : valuationOrderedDiagonalSubmonoid v n := Finset.univ.prod (fun i => dirs i ^ gaps i)
  have hb : b.val = a := by
    exact map_prod (valuationOrderedDiagonalSubmonoid v n).subtype (fun i => dirs i ^ gaps i) _
  have hMono : Monotone (fun i => v (a.val i)) := by
    rw [<- hb]
    exact b.property
  have hE (i : Fin n) : v (a.val i) = v pi.val ^ e i := by
    change v ((valuationUniformizerGapDiagonal n pi gaps).val i) = _
    rw [valuationUniformizerGapDiagonal, valuationConePrefixUniformizer_prod_apply, map_pow]
  have hPow (i j : Fin n) (hij : i < j) :
      v (a.val i) = v pi.val ^ (e i - e j) * v (a.val j) := by
    rw [hE i, hE j, <- pow_add, Nat.sub_add_cancel
      (antitone_orderedValuationConeExponents n gaps hij.le)]
  have hUpper (k : K) :
      Membership.mem (cartanLeftCosetStabilizer K d) k <->
        forall i j, i < j -> v (k.val.val i j) <= v pi.val ^ (e i - e j) := by
    rw [mem_cartanLeftCosetStabilizer_iff_upper_valuation_entries v n a hMono]
    constructor
    . intro h i j hij
      have h' := h i j hij
      rw [hPow i j hij] at h'
      have hM := mul_le_mul' h' (le_refl (v (a.inv j)))
      simpa only [mul_assoc, valuation_diagonalCoordinate_mul_inv v n a j, mul_one] using hM
    . intro h i j hij
      rw [hPow i j hij]
      exact mul_le_mul' (h i j hij) (le_refl _)
  rw [Subgroup.mem_map]
  constructor
  . intro hg
    choose k hk using hg
    have hEq : k.val = g := hk.2
    rw [<- hEq]
    exact And.intro (valuation_det_integralMatrixUnit v n k.val k.property)
      (And.intro ((mem_valuationIntegralMatrixSubgroup_iff v n k.val).mp k.property).1
        ((hUpper k).mp hk.1))
  . intro hg
    let k : K := Subtype.mk g
      (mem_valuationIntegralMatrixSubgroup_of_valuation_det_one v n g hg.2.1 hg.1)
    exact Exists.intro k (And.intro ((hUpper k).mpr hg.2.2) rfl)

end Robin1984.GRH
