import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Instances.Matrix
import Robin1984.GRH.LocalIwasawaMeasure
import Robin1984.GRH.ValuationIwasawa

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Local Iwasawa integration over GL in Goldfeld and Jacquet, Automorphic Representations and L-functions for GL(n), Section 2.4.
- Formalization note: Constructs the two normalized Haar measures for upper-triangular restriction of right-integral-invariant matrix integrals.
- PROVENANCE-END
-/

/-!
# Matrix subgroups and normalized Iwasawa integration

The upper-triangular subgroup is closed. The subgroup of invertible
integral matrices is compact and open when the valuation ring is.
These subgroups give normalized Haar measures with the Iwasawa integral formula.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open MeasureTheory TopologicalSpace

/-- The subgroup of invertible upper-triangular matrices. -/
def valuationUpperTriangularSubgroup (F : Type*) [Field F] (n : Nat) :
    Subgroup (Units (Matrix (Fin n) (Fin n) F)) where
  carrier := fun g => g.val.IsUpperTriangular
  one_mem' := by
    intro i j h
    exact Matrix.one_apply_ne (ne_of_gt h)
  mul_mem' := by
    intro a b ha hb
    exact Matrix.BlockTriangular.mul ha hb
  inv_mem' := by
    intro a ha
    let _ : Invertible a.val := invertibleOfLeftInverse a.val a.inv a.inv_val
    have h := Matrix.blockTriangular_inv_of_blockTriangular ha
    rw [Matrix.inv_eq_left_inv a.inv_val] at h
    exact h

/-- The image of invertible matrices over the valuation ring. -/
def valuationIntegralMatrixSubgroup
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (n : Nat) :
    Subgroup (Units (Matrix (Fin n) (Fin n) F)) :=
  let L : RingHom (Matrix (Fin n) (Fin n) v.integer) (Matrix (Fin n) (Fin n) F) :=
    v.integer.subtype.mapMatrix
  (Units.map L.toMonoidHom).range

/-- An invertible matrix comes from the valuation ring exactly when its
entries and the entries of its inverse belong to that ring. -/
theorem mem_valuationIntegralMatrixSubgroup_iff
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (n : Nat) (g : Units (Matrix (Fin n) (Fin n) F)) :
    Membership.mem (valuationIntegralMatrixSubgroup v n) g <->
      And (forall i j, Membership.mem v.integer (g.val i j))
        (forall i j, Membership.mem v.integer (g.inv i j)) := by
  let L : RingHom (Matrix (Fin n) (Fin n) v.integer) (Matrix (Fin n) (Fin n) F) :=
    v.integer.subtype.mapMatrix
  change Membership.mem (Units.map L.toMonoidHom).range g <-> _
  rw [MonoidHom.mem_range]
  have hL : Function.Injective L := by
    intro A D h
    ext i j
    exact congrFun (congrFun h i) j
  constructor
  next =>
    intro hg
    choose k hk using hg
    rw [<- hk]
    exact And.intro (fun i j => (k.val i j).property) (fun i j => (k.inv i j).property)
  next =>
    intro hg
    let A : Matrix (Fin n) (Fin n) v.integer :=
      Matrix.of (fun i j => Subtype.mk (g.val i j) (hg.1 i j))
    let D : Matrix (Fin n) (Fin n) v.integer :=
      Matrix.of (fun i j => Subtype.mk (g.inv i j) (hg.2 i j))
    have hA : L A = g.val := rfl
    have hD : L D = g.inv := rfl
    have hAD : A * D = 1 := hL (by rw [map_mul, hA, hD, g.val_inv, map_one])
    have hDA : D * A = 1 := hL (by rw [map_mul, hD, hA, g.inv_val, map_one])
    let k : Units (Matrix (Fin n) (Fin n) v.integer) :=
      { val := A, inv := D, val_inv := hAD, inv_val := hDA }
    exact Exists.intro k (Units.ext hA)

/-- Every matrix coset of the integral subgroup has an upper-triangular
representative. This is the subgroup factorization needed for Haar integration. -/
theorem valuationIwasawaSubgroupFactorization
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V] (v : Valuation F V)
    (n : Nat) (g : Units (Matrix (Fin n) (Fin n) F)) :
    Exists (fun b : valuationUpperTriangularSubgroup F n =>
      Membership.mem (valuationIntegralMatrixSubgroup v n) (Inv.inv b.val * g)) := by
  choose k hk using exists_valuationIntegerRightUpperTriangular v n g
  let L : RingHom (Matrix (Fin n) (Fin n) v.integer) (Matrix (Fin n) (Fin n) F) :=
    v.integer.subtype.mapMatrix
  let x := Units.map L.toMonoidHom k
  let b : valuationUpperTriangularSubgroup F n := Subtype.mk (g * x) hk
  refine Exists.intro b ?_
  have h : Inv.inv b.val * g = Inv.inv x := by
    change Inv.inv (g * x) * g = Inv.inv x
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rw [h]
  apply (valuationIntegralMatrixSubgroup v n).inv_mem
  change Membership.mem (Units.map L.toMonoidHom).range x
  exact MonoidHom.mem_range.mpr (Exists.intro k rfl)

/-- The integral matrix subgroup is open whenever the valuation ring is open. -/
theorem isOpen_valuationIntegralMatrixSubgroup
    {F V : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LinearOrderedCommGroupWithZero V] (v : Valuation F V) (n : Nat)
    (hInteger : IsOpen (v.integer : Set F)) :
    IsOpen (valuationIntegralMatrixSubgroup v n : Set (Units (Matrix (Fin n) (Fin n) F))) := by
  let A : Set (Matrix (Fin n) (Fin n) F) :=
    Set.iInter (fun i => Set.iInter (fun j => Set.preimage (fun M => M i j) (v.integer : Set F)))
  have hA : IsOpen A :=
    isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j =>
      hInteger.preimage ((continuous_apply j).comp (continuous_apply i))))
  have hVal : Continuous (fun g : Units (Matrix (Fin n) (Fin n) F) => g.val) :=
    Units.continuous_val
  have hInv : Continuous (fun g : Units (Matrix (Fin n) (Fin n) F) => g.inv) :=
    Units.continuous_coe_inv
  have hEq : (valuationIntegralMatrixSubgroup v n : Set (Units (Matrix (Fin n) (Fin n) F))) =
      Set.inter (Set.preimage (fun g => g.val) A) (Set.preimage (fun g => g.inv) A) := by
    ext g
    change Membership.mem (valuationIntegralMatrixSubgroup v n) g <->
      And (Membership.mem A g.val) (Membership.mem A g.inv)
    rw [mem_valuationIntegralMatrixSubgroup_iff]
    simp only [A, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [hEq]
  exact (hA.preimage hVal).inter (hA.preimage hInv)

/-- Compactness of the valuation ring gives compactness of the integral
matrix subgroup, using the closed embedding by a matrix and its inverse. -/
theorem isCompact_valuationIntegralMatrixSubgroup
    {F V : Type*} [Field F] [TopologicalSpace F] [T2Space F] [IsTopologicalRing F]
    [LinearOrderedCommGroupWithZero V] (v : Valuation F V) (n : Nat)
    (hInteger : IsCompact (v.integer : Set F)) :
    IsCompact (valuationIntegralMatrixSubgroup v n : Set (Units (Matrix (Fin n) (Fin n) F))) := by
  let M := Matrix (Fin n) (Fin n) F
  let A : Set M :=
    Set.ofPred (fun m : M => forall i j : Fin n, Membership.mem v.integer (m i j))
  have hA : IsCompact A := isCompact_pi_infinite (fun _ : Fin n =>
    isCompact_pi_infinite (fun _ : Fin n => hInteger))
  have hAO : IsCompact (Set.preimage (MulOpposite.unop : MulOpposite M -> M) A) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hA
  have hEmbed : Topology.IsClosedEmbedding (Units.embedProduct M) :=
    Units.isClosedEmbedding_embedProduct
  have hPre := hEmbed.isCompact_preimage (hA.prod hAO)
  have hEq : (valuationIntegralMatrixSubgroup v n : Set (Units M)) =
      Set.preimage (Units.embedProduct M) (Set.prod A (Set.preimage MulOpposite.unop A)) := by
    ext g
    change Membership.mem (valuationIntegralMatrixSubgroup v n) g <->
      And (Membership.mem A g.val) (Membership.mem A g.inv)
    exact mem_valuationIntegralMatrixSubgroup_iff v n g
  rw [hEq]
  exact hPre

/-- Upper-triangular invertible matrices form a closed subgroup of GL. -/
theorem isClosed_valuationUpperTriangularSubgroup
    (F : Type*) [Field F] [TopologicalSpace F] [T2Space F] (n : Nat) :
    IsClosed (valuationUpperTriangularSubgroup F n :
      Set (Units (Matrix (Fin n) (Fin n) F))) := by
  let G := Units (Matrix (Fin n) (Fin n) F)
  let C : Set G := Set.iInter (fun i : Fin n => Set.iInter (fun j : Fin n =>
    Set.iInter (fun _ : j < i => Set.preimage
      (fun g : G => g.val i j) ({0} : Set F))))
  have hC : IsClosed C := by
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro h
    have hEntry : Continuous (fun m : Matrix (Fin n) (Fin n) F => m i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact isClosed_singleton.preimage (hEntry.comp Units.continuous_val)
  have hEq : (valuationUpperTriangularSubgroup F n : Set G) = C := by
    ext g
    change (forall i j : Fin n, j < i -> g.val i j = 0) <-> Membership.mem C g
    simp only [C, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hEq]
  exact hC

/-- Over a field with compact open valuation ring, the Haar measures on GL
and its upper-triangular subgroup can be normalized by their integral
subgroups. Their integrals agree for right-integral-subgroup-invariant
measurable complex kernels that are integrable on GL. -/
theorem exists_normalizedHaar_valuationIwasawa
    {F V : Type*} [Field F] [TopologicalSpace F] [T2Space F] [IsTopologicalRing F]
    [SecondCountableTopology F] [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (n : Nat)
    (hOpen : IsOpen (v.integer : Set F)) (hCompact : IsCompact (v.integer : Set F))
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) F))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) F))]
    [MeasurableSpace (valuationUpperTriangularSubgroup F n)]
    [BorelSpace (valuationUpperTriangularSubgroup F n)] :
    let G := Units (Matrix (Fin n) (Fin n) F)
    let B := valuationUpperTriangularSubgroup F n
    let K := valuationIntegralMatrixSubgroup v n
    Exists (fun mu : Measure G => Exists (fun nu : Measure B =>
      And mu.IsHaarMeasure (And nu.IsHaarMeasure
        (And (mu (K : Set G) = 1) (And (nu (K.comap B.subtype : Set B) = 1)
          (forall f : G -> Complex, Measurable f -> Integrable f mu ->
            (forall g k : G, Membership.mem K k -> f (g * k) = f g) ->
              And (Integrable (fun b : B => f (b : G)) nu)
                (integral mu f = integral nu (fun b : B => f (b : G))))))))) := by
  let M := Matrix (Fin n) (Fin n) F
  let G := Units M
  let B := valuationUpperTriangularSubgroup F n
  let K := valuationIntegralMatrixSubgroup v n
  let KB := K.comap B.subtype
  let : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> F))
  let : SecondCountableTopology (MulOpposite M) :=
    (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology G :=
    (Units.isEmbedding_embedProduct (M := M)).secondCountableTopology
  have hBEmbed : Topology.IsEmbedding (Subtype.val : B -> G) := Topology.IsEmbedding.subtypeVal
  let : SecondCountableTopology B := hBEmbed.secondCountableTopology
  have hKC : IsCompact (K : Set G) := isCompact_valuationIntegralMatrixSubgroup v n hCompact
  have hKO : IsOpen (K : Set G) := isOpen_valuationIntegralMatrixSubgroup v n hOpen
  have hBClosed : IsClosed (B : Set G) := isClosed_valuationUpperTriangularSubgroup F n
  have hKBc : IsCompact (KB : Set B) :=
    hBClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hKC
  have hKBo : IsOpen (KB : Set B) := hKO.preimage continuous_subtype_val
  let C : PositiveCompacts G :=
    { carrier := K
      isCompact' := hKC
      interior_nonempty' := by
        rw [hKO.interior_eq]
        exact Exists.intro 1 K.one_mem }
  let D : PositiveCompacts B :=
    { carrier := KB
      isCompact' := hKBc
      interior_nonempty' := by
        rw [hKBo.interior_eq]
        exact Exists.intro 1 KB.one_mem }
  let mu := Measure.haarMeasure C
  let nu := Measure.haarMeasure D
  have hMu : mu (K : Set G) = 1 := Measure.haarMeasure_self
  have hNu : nu (KB : Set B) = 1 := Measure.haarMeasure_self
  refine Exists.intro mu (Exists.intro nu
    (And.intro (inferInstanceAs ((Measure.haarMeasure C).IsHaarMeasure))
      (And.intro (inferInstanceAs ((Measure.haarMeasure D).IsHaarMeasure))
        (And.intro hMu (And.intro hNu ?_)))))
  intro f hF hInt hRight
  exact integral_rightInvariant_eq_integral_of_iwasawa B K
    continuous_subtype_val.measurable hKO (valuationIwasawaSubgroupFactorization v n)
    mu nu hMu hNu f hF hInt hRight

end Robin1984.GRH
