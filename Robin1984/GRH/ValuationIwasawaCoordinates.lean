import Mathlib.MeasureTheory.Measure.Prod
import Robin1984.GRH.ValuationIwasawaSubgroups

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The diagonal and unipotent local integration in Goldfeld and Jacquet, Automorphic Representations and L-functions for GL(n), Section 2.4.
- Formalization note: Proves the diagonal and upper-unitriangular homeomorphism and the normalized product-measure Iwasawa integral formula.
- PROVENANCE-END
-/

/-!
# Diagonal and upper-unitriangular Iwasawa coordinates

Left Haar integration on the upper-triangular group is a product integral
in these coordinates. The integral subgroups give the normalization.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

section

variable (F : Type*) [Field F] (n : Nat)

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "A" => Units (Fin n -> F)
local notation "B" => valuationUpperTriangularSubgroup F n

private theorem upperTriangular_mul_apply_diag
    {X Y : M} (hX : X.IsUpperTriangular) (hY : Y.IsUpperTriangular) (i : Fin n) :
    (X * Y) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  next =>
    intro j _ hj
    cases lt_or_gt_of_ne hj with
    | inl h => rw [hX h, zero_mul]
    | inr h => rw [hY h, mul_zero]
  next =>
    intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The diagonal entries define a homomorphism from upper-triangular units
to the group of invertible diagonal entries. -/
def valuationTriangularDiagonalHom : MonoidHom B A where
  toFun b :=
    { val := fun i => b.val.val i i
      inv := fun i => b.val.inv i i
      val_inv := by
        funext i
        have hi : b.val.inv.IsUpperTriangular := (Inv.inv b).property
        change b.val.val i i * b.val.inv i i = 1
        rw [<- upperTriangular_mul_apply_diag F n b.property hi, b.val.val_inv]
        exact Matrix.one_apply_eq i
      inv_val := by
        funext i
        have hi : b.val.inv.IsUpperTriangular := (Inv.inv b).property
        change b.val.inv i i * b.val.val i i = 1
        rw [<- upperTriangular_mul_apply_diag F n hi b.property, b.val.inv_val]
        exact Matrix.one_apply_eq i }
  map_one' := by
    apply Units.ext
    funext i
    exact Matrix.one_apply_eq i
  map_mul' a b := by
    apply Units.ext
    funext i
    exact upperTriangular_mul_apply_diag F n a.property b.property i

/-- The diagonal homomorphism has the section given by diagonal matrices. -/
def valuationDiagonalSection : MonoidHom A B := by
  let L : RingHom (Fin n -> F) M := Matrix.diagonalRingHom (Fin n) F
  let m := Units.map L.toMonoidHom
  exact
    { toFun := fun a => Subtype.mk (m a) (by
        intro i j hij
        exact Matrix.diagonal_apply_ne a.val (ne_of_gt hij))
      map_one' := Subtype.ext (map_one m)
      map_mul' := fun a b => Subtype.ext (map_mul m a b) }

@[simp]
theorem valuationTriangularDiagonalHom_section (a : A) :
    valuationTriangularDiagonalHom F n (valuationDiagonalSection F n a) = a := by
  apply Units.ext
  funext i
  exact Matrix.diagonal_apply_eq a.val i

/-- Upper unitriangular matrices are the kernel of the diagonal map. -/
def valuationUpperUnitriangularSubgroup : Subgroup B :=
  (valuationTriangularDiagonalHom F n).ker

/-- Every upper-triangular unit has unique coordinates as a diagonal unit
followed by an upper unitriangular unit. -/
def valuationTriangularCoordinates : Equiv B (Prod A (valuationUpperUnitriangularSubgroup F n)) := by
  let d := valuationTriangularDiagonalHom F n
  let s := valuationDiagonalSection F n
  refine
    { toFun := fun b => Prod.mk (d b) (Subtype.mk (Inv.inv (s (d b)) * b) ?_)
      invFun := fun p => s p.1 * p.2.val
      left_inv := ?_
      right_inv := ?_ }
  next =>
    change d (Inv.inv (s (d b)) * b) = 1
    rw [map_mul, map_inv, show d (s (d b)) = d b from
      valuationTriangularDiagonalHom_section F n (d b), inv_mul_cancel]
  next =>
    intro b
    exact mul_inv_cancel_left (s (d b)) b
  next =>
    intro p
    have hU : d p.2.val = 1 := p.2.property
    have hD : d (s p.1 * p.2.val) = p.1 := by
      rw [map_mul, show d (s p.1) = p.1 from valuationTriangularDiagonalHom_section F n p.1,
        hU, mul_one]
    apply Prod.ext
    next =>
      exact hD
    next =>
      apply Subtype.ext
      change Inv.inv (s (d (s p.1 * p.2.val))) * (s p.1 * p.2.val) = p.2.val
      rw [hD, inv_mul_cancel_left]

variable [TopologicalSpace F]

theorem continuous_valuationTriangularDiagonalHom :
    Continuous (fun b : B => valuationTriangularDiagonalHom F n b) := by
  have hV : Continuous (fun b : B => b.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  have hI : Continuous (fun b : B => b.val.inv) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hEntry (i : Fin n) : Continuous (fun m : M => m i i) :=
    (continuous_apply i).comp (continuous_apply i)
  apply Units.continuous_iff.mpr
  exact And.intro (continuous_pi (fun i => (hEntry i).comp hV))
    (continuous_pi (fun i => (hEntry i).comp hI))

theorem continuous_valuationDiagonalSection :
    Continuous (fun a : A => valuationDiagonalSection F n a) := by
  let L : RingHom (Fin n -> F) M := Matrix.diagonalRingHom (Fin n) F
  have hL : Continuous L := by
    change Continuous (fun a : Fin n -> F => fun i j : Fin n => Matrix.diagonal a i j)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    next =>
      subst j
      simpa only [Matrix.diagonal_apply_eq] using
        (continuous_apply i : Continuous (fun a : Fin n -> F => a i))
    next =>
      simpa only [Matrix.diagonal_apply_ne _ hij] using
        (continuous_const : Continuous (fun _ : Fin n -> F => (0 : F)))
  have hM := Units.continuous_map (f := L.toMonoidHom) hL
  exact hM.subtype_mk _

variable [IsTopologicalRing F]

/-- The diagonal and upper unitriangular coordinates are a homeomorphism. -/
def valuationTriangularHomeomorph :
    Homeomorph B (Prod A (valuationUpperUnitriangularSubgroup F n)) where
  toEquiv := valuationTriangularCoordinates F n
  continuous_toFun := by
    let d := valuationTriangularDiagonalHom F n
    let s := valuationDiagonalSection F n
    have hd : Continuous (fun b : B => d b) := continuous_valuationTriangularDiagonalHom F n
    have hs : Continuous (fun a : A => s a) := continuous_valuationDiagonalSection F n
    have hResidual : Continuous (fun b : B => Inv.inv (s (d b)) * b) :=
      ((hs.comp hd).inv).mul continuous_id
    exact hd.prodMk (hResidual.subtype_mk _)
  continuous_invFun := by
    have hs := continuous_valuationDiagonalSection F n
    exact (hs.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

local notation "U" => valuationUpperUnitriangularSubgroup F n

open MeasureTheory in
/-- Product left Haar measures in diagonal and unitriangular coordinates
push forward to a left-invariant measure on the upper-triangular group. -/
theorem isMulLeftInvariant_valuationTriangularProduct
    [MeasurableSpace B] [BorelSpace B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableMul A]
    [MeasurableSpace U] [BorelSpace U] [MeasurableMul U] [BorelSpace (Prod A U)]
    (muA : Measure A) (muU : Measure U)
    [muA.IsMulLeftInvariant] [muU.IsMulLeftInvariant] [SFinite muA] [SFinite muU] :
    (Measure.map (valuationTriangularHomeomorph F n).symm (muA.prod muU)).IsMulLeftInvariant := by
  let d := valuationTriangularDiagonalHom F n
  let s := valuationDiagonalSection F n
  let E := valuationTriangularHomeomorph F n
  have hE : Measurable (E.symm : Prod A U -> B) := E.symm.continuous.measurable
  constructor
  intro b
  let u0 : U := (E b).2
  have hU : d u0.val = 1 := u0.property
  let w (a : A) : U := Subtype.mk (Inv.inv (s a) * u0.val * s a) (by
    change d (Inv.inv (s a) * u0.val * s a) = 1
    rw [map_mul, map_mul, map_inv, hU, mul_one, inv_mul_cancel])
  have hW : Continuous w := by
    have hs : Continuous (fun a : A => s a) := continuous_valuationDiagonalSection F n
    exact ((hs.inv.mul continuous_const).mul hs).subtype_mk _
  let T (p : Prod A U) := Prod.mk (d b * p.1) (w p.1 * p.2)
  have hShear : Measurable (fun p : Prod A U => w p.1 * p.2) :=
    ((hW.comp continuous_fst).mul continuous_snd).measurable
  have hT : MeasurePreserving T (muA.prod muU) (muA.prod muU) :=
    (measurePreserving_mul_left muA (d b)).skew_product hShear
      (Filter.Eventually.of_forall (fun a => map_mul_left_eq_self muU (w a)))
  have hB : b = s (d b) * u0.val :=
    (mul_inv_cancel_left (s (d b)) b).symm
  have hConj (a : A) : s a * (w a).val = u0.val * s a := by
    change s a * (Inv.inv (s a) * u0.val * s a) = _
    rw [<- mul_assoc, mul_inv_cancel_left]
  have hRel : Function.comp (fun x : B => b * x) E.symm = Function.comp E.symm T := by
    funext p
    change b * (s p.1 * p.2.val) = s (d b * p.1) * ((w p.1).val * p.2.val)
    calc
      _ = (s (d b) * u0.val) * (s p.1 * p.2.val) := congrArg (fun x => x * _) hB
      _ = s (d b) * ((u0.val * s p.1) * p.2.val) := by simp only [mul_assoc]
      _ = _ := by rw [map_mul, <- hConj p.1]; simp only [mul_assoc]
  have hLeft : Measurable (fun x : B => b * x) := (continuous_const.mul continuous_id).measurable
  change Measure.map (fun x : B => b * x) (Measure.map E.symm (muA.prod muU)) =
    Measure.map E.symm (muA.prod muU)
  rw [Measure.map_map hLeft hE, hRel, <- Measure.map_map hE hT.measurable, hT.map_eq]

/-- The diagonal matrices whose entries and inverse entries are integral. -/
def valuationDiagonalIntegralSubgroup
    {V : Type*} [LinearOrderedCommGroupWithZero V] (v : Valuation F V) : Subgroup A :=
  (valuationIntegralMatrixSubgroup v n).comap
    ((valuationUpperTriangularSubgroup F n).subtype.comp (valuationDiagonalSection F n))

/-- The intersection of the unitriangular group with the integral matrix group. -/
def valuationUnitriangularIntegralSubgroup
    {V : Type*} [LinearOrderedCommGroupWithZero V] (v : Valuation F V) : Subgroup U :=
  (valuationIntegralMatrixSubgroup v n).comap
    ((valuationUpperTriangularSubgroup F n).subtype.comp
      (valuationUpperUnitriangularSubgroup F n).subtype)

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem diagonalProjection_mem_integral
    {V : Type*} [LinearOrderedCommGroupWithZero V] (v : Valuation F V) (b : B)
    (hb : Membership.mem (valuationIntegralMatrixSubgroup v n) b.val) :
    Membership.mem (valuationDiagonalIntegralSubgroup F n v)
      (valuationTriangularDiagonalHom F n b) := by
  have h := (mem_valuationIntegralMatrixSubgroup_iff v n b.val).mp hb
  change Membership.mem (valuationIntegralMatrixSubgroup v n)
    (valuationDiagonalSection F n (valuationTriangularDiagonalHom F n b)).val
  apply (mem_valuationIntegralMatrixSubgroup_iff v n _).mpr
  constructor
  next =>
    intro i j
    change Membership.mem v.integer (Matrix.diagonal (fun k => b.val.val k k) i j)
    by_cases hij : i = j
    next =>
      subst j
      rw [Matrix.diagonal_apply_eq]
      exact h.1 i i
    next =>
      rw [Matrix.diagonal_apply_ne _ hij]
      exact v.integer.zero_mem
  next =>
    intro i j
    change Membership.mem v.integer (Matrix.diagonal (fun k => b.val.inv k k) i j)
    by_cases hij : i = j
    next =>
      subst j
      rw [Matrix.diagonal_apply_eq]
      exact h.2 i i
    next =>
      rw [Matrix.diagonal_apply_ne _ hij]
      exact v.integer.zero_mem

/-- The integral upper-triangular matrices are a product of the integral
diagonal and integral unitriangular matrices in the Iwasawa coordinates. -/
theorem preimage_valuationTriangularHomeomorph_integral
    {V : Type*} [LinearOrderedCommGroupWithZero V] (v : Valuation F V) :
    Set.preimage (valuationTriangularHomeomorph F n).symm
        ((valuationIntegralMatrixSubgroup v n).comap (valuationUpperTriangularSubgroup F n).subtype :
          Set B) =
      Set.prod (valuationDiagonalIntegralSubgroup F n v : Set A)
        (valuationUnitriangularIntegralSubgroup F n v : Set U) := by
  let K := valuationIntegralMatrixSubgroup v n
  let d := valuationTriangularDiagonalHom F n
  let s := valuationDiagonalSection F n
  let E := valuationTriangularHomeomorph F n
  ext p
  change Membership.mem K (s p.1 * p.2.val).val <->
    And (Membership.mem K (s p.1).val) (Membership.mem K p.2.val.val)
  constructor
  next =>
    intro hp
    have hd : d (s p.1 * p.2.val) = p.1 :=
      congrArg Prod.fst (E.apply_symm_apply p)
    have ha := diagonalProjection_mem_integral F n v (s p.1 * p.2.val) hp
    change Membership.mem (valuationDiagonalIntegralSubgroup F n v) (d (s p.1 * p.2.val)) at ha
    rw [hd] at ha
    have hs : Membership.mem K (s p.1).val := ha
    have hu := K.mul_mem (K.inv_mem hs) hp
    change Membership.mem K (Inv.inv (s p.1).val * ((s p.1).val * p.2.val.val)) at hu
    rw [inv_mul_cancel_left] at hu
    exact And.intro hs hu
  next =>
    intro hp
    exact K.mul_mem hp.1 hp.2

open MeasureTheory in
/-- For a right-integral-invariant kernel, normalized Haar integrability
on the full matrix group is equivalent to that in the product coordinates.
The two Bochner integrals agree. -/
theorem integrable_iff_and_integral_valuationIwasawa_in_product_coordinates
    [SecondCountableTopology F] {V : Type*} [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (hOpen : IsOpen (v.integer : Set F))
    [MeasurableSpace (Units M)] [BorelSpace (Units M)] [MeasurableMul (Units M)]
    [MeasurableSpace B] [BorelSpace B] [MeasurableMul B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableMul A]
    [MeasurableSpace U] [BorelSpace U] [MeasurableMul U] [BorelSpace (Prod A U)]
    (muG : Measure (Units M)) (muA : Measure A) (muU : Measure U)
    [muG.IsMulLeftInvariant] [muA.IsMulLeftInvariant] [muU.IsMulLeftInvariant]
    [SFinite muA] [SFinite muU]
    (hG : muG (valuationIntegralMatrixSubgroup v n : Set (Units M)) = 1)
    (hA : muA (valuationDiagonalIntegralSubgroup F n v : Set A) = 1)
    (hU : muU (valuationUnitriangularIntegralSubgroup F n v : Set U) = 1)
    (f : Units M -> Complex) (hF : Measurable f)
    (hRight : forall g k : Units M, Membership.mem (valuationIntegralMatrixSubgroup v n) k ->
      f (g * k) = f g) :
    let E := valuationTriangularHomeomorph F n
    And (Integrable f muG <-> Integrable (fun p => f (E.symm p).val) (muA.prod muU))
      (integral muG f = integral (muA.prod muU) (fun p => f (E.symm p).val)) := by
  let K := valuationIntegralMatrixSubgroup v n
  let E := valuationTriangularHomeomorph F n
  let : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> F))
  let opposite : Homeomorph M (MulOpposite M) := MulOpposite.opHomeomorph
  let : SecondCountableTopology (MulOpposite M) := opposite.symm.isEmbedding.secondCountableTopology
  have hUnits : Topology.IsEmbedding (Units.embedProduct M) := Units.isEmbedding_embedProduct
  let : SecondCountableTopology (Units M) := hUnits.secondCountableTopology
  let muB := Measure.map E.symm (muA.prod muU)
  let : muB.IsMulLeftInvariant := isMulLeftInvariant_valuationTriangularProduct F n muA muU
  have hIncl : Measurable (Subtype.val : B -> Units M) := continuous_subtype_val.measurable
  have hOpenK : IsOpen (K : Set (Units M)) := isOpen_valuationIntegralMatrixSubgroup v n hOpen
  have hE : Measurable (E.symm : Prod A U -> B) := E.symm.continuous.measurable
  have hKBm : MeasurableSet (K.comap (valuationUpperTriangularSubgroup F n).subtype : Set B) :=
    hIncl hOpenK.measurableSet
  have hPre : Set.preimage E.symm (K.comap (valuationUpperTriangularSubgroup F n).subtype : Set B) =
      Set.prod (valuationDiagonalIntegralSubgroup F n v : Set A)
        (valuationUnitriangularIntegralSubgroup F n v : Set U) :=
    preimage_valuationTriangularHomeomorph_integral F n v
  have hB : muB (K.comap (valuationUpperTriangularSubgroup F n).subtype : Set B) = 1 := by
    change Measure.map E.symm (muA.prod muU) _ = _
    rw [Measure.map_apply hE hKBm, hPre]
    exact (@Measure.prod_prod A U _ _ muA muU _ _ _).trans (by rw [hA, hU, mul_one])
  have hRestrict := integrable_iff_and_integral_rightInvariant_of_iwasawa
    (valuationUpperTriangularSubgroup F n) K hIncl hOpenK
    (valuationIwasawaSubgroupFactorization v n) muG muB hG hB f hF hRight
  have hMeas : AEStronglyMeasurable (fun b : B => f (b : Units M)) muB :=
    (hF.comp hIncl).aestronglyMeasurable
  exact And.intro (hRestrict.1.trans (integrable_map_measure hMeas hE.aemeasurable))
    (hRestrict.2.trans (integral_map hE.aemeasurable hMeas))

open MeasureTheory in
/-- Normalized diagonal and unitriangular Haar measures compute the integral
of a right-integral-invariant kernel on the full matrix group. -/
theorem integral_valuationIwasawa_in_product_coordinates
    [SecondCountableTopology F] {V : Type*} [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (hOpen : IsOpen (v.integer : Set F))
    [MeasurableSpace (Units M)] [BorelSpace (Units M)] [MeasurableMul (Units M)]
    [MeasurableSpace B] [BorelSpace B] [MeasurableMul B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableMul A]
    [MeasurableSpace U] [BorelSpace U] [MeasurableMul U] [BorelSpace (Prod A U)]
    (muG : Measure (Units M)) (muA : Measure A) (muU : Measure U)
    [muG.IsMulLeftInvariant] [muA.IsMulLeftInvariant] [muU.IsMulLeftInvariant]
    [SFinite muA] [SFinite muU]
    (hG : muG (valuationIntegralMatrixSubgroup v n : Set (Units M)) = 1)
    (hA : muA (valuationDiagonalIntegralSubgroup F n v : Set A) = 1)
    (hU : muU (valuationUnitriangularIntegralSubgroup F n v : Set U) = 1)
    (f : Units M -> Complex) (hF : Measurable f) (hInt : Integrable f muG)
    (hRight : forall g k : Units M, Membership.mem (valuationIntegralMatrixSubgroup v n) k ->
      f (g * k) = f g) :
    let E := valuationTriangularHomeomorph F n
    And (Integrable (fun p => f (E.symm p).val) (muA.prod muU))
      (integral muG f = integral (muA.prod muU) (fun p => f (E.symm p).val)) := by
  have h := integrable_iff_and_integral_valuationIwasawa_in_product_coordinates F n v hOpen
    muG muA muU hG hA hU f hF hRight
  exact And.intro (h.1.mp hInt) h.2

end

end Robin1984.GRH
