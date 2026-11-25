import Mathlib.MeasureTheory.Constructions.Pi
import Robin1984.GRH.ValuationIwasawaCoordinates

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Unipotent Haar integration in Goldfeld and Jacquet, Automorphic Representations and L-functions for GL(n), Section 2.4.
- Formalization note: Constructs normalized unitriangular Haar coordinates and evaluates every scaled upper-entry box as a product of scalar volumes.
- PROVENANCE-END
-/

/-!
# Upper-unitriangular measure and scaled integral boxes

First-row coordinates identify the upper-unitriangular group with one
additive row and the trailing upper-unitriangular block. The product
measure is left invariant. The volume of an integral box in scaled
coordinates has one factor for each strictly upper entry.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

section

variable (F : Type*) [Field F]

local notation "U" n => valuationUpperUnitriangularSubgroup F n

private theorem valuation_unitriangular_diag (n : Nat) (u : U n) (i : Fin n) :
    u.val.val.val i i = 1 := by
  have h : valuationTriangularDiagonalHom F n u.val = 1 := u.property
  exact congrArg (fun a : Units (Fin n -> F) => a.val i) h

private def valuationUnitriangularOfMatrix
    (n : Nat) (g : Matrix (Fin n) (Fin n) F) (hG : g.IsUpperTriangular)
    (hD : forall i, g i i = 1) : U n := by
  have hDet : g.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hG]
    simp only [hD, Finset.prod_const_one]
  have hUnit : IsUnit g.det := by
    rw [hDet]
    exact isUnit_one
  let gU : Units (Matrix (Fin n) (Fin n) F) := g.nonsingInvUnit hUnit
  let b : valuationUpperTriangularSubgroup F n := Subtype.mk gU hG
  refine Subtype.mk b ?_
  change valuationTriangularDiagonalHom F n b = 1
  apply Units.ext
  funext i
  exact hD i

private def valuationUnitriangularTail (n : Nat) (u : U (n + 1)) : U n := by
  let g := u.val.val.val.submatrix Fin.succ Fin.succ
  have hT : g.IsUpperTriangular := by
    intro i j hij
    exact u.val.property (Nat.succ_lt_succ hij)
  exact valuationUnitriangularOfMatrix F n g hT
    (fun i => valuation_unitriangular_diag F (n + 1) u i.succ)

private def valuationUnitriangularWithRow
    (n : Nat) (r : Fin n -> F) (u : U n) : U (n + 1) := by
  let g : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    Matrix.of (Fin.cases (Fin.cases 1 r) (fun i => Fin.cases 0 (u.val.val.val i)))
  have hT : g.IsUpperTriangular := by
    intro i j hij
    cases i using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ hij).elim
    | succ i =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact u.val.property (Nat.lt_of_succ_lt_succ hij)
  have hD (i : Fin (n + 1)) : g i i = 1 := by
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact valuation_unitriangular_diag F n u i
  exact valuationUnitriangularOfMatrix F (n + 1) g hT hD

/-- The first row above the diagonal and the trailing principal block give
coordinates on the upper unitriangular group. -/
def valuationUnitriangularFirstRowCoordinates (n : Nat) :
    Equiv (U (n + 1)) (Prod (Fin n -> F) (U n)) where
  toFun u := Prod.mk (fun j => u.val.val.val 0 j.succ) (valuationUnitriangularTail F n u)
  invFun p := valuationUnitriangularWithRow F n p.1 p.2
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (valuation_unitriangular_diag F (n + 1) u 0).symm
      | succ j => rfl
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (u.val.property (Fin.succ_pos i)).symm
      | succ j => rfl
  right_inv p := by
    apply Prod.ext
    next =>
      rfl
    next =>
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      rfl

/-- Left multiplication acts by left multiplication on the trailing block
and by a translation of the row depending on that block. -/
theorem valuationUnitriangularFirstRowCoordinates_mul (n : Nat) (x y : U (n + 1)) :
    let e := valuationUnitriangularFirstRowCoordinates F n
    e (x * y) =
      Prod.mk (fun j => (e y).1 j + Finset.sum Finset.univ (fun i : Fin n =>
        (e x).1 i * (e y).2.val.val.val i j)) ((e x).2 * (e y).2) := by
  apply Prod.ext
  next =>
    funext j
    change (x.val.val.val * y.val.val.val) 0 j.succ =
      y.val.val.val 0 j.succ + Finset.sum Finset.univ (fun i : Fin n =>
        x.val.val.val 0 i.succ * y.val.val.val i.succ j.succ)
    rw [Matrix.mul_apply, Fin.sum_univ_succ, valuation_unitriangular_diag F (n + 1) x 0, one_mul]
  next =>
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    change (x.val.val.val * y.val.val.val) i.succ j.succ =
      (x.val.val.val.submatrix Fin.succ Fin.succ * y.val.val.val.submatrix Fin.succ Fin.succ) i j
    have hx : x.val.val.val i.succ 0 = 0 := x.val.property (Fin.succ_pos i)
    rw [Matrix.mul_apply, Fin.sum_univ_succ, hx, zero_mul, zero_add]
    rfl

variable [TopologicalSpace F]

private theorem continuous_unitriangularMatrixVal (n : Nat) :
    Continuous (fun u : U n => u.val.val.val) := by
  have hV : Continuous (fun b : valuationUpperTriangularSubgroup F n => b.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  exact hV.comp continuous_subtype_val

variable [IsTopologicalRing F]

private theorem continuous_valuationUnitriangularOfMatrix
    {X : Type*} [TopologicalSpace X] (n : Nat) (g : X -> Matrix (Fin n) (Fin n) F)
    (hG : forall x, (g x).IsUpperTriangular)
    (hD : forall x i, g x i i = 1) (hg : Continuous g) :
    Continuous (fun x => valuationUnitriangularOfMatrix F n (g x) (hG x) (hD x)) := by
  let u (x : X) := (valuationUnitriangularOfMatrix F n (g x) (hG x) (hD x)).val.val
  have hi (x : X) : (u x).inv = (g x).adjugate := by
    have hp : (u x).inv * g x = 1 := (u x).inv_val
    have hDet : (g x).det = 1 := by
      rw [Matrix.det_of_isUpperTriangular (hG x)]
      simp only [hD, Finset.prod_const_one]
    rw [<- Matrix.inv_eq_left_inv hp, Matrix.inv_def, hDet, Ring.inverse_one]
    exact one_smul F _
  have hc : Continuous u := by
    apply Units.continuous_iff.mpr
    refine And.intro hg ?_
    change Continuous (fun x => (u x).inv)
    simp only [hi]
    exact hg.matrix_adjugate
  exact (hc.subtype_mk _).subtype_mk _

/-- The first-row and trailing-block coordinates are a homeomorphism. -/
def valuationUnitriangularFirstRowHomeomorph (n : Nat) :
    Homeomorph (U (n + 1)) (Prod (Fin n -> F) (U n)) where
  toEquiv := valuationUnitriangularFirstRowCoordinates F n
  continuous_toFun := by
    have hV := continuous_unitriangularMatrixVal F (n + 1)
    have hRow : Continuous (fun u : U (n + 1) => fun j : Fin n => u.val.val.val 0 j.succ) :=
      continuous_pi (fun j => hV.matrix_elem 0 j.succ)
    have hTail : Continuous (fun u : U (n + 1) => valuationUnitriangularTail F n u) := by
      unfold valuationUnitriangularTail
      apply continuous_valuationUnitriangularOfMatrix
      exact hV.matrix_submatrix Fin.succ Fin.succ
    exact hRow.prodMk hTail
  continuous_invFun := by
    change Continuous (fun p : Prod (Fin n -> F) (U n) =>
      valuationUnitriangularWithRow F n p.1 p.2)
    unfold valuationUnitriangularWithRow
    apply continuous_valuationUnitriangularOfMatrix
    apply continuous_matrix
    intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact continuous_const
      | succ j => exact (continuous_apply j).comp continuous_fst
    | succ i =>
      cases j using Fin.cases with
      | zero => exact continuous_const
      | succ j => exact ((continuous_unitriangularMatrixVal F n).matrix_elem i j).comp continuous_snd

open MeasureTheory

local notation "Row" n => Fin n -> F

/-- Additive row measure and left-invariant tail measure give a left-invariant
measure on the next upper-unitriangular group. -/
theorem isMulLeftInvariant_valuationUnitriangularRowProduct (n : Nat)
    [MeasurableSpace (U n)] [BorelSpace (U n)] [MeasurableMul (U n)]
    [MeasurableSpace (U (n + 1))] [BorelSpace (U (n + 1))]
    [MeasurableSpace (Row n)] [BorelSpace (Row n)] [MeasurableAdd (Row n)]
    [BorelSpace (Prod (U n) (Row n))]
    (muTail : Measure (U n)) (muRow : Measure (Row n))
    [muTail.IsMulLeftInvariant] [muRow.IsAddLeftInvariant] [SFinite muTail] [SFinite muRow] :
    (Measure.map (fun p : Prod (U n) (Row n) =>
      (valuationUnitriangularFirstRowHomeomorph F n).symm (p.2, p.1))
      (muTail.prod muRow)).IsMulLeftInvariant := by
  let E := valuationUnitriangularFirstRowHomeomorph F n
  let decode (p : Prod (U n) (Row n)) : U (n + 1) := E.symm (p.2, p.1)
  have hDecode : Measurable decode :=
    (E.symm.continuous.comp (continuous_snd.prodMk continuous_fst)).measurable
  constructor
  intro x
  let shift (t : U n) : Row n := fun j =>
    Finset.sum Finset.univ (fun i : Fin n => (E x).1 i * t.val.val.val i j)
  have hShift : Continuous shift := by
    apply continuous_pi
    intro j
    exact continuous_finsetSum _ (fun i _ =>
      continuous_const.mul ((continuous_unitriangularMatrixVal F n).matrix_elem i j))
  let T (p : Prod (U n) (Row n)) : Prod (U n) (Row n) :=
    ((E x).2 * p.1, shift p.1 + p.2)
  have hFiber : Measurable (fun p : Prod (U n) (Row n) => shift p.1 + p.2) :=
    ((hShift.comp continuous_fst).add continuous_snd).measurable
  have hT : MeasurePreserving T (muTail.prod muRow) (muTail.prod muRow) :=
    (measurePreserving_mul_left muTail (E x).2).skew_product hFiber
      (Filter.Eventually.of_forall (fun u => map_add_left_eq_self muRow (shift u)))
  have hDecodeCoord (p : Prod (U n) (Row n)) :
      E (decode p) = (p.2, p.1) := E.apply_symm_apply _
  have hRel : Function.comp (fun y : U (n + 1) => x * y) decode =
      Function.comp decode T := by
    funext p
    apply E.injective
    change E (x * decode p) = E (decode (T p))
    rw [hDecodeCoord]
    change (valuationUnitriangularFirstRowCoordinates F n) (x * decode p) = _
    rw [valuationUnitriangularFirstRowCoordinates_mul]
    change Prod.mk (fun j => (E (decode p)).1 j + Finset.sum Finset.univ (fun i : Fin n =>
      (E x).1 i * (E (decode p)).2.val.val.val i j)) ((E x).2 * (E (decode p)).2) = _
    rw [hDecodeCoord]
    apply Prod.ext
    case fst =>
      funext j
      change p.2 j + shift p.1 j = shift p.1 j + p.2 j
      exact add_comm _ _
    case snd => rfl
  have hLeft : Measurable (fun y : U (n + 1) => x * y) :=
    (continuous_const.mul continuous_id).measurable
  change Measure.map (fun y : U (n + 1) => x * y)
      (Measure.map decode (muTail.prod muRow)) = Measure.map decode (muTail.prod muRow)
  rw [Measure.map_map hLeft hDecode, hRel, <- Measure.map_map hDecode hT.measurable, hT.map_eq]

/-- The integrality constraints on scaled upper entries split into the first
row and the lower-right unitriangular block. -/
theorem preimage_valuationUnitriangularRow_scaledIntegral
    {V : Type*} [LinearOrderedCommGroupWithZero V] (v : Valuation F V)
    (n : Nat) (a : Fin (n + 1) -> F) :
    Set.preimage (fun p : Prod (U n) (Row n) =>
      (valuationUnitriangularFirstRowHomeomorph F n).symm (p.2, p.1))
      {u : U (n + 1) | forall i j : Fin (n + 1), i < j ->
        Membership.mem v.integer (a i * u.val.val.val i j)} =
      Set.prod
        {u : U n | forall i j : Fin n, i < j ->
          Membership.mem v.integer (a i.succ * u.val.val.val i j)}
        {r : Row n | forall j : Fin n, Membership.mem v.integer (a 0 * r j)} := by
  ext p
  let E := valuationUnitriangularFirstRowHomeomorph F n
  let y := E.symm (p.2, p.1)
  have hE : E y = (p.2, p.1) := E.apply_symm_apply _
  have hRow (j : Fin n) : y.val.val.val 0 j.succ = p.2 j :=
    congrArg (fun w : Prod (Row n) (U n) => w.1 j) hE
  have hTail (i j : Fin n) : y.val.val.val i.succ j.succ = p.1.val.val.val i j :=
    congrArg (fun w : Prod (Row n) (U n) => w.2.val.val.val i j) hE
  change (forall i j : Fin (n + 1), i < j ->
      Membership.mem v.integer (a i * y.val.val.val i j)) <->
    And (forall i j : Fin n, i < j ->
      Membership.mem v.integer (a i.succ * p.1.val.val.val i j))
      (forall j : Fin n, Membership.mem v.integer (a 0 * p.2 j))
  constructor
  case mp =>
    intro h
    refine And.intro ?_ ?_
    next =>
      intro i j hij
      simpa only [hTail i j] using h i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)
    next =>
      intro j
      simpa only [hRow j] using h 0 j.succ (Fin.succ_pos j)
  case mpr =>
    intro h i j hij
    revert hij
    refine Fin.cases ?_ (fun j => ?_) j
    next =>
      intro hij
      exact False.elim ((Fin.not_lt_zero i) hij)
    next =>
      revert i
      refine Fin.cases ?_ (fun i => ?_)
      next =>
        intro _
        simpa only [hRow j] using h.2 j
      next =>
        intro hij
        simpa only [hTail i j] using h.1 i j (Fin.succ_lt_succ_iff.mp hij)

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- A coordinatewise translate preserves the product of the local additive
measures. -/
theorem isAddLeftInvariant_valuationRowMeasure
    [MeasurableSpace F] [MeasurableAdd F]
    (n : Nat) (mu : Measure F) [SigmaFinite mu] [mu.IsAddLeftInvariant] :
    (Measure.pi (fun _ : Fin n => mu)).IsAddLeftInvariant := by
  constructor
  intro a
  exact (measurePreserving_pi (fun _ : Fin n => mu) (fun _ : Fin n => mu)
    (fun j => measurePreserving_add_left mu (a j))).map_eq

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- Each of the \(n\) entries in the first row contributes the same
one-dimensional volume to a scaled valuation box. -/
theorem measure_valuationRow_scaledIntegral
    {V : Type*} [LinearOrderedCommGroupWithZero V] (v : Valuation F V)
    [MeasurableSpace F] (n : Nat) (mu : Measure F) [SigmaFinite mu] (a : F) :
    Measure.pi (fun _ : Fin n => mu)
      {r : Row n | forall j, Membership.mem v.integer (a * r j)} =
      mu {y : F | Membership.mem v.integer (a * y)} ^ n := by
  have hBox : {r : Row n | forall j, Membership.mem v.integer (a * r j)} =
      Set.pi Set.univ (fun _ : Fin n => {y : F | Membership.mem v.integer (a * y)}) := by
    ext r
    simp
  rw [hBox, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- With product measure in upper-unitriangular coordinates, the first-row
constraints contribute the scalar local mass to the power \(n\). -/
theorem measure_valuationUnitriangularRowProduct_scaledIntegral
    {V : Type*} [LinearOrderedCommGroupWithZero V] (v : Valuation F V)
    [MeasurableSpace F]
    (n : Nat) (a : Fin (n + 1) -> F)
    [MeasurableSpace (U n)] [BorelSpace (U n)]
    [MeasurableSpace (U (n + 1))] [BorelSpace (U (n + 1))]
    [BorelSpace (Prod (U n) (Row n))]
    (muTail : Measure (U n)) (mu : Measure F)
    [SFinite muTail] [SigmaFinite mu] :
    Measure.map (fun p : Prod (U n) (Row n) =>
        (valuationUnitriangularFirstRowHomeomorph F n).symm (p.2, p.1))
        (muTail.prod (Measure.pi (fun _ : Fin n => mu)))
        {u : U (n + 1) | forall i j : Fin (n + 1), i < j ->
          Membership.mem v.integer (a i * u.val.val.val i j)} =
      muTail {u : U n | forall i j : Fin n, i < j ->
          Membership.mem v.integer (a i.succ * u.val.val.val i j)} *
      mu {y : F | Membership.mem v.integer (a 0 * y)} ^ n := by
  let E := (Homeomorph.prodComm (U n) (Row n)).trans
    (valuationUnitriangularFirstRowHomeomorph F n).symm
  have hE : MeasurableEmbedding (fun p : Prod (U n) (Row n) =>
      (valuationUnitriangularFirstRowHomeomorph F n).symm (p.2, p.1)) :=
    E.measurableEmbedding
  rw [hE.map_apply, preimage_valuationUnitriangularRow_scaledIntegral F v n a]
  exact (@Measure.prod_prod (U n) (Row n) _ _ muTail (Measure.pi (fun _ : Fin n => mu))
    _ _ _).trans (by rw [measure_valuationRow_scaledIntegral F v n mu (a 0)])

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- An upper-unitriangular matrix is integral exactly when its entries
strictly above the diagonal lie in the valuation ring. -/
theorem mem_valuationUnitriangularIntegralSubgroup_iff_upper
    {V : Type*} [LinearOrderedCommGroupWithZero V] (v : Valuation F V)
    (n : Nat) (u : U n) :
    Membership.mem (valuationUnitriangularIntegralSubgroup F n v) u <->
      forall i j : Fin n, i < j -> Membership.mem v.integer (u.val.val.val i j) := by
  change Membership.mem (valuationIntegralMatrixSubgroup v n) u.val.val <-> _
  constructor
  case mp =>
    intro hu i j _
    exact ((mem_valuationIntegralMatrixSubgroup_iff v n u.val.val).mp hu).1 i j
  case mpr =>
    intro hUpper
    have hIntegral (i j : Fin n) : Membership.mem v.integer (u.val.val.val i j) := by
      rcases lt_trichotomy i j with hlt | heq | hgt
      case inl => exact hUpper i j hlt
      case inr.inl =>
        subst j
        rw [valuation_unitriangular_diag F n u i]
        exact v.integer.one_mem
      case inr.inr =>
        rw [u.val.property hgt]
        exact v.integer.zero_mem
    let A : Matrix (Fin n) (Fin n) v.integer :=
      Matrix.of (fun i j => Subtype.mk (u.val.val.val i j) (hIntegral i j))
    have hT : A.IsUpperTriangular := by
      intro i j hij
      apply Subtype.ext
      exact u.val.property hij
    have hd (i : Fin n) : A i i = 1 := by
      apply Subtype.ext
      exact valuation_unitriangular_diag F n u i
    have hDet : IsUnit A.det := by
      rw [Matrix.det_of_isUpperTriangular hT]
      simp only [hd, Finset.prod_const_one, isUnit_one]
    apply MonoidHom.mem_range.mpr
    refine Exists.intro (A.nonsingInvUnit hDet) ?_
    apply Units.ext
    rfl

section

variable [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]

local instance unitriangularBorelMeasureSpace (n : Nat) : MeasurableSpace (U n) :=
  borel (U n)

local instance unitriangularBorelSpace (n : Nat) : BorelSpace (U n) :=
  BorelSpace.mk rfl

omit [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F] in
private theorem secondCountable_unitriangular (n : Nat) : SecondCountableTopology (U n) := by
  let M := Matrix (Fin n) (Fin n) F
  let _ : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> F))
  let opposite : Homeomorph M (MulOpposite M) := MulOpposite.opHomeomorph
  let _ : SecondCountableTopology (MulOpposite M) :=
    opposite.symm.isEmbedding.secondCountableTopology
  have hUnits : Topology.IsEmbedding (Units.embedProduct M) := Units.isEmbedding_embedProduct
  let _ : SecondCountableTopology (Units M) := hUnits.secondCountableTopology
  let _ : SecondCountableTopology (valuationUpperTriangularSubgroup F n) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      (fun b : valuationUpperTriangularSubgroup F n => b.val)).secondCountableTopology
  exact (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (fun u : U n => u.val)).secondCountableTopology

/-- Product additive measure on upper-unitriangular matrices, obtained by
adding the strictly upper entries of one row at each successor rank. -/
def valuationUnitriangularProductMeasure (mu : Measure F) : (n : Nat) -> Measure (U n)
  | 0 => Measure.dirac 1
  | n + 1 =>
    Measure.map (fun p : Prod (U n) (Row n) =>
      (valuationUnitriangularFirstRowHomeomorph F n).symm (p.2, p.1))
      ((valuationUnitriangularProductMeasure mu n).prod (Measure.pi (fun _ : Fin n => mu)))

/-- The recursive product has a countable finite-measure cover in every
rank when the one-dimensional additive measure is sigma finite. -/
theorem sigmaFinite_valuationUnitriangularProductMeasure
    (mu : Measure F) [SigmaFinite mu] (n : Nat) :
    SigmaFinite (valuationUnitriangularProductMeasure F mu n) := by
  induction n with
  | zero =>
    change SigmaFinite (Measure.dirac (1 : U 0))
    infer_instance
  | succ n ih =>
    let _ := ih
    let _ := secondCountable_unitriangular F n
    let E := (Homeomorph.prodComm (U n) (Row n)).trans
      (valuationUnitriangularFirstRowHomeomorph F n).symm
    exact E.measurableEmbedding.sigmaFinite_map

/-- Product additive Haar measure is left invariant in every rank. -/
theorem isMulLeftInvariant_valuationUnitriangularProductMeasure
    (mu : Measure F) [SigmaFinite mu] [mu.IsAddLeftInvariant] (n : Nat) :
    (valuationUnitriangularProductMeasure F mu n).IsMulLeftInvariant := by
  induction n with
  | zero =>
    constructor
    intro g
    have hG : g = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      apply Matrix.ext
      intro i _
      exact Fin.elim0 i
    subst g
    simp only [one_mul]
    change Measure.map id _ = _
    rw [Measure.map_id]
  | succ n ih =>
    let _ := secondCountable_unitriangular F n
    let _ := ih
    let _ := sigmaFinite_valuationUnitriangularProductMeasure F mu n
    let _ := isAddLeftInvariant_valuationRowMeasure F n mu
    exact isMulLeftInvariant_valuationUnitriangularRowProduct F n
      (valuationUnitriangularProductMeasure F mu n) (Measure.pi (fun _ : Fin n => mu))

/-- The volume of the region \(a_i u_{ij}\in\mathcal O\) for \(i<j\)
is the product of the scalar volumes with one factor per upper entry. -/
theorem measure_valuationUnitriangularProduct_scaledIntegral
    {V : Type*} [LinearOrderedCommGroupWithZero V] (v : Valuation F V)
    (mu : Measure F) [SigmaFinite mu] (n : Nat) (a : Fin n -> F) :
    valuationUnitriangularProductMeasure F mu n
      {u : U n | forall i j : Fin n, i < j ->
        Membership.mem v.integer (a i * u.val.val.val i j)} =
      Finset.univ.prod (fun i : Fin n =>
        mu {y : F | Membership.mem v.integer (a i * y)} ^ (n - (i.val + 1))) := by
  induction n with
  | zero =>
    rw [show {u : U 0 | forall i j : Fin 0, i < j ->
      Membership.mem v.integer (a i * u.val.val.val i j)} = Set.univ from by
        ext u
        simp]
    simp [valuationUnitriangularProductMeasure]
  | succ n ih =>
    let _ := secondCountable_unitriangular F n
    let _ := sigmaFinite_valuationUnitriangularProductMeasure F mu n
    rw [valuationUnitriangularProductMeasure,
      measure_valuationUnitriangularRowProduct_scaledIntegral F v n a,
      ih (fun i => a i.succ), Fin.prod_univ_succ]
    simp [Fin.val_succ, Nat.succ_sub_succ_eq_sub, mul_comm]

/-- With scalar mass one on the valuation ring, the integral
upper-unitriangular subgroup has mass one in every rank. -/
theorem measure_valuationUnitriangularProduct_integral
    {V : Type*} [LinearOrderedCommGroupWithZero V] (v : Valuation F V)
    (mu : Measure F) [SigmaFinite mu] (hm : mu (v.integer : Set F) = 1) (n : Nat) :
    valuationUnitriangularProductMeasure F mu n
      (valuationUnitriangularIntegralSubgroup F n v : Set (U n)) = 1 := by
  have hBox : (valuationUnitriangularIntegralSubgroup F n v : Set (U n)) =
      {u : U n | forall i j : Fin n, i < j ->
        Membership.mem v.integer ((fun _ : Fin n => (1 : F)) i * u.val.val.val i j)} := by
    ext u
    change Membership.mem (valuationUnitriangularIntegralSubgroup F n v) u <->
      forall i j : Fin n, i < j -> Membership.mem v.integer (1 * u.val.val.val i j)
    simpa only [one_mul] using mem_valuationUnitriangularIntegralSubgroup_iff_upper F v n u
  rw [hBox, measure_valuationUnitriangularProduct_scaledIntegral]
  simp only [one_mul]
  change Finset.univ.prod (fun i : Fin n => mu (v.integer : Set F) ^ (n - (i.val + 1))) = 1
  simp only [hm, one_pow, Finset.prod_const_one]

end
end

end Robin1984.GRH
