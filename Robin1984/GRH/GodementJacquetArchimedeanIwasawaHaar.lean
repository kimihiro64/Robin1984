import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Linarith
import Robin1984.GRH.GodementJacquetArchimedeanIwasawa

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Archimedean Iwasawa coordinates and uniqueness of Haar measure.
- Formalization note: Transfers Haar measure to triangular and compact unitary factors.
- PROVENANCE-END
-/

/-!
# Archimedean Iwasawa coordinates and Haar measure

The positive upper-triangular subgroup and the unitary group give a
homeomorphism onto the matrix units. Compactness makes right unitary
translation preserve left Haar measure. In the resulting coordinates,
Haar measure is a positive constant times the product of the factor
Haar measures.
-/

set_option autoImplicit false

namespace Robin1984.GRH

section

variable {F : Type*} [RCLike F] {n : Nat}

local notation "M" => Matrix (Fin n) (Fin n) F

private theorem archUpperTriangular_mul_diag {A B : M}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  . intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    . have h0 : A i j = 0 := hA h
      rw [h0, zero_mul]
    . have h0 : B j i = 0 := hB h
      rw [h0, mul_zero]
  . exact fun h => (h (Finset.mem_univ i)).elim

private theorem positiveUpperTriangular_isUnit {A : M}
    (hA : A.IsUpperTriangular)
    (hp : forall i, exists x : Real, And (0 < x) (A i i = (x : F))) : IsUnit A := by
  apply (Matrix.isUnit_iff_isUnit_det A).mpr
  rw [Matrix.det_of_isUpperTriangular hA]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  choose x hx using hp i
  rw [hx.2]
  exact fun h => (ne_of_gt hx.1) (RCLike.ofReal_eq_zero.mp h)

/-- Upper-triangular matrix units with positive real diagonal entries. -/
def positiveUpperTriangularMatrixSubgroup (F : Type*) [RCLike F] (n : Nat) :
    Subgroup (Units (Matrix (Fin n) (Fin n) F)) where
  carrier := Set.ofPred (fun g : Units (Matrix (Fin n) (Fin n) F) =>
    And g.val.IsUpperTriangular
      (forall i, exists x : Real, And (0 < x) (g.val i i = (x : F))))
  one_mem' := by
    refine And.intro ?_ ?_
    . intro i j hij
      change (1 : Matrix (Fin n) (Fin n) F) i j = 0
      exact Matrix.one_apply_ne (ne_of_gt hij)
    . intro i
      refine Exists.intro 1 (And.intro zero_lt_one ?_)
      change (1 : Matrix (Fin n) (Fin n) F) i i = ((1 : Real) : F)
      rw [Matrix.one_apply_eq, RCLike.ofReal_one]
  mul_mem' := by
    intro g h hg hh
    have hTri : (g.val * h.val).IsUpperTriangular := hg.1.mul hh.1
    refine And.intro hTri ?_
    intro i
    choose a ha using hg.2 i
    choose b hb using hh.2 i
    refine Exists.intro (a * b) (And.intro (mul_pos ha.1 hb.1) ?_)
    change (g.val * h.val) i i = ((a * b : Real) : F)
    rw [archUpperTriangular_mul_diag hg.1 hh.1, ha.2, hb.2, RCLike.ofReal_mul]
  inv_mem' := by
    intro g hg
    let _ : Invertible g.val :=
      Matrix.invertibleOfIsUnitDet g.val ((Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit)
    have hPair : g.val * (Inv.inv g).val = 1 := g.val_inv
    have hLeft : Inv.inv g.val * g.val = 1 := by
      rw [<- Matrix.invOf_eq_nonsing_inv]
      exact invOf_mul_self g.val
    have hEq : Inv.inv g.val = (Inv.inv g).val := by
      calc
        _ = Inv.inv g.val * (g.val * (Inv.inv g).val) := by rw [hPair, mul_one]
        _ = _ := by rw [<- mul_assoc, hLeft, one_mul]
    have hTri : (Inv.inv g.val).IsUpperTriangular :=
      Matrix.blockTriangular_inv_of_blockTriangular hg.1
    rw [hEq] at hTri
    refine And.intro hTri ?_
    intro i
    choose a ha using hg.2 i
    refine Exists.intro (Inv.inv a) (And.intro (inv_pos.mpr ha.1) ?_)
    have hEntry := congrArg (fun A : Matrix (Fin n) (Fin n) F => A i i) hPair
    change (g.val * (Inv.inv g).val) i i = (1 : Matrix (Fin n) (Fin n) F) i i at hEntry
    rw [archUpperTriangular_mul_diag hg.1 hTri, Matrix.one_apply_eq, ha.2] at hEntry
    have hA : Not ((a : F) = 0) := fun h => (ne_of_gt ha.1) (RCLike.ofReal_eq_zero.mp h)
    have hVal : (Inv.inv g).val i i = (1 : F) / (a : F) :=
      (eq_div_iff hA).mpr ((mul_comm _ _).trans hEntry)
    rw [hVal, one_div, RCLike.ofReal_inv]

private theorem bijective_positiveUpperTriangular_unitary_mul
    (F : Type*) [RCLike F] (n : Nat) :
    Function.Bijective (fun p : Prod (positiveUpperTriangularMatrixSubgroup F n) (Matrix.unitaryGroup (Fin n) F) =>
      p.1.val * Unitary.toUnits (Inv.inv p.2)) := by
  constructor
  . intro p q h
    have hFactor :
        p.1.val.val * (Inv.inv p.2).val = q.1.val.val * (Inv.inv q.2).val :=
      congrArg Units.val h
    have hp := p.1.property
    have hq := q.1.property
    have he := positiveUpperTriangular_unitary_factors_unique
      p.1.val.val q.1.val.val (Inv.inv p.2).val (Inv.inv q.2).val
      hp.1 hq.1 hp.2 hq.2 (Inv.inv p.2).property (Inv.inv q.2).property hFactor
    exact Prod.ext (Subtype.ext (Units.ext he.1)) (inv_injective (Subtype.ext he.2))
  . intro g
    choose R Q h using exists_positive_upperTriangular_mul_unitary g
    have hR := positiveUpperTriangular_isUnit h.1 h.2.1
    let r := hR.unit
    have hr : r.val = R := hR.unit_spec
    have hrp : Membership.mem (positiveUpperTriangularMatrixSubgroup F n) r := by
      change And r.val.IsUpperTriangular (forall i, exists x : Real, And (0 < x) (r.val i i = (x : F)))
      rw [hr]
      exact And.intro h.1 h.2.1
    let q : Matrix.unitaryGroup (Fin n) F := Subtype.mk Q h.2.2.1
    refine Exists.intro (Prod.mk (Subtype.mk r hrp) (Inv.inv q)) ?_
    change r * Unitary.toUnits (Inv.inv (Inv.inv q)) = g
    rw [inv_inv]
    apply Units.ext
    change r.val * Q = g.val
    rw [hr]
    exact h.2.2.2

end

section Topology

variable {F : Type*} [RCLike F] {n : Nat}

local notation "M" => Matrix (Fin n) (Fin n) F

private theorem archMatrixStar_continuous : Continuous (fun A : M => star A) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun A : M => star (A j i))
  exact continuous_star.comp ((continuous_apply i).comp (continuous_apply j))

private theorem norm_entry_le_one_of_unitary {A : M}
    (hA : Membership.mem (Matrix.unitaryGroup (Fin n) F) A)
    (i j : Fin n) : norm (A i j) <= 1 := by
  have hEq := congrArg (fun B : M => B j j) (Matrix.mem_unitaryGroup_iff'.mp hA)
  change (star A * A) j j = (1 : M) j j at hEq
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hEq
  have hTerm (k : Fin n) : (star A) j k * A k j = ((norm (A k j) ^ 2 : Real) : F) := by
    change (starRingEnd F) (A k j) * A k j = _
    rw [RCLike.conj_mul, RCLike.ofReal_pow]
  have hCast : ((Finset.univ.sum (fun k : Fin n => norm (A k j) ^ 2) : Real) : F) = 1 := by
    rw [RCLike.ofReal_sum]
    simpa only [hTerm] using hEq
  have hSum : Finset.univ.sum (fun k : Fin n => norm (A k j) ^ 2) = 1 :=
    RCLike.ofReal_injective (hCast.trans (RCLike.ofReal_one (K := F)).symm)
  have hSq : norm (A i j) ^ 2 <= 1 := by
    rw [<- hSum]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (norm (A k j))) (Finset.mem_univ i)
  nlinarith [norm_nonneg (A i j)]

private theorem isCompact_archimedeanUnitaryGroup [ProperSpace F] :
    IsCompact (Matrix.unitaryGroup (Fin n) F : Set M) := by
  let S : Set M := Set.pi Set.univ
    (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : F) 1))
  have hS : IsCompact S :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  refine hS.of_isClosed_subset ?_ ?_
  . have hEq : (Matrix.unitaryGroup (Fin n) F : Set M) =
        Set.ofPred (fun Q : M => star Q * Q = 1) :=
      Set.ext (fun Q => Matrix.mem_unitaryGroup_iff')
    rw [hEq]
    exact isClosed_eq ((archMatrixStar_continuous (F := F) (n := n)).mul continuous_id)
      continuous_const
  . intro Q hQ i _ j _
    change dist (Q i j) 0 <= 1
    rw [dist_zero_right]
    exact norm_entry_le_one_of_unitary hQ i j

private theorem continuous_archimedeanUnitary_toUnits :
    Continuous (fun Q : Matrix.unitaryGroup (Fin n) F => Unitary.toUnits Q) := by
  rw [Units.isInducing_embedProduct.continuous_iff]
  change Continuous (fun Q : Matrix.unitaryGroup (Fin n) F =>
    Prod.mk Q.val (MulOpposite.op (star Q.val)))
  have hs : Continuous (fun Q : Matrix.unitaryGroup (Fin n) F => star Q.val) :=
    (archMatrixStar_continuous (F := F) (n := n)).comp continuous_subtype_val
  exact continuous_subtype_val.prodMk (MulOpposite.opHomeomorph.continuous.comp hs)

end Topology


open MeasureTheory MeasureTheory.Measure


private theorem exists_pos_smul_map_mul_inv_productHaar
    {T U G : Type*} [Group T] [Group U] [Group G]
    [TopologicalSpace T] [TopologicalSpace U] [TopologicalSpace G]
    [IsTopologicalGroup T] [IsTopologicalGroup U] [IsTopologicalGroup G]
    [T2Space T] [T2Space U] [SecondCountableTopology T] [SecondCountableTopology U]
    [LocallyCompactSpace T] [LocallyCompactSpace U]
    [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace G]
    [BorelSpace T] [BorelSpace U] [BorelSpace G]
    (a : MonoidHom T G) (b : MonoidHom U G) (e : Homeomorph (Prod T U) G)
    (hChart : forall x, e x = a x.1 * Inv.inv (b x.2))
    (mu : Measure G) [mu.IsHaarMeasure]
    (hRight : forall u : U, MeasurePreserving (fun x : G => x * Inv.inv (b u)) mu mu)
    (muT : Measure T) (muU : Measure U) [muT.IsHaarMeasure] [muU.IsHaarMeasure]
    [SFinite muT] [SFinite muU] :
    exists c : NNReal, And (0 < c)
      (mu = HSMul.hSMul c (Measure.map e (muT.prod muU))) := by
  let E : MeasurableEquiv (Prod T U) G := e.toMeasurableEquiv
  let nu := mu.comap E
  have hNu : nu = Measure.map E.symm mu := by
    apply Measure.ext
    intro s hs
    change (mu.comap E) s = (Measure.map E.symm mu) s
    rw [E.measurableEmbedding.comap_apply, Measure.map_apply E.symm.measurable hs]
    exact congrArg (fun t => mu t) (Equiv.image_eq_preimage_symm E.toEquiv s)
  have hInv : nu.IsMulLeftInvariant := by
    constructor
    intro p
    let f (x : G) := a p.1 * x * Inv.inv (b p.2)
    have hf : MeasurePreserving f mu mu :=
      (hRight p.2).comp (measurePreserving_mul_left mu (a p.1))
    have hE (x : G) : E (p * E.symm x) = f x := by
      have hLocal : x = a (E.symm x).1 * Inv.inv (b (E.symm x).2) :=
        (E.apply_symm_apply x).symm.trans (hChart (E.symm x))
      change e (p * E.symm x) = a p.1 * x * Inv.inv (b p.2)
      rw [hChart]
      change a (p.1 * (E.symm x).1) * Inv.inv (b (p.2 * (E.symm x).2)) = _
      rw [map_mul, map_mul, mul_inv_rev]
      calc
        _ = a p.1 * (a (E.symm x).1 * Inv.inv (b (E.symm x).2)) * Inv.inv (b p.2) := by
          simp only [mul_assoc]
        _ = _ := congrArg (fun y => a p.1 * y * Inv.inv (b p.2)) hLocal.symm
    have hComp : Function.comp (fun y : Prod T U => p * y) E.symm = Function.comp E.symm f :=
      funext (fun x => E.injective ((hE x).trans (E.apply_symm_apply (f x)).symm))
    change Measure.map (fun y : Prod T U => p * y) nu = nu
    rw [hNu, Measure.map_map (measurable_const_mul p) E.symm.measurable, hComp,
      <- Measure.map_map E.symm.measurable hf.measurable, hf.map_eq]
  let _ : nu.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts :=
        IsFiniteMeasureOnCompacts.comap' mu e.continuous E.measurableEmbedding
      toIsMulLeftInvariant := hInv
      toIsOpenPosMeasure := IsOpenPosMeasure.comap mu e.isOpenEmbedding }
  let P := muT.prod muU
  let c := Measure.haarScalarFactor nu P
  have hScale : nu = HSMul.hSMul c P := Measure.isMulLeftInvariant_eq_smul_of_regular nu P
  have hMap : Measure.map E nu = mu := by
    rw [hNu, Measure.map_map E.measurable E.symm.measurable]
    have hId : Function.comp (E : Prod T U -> G) E.symm = id :=
      funext (fun y => E.apply_symm_apply y)
    rw [hId, Measure.map_id]
  refine Exists.intro c (And.intro (Measure.haarScalarFactor_pos_of_isHaarMeasure nu P) ?_)
  rw [<- hMap, hScale, Measure.map_smul]
  rfl

private theorem exists_homeomorph_mul_inv_of_closed_left
    {T U G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace T] [TopologicalSpace U] [CompactSpace U]
    (a : T -> G) (b : U -> G) (ha : Topology.IsClosedEmbedding a) (hb : Continuous b)
    (hBij : Function.Bijective (fun p : Prod T U => a p.1 * Inv.inv (b p.2))) :
    exists e : Homeomorph (Prod T U) G, forall p, e p = a p.1 * Inv.inv (b p.2) := by
  let H : Homeomorph (Prod G U) (Prod G U) :=
    { toEquiv :=
        { toFun := fun p => Prod.mk (p.1 * Inv.inv (b p.2)) p.2
          invFun := fun p => Prod.mk (p.1 * b p.2) p.2
          left_inv := by
            intro p
            apply Prod.ext
            . change (p.1 * Inv.inv (b p.2)) * b p.2 = p.1
              rw [mul_assoc, inv_mul_cancel, mul_one]
            . rfl
          right_inv := by
            intro p
            apply Prod.ext
            . change (p.1 * b p.2) * Inv.inv (b p.2) = p.1
              rw [mul_assoc, mul_inv_cancel, mul_one]
            . rfl }
      continuous_toFun :=
        (continuous_fst.mul ((hb.comp continuous_snd).inv)).prodMk continuous_snd
      continuous_invFun :=
        (continuous_fst.mul (hb.comp continuous_snd)).prodMk continuous_snd }
  let f (p : Prod T U) := a p.1 * Inv.inv (b p.2)
  let e := Equiv.ofBijective f hBij
  have hCont : Continuous f :=
    (ha.continuous.comp continuous_fst).mul ((hb.comp continuous_snd).inv)
  have hId : Topology.IsClosedEmbedding (id : U -> U) :=
    (Homeomorph.refl U).isClosedEmbedding
  have hIncl : Topology.IsClosedEmbedding (Prod.map a (id : U -> U)) :=
    ha.prodMap hId
  have hFst : IsClosedMap (Prod.fst : Prod G U -> G) := isClosedMap_fst_of_compactSpace
  have hClosed : IsClosedMap f :=
    hFst.comp (H.isClosedMap.comp hIncl.isClosedMap)
  exact Exists.intro (e.toHomeomorphOfContinuousClosed hCont hClosed) (fun _ => rfl)


section ActualChart

variable {F : Type*} [RCLike F] {n : Nat}

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "G" => Units M

private theorem isClosed_positiveUpperTriangularMatrixSubgroup :
    IsClosed (positiveUpperTriangularMatrixSubgroup F n : Set G) := by
  let T : Set G := Set.iInter (fun i : Fin n => Set.iInter (fun j : Fin n =>
    Set.iInter (fun _ : j < i => Set.ofPred (fun g : G => g.val i j = 0))))
  let D : Set G := Set.iInter (fun i : Fin n => Set.inter
    (Set.ofPred (fun g : G => RCLike.im (g.val i i) = 0))
    (Set.ofPred (fun g : G => 0 <= RCLike.re (g.val i i))))
  have hTMem (g : G) : Membership.mem T g <->
      forall i j : Fin n, j < i -> g.val i j = 0 := by
    constructor
    . intro h i j hij
      exact Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp h i) j) hij
    . intro h
      exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun j =>
        Set.mem_iInter.mpr (fun hlt => h i j hlt)))
  have hDMem (g : G) : Membership.mem D g <->
      forall i : Fin n, And (RCLike.im (g.val i i) = 0) (0 <= RCLike.re (g.val i i)) :=
    Iff.intro (fun h i => Set.mem_iInter.mp h i) (fun h => Set.mem_iInter.mpr h)
  have hEq : (positiveUpperTriangularMatrixSubgroup F n : Set G) = Set.inter T D := by
    ext g
    change And g.val.IsUpperTriangular (forall i, exists x : Real, And (0 < x) (g.val i i = (x : F))) <->
      And (Membership.mem T g) (Membership.mem D g)
    rw [hTMem g, hDMem g]
    constructor
    . intro h
      refine And.intro (fun _ _ hlt => h.1 hlt) ?_
      intro i
      choose x hx using h.2 i
      rw [hx.2, RCLike.ofReal_im, RCLike.ofReal_re]
      exact And.intro rfl hx.1.le
    . intro h
      have ht : g.val.IsUpperTriangular := by
        intro i j hij
        exact h.1 i j hij
      have hDet : Not (g.val.det = 0) :=
        ((Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit).ne_zero
      rw [Matrix.det_of_isUpperTriangular ht] at hDet
      refine And.intro ht ?_
      intro i
      let x : Real := RCLike.re (g.val i i)
      have hx : g.val i i = (x : F) := by
        apply RCLike.ext
        . rw [RCLike.ofReal_re]
        . rw [RCLike.ofReal_im]
          exact (h.2 i).1
      have hg0 : Not (g.val i i = 0) := Finset.prod_ne_zero_iff.mp hDet i (Finset.mem_univ i)
      have hx0 : Not (x = 0) := by
        intro he
        apply hg0
        rw [hx, he, RCLike.ofReal_zero]
      exact Exists.intro x (And.intro (lt_of_le_of_ne (h.2 i).2 (Ne.symm hx0)) hx)
  have hv (i j : Fin n) : Continuous (fun g : G => g.val i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (@Units.continuous_val M _ _))
  have hT : IsClosed T :=
    isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter
      (fun _ => isClosed_eq (hv i j) continuous_const)))
  have hD : IsClosed D :=
    isClosed_iInter (fun i => (isClosed_eq (RCLike.continuous_im.comp (hv i i)) continuous_const).inter
      (isClosed_le continuous_const (RCLike.continuous_re.comp (hv i i))))
  rw [hEq]
  exact hT.inter hD

/-- Multiplication in triangular and inverse-unitary coordinates is a homeomorphism. -/
theorem exists_archimedeanIwasawaHomeomorph
    (F : Type*) [RCLike F] [ProperSpace F] (n : Nat) :
    exists e : Homeomorph
        (Prod (positiveUpperTriangularMatrixSubgroup F n)
          (Matrix.unitaryGroup (Fin n) F))
        (Units (Matrix (Fin n) (Fin n) F)),
      forall p, e p = p.1.val * Unitary.toUnits (Inv.inv p.2) := by
  let T := positiveUpperTriangularMatrixSubgroup F n
  let U := Matrix.unitaryGroup (Fin n) F
  let a : T -> Units (Matrix (Fin n) (Fin n) F) := Subtype.val
  let b : U -> Units (Matrix (Fin n) (Fin n) F) := fun x => Unitary.toUnits x
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp
    (isCompact_archimedeanUnitaryGroup (F := F) (n := n))
  have ha : Topology.IsClosedEmbedding a :=
    (isClosed_positiveUpperTriangularMatrixSubgroup (F := F) (n := n)).isClosedEmbedding_subtypeVal
  have hb : Continuous b := continuous_archimedeanUnitary_toUnits
  have hEq (p : Prod T U) : a p.1 * Inv.inv (b p.2) = p.1.val * Unitary.toUnits (Inv.inv p.2) := by
    unfold a b
    rw [map_inv]
  have hBij : Function.Bijective (fun p : Prod T U => a p.1 * Inv.inv (b p.2)) := by
    rw [funext hEq]
    exact bijective_positiveUpperTriangular_unitary_mul F n
  choose e he using exists_homeomorph_mul_inv_of_closed_left a b ha hb hBij
  exact Exists.intro e (fun p => (he p).trans (hEq p))

end ActualChart


open scoped Pointwise

private theorem measurePreserving_rightMul_of_compactImage
    {U G : Type*} [Group U] [Group G]
    [TopologicalSpace U] [CompactSpace U]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (b : MonoidHom U G) (hb : Continuous b)
    (mu : Measure G) [mu.IsHaarMeasure] [mu.InnerRegular] (u : U) :
    MeasurePreserving (fun x : G => x * b u) mu mu := by
  let C : TopologicalSpace.PositiveCompacts G := Classical.choice inferInstance
  let D : Set G := (C : Set G) * Set.range b
  have hD : IsCompact D := C.isCompact.mul (isCompact_range hb)
  have hDfinite : Not (mu D = Top.top) := hD.measure_ne_top
  have hCpos : 0 < (mu (C : Set G)).toReal := by
    choose x hx using C.interior_nonempty
    have hmu : 0 < mu (C : Set G) :=
      Measure.measure_pos_of_mem_nhds mu (mem_interior_iff_mem_nhds.mp hx)
    exact ENNReal.toReal_pos (ne_of_gt hmu) C.isCompact.measure_ne_top
  let d : MonoidHom U NNReal := Measure.modularCharacter.comp b
  have hBound (v : U) : (d v : Real) * (mu (C : Set G)).toReal <= (mu D).toReal := by
    have hS : Measure.map (fun x : G => x * b v) mu (C : Set G) <= mu D := by
      rw [Measure.map_apply (measurable_mul_const (b v)) C.isCompact.isClosed.measurableSet]
      apply measure_mono
      intro x hx
      have hxc : Membership.mem (C : Set G) (x * b v) := hx
      refine Set.mem_mul.mpr (Exists.intro (x * b v) (And.intro hxc ?_))
      refine Exists.intro (b (Inv.inv v)) (And.intro (Set.mem_range_self _) ?_)
      rw [map_inv, mul_assoc, mul_inv_cancel, mul_one]
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul, Measure.smul_apply] at hS
    change (((d v : NNReal) : ENNReal) * mu (C : Set G)) <= mu D at hS
    have h := ENNReal.toReal_mono hDfinite hS
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal] at h
    exact h
  have hLe (v : U) : (d v : Real) <= 1 := by
    apply le_of_not_gt
    intro hv
    let A := (mu (C : Set G)).toReal
    let B := (mu D).toReal
    choose j hj using pow_unbounded_of_one_lt (B / A) hv
    have hp : (d v : Real) ^ j * A <= B := by
      simpa only [map_pow, NNReal.coe_pow] using hBound (v ^ j)
    have hA : Not (A = 0) := ne_of_gt hCpos
    have he : B / A * A = B := ((div_eq_iff hA).mp (show B / A = B / A from rfl)).symm
    have hlt := mul_lt_mul_of_pos_right hj hCpos
    rw [he] at hlt
    exact (not_le_of_gt hlt) hp
  have hProd : (d u : Real) * (d (Inv.inv u) : Real) = 1 := by
    have h : d u * d (Inv.inv u) = 1 := by
      rw [<- map_mul, mul_inv_cancel, map_one]
    exact_mod_cast h
  have hGe : (1 : Real) <= d u := by
    calc
      _ = (d u : Real) * (d (Inv.inv u) : Real) := hProd.symm
      _ <= (d u : Real) * 1 := mul_le_mul_of_nonneg_left (hLe (Inv.inv u)) (NNReal.coe_nonneg _)
      _ = _ := mul_one _
  have hOne : d u = 1 := Subtype.ext (le_antisymm (hLe u) hGe)
  refine { measurable := measurable_mul_const _, map_eq := ?_ }
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
  change HSMul.hSMul (d u) mu = mu
  rw [hOne, one_smul]


section MatrixHaar

variable (F : Type*) [RCLike F] [ProperSpace F] [SecondCountableTopology F] (n : Nat)

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "G" => Units M
local notation "T" => positiveUpperTriangularMatrixSubgroup F n
local notation "U" => Matrix.unitaryGroup (Fin n) F

/-- Left Haar measure on the matrix units is a positive multiple of the product
of triangular and unitary Haar measures in Iwasawa coordinates. -/
theorem exists_pos_smul_map_archimedeanIwasawaHaar
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace T] [BorelSpace T]
    [MeasurableSpace U] [BorelSpace U]
    (mu : Measure G) [mu.IsHaarMeasure] [mu.InnerRegular]
    (muT : Measure T) (muU : Measure U) [muT.IsHaarMeasure] [muU.IsHaarMeasure]
    [SFinite muT] [SFinite muU] :
    exists e : Homeomorph (Prod T U) G,
      And (forall p, e p = p.1.val * Unitary.toUnits (Inv.inv p.2))
        (exists c : NNReal, And (0 < c)
          (mu = HSMul.hSMul c (Measure.map e (muT.prod muU)))) := by
  let _ : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> F))
  let _ : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (Fin n -> Fin n -> F))
  let op : Homeomorph M (MulOpposite M) := MulOpposite.opHomeomorph
  let _ : SecondCountableTopology (MulOpposite M) := op.symm.isEmbedding.secondCountableTopology
  let _ : LocallyCompactSpace (MulOpposite M) := op.symm.isClosedEmbedding.locallyCompactSpace
  have hG : Topology.IsClosedEmbedding (Units.embedProduct M) := Units.isClosedEmbedding_embedProduct
  let _ : SecondCountableTopology G := hG.isEmbedding.secondCountableTopology
  let _ : LocallyCompactSpace G := hG.locallyCompactSpace
  have hT : Topology.IsClosedEmbedding (fun t : T => t.val) :=
    (isClosed_positiveUpperTriangularMatrixSubgroup (F := F) (n := n)).isClosedEmbedding_subtypeVal
  let _ : SecondCountableTopology T := hT.isEmbedding.secondCountableTopology
  let _ : LocallyCompactSpace T := hT.locallyCompactSpace
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp
    (isCompact_archimedeanUnitaryGroup (F := F) (n := n))
  let a : MonoidHom T G := (positiveUpperTriangularMatrixSubgroup F n).subtype
  let b : MonoidHom U G := Unitary.toUnits
  have hb : Continuous b := continuous_archimedeanUnitary_toUnits
  have hInj : Function.Injective b := by
    intro u v huv
    apply Subtype.ext
    exact congrArg (fun g : G => g.val) huv
  have hU : Topology.IsClosedEmbedding b := hb.isClosedEmbedding hInj
  let _ : SecondCountableTopology U := hU.isEmbedding.secondCountableTopology
  let _ : LocallyCompactSpace U := hU.locallyCompactSpace
  let _ : IsTopologicalGroup U := hU.isEmbedding.isInducing.topologicalGroup b
  choose e he using exists_archimedeanIwasawaHomeomorph F n
  refine Exists.intro e (And.intro he ?_)
  have hE (p : Prod T U) : e p = a p.1 * Inv.inv (b p.2) := by
    rw [he]
    change p.1.val * b (Inv.inv p.2) = p.1.val * Inv.inv (b p.2)
    rw [map_inv]
  have hR (u : U) : MeasurePreserving (fun x : G => x * Inv.inv (b u)) mu mu := by
    rw [<- map_inv]
    exact measurePreserving_rightMul_of_compactImage b hb mu (Inv.inv u)
  exact exists_pos_smul_map_mul_inv_productHaar a b e hE mu hR muT muU

end MatrixHaar

end Robin1984.GRH
