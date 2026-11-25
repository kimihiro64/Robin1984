import Mathlib.MeasureTheory.Measure.WithDensity
import Robin1984.GRH.GodementJacquetMatrixMeasure
import Robin1984.GRH.HeckeFiniteHaarDilation
import Robin1984.GRH.ValuationUnitriangularMeasure

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The normalized additive measure and upper-unitriangular volumes in the unramified local Godement-Jacquet integral.
- Formalization note: Constructs the finite-place additive measure and proves the exact inverse-norm box volume in every rank.
- PROVENANCE-END
-/

/-!
# Additive measure at a finite place and unitriangular volume

Projection from the finite adeles supplies the normalized additive
measure at one place. The scalar dilation formula gives the factor
contributed by each strictly upper entry in the local spherical integral.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

open IsDedekindDomain MeasureTheory NumberField TopologicalSpace
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K]

private abbrev LocalProjectionAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

local notation "Place" => HeightOneSpectrum (RingOfIntegers K)
local notation "A" => LocalProjectionAdeles K

/-- The open additive subgroup of adeles that are integral away from a
single specified finite place. -/
def heckeFiniteLocalSlab (p : Place) : AddSubgroup A where
  carrier := {z | forall q : Place, Not (q = p) ->
    Membership.mem (q.adicCompletionIntegers K) (z q)}
  zero_mem' := fun q _ => (q.adicCompletionIntegers K).zero_mem
  add_mem' := by
    intro z w hz hw q hq
    exact (q.adicCompletionIntegers K).add_mem (z q) (w q) (hz q hq) (hw q hq)
  neg_mem' := by
    intro z hz q hq
    exact (q.adicCompletionIntegers K).neg_mem (z q) (hz q hq)

/-- The additive slab is open since it contains the open integral subgroup. -/
theorem isOpen_heckeFiniteLocalSlab (p : Place) :
    IsOpen (heckeFiniteLocalSlab p : Set A) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  let U := (heckeIntegralFiniteAdeles (K := K) : Set A)
  have hOpen : IsOpen (Set.preimage (fun y : A => y - z) U) :=
    isOpen_heckeIntegralFiniteAdeles.preimage (continuous_id.sub continuous_const)
  have hZ : Membership.mem (Set.preimage (fun y : A => y - z) U) z := by
    change Membership.mem (heckeIntegralFiniteAdeles (K := K)) (z - z)
    rw [sub_self]
    exact (heckeIntegralFiniteAdeles (K := K)).zero_mem
  refine Filter.mem_of_superset (hOpen.mem_nhds hZ) ?_
  intro y hy
  have hSub : Membership.mem (heckeFiniteLocalSlab p) (y - z) :=
    fun q _ => hy q
  change Membership.mem (heckeFiniteLocalSlab p) y
  simpa only [sub_add_cancel] using (heckeFiniteLocalSlab p).add_mem hSub hz

variable [MeasurableSpace (LocalProjectionAdeles K)] [BorelSpace (LocalProjectionAdeles K)]

/-- The local additive measure obtained by giving the integral parts
away from the supported place total mass one. -/
def heckeLocalAdditiveMeasure (p : Place) [MeasurableSpace (p.adicCompletion K)] :
    Measure (p.adicCompletion K) :=
  Measure.map (fun z : A => z p)
    ((heckeFiniteAdeleHaar (K := K)).restrict (heckeFiniteLocalSlab p : Set A))

omit [MeasurableSpace (LocalProjectionAdeles K)] [BorelSpace (LocalProjectionAdeles K)] in
private theorem preimage_localIntegral_mul_inter_slab
    (p : Place) (a : Units (p.adicCompletion K)) :
    Set.inter (Set.preimage (fun z : A => z p)
        {y : p.adicCompletion K | Membership.mem (p.adicCompletionIntegers K) (a.val * y)})
      (heckeFiniteLocalSlab p : Set A) =
      HSMul.hSMul (Inv.inv (heckeFiniteLocalIdele p a))
        (heckeIntegralFiniteAdeles (K := K) : Set A) := by
  let b := heckeFiniteLocalIdele p a
  have hMem (z : A) :
      And (Membership.mem (p.adicCompletionIntegers K) (a.val * z p))
        (Membership.mem (heckeFiniteLocalSlab p) z) <->
      Membership.mem (heckeIntegralFiniteAdeles (K := K)) (b.val * z) := by
    constructor
    case mp =>
      intro hz q
      change Membership.mem (q.adicCompletionIntegers K) (b.val q * z q)
      by_cases hq : q = p
      case pos =>
        subst q
        simpa only [b, heckeFiniteLocalIdele_at] using hz.1
      case neg =>
        rw [show b.val q = 1 from heckeFiniteLocalIdele_away p q hq a, one_mul]
        exact hz.2 q hq
    case mpr =>
      intro h
      refine And.intro ?_ ?_
      next =>
        have hq := h p
        change Membership.mem (p.adicCompletionIntegers K) (b.val p * z p) at hq
        simpa only [b, heckeFiniteLocalIdele_at] using hq
      next =>
        intro q hq
        have hq' := h q
        change Membership.mem (q.adicCompletionIntegers K) (b.val q * z q) at hq'
        rw [show b.val q = 1 from heckeFiniteLocalIdele_away p q hq a, one_mul] at hq'
        exact hq'
  ext z
  change And (Membership.mem (p.adicCompletionIntegers K) (a.val * z p))
      (Membership.mem (heckeFiniteLocalSlab p) z) <->
    exists x : A, And (Membership.mem (heckeIntegralFiniteAdeles (K := K)) x) (b.inv * x = z)
  rw [hMem]
  constructor
  case mp =>
    intro h
    refine Exists.intro (b.val * z) (And.intro h ?_)
    rw [<- mul_assoc, b.inv_val, one_mul]
  case mpr =>
    intro h
    choose x hx using h
    rw [<- hx.2, <- mul_assoc, b.val_inv, one_mul]
    exact hx.1

/-- The local integral ball scaled by the inverse of \(a\) has additive
volume \(|a|^{-1}\) for the normalized absolute value. -/
theorem heckeLocalAdditiveMeasure_scaledIntegral
    (p : Place) [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (a : Units (p.adicCompletion K)) :
    heckeLocalAdditiveMeasure p
      {y : p.adicCompletion K | Membership.mem (p.adicCompletionIntegers K) (a.val * y)} =
      ENNReal.ofReal (Inv.inv (norm a.val)) := by
  let target := {y : p.adicCompletion K | Membership.mem (p.adicCompletionIntegers K) (a.val * y)}
  have hOpen : IsOpen target :=
    (Valued.isOpen_valuationSubring (p.adicCompletion K)).preimage
      (continuous_const.mul continuous_id)
  have hCEval : Continuous (fun z : A => z p) := RestrictedProduct.continuous_eval p
  have hEval : Measurable (fun z : A => z p) := hCEval.measurable
  change Measure.map (fun z : A => z p)
    ((heckeFiniteAdeleHaar (K := K)).restrict (heckeFiniteLocalSlab p : Set A)) target = _
  rw [Measure.map_apply hEval hOpen.measurableSet,
    Measure.restrict_apply (hOpen.measurableSet.preimage hEval)]
  change (heckeFiniteAdeleHaar (K := K))
      (Set.inter (Set.preimage (fun z : A => z p) target) (heckeFiniteLocalSlab p : Set A)) = _
  have hMass := congrArg (fun S : Set A => (heckeFiniteAdeleHaar (K := K)) S)
    (preimage_localIntegral_mul_inter_slab p a)
  change (heckeFiniteAdeleHaar (K := K))
      (Set.inter (Set.preimage (fun z : A => z p) target) (heckeFiniteLocalSlab p : Set A)) = _ at hMass
  refine hMass.trans ?_
  rw [<- heckeFiniteAdditiveModulus_eq_measure, <- map_inv]
  have hNorm := heckeFiniteAdditiveModulus_localIdele_eq_norm p (Inv.inv a)
  rw [show Inv.inv (norm a.val) = norm (Inv.inv a).val from by
    rw [Units.val_inv_eq_inv_val, norm_inv]]
  rw [<- hNorm]
  exact ENNReal.ofReal_coe_nnreal.symm

/-- Addition at a finite place lifts to translation inside the slab, so
the projected measure is additive left invariant. -/
theorem isAddLeftInvariant_heckeLocalAdditiveMeasure
    (p : Place) [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)] :
    (heckeLocalAdditiveMeasure p).IsAddLeftInvariant := by
  classical
  let L := p.adicCompletion K
  let D := heckeFiniteLocalSlab p
  let mu := heckeFiniteAdeleHaar (K := K)
  let _ : LocallyCompactSpace A := locallyCompactSpace_heckeFiniteAdeles
  let _ : mu.IsAddHaarMeasure := by
    dsimp [mu, heckeFiniteAdeleHaar]
    infer_instance
  constructor
  intro t
  let e : A := Subtype.mk (Pi.single p t) (by
    filter_upwards [show Membership.mem Filter.cofinite (Compl.compl (Set.singleton p)) from by
      rw [Filter.mem_cofinite, compl_compl]
      exact Set.finite_singleton p]
      with q hq
    have hne : Not (q = p) := hq
    rw [Pi.single_eq_of_ne hne]
    exact (q.adicCompletionIntegers K).zero_mem)
  have hE : Membership.mem D e := by
    intro q hq
    have hZero : e q = 0 := by
      change Pi.single p t q = 0
      simp [hq]
    rw [hZero]
    exact (q.adicCompletionIntegers K).zero_mem
  have hAt : e p = t := by
    change Pi.single p t p = t
    simp
  have hD : MeasurableSet (D : Set A) := (isOpen_heckeFiniteLocalSlab p).measurableSet
  have hC : Continuous (fun z : A => z p) := RestrictedProduct.continuous_eval p
  have hEval : Measurable (fun z : A => z p) := hC.measurable
  have hLocal : Measurable (fun y : L => t + y) := (continuous_const.add continuous_id).measurable
  have hTranslate : Measurable (fun z : A => e + z) := (continuous_const.add continuous_id).measurable
  have hPre : Set.preimage (fun z : A => e + z) (D : Set A) = D := by
    ext z
    change Membership.mem D (e + z) <-> Membership.mem D z
    constructor
    case mp =>
      intro h
      have hz := D.add_mem (D.neg_mem hE) h
      rwa [<- add_assoc, neg_add_cancel, zero_add] at hz
    case mpr =>
      exact D.add_mem hE
  have hRestrict : (Measure.map (fun z : A => e + z) mu).restrict (D : Set A) =
      Measure.map (fun z : A => e + z)
        (mu.restrict (Set.preimage (fun z : A => e + z) (D : Set A))) :=
    Measure.restrict_map hTranslate hD
  rw [map_add_left_eq_self mu e, hPre] at hRestrict
  have hRel : Function.comp (fun y : L => t + y) (fun z : A => z p) =
      Function.comp (fun z : A => z p) (fun z : A => e + z) := by
    funext z
    change t + z p = e p + z p
    rw [hAt]
  change Measure.map (fun y : L => t + y)
      (Measure.map (fun z : A => z p) (mu.restrict (D : Set A))) =
    Measure.map (fun z : A => z p) (mu.restrict (D : Set A))
  rw [Measure.map_map hLocal hEval, hRel, <- Measure.map_map hEval hTranslate, <- hRestrict]

/-- The local valuation ring has mass one. -/
theorem heckeLocalAdditiveMeasure_integral
    (p : Place) [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)] :
    heckeLocalAdditiveMeasure p (p.adicCompletionIntegers K : Set (p.adicCompletion K)) = 1 := by
  have h := heckeLocalAdditiveMeasure_scaledIntegral p (1 : Units (p.adicCompletion K))
  change heckeLocalAdditiveMeasure p
      {y : p.adicCompletion K | Membership.mem (p.adicCompletionIntegers K) (1 * y)} =
    ENNReal.ofReal (Inv.inv (norm (1 : p.adicCompletion K))) at h
  have hSet : {y : p.adicCompletion K | Membership.mem (p.adicCompletionIntegers K) (1 * y)} =
      (p.adicCompletionIntegers K : Set (p.adicCompletion K)) := by
    ext y
    change Membership.mem (p.adicCompletionIntegers K) (1 * y) <->
      Membership.mem (p.adicCompletionIntegers K) y
    rw [one_mul]
  rw [hSet, norm_one, inv_one, ENNReal.ofReal_one] at h
  exact h

/-- Every point has an open neighborhood of finite local measure. -/
theorem isLocallyFiniteMeasure_heckeLocalAdditiveMeasure
    (p : Place) [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)] :
    IsLocallyFiniteMeasure (heckeLocalAdditiveMeasure p) := by
  let L := p.adicCompletion K
  constructor
  intro x
  have hxBall : exists a : Units L, Membership.mem (p.adicCompletionIntegers K) (a.val * x) := by
    by_cases hx : x = 0
    case pos =>
      refine Exists.intro 1 ?_
      rw [hx, mul_zero]
      exact (p.adicCompletionIntegers K).zero_mem
    case neg =>
      let b := Units.mk0 x hx
      refine Exists.intro (Inv.inv b) ?_
      change Membership.mem (p.adicCompletionIntegers K) (b.inv * b.val)
      rw [b.inv_val]
      exact (p.adicCompletionIntegers K).one_mem
  choose a ha using hxBall
  let S : Set L := {y | Membership.mem (p.adicCompletionIntegers K) (a.val * y)}
  have hOpen : IsOpen S :=
    (Valued.isOpen_valuationSubring L).preimage (continuous_const.mul continuous_id)
  refine Exists.intro S (And.intro (hOpen.mem_nhds ha) ?_)
  have hS : heckeLocalAdditiveMeasure p S = ENNReal.ofReal (Inv.inv (norm a.val)) :=
    heckeLocalAdditiveMeasure_scaledIntegral p a
  rw [hS]
  exact ENNReal.ofReal_lt_top

omit [MeasurableSpace (LocalProjectionAdeles K)] [BorelSpace (LocalProjectionAdeles K)] in
/-- The finite-place topology has a countable basis. -/
theorem secondCountableLocalAdditiveCompletion (p : Place) :
    SecondCountableTopology (p.adicCompletion K) := by
  let _ : Countable K := (Module.finBasis Rat K).equivFun.injective.countable
  let L := p.adicCompletion K
  let V := WithZero (Multiplicative Int)
  let v : Valuation L V := Valued.v
  let G := MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass v)
  let _ : Countable V := inferInstanceAs (Countable (Option Int))
  let _ : Countable (Units V) := Units.val_injective.countable
  let _ : Countable G := (Subtype.val_injective : Function.Injective
    (Subtype.val : G -> Units V)).countable
  let _ : Countable (WithZero G) := inferInstanceAs (Countable (Option G))
  let _ : Countable (Units (WithZero G)) := Units.val_injective.countable
  let _ : (uniformity L).IsCountablyGenerated :=
    (Valued.hasBasis_uniformity L (WithZero (Multiplicative Int))).isCountablyGenerated
  let _ : SeparableSpace L :=
    SeparableSpace.mk (Exists.intro (Set.range (algebraMap K L))
      (And.intro (Set.countable_range _) (p.denseRange_algebraMap K)))
  infer_instance

/-- The normalized local additive measure is sigma finite. -/
theorem sigmaFinite_heckeLocalAdditiveMeasure
    (p : Place) [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)] :
    SigmaFinite (heckeLocalAdditiveMeasure p) := by
  let _ := secondCountableLocalAdditiveCompletion p
  let _ := isLocallyFiniteMeasure_heckeLocalAdditiveMeasure p
  infer_instance

/-- Multiplication by a unit of the completion pushes normalized
additive measure forward to its inverse-norm multiple. -/
theorem map_heckeLocalAdditiveMeasure_mul_unit
    (p : Place) [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (a : Units (p.adicCompletion K)) :
    Measure.map (fun y : p.adicCompletion K => a.val * y) (heckeLocalAdditiveMeasure p) =
      HSMul.hSMul (Real.toNNReal (Inv.inv (norm a.val))) (heckeLocalAdditiveMeasure p) := by
  let L := p.adicCompletion K
  let D := heckeFiniteLocalSlab p
  let mu := heckeFiniteAdeleHaar (K := K)
  let b := heckeFiniteLocalIdele p a
  let c := heckeFiniteAdditiveModulus (Inv.inv b)
  let : LocallyCompactSpace A := locallyCompactSpace_heckeFiniteAdeles
  let : mu.IsAddHaarMeasure := by
    unfold mu heckeFiniteAdeleHaar
    infer_instance
  let : mu.Regular := by
    unfold mu heckeFiniteAdeleHaar
    infer_instance
  have hD : MeasurableSet (D : Set A) := (isOpen_heckeFiniteLocalSlab p).measurableSet
  have hCEval : Continuous (fun z : A => z p) := RestrictedProduct.continuous_eval p
  have hEval : Measurable (fun z : A => z p) := hCEval.measurable
  have hLocal : Measurable (fun y : L => a.val * y) := (continuous_const.mul continuous_id).measurable
  have hGlobal : Measurable (fun z : A => b.val * z) := (continuous_const.mul continuous_id).measurable
  have hPre : Set.preimage (fun z : A => b.val * z) (D : Set A) = D := by
    ext z
    change Membership.mem D (b.val * z) <-> Membership.mem D z
    constructor
    . intro hz q hq
      have hm := hz q hq
      change Membership.mem (q.adicCompletionIntegers K) (b.val q * z q) at hm
      rwa [show b.val q = 1 from heckeFiniteLocalIdele_away p q hq a, one_mul] at hm
    . intro hz q hq
      change Membership.mem (q.adicCompletionIntegers K) (b.val q * z q)
      rw [show b.val q = 1 from heckeFiniteLocalIdele_away p q hq a, one_mul]
      exact hz q hq
  have hRel : Function.comp (fun y : L => a.val * y) (fun z : A => z p) =
      Function.comp (fun z : A => z p) (fun z : A => b.val * z) := by
    funext z
    change a.val * z p = b.val p * z p
    rw [show b.val p = a.val from heckeFiniteLocalIdele_at p a]
  have hScale : Measure.map (fun z : A => b.val * z) mu = HSMul.hSMul c mu :=
    map_finiteAdele_mul_unit_additiveHaar mu b
  have hRestrict : (Measure.map (fun z : A => b.val * z) mu).restrict (D : Set A) =
      Measure.map (fun z : A => b.val * z)
        (mu.restrict (Set.preimage (fun z : A => b.val * z) (D : Set A))) :=
    Measure.restrict_map hGlobal hD
  rw [hScale, Measure.restrict_smul, hPre] at hRestrict
  have hNorm : c = Real.toNNReal (Inv.inv (norm a.val)) := by
    change heckeFiniteAdditiveModulus (Inv.inv b) = _
    rw [show Inv.inv b = heckeFiniteLocalIdele p (Inv.inv a) from (map_inv (heckeFiniteLocalIdele p) a).symm]
    have h := heckeFiniteAdditiveModulus_localIdele_eq_norm p (Inv.inv a)
    rw [Units.val_inv_eq_inv_val, norm_inv] at h
    rw [<- h]
    exact Real.toNNReal_coe.symm
  change Measure.map (fun y : L => a.val * y)
      (Measure.map (fun z : A => z p) (mu.restrict (D : Set A))) =
    HSMul.hSMul (Real.toNNReal (Inv.inv (norm a.val)))
      (Measure.map (fun z : A => z p) (mu.restrict (D : Set A)))
  rw [Measure.map_map hLocal hEval, hRel, <- Measure.map_map hEval hGlobal, <- hRestrict,
    Measure.map_smul, hNorm]

/-- The inverse normalized local absolute value as a multiplier. -/
def heckeLocalInverseNorm (p : Place) : MonoidHom (p.adicCompletion K) NNReal where
  toFun x := Real.toNNReal (Inv.inv (norm x))
  map_one' := by simp
  map_mul' := by
    intro x y
    change Real.toNNReal (Inv.inv (norm (x * y))) =
      Real.toNNReal (Inv.inv (norm x)) * Real.toNNReal (Inv.inv (norm y))
    rw [norm_mul, show Inv.inv (norm x * norm y) = Inv.inv (norm x) * Inv.inv (norm y) from by
      simp only [<- one_div, div_mul_div_comm, one_mul]]
    exact Real.toNNReal_mul (inv_nonneg.mpr (norm_nonneg x))

/-- An invertible matrix on a finite vector space over the completion
scales product additive measure by the inverse norm of its determinant. -/
theorem map_heckeLocalAdditiveMeasure_mulVec_det
    (p : Place) [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (p.adicCompletion K)) (hM : IsUnit M) :
    Measure.map M.mulVec (Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p)) =
      HSMul.hSMul (heckeLocalInverseNorm p M.det)
        (Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p)) := by
  let L := p.adicCompletion K
  let mu := heckeLocalAdditiveMeasure p
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let : SigmaFinite mu := sigmaFinite_heckeLocalAdditiveMeasure p
  let : mu.IsAddLeftInvariant := isAddLeftInvariant_heckeLocalAdditiveMeasure p
  have hadd : Measurable (fun q : Prod L L => q.1 + q.2) :=
    (continuous_fst.add continuous_snd).measurable
  have hmul (a : L) : Measurable (fun y : L => a * y) :=
    (continuous_const.mul continuous_id).measurable
  exact map_localRing_matrix_mulVec_det mu (heckeLocalInverseNorm p) hadd hmul
    (map_heckeLocalAdditiveMeasure_mul_unit p) M hM

private theorem heckeMatrixProduct_smul_const {J E : Type*} [Fintype J] [MeasurableSpace E]
    (mu : Measure E) [SigmaFinite mu] (c : NNReal) :
    Measure.pi (fun _ : J => HSMul.hSMul c mu) =
      HSMul.hSMul (c ^ Fintype.card J) (Measure.pi (fun _ : J => mu)) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply]
  change ((c ^ Fintype.card J : NNReal) : ENNReal) *
      (Finset.univ.prod fun j => mu (s j)) =
    Finset.univ.prod (fun j => (c : ENNReal) * mu (s j))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

private def heckeLocalRightMatrix (p : Place)
    {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I (p.adicCompletion K))
    (X : I -> I -> p.adicCompletion K) : I -> I -> p.adicCompletion K :=
  @Mul.mul (Matrix I I (p.adicCompletion K)) inferInstance (Matrix.of X) M

omit [MeasurableSpace (LocalProjectionAdeles K)] [BorelSpace (LocalProjectionAdeles K)] in
private theorem measurable_heckeLocalMatrixTranspose_mulVec (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] (M : Matrix I I (p.adicCompletion K)) :
    Measurable M.transpose.mulVec := by
  let L := p.adicCompletion K
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  refine measurable_pi_lambda _ (fun i => ?_)
  change Measurable (fun y : I -> L => Finset.univ.sum (fun j => M.transpose i j * y j))
  have hc : Continuous (fun y : I -> L => Finset.univ.sum (fun j => M.transpose i j * y j)) :=
    continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j))
  exact hc.measurable

omit [MeasurableSpace (LocalProjectionAdeles K)] [BorelSpace (LocalProjectionAdeles K)] in
private theorem heckeLocalRightMatrix_rows (p : Place)
    {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I (p.adicCompletion K)) :
    heckeLocalRightMatrix p M =
      (fun X : I -> I -> p.adicCompletion K => fun i => M.transpose.mulVec (X i)) := by
  funext X i j
  change ((Matrix.of X) * M) i j = M.transpose.mulVec (X i) j
  rw [Matrix.mul_apply]
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro k _
  change X i k * M k j = M k j * X i k
  exact mul_comm _ _

omit [MeasurableSpace (LocalProjectionAdeles K)] [BorelSpace (LocalProjectionAdeles K)] in
private theorem measurable_heckeLocalRightMatrix (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I (p.adicCompletion K)) :
    Measurable (heckeLocalRightMatrix p M) := by
  rw [heckeLocalRightMatrix_rows]
  exact measurable_pi_lambda _ (fun i =>
    (measurable_heckeLocalMatrixTranspose_mulVec p M).comp (measurable_pi_apply i))

/-- Right multiplication by an invertible matrix scales the product
additive measure on its row coordinates by one inverse determinant norm
per row. -/
theorem map_heckeLocalAdditiveMeasure_matrix_mul_right
    (p : Place) [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (p.adicCompletion K)) (hM : IsUnit M) :
    @Measure.map (I -> I -> p.adicCompletion K) (I -> I -> p.adicCompletion K) _ _
      (fun X => @Mul.mul (Matrix I I (p.adicCompletion K)) inferInstance (Matrix.of X) M)
      (Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))) =
    HSMul.hSMul (heckeLocalInverseNorm p M.det ^ Fintype.card I)
      (Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))) := by
  let L := p.adicCompletion K
  let mu := heckeLocalAdditiveMeasure p
  let nu := Measure.pi (fun _ : I => mu)
  let : SigmaFinite mu := sigmaFinite_heckeLocalAdditiveMeasure p
  have hMT : IsUnit M.transpose := by
    apply (Matrix.isUnit_iff_isUnit_det M.transpose).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det M).mp hM
  have hscale : Measure.map M.transpose.mulVec nu =
      HSMul.hSMul (heckeLocalInverseNorm p M.det) nu := by
    simpa only [Matrix.det_transpose] using map_heckeLocalAdditiveMeasure_mulVec_det p M.transpose hMT
  have hmeas := measurable_heckeLocalMatrixTranspose_mulVec p M
  let : SigmaFinite (Measure.map M.transpose.mulVec nu) := by
    rw [hscale]
    infer_instance
  change Measure.map (heckeLocalRightMatrix p M)
      (Measure.pi (fun _ : I => nu)) = _
  rw [heckeLocalRightMatrix_rows]
  change Measure.map (fun X : I -> I -> L => fun i => M.transpose.mulVec (X i))
      (Measure.pi (fun _ : I => nu)) = _
  rw [Measure.pi_map_pi (fun _ => hmeas.aemeasurable)]
  simp only [hscale]
  exact heckeMatrixProduct_smul_const nu (heckeLocalInverseNorm p M.det)

private theorem map_withDensity_eq_of_scaling
    {E : Type*} [MeasurableSpace E] (e : MeasurableEquiv E E)
    (mu : Measure E) (w : E -> ENNReal) (a : NNReal)
    (hMap : Measure.map e mu = HSMul.hSMul (a : ENNReal) mu)
    (hWeight : forall x : E, w (e x) = (a : ENNReal) * w x) :
    Measure.map e (mu.withDensity w) = mu.withDensity w := by
  let wInv := Function.comp w e.symm
  have hPush : Measure.map e (mu.withDensity w) =
      (Measure.map e mu).withDensity wInv := by
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
      withDensity_apply _ hs, Measure.restrict_map e.measurable hs, lintegral_map_equiv]
    simp only [wInv, Function.comp_apply, e.symm_apply_apply]
  have hDensity : HSMul.hSMul (a : ENNReal) wInv = w := by
    funext x
    change (a : ENNReal) * w (e.symm x) = w x
    simpa only [e.apply_symm_apply] using (hWeight (e.symm x)).symm
  rw [hPush, hMap, withDensity_smul_measure, <- withDensity_smul' (a : ENNReal) wInv ENNReal.coe_ne_top, hDensity]

private def heckeLocalRightMatrixEquiv (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    (m : Units (Matrix I I (p.adicCompletion K))) :
    MeasurableEquiv (I -> I -> p.adicCompletion K) (I -> I -> p.adicCompletion K) where
  toFun := heckeLocalRightMatrix p m.val
  invFun := heckeLocalRightMatrix p m.inv
  left_inv := fun X => by
    change (Matrix.of X * m.val) * m.inv = Matrix.of X
    rw [mul_assoc, m.val_inv, mul_one]
  right_inv := fun X => by
    change (Matrix.of X * m.inv) * m.val = Matrix.of X
    rw [mul_assoc, m.inv_val, mul_one]
  measurable_toFun := measurable_heckeLocalRightMatrix p m.val
  measurable_invFun := measurable_heckeLocalRightMatrix p m.inv

/-- The determinant weight on a matrix, equal to the inverse determinant
norm raised to the number of rows when the matrix is invertible. -/
def heckeLocalMatrixDeterminantWeight (p : Place)
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : I -> I -> p.adicCompletion K) : ENNReal :=
  ((heckeLocalInverseNorm p (Matrix.of X).det ^ Fintype.card I : NNReal) : ENNReal)

/-- The determinant-weighted additive measure on local matrix coordinates. -/
def heckeLocalDeterminantWeightedMeasure (p : Place) (I : Type*)
    [Fintype I] [DecidableEq I] [MeasurableSpace (p.adicCompletion K)] :
    Measure (I -> I -> p.adicCompletion K) :=
  (Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))).withDensity
    (heckeLocalMatrixDeterminantWeight p)

/-- Right multiplication by an invertible matrix preserves the
determinant-weighted additive measure on local matrix coordinates. -/
theorem map_heckeLocalDeterminantWeightedMeasure_mul_right (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    (m : Units (Matrix I I (p.adicCompletion K))) :
    Measure.map (heckeLocalRightMatrix p m.val) (heckeLocalDeterminantWeightedMeasure p I) =
      heckeLocalDeterminantWeightedMeasure p I := by
  let mu := Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))
  let e := heckeLocalRightMatrixEquiv p m
  let c := heckeLocalInverseNorm p m.val.det ^ Fintype.card I
  change Measure.map e (mu.withDensity (heckeLocalMatrixDeterminantWeight p)) =
    mu.withDensity (heckeLocalMatrixDeterminantWeight p)
  apply map_withDensity_eq_of_scaling e mu (heckeLocalMatrixDeterminantWeight p) c
  . exact map_heckeLocalAdditiveMeasure_matrix_mul_right p m.val m.isUnit
  . intro X
    have hd : (Matrix.of (e X)).det = (Matrix.of X).det * m.val.det := by
      change (Matrix.of X * m.val).det = _
      exact Matrix.det_mul _ _
    unfold heckeLocalMatrixDeterminantWeight
    rw [hd, map_mul, mul_pow, ENNReal.coe_mul, mul_comm]

private theorem map_matrixTranspose_pi
    {I E : Type*} [Fintype I] [MeasurableSpace E] (mu : Measure E) [SigmaFinite mu] :
    Measure.map (fun X : I -> I -> E => fun i j => X j i)
      (Measure.pi (fun _ : I => Measure.pi (fun _ : I => mu))) =
      Measure.pi (fun _ : I => Measure.pi (fun _ : I => mu)) := by
  let nu := Measure.pi (fun _ : I => Measure.pi (fun _ : I => mu))
  let omega := Measure.pi (fun _ : Prod I I => mu)
  let encode (X : I -> I -> E) (p : Prod I I) := X p.1 p.2
  let decode (x : Prod I I -> E) (i j : I) := x (Prod.mk i j)
  let e := Equiv.prodComm I I
  let swap := MeasurableEquiv.piCongrLeft (fun _ : Prod I I => E) e
  have hmEncode : Measurable encode :=
    measurable_pi_lambda _ (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  have hmDecode : Measurable decode :=
    measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => measurable_pi_apply (Prod.mk i j)))
  have hEncode : Measure.map encode nu = omega := by
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply hmEncode (MeasurableSet.pi Set.countable_univ (fun p _ => hs p))]
    have hPre : Set.preimage encode (Set.pi Set.univ s) =
        Set.pi Set.univ (fun i : I => Set.pi Set.univ (fun j : I => s (Prod.mk i j))) := by
      ext X
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, encode]
      exact Iff.intro (fun h i j => h (Prod.mk i j)) (fun h p => h p.1 p.2)
    rw [hPre]
    change Measure.pi (fun _ : I => Measure.pi (fun _ : I => mu)) _ = _
    simp only [Measure.pi_pi]
    exact (Fintype.prod_prod_type (fun p : Prod I I => mu (s p))).symm
  have hDecode : Measure.map decode omega = nu := by
    rw [<- hEncode, Measure.map_map hmDecode hmEncode]
    have hId : Function.comp decode encode = id := rfl
    rw [hId, Measure.map_id]
  have hSwap : MeasurePreserving swap omega omega := measurePreserving_piCongrLeft (fun _ => mu) e
  have hTranspose : Function.comp decode (Function.comp swap encode) =
      (fun X : I -> I -> E => fun i j => X j i) := by
    funext X i j
    change swap (encode X) (e (Prod.mk j i)) = encode X (Prod.mk j i)
    exact @MeasurableEquiv.piCongrLeft_apply_apply (Prod I I) (Prod I I) e (fun _ => E)
      (fun _ => inferInstance) (encode X) (Prod.mk j i)
  change Measure.map (fun X : I -> I -> E => fun i j => X j i) nu = nu
  rw [<- hTranspose, <- Measure.map_map hmDecode (swap.measurable.comp hmEncode),
    <- Measure.map_map swap.measurable hmEncode, hEncode, hSwap.map_eq, hDecode]


private def matrixTransposeCoordinatesEquiv {I E : Type*} [MeasurableSpace E] :
    MeasurableEquiv (I -> I -> E) (I -> I -> E) := by
  let flip (X : I -> I -> E) (i j : I) := X j i
  have hf : Measurable flip :=
    measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply i).comp (measurable_pi_apply j)))
  exact
    { toFun := flip
      invFun := flip
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      measurable_toFun := hf
      measurable_invFun := hf }

private theorem map_heckeLocalDeterminantWeightedMeasure_transpose (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I] :
    Measure.map (matrixTransposeCoordinatesEquiv (I := I) (E := p.adicCompletion K))
        (heckeLocalDeterminantWeightedMeasure p I) =
      heckeLocalDeterminantWeightedMeasure p I := by
  let mu := heckeLocalAdditiveMeasure p
  let : SigmaFinite mu := by
    exact sigmaFinite_heckeLocalAdditiveMeasure p
  let e := matrixTransposeCoordinatesEquiv (I := I) (E := p.adicCompletion K)
  unfold heckeLocalDeterminantWeightedMeasure
  apply map_withDensity_eq_of_scaling e _ (heckeLocalMatrixDeterminantWeight p) 1
  . rw [ENNReal.coe_one, one_smul]
    exact map_matrixTranspose_pi mu
  . intro X
    rw [ENNReal.coe_one, one_mul]
    have hTrans : Matrix.of (e X) = (Matrix.of X).transpose := rfl
    unfold heckeLocalMatrixDeterminantWeight
    rw [hTrans, Matrix.det_transpose]

/-- Left multiplication by an invertible matrix preserves the
determinant-weighted additive measure on local matrix coordinates. -/
theorem map_heckeLocalDeterminantWeightedMeasure_mul_left (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    (m : Units (Matrix I I (p.adicCompletion K))) :
    @Measure.map (I -> I -> p.adicCompletion K) (I -> I -> p.adicCompletion K) _ _
      (fun X => @Mul.mul (Matrix I I (p.adicCompletion K)) inferInstance m.val (Matrix.of X))
      (heckeLocalDeterminantWeightedMeasure p I) =
      heckeLocalDeterminantWeightedMeasure p I := by
  let L := p.adicCompletion K
  let mt : Units (Matrix I I L) :=
    { val := m.val.transpose
      inv := m.inv.transpose
      val_inv := by rw [<- Matrix.transpose_mul, m.inv_val, Matrix.transpose_one]
      inv_val := by rw [<- Matrix.transpose_mul, m.val_inv, Matrix.transpose_one] }
  let e := matrixTransposeCoordinatesEquiv (I := I) (E := L)
  let right := heckeLocalRightMatrix p mt.val
  let left (X : I -> I -> L) : I -> I -> L :=
    @Mul.mul (Matrix I I L) inferInstance m.val (Matrix.of X)
  let nu := heckeLocalDeterminantWeightedMeasure p I
  have hRight : Measurable right := measurable_heckeLocalRightMatrix p mt.val
  have hComp : Function.comp e (Function.comp right e) = left := by
    funext X i j
    change (Matrix.of (fun i j => X j i) * m.val.transpose) j i =
      (m.val * Matrix.of X) i j
    have hTrans : Matrix.of (fun i j => X j i) = (Matrix.of X).transpose := rfl
    rw [hTrans, <- Matrix.transpose_mul]
    rfl
  have hT : Measure.map e nu = nu := map_heckeLocalDeterminantWeightedMeasure_transpose p
  have hR : Measure.map right nu = nu := map_heckeLocalDeterminantWeightedMeasure_mul_right p mt
  change Measure.map left nu = nu
  calc
    Measure.map left nu = Measure.map e (Measure.map right (Measure.map e nu)) := by
      rw [Measure.map_map hRight e.measurable,
        Measure.map_map e.measurable (hRight.comp e.measurable), hComp]
    _ = nu := by rw [hT, hR, hT]

/-- Singular matrices have zero determinant-weighted measure. -/
theorem heckeLocalDeterminantWeightedMeasure_singular (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I] :
    heckeLocalDeterminantWeightedMeasure p I
      {X : I -> I -> p.adicCompletion K | (Matrix.of X).det = 0} = 0 := by
  let L := p.adicCompletion K
  let S := {X : I -> I -> L | (Matrix.of X).det = 0}
  let mu := Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  have hMatrix : Continuous (fun X : I -> I -> L => Matrix.of X) :=
    continuous_matrixOf.mpr continuous_id
  have hC : Continuous (fun X : I -> I -> L => (Matrix.of X).det) := hMatrix.matrix_det
  have hS : MeasurableSet S := (isClosed_eq hC continuous_const).measurableSet
  change (mu.withDensity (heckeLocalMatrixDeterminantWeight p)) S = 0
  rw [withDensity_apply _ hS]
  have hZero : Filter.EventuallyEq (ae (mu.restrict S))
      (heckeLocalMatrixDeterminantWeight p) (fun _ : I -> I -> L => (0 : ENNReal)) := by
    filter_upwards [ae_restrict_mem hS] with X hX
    change (Matrix.of X).det = 0 at hX
    have hDim : Not (Fintype.card I = 0) := by
      intro h
      let : IsEmpty I := Fintype.card_eq_zero_iff.mp h
      rw [Matrix.det_isEmpty] at hX
      exact one_ne_zero hX
    change ((Real.toNNReal (Inv.inv (norm (Matrix.of X).det)) ^ Fintype.card I : NNReal) :
      ENNReal) = 0
    rw [hX, norm_zero, inv_zero, Real.toNNReal_zero, zero_pow hDim, ENNReal.coe_zero]
  rw [lintegral_congr_ae hZero, lintegral_zero]

/-- On measurable sets of unit determinant norm, the determinant-weighted
measure is the normalized product additive measure. -/
theorem heckeLocalDeterminantWeightedMeasure_apply_of_detNorm_one (p : Place)
    [MeasurableSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Set (I -> I -> p.adicCompletion K)) (hS : MeasurableSet S)
    (hDet : forall X, Membership.mem S X -> norm (Matrix.of X).det = 1) :
    heckeLocalDeterminantWeightedMeasure p I S =
      (Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))) S := by
  let mu := Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))
  rw [heckeLocalDeterminantWeightedMeasure, withDensity_apply _ hS]
  change lintegral (mu.restrict S) (heckeLocalMatrixDeterminantWeight p) = mu S
  have hOne : Filter.EventuallyEq (ae (mu.restrict S)) (heckeLocalMatrixDeterminantWeight p)
      (fun _ : I -> I -> p.adicCompletion K => (1 : ENNReal)) := by
    filter_upwards [ae_restrict_mem hS] with X hX
    change ((Real.toNNReal (Inv.inv (norm (Matrix.of X).det)) ^ Fintype.card I : NNReal) :
      ENNReal) = 1
    rw [hDet X hX, inv_one, Real.toNNReal_one, one_pow, ENNReal.coe_one]
  rw [lintegral_congr_ae hOne, lintegral_const, Measure.restrict_apply_univ, one_mul]

/-- The normalized standard local measure gives one inverse norm for
each scaled entry strictly above the diagonal of a unitriangular matrix. -/
theorem measure_heckeLocalUnitriangular_scaledIntegral
    (p : Place) [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (n : Nat) (a : Units (Fin n -> p.adicCompletion K)) :
    valuationUnitriangularProductMeasure (p.adicCompletion K) (heckeLocalAdditiveMeasure p) n
      {u : valuationUpperUnitriangularSubgroup (p.adicCompletion K) n |
        forall i j : Fin n, i < j ->
          Membership.mem (p.adicCompletionIntegers K) (a.val i * u.val.val.val i j)} =
      Finset.univ.prod (fun i : Fin n =>
        (ENNReal.ofReal (Inv.inv (norm (a.val i)))) ^ (n - (i.val + 1))) := by
  let L := p.adicCompletion K
  let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
  let _ := secondCountableLocalAdditiveCompletion p
  let _ := sigmaFinite_heckeLocalAdditiveMeasure p
  change valuationUnitriangularProductMeasure L (heckeLocalAdditiveMeasure p) n
      {u : valuationUpperUnitriangularSubgroup L n |
        forall i j : Fin n, i < j ->
          Membership.mem v.integer (a.val i * u.val.val.val i j)} = _
  rw [measure_valuationUnitriangularProduct_scaledIntegral L v (heckeLocalAdditiveMeasure p) n a.val]
  refine Finset.prod_congr rfl ?_
  intro i _
  let ai : Units L :=
    { val := a.val i
      inv := a.inv i
      val_inv := congrArg (fun f : Fin n -> L => f i) a.val_inv
      inv_val := congrArg (fun f : Fin n -> L => f i) a.inv_val }
  exact congrArg (fun c : ENNReal => c ^ (n - (i.val + 1)))
    (heckeLocalAdditiveMeasure_scaledIntegral p ai)

end Robin1984.GRH
