import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Group.Units
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

section LocalMatrixGroupMeasure

open Topology

/-- The row coordinates of an invertible matrix. -/
def heckeLocalMatrixUnitEntries {I F : Type*} [Fintype I] [DecidableEq I] [Semiring F]
    (g : Units (Matrix I I F)) : I -> I -> F :=
  fun i j => g.val i j

private theorem isOpenEmbedding_heckeLocalMatrixUnitEntries
    {I F : Type*} [Fintype I] [DecidableEq I] [NormedField F] :
    IsOpenEmbedding (heckeLocalMatrixUnitEntries (I := I) (F := F)) := by
  let M := Matrix I I F
  let G := Units M
  let D : Set (I -> I -> F) := {X | Not ((Matrix.of X).det = 0)}
  have hMatrix : Continuous (fun X : I -> I -> F => Matrix.of X) :=
    continuous_matrixOf.mpr continuous_id
  have hD : IsOpen D := isOpen_ne_fun hMatrix.matrix_det continuous_const
  let encode (g : G) : D := Subtype.mk (heckeLocalMatrixUnitEntries g)
    (g.isUnit.map Matrix.detMonoidHom).ne_zero
  let decode (X : D) : G := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of X.val) X.property
  have hEntries : Continuous (heckeLocalMatrixUnitEntries (I := I) (F := F)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have hVal0 : Continuous (fun g : G => g.val) := Units.continuous_val
    have hEval : Continuous (fun M0 : M => M0 i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact hEval.comp hVal0
  have hEncode : Continuous encode := hEntries.subtype_mk (fun g => (encode g).property)
  have hVal : Continuous (fun X : D => Matrix.of X.val) := hMatrix.comp continuous_subtype_val
  have hDecode : Continuous decode := by
    apply Units.continuous_iff.mpr
    refine And.intro hVal ?_
    have hEq (X : D) : (Inv.inv (decode X)).val = Inv.inv (Matrix.of X.val) :=
      Matrix.coe_units_inv (decode X)
    simp only [hEq]
    rw [continuous_iff_continuousAt]
    intro X
    have hInv : ContinuousAt (Ring.inverse : F -> F) (Matrix.of X.val).det := by
      rw [show (Ring.inverse : F -> F) = Inv.inv from funext Ring.inverse_eq_inv]
      fun_prop (disch := exact X.property)
    have hAt : ContinuousAt (fun Y : D => Matrix.of Y.val) X := hVal.continuousAt
    have hMatrixInv : ContinuousAt (Inv.inv : M -> M) (Matrix.of X.val) :=
      continuousAt_matrix_inv _ hInv
    exact hMatrixInv.comp (f := fun Y : D => Matrix.of Y.val) (x := X) hAt
  let e : Homeomorph G D :=
    { toFun := encode
      invFun := decode
      left_inv := fun g => Units.ext rfl
      right_inv := fun X => Subtype.ext rfl
      continuous_toFun := hEncode
      continuous_invFun := hDecode }
  exact hD.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding

/-- Pullback of the determinant-weighted measure to invertible matrices. -/
def heckeLocalMatrixUnitWeightedMeasure (p : Place) (I : Type*) [Fintype I] [DecidableEq I]
    [MeasurableSpace (p.adicCompletion K)]
    [MeasurableSpace (Units (Matrix I I (p.adicCompletion K)))] :
    Measure (Units (Matrix I I (p.adicCompletion K))) :=
  Measure.comap heckeLocalMatrixUnitEntries (heckeLocalDeterminantWeightedMeasure p I)

/-- Pushing the pullback forward recovers the determinant-weighted measure. -/
theorem map_heckeLocalMatrixUnitWeightedMeasure (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Units (Matrix I I (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix I I (p.adicCompletion K)))] :
    Measure.map heckeLocalMatrixUnitEntries (heckeLocalMatrixUnitWeightedMeasure p I) =
      heckeLocalDeterminantWeightedMeasure p I := by
  let L := p.adicCompletion K
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let G := Units (Matrix I I L)
  let e : G -> I -> I -> L := heckeLocalMatrixUnitEntries
  let nu := heckeLocalDeterminantWeightedMeasure p I
  have hE : MeasurableEmbedding e := isOpenEmbedding_heckeLocalMatrixUnitEntries.measurableEmbedding
  have hRange : Set.range e = {X : I -> I -> L | Not ((Matrix.of X).det = 0)} := by
    ext X
    constructor
    . intro hX
      change exists g : G, e g = X at hX
      choose g hg using hX
      rw [<- hg]
      exact (g.isUnit.map Matrix.detMonoidHom).ne_zero
    . intro hX
      exact Exists.intro (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of X) hX) rfl
  change Measure.map e (Measure.comap e nu) = nu
  rw [hE.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  apply ae_iff.mpr
  have hS : {X | Not (Membership.mem (Set.range e) X)} =
      {X : I -> I -> L | (Matrix.of X).det = 0} := by
    ext X
    rw [hRange]
    exact not_not
  rw [hS]
  exact heckeLocalDeterminantWeightedMeasure_singular p

/-- The pulled-back measure is invariant under left translation. -/
theorem isMulLeftInvariant_heckeLocalMatrixUnitWeightedMeasure (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Units (Matrix I I (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix I I (p.adicCompletion K)))] :
    (heckeLocalMatrixUnitWeightedMeasure p I).IsMulLeftInvariant := by
  let L := p.adicCompletion K
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let G := Units (Matrix I I L)
  let e : G -> I -> I -> L := heckeLocalMatrixUnitEntries
  let nu := heckeLocalDeterminantWeightedMeasure p I
  let mu := heckeLocalMatrixUnitWeightedMeasure p I
  have hE : MeasurableEmbedding e := isOpenEmbedding_heckeLocalMatrixUnitEntries.measurableEmbedding
  have hMap : Measure.map e mu = nu := map_heckeLocalMatrixUnitWeightedMeasure p
  constructor
  intro m
  let f (X : I -> I -> L) : I -> I -> L :=
    @Mul.mul (Matrix I I L) inferInstance m.val (Matrix.of X)
  have hm : Measurable (fun g : G => m * g) := (continuous_const.mul continuous_id).measurable
  have hf : Measurable f := by
    have hMat : Continuous (fun X : I -> I -> L => Matrix.of X) :=
      continuous_matrixOf.mpr continuous_id
    have hMul : Continuous (fun X : I -> I -> L => m.val * Matrix.of X) :=
      continuous_const.mul hMat
    exact (continuous_pi (fun i => continuous_pi (fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp hMul)))).measurable
  have hRel : Function.comp e (fun g : G => m * g) = Function.comp f e := by
    funext g
    rfl
  apply hE.map_injective
  change Measure.map e (Measure.map (fun g : G => m * g) mu) = Measure.map e mu
  rw [Measure.map_map hE.measurable hm, hRel, <- Measure.map_map hf hE.measurable, hMap]
  exact map_heckeLocalDeterminantWeightedMeasure_mul_left p m

/-- The pulled-back measure is finite in a neighborhood of each matrix unit. -/
theorem isLocallyFiniteMeasure_heckeLocalMatrixUnitWeightedMeasure (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Units (Matrix I I (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix I I (p.adicCompletion K)))] :
    IsLocallyFiniteMeasure (heckeLocalMatrixUnitWeightedMeasure p I) := by
  let L := p.adicCompletion K
  let G := Units (Matrix I I L)
  let e : G -> I -> I -> L := heckeLocalMatrixUnitEntries
  let mu := heckeLocalAdditiveMeasure p
  let base := Measure.pi (fun _ : I => Measure.pi (fun _ : I => mu))
  let nu := heckeLocalMatrixUnitWeightedMeasure p I
  let weight := heckeLocalMatrixDeterminantWeight (I := I) p
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let : SigmaFinite mu := sigmaFinite_heckeLocalAdditiveMeasure p
  let : IsLocallyFiniteMeasure mu := isLocallyFiniteMeasure_heckeLocalAdditiveMeasure p
  let : IsLocallyFiniteMeasure base := inferInstance
  have he : IsOpenEmbedding e := isOpenEmbedding_heckeLocalMatrixUnitEntries
  have hE : MeasurableEmbedding e := he.measurableEmbedding
  let w (g : G) : NNReal := heckeLocalInverseNorm p g.val.det ^ Fintype.card I
  have hVal : Continuous (fun g : G => g.val) := Units.continuous_val
  have hInv : Continuous (fun g : G => Inv.inv (norm g.val.det)) := by
    have hNorm : Continuous (fun g : G => norm g.val.det) := hVal.matrix_det.norm
    rw [continuous_iff_continuousAt]
    intro g
    have hNormNeZero : Not (norm g.val.det = 0) := norm_ne_zero_iff.mpr
      (g.isUnit.map Matrix.detMonoidHom).ne_zero
    have hRe : ContinuousAt (Inv.inv : Real -> Real) (norm g.val.det) := by
      fun_prop (disch := exact hNormNeZero)
    exact hRe.comp (f := fun y : G => norm y.val.det) (x := g) hNorm.continuousAt
  have hToNNReal : Continuous Real.toNNReal :=
    (continuous_id.max continuous_const).subtype_mk (fun y : Real => le_max_right y 0)
  have hW : Continuous w := (hToNNReal.comp hInv).pow _
  constructor
  intro g
  choose U hU using base.exists_isOpen_measure_lt_top (e g)
  let B := w g + 1
  let V := Set.inter {x : G | w x < B} (Set.preimage e U)
  have hV : IsOpen V := (isOpen_lt hW continuous_const).inter (hU.2.1.preimage he.continuous)
  have hgV : Membership.mem V g := by
    refine And.intro ?_ hU.1
    change w g < w g + 1
    exact lt_add_of_pos_right _ zero_lt_one
  refine Exists.intro V (And.intro (hV.mem_nhds hgV) ?_)
  have hImage : MeasurableSet (Set.image e V) := (he.isOpenMap V hV).measurableSet
  have hFinite : base (Set.image e V) < Top.top := by
    refine lt_of_le_of_lt (measure_mono ?_) hU.2.2
    intro X hX
    choose x hx using hX
    rw [<- hx.2]
    exact hx.1.2
  have hBound : Filter.Eventually (fun X => weight X <= (B : ENNReal))
      (ae (base.restrict (Set.image e V))) := by
    filter_upwards [ae_restrict_mem hImage] with X hX
    choose x hx using hX
    rw [<- hx.2]
    change (w x : ENNReal) <= (B : ENNReal)
    exact ENNReal.coe_le_coe.mpr (le_of_lt hx.1.1)
  change (Measure.comap e (base.withDensity weight)) V < Top.top
  rw [hE.comap_apply, withDensity_apply _ hImage]
  refine lt_of_le_of_lt (lintegral_mono_ae hBound) ?_
  rw [lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hFinite

/-- For a Haar measure normalized on a measurable set of unit determinant
norm, the scalar for the determinant-weighted measure is the product
additive volume of that set in row coordinates. -/
theorem heckeLocalMatrixUnitWeightedMeasure_eq_smul_haar (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Units (Matrix I I (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix I I (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix I I (p.adicCompletion K)))) [mu.IsHaarMeasure]
    (C : Set (Units (Matrix I I (p.adicCompletion K)))) (hC : MeasurableSet C)
    (hMu : mu C = 1) (hDet : forall g, Membership.mem C g -> norm g.val.det = 1) :
    heckeLocalMatrixUnitWeightedMeasure p I =
      HSMul.hSMul (((Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p)))
        (Set.image heckeLocalMatrixUnitEntries C)).toNNReal) mu := by
  let L := p.adicCompletion K
  let G := Units (Matrix I I L)
  let nu := heckeLocalMatrixUnitWeightedMeasure p I
  let e : G -> I -> I -> L := heckeLocalMatrixUnitEntries
  let base := Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))
  let O : Set L := p.adicCompletionIntegers K
  have hComp : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_heckeLocalIntegers p)
  have hOpen : IsOpen O := Valued.isOpen_valuationSubring L
  have hz : Membership.mem O (0 : L) := (p.adicCompletionIntegers K).zero_mem
  let : LocallyCompactSpace L :=
    hComp.locallyCompactSpace_of_mem_nhds_of_addGroup (hOpen.mem_nhds hz)
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  have he : IsOpenEmbedding e := isOpenEmbedding_heckeLocalMatrixUnitEntries
  let : LocallyCompactSpace G := he.locallyCompactSpace
  let : SecondCountableTopology G := he.isEmbedding.secondCountableTopology
  let : IsLocallyFiniteMeasure nu := isLocallyFiniteMeasure_heckeLocalMatrixUnitWeightedMeasure p
  let : nu.IsMulLeftInvariant := isMulLeftInvariant_heckeLocalMatrixUnitWeightedMeasure p
  let c := nu.haarScalarFactor mu
  have hScale : nu = HSMul.hSMul c mu := Measure.isMulLeftInvariant_eq_smul nu mu
  have hE : MeasurableEmbedding e := he.measurableEmbedding
  have hImage : MeasurableSet (Set.image e C) := hE.measurableSet_image' hC
  have hD (X : I -> I -> L) (hX : Membership.mem (Set.image e C) X) :
      norm (Matrix.of X).det = 1 := by
    choose g hg using hX
    rw [<- hg.2]
    exact hDet g hg.1
  have hBase : nu C = base (Set.image e C) := by
    change (Measure.comap e (heckeLocalDeterminantWeightedMeasure p I)) C = _
    rw [hE.comap_apply]
    exact heckeLocalDeterminantWeightedMeasure_apply_of_detNorm_one p _ hImage hD
  have hc : (c : ENNReal) = base (Set.image e C) := by
    calc
      (c : ENNReal) = (HSMul.hSMul c mu) C := by
        rw [Measure.coe_nnreal_smul_apply, hMu, mul_one]
      _ = nu C := (congrArg (fun m : Measure G => m C) hScale).symm
      _ = base (Set.image e C) := hBase
  change nu = HSMul.hSMul ((base (Set.image e C)).toNNReal) mu
  rw [<- hc, ENNReal.toNNReal_coe]
  exact hScale

/-- The determinant-weighted measure is the pushforward of normalized Haar
measure scaled by the additive volume of its normalizing set. -/
theorem smul_map_heckeLocalMatrixHaar_eq_determinantWeightedMeasure (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Units (Matrix I I (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix I I (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix I I (p.adicCompletion K)))) [mu.IsHaarMeasure]
    (C : Set (Units (Matrix I I (p.adicCompletion K)))) (hC : MeasurableSet C)
    (hMu : mu C = 1) (hDet : forall g, Membership.mem C g -> norm g.val.det = 1) :
    HSMul.hSMul
        (((Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p)))
          (Set.image heckeLocalMatrixUnitEntries C)).toNNReal)
        (Measure.map heckeLocalMatrixUnitEntries mu) =
      heckeLocalDeterminantWeightedMeasure p I := by
  let c := ((Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p)))
    (Set.image heckeLocalMatrixUnitEntries C)).toNNReal
  change HSMul.hSMul c (Measure.map heckeLocalMatrixUnitEntries mu) = _
  rw [<- Measure.map_smul c,
    <- heckeLocalMatrixUnitWeightedMeasure_eq_smul_haar p mu C hC hMu hDet,
    map_heckeLocalMatrixUnitWeightedMeasure]

/-- The additive measure at a finite place is Haar measure normalized on
the integral ball. -/
theorem isAddHaarMeasure_heckeLocalAdditiveMeasure (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)] :
    (heckeLocalAdditiveMeasure p).IsAddHaarMeasure := by
  let L := p.adicCompletion K
  let O : Set L := p.adicCompletionIntegers K
  have hOpen : IsOpen O := Valued.isOpen_valuationSubring L
  have hCompact : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_heckeLocalIntegers p)
  let P : PositiveCompacts L :=
    { toCompacts := { carrier := O, isCompact' := hCompact }
      interior_nonempty' := by
        rw [hOpen.interior_eq]
        exact Exists.intro 0 (p.adicCompletionIntegers K).zero_mem }
  let : LocallyCompactSpace L := P.locallyCompactSpace_of_addGroup
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let mu := heckeLocalAdditiveMeasure p
  let eta : Measure L := Measure.addHaarMeasure P
  let : eta.IsAddHaarMeasure := inferInstanceAs ((Measure.addHaarMeasure P).IsAddHaarMeasure)
  let : mu.IsAddLeftInvariant := isAddLeftInvariant_heckeLocalAdditiveMeasure p
  let : IsLocallyFiniteMeasure mu := isLocallyFiniteMeasure_heckeLocalAdditiveMeasure p
  let c := mu.addHaarScalarFactor eta
  have hScale : mu = HSMul.hSMul c eta := Measure.isAddLeftInvariant_eq_smul mu eta
  have hEta : eta O = 1 := Measure.addHaarMeasure_self
  have hMu : mu O = 1 := heckeLocalAdditiveMeasure_integral p
  have hc : (c : ENNReal) = 1 := by
    have h := congrArg (fun m : Measure L => m O) hScale
    rw [hMu, Measure.coe_nnreal_smul_apply, hEta, mul_one] at h
    exact h.symm
  change mu.IsAddHaarMeasure
  rw [hScale, ENNReal.coe_eq_one.mp hc, one_smul]
  infer_instance

/-- A nonempty compact open normalizing set has positive finite additive
volume in matrix coordinates. -/
theorem heckeLocalMatrixHaar_additiveNormalization_pos (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    (C : Set (Units (Matrix I I (p.adicCompletion K))))
    (hCOpen : IsOpen C) (hCCompact : IsCompact C) (hCN : C.Nonempty) :
    let base := Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))
    0 < (base (Set.image heckeLocalMatrixUnitEntries C)).toNNReal := by
  intro base
  let L := p.adicCompletion K
  let mu := heckeLocalAdditiveMeasure p
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let : SigmaFinite mu := sigmaFinite_heckeLocalAdditiveMeasure p
  let : mu.IsAddHaarMeasure := isAddHaarMeasure_heckeLocalAdditiveMeasure p
  let : base.IsOpenPosMeasure := inferInstance
  let : IsFiniteMeasureOnCompacts base := inferInstance
  have he : IsOpenEmbedding (heckeLocalMatrixUnitEntries (I := I) (F := L)) :=
    isOpenEmbedding_heckeLocalMatrixUnitEntries
  have hPos := (he.isOpenMap _ hCOpen).measure_pos base (hCN.image _)
  have hFin : base (Set.image heckeLocalMatrixUnitEntries C) < Top.top :=
    (hCCompact.image he.continuous).measure_lt_top
  exact ENNReal.toNNReal_pos (ne_of_gt hPos) (ne_of_lt hFin)

/-- The determinant density transfers a measurable integrable function
on the matrix group to the product additive measure in row coordinates. -/
theorem integrableAndIntegral_heckeLocalMatrixHaar_additive (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Units (Matrix I I (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix I I (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix I I (p.adicCompletion K)))) [mu.IsHaarMeasure]
    (C : Set (Units (Matrix I I (p.adicCompletion K)))) (hC : MeasurableSet C)
    (hMu : mu C = 1) (hDet : forall g, Membership.mem C g -> norm g.val.det = 1)
    (f : Units (Matrix I I (p.adicCompletion K)) -> Complex)
    (hf : Measurable f) (hInt : Integrable f mu) :
    let e := heckeLocalMatrixUnitEntries (I := I) (F := p.adicCompletion K)
    let base := Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))
    let c := (base (Set.image e C)).toNNReal
    let F := Function.extend e f (fun _ => (0 : Complex))
    let T := fun X => HSMul.hSMul (heckeLocalInverseNorm p (Matrix.of X).det ^ Fintype.card I) (F X)
    And (Integrable T base) (integral base T = HSMul.hSMul c (integral mu f)) := by
  intro e base c F T
  let L := p.adicCompletion K
  let W (X : I -> I -> L) := heckeLocalInverseNorm p (Matrix.of X).det ^ Fintype.card I
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  have he : MeasurableEmbedding e := isOpenEmbedding_heckeLocalMatrixUnitEntries.measurableEmbedding
  have hF : Measurable F := he.measurable_extend hf measurable_const
  have hEntry (g : Units (Matrix I I L)) : F (e g) = f g :=
    he.injective.extend_apply f (fun _ => 0) g
  have hMatrix : Continuous (fun X : I -> I -> L => Matrix.of X) :=
    continuous_matrixOf.mpr continuous_id
  have hInv : Measurable (fun X : I -> I -> L => Inv.inv (norm (Matrix.of X).det)) :=
    hMatrix.matrix_det.norm.measurable.inv
  have hToNNReal : Continuous Real.toNNReal :=
    (continuous_id.max continuous_const).subtype_mk (fun y : Real => le_max_right y 0)
  have hW : Measurable W := (hToNNReal.measurable.comp hInv).pow_const _
  have hScale : HSMul.hSMul c (Measure.map e mu) =
      base.withDensity (fun X => (W X : ENNReal)) :=
    smul_map_heckeLocalMatrixHaar_eq_determinantWeightedMeasure p mu C hC hMu hDet
  have hMap : Integrable F (Measure.map e mu) := he.integrable_map_iff.mpr (by
    rw [show Function.comp F e = f from funext hEntry]
    exact hInt)
  have hScaled : Integrable F (base.withDensity (fun X => (W X : ENNReal))) := by
    rw [<- hScale]
    exact hMap.smul_measure (c := (c : ENNReal)) ENNReal.coe_ne_top
  constructor
  . refine And.intro (hW.smul hF).aestronglyMeasurable ?_
    have hFinite := (hasFiniteIntegral_iff_norm F).mp hScaled.2
    have hWM : Measurable (fun X : I -> I -> L => (W X : ENNReal)) :=
      measurable_coe_nnreal_ennreal.comp hW
    have hFN : Measurable (fun X : I -> I -> L => ENNReal.ofReal (norm (F X))) :=
      ENNReal.continuous_ofReal.measurable.comp hF.norm
    rw [lintegral_withDensity_eq_lintegral_mul base hWM hFN] at hFinite
    apply (hasFiniteIntegral_iff_norm T).mpr
    have hNorm (X : I -> I -> L) : ENNReal.ofReal (norm (T X)) =
        (W X : ENNReal) * ENNReal.ofReal (norm (F X)) := by
      change ENNReal.ofReal (norm (HSMul.hSMul (W X : Real) (F X))) = _
      have hNonneg : 0 <= (W X : Real) := (W X).2
      have hScalarNorm : norm (W X : Real) = (W X : Real) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
      rw [norm_smul, hScalarNorm, ENNReal.ofReal_mul hNonneg, ENNReal.ofReal_coe_nnreal]
    simp only [hNorm]
    exact hFinite
  . change integral base (fun X => HSMul.hSMul (W X) (F X)) = _
    rw [<- integral_withDensity_eq_integral_smul hW, <- hScale,
      integral_smul_nnreal_measure, he.integral_map]
    simp only [hEntry]

/-- The local zeta integrand with its determinant density absorbed and
extended by zero on singular matrices. -/
def heckeLocalZetaAdditiveIntegrand (p : Place)
    {I : Type*} [Fintype I] [DecidableEq I]
    (Phi : Matrix I I (p.adicCompletion K) -> Complex)
    (c : Units (Matrix I I (p.adicCompletion K)) -> Complex) (z : Complex) :
    (I -> I -> p.adicCompletion K) -> Complex :=
  Function.extend heckeLocalMatrixUnitEntries
    (fun g => (norm g.val.det : Complex) ^ (z - (Fintype.card I : Complex)) * (Phi g.val * c g))
    (fun _ => 0)

/-- Additive coordinates replace the determinant exponent z by z minus
the matrix dimension and scale the Haar integral by the additive
normalizing volume. Absolute integrability transfers to these coordinates. -/
theorem integrableAndIntegral_heckeLocalZeta_additive (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Units (Matrix I I (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix I I (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix I I (p.adicCompletion K)))) [mu.IsHaarMeasure]
    (C : Set (Units (Matrix I I (p.adicCompletion K)))) (hC : MeasurableSet C)
    (hMu : mu C = 1) (hDet : forall g, Membership.mem C g -> norm g.val.det = 1)
    (Phi : Matrix I I (p.adicCompletion K) -> Complex) (hPhi : Continuous Phi)
    (c : Units (Matrix I I (p.adicCompletion K)) -> Complex) (hc : Measurable c)
    (z : Complex) :
    let f := fun g : Units (Matrix I I (p.adicCompletion K)) =>
      (norm g.val.det : Complex) ^ z * (Phi g.val * c g)
    let base := Measure.pi (fun _ : I => Measure.pi (fun _ : I => heckeLocalAdditiveMeasure p))
    let m := (base (Set.image heckeLocalMatrixUnitEntries C)).toNNReal
    Integrable f mu ->
      And (Integrable (heckeLocalZetaAdditiveIntegrand p Phi c z) base)
        (integral base (heckeLocalZetaAdditiveIntegrand p Phi c z) =
          HSMul.hSMul m (integral mu f)) := by
  intro f base m hInt
  let L := p.adicCompletion K
  let G := Units (Matrix I I L)
  let e : G -> I -> I -> L := heckeLocalMatrixUnitEntries
  have hVal : Continuous (fun g : G => g.val) := Units.continuous_val
  have hBase : Continuous (fun g : G => (norm g.val.det : Complex)) :=
    Complex.continuous_ofReal.comp hVal.matrix_det.norm
  have hPow : Continuous (fun g : G => (norm g.val.det : Complex) ^ z) :=
    hBase.cpow continuous_const (fun g => Complex.ofReal_mem_slitPlane.mpr
      (norm_pos_iff.mpr (g.isUnit.map Matrix.detMonoidHom).ne_zero))
  have hf : Measurable f := hPow.measurable.mul ((hPhi.comp hVal).measurable.mul hc)
  have hTransfer := integrableAndIntegral_heckeLocalMatrixHaar_additive p mu C hC hMu hDet f hf hInt
  let F := Function.extend e f (fun _ => (0 : Complex))
  let T := fun X => HSMul.hSMul (heckeLocalInverseNorm p (Matrix.of X).det ^ Fintype.card I) (F X)
  have he : Function.Injective e := isOpenEmbedding_heckeLocalMatrixUnitEntries.injective
  have hEq : T = heckeLocalZetaAdditiveIntegrand p Phi c z := by
    funext X
    by_cases h : exists g : G, e g = X
    . choose g hg using h
      rw [<- hg]
      have hX : (Matrix.of (e g)).det = g.val.det := rfl
      have hF : F (e g) = f g := he.extend_apply f (fun _ => 0) g
      change HSMul.hSMul (heckeLocalInverseNorm p (Matrix.of (e g)).det ^ Fintype.card I)
        (F (e g)) = _
      rw [hX, hF, heckeLocalZetaAdditiveIntegrand, he.extend_apply]
      let r := norm g.val.det
      have hr : Not ((r : Complex) = 0) :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (g.isUnit.map Matrix.detMonoidHom).ne_zero)
      change HSMul.hSMul
          ((Real.toNNReal (Inv.inv r) ^ Fintype.card I : NNReal) : Real)
          ((r : Complex) ^ z * (Phi g.val * c g)) =
        (r : Complex) ^ (z - (Fintype.card I : Complex)) * (Phi g.val * c g)
      rw [Complex.real_smul, NNReal.coe_pow,
        Real.coe_toNNReal _ (inv_nonneg.mpr (norm_nonneg _)), Complex.ofReal_pow,
        Complex.ofReal_inv, inv_pow, Complex.cpow_sub z _ hr, Complex.cpow_natCast,
        div_eq_mul_inv]
      ac_rfl
    . have hF : F X = 0 := Function.extend_apply' _ _ X h
      change HSMul.hSMul (heckeLocalInverseNorm p (Matrix.of X).det ^ Fintype.card I) (F X) = _
      rw [hF, smul_zero, heckeLocalZetaAdditiveIntegrand, Function.extend_apply' _ _ X h]
  change And (Integrable T base) (integral base T = HSMul.hSMul m (integral mu f)) at hTransfer
  rw [hEq] at hTransfer
  exact hTransfer

private theorem measurePreserving_splitMatrixColumns
    {E R I J : Type*} [MeasurableSpace E] [Fintype R] [Fintype I] [Fintype J]
    (mu : Measure E) [SigmaFinite mu] :
    MeasurePreserving
      (fun X : R -> Sum I J -> E =>
        Prod.mk (fun r i => X r (Sum.inl i)) (fun r j => X r (Sum.inr j)))
      (Measure.pi (fun _ : R => Measure.pi (fun _ : Sum I J => mu)))
      ((Measure.pi (fun _ : R => Measure.pi (fun _ : I => mu))).prod
        (Measure.pi (fun _ : R => Measure.pi (fun _ : J => mu)))) := by
  let rowI := Measure.pi (fun _ : I => mu)
  let rowJ := Measure.pi (fun _ : J => mu)
  let rowSum := Measure.pi (fun _ : Sum I J => mu)
  have hSplit := measurePreserving_pi
    (fun _ : R => rowSum) (fun _ : R => rowI.prod rowJ)
    (fun _ => measurePreserving_sumPiEquivProdPi (fun _ : Sum I J => mu))
  have hCollect := measurePreserving_arrowProdEquivProdArrow
    (I -> E) (J -> E) R (fun _ => rowI) (fun _ => rowJ)
  exact hCollect.comp hSplit

private theorem measurePreserving_fourBlockSplit
    {E I J : Type*} [MeasurableSpace E] [Fintype I] [Fintype J]
    (mu : Measure E) [SigmaFinite mu] :
    MeasurePreserving
      (fun X : Sum I J -> Sum I J -> E =>
        Prod.mk
          (Prod.mk (fun i k => X (Sum.inl i) (Sum.inl k))
                   (fun i l => X (Sum.inl i) (Sum.inr l)))
          (Prod.mk (fun j k => X (Sum.inr j) (Sum.inl k))
                   (fun j l => X (Sum.inr j) (Sum.inr l))))
      (Measure.pi (fun _ : Sum I J => Measure.pi (fun _ : Sum I J => mu)))
      (((Measure.pi (fun _ : I => Measure.pi (fun _ : I => mu))).prod
         (Measure.pi (fun _ : I => Measure.pi (fun _ : J => mu)))).prod
       ((Measure.pi (fun _ : J => Measure.pi (fun _ : I => mu))).prod
         (Measure.pi (fun _ : J => Measure.pi (fun _ : J => mu))))) := by
  have hRows := measurePreserving_sumPiEquivProdPi
    (fun _ : Sum I J => Measure.pi (fun _ : Sum I J => mu))
  have hTop := measurePreserving_splitMatrixColumns (R := I) (I := I) (J := J) mu
  have hBottom := measurePreserving_splitMatrixColumns (R := J) (I := I) (J := J) mu
  exact (hTop.prod hBottom).comp hRows

section LocalSchurCoordinates

variable {F I J : Type*} [NormedField F] [Fintype I] [Fintype J] [DecidableEq I]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

local notation "TopRows" => Prod (I -> I -> F) (I -> J -> F)
local notation "BelowLeft" => J -> I -> F
local notation "BelowRight" => J -> J -> F
local notation "SchurBase" => Prod TopRows BelowLeft
local notation "FourBlocks" => Prod TopRows (Prod BelowLeft BelowRight)

/-- The correction C A^-1 B in the trailing block of a Schur substitution. -/
def godementJacquetSchurCorrection (P : SchurBase) : BelowRight :=
  fun i j => (Matrix.of P.2 * Inv.inv (Matrix.of P.1.1) * Matrix.of P.1.2) i j

omit [Fintype J] in
private theorem measurable_godementJacquetSchurCorrection :
    Measurable (godementJacquetSchurCorrection (I := I) (J := J) (F := F)) := by
  let G := Units (Matrix I I F)
  let : MeasurableSpace G := borel G
  let : BorelSpace G := { measurable_eq := rfl }
  let e : G -> I -> I -> F := heckeLocalMatrixUnitEntries
  let v : (I -> I -> F) -> I -> I -> F :=
    Function.extend e (fun g : G => e (Inv.inv g)) (fun _ => 0)
  have he : MeasurableEmbedding e :=
    isOpenEmbedding_heckeLocalMatrixUnitEntries.measurableEmbedding
  have hv : Measurable v := he.measurable_extend
    (he.measurable.comp continuous_inv.measurable) measurable_const
  have hvEq (a : I -> I -> F) : Matrix.of (v a) = Inv.inv (Matrix.of a) := by
    by_cases hA : (Matrix.of a).det = 0
    . have hNot : Not (exists g : G, e g = a) := by
        intro hex
        choose g hg using hex
        have hDet : g.val.det = 0 := by
          change (Matrix.of (e g)).det = 0
          rw [hg, hA]
        exact (g.isUnit.map Matrix.detMonoidHom).ne_zero hDet
      have hz : v a = 0 := Function.extend_apply' _ _ a hNot
      have hUnit : Not (IsUnit (Matrix.of a).det) := by
        rw [hA]
        exact not_isUnit_zero
      rw [hz, Matrix.nonsing_inv_apply_not_isUnit _ hUnit]
      ext i j
      rfl
    . let g : G := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of a) hA
      have hAg : e g = a := rfl
      rw [<- hAg, show v (e g) = e (Inv.inv g) from he.injective.extend_apply _ _ g]
      exact Matrix.coe_units_inv g
  have hTop (i k : I) : Measurable (fun p : SchurBase => v p.1.1 i k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp
      (hv.comp (measurable_fst.comp measurable_fst)))
  have hLeft (i : J) (k : I) : Measurable (fun p : SchurBase => p.2 i k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_snd)
  have hRight (i : I) (j : J) : Measurable (fun p : SchurBase => p.1.2 i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_snd.comp measurable_fst))
  refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
  have hInner (k : I) : Measurable (fun p : SchurBase =>
      (Matrix.of p.2 * Matrix.of (v p.1.1)) i k) := by
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_fun_sum _ (fun l _ => (hLeft i l).mul (hTop l k))
  have hOuter : Measurable (fun p : SchurBase =>
      (Matrix.of p.2 * Matrix.of (v p.1.1) * Matrix.of p.1.2) i j) := by
    simp only [Matrix.mul_apply, Matrix.of_apply]
    simpa only [Matrix.mul_apply, Matrix.of_apply, Pi.mul_apply] using
      (Finset.measurable_fun_sum Finset.univ (fun l _ => (hInner l).mul (hRight l j)))
  simpa only [godementJacquetSchurCorrection, hvEq] using hOuter

private theorem measurePreserving_godementJacquetSchurShift
    (mu : Measure F) [SigmaFinite mu] [mu.IsAddLeftInvariant] :
    let mA := Measure.pi (fun _ : I => Measure.pi (fun _ : I => mu))
    let mB := Measure.pi (fun _ : I => Measure.pi (fun _ : J => mu))
    let mC := Measure.pi (fun _ : J => Measure.pi (fun _ : I => mu))
    let mD := Measure.pi (fun _ : J => Measure.pi (fun _ : J => mu))
    let m := (mA.prod mB).prod (mC.prod mD)
    MeasurePreserving
      (fun X : FourBlocks => Prod.mk X.1
        (Prod.mk X.2.1 (X.2.2 - godementJacquetSchurCorrection (Prod.mk X.1 X.2.1))))
      m m := by
  intro mA mB mC mD m
  let mLeft := (mA.prod mB).prod mC
  let : mD.IsAddLeftInvariant := by
    let nu := Measure.pi (fun _ : J => mu)
    let : forall _ : J, mu.IsAddLeftInvariant := fun _ => inferInstance
    let : nu.IsAddLeftInvariant := Measure.pi.isAddLeftInvariant (fun _ : J => mu)
    let : forall _ : J, nu.IsAddLeftInvariant := fun _ => inferInstance
    exact Measure.pi.isAddLeftInvariant (fun _ : J => nu)
  let e : MeasurableEquiv (Prod SchurBase BelowRight) FourBlocks := MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e (mLeft.prod mD) m :=
    measurePreserving_prodAssoc (mA.prod mB) mC mD
  have heInv : MeasurePreserving e.symm m (mLeft.prod mD) := he.symm
  let sh : Prod SchurBase BelowRight -> Prod SchurBase BelowRight :=
    fun P => Prod.mk P.1 (P.2 - godementJacquetSchurCorrection P.1)
  have hd : Measurable (fun P : Prod SchurBase BelowRight =>
      P.2 - godementJacquetSchurCorrection P.1) :=
    measurable_snd.sub (measurable_godementJacquetSchurCorrection.comp measurable_fst)
  have hSh : MeasurePreserving sh (mLeft.prod mD) (mLeft.prod mD) := by
    refine (MeasurePreserving.id mLeft).skew_product
      (g := fun P D => D - godementJacquetSchurCorrection P) hd ?_
    refine Filter.Eventually.of_forall ?_
    intro P
    have hMove : MeasurePreserving (fun D : BelowRight => D - godementJacquetSchurCorrection P)
        mD mD := by
      simpa only [sub_eq_add_neg, add_comm] using
        measurePreserving_add_left mD (-godementJacquetSchurCorrection P)
    exact hMove.map_eq
  exact he.comp (hSh.comp heInv)

/-- The change of entries taking the trailing block D to D - C a^-1 B
sends the additive matrix measure to the product measure of the blocks. -/
theorem measurePreserving_godementJacquetSchurCoordinates
    (mu : Measure F) [SigmaFinite mu] [mu.IsAddLeftInvariant] :
    MeasurePreserving
      (fun X : Sum I J -> Sum I J -> F =>
        let a := fun i k => X (Sum.inl i) (Sum.inl k)
        let b := fun i l => X (Sum.inl i) (Sum.inr l)
        let c := fun j k => X (Sum.inr j) (Sum.inl k)
        let d := fun j l => X (Sum.inr j) (Sum.inr l)
        Prod.mk (Prod.mk a b) (Prod.mk c
          (d - godementJacquetSchurCorrection (Prod.mk (Prod.mk a b) c))))
      (Measure.pi (fun _ : Sum I J => Measure.pi (fun _ : Sum I J => mu)))
      (((Measure.pi (fun _ : I => Measure.pi (fun _ : I => mu))).prod
         (Measure.pi (fun _ : I => Measure.pi (fun _ : J => mu)))).prod
       ((Measure.pi (fun _ : J => Measure.pi (fun _ : I => mu))).prod
         (Measure.pi (fun _ : J => Measure.pi (fun _ : J => mu))))) :=
  (measurePreserving_godementJacquetSchurShift mu).comp (measurePreserving_fourBlockSplit mu)

end LocalSchurCoordinates

section SchurIntegral

variable {F I J : Type*} [NormedField F] [Fintype I] [Fintype J] [DecidableEq I]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

local notation "TopRows" => Prod (I -> I -> F) (I -> J -> F)
local notation "FourBlocks" => Prod TopRows (Prod (J -> I -> F) (J -> J -> F))
local notation "Entries" => Sum I J -> Sum I J -> F

/-- Recover the original matrix entries by adding C A^-1 B to the trailing block. -/
def godementJacquetSchurAssemble (p : FourBlocks) : Entries :=
  fun i j => Sum.elim
    (fun a => Sum.elim (p.1.1 a) (p.1.2 a) j)
    (fun a => Sum.elim (p.2.1 a)
      ((p.2.2 + godementJacquetSchurCorrection (Prod.mk p.1 p.2.1)) a) j) i

/-- The explicit Schur coordinate substitution preserves integrals and absolute integrability. -/
theorem integrableAndIntegral_godementJacquetSchurCoordinates
    (mu : Measure F) [SigmaFinite mu] [mu.IsAddLeftInvariant]
    (f : Entries -> Complex) :
    let mA := Measure.pi (fun _ : I => Measure.pi (fun _ : I => mu))
    let mB := Measure.pi (fun _ : I => Measure.pi (fun _ : J => mu))
    let mC := Measure.pi (fun _ : J => Measure.pi (fun _ : I => mu))
    let mD := Measure.pi (fun _ : J => Measure.pi (fun _ : J => mu))
    let m := (mA.prod mB).prod (mC.prod mD)
    let base := Measure.pi (fun _ : Sum I J => Measure.pi (fun _ : Sum I J => mu))
    And (Integrable f base <->
        Integrable (fun p => f (godementJacquetSchurAssemble p)) m)
      (integral base f = integral m (fun p => f (godementJacquetSchurAssemble p))) := by
  intro mA mB mC mD m base
  let entries (x : Entries) : FourBlocks :=
    let a := fun i k => x (Sum.inl i) (Sum.inl k)
    let b := fun i l => x (Sum.inl i) (Sum.inr l)
    let c := fun j k => x (Sum.inr j) (Sum.inl k)
    let d := fun j l => x (Sum.inr j) (Sum.inr l)
    Prod.mk (Prod.mk a b) (Prod.mk c
      (d - godementJacquetSchurCorrection (Prod.mk (Prod.mk a b) c)))
  have hEntries : MeasurePreserving entries base m :=
    measurePreserving_godementJacquetSchurCoordinates mu
  let restore : FourBlocks -> Entries := godementJacquetSchurAssemble
  have hLeft : Function.LeftInverse restore entries := by
    intro x
    funext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j =>
        change (x (Sum.inr i) (Sum.inr j) - _) + _ = _
        exact sub_add_cancel _ _
  have hRight : Function.RightInverse restore entries := by
    intro p
    apply Prod.ext
    . rfl
    . apply Prod.ext
      . rfl
      . change (p.2.2 + godementJacquetSchurCorrection (Prod.mk p.1 p.2.1)) -
            godementJacquetSchurCorrection (Prod.mk p.1 p.2.1) = _
        exact add_sub_cancel_right _ _
  have hRestore : Measurable restore := by
    have hCorrection : Measurable (fun p : FourBlocks =>
        godementJacquetSchurCorrection (Prod.mk p.1 p.2.1)) :=
      measurable_godementJacquetSchurCorrection.comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hTrailing : Measurable (fun p : FourBlocks =>
        p.2.2 + godementJacquetSchurCorrection (Prod.mk p.1 p.2.1)) :=
      (measurable_snd.comp measurable_snd).add hCorrection
    refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_fst))
      | inr j =>
        exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
          (measurable_snd.comp measurable_fst))
    | inr i =>
      cases j with
      | inl j =>
        exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_snd))
      | inr j =>
        exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hTrailing)
  let e : MeasurableEquiv Entries FourBlocks :=
    { toFun := entries
      invFun := restore
      left_inv := hLeft
      right_inv := hRight
      measurable_toFun := hEntries.measurable
      measurable_invFun := hRestore }
  have he : MeasurePreserving e base m := hEntries
  have hInv : MeasurePreserving e.symm m base := he.symm
  constructor
  . rw [<- hInv.map_eq, e.symm.measurableEmbedding.integrable_map_iff]
    rfl
  . exact (hInv.integral_comp' f).symm

end SchurIntegral

omit [MeasurableSpace A] [BorelSpace A] in
/-- At invertible matrices the additive integrand is given by the shifted exponent. -/
theorem heckeLocalZetaAdditiveIntegrand_apply_entries (p : Place)
    {I : Type*} [Fintype I] [DecidableEq I]
    (Phi : Matrix I I (p.adicCompletion K) -> Complex)
    (c : Units (Matrix I I (p.adicCompletion K)) -> Complex) (z : Complex)
    (g : Units (Matrix I I (p.adicCompletion K))) :
    heckeLocalZetaAdditiveIntegrand p Phi c z (heckeLocalMatrixUnitEntries g) =
      (norm g.val.det : Complex) ^ (z - (Fintype.card I : Complex)) * (Phi g.val * c g) := by
  unfold heckeLocalZetaAdditiveIntegrand
  exact isOpenEmbedding_heckeLocalMatrixUnitEntries.injective.extend_apply _ _ g

omit [MeasurableSpace A] [BorelSpace A] in
/-- The additive integrand vanishes on every singular matrix. -/
theorem heckeLocalZetaAdditiveIntegrand_eq_zero_of_det_eq_zero (p : Place)
    {I : Type*} [Fintype I] [DecidableEq I]
    (Phi : Matrix I I (p.adicCompletion K) -> Complex)
    (c : Units (Matrix I I (p.adicCompletion K)) -> Complex) (z : Complex)
    (x : I -> I -> p.adicCompletion K) (hx : (Matrix.of x).det = 0) :
    heckeLocalZetaAdditiveIntegrand p Phi c z x = 0 := by
  have hNot : Not (exists g : Units (Matrix I I (p.adicCompletion K)),
      heckeLocalMatrixUnitEntries g = x) := by
    intro h
    choose g hg using h
    have hDet : g.val.det = 0 := by
      change (Matrix.of (heckeLocalMatrixUnitEntries g)).det = 0
      rw [hg, hx]
    exact (g.isUnit.map Matrix.detMonoidHom).ne_zero hDet
  exact Function.extend_apply' _ _ x hNot

/-- For a finite-place local zeta integral, Schur block coordinates preserve
absolute integrability and give the same additive normalizing factor
as the original Haar-to-additive comparison. -/
theorem integrableAndIntegral_heckeLocalZeta_schur (p : Place)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [MeasurableSpace (Units (Matrix (Sum I J) (Sum I J) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Sum I J) (Sum I J) (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix (Sum I J) (Sum I J) (p.adicCompletion K)))) [mu.IsHaarMeasure]
    (C : Set (Units (Matrix (Sum I J) (Sum I J) (p.adicCompletion K)))) (hC : MeasurableSet C)
    (hMu : mu C = 1) (hDet : forall g, Membership.mem C g -> norm g.val.det = 1)
    (Phi : Matrix (Sum I J) (Sum I J) (p.adicCompletion K) -> Complex) (hPhi : Continuous Phi)
    (c : Units (Matrix (Sum I J) (Sum I J) (p.adicCompletion K)) -> Complex) (hc : Measurable c)
    (z : Complex) :
    let f := fun g : Units (Matrix (Sum I J) (Sum I J) (p.adicCompletion K)) =>
      (norm g.val.det : Complex) ^ z * (Phi g.val * c g)
    let nu := heckeLocalAdditiveMeasure p
    let base := Measure.pi (fun _ : Sum I J => Measure.pi (fun _ : Sum I J => nu))
    let volume := (base (Set.image heckeLocalMatrixUnitEntries C)).toNNReal
    let mA := Measure.pi (fun _ : I => Measure.pi (fun _ : I => nu))
    let mB := Measure.pi (fun _ : I => Measure.pi (fun _ : J => nu))
    let mC := Measure.pi (fun _ : J => Measure.pi (fun _ : I => nu))
    let mD := Measure.pi (fun _ : J => Measure.pi (fun _ : J => nu))
    let blocks := (mA.prod mB).prod (mC.prod mD)
    let g := fun x =>
      heckeLocalZetaAdditiveIntegrand p Phi c z (godementJacquetSchurAssemble x)
    Integrable f mu ->
      And (Integrable g blocks) (integral blocks g = HSMul.hSMul volume (integral mu f)) := by
  intro f nu base volume mA mB mC mD blocks g hInt
  let : SecondCountableTopology (p.adicCompletion K) := secondCountableLocalAdditiveCompletion p
  let : SigmaFinite nu := sigmaFinite_heckeLocalAdditiveMeasure p
  let : nu.IsAddLeftInvariant := isAddLeftInvariant_heckeLocalAdditiveMeasure p
  have hAdd := integrableAndIntegral_heckeLocalZeta_additive p mu C hC hMu hDet
    Phi hPhi c hc z hInt
  have hSchur := integrableAndIntegral_godementJacquetSchurCoordinates (I := I) (J := J)
    nu (heckeLocalZetaAdditiveIntegrand p Phi c z)
  exact And.intro (hSchur.1.mp hAdd.1) (hSchur.2.symm.trans hAdd.2)

end LocalMatrixGroupMeasure

end Robin1984.GRH
