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
private theorem secondCountableLocalAdditiveCompletion (p : Place) :
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
