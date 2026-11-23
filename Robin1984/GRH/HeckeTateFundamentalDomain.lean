import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Topology.Covering.Quotient
import Robin1984.GRH.HeckeTateThetaDecay

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Fundamental domains for discrete principal ideles in Tate's quotient integration.
- Formalization note: Selects one Borel representative per norm-one class from a finite cover of the compact quotient and proves finite mass on the selected domain.
- PROVENANCE-END
-/

/-!
# A Borel fundamental domain for norm-one ideles

The discrete principal subgroup acts by right translations. A finite cover
of the compact class quotient by local sections gives a relatively compact
Borel fundamental domain and a finite pushforward of the restricted measure.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField MeasureTheory Topology IsDedekindDomain
open scoped Classical

/-- A surjective local homeomorphism onto a compact space has a relatively compact Borel section. -/
theorem exists_measurableSectionSet_of_compactLocalHomeomorph
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (q : X -> Y) (hq : Continuous q) (hOpen : IsOpenMap q) (hSurj : Function.Surjective q)
    (hLocal : IsLocalHomeomorph q) :
    Exists (fun S : Set X => Exists (fun C : Set X =>
      And (IsCompact C) (And (S <= C)
        (And (MeasurableSet S) (And (Set.InjOn q S) (Set.image q S = Set.univ)))))) := by
  choose E hE hQ using hLocal
  choose B hB using (fun x : X => exists_compact_mem_nhds x)
  let U (x : X) := Set.inter (E x).source (interior (B x))
  let V (x : X) := Set.image q (U x)
  have hU (x : X) : IsOpen (U x) := (E x).open_source.inter isOpen_interior
  have hV (x : X) : IsOpen (V x) := hOpen _ (hU x)
  have hInj (x : X) : Set.InjOn q (U x) := by
    rw [hQ x]
    exact (E x).injOn.mono Set.inter_subset_left
  have hCover : (Set.univ : Set Y) <= Set.iUnion V := by
    intro y _
    choose x hx using hSurj y
    have hxU : Membership.mem (U x) x :=
      And.intro (hE x) (mem_interior_iff_mem_nhds.mpr (hB x).2)
    exact Set.mem_iUnion.mpr (Exists.intro x (Exists.intro x (And.intro hxU hx)))
  choose F hF using isCompact_univ.elim_finite_subcover V hV hCover
  have hFinite (F : Finset X) :
      Exists (fun S : Set X => Exists (fun C : Set X => And (IsCompact C) (And (S <= C)
        (And (MeasurableSet S) (And (Set.InjOn q S) (And (IsOpen (Set.image q S))
          (forall x : X, Membership.mem F x -> V x <= Set.image q S))))))) := by
    induction F using Finset.induction_on with
    | empty =>
      let empty : Set X := EmptyCollection.emptyCollection
      refine Exists.intro empty (Exists.intro empty (And.intro isCompact_empty
        (And.intro le_rfl (And.intro MeasurableSet.empty (And.intro (Set.injOn_empty q) ?_)))))
      refine And.intro (by rw [Set.image_empty]; exact isOpen_empty) ?_
      intro x hx
      exact False.elim (Finset.notMem_empty x hx)
    | insert a F ha ih =>
      choose S C hS using ih
      let A := SDiff.sdiff (U a) (Set.preimage q (Set.image q S))
      let W := Union.union S A
      have hA : MeasurableSet A :=
        (IsOpen.measurableSet (hU a)).diff ((IsOpen.measurableSet hS.2.2.2.2.1).preimage hq.measurable)
      have hA' : A <= B a := Set.sdiff_subset.trans (Set.inter_subset_right.trans interior_subset)
      have hImg : Set.image q W = Union.union (Set.image q S) (V a) := by
        change Set.image q (Union.union S (SDiff.sdiff (U a) (Set.preimage q (Set.image q S)))) = _
        rw [Set.image_union, Set.image_sdiff_preimage]
        ext y
        change Iff
          (Or (Membership.mem (Set.image q S) y)
            (And (Membership.mem (V a) y) (Not (Membership.mem (Set.image q S) y))))
          (Or (Membership.mem (Set.image q S) y) (Membership.mem (V a) y))
        by_cases hy : Membership.mem (Set.image q S) y <;> simp [hy]
      have hCross {x y : X} (hx : Membership.mem S x) (hy : Membership.mem A y)
          (he : q x = q y) : False := by
        exact hy.2 (Exists.intro x (And.intro hx he))
      refine Exists.intro W (Exists.intro (Union.union C (B a)) (And.intro (hS.1.union (hB a).1)
        (And.intro (Set.union_subset_union hS.2.1 hA') (And.intro (hS.2.2.1.union hA)
          (And.intro ?_ (And.intro ?_ ?_))))))
      . intro x hx y hy he
        cases hx with
        | inl hx =>
          cases hy with
          | inl hy => exact hS.2.2.2.1 hx hy he
          | inr hy => exact False.elim (hCross hx hy he)
        | inr hx =>
          cases hy with
          | inl hy => exact False.elim (hCross hy hx he.symm)
          | inr hy => exact hInj a hx.1 hy.1 he
      . rw [hImg]
        exact hS.2.2.2.2.1.union (hV a)
      . intro x hx y hy
        rw [hImg]
        rcases Finset.mem_insert.mp hx with hx | hx
        . exact Or.inr (by rw [<- hx]; exact hy)
        . exact Or.inl (hS.2.2.2.2.2 x hx hy)
  choose S C hS using hFinite F
  refine Exists.intro S (Exists.intro C (And.intro hS.1 (And.intro hS.2.1
    (And.intro hS.2.2.1 (And.intro hS.2.2.2.1 ?_)))))
  apply Set.eq_univ_of_forall
  intro y
  have h := hF (Set.mem_univ y)
  choose x hx using Set.mem_iUnion.mp h
  choose hxF hy using Set.mem_iUnion.mp hx
  exact hS.2.2.2.2.2 x hxF hy

variable (K : Type*) [Field K] [NumberField K]

/-- The group of norm-one ideles is locally compact in its subgroup topology. -/
theorem locallyCompactSpace_heckeNormOneIdeles : LocallyCompactSpace (heckeNormOneIdeles K) := by
  let V := InfiniteAdeleRing K
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let e : Homeomorph V (mixedEmbedding.mixedSpace K) :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
      continuous_toFun := continuous_heckeInfiniteAdele_mixedSpace (K := K)
      continuous_invFun := continuous_heckeInfiniteAdele_mixedSpace_symm K }
  let : LocallyCompactSpace V := e.isClosedEmbedding.locallyCompactSpace
  let : LocallyCompactSpace F := locallyCompactSpace_heckeFiniteAdeles
  let A := AdeleRing (RingOfIntegers K) K
  let : T2Space V := by
    change T2Space ((w : InfinitePlace K) -> w.Completion)
    infer_instance
  let : T2Space F := by
    let projection (a : F) (p : HeightOneSpectrum (RingOfIntegers K)) := a p
    have hInj : Function.Injective projection := DFunLike.coe_injective
    have hCont : Continuous projection := continuous_pi (fun p => RestrictedProduct.continuous_eval p)
    exact T2Space.of_injective_continuous hInj hCont
  let : T2Space A := (inferInstance : T2Space (Prod V F))
  let : LocallyCompactSpace A := (inferInstance : LocallyCompactSpace (Prod V F))
  let : LocallyCompactSpace (MulOpposite A) :=
    (MulOpposite.opHomeomorph.symm : Homeomorph (MulOpposite A) A).isClosedEmbedding.locallyCompactSpace
  let : LocallyCompactSpace (Units A) :=
    (show IsClosedEmbedding (Units.embedProduct A) from Units.isClosedEmbedding_embedProduct).locallyCompactSpace
  have hClosed : IsClosed ((heckeNormOneIdeles K) : Set (Units (AdeleRing (RingOfIntegers K) K))) := by
    have hEq : ((heckeNormOneIdeles K) : Set (Units (AdeleRing (RingOfIntegers K) K))) =
        Set.ofPred (fun a => heckeIdelicNorm a = 1) :=
      Set.ext (mem_heckeNormOneIdeles K)
    rw [hEq]
    exact isClosed_eq continuous_heckeIdelicNorm continuous_const
  exact hClosed.locallyCompactSpace

/-- The norm-one idele class quotient has a Borel section contained in a compact set. -/
theorem exists_heckeNormOneClassBorelSection
    [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]
    [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)] :
    Exists (fun S : Set (heckeNormOneIdeles K) => Exists (fun C : Set (heckeNormOneIdeles K) =>
      And (IsCompact C) (And (S <= C) (And (MeasurableSet S)
        (And (Set.InjOn (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S)
          (Set.image (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S = Set.univ)))))) := by
  let G := (heckePrincipalNormOneIdele K).range
  let : CompactSpace (heckeNormOneIdeleClass K) := compactSpace_heckeNormOneIdeleClass K
  let : LocallyCompactSpace (heckeNormOneIdeles K) := locallyCompactSpace_heckeNormOneIdeles K
  have hG : IsDiscrete (G : Set (heckeNormOneIdeles K)) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr (discreteTopology_heckePrincipalNormOneIdeles K)
  have hQ : IsLocalHomeomorph (QuotientGroup.mk (s := G)) :=
    (G.isQuotientCoveringMap hG).isCoveringMap.isLocalHomeomorph
  exact exists_measurableSectionSet_of_compactLocalHomeomorph (QuotientGroup.mk (s := G))
    QuotientGroup.continuous_mk QuotientGroup.isOpenMap_coe Quotient.mk_surjective hQ

/-- There is a relatively compact Borel fundamental domain for principal translations of norm-one ideles. -/
theorem exists_heckeNormOneClassFundamentalDomain
    [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]
    [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeles K)) :
    Exists (fun S : Set (heckeNormOneIdeles K) => Exists (fun C : Set (heckeNormOneIdeles K) =>
      And (IsCompact C) (And (S <= C) (And (MeasurableSet S)
        (IsFundamentalDomain (heckePrincipalNormOneIdele K).range.op S mu))))) := by
  let G := (heckePrincipalNormOneIdele K).range
  let q := QuotientGroup.mk' G
  choose S C hS using exists_heckeNormOneClassBorelSection K
  refine Exists.intro S (Exists.intro C (And.intro hS.1
    (And.intro hS.2.1 (And.intro hS.2.2.1 ?_))))
  apply IsFundamentalDomain.mk' hS.2.2.1.nullMeasurableSet
  intro x
  have hx : Membership.mem (Set.image q S) (q x) := by
    have h : Set.image q S = Set.univ := hS.2.2.2.2
    rw [h]
    exact Set.mem_univ _
  choose y hy hyq using hx
  have hG : Membership.mem G (Inv.inv x * y) := QuotientGroup.leftRel_apply.mp (Quotient.exact hyq.symm)
  let a : G.op := Subtype.mk (MulOpposite.op (Inv.inv x * y)) hG
  have ha : SMul.smul a x = y := by
    change x * (Inv.inv x * y) = y
    rw [<- mul_assoc, mul_inv_cancel, one_mul]
  have haS : Membership.mem S (SMul.smul a x) := by
    rw [ha]
    exact hy
  refine ExistsUnique.intro a haS ?_
  intro b hb
  have hbq : q (SMul.smul b x) = q x := by
    change q (x * MulOpposite.unop b.val) = q x
    have hOne : q (MulOpposite.unop b.val) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr b.property
    rw [q.map_mul, hOne]
    exact mul_one (q x)
  have hInj : Set.InjOn q S := hS.2.2.2.1
  have haq : q (SMul.smul a x) = q x := (congrArg (fun z => q z) ha).trans hyq
  have hba : SMul.smul b x = SMul.smul a x := hInj hb haS (hbq.trans haq.symm)
  apply Subtype.ext
  apply MulOpposite.unop_injective
  exact mul_left_cancel hba

/-- The principal norm-one subgroup is countable. -/
theorem countable_heckePrincipalNormOneIdeles :
    Countable (heckePrincipalNormOneIdele K).range := by
  let e := (Module.finBasis Rat K).equivFun
  let : Countable K := e.injective.countable
  let : Countable (Units K) := Units.val_injective.countable
  let P := heckePrincipalNormOneIdele K
  have h : Function.Surjective P.rangeRestrict := by
    intro a
    choose b hb using a.property
    exact Exists.intro b (Subtype.ext hb)
  exact h.countable

/-- The opposite principal subgroup used for right translations is countable. -/
theorem countable_heckePrincipalNormOneIdeles_op :
    Countable (heckePrincipalNormOneIdele K).range.op := by
  let G := (heckePrincipalNormOneIdele K).range
  let : Countable G := countable_heckePrincipalNormOneIdeles K
  let f (a : G.op) : G := Subtype.mk (MulOpposite.unop a.val) a.property
  have h : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (MulOpposite.unop_injective (congrArg Subtype.val hab))
  exact h.countable

/-- Push a measure restricted to an idele fundamental domain forward to the class group. -/
noncomputable def heckeNormOneClassQuotientMeasure
    [MeasurableSpace (heckeNormOneIdeles K)] [MeasurableSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeles K)) (S : Set (heckeNormOneIdeles K)) :
    Measure (heckeNormOneIdeleClass K) :=
  Measure.map (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) (mu.restrict S)

/-- A compact bound on the chosen representatives gives finite quotient mass. -/
theorem isFiniteMeasure_heckeNormOneClassQuotientMeasure
    [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]
    [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeles K)) [IsFiniteMeasureOnCompacts mu]
    {S C : Set (heckeNormOneIdeles K)} (hC : IsCompact C) (hSC : S <= C) :
    IsFiniteMeasure (heckeNormOneClassQuotientMeasure K mu S) := by
  let q := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
  have hq : Measurable q := (show Continuous q from QuotientGroup.continuous_mk).measurable
  refine IsFiniteMeasure.mk ?_
  change Measure.map q (mu.restrict S) Set.univ < Top.top
  rw [Measure.map_apply hq MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact (measure_mono hSC).trans_lt hC.measure_lt_top

end Robin1984.GRH
