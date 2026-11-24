import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Topology.Compactness.Lindelof
import Robin1984.GRH.GodementJacquetCoordinates
import Robin1984.GRH.HeckeTateAdelicEuler

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Borel fundamental domains for discrete subgroups of second-countable groups and the determinant-one quotient in the Godement-Jacquet zeta integral.
- Formalization note: Constructs a measurable fundamental domain for rational left translation on the determinant-norm-one adelic general linear group.
- PROVENANCE-END
-/

/-!
# A Borel fundamental domain for rational matrices

Small right translates of a neighborhood of the identity meet each
left orbit in at most one point. A countable subcover supplies an
order on these sets. On each set, remove the translates of all
earlier sets. The remaining union is Borel and contains one point
from every orbit.

The determinant-norm-one adelic group is second countable. Its
rational subgroup is discrete because each matrix entry is a
principal adele. The Borel fundamental domain therefore exists for
the quotient integral.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open MeasureTheory Topology
open scoped Classical

/-- A discrete subgroup of a second-countable topological group admits
a Borel fundamental domain for left translation. -/
theorem exists_isFundamentalDomain_of_discreteSubgroup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) [DiscreteTopology H] (mu : Measure G) :
    Exists (fun S : Set G => And (MeasurableSet S) (IsFundamentalDomain H S mu)) := by
  have hSingleton : IsOpen ({(1 : H)} : Set H) := isOpen_discrete _
  choose V hV using (isOpen_induced_iff (f := fun h : H => (h : G))).mp hSingleton
  have hOneV : Membership.mem V (1 : G) := by
    change Membership.mem (Set.preimage (fun h : H => (h : G)) V) (1 : H)
    rw [hV.2]
    exact Set.mem_singleton 1
  have hLocal {x : G} (hx : Membership.mem V x) (hH : Membership.mem H x) : x = 1 := by
    let y : H := Subtype.mk x hH
    have hy : Membership.mem (Set.preimage (fun h : H => (h : G)) V) y := hx
    rw [hV.2] at hy
    exact congrArg (fun h : H => (h : G)) (Set.mem_singleton_iff.mp hy)
  let F (z : Prod G G) := z.1 * Inv.inv z.2
  have hFo : IsOpen (Set.preimage F V) := hV.1.preimage (continuous_fst.mul continuous_snd.inv)
  have hFo1 : Membership.mem (Set.preimage F V) (Prod.mk (1 : G) (1 : G)) := by
    change Membership.mem V (1 * Inv.inv (1 : G))
    rw [inv_one, mul_one]
    exact hOneV
  choose U1 U2 hU using mem_nhds_prod_iff'.mp (hFo.mem_nhds hFo1)
  let U := Set.inter U1 U2
  have hOpenU : IsOpen U := hU.1.inter hU.2.2.1
  have hOneU : Membership.mem U (1 : G) := And.intro hU.2.1 hU.2.2.2.1
  have hUV {x y : G} (hx : Membership.mem U x) (hy : Membership.mem U y) :
      Membership.mem V (x * Inv.inv y) :=
    hU.2.2.2.2 (show Membership.mem (Set.prod U1 U2) (Prod.mk x y) from And.intro hx.1 hy.2)
  let W (g : G) := Set.image (fun u : G => u * g) U
  have hOpenW (g : G) : IsOpen (W g) := (Homeomorph.mulRight g).isOpenMap _ hOpenU
  have hW (g : G) : Membership.mem (W g) g := Exists.intro 1 (And.intro hOneU (one_mul g))
  have hUniqueInW (g : G) {x y : G} (hx : Membership.mem (W g) x)
      (hy : Membership.mem (W g) y) (hxy : Membership.mem H (x * Inv.inv y)) : x = y := by
    choose u hu using hx
    choose v hv using hy
    have he : x * Inv.inv y = u * Inv.inv v := by
      rw [<- hu.2, <- hv.2, mul_inv_rev, mul_assoc u g, <- mul_assoc g, mul_inv_cancel, one_mul]
    have hVxy : Membership.mem V (x * Inv.inv y) := by
      rw [he]
      exact hUV hu.1 hv.1
    calc
      x = (x * Inv.inv y) * y := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = y := by rw [hLocal hVxy hxy, one_mul]
  have hCover : (Set.univ : Set G) <= Set.iUnion W :=
    fun x _ => Set.mem_iUnion.mpr (Exists.intro x (hW x))
  choose c hc using isLindelof_univ.indexed_countable_subcover W hOpenW hCover
  let Z (k : Nat) (h : H) := Set.image (fun z : G => (h : G) * z) (W (c k))
  let B (n : Nat) := Set.iUnion (fun k : Nat => Set.iUnion (fun _ : k < n => Set.iUnion (Z k)))
  let T (n : Nat) := SDiff.sdiff (W (c n)) (B n)
  let S : Set G := Set.iUnion T
  have hOpenB (n : Nat) : IsOpen (B n) :=
    isOpen_iUnion (fun k => isOpen_iUnion (fun _ => isOpen_iUnion
      (fun h : H => (Homeomorph.mulLeft (h : G)).isOpenMap _ (hOpenW (c k)))))
  have hS : MeasurableSet S := MeasurableSet.iUnion (fun n =>
    (hOpenW (c n)).measurableSet.diff (hOpenB n).measurableSet)
  have mem_B (n : Nat) (y : G) :
      Membership.mem (B n) y <-> Exists (fun k : Nat => And (k < n)
        (Exists (fun a : H => Exists (fun z : G =>
          And (Membership.mem (W (c k)) z) (SMul.smul a z = y))))) := by
    constructor
    case mp =>
      intro hy
      choose k hk using Set.mem_iUnion.mp hy
      choose hkn hz using Set.mem_iUnion.mp hk
      choose a ha using Set.mem_iUnion.mp hz
      exact Exists.intro k (And.intro hkn (Exists.intro a ha))
    case mpr =>
      intro hy
      choose k hk using hy
      choose a ha using hk.2
      exact Set.mem_iUnion.mpr (Exists.intro k
        (Set.mem_iUnion.mpr (Exists.intro hk.1 (Set.mem_iUnion.mpr (Exists.intro a ha)))))
  refine Exists.intro S (And.intro hS (IsFundamentalDomain.mk' hS.nullMeasurableSet ?_))
  intro x
  let P (n : Nat) := Exists (fun h : H => Membership.mem (W (c n)) (SMul.smul h x))
  have hP : Exists P := by
    choose n hn using Set.mem_iUnion.mp (hc (Set.mem_univ x))
    refine Exists.intro n (Exists.intro (1 : H) ?_)
    change Membership.mem (W (c n)) ((1 : G) * x)
    rw [one_mul]
    exact hn
  let i := Nat.find hP
  choose a ha using Nat.find_spec hP
  have haB : Not (Membership.mem (B i) (SMul.smul a x)) := by
    intro h
    choose k hk using (mem_B i (SMul.smul a x)).mp h
    choose b z hz using hk.2
    have he : SMul.smul (Inv.inv b * a) x = z := by
      change (Inv.inv (b : G) * (a : G)) * x = z
      have hz' : (b : G) * z = (a : G) * x := hz.2
      rw [mul_assoc (Inv.inv (b : G)), <- hz', <- mul_assoc, inv_mul_cancel, one_mul]
    have hpk : P k := Exists.intro (Inv.inv b * a) (he.symm.subst hz.1)
    exact (not_lt_of_ge (Nat.find_min' hP hpk)) hk.1
  have haT : Membership.mem (T i) (SMul.smul a x) := And.intro ha haB
  refine ExistsUnique.intro a (Set.mem_iUnion.mpr (Exists.intro i haT)) ?_
  intro b hb
  choose j hj using Set.mem_iUnion.mp hb
  have hLater {k l : Nat} {r s : H} (hr : Membership.mem (T k) (SMul.smul r x))
      (hs : Membership.mem (T l) (SMul.smul s x)) (hkl : k < l) : False := by
    have he : SMul.smul (s * Inv.inv r) (SMul.smul r x) = SMul.smul s x := by
      change ((s : G) * Inv.inv (r : G)) * ((r : G) * x) = (s : G) * x
      rw [mul_assoc (s : G), <- mul_assoc (Inv.inv (r : G)), inv_mul_cancel, one_mul]
    exact hs.2 ((mem_B l (SMul.smul s x)).mpr (Exists.intro k (And.intro hkl
      (Exists.intro (s * Inv.inv r) (Exists.intro (SMul.smul r x) (And.intro hr.1 he))))))
  have hji : j = i :=
    le_antisymm (not_lt.mp (fun hi => hLater haT hj hi)) (not_lt.mp (fun hj' => hLater hj haT hj'))
  rw [hji] at hj
  have hbH : Membership.mem H (SMul.smul b x * Inv.inv (SMul.smul a x)) := by
    change Membership.mem H (((b : G) * x) * Inv.inv ((a : G) * x))
    rw [mul_inv_rev, mul_assoc (b : G) x, <- mul_assoc x, mul_inv_cancel, one_mul]
    exact H.mul_mem b.property (H.inv_mem a.property)
  have he := hUniqueInW (c i) hj.1 haT.1 hbH
  apply Subtype.ext
  exact mul_right_cancel he

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

/-- The adelic general linear group is second countable in its unit topology. -/
theorem secondCountableTopology_adelicGeneralLinearGroup :
    SecondCountableTopology (AdelicGeneralLinearGroup K n) := by
  let V := InfiniteAdeleRing K
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let e : Homeomorph V (mixedEmbedding.mixedSpace K) :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
      continuous_toFun := continuous_heckeInfiniteAdele_mixedSpace (K := K)
      continuous_invFun := continuous_heckeInfiniteAdele_mixedSpace_symm K }
  let : SecondCountableTopology V := e.isEmbedding.secondCountableTopology
  let : SecondCountableTopology F := secondCountableTopology_heckeFiniteAdeles K
  let A := AdeleRing (RingOfIntegers K) K
  let : SecondCountableTopology A := inferInstanceAs (SecondCountableTopology (Prod V F))
  let M := Matrix (Fin n) (Fin n) A
  let : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> A))
  let : SecondCountableTopology (MulOpposite M) :=
    (MulOpposite.opHomeomorph.symm : Homeomorph (MulOpposite M) M).isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := M)).secondCountableTopology

/-- The rational subgroup of the determinant-norm-one adelic group is discrete. -/
theorem discreteTopology_adelicPrincipalDeterminantOne :
    DiscreteTopology (adelicPrincipalDeterminantOne K n).range := by
  let A := AdeleRing (RingOfIntegers K) K
  let D := AdeleRing.principalSubgroup (RingOfIntegers K) K
  let P := (adelicPrincipalDeterminantOne K n).range
  let : DiscreteTopology D := discreteTopology_principalAdeles K
  have hEntry (x : P) (i j : Fin n) : Membership.mem D (x.val.val.val i j) := by
    choose g hg using x.property
    refine Exists.intro (g.val i j) ?_
    exact congrArg (fun z : (adelicDeterminantLogNorm K n).ker => z.val.val i j) hg
  let E (x : P) (i j : Fin n) : D := Subtype.mk (x.val.val.val i j) (hEntry x i j)
  have hVal : Continuous (fun x : P => (x.val.val.val : Matrix (Fin n) (Fin n) A)) :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val
  have hE : Continuous E := by
    refine continuous_pi (fun i => continuous_pi (fun j => ?_))
    exact ((continuous_apply j).comp ((continuous_apply i).comp hVal)).subtype_mk _
  have hInj : Function.Injective E := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact congrArg Subtype.val (congrFun (congrFun h i) j)
  exact DiscreteTopology.of_continuous_injective hE hInj

/-- A Borel fundamental domain for rational left translation on the
determinant-norm-one adelic group. -/
theorem exists_adelicPrincipalDeterminantOneFundamentalDomain
    [MeasurableSpace (adelicDeterminantLogNorm K n).ker] [BorelSpace (adelicDeterminantLogNorm K n).ker]
    (mu : Measure (adelicDeterminantLogNorm K n).ker) :
    Exists (fun S : Set (adelicDeterminantLogNorm K n).ker =>
      And (MeasurableSet S) (IsFundamentalDomain (adelicPrincipalDeterminantOne K n).range S mu)) := by
  let : SecondCountableTopology (AdelicGeneralLinearGroup K n) :=
    secondCountableTopology_adelicGeneralLinearGroup K n
  let : SecondCountableTopology (adelicDeterminantLogNorm K n).ker :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      (fun g : (adelicDeterminantLogNorm K n).ker => g.val)).secondCountableTopology
  let : DiscreteTopology (adelicPrincipalDeterminantOne K n).range :=
    discreteTopology_adelicPrincipalDeterminantOne K n
  exact exists_isFundamentalDomain_of_discreteSubgroup (adelicPrincipalDeterminantOne K n).range mu

private theorem adelicGeneralLinearGroup_topology :
    And (T2Space (AdelicGeneralLinearGroup K n))
      (LocallyCompactSpace (AdelicGeneralLinearGroup K n)) := by
  let V := InfiniteAdeleRing K
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let e : Homeomorph V (mixedEmbedding.mixedSpace K) :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
      continuous_toFun := continuous_heckeInfiniteAdele_mixedSpace (K := K)
      continuous_invFun := continuous_heckeInfiniteAdele_mixedSpace_symm K }
  let : T2Space V := T2Space.of_injective_continuous e.injective e.continuous
  let : LocallyCompactSpace V := e.isClosedEmbedding.locallyCompactSpace
  let : T2Space F := by
    let projection (x : F) (p : HeightOneSpectrum (RingOfIntegers K)) := x p
    exact T2Space.of_injective_continuous (show Function.Injective projection from DFunLike.coe_injective)
      (continuous_pi (fun p => RestrictedProduct.continuous_eval p))
  let : LocallyCompactSpace F := locallyCompactSpace_heckeFiniteAdeles
  let A := AdeleRing (RingOfIntegers K) K
  let : T2Space A := inferInstanceAs (T2Space (Prod V F))
  let : LocallyCompactSpace A := inferInstanceAs (LocallyCompactSpace (Prod V F))
  let M := Matrix (Fin n) (Fin n) A
  let : T2Space M := inferInstanceAs (T2Space (Fin n -> Fin n -> A))
  let : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (Fin n -> Fin n -> A))
  let o : Homeomorph (MulOpposite M) M := MulOpposite.opHomeomorph.symm
  let : T2Space (MulOpposite M) := T2Space.of_injective_continuous o.injective o.continuous
  let : LocallyCompactSpace (MulOpposite M) := o.isClosedEmbedding.locallyCompactSpace
  have hU : Topology.IsClosedEmbedding (Units.embedProduct M) := Units.isClosedEmbedding_embedProduct
  exact And.intro (T2Space.of_injective_continuous hU.injective hU.continuous) hU.locallyCompactSpace

/-- The determinant-norm-one subgroup is closed in the adelic general linear group. -/
theorem isClosed_adelicDeterminantNormOne :
    IsClosed ((adelicDeterminantLogNorm K n).ker : Set (AdelicGeneralLinearGroup K n)) := by
  have hEq : ((adelicDeterminantLogNorm K n).ker : Set (AdelicGeneralLinearGroup K n)) =
    Set.ofPred (fun g => adelicDeterminantNorm K n g = 1) := by
    apply Set.ext
    intro g
    constructor
    . intro hg
      change Real.log (adelicDeterminantNorm K n g) = 0 at hg
      change adelicDeterminantNorm K n g = 1
      rw [<- Real.exp_log (adelicDeterminantNorm_pos K n g), hg, Real.exp_zero]
    . intro hg
      change adelicDeterminantNorm K n g = 1 at hg
      change Real.log (adelicDeterminantNorm K n g) = 0
      rw [hg, Real.log_one]
  rw [hEq]
  exact isClosed_eq (continuous_adelicDeterminantNorm K n) continuous_const

/-- The determinant-norm-one adelic group has a left Haar measure and
a Borel fundamental domain for rational left translation. -/
theorem exists_adelicDeterminantNormOneHaar_fundamentalDomain
    [MeasurableSpace (adelicDeterminantLogNorm K n).ker]
    [BorelSpace (adelicDeterminantLogNorm K n).ker] :
    Exists (fun mu : Measure (adelicDeterminantLogNorm K n).ker =>
      And mu.IsHaarMeasure
        (Exists (fun S : Set (adelicDeterminantLogNorm K n).ker =>
          And (MeasurableSet S) (IsFundamentalDomain (adelicPrincipalDeterminantOne K n).range S mu)))) := by
  let G := AdelicGeneralLinearGroup K n
  let N := (adelicDeterminantLogNorm K n).ker
  let : T2Space G := (adelicGeneralLinearGroup_topology K n).1
  let : LocallyCompactSpace G := (adelicGeneralLinearGroup_topology K n).2
  let : T2Space N := T2Space.of_injective_continuous Subtype.val_injective continuous_subtype_val
  let : LocallyCompactSpace N := (isClosed_adelicDeterminantNormOne K n).locallyCompactSpace
  let C : TopologicalSpace.PositiveCompacts N := Classical.choice (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts N))
  let mu := Measure.haarMeasure C
  exact Exists.intro mu (And.intro inferInstance (exists_adelicPrincipalDeterminantOneFundamentalDomain K n mu))

section NormalizerOrbitMeasure

variable {G : Type*} [Group G]

private abbrev LeftOrbit (H : Subgroup G) := Quotient (MulAction.orbitRel H G)

private def leftOrbitNormalizerMap (H : Subgroup G) (a : G)
    (ha : forall h : H, Membership.mem H (a * h.val * Inv.inv a)) :
    LeftOrbit H -> LeftOrbit H :=
  Quotient.map (fun x => a * x) (by
    intro x y h
    change Exists (fun k : H => k.val * y = x) at h
    choose k hk using h
    change Exists (fun z : H => z.val * (a * y) = a * x)
    refine Exists.intro (Subtype.mk (a * k.val * Inv.inv a) (ha k)) ?_
    change (a * k.val * Inv.inv a) * (a * y) = a * x
    calc
      _ = a * (k.val * y) := by simp [mul_assoc]
      _ = _ := congrArg (fun t => a * t) hk)

variable [MeasurableSpace G] [MeasurableMul G]

/-- Left translation by a normalizer element acts on the left orbit space. -/
def leftOrbitNormalizerEquiv (H : Subgroup G) (a : G)
    (ha : forall h : H, Membership.mem H (a * h.val * Inv.inv a))
    (hai : forall h : H, Membership.mem H (Inv.inv a * h.val * a)) :
    MeasurableEquiv (LeftOrbit H) (LeftOrbit H) where
  toEquiv :=
    { toFun := leftOrbitNormalizerMap H a ha
      invFun := leftOrbitNormalizerMap H (Inv.inv a) (fun h => by simpa only [inv_inv] using hai h)
      left_inv := by
        intro x
        refine Quotient.inductionOn x ?_
        intro y
        change Quotient.mk (MulAction.orbitRel H G) (Inv.inv a * (a * y)) =
          Quotient.mk (MulAction.orbitRel H G) y
        simp
      right_inv := by
        intro x
        refine Quotient.inductionOn x ?_
        intro y
        change Quotient.mk (MulAction.orbitRel H G) (a * (Inv.inv a * y)) =
          Quotient.mk (MulAction.orbitRel H G) y
        simp }
  measurable_toFun := by
    refine measurable_from_quotient.mpr ?_
    have hq : Measurable (Quotient.mk (MulAction.orbitRel H G)) :=
      fun _ hs => measurableSet_quotient.mp hs
    exact hq.comp (MeasurableEquiv.mulLeft a).measurable
  measurable_invFun := by
    refine measurable_from_quotient.mpr ?_
    have hq : Measurable (Quotient.mk (MulAction.orbitRel H G)) :=
      fun _ hs => measurableSet_quotient.mp hs
    exact hq.comp (MeasurableEquiv.mulLeft (Inv.inv a)).measurable

/-- A normalizer translation preserves the quotient measure obtained by
restricting left Haar measure to a Borel fundamental domain. -/
theorem measurePreserving_leftOrbitNormalizerEquiv (H : Subgroup G) [Countable H]
    (mu : Measure G) [mu.IsMulLeftInvariant] (S : Set G) (hS : MeasurableSet S)
    (hUnique : forall x : G, ExistsUnique (fun h : H => Membership.mem S (HSMul.hSMul h x)))
    (a : G) (ha : forall h : H, Membership.mem H (a * h.val * Inv.inv a))
    (hai : forall h : H, Membership.mem H (Inv.inv a * h.val * a)) :
    let m := (mu.restrict S).map (Quotient.mk (MulAction.orbitRel H G))
    MeasurePreserving (leftOrbitNormalizerEquiv H a ha hai) m m := by
  let q := Quotient.mk (MulAction.orbitRel H G)
  let e := MeasurableEquiv.mulLeft a
  let E := leftOrbitNormalizerEquiv H a ha hai
  let T := Set.preimage e.symm S
  let c (h : H) : H := Subtype.mk (a * h.val * Inv.inv a) (ha h)
  let d (h : H) : H := Subtype.mk (Inv.inv a * h.val * a) (hai h)
  have hCD (h : H) : c (d h) = h := Subtype.ext (by simp [c, d, mul_assoc])
  have hDC (h : H) : d (c h) = h := Subtype.ext (by simp [c, d, mul_assoc])
  have hT : MeasurableSet T := e.symm.measurable hS
  have hMem (h : H) (x : G) : Membership.mem T (HSMul.hSMul h x) <->
      Membership.mem S (HSMul.hSMul (d h) (Inv.inv a * x)) := by
    change Membership.mem S (Inv.inv a * (h.val * x)) <->
      Membership.mem S ((Inv.inv a * h.val * a) * (Inv.inv a * x))
    simp [mul_assoc]
  have hDom : IsFundamentalDomain H S mu := IsFundamentalDomain.mk' hS.nullMeasurableSet hUnique
  have hDomT : IsFundamentalDomain H T mu := by
    refine IsFundamentalDomain.mk' hT.nullMeasurableSet ?_
    intro x
    have h := hUnique (Inv.inv a * x)
    change Exists (fun k : H => And (Membership.mem S (HSMul.hSMul k (Inv.inv a * x)))
      (forall l : H, Membership.mem S (HSMul.hSMul l (Inv.inv a * x)) -> l = k)) at h
    choose k hk using h
    refine Exists.intro (c k) (And.intro ?_ ?_)
    . apply (hMem (c k) x).mpr
      rw [hDC]
      exact hk.1
    . intro l hl
      have hd : d l = k := hk.2 (d l) ((hMem l x).mp hl)
      exact (hCD l).symm.trans (congrArg c hd)
  have hq : Measurable q := fun _ hs => measurableSet_quotient.mp hs
  let : SMulInvariantMeasure H G mu :=
    { measure_preimage_smul := fun h s hs =>
        (measurePreserving_mul_left mu h.val).measure_preimage hs.nullMeasurableSet }
  have hPreT : Set.preimage e T = S := by
    ext y
    change Membership.mem S (e.symm (e y)) <-> Membership.mem S y
    rw [e.symm_apply_apply]
  have hMap : (mu.restrict S).map e = mu.restrict T := by
    ext U hU
    rw [Measure.map_apply e.measurable hU, Measure.restrict_apply (e.measurable hU),
      Measure.restrict_apply hU]
    have hEq : Set.preimage e (Inter.inter U T) = Inter.inter (Set.preimage e U) S := by
      rw [Set.preimage_inter, hPreT]
    rw [<- hEq]
    exact (measurePreserving_mul_left mu a).measure_preimage (hU.inter hT).nullMeasurableSet
  refine MeasurePreserving.mk E.measurable ?_
  change Measure.map E (Measure.map q (mu.restrict S)) = Measure.map q (mu.restrict S)
  rw [Measure.map_map E.measurable hq,
    show Function.comp E q = Function.comp q e from rfl,
    <- Measure.map_map hq e.measurable, hMap]
  exact hDomT.quotientMeasure_eq mu hDom

end NormalizerOrbitMeasure

section OrbitAverage

variable {G X E : Type*} [MeasurableSpace G] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

private theorem integral_eq_integral_orbitAverage
    (nu : Measure G) [IsProbabilityMeasure nu] (mu : Measure X) [SFinite mu]
    (act : G -> MeasurableEquiv X X)
    (hAct : Measurable (fun z : Prod G X => act z.1 z.2))
    (hPres : forall u, MeasurePreserving (act u) mu mu)
    (f : X -> E) (hf : Measurable f) (hI : Integrable f mu) :
    integral mu f = integral mu (fun x => integral nu (fun u => f (act u x))) := by
  let F (z : Prod G X) := f (act z.1 z.2)
  have hSlice (u : G) : Integrable (fun x => f (act u x)) mu :=
    ((hPres u).integrable_comp_emb (act u).measurableEmbedding).mpr hI
  have hNorm (u : G) : integral mu (fun x => norm (f (act u x))) =
      integral mu (fun x => norm (f x)) :=
    (hPres u).integral_comp (act u).measurableEmbedding (fun x => norm (f x))
  have hm : Measurable F := hf.comp hAct
  have hProd : Integrable F (nu.prod mu) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).mpr
      (And.intro (Filter.Eventually.of_forall hSlice) ?_)
    simp only [F, hNorm]
    exact integrable_const (integral mu (fun x => norm (f x)))
  have hValue (u : G) : integral mu (fun x => f (act u x)) = integral mu f :=
    (hPres u).integral_comp (act u).measurableEmbedding f
  calc
    integral mu f = integral nu (fun _ => integral mu f) := by simp
    _ = integral nu (fun u => integral mu (fun x => f (act u x))) := by simp only [hValue]
    _ = _ := integral_integral_swap hProd

private theorem integral_weighted_eq_zero_of_orbitAverage
    (nu : Measure G) [IsProbabilityMeasure nu] (mu : Measure X) [SFinite mu]
    (act : G -> MeasurableEquiv X X)
    (hAct : Measurable (fun z : Prod G X => act z.1 z.2))
    (hPres : forall u, MeasurePreserving (act u) mu mu)
    (f : X -> E) (hf : Measurable f) (w : X -> Real) (hw : Measurable w)
    (hInvariant : forall u x, w (act u x) = w x)
    (hI : Integrable (fun x => HSMul.hSMul (w x) (f x)) mu)
    (hMean : Filter.Eventually (fun x => integral nu (fun u => f (act u x)) = 0) (ae mu)) :
    integral mu (fun x => HSMul.hSMul (w x) (f x)) = 0 := by
  rw [integral_eq_integral_orbitAverage nu mu act hAct hPres
    (fun x => HSMul.hSMul (w x) (f x)) (hw.smul hf) hI]
  have hZero : Filter.EventuallyEq (ae mu)
      (fun x => integral nu (fun u => HSMul.hSMul (w (act u x)) (f (act u x)))) (fun _ => 0) := by
    filter_upwards [hMean] with x hx
    simp only [hInvariant, integral_smul, hx, smul_zero]
  exact (integral_congr_ae hZero).trans (integral_zero X E)

end OrbitAverage

section FundamentalDomainWeights

variable {L X E : Type*} [Group L] [Countable L] [MeasurableSpace X]
  [MulAction L X] [MeasurableConstSMul L X]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Integration on a fundamental domain equals integration against a
nonnegative weight whose sum over each orbit is one. -/
private theorem integrable_weightedFundamentalDomain
    (mu : Measure X) [SMulInvariantMeasure L X mu] (S : Set X)
    (hS : IsFundamentalDomain L S mu)
    (f : X -> E) (hf : Measurable f) (hInt : IntegrableOn f S mu)
    (hInvariant : forall (g : L) x, f (HSMul.hSMul g x) = f x)
    (w : X -> ENNReal) (hw : Measurable w) (hBound : forall x, w x <= 1)
    (hPartition : forall x, tsum (fun g : L => w (HSMul.hSMul g x)) = 1) :
    let F := fun x => HSMul.hSMul (w x).toReal (f x)
    And (Integrable F mu) (integral mu F = integral (mu.restrict S) f) := by
  let nu := mu.restrict S
  let F (x : X) := HSMul.hSMul (w x).toReal (f x)
  let J (g : L) (x : X) := F (HSMul.hSMul (Inv.inv g) x)
  have hWF (x : X) : Not (w x = Top.top) :=
    ne_of_lt (lt_of_le_of_lt (hBound x) ENNReal.one_lt_top)
  have hPart (x : X) : tsum (fun g : L => w (HSMul.hSMul (Inv.inv g) x)) = 1 :=
    ((Equiv.inv L).tsum_eq (fun g => w (HSMul.hSMul g x))).trans (hPartition x)
  have hF : Measurable F := hw.ennreal_toReal.smul hf
  have hJ (g : L) : Measurable (J g) :=
    hF.comp (measurable_const_smul (Inv.inv g))
  have hNorm (x : X) : enorm (F x) = w x * enorm (f x) := by
    change enorm (HSMul.hSMul (w x).toReal (f x)) = _
    rw [enorm_smul, Real.enorm_toReal (hWF x)]
  have hSize : tsum (fun g : L => lintegral nu (fun x => enorm (J g x))) =
      lintegral nu (fun x => enorm (f x)) := calc
    _ = lintegral nu (fun x => tsum (fun g : L => enorm (J g x))) :=
      (lintegral_tsum (fun g => (hJ g).enorm.aemeasurable)).symm
    _ = _ := lintegral_congr (fun x => by
      simp only [J, hNorm, hInvariant]
      rw [ENNReal.tsum_mul_right, hPart, one_mul])
  have hFin : Integrable F mu := by
    refine And.intro hF.aestronglyMeasurable ?_
    change lintegral mu (fun x => enorm (F x)) < Top.top
    rw [hS.lintegral_eq_tsum', hSize]
    exact hInt.hasFiniteIntegral
  have hMass : Not (tsum (fun g : L => lintegral nu (fun x => enorm (J g x))) = Top.top) :=
    hSize.trans_ne (ne_of_lt hInt.hasFiniteIntegral)
  have hPoint (x : X) : tsum (fun g : L => J g x) = f x := by
    have hne : Not (tsum (fun g : L => w (HSMul.hSMul (Inv.inv g) x)) = Top.top) :=
      (hPart x).trans_ne ENNReal.one_ne_top
    simp only [J, F, hInvariant]
    rw [Summable.tsum_smul_const (ENNReal.summable_toReal hne),
      <- ENNReal.tsum_toReal_eq (fun g => hWF (HSMul.hSMul (Inv.inv g) x)),
      hPart, ENNReal.toReal_one, one_smul]
  refine And.intro hFin ?_
  calc
    _ = tsum (fun g : L => integral nu (J g)) := hS.integral_eq_tsum' F hFin
    _ = integral nu (fun x => tsum (fun g => J g x)) :=
      (integral_tsum (fun g => (hJ g).aestronglyMeasurable) hMass).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hPoint)

end FundamentalDomainWeights

section OrbitCancellation

variable {C L X E : Type*}
  [Group C] [MeasurableSpace C] [MeasurableMul C]
  [Group L] [Countable L] [MeasurableSpace X]
  [MulAction C X] [MeasurableConstSMul C X]
  [MulAction L X] [MeasurableConstSMul L X]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Integrating over the discrete quotient gives zero when the function
has zero compact orbit average and the discrete group normalizes
the compact action through measure-preserving automorphisms. -/
theorem setIntegral_eq_zero_of_orbitAverage
    (nu : Measure C) [IsProbabilityMeasure nu] [nu.IsMulRightInvariant]
    (mu : Measure X) [SFinite mu] [SMulInvariantMeasure C X mu]
    [SMulInvariantMeasure L X mu] (S : Set X)
    (hS : IsFundamentalDomain L S mu) (hMeas : MeasurableSet S)
    (hUnique : forall x : X, ExistsUnique (fun g : L => Membership.mem S (HSMul.hSMul g x)))
    (hAct : Measurable (fun p : Prod C X => HSMul.hSMul p.1 p.2))
    (aut : L -> MeasurableEquiv C C)
    (hAut : forall g, MeasurePreserving (aut g) nu nu)
    (hCompat : forall (g : L) (u : C) (x : X),
      HSMul.hSMul u (HSMul.hSMul g x) = HSMul.hSMul g (HSMul.hSMul (aut g u) x))
    (f : X -> E) (hf : Measurable f) (hInt : IntegrableOn f S mu)
    (hInvariant : forall (g : L) x, f (HSMul.hSMul g x) = f x)
    (hMean : Filter.Eventually (fun x => integral nu (fun u : C => f (HSMul.hSMul u x)) = 0) (ae mu)) :
    integral (mu.restrict S) f = 0 := by
  let chi : X -> ENNReal := S.indicator (fun _ => 1)
  let w (x : X) := lintegral nu (fun u : C => chi (HSMul.hSMul u x))
  have hChi : Measurable chi := measurable_const.indicator hMeas
  have hSlice (x : X) : Measurable (fun u : C => HSMul.hSMul u x) :=
    hAct.comp (measurable_id.prodMk measurable_const)
  have hW : Measurable w :=
    (hChi.comp (hAct.comp (measurable_snd.prodMk measurable_fst :
      Measurable (fun p : Prod X C => Prod.mk p.2 p.1)))).lintegral_prod_right'
  have hBound (x : X) : w x <= 1 := calc
    _ <= lintegral nu (fun _ : C => (1 : ENNReal)) := lintegral_mono (fun u => by
      by_cases h : Membership.mem S (HSMul.hSMul u x)
      . simp [chi, h]
      . simp [chi, h])
    _ = _ := by simp
  have hWInv (u : C) (x : X) : w (HSMul.hSMul u x) = w x := calc
    _ = lintegral nu (fun v : C => chi (HSMul.hSMul (v * u) x)) := by simp only [w, mul_smul]
    _ = w x := lintegral_mul_right_eq_self (fun v : C => chi (HSMul.hSMul v x)) u
  have hCount (x : X) : tsum (fun g : L => chi (HSMul.hSMul g x)) = 1 := by
    have h := hUnique x
    change Exists (fun g : L => And (Membership.mem S (HSMul.hSMul g x))
      (forall l : L, Membership.mem S (HSMul.hSMul l x) -> l = g)) at h
    choose g hg using h
    calc
      _ = chi (HSMul.hSMul g x) := tsum_eq_single g (fun l hl =>
        Set.indicator_of_notMem (fun hs => hl (hg.2 l hs)) _)
      _ = _ := Set.indicator_of_mem hg.1 _
  have hWCompat (g : L) (x : X) :
      w (HSMul.hSMul g x) = lintegral nu (fun u : C => chi (HSMul.hSMul g (HSMul.hSMul u x))) := by
    have hF : Measurable (fun u : C => chi (HSMul.hSMul g (HSMul.hSMul u x))) :=
      hChi.comp ((measurable_const_smul g).comp (hSlice x))
    have hMap : lintegral (Measure.map (aut g) nu) (fun u : C =>
        chi (HSMul.hSMul g (HSMul.hSMul u x))) =
          lintegral nu (fun u : C => chi (HSMul.hSMul g (HSMul.hSMul (aut g u) x))) :=
      lintegral_map hF (aut g).measurable
    rw [(hAut g).map_eq] at hMap
    change lintegral nu (fun u : C => chi (HSMul.hSMul u (HSMul.hSMul g x))) = _
    simp only [hCompat]
    exact hMap.symm
  have hPartition (x : X) : tsum (fun g : L => w (HSMul.hSMul g x)) = 1 := calc
    _ = tsum (fun g : L => lintegral nu (fun u : C => chi (HSMul.hSMul g (HSMul.hSMul u x)))) :=
      tsum_congr (fun g => hWCompat g x)
    _ = lintegral nu (fun u : C => tsum (fun g : L => chi (HSMul.hSMul g (HSMul.hSMul u x)))) :=
      (lintegral_tsum (fun g => (hChi.comp ((measurable_const_smul g).comp
        (hSlice x))).aemeasurable)).symm
    _ = _ := by simp [hCount]
  have hWeighted := integrable_weightedFundamentalDomain mu S hS f hf hInt hInvariant
    w hW hBound hPartition
  calc
    _ = integral mu (fun x => HSMul.hSMul (w x).toReal (f x)) := hWeighted.2.symm
    _ = _ := integral_weighted_eq_zero_of_orbitAverage nu mu
      (fun u : C => MeasurableEquiv.smul u) hAct
      (fun u => measurePreserving_smul u mu) f hf (fun x => (w x).toReal)
      hW.ennreal_toReal (fun u x => congrArg ENNReal.toReal (hWInv u x)) hWeighted.1 hMean

end OrbitCancellation

end Robin1984.GRH
