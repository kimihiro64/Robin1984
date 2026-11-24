import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Topology.Compactness.Lindelof
import Robin1984.GRH.GodementJacquetCoordinates
import Robin1984.GRH.GodementJacquetSingularOrbits
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

/-- A discrete subgroup has a Borel set containing exactly one point in each left orbit. -/
theorem exists_measurableFundamentalRepresentatives_of_discreteSubgroup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) [DiscreteTopology H] :
    Exists (fun S : Set G => And (MeasurableSet S)
      (forall x : G, ExistsUnique (fun h : H => Membership.mem S (HSMul.hSMul h x)))) := by
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
  refine Exists.intro S (And.intro hS ?_)
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

/-- Exact Borel representatives give a measurable section of the quotient
by a countable subgroup acting by left translation. -/
theorem exists_measurable_leftOrbitSection
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) [Countable H] (S : Set G) (hS : MeasurableSet S)
    (hUnique : forall x : G, ExistsUnique (fun h : H => Membership.mem S (h.val * x))) :
    let q := Quotient.mk (MulAction.orbitRel H G)
    Exists (fun f : Quotient (MulAction.orbitRel H G) -> G =>
      And (Measurable f) (Function.RightInverse f q)) := by
  let q := Quotient.mk (MulAction.orbitRel H G)
  have hRep (y : Quotient (MulAction.orbitRel H G)) : Exists (fun x : G =>
      And (Membership.mem S x) (q x = y)) := by
    refine Quotient.inductionOn y ?_
    intro x
    choose h hh using (hUnique x).exists
    refine Exists.intro (h.val * x) (And.intro hh (Quotient.sound ?_))
    exact Exists.intro h rfl
  choose f hf using hRep
  refine Exists.intro f (And.intro ?_ (fun x => (hf x).2))
  apply measurable_from_quotient.mpr
  intro B hB
  have hB' : Set.preimage (Function.comp f q) B =
      Set.iUnion (fun h : H => Set.preimage (MeasurableEquiv.mulLeft h.val) (Inter.inter S B)) := by
    ext x
    have hr := Quotient.exact (hf (q x)).2
    change Exists (fun h : H => h.val * x = f (q x)) at hr
    choose h hh using hr
    constructor
    . intro hx
      have hxB : Membership.mem B (f (q x)) := hx
      refine Set.mem_iUnion.mpr (Exists.intro h ?_)
      change And (Membership.mem S (h.val * x)) (Membership.mem B (h.val * x))
      rw [hh]
      exact And.intro (hf (q x)).1 hxB
    . intro hx
      choose g hg using Set.mem_iUnion.mp hx
      change And (Membership.mem S (g.val * x)) (Membership.mem B (g.val * x)) at hg
      have hSx : Membership.mem S (h.val * x) := by rw [hh]; exact (hf (q x)).1
      have he := (hUnique x).unique hSx hg.1
      change Membership.mem B (f (q x))
      rw [<- hh, he]
      exact hg.2
  rw [hB']
  exact MeasurableSet.iUnion (fun h => (MeasurableEquiv.mulLeft h.val).measurable (hS.inter hB))

/-- A discrete subgroup of a second-countable topological group admits
a Borel fundamental domain for left translation. -/
theorem exists_isFundamentalDomain_of_discreteSubgroup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) [DiscreteTopology H] (mu : Measure G) :
    Exists (fun S : Set G => And (MeasurableSet S) (IsFundamentalDomain H S mu)) := by
  choose S hS using exists_measurableFundamentalRepresentatives_of_discreteSubgroup H
  exact Exists.intro S (And.intro hS.1 (IsFundamentalDomain.mk' hS.1.nullMeasurableSet hS.2))

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

section QuotientTower

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- Lift an exact fundamental domain for a split subgroup to an exact
fundamental domain for its first factor. The image of the original
domain has the restricted quotient measure from that domain. -/
theorem exists_leftOrbitRestriction_of_splitSubgroup
    (U L H : Subgroup G) [Countable U] [Countable L]
    (hU : U <= H) (hL : L <= H)
    (split : Equiv (Prod U L) H)
    (hSplit : forall a : Prod U L, (split a).val = a.1.val * a.2.val)
    (mu : Measure G) (S : Set G) (hS : MeasurableSet S)
    (hUnique : forall x : G, ExistsUnique (fun h : H => Membership.mem S (h.val * x))) :
    let q := Quotient.mk (MulAction.orbitRel U G)
    let T := Set.image q S
    Exists (fun W : Set G => And (MeasurableSet W)
      (And (forall x : G, ExistsUnique (fun u : U => Membership.mem W (u.val * x)))
        (And (MeasurableSet T)
          (((mu.restrict W).map q).restrict T = (mu.restrict S).map q)))) := by
  let q := Quotient.mk (MulAction.orbitRel U G)
  let T := Set.image q S
  let A (l : L) : Set G := Set.preimage (MeasurableEquiv.mulLeft l.val).symm S
  let W : Set G := Set.iUnion A
  have hW' (x : G) : Membership.mem W x <->
      Exists (fun l : L => Membership.mem S (Inv.inv l.val * x)) :=
    Set.mem_iUnion
  have hW : MeasurableSet W := MeasurableSet.iUnion (fun l => (MeasurableEquiv.mulLeft l.val).symm.measurable hS)
  have hSU : forall x : G, ExistsUnique (fun u : U => Membership.mem W (u.val * x)) := by
    intro x
    have h := hUnique x
    change Exists (fun h : H => And (Membership.mem S (h.val * x))
      (forall v : H, Membership.mem S (v.val * x) -> v = h)) at h
    choose h hh using h
    let a := split.symm (Inv.inv h)
    have ha : a.1.val * a.2.val = Inv.inv h.val := by
      rw [<- hSplit, show split a = Inv.inv h from split.apply_symm_apply _]
      rfl
    refine Exists.intro (Inv.inv a.1) (And.intro ?_ ?_)
    . apply (hW' _).mpr
      refine Exists.intro a.2 ?_
      change Membership.mem S (Inv.inv a.2.val * (Inv.inv a.1.val * x))
      have he : Inv.inv a.2.val * (Inv.inv a.1.val * x) = h.val * x := calc
        _ = Inv.inv (a.1.val * a.2.val) * x := by rw [mul_inv_rev, mul_assoc]
        _ = _ := by rw [ha, inv_inv]
      rw [he]
      exact hh.1
    . intro v hv
      choose l hl using (hW' _).mp hv
      let b : H := Subtype.mk (Inv.inv l.val * v.val) (H.mul_mem (H.inv_mem (hL l.property)) (hU v.property))
      have hb : b = h := hh.2 b (by
        change Membership.mem S ((Inv.inv l.val * v.val) * x)
        rw [mul_assoc]
        exact hl)
      have hc : split (Prod.mk (Inv.inv v) l) = Inv.inv h := by
        apply Subtype.ext
        rw [hSplit]
        change Inv.inv v.val * l.val = Inv.inv h.val
        have hd := congrArg (fun a : H => Inv.inv a.val) hb
        change Inv.inv (Inv.inv l.val * v.val) = Inv.inv h.val at hd
        simpa only [mul_inv_rev, inv_inv] using hd
      have hPair : Prod.mk (Inv.inv v) l = a :=
        split.injective (hc.trans (split.apply_symm_apply _).symm)
      have hu : Inv.inv v = a.1 := congrArg Prod.fst hPair
      simpa only [inv_inv] using congrArg Inv.inv hu
  have hSub : S.Subset W := by
    intro x hx
    apply (hW' x).mpr
    exact Exists.intro (1 : L) (by simpa using hx)
  have hq : Measurable q := fun _ hs => measurableSet_quotient.mp hs
  have hPre : Set.preimage q T =
      Set.iUnion (fun u : U => Set.preimage (MeasurableEquiv.mulLeft u.val) S) := by
    ext x
    constructor
    . intro hx
      change Membership.mem (Set.image q S) (q x) at hx
      choose y hy using hx
      have hr := Quotient.exact hy.2
      change Exists (fun u : U => u.val * x = y) at hr
      choose u hu using hr
      exact Set.mem_iUnion.mpr (Exists.intro u (by
        change Membership.mem S (u.val * x)
        rw [hu]
        exact hy.1))
    . intro hx
      choose u hu using Set.mem_iUnion.mp hx
      change Membership.mem (Set.image q S) (q x)
      exact Exists.intro (u.val * x) (And.intro hu (Quotient.sound (Exists.intro u rfl)))
  have hT : MeasurableSet T := measurableSet_quotient.mpr (by
    rw [hPre]
    exact MeasurableSet.iUnion (fun u => (MeasurableEquiv.mulLeft u.val).measurable hS))
  have hInj : Set.InjOn q W := by
    intro x hx y hy hxy
    have hr := Quotient.exact hxy
    change Exists (fun u : U => u.val * y = x) at hr
    choose u hu using hr
    have huW : Membership.mem W (u.val * y) := by rw [hu]; exact hx
    have hOne : Membership.mem W ((1 : U).val * y) := by simpa using hy
    have hEq := (hSU y).unique huW hOne
    simpa [hEq] using hu.symm
  have hCut : Inter.inter (Set.preimage q T) W = S := by
    ext x
    constructor
    . intro hx
      have h := hx.1
      change Membership.mem (Set.image q S) (q x) at h
      choose y hy using h
      have he := hInj (hSub hy.1) hx.2 hy.2
      rw [<- he]
      exact hy.1
    . intro hx
      exact And.intro (Exists.intro x (And.intro hx rfl)) (hSub hx)
  refine Exists.intro W (And.intro hW (And.intro hSU (And.intro hT ?_)))
  ext B hB
  change ((mu.restrict W).map q).restrict T B = (mu.restrict S).map q B
  rw [Measure.restrict_apply hB, Measure.map_apply hq (hB.inter hT), Measure.map_apply hq hB,
    Measure.restrict_apply (hq (hB.inter hT)), Measure.restrict_apply (hq hB),
    Set.preimage_inter, Set.inter_assoc, hCut]

end QuotientTower

section LeviAction

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- The action of an element of a normalizing subgroup on rational unipotent cosets. -/
def leftOrbitNormalizerSubgroupEquiv (U L : Subgroup G)
    (hNorm : forall (l : L) (u : U), Membership.mem U (l.val * u.val * Inv.inv l.val))
    (l : L) : MeasurableEquiv (LeftOrbit U) (LeftOrbit U) :=
  leftOrbitNormalizerEquiv U l.val (hNorm l) (fun u => by
    simpa only [Subgroup.coe_inv, inv_inv] using hNorm (Inv.inv l) u)

/-- The normalizer action on the quotient by the first subgroup. -/
@[instance_reducible]
def leftOrbitNormalizerMulAction (U L : Subgroup G)
    (hNorm : forall (l : L) (u : U), Membership.mem U (l.val * u.val * Inv.inv l.val)) :
    MulAction L (LeftOrbit U) where
  smul l x := leftOrbitNormalizerSubgroupEquiv U L hNorm l x
  one_smul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro y
    change Quotient.mk (MulAction.orbitRel U G) ((1 : G) * y) =
      Quotient.mk (MulAction.orbitRel U G) y
    rw [one_mul]
  mul_smul := by
    intro l k x
    refine Quotient.inductionOn x ?_
    intro y
    change Quotient.mk (MulAction.orbitRel U G) ((l.val * k.val) * y) =
      Quotient.mk (MulAction.orbitRel U G) (l.val * (k.val * y))
    rw [mul_assoc]

/-- The image of the rational stabilizer fundamental domain is an
exact fundamental domain for the Levi action on unipotent cosets. -/
theorem existsUnique_leftOrbitNormalizerSubgroup_imageDomain
    (U L H : Subgroup G)
    (hNorm : forall (l : L) (u : U), Membership.mem U (l.val * u.val * Inv.inv l.val))
    (split : Equiv (Prod U L) H)
    (hSplit : forall a : Prod U L, (split a).val = a.1.val * a.2.val)
    (S : Set G)
    (hUnique : forall x : G, ExistsUnique (fun h : H => Membership.mem S (h.val * x))) :
    let T := Set.image (Quotient.mk (MulAction.orbitRel U G)) S
    forall x : LeftOrbit U, ExistsUnique
      (fun l : L => Membership.mem T (leftOrbitNormalizerSubgroupEquiv U L hNorm l x)) := by
  let q := Quotient.mk (MulAction.orbitRel U G)
  let T := Set.image q S
  change forall x : LeftOrbit U, ExistsUnique
    (fun l : L => Membership.mem T (leftOrbitNormalizerSubgroupEquiv U L hNorm l x))
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  have h := hUnique y
  change Exists (fun a : H => And (Membership.mem S (a.val * y))
    (forall b : H, Membership.mem S (b.val * y) -> b = a)) at h
  choose a ha using h
  let p := split.symm a
  have hp : p.1.val * p.2.val = a.val := by
    rw [<- hSplit, show split p = a from split.apply_symm_apply _]
  refine Exists.intro p.2 (And.intro ?_ ?_)
  . change Membership.mem T (q (p.2.val * y))
    refine Exists.intro (a.val * y) (And.intro ha.1 (Quotient.sound ?_))
    refine Exists.intro p.1 ?_
    change p.1.val * (p.2.val * y) = a.val * y
    rw [<- mul_assoc, hp]
  . intro l hl
    change Membership.mem T (q (l.val * y)) at hl
    choose z hz using hl
    have hr := Quotient.exact hz.2
    change Exists (fun u : U => u.val * (l.val * y) = z) at hr
    choose u hu using hr
    let b := split (Prod.mk u l)
    have hb : b.val * y = z := by
      change (split (Prod.mk u l)).val * y = z
      rw [hSplit, mul_assoc]
      exact hu
    have hd : b = a := ha.2 b (by rw [hb]; exact hz.1)
    have hpair : Prod.mk u l = p :=
      split.injective (hd.trans (split.apply_symm_apply a).symm)
    exact congrArg Prod.snd hpair

end LeviAction

section UnipotentHaar

variable (K : Type*) [Field K] [NumberField K] (r k : Nat)

/-- The compact group of adelic upper unipotent coordinates modulo rational coordinates. -/
abbrev GodementJacquetUnipotentClassGroup :=
  Multiplicative (HasQuotient.Quotient
    (Matrix (Fin r) (Fin k) (AdeleRing (RingOfIntegers K) K))
    (godementJacquetPrincipalMatrixBlock K r k))

/-- The compact unipotent quotient admits a bi-invariant Haar probability measure. -/
theorem exists_godementJacquetUnipotentClassHaarProbability
    [MeasurableSpace (GodementJacquetUnipotentClassGroup K r k)]
    [BorelSpace (GodementJacquetUnipotentClassGroup K r k)] :
    Exists (fun mu : Measure (GodementJacquetUnipotentClassGroup K r k) =>
      And mu.IsHaarMeasure (And (IsProbabilityMeasure mu) mu.IsMulRightInvariant)) := by
  let A := AdeleRing (RingOfIntegers K) K
  let M := Matrix (Fin r) (Fin k) A
  let H := godementJacquetPrincipalMatrixBlock K r k
  let Q := HasQuotient.Quotient M H
  let C := GodementJacquetUnipotentClassGroup K r k
  let : IsClosed (H : Set M) := isClosed_godementJacquetPrincipalMatrixBlock K r k
  let : T2Space Q := inferInstance
  let : T2Space C := show T2Space Q from inferInstance
  let : CompactSpace Q := compactSpace_godementJacquetMatrixBlockModuloPrincipal K r k
  let : CompactSpace C := inferInstanceAs (CompactSpace (Multiplicative Q))
  let S : TopologicalSpace.PositiveCompacts C :=
    { carrier := Set.univ
      isCompact' := isCompact_univ
      interior_nonempty' := by rw [interior_univ]; exact Set.univ_nonempty }
  let mu := Measure.haarMeasure S
  let : mu.IsHaarMeasure := inferInstance
  have hMass : mu (Set.univ : Set C) = 1 :=
    (Measure.haarMeasure_self : mu (S : Set C) = 1)
  let : IsProbabilityMeasure mu := { measure_univ := hMass }
  have hRight : mu.IsMulRightInvariant := by
    constructor
    intro u
    have hEq : (fun v : C => v * u) = (fun v : C => u * v) :=
      funext (fun v => mul_comm v u)
    rw [hEq]
    exact map_mul_left_eq_self mu u
  exact Exists.intro mu (And.intro inferInstance (And.intro inferInstance hRight))

private abbrev LeviAdeles := AdeleRing (RingOfIntegers K) K
private abbrev UnipotentBlock := Matrix (Fin r) (Fin k) (LeviAdeles K)
private abbrev UnipotentQuotient :=
  HasQuotient.Quotient (UnipotentBlock K r k) (godementJacquetPrincipalMatrixBlock K r k)

private def blockLeviAddEquiv (V : Matrix.GeneralLinearGroup (Fin k) K) :
    AddEquiv (UnipotentBlock K r k) (UnipotentBlock K r k) :=
  let T := Matrix.GeneralLinearGroup.map (algebraMap K (LeviAdeles K)) V
  { toFun := fun B => B * T.val
    invFun := fun B => B * T.inv
    left_inv := fun B => by
      change (B * T.val) * T.inv = B
      rw [Matrix.mul_assoc, T.val_inv, Matrix.mul_one]
    right_inv := fun B => by
      change (B * T.inv) * T.val = B
      rw [Matrix.mul_assoc, T.inv_val, Matrix.mul_one]
    map_add' := fun B D => Matrix.add_mul B D T.val }

private theorem rightMul_mem_principalBlock (D : Matrix (Fin k) (Fin k) K)
    (B : UnipotentBlock K r k) (hB : Membership.mem (godementJacquetPrincipalMatrixBlock K r k) B) :
    Membership.mem (godementJacquetPrincipalMatrixBlock K r k) (B * D.map (algebraMap K (LeviAdeles K))) := by
  choose P hP using (mem_godementJacquetPrincipalMatrixBlock K r k B).mp hB
  apply (mem_godementJacquetPrincipalMatrixBlock K r k _).mpr
  refine Exists.intro (P * D) ?_
  rw [<- hP]
  apply Matrix.ext
  intro i j
  simp [Matrix.mul_apply]

private theorem blockLeviAddEquiv_map (V : Matrix.GeneralLinearGroup (Fin k) K) :
    (godementJacquetPrincipalMatrixBlock K r k).map (blockLeviAddEquiv K r k V).toAddMonoidHom =
      godementJacquetPrincipalMatrixBlock K r k := by
  let H := godementJacquetPrincipalMatrixBlock K r k
  let e := blockLeviAddEquiv K r k V
  change H.map e.toAddMonoidHom = H
  apply le_antisymm
  . intro B hB
    choose A hA using AddSubgroup.mem_map.mp hB
    rw [<- hA.2]
    exact rightMul_mem_principalBlock K r k V.val A hA.1
  . intro B hB
    apply AddSubgroup.mem_map.mpr
    exact Exists.intro (e.symm B) (And.intro
      (rightMul_mem_principalBlock K r k V.inv B hB) (e.apply_symm_apply B))

private def quotientBlockLeviAddEquiv (V : Matrix.GeneralLinearGroup (Fin k) K) :
    AddEquiv (UnipotentQuotient K r k) (UnipotentQuotient K r k) :=
  let H := godementJacquetPrincipalMatrixBlock K r k
  QuotientAddGroup.congr H H (blockLeviAddEquiv K r k V) (blockLeviAddEquiv_map K r k V)

/-- Right multiplication by a rational Levi block descends to an
automorphism of the compact unipotent quotient. -/
def godementJacquetUnipotentClassLeviEquiv (V : Matrix.GeneralLinearGroup (Fin k) K) :
    MulEquiv (GodementJacquetUnipotentClassGroup K r k) (GodementJacquetUnipotentClassGroup K r k) :=
  let e := quotientBlockLeviAddEquiv K r k V
  { toFun := fun x => Multiplicative.ofAdd (e (Multiplicative.toAdd x))
    invFun := fun x => Multiplicative.ofAdd (e.symm (Multiplicative.toAdd x))
    left_inv := fun x => congrArg Multiplicative.ofAdd (e.symm_apply_apply (Multiplicative.toAdd x))
    right_inv := fun x => congrArg Multiplicative.ofAdd (e.apply_symm_apply (Multiplicative.toAdd x))
    map_mul' := fun x y => congrArg Multiplicative.ofAdd
      (map_add e (Multiplicative.toAdd x) (Multiplicative.toAdd y)) }

/-- The Levi automorphism preserves normalized Haar measure on the compact quotient. -/
theorem measurePreserving_godementJacquetUnipotentClassLeviEquiv
    (V : Matrix.GeneralLinearGroup (Fin k) K)
    [MeasurableSpace (GodementJacquetUnipotentClassGroup K r k)]
    [BorelSpace (GodementJacquetUnipotentClassGroup K r k)]
    (mu : Measure (GodementJacquetUnipotentClassGroup K r k))
    [mu.IsHaarMeasure] [IsProbabilityMeasure mu] :
    MeasurePreserving (godementJacquetUnipotentClassLeviEquiv K r k V) mu mu := by
  let C := GodementJacquetUnipotentClassGroup K r k
  let H := godementJacquetPrincipalMatrixBlock K r k
  let : IsClosed (H : Set (UnipotentBlock K r k)) :=
    isClosed_godementJacquetPrincipalMatrixBlock K r k
  let : T2Space C := show T2Space (UnipotentQuotient K r k) from inferInstance
  let : CompactSpace C := show CompactSpace (UnipotentQuotient K r k) from
    compactSpace_godementJacquetMatrixBlockModuloPrincipal K r k
  let e := godementJacquetUnipotentClassLeviEquiv K r k V
  let T := Matrix.GeneralLinearGroup.map (algebraMap K (LeviAdeles K)) V
  have hC : Continuous e := by
    change Continuous (quotientBlockLeviAddEquiv K r k V)
    apply (QuotientAddGroup.isQuotientMap_mk H).continuous_iff.mpr
    exact QuotientAddGroup.continuous_mk.comp
      (continuous_id.matrix_mul (continuous_const (y := T.val)))
  exact MonoidHom.measurePreserving (f := e.toMonoidHom) hC e.surjective rfl

end UnipotentHaar

section UnipotentRepresentatives

variable (r k : Nat)

/-- The principal additive lattice in a rectangular adelic matrix block is discrete. -/
theorem discreteTopology_godementJacquetPrincipalMatrixBlock :
    DiscreteTopology (godementJacquetPrincipalMatrixBlock K r k) := by
  let H := godementJacquetPrincipalMatrixBlock K r k
  let H0 := AdeleRing.principalSubgroup (RingOfIntegers K) K
  let e (X : H) (i : Fin r) (j : Fin k) : H0 := Subtype.mk (X.val i j) (by
    choose P hP using (mem_godementJacquetPrincipalMatrixBlock K r k X.val).mp X.property
    exact Exists.intro (P i j) (congrArg (fun M : UnipotentBlock K r k => M i j) hP))
  have he : Function.Injective e := by
    intro X Y h
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    exact congrArg (fun M : Fin r -> Fin k -> H0 => (M i j).val) h
  have hVal : Continuous (fun X : H => X.val) := continuous_subtype_val
  have hCoordinates (i : Fin r) (j : Fin k) : Continuous (fun X : H => (e X i j).val) :=
    (continuous_apply j).comp ((continuous_apply i).comp hVal)
  have hC : Continuous e := continuous_pi (fun i => continuous_pi (fun j =>
    (hCoordinates i j).subtype_mk (fun X => (e X i j).property)))
  let : DiscreteTopology H0 := discreteTopology_principalAdeles K
  let : DiscreteTopology (Fin r -> Fin k -> H0) := inferInstance
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro X
  have hEq : Set.preimage e (Singleton.singleton (e X)) = Singleton.singleton X := by
    ext Y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, he.eq_iff]
  rw [<- hEq]
  exact (isOpen_discrete _).preimage hC

private theorem sectionQuotient_isLocalHomeomorph :
    IsLocalHomeomorph (QuotientAddGroup.mk
      (s := godementJacquetPrincipalMatrixBlock K r k)) := by
  let H := godementJacquetPrincipalMatrixBlock K r k
  have hH : IsDiscrete (H : Set (UnipotentBlock K r k)) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr (discreteTopology_godementJacquetPrincipalMatrixBlock K r k)
  exact (H.isAddQuotientCoveringMap_of_comm hH).isCoveringMap.isLocalHomeomorph

/-- The additive unipotent quotient has a relatively compact Borel set of
representatives, with exactly one representative of each class. -/
theorem exists_godementJacquetUnipotentCompactSection
    [MeasurableSpace (UnipotentBlock K r k)] [BorelSpace (UnipotentBlock K r k)]
    [MeasurableSpace (UnipotentQuotient K r k)] [BorelSpace (UnipotentQuotient K r k)] :
    let q := QuotientAddGroup.mk' (godementJacquetPrincipalMatrixBlock K r k)
    Exists (fun S : Set (UnipotentBlock K r k) => Exists (fun C : Set (UnipotentBlock K r k) =>
      And (IsCompact C) (And (S <= C)
        (And (MeasurableSet S) (And (Set.InjOn q S) (Set.image q S = Set.univ)))))) := by
  let V := InfiniteAdeleRing K
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let e : Homeomorph V (mixedEmbedding.mixedSpace K) :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
      continuous_toFun := continuous_heckeInfiniteAdele_mixedSpace (K := K)
      continuous_invFun := continuous_heckeInfiniteAdele_mixedSpace_symm K }
  let : LocallyCompactSpace V := e.isClosedEmbedding.locallyCompactSpace
  let : LocallyCompactSpace F := locallyCompactSpace_heckeFiniteAdeles
  let : LocallyCompactSpace (LeviAdeles K) :=
    inferInstanceAs (LocallyCompactSpace (Prod V F))
  let : LocallyCompactSpace (UnipotentBlock K r k) :=
    inferInstanceAs (LocallyCompactSpace (Fin r -> Fin k -> LeviAdeles K))
  let H := godementJacquetPrincipalMatrixBlock K r k
  let : CompactSpace (UnipotentQuotient K r k) :=
    compactSpace_godementJacquetMatrixBlockModuloPrincipal K r k
  have hQ := sectionQuotient_isLocalHomeomorph K r k
  exact exists_measurableSectionSet_of_compactLocalHomeomorph (QuotientAddGroup.mk (s := H))
    QuotientAddGroup.continuous_mk QuotientAddGroup.isOpenMap_coe Quotient.mk_surjective hQ

/-- A surjective local homeomorphism onto a compact space admits a measurable section. -/
private theorem exists_measurable_section_of_compact_localHomeomorph
    {X Y : Type*} [Nonempty X]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (q : X -> Y) (hSurj : Function.Surjective q) (hLocal : IsLocalHomeomorph q) :
    Exists (fun f : Y -> X => And (Measurable f) (Function.RightInverse f q)) := by
  classical
  choose E hE hQ using hLocal
  let V (x : X) := (E x).target
  have hV (x : X) : IsOpen (V x) := (E x).open_target
  have hCover : (Set.univ : Set Y) <= Set.iUnion V := by
    intro y _
    choose x hx using hSurj y
    refine Set.mem_iUnion.mpr (Exists.intro x ?_)
    rw [<- hx, hQ x]
    exact (E x).map_source (hE x)
  choose F hF using isCompact_univ.elim_finite_subcover V hV hCover
  have hFinite : forall D : Finset X, Exists (fun f : Y -> X => And (Measurable f)
      (forall x, Membership.mem D x -> forall y, Membership.mem (V x) y -> q (f y) = y)) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      exact Exists.intro (fun _ => Classical.choice (inferInstance : Nonempty X))
        (And.intro measurable_const (fun _ h => False.elim (Finset.notMem_empty _ h)))
    | insert x D hx ih =>
      choose f hf using ih
      let g (y : Y) := if hy : Membership.mem (V x) y then (E x).symm y else f y
      have hInv : Measurable (fun y : V x => (E x).symm y) :=
        (continuousOn_iff_continuous_domRestrict.mp (E x).continuousOn_symm).measurable
      have hG : Measurable g := hInv.dite (hf.1.comp measurable_subtype_coe) (hV x).measurableSet
      refine Exists.intro g (And.intro hG ?_)
      intro z hz y hy
      by_cases h : Membership.mem (V x) y
      . rw [show g y = (E x).symm y from dif_pos h, hQ x]
        exact (E x).right_inv h
      . have hzD : Membership.mem D z := by
          rcases Finset.mem_insert.mp hz with he | hzD
          . rw [he] at hy
            exact False.elim (h hy)
          . exact hzD
        rw [show g y = f y from dif_neg h]
        exact hf.2 z hzD y hy
  choose s hs using hFinite F
  refine Exists.intro s (And.intro hs.1 ?_)
  intro y
  choose x hx using Set.mem_iUnion.mp (hF (Set.mem_univ y))
  choose hxF hy using Set.mem_iUnion.mp hx
  exact hs.2 x hxF y hy

/-- The compact unipotent quotient has a measurable representative in the adelic matrix block. -/
theorem exists_measurable_godementJacquetUnipotentRepresentative
    [MeasurableSpace (UnipotentBlock K r k)] [BorelSpace (UnipotentBlock K r k)]
    [MeasurableSpace (UnipotentQuotient K r k)] [BorelSpace (UnipotentQuotient K r k)] :
    let q := QuotientAddGroup.mk' (godementJacquetPrincipalMatrixBlock K r k)
    Exists (fun f : UnipotentQuotient K r k -> UnipotentBlock K r k =>
      And (Measurable f) (Function.RightInverse f q)) := by
  let : CompactSpace (UnipotentQuotient K r k) :=
    compactSpace_godementJacquetMatrixBlockModuloPrincipal K r k
  exact exists_measurable_section_of_compact_localHomeomorph _
    Quotient.mk_surjective (sectionQuotient_isLocalHomeomorph K r k)

end UnipotentRepresentatives

section AdditiveQuotientAction

variable {A G : Type*} [AddCommGroup A] [Group G]
variable [MeasurableSpace G] [MeasurableMul G]

private abbrev AddClasses (D : AddSubgroup A) := HasQuotient.Quotient A D

/-- A group of additive translations which is trivial on the rational
orbits descends to an action by the quotient of its rational subgroup. -/
theorem exists_leftOrbitAddQuotientMulAction
    (D : AddSubgroup A) (U : Subgroup G) (alpha : MonoidHom (Multiplicative A) G)
    (hNorm : forall (a : Multiplicative A) (u : U),
      Membership.mem U (alpha a * u.val * Inv.inv (alpha a)))
    (hRat : forall d : A, Membership.mem D d ->
      Membership.mem U (alpha (Multiplicative.ofAdd d))) :
    Exists (fun act : MulAction (Multiplicative (AddClasses D)) (LeftOrbit U) =>
      forall (a : A) (g : G),
        act.smul (Multiplicative.ofAdd (QuotientAddGroup.mk' D a))
          (Quotient.mk (MulAction.orbitRel U G) g) =
        Quotient.mk (MulAction.orbitRel U G) (alpha (Multiplicative.ofAdd a) * g)) := by
  let q := Quotient.mk (MulAction.orbitRel U G)
  let E (a : Multiplicative A) :=
    leftOrbitNormalizerEquiv U (alpha a) (hNorm a) (fun u => by
      simpa only [map_inv, inv_inv] using hNorm (Inv.inv a) u)
  let f : MonoidHom (Multiplicative A) (Equiv.Perm (LeftOrbit U)) :=
    { toFun := fun a => (E a).toEquiv
      map_one' := by
        ext x
        refine Quotient.inductionOn x ?_
        intro g
        change q (alpha 1 * g) = q g
        rw [map_one, one_mul]
      map_mul' := by
        intro a b
        ext x
        refine Quotient.inductionOn x ?_
        intro g
        change q (alpha (a * b) * g) = q (alpha a * (alpha b * g))
        rw [map_mul, mul_assoc] }
  let F := MonoidHom.toAdditiveRight f
  have hker : D <= F.ker := by
    intro d hd
    change F d = 0
    change f (Multiplicative.ofAdd d) = (1 : Equiv.Perm (LeftOrbit U))
    ext x
    refine Quotient.inductionOn x ?_
    intro g
    change q (alpha (Multiplicative.ofAdd d) * g) = q g
    exact Quotient.sound (Exists.intro
      (Subtype.mk (alpha (Multiplicative.ofAdd d)) (hRat d hd)) rfl)
  let lifted := QuotientAddGroup.lift D F hker
  let fQ := AddMonoidHom.toMultiplicativeLeft lifted
  let act : MulAction (Multiplicative (AddClasses D)) (LeftOrbit U) :=
    { smul := fun a x => fQ a x
      one_smul := by
        intro x
        change fQ 1 x = x
        rw [map_one]
        rfl
      mul_smul := by
        intro a b x
        change fQ (a * b) x = fQ a (fQ b x)
        rw [map_mul]
        rfl }
  refine Exists.intro act ?_
  intro a g
  change (Additive.toMul (lifted (QuotientAddGroup.mk' D a))) (q g) = _
  rw [show lifted (QuotientAddGroup.mk' D a) = F a from rfl]
  rfl

omit [MeasurableMul G] in
/-- Measurable choices of representatives give joint measurability of
the descended translations. -/
theorem measurable_leftOrbitAddQuotientMulAction
    {D : AddSubgroup A} {U : Subgroup G} {alpha : MonoidHom (Multiplicative A) G}
    [MeasurableSpace A] [MeasurableSpace (AddClasses D)]
    (hAlpha : Measurable (fun a : A => alpha (Multiplicative.ofAdd a)))
    (hMul : Measurable (fun p : Prod G G => p.1 * p.2))
    (act : MulAction (Multiplicative (AddClasses D)) (LeftOrbit U))
    (hAct : forall (a : A) (g : G),
      act.smul (Multiplicative.ofAdd (QuotientAddGroup.mk' D a))
        (Quotient.mk (MulAction.orbitRel U G) g) =
      Quotient.mk (MulAction.orbitRel U G) (alpha (Multiplicative.ofAdd a) * g))
    (sA : AddClasses D -> A) (hsA : Measurable sA)
    (hrA : Function.RightInverse sA (QuotientAddGroup.mk' D))
    (sG : LeftOrbit U -> G) (hsG : Measurable sG)
    (hrG : Function.RightInverse sG (Quotient.mk (MulAction.orbitRel U G))) :
    Measurable (fun p : Prod (AddClasses D) (LeftOrbit U) =>
      act.smul (Multiplicative.ofAdd p.1) p.2) := by
  let q := Quotient.mk (MulAction.orbitRel U G)
  have hq : Measurable q := fun _ hs => measurableSet_quotient.mp hs
  have hProduct : Measurable (fun p : Prod (AddClasses D) (LeftOrbit U) =>
      alpha (Multiplicative.ofAdd (sA p.1)) * sG p.2) :=
    hMul.comp ((hAlpha.comp (hsA.comp measurable_fst)).prodMk (hsG.comp measurable_snd))
  have he : (fun p : Prod (AddClasses D) (LeftOrbit U) =>
      act.smul (Multiplicative.ofAdd p.1) p.2) =
      (fun p => q (alpha (Multiplicative.ofAdd (sA p.1)) * sG p.2)) := by
    funext p
    have hp := hAct (sA p.1) (sG p.2)
    rw [hrA p.1, hrG p.2] at hp
    exact hp
  rw [he]
  exact hq.comp hProduct

/-- Each descended translation preserves the quotient of left Haar measure. -/
theorem measurePreserving_leftOrbitAddQuotientMulAction
    {D : AddSubgroup A} {U : Subgroup G} [Countable U]
    (alpha : MonoidHom (Multiplicative A) G)
    (hNorm : forall (a : Multiplicative A) (u : U),
      Membership.mem U (alpha a * u.val * Inv.inv (alpha a)))
    (act : MulAction (Multiplicative (AddClasses D)) (LeftOrbit U))
    (hAct : forall (a : A) (g : G),
      act.smul (Multiplicative.ofAdd (QuotientAddGroup.mk' D a))
        (Quotient.mk (MulAction.orbitRel U G) g) =
      Quotient.mk (MulAction.orbitRel U G) (alpha (Multiplicative.ofAdd a) * g))
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (W : Set G) (hW : MeasurableSet W)
    (hUnique : forall g : G, ExistsUnique (fun u : U => Membership.mem W (u.val * g)))
    (c : Multiplicative (AddClasses D)) :
    let nu := (mu.restrict W).map (Quotient.mk (MulAction.orbitRel U G))
    MeasurePreserving (act.smul c) nu nu := by
  choose a ha using QuotientAddGroup.mk'_surjective D (Multiplicative.toAdd c)
  have hc : c = Multiplicative.ofAdd (QuotientAddGroup.mk' D a) :=
    (congrArg Multiplicative.ofAdd ha).symm
  let t := Multiplicative.ofAdd a
  have hi (u : U) : Membership.mem U (Inv.inv (alpha t) * u.val * alpha t) := by
    simpa only [map_inv, inv_inv] using hNorm (Inv.inv t) u
  let E := leftOrbitNormalizerEquiv U (alpha t) (hNorm t) hi
  have he : act.smul c = (E : LeftOrbit U -> LeftOrbit U) := by
    funext x
    refine Quotient.inductionOn x ?_
    intro g
    rw [hc]
    exact hAct a g
  rw [he]
  exact measurePreserving_leftOrbitNormalizerEquiv U mu W hW hUnique
    (alpha t) (hNorm t) hi

end AdditiveQuotientAction

section PrincipalRankTransport

variable {K : Type*} [Field K] [NumberField K] {n r k : Nat}

private abbrev AdelicScalars (K : Type*) [Field K] [NumberField K] := AdeleRing (RingOfIntegers K) K
private abbrev DeterminantNormOneGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker
private abbrev RationalRankBlockGL (K : Type*) [Field K] (r k : Nat) :=
  Matrix.GeneralLinearGroup (Sum (Fin r) (Fin k)) K

/-- The entrywise principal embedding on the determinant-norm-one group is faithful. -/
theorem adelicPrincipalDeterminantOne_injective :
    Function.Injective (adelicPrincipalDeterminantOne K n) := by
  intro g h he
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply AdeleRing.algebraMap_injective (RingOfIntegers K) K
  exact congrArg (fun x : DeterminantNormOneGroup K n => x.val.val i j) he

/-- The rational rank coordinates, embedded in the norm-one adelic group. -/
def godementJacquetPrincipalRankTransport
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k))) (a : Matrix.GeneralLinearGroup (Fin n) K) :
    MonoidHom (RationalRankBlockGL K r k) (DeterminantNormOneGroup K n) :=
  (adelicPrincipalDeterminantOne K n).comp (godementJacquetRankTransport e a).toMonoidHom

theorem godementJacquetPrincipalRankTransport_injective
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k))) (a : Matrix.GeneralLinearGroup (Fin n) K) :
    Function.Injective (godementJacquetPrincipalRankTransport e a) :=
  adelicPrincipalDeterminantOne_injective.comp (godementJacquetRankTransport e a).injective

/-- The transported subgroup consists of exactly the rational elements
of the adelic group fixing the given rational matrix on the left. -/
theorem mem_godementJacquetPrincipalSingularStabilizer_iff
    (P : Matrix (Fin n) (Fin n) K) (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a b : Matrix.GeneralLinearGroup (Fin n) K)
    (h : a.val * P * b.val = (godementJacquetRankProjection K r k).submatrix e e)
    (x : DeterminantNormOneGroup K n) :
    Membership.mem ((godementJacquetProjectionStabilizer K r k).map
      (godementJacquetPrincipalRankTransport e a)) x <->
    And (Membership.mem (adelicPrincipalDeterminantOne K n).range x)
      (x.val.val * P.map (algebraMap K (AdelicScalars K)) = P.map (algebraMap K (AdelicScalars K))) := by
  let f := algebraMap K (AdelicScalars K)
  let FM : RingHom (Matrix (Fin n) (Fin n) K) (Matrix (Fin n) (Fin n) (AdelicScalars K)) :=
    RingHom.mapMatrix f
  let T := godementJacquetRankTransport e a
  let principal := adelicPrincipalDeterminantOne K n
  have hInj : Function.Injective FM := by
    intro g z hg
    apply Matrix.ext
    intro i j
    apply AdeleRing.algebraMap_injective (RingOfIntegers K) K
    exact congrArg (fun X : Matrix (Fin n) (Fin n) (AdelicScalars K) => X i j) hg
  have hFix (z : Matrix.GeneralLinearGroup (Fin n) K) :
      (principal z).val.val * P.map f = P.map f <-> z.val * P = P := by
    change FM z.val * FM P = FM P <-> _
    rw [<- map_mul, hInj.eq_iff]
  constructor
  . intro hx
    choose u hu using hx
    have hu' : principal (T u) = x := hu.2
    have hFixP := (godementJacquetRankTransport_mul_eq_iff P e a b h u).mpr hu.1
    refine And.intro (Exists.intro (T u) hu') ?_
    rw [<- hu']
    exact (hFix (T u)).mpr hFixP
  . intro hx
    choose z hz using hx.1
    have hFixP : z.val * P = P := (hFix z).mp (by rw [hz]; exact hx.2)
    let u := T.symm z
    have hu : T u = z := T.apply_symm_apply z
    refine Exists.intro u (And.intro ?_ ?_)
    . apply (godementJacquetRankTransport_mul_eq_iff P e a b h u).mp
      change (T u).val * P = P
      rwa [hu]
    . change principal (T u) = x
      rwa [hu]

/-- Subgroups transported from rational rank coordinates remain discrete. -/
theorem discreteTopology_godementJacquetPrincipalRankSubgroup
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a : Matrix.GeneralLinearGroup (Fin n) K) (S : Subgroup (RationalRankBlockGL K r k)) :
    DiscreteTopology (S.map (godementJacquetPrincipalRankTransport e a)) := by
  apply SetLike.isDiscrete_iff_discreteTopology.mp
  have hP : IsDiscrete (SetLike.coe (adelicPrincipalDeterminantOne K n).range) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr (discreteTopology_adelicPrincipalDeterminantOne K n)
  apply hP.mono
  intro g hg
  choose u hu using hg
  exact Exists.intro ((godementJacquetRankTransport e a) u) hu.2

end PrincipalRankTransport

end Robin1984.GRH
