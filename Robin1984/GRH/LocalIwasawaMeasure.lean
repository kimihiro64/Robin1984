import Mathlib.GroupTheory.Coset.Defs
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Bases

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The normalized local Haar integral in Goldfeld and Jacquet, Automorphic Representations and L-functions for GL(n), Section 2.4.
- Formalization note: Transfers integrability and the integral of a right-invariant complex kernel from G = BK to B with normalized left Haar measures.
- PROVENANCE-END
-/

/-!
# Normalized Haar integration along an Iwasawa decomposition

A right-K-invariant kernel can be integrated over its left cosets.
When G = BK, the same cosets compute the integral on B.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open MeasureTheory TopologicalSpace
open scoped Pointwise

private theorem eqOn_leftCoset_of_rightInvariant
    {G X : Type*} [Group G] (K : Subgroup G) (r : G) (f : G -> X)
    (hRight : forall g k : G, Membership.mem K k -> f (g * k) = f g) :
    Set.EqOn f (fun _ => f r) (SMul.smul r (K : Set G)) := by
  intro g hg
  change Exists (fun k : G => And (Membership.mem K k) (r * k = g)) at hg
  choose k hk using hg
  rw [<- hk.2]
  exact hRight r k hk.1

/-- The nonnegative integral of a right-invariant kernel is the sum
of its values at representatives of the cosets of a mass-one subgroup. -/
theorem lintegral_rightInvariant_eq_tsum_on_cosets
    {G I : Type*} [Group G] [Countable I] [MeasurableSpace G] [MeasurableMul G]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G)) (hMass : mu (K : Set G) = 1)
    (r : I -> G)
    (hDisjoint : Pairwise (fun i j => Disjoint
      (SMul.smul (r i) (K : Set G)) (SMul.smul (r j) (K : Set G))))
    (hCover : Set.iUnion (fun i => SMul.smul (r i) (K : Set G)) = Set.univ)
    (f : G -> ENNReal) (hRight : forall g k : G, Membership.mem K k -> f (g * k) = f g) :
    lintegral mu f = tsum (fun i => f (r i)) := by
  let C (i : I) := SMul.smul (r i) (K : Set G)
  have hM (i : I) : MeasurableSet (C i) :=
    (MeasurableEquiv.mulLeft (r i)).measurableSet_image.mpr hK
  have hD (i : I) : mu (C i) = 1 := (measure_smul mu (r i) (K : Set G)).trans hMass
  calc
    _ = lintegral (mu.restrict (Set.iUnion C)) f := by
      change _ = lintegral (mu.restrict (Set.iUnion (fun i => SMul.smul (r i) (K : Set G)))) f
      rw [hCover, Measure.restrict_univ]
    _ = tsum (fun i => lintegral (mu.restrict (C i)) f) := lintegral_iUnion hM hDisjoint f
    _ = _ := by
      apply tsum_congr
      intro i
      calc
        _ = lintegral (mu.restrict (C i)) (fun _ => f (r i)) :=
          setLIntegral_congr_fun (hM i) (eqOn_leftCoset_of_rightInvariant K (r i) f hRight)
        _ = f (r i) * mu (C i) := setLIntegral_const (C i) (f (r i))
        _ = _ := by rw [hD, mul_one]

/-- The corresponding equality for an integrable complex-valued kernel. -/
theorem integral_rightInvariant_eq_tsum_on_cosets
    {G I : Type*} [Group G] [Countable I] [MeasurableSpace G] [MeasurableMul G]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G)) (hMass : mu (K : Set G) = 1)
    (r : I -> G)
    (hDisjoint : Pairwise (fun i j => Disjoint
      (SMul.smul (r i) (K : Set G)) (SMul.smul (r j) (K : Set G))))
    (hCover : Set.iUnion (fun i => SMul.smul (r i) (K : Set G)) = Set.univ)
    (f : G -> Complex) (hF : Integrable f mu)
    (hRight : forall g k : G, Membership.mem K k -> f (g * k) = f g) :
    integral mu f = tsum (fun i => f (r i)) := by
  let C (i : I) := SMul.smul (r i) (K : Set G)
  have hM (i : I) : MeasurableSet (C i) :=
    (MeasurableEquiv.mulLeft (r i)).measurableSet_image.mpr hK
  have hCover' : Set.iUnion C = Set.univ := hCover
  have hF' : IntegrableOn f (Set.iUnion C) mu := by
    rw [hCover', integrableOn_univ]
    exact hF
  have hD (i : I) : mu.real (C i) = 1 := by
    change ENNReal.toReal (mu (C i)) = 1
    rw [show mu (C i) = 1 from (measure_smul mu (r i) (K : Set G)).trans hMass]
    exact ENNReal.toReal_one
  calc
    _ = integral (mu.restrict (Set.iUnion C)) f := by rw [hCover', Measure.restrict_univ]
    _ = tsum (fun i => integral (mu.restrict (C i)) f) := integral_iUnion hM hDisjoint hF'
    _ = _ := by
      apply tsum_congr
      intro i
      calc
        _ = integral (mu.restrict (C i)) (fun _ => f (r i)) :=
          setIntegral_congr_fun (hM i) (eqOn_leftCoset_of_rightInvariant K (r i) f hRight)
        _ = SMul.smul (mu.real (C i)) (f (r i)) := setIntegral_const _
        _ = _ := by
          rw [hD]
          exact one_smul Real (f (r i))

private theorem preimage_leftCoset_subtype
    {G : Type*} [Group G] (B K : Subgroup G) (r : B) :
    Set.preimage (fun b : B => (b : G)) (SMul.smul (r : G) (K : Set G)) =
      SMul.smul r (K.comap B.subtype : Set B) := by
  ext b
  change (Exists (fun k : G => And (Membership.mem K k) ((r : G) * k = (b : G)))) <->
    (Exists (fun k : B => And (Membership.mem (K.comap B.subtype) k) (r * k = b)))
  constructor
  next =>
    intro hb
    choose k hk using hb
    let z : B := Inv.inv r * b
    have hZ : (z : G) = k := by
      change Inv.inv (r : G) * (b : G) = k
      rw [<- hk.2, inv_mul_cancel_left]
    refine Exists.intro z (And.intro ?_ ?_)
    next =>
      change Membership.mem K (z : G)
      rw [hZ]
      exact hk.1
    next =>
      change r * (Inv.inv r * b) = b
      exact mul_inv_cancel_left r b
  next =>
    intro hb
    choose k hk using hb
    exact Exists.intro (k : G) (And.intro hk.1 (congrArg Subtype.val hk.2))

private theorem leftCoset_subtype_partition
    {G I : Type*} [Group G] (B K : Subgroup G) (r : I -> B)
    (hDisjoint : Pairwise (fun i j => Disjoint
      (SMul.smul (r i : G) (K : Set G)) (SMul.smul (r j : G) (K : Set G))))
    (hCover : Set.iUnion (fun i => SMul.smul (r i : G) (K : Set G)) = Set.univ) :
    And (Pairwise (fun i j => Disjoint (SMul.smul (r i) (K.comap B.subtype : Set B))
      (SMul.smul (r j) (K.comap B.subtype : Set B))))
      (Set.iUnion (fun i => SMul.smul (r i) (K.comap B.subtype : Set B)) = Set.univ) := by
  constructor
  next =>
    intro i j hij
    rw [<- preimage_leftCoset_subtype, <- preimage_leftCoset_subtype]
    exact (hDisjoint hij).preimage (fun b : B => (b : G))
  next =>
    apply Set.eq_univ_of_forall
    intro b
    have hb : Membership.mem (Set.iUnion (fun i => SMul.smul (r i : G) (K : Set G))) (b : G) := by
      rw [hCover]
      exact Set.mem_univ _
    choose i hi using Set.mem_iUnion.mp hb
    apply Set.mem_iUnion.mpr
    refine Exists.intro i ?_
    rw [<- preimage_leftCoset_subtype]
    exact hi

/-- Normalized left Haar integration of a nonnegative right-K-invariant kernel
restricts to any subgroup meeting all the cosets in a countable partition. -/
theorem lintegral_rightInvariant_eq_lintegral_subgroup
    {G I : Type*} [Group G] [Countable I] [MeasurableSpace G] [MeasurableMul G]
    (B K : Subgroup G) [MeasurableSpace B] [MeasurableMul B]
    (hIncl : Measurable (fun b : B => (b : G)))
    (mu : Measure G) (nu : Measure B) [mu.IsMulLeftInvariant] [nu.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hMass : mu (K : Set G) = 1)
    (hMassB : nu (K.comap B.subtype : Set B) = 1)
    (r : I -> B)
    (hDisjoint : Pairwise (fun i j => Disjoint
      (SMul.smul (r i : G) (K : Set G)) (SMul.smul (r j : G) (K : Set G))))
    (hCover : Set.iUnion (fun i => SMul.smul (r i : G) (K : Set G)) = Set.univ)
    (f : G -> ENNReal) (hRight : forall g k : G, Membership.mem K k -> f (g * k) = f g) :
    lintegral mu f = lintegral nu (fun b : B => f (b : G)) := by
  have hPartition := leftCoset_subtype_partition B K r hDisjoint hCover
  exact (lintegral_rightInvariant_eq_tsum_on_cosets mu K hK hMass
    (fun i => (r i : G)) hDisjoint hCover f hRight).trans
    (lintegral_rightInvariant_eq_tsum_on_cosets nu (K.comap B.subtype) (hIncl hK) hMassB
      r hPartition.1 hPartition.2 (fun b => f (b : G))
      (fun g k hk => hRight (g : G) (k : G) hk)).symm

/-- For a measurable complex-valued kernel, the same comparison transfers
integrability and gives equality of the two complex integrals. -/
theorem integral_rightInvariant_eq_integral_subgroup
    {G I : Type*} [Group G] [Countable I] [MeasurableSpace G] [MeasurableMul G]
    (B K : Subgroup G) [MeasurableSpace B] [MeasurableMul B]
    (hIncl : Measurable (fun b : B => (b : G)))
    (mu : Measure G) (nu : Measure B) [mu.IsMulLeftInvariant] [nu.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hMass : mu (K : Set G) = 1)
    (hMassB : nu (K.comap B.subtype : Set B) = 1)
    (r : I -> B)
    (hDisjoint : Pairwise (fun i j => Disjoint
      (SMul.smul (r i : G) (K : Set G)) (SMul.smul (r j : G) (K : Set G))))
    (hCover : Set.iUnion (fun i => SMul.smul (r i : G) (K : Set G)) = Set.univ)
    (f : G -> Complex) (hF : Measurable f) (hInt : Integrable f mu)
    (hRight : forall g k : G, Membership.mem K k -> f (g * k) = f g) :
    And (Integrable (fun b : B => f (b : G)) nu)
      (integral mu f = integral nu (fun b : B => f (b : G))) := by
  have hNorm := lintegral_rightInvariant_eq_lintegral_subgroup B K hIncl mu nu
    hK hMass hMassB r hDisjoint hCover (fun g => enorm (f g))
    (fun g k hk => congrArg enorm (hRight g k hk))
  have hFin := hInt.hasFiniteIntegral
  change lintegral mu (fun g => enorm (f g)) < Top.top at hFin
  rw [hNorm] at hFin
  have hIntB : Integrable (fun b : B => f (b : G)) nu :=
    And.intro (hF.comp hIncl).aestronglyMeasurable hFin
  have hPartition := leftCoset_subtype_partition B K r hDisjoint hCover
  refine And.intro hIntB ?_
  exact (integral_rightInvariant_eq_tsum_on_cosets mu K hK hMass
    (fun i => (r i : G)) hDisjoint hCover f hInt hRight).trans
    (integral_rightInvariant_eq_tsum_on_cosets nu (K.comap B.subtype) (hIncl hK) hMassB
      r hPartition.1 hPartition.2 (fun b => f (b : G)) hIntB
      (fun g k hk => hRight (g : G) (k : G) hk)).symm

private theorem mem_leftCoset_iff_quotient_eq
    {G : Type*} [Group G] (K : Subgroup G) (a g : G) :
    Membership.mem (SMul.smul a (K : Set G)) g <->
      QuotientGroup.mk (s := K) a = QuotientGroup.mk (s := K) g := by
  rw [QuotientGroup.eq]
  change (Exists (fun k : G => And (Membership.mem K k) (a * k = g))) <->
    Membership.mem K (Inv.inv a * g)
  constructor
  next =>
    intro hg
    choose k hk using hg
    rw [<- hk.2, inv_mul_cancel_left]
    exact hk.1
  next =>
    intro hg
    exact Exists.intro (Inv.inv a * g) (And.intro hg (mul_inv_cancel_left a g))

/-- An open subgroup K of a separable topological group has countably many left
cosets. If G = BK, those cosets have representatives in B. -/
theorem exists_countable_leftCosets_of_iwasawa
    {G : Type*} [Group G] [TopologicalSpace G] [SeparableSpace G] [ContinuousMul G]
    (B K : Subgroup G) (hK : IsOpen (K : Set G))
    (hBK : forall g : G, Exists (fun b : B => Membership.mem K (Inv.inv (b : G) * g))) :
    And (Countable (Quotient (QuotientGroup.leftRel K)))
      (Exists (fun r : Quotient (QuotientGroup.leftRel K) -> B =>
        And (Pairwise (fun i j => Disjoint
          (SMul.smul (r i : G) (K : Set G)) (SMul.smul (r j : G) (K : Set G))))
          (Set.iUnion (fun i => SMul.smul (r i : G) (K : Set G)) = Set.univ))) := by
  let q : G -> Quotient (QuotientGroup.leftRel K) := QuotientGroup.mk (s := K)
  have hRep (i : Quotient (QuotientGroup.leftRel K)) :
      Exists (fun b : B => q (b : G) = i) := by
    have hx : Exists (fun g : G => q g = i) := QuotientGroup.mk_surjective (s := K) i
    choose g hg using hx
    choose b hb using hBK g
    have hbg : q (b : G) = q g := (QuotientGroup.eq (s := K)).mpr hb
    exact Exists.intro b (hbg.trans hg)
  choose r hr using hRep
  let C (i : Quotient (QuotientGroup.leftRel K)) := SMul.smul (r i : G) (K : Set G)
  have hMem (i : Quotient (QuotientGroup.leftRel K)) (g : G) :
      Membership.mem (C i) g <-> i = q g := by
    change Membership.mem (SMul.smul (r i : G) (K : Set G)) g <-> i = q g
    rw [mem_leftCoset_iff_quotient_eq]
    change (q (r i : G) = q g) <-> i = q g
    rw [hr]
  have hDisjoint : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro g hi hj
    exact hij (((hMem i g).mp hi).trans ((hMem j g).mp hj).symm)
  have hCount : Countable (Quotient (QuotientGroup.leftRel K)) :=
    hDisjoint.countable_of_isOpen_disjoint (fun i => hK.leftCoset (r i : G))
      (fun i => Exists.intro (r i : G) ((hMem i (r i : G)).mpr (hr i).symm))
  have hCover : Set.iUnion C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    exact Set.mem_iUnion.mpr (Exists.intro (q g) ((hMem (q g) g).mpr rfl))
  exact And.intro hCount (Exists.intro r (And.intro hDisjoint hCover))

/-- A measurable right-invariant kernel is integrable on the matrix
group exactly when its restriction is integrable on the subgroup meeting
the Iwasawa cosets. The two Bochner integrals agree. -/
theorem integrable_iff_and_integral_rightInvariant_of_iwasawa
    {G : Type*} [Group G] [TopologicalSpace G] [SeparableSpace G] [ContinuousMul G]
    [MeasurableSpace G] [MeasurableMul G] [OpensMeasurableSpace G]
    (B K : Subgroup G) [MeasurableSpace B] [MeasurableMul B]
    (hIncl : Measurable (fun b : B => (b : G))) (hK : IsOpen (K : Set G))
    (hBK : forall g : G, Exists (fun b : B => Membership.mem K (Inv.inv (b : G) * g)))
    (mu : Measure G) (nu : Measure B) [mu.IsMulLeftInvariant] [nu.IsMulLeftInvariant]
    (hMass : mu (K : Set G) = 1) (hMassB : nu (K.comap B.subtype : Set B) = 1)
    (f : G -> Complex) (hF : Measurable f)
    (hRight : forall g k : G, Membership.mem K k -> f (g * k) = f g) :
    And (Integrable f mu <-> Integrable (fun b : B => f (b : G)) nu)
      (integral mu f = integral nu (fun b : B => f (b : G))) := by
  have hPartition := exists_countable_leftCosets_of_iwasawa B K hK hBK
  let _ : Countable (Quotient (QuotientGroup.leftRel K)) := hPartition.1
  choose r hr using hPartition.2
  have hNorm := lintegral_rightInvariant_eq_lintegral_subgroup B K hIncl mu nu
    hK.measurableSet hMass hMassB r hr.1 hr.2 (fun g => enorm (f g))
    (fun g k hk => congrArg enorm (hRight g k hk))
  have hFinite : HasFiniteIntegral f mu <-> HasFiniteIntegral (fun b : B => f (b : G)) nu := by
    change (lintegral mu (fun g => enorm (f g)) < Top.top) <->
      (lintegral nu (fun b : B => enorm (f (b : G))) < Top.top)
    rw [hNorm]
  have hIff : Integrable f mu <-> Integrable (fun b : B => f (b : G)) nu :=
    Iff.intro (fun h => And.intro (hF.comp hIncl).aestronglyMeasurable (hFinite.mp h.2))
      (fun h => And.intro hF.aestronglyMeasurable (hFinite.mpr h.2))
  refine And.intro hIff ?_
  by_cases hInt : Integrable f mu
  next =>
    exact (integral_rightInvariant_eq_integral_subgroup B K hIncl mu nu hK.measurableSet
      hMass hMassB r hr.1 hr.2 f hF hInt hRight).2
  next =>
    rw [integral_undef hInt, integral_undef (fun h => hInt (hIff.mpr h))]

/-- With mu(K) = nu(B intersect K) = 1 and G = BK, a right-K-invariant
complex integral on G equals its restriction to B with left Haar measure. -/
theorem integral_rightInvariant_eq_integral_of_iwasawa
    {G : Type*} [Group G] [TopologicalSpace G] [SeparableSpace G] [ContinuousMul G]
    [MeasurableSpace G] [MeasurableMul G] [OpensMeasurableSpace G]
    (B K : Subgroup G) [MeasurableSpace B] [MeasurableMul B]
    (hIncl : Measurable (fun b : B => (b : G))) (hK : IsOpen (K : Set G))
    (hBK : forall g : G, Exists (fun b : B => Membership.mem K (Inv.inv (b : G) * g)))
    (mu : Measure G) (nu : Measure B) [mu.IsMulLeftInvariant] [nu.IsMulLeftInvariant]
    (hMass : mu (K : Set G) = 1) (hMassB : nu (K.comap B.subtype : Set B) = 1)
    (f : G -> Complex) (hF : Measurable f) (hInt : Integrable f mu)
    (hRight : forall g k : G, Membership.mem K k -> f (g * k) = f g) :
    And (Integrable (fun b : B => f (b : G)) nu)
      (integral mu f = integral nu (fun b : B => f (b : G))) := by
  have h := integrable_iff_and_integral_rightInvariant_of_iwasawa
    B K hIncl hK hBK mu nu hMass hMassB f hF hRight
  exact And.intro (h.1.mp hInt) h.2

end Robin1984.GRH
