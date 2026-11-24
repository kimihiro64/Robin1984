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

end Robin1984.GRH
