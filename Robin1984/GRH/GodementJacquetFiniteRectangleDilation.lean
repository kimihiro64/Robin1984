import Mathlib.Tactic.Abel
import Mathlib.Topology.Instances.Matrix
import Robin1984.GRH.HeckeAdelePoisson

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Schwartz-Bruhat test functions and matrix dilations in Godement and Jacquet, Zeta Functions of Simple Algebras.
- Formalization note: Proves that the inverse image of a finite adelic principal rectangle under an invertible matrix is a finite disjoint union of principal rectangles.
- PROVENANCE-END
-/

/-!
# Finite adelic rectangles under a matrix dilation

A nonzero principal integer clears the finitely many matrix
denominators. A sufficiently small principal vector subgroup
therefore maps into the prescribed subgroup of integral vectors.

The inverse image of a rectangle under the invertible matrix is
compact and invariant under this smaller subgroup. A finite
subcover by cosets becomes a disjoint partition after equal cosets
are identified. Every member of the partition has the same modulus.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

section AdditiveCosets

variable {G : Type*} [AddCommGroup G]

/-- The translate of an additive subgroup by one element. -/
def additiveSubgroupCoset (H : AddSubgroup G) (x : G) : Set G :=
  Set.image (fun y : G => x + y) (H : Set G)

private theorem additiveSubgroupCoset_eq_of_mem_inter
    (H : AddSubgroup G) {x y z : G}
    (hx : Membership.mem (additiveSubgroupCoset H x) z)
    (hy : Membership.mem (additiveSubgroupCoset H y) z) :
    additiveSubgroupCoset H x = additiveSubgroupCoset H y := by
  choose a ha using hx
  choose b hb using hy
  have hx' : x = z - a := eq_sub_of_add_eq ha.2
  have hy' : y = z - b := eq_sub_of_add_eq hb.2
  have hxy : Membership.mem H (x - y) := by
    have h : x - y = b - a := by
      rw [hx', hy']
      abel
    rw [h]
    exact H.sub_mem hb.1 ha.1
  have hyx : Membership.mem H (y - x) := by
    rw [<- neg_sub]
    exact H.neg_mem hxy
  apply Set.ext
  intro w
  constructor
  case mp =>
    intro hw
    choose u hu using hw
    refine Exists.intro (x - y + u) (And.intro (H.add_mem hxy hu.1) ?_)
    calc
      y + (x - y + u) = x + u := by abel
      _ = w := hu.2
  case mpr =>
    intro hw
    choose u hu using hw
    refine Exists.intro (y - x + u) (And.intro (H.add_mem hyx hu.1) ?_)
    calc
      x + (y - x + u) = y + u := by abel
      _ = w := hu.2

end AdditiveCosets

/-- A compact set invariant under translation by an open subgroup
is a finite disjoint union of cosets of that subgroup. -/
theorem exists_disjoint_additiveCoset_partition
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (H : AddSubgroup G) (hOpen : IsOpen (H : Set G))
    (S : Set G) (hS : IsCompact S)
    (hStable : forall x, Membership.mem S x ->
      forall h, Membership.mem H h -> Membership.mem S (x + h)) :
    Exists (fun T : Finset (Set G) =>
      And (forall C, Membership.mem T C ->
        Exists (fun x => And (Membership.mem S x) (C = additiveSubgroupCoset H x)))
      (And (forall C, Membership.mem T C -> forall D, Membership.mem T D ->
        Not (C = D) -> Disjoint C D)
      (S = Set.iUnion (fun C : Set G => Set.iUnion (fun _ : Membership.mem T C => C))))) := by
  let W (x : S) := additiveSubgroupCoset H x.val
  have hOpenW (x : S) : IsOpen (W x) := (Homeomorph.addLeft x.val).isOpenMap _ hOpen
  have hSub (x : S) : W x <= S := by
    intro y hy
    choose z hz using hy
    rw [<- hz.2]
    exact hStable x.val x.property z hz.1
  have hCover : S <= Set.iUnion W := by
    intro x hx
    refine Set.mem_iUnion.mpr (Exists.intro (Subtype.mk x hx) ?_)
    exact Exists.intro 0 (And.intro H.zero_mem (add_zero x))
  choose F hF using hS.elim_finite_subcover W hOpenW hCover
  let T := F.image W
  refine Exists.intro T (And.intro ?_ (And.intro ?_ ?_))
  . intro C hC
    choose x hx using Finset.mem_image.mp hC
    exact Exists.intro x.val (And.intro x.property hx.2.symm)
  . intro C hC D hD hNe
    apply Set.disjoint_left.mpr
    intro z hzC hzD
    choose x hx using Finset.mem_image.mp hC
    choose y hy using Finset.mem_image.mp hD
    have hzx : Membership.mem (W x) z := by rw [hx.2]; exact hzC
    have hzy : Membership.mem (W y) z := by rw [hy.2]; exact hzD
    exact hNe (hx.2.symm.trans ((additiveSubgroupCoset_eq_of_mem_inter H hzx hzy).trans hy.2))
  . apply Set.Subset.antisymm
    . intro x hx
      choose c hc using Set.mem_iUnion.mp (hF hx)
      choose hmem hxc using Set.mem_iUnion.mp hc
      exact Set.mem_iUnion.mpr (Exists.intro (W c) (Set.mem_iUnion.mpr
        (Exists.intro (Finset.mem_image_of_mem W hmem) hxc)))
    . intro x hx
      choose C hC using Set.mem_iUnion.mp hx
      choose hmem hxC using Set.mem_iUnion.mp hC
      choose c hc using Finset.mem_image.mp hmem
      apply hSub c
      rw [hc.2]
      exact hxC

variable (K : Type*) [Field K] [NumberField K]

private abbrev FiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev integralFiniteAdeles (K : Type*) [Field K] [NumberField K] :
    AddSubgroup (FiniteAdeles K) := heckeIntegralFiniteAdeles

private def principalIntegerFiniteAdele (d : RingOfIntegers K) : FiniteAdeles K :=
  algebraMap K (FiniteAdeles K) (algebraMap (RingOfIntegers K) K d)

private theorem principalIntegerFiniteAdele_mul (d e : RingOfIntegers K) :
    principalIntegerFiniteAdele K (d * e) =
      principalIntegerFiniteAdele K d * principalIntegerFiniteAdele K e := by
  unfold principalIntegerFiniteAdele
  rw [map_mul, map_mul]

private theorem principalIntegerFiniteAdele_apply (d : RingOfIntegers K)
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    (principalIntegerFiniteAdele K d) p =
      algebraMap (RingOfIntegers K) (p.adicCompletion K) d := by
  change algebraMap K (p.adicCompletion K) (algebraMap (RingOfIntegers K) K d) = _
  exact (IsScalarTower.algebraMap_apply (RingOfIntegers K) K (p.adicCompletion K) d).symm

private theorem principalIntegerFiniteAdele_mem (d : RingOfIntegers K) :
    Membership.mem (integralFiniteAdeles K) (principalIntegerFiniteAdele K d) := by
  intro p
  rw [principalIntegerFiniteAdele_apply K d p]
  exact HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers K) K p d

private theorem integralFiniteAdeles_mul_mem {a b : FiniteAdeles K}
    (ha : Membership.mem (integralFiniteAdeles K) a)
    (hb : Membership.mem (integralFiniteAdeles K) b) :
    Membership.mem (integralFiniteAdeles K) (a * b) :=
  fun p => (p.adicCompletionIntegers K).mul_mem _ _ (ha p) (hb p)

private theorem exists_principalIntegralMultiple_finiteAdele (a : FiniteAdeles K) :
    Exists (fun d : RingOfIntegers K => And (Not (d = 0))
      (Membership.mem (integralFiniteAdeles K) (principalIntegerFiniteAdele K d * a))) := by
  choose d hd using exists_finiteAdele_integral_multiple a
  refine Exists.intro d (And.intro hd.1 ?_)
  intro p
  change Membership.mem (p.adicCompletionIntegers K) ((principalIntegerFiniteAdele K d) p * a p)
  rw [principalIntegerFiniteAdele_apply K d p, mul_comm]
  exact hd.2 p

/-- A finite family of finite adeles has a common principal integral
multiple. -/
theorem exists_principalIntegralMultiple_finiteAdeles
    (I : Type*) [Fintype I] (a : I -> FiniteAdeles K) :
    Exists (fun d : RingOfIntegers K => And (Not (d = 0))
      (forall i, Membership.mem (integralFiniteAdeles K) (principalIntegerFiniteAdele K d * a i))) := by
  choose d hd using fun i => exists_principalIntegralMultiple_finiteAdele K (a i)
  let b := Finset.univ.prod d
  have hb : Not (b = 0) := Finset.prod_ne_zero_iff.mpr (fun i _ => (hd i).1)
  refine Exists.intro b (And.intro hb ?_)
  intro i
  choose c hc using Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  rw [show b = d i * c from hc, principalIntegerFiniteAdele_mul,
    mul_comm (principalIntegerFiniteAdele K (d i)), mul_assoc]
  exact integralFiniteAdeles_mul_mem K (principalIntegerFiniteAdele_mem K c) (hd i).2

/-- The inverse image of a finite adelic principal rectangle under a
matrix dilation is invariant under a sufficiently small principal vector subgroup. -/
theorem exists_heckeScaledIntegralFiniteAdeles_mulVec
    (I : Type*) [Fintype I] (M : Matrix I I (FiniteAdeles K))
    (d : RingOfIntegers K) (hd : Not (d = 0)) :
    Exists (fun b : RingOfIntegers K => And (Not (b = 0))
      (forall v : I -> FiniteAdeles K,
        (forall i, Membership.mem (heckeScaledIntegralFiniteAdeles
          (algebraMap (RingOfIntegers K) K b)) (v i)) ->
        forall i, Membership.mem (heckeScaledIntegralFiniteAdeles
          (algebraMap (RingOfIntegers K) K d)) ((M.mulVec v) i))) := by
  let A := FiniteAdeles K
  let R := RingOfIntegers K
  let e := algebraMap R K
  let q := algebraMap K A
  let H := integralFiniteAdeles K
  choose c hc using exists_principalIntegralMultiple_finiteAdeles K (Prod I I)
    (fun ij => M ij.1 ij.2)
  let b := c * d
  have hb : Not (b = 0) := mul_ne_zero hc.1 hd
  refine Exists.intro b (And.intro hb ?_)
  intro v hv i
  have hRep (j : I) : Exists (fun u : A => And (Membership.mem H u) (u * q (e b) = v j)) :=
    AddSubgroup.mem_map.mp (hv j)
  choose w hw using hRep
  let z (j : I) := (q (e c) * M i j) * w j
  have hz (j : I) : Membership.mem H (z j) :=
    integralFiniteAdeles_mul_mem K (hc.2 (Prod.mk i j)) (hw j).1
  have hS : Membership.mem H (Finset.univ.sum z) := H.sum_mem (fun j _ => hz j)
  refine AddSubgroup.mem_map.mpr (Exists.intro (Finset.univ.sum z) (And.intro hS ?_))
  change (Finset.univ.sum z) * q (e d) = (M.mulVec v) i
  rw [Finset.sum_mul]
  change Finset.univ.sum (fun j => z j * q (e d)) =
    Finset.univ.sum (fun j => M i j * v j)
  apply Finset.sum_congr rfl
  intro j _
  have hB : q (e b) = q (e c) * q (e d) := principalIntegerFiniteAdele_mul K c d
  rw [<- (hw j).2, hB]
  change ((q (e c) * M i j) * w j) * q (e d) =
    M i j * (w j * (q (e c) * q (e d)))
  ac_rfl

variable (I : Type*)

private def scaledFiniteAdeleVectorSubgroup (d : K) : AddSubgroup (I -> FiniteAdeles K) where
  carrier := fun v => forall i, Membership.mem (heckeScaledIntegralFiniteAdeles d) (v i)
  zero_mem' := fun _ => (heckeScaledIntegralFiniteAdeles d).zero_mem
  add_mem' hx hy := fun i => (heckeScaledIntegralFiniteAdeles d).add_mem (hx i) (hy i)
  neg_mem' hx := fun i => (heckeScaledIntegralFiniteAdeles d).neg_mem (hx i)

/-- The product of finite adelic principal cosets with a common modulus. -/
def finiteAdelePrincipalRectangle (a : I -> FiniteAdeles K) (d : K) : Set (I -> FiniteAdeles K) :=
  additiveSubgroupCoset (scaledFiniteAdeleVectorSubgroup K I d) a

theorem mem_finiteAdelePrincipalRectangle_iff
    (a v : I -> FiniteAdeles K) (d : K) :
    Membership.mem (finiteAdelePrincipalRectangle K I a d) v <->
      forall i, Membership.mem (heckeFiniteAdelePrincipalCoset (a i) d) (v i) := by
  constructor
  case mp =>
    intro hv i
    choose w hw using hv
    exact Exists.intro (w i) (And.intro (hw.1 i) (congrFun hw.2 i))
  case mpr =>
    intro hv
    choose w hw using hv
    exact Exists.intro w (And.intro (fun i => (hw i).1) (funext (fun i => (hw i).2)))

private theorem isOpen_scaledFiniteAdeleVectorSubgroup [Fintype I] (d : K) (hd : Not (d = 0)) :
    IsOpen (scaledFiniteAdeleVectorSubgroup K I d : Set (I -> FiniteAdeles K)) := by
  let P (i : I) : Set (I -> FiniteAdeles K) :=
    Set.preimage (fun v => v i) (heckeScaledIntegralFiniteAdeles d : Set (FiniteAdeles K))
  have hEq : (scaledFiniteAdeleVectorSubgroup K I d : Set (I -> FiniteAdeles K)) = Set.iInter P := by
    apply Set.ext
    intro v
    constructor
    . intro hv
      exact Set.mem_iInter.mpr (fun i => hv i)
    . intro hv i
      exact Set.mem_iInter.mp hv i
  rw [hEq]
  exact isOpen_iInter_of_finite (fun i =>
    (isOpen_heckeScaledIntegralFiniteAdeles d hd).preimage (continuous_apply i))

private theorem isCompact_scaledFiniteAdeleVectorSubgroup (d : K) :
    IsCompact (scaledFiniteAdeleVectorSubgroup K I d : Set (I -> FiniteAdeles K)) := by
  let H := heckeScaledIntegralFiniteAdeles d
  have hc : IsCompact (H : Set (FiniteAdeles K)) := by
    change IsCompact (Set.image (fun z : FiniteAdeles K => z * algebraMap K (FiniteAdeles K) d)
      (integralFiniteAdeles K : Set (FiniteAdeles K)))
    exact (isCompact_integralFiniteAdeles (K := K)).image (continuous_id.mul continuous_const)
  have hEq : (scaledFiniteAdeleVectorSubgroup K I d : Set (I -> FiniteAdeles K)) =
      Set.pi Set.univ (fun _ : I => (H : Set (FiniteAdeles K))) := by
    apply Set.ext
    intro v
    constructor
    . intro hv
      exact fun i _ => hv i
    . intro hv i
      exact hv i (Set.mem_univ i)
  rw [hEq]
  exact isCompact_univ_pi (fun _ => hc)

theorem isCompact_finiteAdelePrincipalRectangle (a : I -> FiniteAdeles K) (d : K) :
    IsCompact (finiteAdelePrincipalRectangle K I a d) :=
  (isCompact_scaledFiniteAdeleVectorSubgroup K I d).image (continuous_const.add continuous_id)

variable [Fintype I]

private def finiteAdeleMulVecHomeomorph (M : Units (Matrix I I (FiniteAdeles K))) :
    Homeomorph (I -> FiniteAdeles K) (I -> FiniteAdeles K) where
  toFun := M.val.mulVec
  invFun := M.inv.mulVec
  left_inv v := by rw [Matrix.mulVec_mulVec, M.inv_val, Matrix.one_mulVec]
  right_inv v := by rw [Matrix.mulVec_mulVec, M.val_inv, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

/-- The pullback of a finite adelic rectangle by an invertible matrix
is a finite disjoint union of rectangles with a common nonzero modulus. -/
theorem exists_disjoint_principalRectangles_mulVec_preimage
    (M : Units (Matrix I I (FiniteAdeles K))) (a : I -> FiniteAdeles K)
    (d : RingOfIntegers K) (hd : Not (d = 0)) :
    let e := algebraMap (RingOfIntegers K) K
    let S := Set.preimage M.val.mulVec (finiteAdelePrincipalRectangle K I a (e d))
    Exists (fun b : RingOfIntegers K => And (Not (b = 0))
      (Exists (fun T : Finset (Set (I -> FiniteAdeles K)) =>
        And (forall C, Membership.mem T C -> Exists (fun x => And (Membership.mem S x)
          (C = finiteAdelePrincipalRectangle K I x (e b))))
        (And (forall C, Membership.mem T C -> forall D, Membership.mem T D ->
          Not (C = D) -> Disjoint C D)
          (S = Set.iUnion (fun C : Set (I -> FiniteAdeles K) =>
            Set.iUnion (fun _ : Membership.mem T C => C))))))) := by
  let e := algebraMap (RingOfIntegers K) K
  let S := Set.preimage M.val.mulVec (finiteAdelePrincipalRectangle K I a (e d))
  have hSc : IsCompact S :=
    (finiteAdeleMulVecHomeomorph K I M).isCompact_preimage.mpr
      (isCompact_finiteAdelePrincipalRectangle K I a (e d))
  choose b hb using exists_heckeScaledIntegralFiniteAdeles_mulVec K I M.val d hd
  let H := scaledFiniteAdeleVectorSubgroup K I (e b)
  have hb' : Not (e b = 0) :=
    (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective (RingOfIntegers K) K)).mpr hb.1
  have hO : IsOpen (H : Set (I -> FiniteAdeles K)) := isOpen_scaledFiniteAdeleVectorSubgroup K I (e b) hb'
  have hStable (x : I -> FiniteAdeles K) (hx : Membership.mem S x)
      (y : I -> FiniteAdeles K) (hy : Membership.mem H y) : Membership.mem S (x + y) := by
    change Membership.mem (finiteAdelePrincipalRectangle K I a (e d)) (M.val.mulVec (x + y))
    rw [Matrix.mulVec_add]
    choose w hw using hx
    let H' := scaledFiniteAdeleVectorSubgroup K I (e d)
    exact Exists.intro (w + M.val.mulVec y) (And.intro (H'.add_mem hw.1 (hb.2 y hy))
      (by
        change a + (w + M.val.mulVec y) = M.val.mulVec x + M.val.mulVec y
        have he : a + w = M.val.mulVec x := hw.2
        rw [<- add_assoc, he]))
  exact Exists.intro b (And.intro hb.1 (exists_disjoint_additiveCoset_partition H hO S hSc hStable))

end Robin1984.GRH
