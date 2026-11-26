import Robin1984.GRH.GodementJacquetFiniteRectangleDilation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The compact-open subgroup topology of finite adeles and finite coset decompositions of compactly supported locally constant functions.
- Formalization note: Constructs a common nonzero integral modulus for finite adelic neighborhoods and expands compact locally constant tests into disjoint principal rectangles.
- PROVENANCE-END
-/

/-!
# Principal rectangles for finite adelic tests

A nonzero integral modulus can make all prescribed finite-place coordinates
arbitrarily small. The resulting principal subgroups give a neighborhood
basis in each finite adelic vector space. A compactly supported locally
constant test therefore has a finite expansion in disjoint translates of
one principal subgroup.
-/

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace Robin1984.GRH

private theorem isCompact_support_locallyConstant
    {G : Type*} [TopologicalSpace G] (Phi : LocallyConstant G Complex)
    (hPhi : HasCompactSupport (fun x => Phi x)) :
    IsCompact (Function.support (fun x => Phi x)) := by
  let S := Function.support (fun x => Phi x)
  have hClosed : IsClosed S := (Phi.isLocallyConstant.isOpen_fiber (0 : Complex)).isClosed_compl
  change IsCompact (closure S) at hPhi
  rw [hClosed.closure_eq] at hPhi
  exact hPhi

private theorem exists_addSubgroup_period_of_locallyConstant
    {G J : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (H : J -> AddSubgroup G) (hOpen : forall i, IsOpen (H i : Set G))
    (hBasis : forall V : Set G, IsOpen V -> Membership.mem V 0 ->
      exists i : J, Set.Subset (H i : Set G) V)
    (Phi : LocallyConstant G Complex) (hPhi : HasCompactSupport (fun x => Phi x)) :
    exists i : J, forall x y : G, Membership.mem (H i) y -> Phi (x + y) = Phi x := by
  classical
  let S := Function.support (fun x => Phi x)
  have hCompact : IsCompact S := isCompact_support_locallyConstant Phi hPhi
  have hLocal (x : S) :
      exists i : J, forall y, Membership.mem (H i) y -> Phi (x.val + y) = Phi x.val := by
    let V : Set G := {y | Phi (x.val + y) = Phi x.val}
    have hV : IsOpen V :=
      (Phi.isLocallyConstant.isOpen_fiber (Phi x.val)).preimage (continuous_const.add continuous_id)
    have h0 : Membership.mem V 0 := by simp [V]
    choose j hj using hBasis V hV h0
    exact Exists.intro j (fun y hy => hj hy)
  choose i hI using hLocal
  let W (x : S) := additiveSubgroupCoset (H (i x)) x.val
  have hW (x : S) : IsOpen (W x) := (Homeomorph.addLeft x.val).isOpenMap _ (hOpen (i x))
  have hCover : Set.Subset S (Set.iUnion W) := by
    intro x hx
    refine Set.mem_iUnion.mpr (Exists.intro (Subtype.mk x hx) ?_)
    exact Exists.intro 0 (And.intro (H (i (Subtype.mk x hx))).zero_mem (add_zero x))
  choose F hF using hCompact.elim_finite_subcover W hW hCover
  have hCommon (T : Finset S) :
      exists j : J, forall x : S, Membership.mem T x -> H j <= H (i x) := by
    induction T using Finset.induction_on with
    | empty =>
      choose j _hj using hBasis Set.univ isOpen_univ (Set.mem_univ 0)
      exact Exists.intro j (fun x hx => False.elim (Finset.notMem_empty x hx))
    | insert x T hx hT =>
      choose j hj using hT
      let V : Set G := Inter.inter (H j : Set G) (H (i x) : Set G)
      have hVO : IsOpen V := (hOpen j).inter (hOpen (i x))
      have hVZ : Membership.mem V 0 := And.intro (H j).zero_mem (H (i x)).zero_mem
      choose k hk using hBasis V hVO hVZ
      refine Exists.intro k ?_
      intro y hy z hz
      have hSub : And (Membership.mem (H j) z) (Membership.mem (H (i x)) z) := hk hz
      rcases Finset.mem_insert.mp hy with hEq | hMem
      . subst y
        exact hSub.2
      . exact hj y hMem hSub.1
  choose j hj using hCommon F
  have hOn (x : G) (hx : Membership.mem S x) (y : G) (hy : Membership.mem (H j) y) :
      Phi (x + y) = Phi x := by
    choose z hz using Set.mem_iUnion.mp (hF hx)
    choose hzF hzx using Set.mem_iUnion.mp hz
    choose v hv using hzx
    rw [<- hv.2, add_assoc, hI z (v + y) ((H (i z)).add_mem hv.1 (hj z hzF hy)), hI z v hv.1]
  refine Exists.intro j ?_
  intro x y hy
  by_cases hx : Membership.mem S x
  . exact hOn x hx y hy
  . by_cases hxy : Membership.mem S (x + y)
    . have hBack := hOn (x + y) hxy (-y) ((H j).neg_mem hy)
      rw [add_neg_cancel_right] at hBack
      exact hBack.symm
    . have hx0 : Phi x = 0 := by
        by_contra hn
        exact hx hn
      have hxy0 : Phi (x + y) = 0 := by
        by_contra hn
        exact hxy hn
      rw [hx0, hxy0]

/-- A compactly supported locally constant function on an additive group
with an open-subgroup basis is a finite sum over disjoint cosets. -/
theorem exists_locallyConstant_additiveCoset_expansion
    {G J : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (H : J -> AddSubgroup G) (hOpen : forall i, IsOpen (H i : Set G))
    (hBasis : forall V : Set G, IsOpen V -> Membership.mem V 0 ->
      exists i : J, Set.Subset (H i : Set G) V)
    (Phi : LocallyConstant G Complex) (hPhi : HasCompactSupport (fun x => Phi x)) :
    exists (i : J) (T : Finset (Set G)) (a : Set G -> Complex),
      And (forall C, Membership.mem T C -> exists x : G, C = additiveSubgroupCoset (H i) x)
        (And (forall C, Membership.mem T C -> forall D, Membership.mem T D ->
            Not (C = D) -> Disjoint C D)
          (forall x : G, Phi x = T.sum (fun C =>
            @ite Complex (Membership.mem C x) (Classical.propDecidable _) (a C) 0))) := by
  classical
  let S := Function.support (fun x => Phi x)
  have hCompact : IsCompact S := isCompact_support_locallyConstant Phi hPhi
  choose i hI using exists_addSubgroup_period_of_locallyConstant H hOpen hBasis Phi hPhi
  have hStable (x : G) (hx : Membership.mem S x) (y : G) (hy : Membership.mem (H i) y) :
      Membership.mem S (x + y) := by
    change Not (Phi (x + y) = 0)
    rw [hI x y hy]
    exact hx
  choose T hT using exists_disjoint_additiveCoset_partition (H i) (hOpen i) S hCompact hStable
  have hRep (C : {C : Set G // Membership.mem T C}) := hT.1 C.val C.property
  choose r hr using hRep
  let a (C : Set G) := if hC : Membership.mem T C then Phi (r (Subtype.mk C hC)) else 0
  refine Exists.intro i (Exists.intro T (Exists.intro a (And.intro ?_ (And.intro hT.2.1 ?_))))
  . intro C hC
    exact Exists.intro (r (Subtype.mk C hC)) (hr (Subtype.mk C hC)).2
  . intro x
    have hIn (C : Set G) (hC : Membership.mem T C) (hx : Membership.mem C x) :
        Membership.mem S x := by
      rw [hT.2.2]
      exact Set.mem_iUnion.mpr (Exists.intro C
        (Set.mem_iUnion.mpr (Exists.intro hC hx)))
    by_cases hx : Membership.mem S x
    . have hUnion := hx
      rw [hT.2.2] at hUnion
      choose C hC using Set.mem_iUnion.mp hUnion
      choose hCT hxC using Set.mem_iUnion.mp hC
      rw [Finset.sum_eq_single C]
      . rw [if_pos hxC]
        simp only [a, dif_pos hCT]
        have hCoset : Membership.mem (additiveSubgroupCoset (H i) (r (Subtype.mk C hCT))) x := by
          rw [<- (hr (Subtype.mk C hCT)).2]
          exact hxC
        choose y hy using hCoset
        rw [<- hy.2]
        exact hI _ y hy.1
      . intro D hD hDC
        have hNo : Not (Membership.mem D x) := fun h =>
          Set.disjoint_left.mp (hT.2.1 D hD C hCT hDC) h hxC
        rw [if_neg hNo]
      . intro hNo
        exact False.elim (hNo hCT)
    . have hx0 : Phi x = 0 := by
        by_contra hn
        exact hx hn
      rw [hx0, Finset.sum_eq_zero (fun C hC => if_neg (fun h => hx (hIn C hC h)))]

section

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)

private theorem exists_integer_small_at_finitePlace (p : P)
    (eps : Real) (hEps : 0 < eps) :
    exists d : RingOfIntegers K, And (Not (d = 0))
      (norm (FinitePlace.embedding p (algebraMap (RingOfIntegers K) K d)) < eps) := by
  classical
  have hIdeal : exists x : RingOfIntegers K, And (Membership.mem p.asIdeal x) (Not (x = 0)) := by
    by_contra h
    apply p.ne_bot
    apply le_antisymm ?_ bot_le
    intro x hx
    rw [Ideal.mem_bot]
    by_contra hn
    exact h (Exists.intro x (And.intro hx hn))
  choose r hr using hIdeal
  have hN : norm (FinitePlace.embedding p (algebraMap (RingOfIntegers K) K r)) < 1 :=
    (FinitePlace.norm_lt_one_iff_mem K p r).mpr hr.1
  choose m hm using exists_pow_lt_of_lt_one hEps hN
  refine Exists.intro (r ^ m) (And.intro (pow_ne_zero _ hr.2) ?_)
  simpa only [map_pow, norm_pow] using hm

/-- A single nonzero algebraic integer satisfies any prescribed positive
norm bounds at finitely many finite places. -/
theorem exists_integer_small_at_finitePlaces
    (E : Finset P) (eps : P -> Real)
    (hEps : forall p : P, Membership.mem E p -> 0 < eps p) :
    exists d : RingOfIntegers K, And (Not (d = 0))
      (forall p : P, Membership.mem E p ->
        norm (FinitePlace.embedding p (algebraMap (RingOfIntegers K) K d)) < eps p) := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    exact Exists.intro 1 (And.intro one_ne_zero (fun p hp => False.elim (Finset.notMem_empty p hp)))
  | insert p E hp hE =>
    choose d hd using hE (fun q hq => hEps q (Finset.mem_insert_of_mem hq))
    choose c hc using exists_integer_small_at_finitePlace K p (eps p)
      (hEps p (Finset.mem_insert_self p E))
    refine Exists.intro (d * c) (And.intro (mul_ne_zero hd.1 hc.1) ?_)
    intro q hq
    simp only [map_mul, norm_mul]
    rcases Finset.mem_insert.mp hq with hEq | hMem
    . subst q
      calc
        _ <= 1 * norm (FinitePlace.embedding p (algebraMap (RingOfIntegers K) K c)) :=
          mul_le_mul_of_nonneg_right (FinitePlace.norm_le_one K p d) (norm_nonneg _)
        _ < eps p := by rw [one_mul]; exact hc.2
    . calc
        _ <= norm (FinitePlace.embedding q (algebraMap (RingOfIntegers K) K d)) * 1 :=
          mul_le_mul_of_nonneg_left (FinitePlace.norm_le_one K q c) (norm_nonneg _)
        _ < eps q := by rw [mul_one]; exact hd.2 q hMem

local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K

/-- A nonzero integral multiple of the integral finite adeles lies in any
open neighborhood of zero. -/
theorem exists_scaledIntegralFiniteAdeles_subset_neighborhood
    (V : Set FA) (hV : IsOpen V) (hZero : Membership.mem V 0) :
    exists d : RingOfIntegers K, And (Not (d = 0))
      (Set.Subset (heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d) : Set FA) V) := by
  classical
  let L (p : P) := p.adicCompletion K
  let O (p : P) := p.adicCompletionIntegers K
  let j : (forall p : P, O p) -> FA := RestrictedProduct.structureMap L
    (fun p : P => (O p : Set (L p))) Filter.cofinite
  have hJ : Continuous j :=
    (show Topology.IsEmbedding j from RestrictedProduct.isEmbedding_structureMap).continuous
  have hJ0 : j 0 = 0 := by
    apply RestrictedProduct.ext
    intro p
    rfl
  have hPre0 : Membership.mem (Set.preimage j V) 0 := by
    change Membership.mem V (j 0)
    rwa [hJ0]
  have hPre := (hV.preimage hJ).mem_nhds hPre0
  rw [nhds_pi] at hPre
  choose E T hT using Filter.mem_pi'.mp hPre
  have hBall (p : P) := Metric.mem_nhds_iff.mp (hT.1 p)
  choose eps hEps using hBall
  choose d hd using exists_integer_small_at_finitePlaces K E eps
    (fun p _ => (hEps p).1)
  refine Exists.intro d (And.intro hd.1 ?_)
  intro x hx
  change exists y : FA, And (Membership.mem heckeIntegralFiniteAdeles y)
    (y * algebraMap K FA (algebraMap (RingOfIntegers K) K d) = x) at hx
  choose y hy using hx
  let a (p : P) := algebraMap (RingOfIntegers K) (L p) d
  let z (p : P) : O p := Subtype.mk (y p * a p)
    ((O p).mul_mem _ _ (hy.1 p) (HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers K) K p d))
  have hZ : Membership.mem (Set.pi (E : Set P) T) z := by
    intro p hp
    apply (hEps p).2
    change dist (y p * a p) 0 < eps p
    rw [dist_eq_norm, sub_zero, norm_mul]
    have hY : norm (y p) <= 1 :=
      Valued.toNormedField.norm_le_one_iff.mpr (hy.1 p)
    have hA : norm (a p) < eps p := by
      change norm (algebraMap (RingOfIntegers K) (p.adicCompletion K) d) < eps p
      have heq := congrFun (HeightOneSpectrum.algebraMap_adicCompletion
        (S := RingOfIntegers K) (K := K) (v := p)) d
      exact (congrArg (fun z : p.adicCompletion K => norm z) heq).trans_lt (hd.2 p hp)
    exact (mul_le_mul_of_nonneg_right hY (norm_nonneg _)).trans_lt (by rwa [one_mul])
  have hVZ : Membership.mem V (j z) := hT.2 hZ
  have hEq : j z = x := by
    apply RestrictedProduct.ext
    intro p
    change y p * a p = x p
    rw [<- congrArg (fun w : FA => w p) hy.2]
    change y p * a p = y p * algebraMap K (L p) (algebraMap (RingOfIntegers K) K d)
    rw [show a p = _ from IsScalarTower.algebraMap_apply (RingOfIntegers K) K (L p) d]
  rwa [hEq] at hVZ

private theorem scaledIntegralFiniteAdeles_le_of_dvd
    {d e : RingOfIntegers K} (h : Dvd.dvd d e) :
    heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K e) <=
      heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d) := by
  choose c hc using h
  let j := algebraMap K FA (algebraMap (RingOfIntegers K) K c)
  have hJ : Membership.mem heckeIntegralFiniteAdeles j := by
    intro p
    change Membership.mem (p.adicCompletionIntegers K)
      (algebraMap K (p.adicCompletion K) (algebraMap (RingOfIntegers K) K c))
    rw [<- IsScalarTower.algebraMap_apply (RingOfIntegers K) K (p.adicCompletion K)]
    exact HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers K) K p c
  intro x hx
  change exists y : FA, And (Membership.mem heckeIntegralFiniteAdeles y)
    (y * algebraMap K FA (algebraMap (RingOfIntegers K) K e) = x) at hx
  choose y hy using hx
  change exists z : FA, And (Membership.mem heckeIntegralFiniteAdeles z)
    (z * algebraMap K FA (algebraMap (RingOfIntegers K) K d) = x)
  refine Exists.intro (y * j) (And.intro ?_ ?_)
  . intro p
    exact (p.adicCompletionIntegers K).mul_mem _ _ (hy.1 p) (hJ p)
  . rw [<- hy.2, hc, map_mul, map_mul]
    dsimp only [j]
    ac_rfl

/-- One modulus puts the product of the principal subgroups into any
open neighborhood of zero in a finite adelic vector space. -/
theorem exists_finiteAdeleVectorPrincipalSubgroup_subset_neighborhood
    (I : Type*) [Fintype I] (V : Set (I -> FA)) (hV : IsOpen V) (hZero : Membership.mem V 0) :
    exists d : RingOfIntegers K, And (Not (d = 0))
      (forall v : I -> FA,
        (forall i, Membership.mem (heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d))
          (v i)) -> Membership.mem V v) := by
  classical
  have hN := hV.mem_nhds hZero
  rw [nhds_pi] at hN
  choose _E T hT using Filter.mem_pi'.mp hN
  have hChoice (i : I) :
      exists d : RingOfIntegers K, And (Not (d = 0))
        (Set.Subset (heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d) : Set FA) (T i)) := by
    choose W hW using mem_nhds_iff.mp (hT.1 i)
    choose d hd using exists_scaledIntegralFiniteAdeles_subset_neighborhood K W hW.2.1 hW.2.2
    exact Exists.intro d (And.intro hd.1 (hd.2.trans hW.1))
  choose d hd using hChoice
  let D := Finset.univ.prod d
  have hD : Not (D = 0) := Finset.prod_ne_zero_iff.mpr (fun i _ => (hd i).1)
  refine Exists.intro D (And.intro hD ?_)
  intro v hv
  apply hT.2
  intro i _
  apply (hd i).2
  exact scaledIntegralFiniteAdeles_le_of_dvd K (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) (hv i)

/-- A compactly supported locally constant finite adelic test is a finite
linear combination of disjoint principal rectangle indicators with one
common nonzero integral modulus. -/
theorem exists_locallyConstant_finiteAdelePrincipalRectangle_expansion
    (I : Type*) [Fintype I] (Phi : LocallyConstant (I -> FA) Complex)
    (hPhi : HasCompactSupport (fun x => Phi x)) :
    exists (d : RingOfIntegers K) (T : Finset (Set (I -> FA))) (a : Set (I -> FA) -> Complex),
      And (Not (d = 0))
        (And (forall C, Membership.mem T C -> exists x : I -> FA,
            C = finiteAdelePrincipalRectangle K I x (algebraMap (RingOfIntegers K) K d))
          (And (forall C, Membership.mem T C -> forall D, Membership.mem T D ->
              Not (C = D) -> Disjoint C D)
            (forall x : I -> FA, Phi x = T.sum (fun C =>
              @ite Complex (Membership.mem C x) (Classical.propDecidable _) (a C) 0)))) := by
  let J := {d : RingOfIntegers K // Not (d = 0)}
  let H (d : J) : AddSubgroup (I -> FA) :=
    let A := heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d.val)
    { carrier := fun v => forall i, Membership.mem A (v i)
      zero_mem' := fun _ => A.zero_mem
      add_mem' := fun hx hy i => A.add_mem (hx i) (hy i)
      neg_mem' := fun hx i => A.neg_mem (hx i) }
  have hOpen (d : J) : IsOpen (H d : Set (I -> FA)) := by
    let A := heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d.val)
    have hD : Not (algebraMap (RingOfIntegers K) K d.val = 0) := by
      intro hz
      apply d.property
      exact (FaithfulSMul.algebraMap_injective (RingOfIntegers K) K) (hz.trans (map_zero _).symm)
    have hEq : (H d : Set (I -> FA)) =
        Set.iInter (fun i : I => Set.preimage (fun v : I -> FA => v i) (A : Set FA)) := by
      apply Set.ext
      intro v
      exact Iff.intro (fun hv => Set.mem_iInter.mpr hv) (fun hv => Set.mem_iInter.mp hv)
    rw [hEq]
    exact isOpen_iInter_of_finite (fun i =>
      (isOpen_heckeScaledIntegralFiniteAdeles _ hD).preimage (continuous_apply i))
  have hBasis (V : Set (I -> FA)) (hV : IsOpen V) (h0 : Membership.mem V 0) :
      exists j : J, Set.Subset (H j : Set (I -> FA)) V := by
    choose d hd using exists_finiteAdeleVectorPrincipalSubgroup_subset_neighborhood K I V hV h0
    exact Exists.intro (Subtype.mk d hd.1) hd.2
  choose d T a h using exists_locallyConstant_additiveCoset_expansion H hOpen hBasis Phi hPhi
  refine Exists.intro d.val (Exists.intro T (Exists.intro a (And.intro d.property (And.intro ?_ h.2))))
  intro C hC
  choose x hx using h.1 C hC
  refine Exists.intro x ?_
  rw [hx]
  rfl

end

end Robin1984.GRH
