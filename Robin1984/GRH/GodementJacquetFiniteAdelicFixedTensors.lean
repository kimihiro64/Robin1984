import Robin1984.GRH.GodementJacquetLocalZetaFixedCombination

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Finite multilinearity of restricted products and the normalized finite adelic matrix-unit charts.
- Formalization note: Expands the finite ramified sums as fixed tensor selections and transports the identity through the Haar chart cover and the integral.
- PROVENANCE-END
-/

/-!
# Fixed tensor expansions of finite adelic zeta integrands

At each place in a finite set, replace its factor by a finite linear
combination. The resulting restricted product expands into a finite sum
indexed by one choice at each such place. The spherical factor remains
fixed outside that set. Absolute integrability of the chosen tensors
allows the same expansion under the Haar integral.
-/

set_option autoImplicit false

open Function IsDedekindDomain MeasureTheory NumberField

namespace Robin1984.GRH

private theorem finprod_ramifiedPiece_eq_mul
    {P : Type*} (E : Finset P) [Fintype (Subtype (fun p : P => Membership.mem E p))]
    [DecidablePred (fun p : P => Membership.mem E p)]
    (a : (Subtype (fun p : P => Membership.mem E p)) -> Complex) (b : P -> Complex)
    (hB : HasFiniteMulSupport (fun p : P => if Membership.mem E p then 1 else b p)) :
    finprod (fun p : P => if hp : Membership.mem E p then a (Subtype.mk p hp) else b p) =
      (Finset.univ.prod a) * finprod (fun p : P => if Membership.mem E p then 1 else b p) := by
  let aE (p : P) := if hp : Membership.mem E p then a (Subtype.mk p hp) else 1
  let bE (p : P) := if Membership.mem E p then 1 else b p
  have hA : Set.Subset (mulSupport aE) (E : Set P) := by
    intro p hp
    by_contra h
    exact hp (dif_neg h)
  have hFin : HasFiniteMulSupport aE := E.finite_toSet.subset hA
  have hProd : finprod aE = Finset.univ.prod a := by
    have hE : E.finite_toSet.toFinset = E := Finset.finite_toSet_toFinset E
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hA E.finite_toSet, hE,
      Finset.prod_subtype (p := fun p => Membership.mem (E : Set P) p) E (fun _ => Iff.rfl)]
    apply Finset.prod_congr rfl
    intro p _
    exact dif_pos p.property
  calc
    _ = finprod (fun p : P => aE p * bE p) := by
      apply congrArg finprod
      funext p
      by_cases hp : Membership.mem E p
      . simp only [aE, bE, dif_pos hp, if_pos hp, mul_one]
      . simp only [aE, bE, dif_neg hp, if_neg hp, one_mul]
    _ = _ := by rw [finprod_mul_distrib hFin hB, hProd]

private theorem finprod_ramifiedSum_eq_sum_tensors
    {P : Type*} [DecidableEq P] (E : Finset P)
    [Fintype (Subtype (fun p : P => Membership.mem E p))]
    [DecidablePred (fun p : P => Membership.mem E p)]
    (I : (Subtype (fun p : P => Membership.mem E p)) -> Type*) [forall p, Fintype (I p)]
    (a v : forall p : Subtype (fun p : P => Membership.mem E p), I p -> Complex) (b : P -> Complex)
    (hB : HasFiniteMulSupport (fun p : P => if Membership.mem E p then 1 else b p)) :
    finprod (fun p : P => if hp : Membership.mem E p then
      Finset.univ.sum (fun i : I (Subtype.mk p hp) => a (Subtype.mk p hp) i * v (Subtype.mk p hp) i)
      else b p) =
      Finset.univ.sum (fun choice : forall p : Subtype (fun p : P => Membership.mem E p), I p =>
        (Finset.univ.prod (fun p => a p (choice p))) *
          finprod (fun p : P => if hp : Membership.mem E p then
            v (Subtype.mk p hp) (choice (Subtype.mk p hp)) else b p)) := by
  classical
  rw [finprod_ramifiedPiece_eq_mul E (fun p => Finset.univ.sum (fun i => a p i * v p i)) b hB,
    Fintype.prod_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro choice _
  rw [finprod_ramifiedPiece_eq_mul E (fun p => v p (choice p)) b hB,
    Finset.prod_mul_distrib, mul_assoc]

section

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)

private noncomputable abbrev localMatrixGroup (n : Nat) (p : P) :=
  Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))

private theorem finiteAdeleMatrixRestrictedZetaIntegrand_fixedTensorExpansion_on_chart
    (n : Nat) (E S : Finset P) [DecidableEq P]
    [Fintype (Subtype (fun p : P => Membership.mem E p))] [Fintype (S : Set P)]
    [DecidablePred (fun p : P => Membership.mem E p)] (hES : E <= S)
    (I : (Subtype (fun p : P => Membership.mem E p)) -> Type*) [forall p, Fintype (I p)]
    (a : forall p : Subtype (fun p : P => Membership.mem E p), I p -> Complex)
    (v : forall p : Subtype (fun p : P => Membership.mem E p), I p -> localMatrixGroup K n p.val -> Complex)
    (b : forall p : P, localMatrixGroup K n p -> Complex)
    (hUnit : forall p : P, Not (Membership.mem E p) -> forall y,
      Membership.mem (finiteLocalMatrixUnitSubgroup K n p) y -> b p y = 1)
    (x : FiniteAdeleMatrixHaarChart K n S) :
    let g := finiteAdeleMatrixHaarChartEmbedding K n S x
    let f (p : P) (y : localMatrixGroup K n p) :=
      if hp : Membership.mem E p then
        Finset.univ.sum (fun i : I (Subtype.mk p hp) =>
          a (Subtype.mk p hp) i * v (Subtype.mk p hp) i y) else b p y
    let pick (choice : forall p : Subtype (fun p : P => Membership.mem E p), I p) (p : P) (y : localMatrixGroup K n p) :=
      if hp : Membership.mem E p then v (Subtype.mk p hp) (choice (Subtype.mk p hp)) y else b p y
    finiteAdeleMatrixRestrictedZetaIntegrand K n f g =
      Finset.univ.sum (fun choice : forall p : Subtype (fun p : P => Membership.mem E p), I p =>
        (Finset.univ.prod (fun p => a p (choice p))) *
          finiteAdeleMatrixRestrictedZetaIntegrand K n (pick choice) g) := by
  intro g f pick
  let ev (p : P) : localMatrixGroup K n p :=
    Units.map (finiteAdeleMatrixEval K n p).toMonoidHom g
  let bG (p : P) := b p (ev p)
  have hSupport : HasFiniteMulSupport (fun p : P => if Membership.mem E p then 1 else bG p) := by
    apply S.finite_toSet.subset
    intro p hp
    by_contra hNot
    let q : {q : P // Not (Membership.mem (S : Set P) q)} := Subtype.mk p hNot
    have hpE : Not (Membership.mem E p) := fun h => hNot (hES h)
    have hEval := finiteAdeleMatrixHaarChartEval_of_notMem K n S x q
    have hOne : bG p = 1 := (congrArg (b p) hEval).trans (hUnit p hpE _ (x.2 q).property)
    exact hp ((if_neg hpE).trans hOne)
  exact finprod_ramifiedSum_eq_sum_tensors E I a (fun p i => v p i (ev p.val)) bG hSupport

/-- Expand a finite-place zeta integrand with finite sums at the ramified
places into individual tensor choices, both pointwise and after Haar
integration when every tensor choice is integrable. -/
theorem finiteAdeleMatrixRestrictedZetaIntegrand_fixedTensorExpansion
    (n : Nat) (E : Finset P) [DecidableEq P]
    [Fintype (Subtype (fun p : P => Membership.mem E p))]
    [forall S : Finset P, Fintype (S : Set P)]
    [DecidablePred (fun p : P => Membership.mem E p)]
    (I : Subtype (fun p : P => Membership.mem E p) -> Type*) [forall p, Fintype (I p)]
    (a : forall p : Subtype (fun p : P => Membership.mem E p), I p -> Complex)
    (v : forall p : Subtype (fun p : P => Membership.mem E p), I p ->
        localMatrixGroup K n p.val -> Complex)
    (b : forall p : P, localMatrixGroup K n p -> Complex)
    (hUnit : forall p : P, Not (Membership.mem E p) -> forall y,
      Membership.mem (finiteLocalMatrixUnitSubgroup K n p) y -> b p y = 1) :
    let G := Units (Matrix (Fin n) (Fin n) (FiniteAdeleRing (RingOfIntegers K) K))
    let C := forall p : Subtype (fun p : P => Membership.mem E p), I p
    let f (p : P) (y : localMatrixGroup K n p) :=
      if hp : Membership.mem E p then
        Finset.univ.sum (fun i : I (Subtype.mk p hp) =>
          a (Subtype.mk p hp) i * v (Subtype.mk p hp) i y) else b p y
    let pick (choice : C) (p : P) (y : localMatrixGroup K n p) :=
      if hp : Membership.mem E p then v (Subtype.mk p hp) (choice (Subtype.mk p hp)) y else b p y
    let w (choice : C) := Finset.univ.prod (fun p => a p (choice p))
    let F (g : G) := finiteAdeleMatrixRestrictedZetaIntegrand K n f g
    let H (choice : C) (g : G) := finiteAdeleMatrixRestrictedZetaIntegrand K n (pick choice) g
    And (forall g : G, F g = Finset.univ.sum (fun choice : C => w choice * H choice g))
      (forall [MeasurableSpace G] (mu : Measure G), (forall choice : C, Integrable (H choice) mu) ->
        And (Integrable F mu)
          (integral mu F = Finset.univ.sum (fun choice : C => w choice * integral mu (H choice)))) := by
  intro G C f pick w F H
  have hPoint (g : G) : F g = Finset.univ.sum (fun choice : C => w choice * H choice g) := by
    have hCover : Membership.mem
        (Set.iUnion (fun S : Finset P => Set.range (finiteAdeleMatrixHaarChartEmbedding K n S))) g := by
      rw [iUnion_range_finiteAdeleMatrixHaarChartEmbedding K n]
      exact Set.mem_univ g
    choose S hS using Set.mem_iUnion.mp hCover
    have hLarger := monotone_range_finiteAdeleMatrixHaarChartEmbedding K n
      (Finset.subset_union_left : S <= Union.union S E) hS
    choose x hx using hLarger
    rw [<- hx]
    exact finiteAdeleMatrixRestrictedZetaIntegrand_fixedTensorExpansion_on_chart
      K n E (Union.union S E) Finset.subset_union_right I a v b hUnit x
  refine And.intro hPoint ?_
  intro _ mu hIntegral
  have hWeighted (c : C) : Integrable (fun g : G => w c * H c g) mu :=
    (hIntegral c).const_mul _
  rw [funext hPoint]
  refine And.intro (integrable_finsetSum Finset.univ (fun c _ => hWeighted c)) ?_
  rw [integral_finsetSum Finset.univ (fun c _ => hWeighted c)]
  simp only [integral_const_mul]

/-- Realize any finite set of local translates by one finite adelic matrix
unit. The product coefficient at the translated matrix agrees with the
product of the chosen local translates. -/
theorem exists_finiteAdeleMatrixUnit_translateRestrictedCoefficient
    (n : Nat) (E : Finset P) [DecidablePred (fun p : P => Membership.mem E p)]
    (T : forall p : Subtype (fun p : P => Membership.mem E p), localMatrixGroup K n p.val)
    (c : forall p : P, localMatrixGroup K n p -> Complex) :
    let G := Units (Matrix (Fin n) (Fin n) (FiniteAdeleRing (RingOfIntegers K) K))
    let ev (p : P) : MonoidHom G (localMatrixGroup K n p) :=
      Units.map (finiteAdeleMatrixEval K n p).toMonoidHom
    let t (p : P) : localMatrixGroup K n p :=
      if hp : Membership.mem E p then T (Subtype.mk p hp) else 1
    exists A : G,
      And (forall p : P, ev p A = t p)
        (forall g : G,
          finiteAdeleMatrixRestrictedZetaIntegrand K n c (A * g) =
          finiteAdeleMatrixRestrictedZetaIntegrand K n
            (fun p y => c p (t p * y)) g) := by
  intro G ev t
  let x : FiniteAdeleMatrixHaarChart K n E := Prod.mk T (fun _ => 1)
  let A : G := finiteAdeleMatrixHaarChartEmbedding K n E x
  have hEval (p : P) : ev p A = t p := by
    by_cases hp : Membership.mem E p
    . simp only [t, dif_pos hp]
      exact finiteAdeleMatrixHaarChartEval_of_mem K n E x (Subtype.mk p hp)
    . simp only [t, dif_neg hp]
      exact finiteAdeleMatrixHaarChartEval_of_notMem K n E x (Subtype.mk p hp)
  refine Exists.intro A (And.intro hEval (fun g => ?_))
  change finprod (fun p : P => c p (ev p (A * g))) =
    finprod (fun p : P => c p (t p * ev p g))
  apply congrArg finprod
  funext p
  rw [map_mul, hEval p]

end

end Robin1984.GRH
