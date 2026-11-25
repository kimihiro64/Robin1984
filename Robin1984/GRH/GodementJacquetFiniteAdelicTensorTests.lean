import Robin1984.GRH.GodementJacquetAdelicProductTest
import Robin1984.GRH.GodementJacquetFiniteAdelicFixedTensors

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement-Jacquet restricted tensor tests, idelic absolute values, and the finite-place spherical integral.
- Formalization note: Identifies the actual compact finite adelic test and restricted coefficient in each canonical finite tensor integral.
- PROVENANCE-END
-/

/-!
# Matrix tests for the finite adelic zeta tensors

The finite determinant norm separates into the local norms before taking a
complex power. Compact tests at the ramified places and the integral matrix
indicator at the other places give an actual compactly supported locally
constant test on the finite matrix adeles. Together with the restricted
coefficient, it realizes the finite adelic zeta integrand.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical

namespace Robin1984.GRH

section

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K

/-- A complex power of the finite idelic norm factors into the normalized
local powers. The factors differ from one at only finitely many places. -/
theorem heckeFiniteIdeleNorm_cpow_finprod (a : Units FA) (z : Complex) :
    (heckeFiniteIdeleNorm a : Complex) ^ z =
      finprod (fun p : P => (norm (a.val p) : Complex) ^ z) := by
  classical
  let b (p : P) : Real := norm (a.val p)
  have hb : Function.HasFiniteMulSupport b := finiteSupport_heckeFiniteIdeleFactors a
  let S := hb.toFinset
  have hSupport : Set.Subset (Function.mulSupport (fun p => (b p : Complex) ^ z))
      (S : Set P) := by
    intro p hp
    have hB : Membership.mem (Function.mulSupport b) p := by
      change Not (b p = 1)
      intro h
      apply hp
      change (b p : Complex) ^ z = 1
      rw [h, Complex.ofReal_one, Complex.one_cpow]
    change Membership.mem hb.toFinset p
    exact (Set.Finite.mem_toFinset hb).mpr hB
  have hFinite (T : Finset P) :
      ((T.prod b : Real) : Complex) ^ z = T.prod (fun p => (b p : Complex) ^ z) := by
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.prod_empty, Complex.ofReal_one, Complex.one_cpow]
    | insert p T hp ih =>
      simp only [Finset.prod_insert hp, Complex.ofReal_mul]
      rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun q _ => norm_nonneg _)), ih]
  change ((finprod b : Real) : Complex) ^ z = _
  rw [finprod_eq_prod b hb, finprod_eq_prod_of_mulSupport_subset _ hSupport]
  exact hFinite S

private theorem eval_finiteMatrixUnit_det (n : Nat)
    (g : Units (Matrix (Fin n) (Fin n) FA)) (p : P) :
    (Matrix.GeneralLinearGroup.det g).val p =
      (Units.map (finiteAdeleMatrixEval K n p).toMonoidHom g).val.det :=
  RingHom.map_det (RestrictedProduct.evalRingHom (fun q : P => q.adicCompletion K) p :
    RingHom FA (p.adicCompletion K)) g.val

/-- Finite adelic matrix evaluation commutes with the determinant weight. -/
theorem heckeFiniteDeterminantNorm_cpow_finprod
    (n : Nat) (g : Units (Matrix (Fin n) (Fin n) FA)) (z : Complex) :
    (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^ z =
      finprod (fun p : P =>
        (norm (Units.map (finiteAdeleMatrixEval K n p).toMonoidHom g).val.det : Complex) ^ z) := by
  rw [heckeFiniteIdeleNorm_cpow_finprod K]
  apply finprod_congr
  intro p
  rw [eval_finiteMatrixUnit_det K n g p]

private abbrev FiniteTensorLocalGroup (n : Nat) (p : P) :=
  Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))

private theorem hasFiniteMulSupport_finiteAdelicTensor
    (n : Nat) (E : Finset P)
    (f : forall p : P, FiniteTensorLocalGroup K n p -> Complex)
    (hUnit : forall p, Not (Membership.mem E p) -> forall g,
      Membership.mem (finiteLocalMatrixUnitSubgroup K n p) g -> f p g = 1)
    (g : Units (Matrix (Fin n) (Fin n) FA)) :
    Function.HasFiniteMulSupport
      (fun p : P => f p (Units.map (finiteAdeleMatrixEval K n p).toMonoidHom g)) := by
  classical
  have hCover : Membership.mem
      (Set.iUnion (fun S : Finset P => Set.range (finiteAdeleMatrixHaarChartEmbedding K n S))) g := by
    rw [iUnion_range_finiteAdeleMatrixHaarChartEmbedding K n]
    exact Set.mem_univ g
  choose S hS using Set.mem_iUnion.mp hCover
  refine (Union.union S E).finite_toSet.subset ?_
  intro p hp
  by_contra h
  have hS' : Not (Membership.mem (S : Set P) p) := fun hQ =>
    h (Finset.mem_union.mpr (Or.inl hQ))
  have hE' : Not (Membership.mem E p) := fun hQ =>
    h (Finset.mem_union.mpr (Or.inr hQ))
  exact hp (hUnit p hE' _ ((mem_range_finiteAdeleMatrixHaarChartEmbedding_iff K n S g).mp hS p hS'))

/-- Separate a weighted finite adelic tensor integrand into its compact test,
restricted coefficient, and finite determinant weight. -/
theorem finiteAdeleMatrixRestrictedZetaIntegrand_tensorFactorization
    (n : Nat) (E : Finset P)
    (Phi c : forall p : P, FiniteTensorLocalGroup K n p -> Complex)
    (hPhi : forall p, Not (Membership.mem E p) -> forall g,
      Membership.mem (finiteLocalMatrixUnitSubgroup K n p) g -> Phi p g = 1)
    (hc : forall p, Not (Membership.mem E p) -> forall g,
      Membership.mem (finiteLocalMatrixUnitSubgroup K n p) g -> c p g = 1)
    (g : Units (Matrix (Fin n) (Fin n) FA)) (z : Complex) :
    finiteAdeleMatrixRestrictedZetaIntegrand K n
      (fun p y => (norm y.val.det : Complex) ^ z * (Phi p y * c p y)) g =
      (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^ z *
        (finiteAdeleMatrixRestrictedZetaIntegrand K n Phi g *
          finiteAdeleMatrixRestrictedZetaIntegrand K n c g) := by
  let ev (p : P) := Units.map (finiteAdeleMatrixEval K n p).toMonoidHom g
  let a (p : P) := Phi p (ev p)
  let b (p : P) := c p (ev p)
  let d (p : P) := (norm (ev p).val.det : Complex) ^ z
  have ha : Function.HasFiniteMulSupport a := hasFiniteMulSupport_finiteAdelicTensor K n E Phi hPhi g
  have hb : Function.HasFiniteMulSupport b := hasFiniteMulSupport_finiteAdelicTensor K n E c hc g
  have hd : Function.HasFiniteMulSupport d := by
    apply (finiteSupport_heckeFiniteIdeleFactors (Matrix.GeneralLinearGroup.det g)).subset
    intro p hp
    change Not (norm ((Matrix.GeneralLinearGroup.det g).val p) = 1)
    intro hz
    apply hp
    change (norm (ev p).val.det : Complex) ^ z = 1
    rw [<- eval_finiteMatrixUnit_det K n g p, hz, Complex.ofReal_one, Complex.one_cpow]
  change finprod (fun p => d p * (a p * b p)) =
    (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^ z * (finprod a * finprod b)
  calc
    _ = finprod d * finprod (a * b) := finprod_mul_distrib hd (ha.mul hb)
    _ = finprod d * (finprod a * finprod b) :=
      congrArg (fun y : Complex => finprod d * y) (finprod_mul_distrib ha hb)
    _ = _ := congrArg (fun y : Complex => y * (finprod a * finprod b))
      (heckeFiniteDeterminantNorm_cpow_finprod K n g z).symm

private def finiteMatrixVectorHomeomorph (n : Nat) (L : Type*) [TopologicalSpace L] :
    Homeomorph (Prod (Fin n) (Fin n) -> L) (Matrix (Fin n) (Fin n) L) where
  toFun x := Matrix.of (fun i j => x (Prod.mk j i))
  invFun X := X.vec
  left_inv _x := funext (fun _ => rfl)
  right_inv _X := Matrix.ext (fun _ _ => rfl)
  continuous_toFun := continuous_matrix (fun i j => continuous_apply (Prod.mk j i))
  continuous_invFun := continuous_pi (fun i => (continuous_apply i.1).comp (continuous_apply i.2))

set_option maxHeartbeats 1000000 in
/-- Compact ramified matrix tests, with the integral indicator elsewhere,
give a compact locally constant test in the finite adelic matrix coordinates. -/
theorem exists_finiteAdeleRestrictedMatrixTest
    (n : Nat) (E : Finset P)
    [Fintype (Subtype (fun p : P => Membership.mem E p))]
    (Phi : forall p : Subtype (fun p : P => Membership.mem E p),
      LocallyConstant (Matrix (Fin n) (Fin n) (p.val.adicCompletion K)) Complex)
    (hPhi : forall p, HasCompactSupport (fun X => Phi p X)) :
    let I := Prod (Fin n) (Fin n)
    let PhiLocal (p : P) (g : FiniteTensorLocalGroup K n p) :=
      if hp : Membership.mem E p then Phi (Subtype.mk p hp) g.val else
        Set.indicator
          {y : FiniteTensorLocalGroup K n p | forall i j : Fin n,
            Membership.mem (p.adicCompletionIntegers K) (y.val i j)}
          (fun _ => (1 : Complex)) g
    exists F : LocallyConstant (I -> FA) Complex,
      And (HasCompactSupport (fun x => F x))
        (forall g : Units (Matrix (Fin n) (Fin n) FA),
          F g.val.vec = finiteAdeleMatrixRestrictedZetaIntegrand K n PhiLocal g) := by
  intro I PhiLocal
  let R := Subtype (fun p : P => Membership.mem E p)
  let e (p : R) := finiteMatrixVectorHomeomorph n (p.val.adicCompletion K)
  let psi (p : R) := LocallyConstant.comap
    (ContinuousMap.mk (e p) (e p).continuous_toFun) (Phi p)
  have hPsi (p : R) : HasCompactSupport (fun x => psi p x) :=
    HasCompactSupport.comp_homeomorph (hPhi p) (e p)
  choose F hF using exists_finiteAdeleProductCompactLocallyConstant K I E psi hPsi
  refine Exists.intro F (And.intro hF.1 ?_)
  intro g
  let ev (p : P) := Units.map (finiteAdeleMatrixEval K n p).toMonoidHom g
  let a (p : P) := PhiLocal p (ev p)
  have hUnit (p : P) (hp : Not (Membership.mem E p)) (y : FiniteTensorLocalGroup K n p)
      (hy : Membership.mem (finiteLocalMatrixUnitSubgroup K n p) y) : PhiLocal p y = 1 := by
    have hy' : Membership.mem {u : FiniteTensorLocalGroup K n p | forall i j : Fin n,
        Membership.mem (p.adicCompletionIntegers K) (u.val i j)} y := hy.1
    simp only [PhiLocal, dif_neg hp, Set.indicator_of_mem hy']
  have hSupport : Function.HasFiniteMulSupport a :=
    hasFiniteMulSupport_finiteAdelicTensor K n E PhiLocal hUnit g
  let ok := forall p : P, Not (Membership.mem E p) -> forall i j : Fin n,
    Membership.mem (p.adicCompletionIntegers K) ((ev p).val i j)
  have hVec :
      (forall p : P, Not (Membership.mem E p) -> forall i : I,
        Membership.mem (p.adicCompletionIntegers K) (g.val.vec i p)) <-> ok := by
    constructor
    . intro h p hp i j
      exact h p hp (Prod.mk j i)
    . intro h p hp i
      exact h p hp i.2 i.1
  change F g.val.vec = finprod a
  rw [hF.2 (g.val.vec)]
  by_cases h : ok
  . rw [if_pos (hVec.mpr h)]
    have hSub : Set.Subset (Function.mulSupport a) (E : Set P) := by
      intro p hp
      by_contra hnot
      have hMem : Membership.mem {u : FiniteTensorLocalGroup K n p | forall i j : Fin n,
          Membership.mem (p.adicCompletionIntegers K) (u.val i j)} (ev p) := h p hnot
      have hpE : Not (Membership.mem E p) := hnot
      exact hp (by simp only [a, PhiLocal, dif_neg hpE, Set.indicator_of_mem hMem])
    rw [finprod_eq_prod_of_mulSupport_subset a hSub,
      Finset.prod_subtype (p := fun p => Membership.mem E p) E (fun _ => Iff.rfl)]
    apply Finset.prod_congr rfl
    intro p _
    have he : (e p) (fun i : I => g.val.vec i p.val) = (ev p.val).val :=
      Matrix.ext (fun _ _ => rfl)
    change Phi p ((e p) (fun i : I => g.val.vec i p.val)) = a p.val
    rw [he]
    simp only [a, PhiLocal, dif_pos p.property]
  . rw [if_neg (fun hv => h (hVec.mp hv))]
    choose p hp using not_forall.mp h
    have ht := Classical.not_imp.mp hp
    have hOut := ht.1
    have hNon : Not (Membership.mem {u : FiniteTensorLocalGroup K n p | forall i j : Fin n,
        Membership.mem (p.adicCompletionIntegers K) (u.val i j)} (ev p)) := ht.2
    have hZero : a p = 0 := by
      simp only [a, PhiLocal, dif_neg hOut, Set.indicator_of_notMem hNon]
    exact (finprod_eq_zero a p hZero hSupport).symm

private noncomputable abbrev FiniteSphericalSubgroup (n : Nat) (p : P) :=
  valuationIntegralMatrixSubgroup
    (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) n

set_option maxHeartbeats 1200000 in
/-- For a finite adelic spherical tensor, the actual compact matrix test times
the restricted coefficient and determinant weight is the prescribed zeta
integrand. -/
theorem exists_finiteAdeleSphericalTensorTest
    (n : Nat) (E : Finset P)
    [Fintype (Subtype (fun p : P => Membership.mem E p))]
    [forall p : P, MeasurableSpace (FiniteSphericalSubgroup K n p)]
    (nu : forall p : P, Measure (FiniteSphericalSubgroup K n p))
    [forall p, IsProbabilityMeasure (nu p)]
    (chi : forall p : P, Fin n -> MonoidHom (Units (p.adicCompletion K)) Complex)
    (hUnit : forall p, Not (Membership.mem E p) -> forall i x,
      Membership.mem (heckeLocalUnitShell p) x -> chi p i x = 1)
    (Phi : forall p : Subtype (fun p : P => Membership.mem E p),
      LocallyConstant (Matrix (Fin n) (Fin n) (p.val.adicCompletion K)) Complex)
    (hPhi : forall p, HasCompactSupport (fun X => Phi p X))
    (c : forall p : Subtype (fun p : P => Membership.mem E p),
      FiniteTensorLocalGroup K n p.val -> Complex) :
    let delta : Real := ((n : Real) - 1) / 2
    let C (p : P) (y : FiniteTensorLocalGroup K n p) :=
      if hp : Membership.mem E p then c (Subtype.mk p hp) y else
        heckeUnramifiedSphericalCoefficient p n (nu p) (productDiagonalCharacter n (chi p)) y
    let h (s : Complex) (p : P) (y : FiniteTensorLocalGroup K n p) :=
      if hp : Membership.mem E p then
        (norm y.val.det : Complex) ^ (s + (delta : Complex)) *
          (Phi (Subtype.mk p hp) y.val * c (Subtype.mk p hp) y)
      else heckeUnramifiedLocalZetaIntegrand p n (nu p) (chi p) s y
    exists F : LocallyConstant (Prod (Fin n) (Fin n) -> FA) Complex,
      And (HasCompactSupport (fun x => F x))
        (forall (s : Complex) (g : Units (Matrix (Fin n) (Fin n) FA)),
          finiteAdeleMatrixRestrictedZetaIntegrand K n (h s) g =
            (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
              (s + (delta : Complex)) *
                (F g.val.vec * finiteAdeleMatrixRestrictedZetaIntegrand K n C g)) := by
  intro delta C h
  let T (p : P) : Set (FiniteTensorLocalGroup K n p) :=
    {y | forall i j : Fin n, Membership.mem (p.adicCompletionIntegers K) (y.val i j)}
  let PL (p : P) (y : FiniteTensorLocalGroup K n p) :=
    if hp : Membership.mem E p then Phi (Subtype.mk p hp) y.val else
      Set.indicator (T p) (fun _ => (1 : Complex)) y
  choose F hF using exists_finiteAdeleRestrictedMatrixTest K n E Phi hPhi
  have ha (p : P) (hp : Not (Membership.mem E p)) (y : FiniteTensorLocalGroup K n p)
      (hy : Membership.mem (finiteLocalMatrixUnitSubgroup K n p) y) : PL p y = 1 := by
    have hMem : Membership.mem (T p) y := hy.1
    simp only [PL, dif_neg hp, Set.indicator_of_mem hMem]
  have hb (p : P) (hp : Not (Membership.mem E p)) (y : FiniteTensorLocalGroup K n p)
      (hy : Membership.mem (finiteLocalMatrixUnitSubgroup K n p) y) : C p y = 1 := by
    let v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
    have hy' : Membership.mem (valuationIntegralMatrixSubgroup v n) y :=
      (mem_valuationIntegralMatrixSubgroup_iff v n y).mpr hy
    have hZ := heckeUnramifiedLocalZetaIntegrand_eq_one_of_mem_integral
      p n (nu p) (chi p) (hUnit p hp) (-(delta : Complex)) y hy'
    have hW : heckeUnramifiedLocalMatrixWeight p n (-(delta : Complex)) y = 1 := by
      have hMem : Membership.mem (T p) y := hy.1
      change Set.indicator (T p) (fun g => (norm g.val.det : Complex) ^
        (-(delta : Complex) + (delta : Complex))) y = 1
      rw [Set.indicator_of_mem hMem, neg_add_cancel, Complex.cpow_zero]
    simpa only [C, dif_neg hp, heckeUnramifiedLocalZetaIntegrand, hW, one_mul] using hZ
  have hEq (s : Complex) : h s = (fun p y =>
      (norm y.val.det : Complex) ^ (s + (delta : Complex)) * (PL p y * C p y)) := by
    funext p y
    by_cases hp : Membership.mem E p
    . simp only [h, PL, C, dif_pos hp]
    . simp only [h, PL, C, dif_neg hp, heckeUnramifiedLocalZetaIntegrand]
      change Set.indicator (T p) (fun g => (norm g.val.det : Complex) ^
        (s + (delta : Complex))) y * _ = _
      by_cases hy : Membership.mem (T p) y
      . simp only [Set.indicator_of_mem hy, one_mul]
      . simp only [Set.indicator_of_notMem hy, zero_mul, mul_zero]
  refine Exists.intro F (And.intro hF.1 ?_)
  intro s g
  rw [hEq s, finiteAdeleMatrixRestrictedZetaIntegrand_tensorFactorization K n E
    PL C ha hb g (s + (delta : Complex))]
  rw [hF.2 g]

end

end Robin1984.GRH
