import Mathlib.Topology.LocallyConstant.Algebra
import Robin1984.GRH.GodementJacquetFiniteAdelicTestRectangles
import Robin1984.GRH.GodementJacquetMatrixPoisson

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The restricted product topology of finite adeles and the finite coset decomposition of compactly supported locally constant tests.
- Formalization note: Builds the finite adelic restricted product test from finitely many local factors and expands its product with a joint archimedean Schwartz test in principal matrix rectangles.
- PROVENANCE-END
-/

/-!
# Restricted product tests on adelic matrices

At the chosen finite places the test uses prescribed local factors. At the
other finite places it uses the integral indicator. Compact local support
gives a compactly supported locally constant finite adelic test. Pairing it
with an archimedean Schwartz test then gives a finite sum of the matrix
rectangles used by the theta argument.
-/

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace Robin1984.GRH

section

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K

private def outsideIntegralVectorSubgroup (I : Type*) (E : Finset P) :
    AddSubgroup (I -> FA) where
  carrier := fun x => forall p : P, Not (Membership.mem E p) -> forall i : I,
    Membership.mem (p.adicCompletionIntegers K) (x i p)
  zero_mem' := fun p _ _ => (p.adicCompletionIntegers K).zero_mem
  add_mem' := fun hx hy p hp i => add_mem (hx p hp i) (hy p hp i)
  neg_mem' := fun hx p hp i => neg_mem (hx p hp i)

private theorem isClopen_outsideIntegralVectorSubgroup
    (I : Type*) [Fintype I] (E : Finset P) :
    IsClopen (outsideIntegralVectorSubgroup K I E : Set (I -> FA)) := by
  let H := outsideIntegralVectorSubgroup K I E
  let B : Set FA := (heckeIntegralFiniteAdeles (K := K) : AddSubgroup FA)
  have hB : IsOpen B := by
    have hEq : (heckeScaledIntegralFiniteAdeles (1 : K) : Set FA) = B := by
      apply Set.ext
      intro x
      change (exists y : FA, And (Membership.mem B y) (y * algebraMap K FA 1 = x)) <->
        Membership.mem B x
      simp only [map_one, mul_one, exists_eq_right]
    rw [<- hEq]
    exact isOpen_heckeScaledIntegralFiniteAdeles 1 one_ne_zero
  let Q : Set (I -> FA) := Set.iInter (fun i : I => Set.preimage (fun v : I -> FA => v i) B)
  have hQ : IsOpen Q := isOpen_iInter_of_finite
    (fun i : I => hB.preimage (continuous_apply i))
  have hQ0 : Membership.mem Q 0 :=
    Set.mem_iInter.mpr (fun _ => (heckeIntegralFiniteAdeles : AddSubgroup FA).zero_mem)
  have hSub : Set.Subset Q (H : Set (I -> FA)) := by
    intro x hx p _ i
    have hi : Membership.mem (Set.preimage (fun v : I -> FA => v i) B) x :=
      Set.mem_iInter.mp hx i
    exact hi p
  have hOpen : IsOpen (H : Set (I -> FA)) :=
    H.isOpen_of_mem_nhds (Filter.mem_of_superset (hQ.mem_nhds hQ0) hSub)
  exact And.intro (H.isClosed_of_isOpen hOpen) hOpen

/-- Assemble local tests at the places in `E`, with the integral indicator at every
other place, to obtain a locally constant test on finite adelic vectors. -/
theorem exists_finiteAdeleProductLocallyConstant
    (I : Type*) [Fintype I] (E : Finset P)
    [Fintype (Subtype (fun p : P => Membership.mem E p))]
    (Phi : forall p : Subtype (fun p : P => Membership.mem E p),
      LocallyConstant (I -> p.val.adicCompletion K) Complex) :
    exists F : LocallyConstant (I -> FA) Complex, forall x : I -> FA,
      F x = @ite Complex
        (forall p : P, Not (Membership.mem E p) -> forall i : I,
          Membership.mem (p.adicCompletionIntegers K) (x i p))
        (Classical.propDecidable _)
        (Finset.univ.prod (fun p : Subtype (fun p : P => Membership.mem E p) =>
          Phi p (fun i => x i p.val))) 0 := by
  classical
  let R := Subtype (fun p : P => Membership.mem E p)
  let H := outsideIntegralVectorSubgroup K I E
  let chi : LocallyConstant (I -> FA) Complex :=
    LocallyConstant.charFn Complex (isClopen_outsideIntegralVectorSubgroup K I E)
  let proj (p : R) : ContinuousMap (I -> FA) (I -> p.val.adicCompletion K) :=
    ContinuousMap.mk (fun x i => x i p.val)
      (continuous_pi (fun i => (RestrictedProduct.continuous_eval p.val).comp (continuous_apply i)))
  let factors (p : R) := LocallyConstant.comap (proj p) (Phi p)
  let F := chi * Finset.univ.prod factors
  refine Exists.intro F ?_
  intro x
  have hProd (S : Finset R) : (S.prod factors) x = S.prod (fun p => Phi p (fun i => x i p.val)) := by
    induction S using Finset.induction_on with
    | empty => rfl
    | insert p S hp ih =>
      rw [Finset.prod_insert hp, LocallyConstant.mul_apply, ih, Finset.prod_insert hp]
      rfl
  change (chi * Finset.univ.prod factors) x = _
  rw [LocallyConstant.mul_apply, hProd]
  change Set.indicator (H : Set (I -> FA)) (1 : (I -> FA) -> Complex) x * _ = _
  by_cases hx : Membership.mem H x
  . have hx' : forall p : P, Not (Membership.mem E p) -> forall i : I,
      Membership.mem (p.adicCompletionIntegers K) (x i p) := hx
    rw [Set.indicator_of_mem hx, if_pos hx']
    exact one_mul _
  . have hx' : Not (forall p : P, Not (Membership.mem E p) -> forall i : I,
      Membership.mem (p.adicCompletionIntegers K) (x i p)) := hx
    rw [Set.indicator_of_notMem hx, if_neg hx', zero_mul]

set_option maxHeartbeats 800000 in
/-- Compact support of the tests at the places in `E` gives compact support for
the assembled finite adelic test. A single inverse integral dilation bounds
its support at all places. -/
theorem exists_finiteAdeleProductCompactLocallyConstant
    (I : Type*) [Fintype I] (E : Finset P)
    [Fintype (Subtype (fun p : P => Membership.mem E p))]
    (Phi : forall p : Subtype (fun p : P => Membership.mem E p),
      LocallyConstant (I -> p.val.adicCompletion K) Complex)
    (hPhi : forall p, HasCompactSupport (fun x => Phi p x)) :
    exists F : LocallyConstant (I -> FA) Complex,
      And (HasCompactSupport (fun x => F x)) (forall x : I -> FA,
        F x = @ite Complex
          (forall p : P, Not (Membership.mem E p) -> forall i : I,
            Membership.mem (p.adicCompletionIntegers K) (x i p))
          (Classical.propDecidable _)
          (Finset.univ.prod (fun p : Subtype (fun p : P => Membership.mem E p) =>
            Phi p (fun i => x i p.val))) 0) := by
  classical
  let R := Subtype (fun p : P => Membership.mem E p)
  choose F hF using exists_finiteAdeleProductLocallyConstant K I E Phi
  have hBound (p : R) (i : I) :
      exists B : Real, forall y, Membership.mem (tsupport (fun x => Phi p x)) y -> norm (y i) <= B := by
    have hC : IsCompact (tsupport (fun x => Phi p x)) := hPhi p
    have hImage := hC.image (continuous_norm.comp (continuous_apply i))
    choose M hM using hImage.bddAbove
    exact Exists.intro M (fun y hy => hM (Set.mem_image_of_mem _ hy))
  choose M hM using hBound
  let B (p : R) := 1 + Finset.univ.sum (fun i : I => abs (M p i))
  have hB (p : R) : 0 < B p := by
    have hS : 0 <= Finset.univ.sum (fun i : I => abs (M p i)) :=
      Finset.sum_nonneg (fun i _ => abs_nonneg (M p i))
    exact add_pos_of_pos_of_nonneg zero_lt_one hS
  let eps (p : P) : Real :=
    if hp : Membership.mem E p then Inv.inv (B (Subtype.mk p hp)) else 1
  have hEps (p : P) (hp : Membership.mem E p) : 0 < eps p := by
    simp only [eps, dif_pos hp]
    exact inv_pos.mpr (hB (Subtype.mk p hp))
  choose d hd using exists_integer_small_at_finitePlaces K E eps hEps
  let D := algebraMap (RingOfIntegers K) K d
  have hD : Not (D = 0) := by
    intro h
    apply hd.1
    exact (FaithfulSMul.algebraMap_injective (RingOfIntegers K) K) (h.trans (map_zero _).symm)
  let C := finiteAdelePrincipalRectangle K I (0 : I -> FA) (Inv.inv D)
  have hC : IsCompact C := isCompact_finiteAdelePrincipalRectangle K I 0 _
  have hClosed : IsClosed C := by
    let H := heckeScaledIntegralFiniteAdeles (Inv.inv D)
    have hH : IsClosed (H : Set FA) :=
      H.isClosed_of_isOpen (isOpen_heckeScaledIntegralFiniteAdeles _ (inv_ne_zero hD))
    have hEq : C = Set.iInter (fun i : I => Set.preimage (fun x : I -> FA => x i) (H : Set FA)) := by
      apply Set.ext
      intro x
      change Membership.mem (finiteAdelePrincipalRectangle K I 0 (Inv.inv D)) x <-> _
      rw [mem_finiteAdelePrincipalRectangle_iff]
      constructor
      . intro h
        apply Set.mem_iInter.mpr
        intro i
        choose y hy using h i
        have he : y = x i := by simpa only [Pi.zero_apply, zero_add] using hy.2
        change Membership.mem H (x i)
        rw [<- he]
        exact hy.1
      . intro h i
        exact Exists.intro (x i) (And.intro (Set.mem_iInter.mp h i) (zero_add (x i)))
    rw [hEq]
    exact isClosed_iInter (fun i => hH.preimage (continuous_apply i))
  refine Exists.intro F (And.intro ?_ hF)
  have hSupport : Set.Subset (Function.support (fun x => F x)) C := by
    intro x hx
    have hxNZ : Not (F x = 0) := hx
    have hOut : forall p : P, Not (Membership.mem E p) -> forall i : I,
        Membership.mem (p.adicCompletionIntegers K) (x i p) := by
      by_contra h
      apply hxNZ
      rw [hF x, if_neg h]
    have hNonzero (p : R) : Not (Phi p (fun i => x i p.val) = 0) := by
      intro h
      apply hxNZ
      rw [hF x, if_pos hOut]
      exact Finset.prod_eq_zero (Finset.mem_univ p) h
    apply (mem_finiteAdelePrincipalRectangle_iff K I 0 x (Inv.inv D)).mpr
    intro i
    have hi : Membership.mem (heckeScaledIntegralFiniteAdeles (Inv.inv D)) (x i) := by
      let y := x i * algebraMap K FA D
      change exists z : FA, And (Membership.mem (heckeIntegralFiniteAdeles (K := K)) z)
        (z * algebraMap K FA (Inv.inv D) = x i)
      refine Exists.intro y (And.intro ?_ ?_)
      . intro p
        change Membership.mem (p.adicCompletionIntegers K)
          (x i p * algebraMap K (p.adicCompletion K) D)
        rw [<- IsScalarTower.algebraMap_apply (RingOfIntegers K) K (p.adicCompletion K)]
        by_cases hp : Membership.mem E p
        . let q : R := Subtype.mk p hp
          have hPc : Membership.mem (Function.support (fun y => Phi q y))
              (fun j : I => x j p) := hNonzero q
          have hBase : norm (x i p) <= M q i :=
            hM q i (fun j : I => x j p) (subset_closure hPc)
          have hxB : norm (x i p) <= B q := by
            calc
              _ <= M q i := hBase
              _ <= abs (M q i) := le_abs_self _
              _ <= Finset.univ.sum (fun j : I => abs (M q j)) :=
                Finset.single_le_sum (fun j _ => abs_nonneg (M q j)) (Finset.mem_univ i)
              _ <= B q := le_add_of_nonneg_left zero_le_one
          have hVal :
              norm (algebraMap (RingOfIntegers K) (p.adicCompletion K) d) < Inv.inv (B q) := by
            have heq := congrFun (HeightOneSpectrum.algebraMap_adicCompletion
              (S := RingOfIntegers K) (K := K) (v := p)) d
            have hlt : norm (algebraMap (RingOfIntegers K) (p.adicCompletion K) d) < eps p :=
              (congrArg (fun z : p.adicCompletion K => norm z) heq).trans_lt (hd.2 p hp)
            exact hlt.trans_eq (dif_pos hp)
          have hSmall : norm (x i p * algebraMap (RingOfIntegers K) (p.adicCompletion K) d) < 1 := by
            rw [norm_mul]
            calc
              _ <= B q * norm (algebraMap (RingOfIntegers K) (p.adicCompletion K) d) :=
                mul_le_mul_of_nonneg_right hxB (norm_nonneg _)
              _ < B q * Inv.inv (B q) := mul_lt_mul_of_pos_left hVal (hB q)
              _ = 1 := by field_simp [(hB q).ne']
          exact Valued.toNormedField.norm_le_one_iff.mp hSmall.le
        . exact (p.adicCompletionIntegers K).mul_mem _ _ (hOut p hp i)
            (HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers K) K p d)
      . have hOne : D * Inv.inv D = 1 := by field_simp [hD]
        change (x i * algebraMap K FA D) * algebraMap K FA (Inv.inv D) = x i
        rw [mul_assoc, <- map_mul, hOne, map_one, mul_one]
    exact Exists.intro (x i) (And.intro hi (zero_add (x i)))
  change IsCompact (closure (Function.support (fun x => F x)))
  exact hC.of_isClosed_subset isClosed_closure (closure_minimal hSupport hClosed)

end

section

open scoped Classical RealInnerProductSpace FourierTransform

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "Ix" => Prod (Fin n) (Fin n)
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K
local notation "MA" => Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K)
local notation "Arch" => PiLp 2 (fun _ : Ix => DedekindZeta.Theta.minkowskiSpace K)

/-- The product of a joint archimedean Schwartz test and a compactly supported
locally constant finite adelic test is a finite sum of matrix rectangles
with one nonzero integral modulus. -/
theorem exists_godementJacquetProductTest_eq_sum_rectangles
    (f : SchwartzMap Arch Complex) (Phi : LocallyConstant (Ix -> FA) Complex)
    (hPhi : HasCompactSupport (fun x => Phi x)) :
    let xi (X : MA) : Arch := WithLp.toLp 2 (fun i : Ix =>
      DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (X.vec i).1))
    let xf (X : MA) (i : Ix) : FA := (X.vec i).2
    exists (d : RingOfIntegers K) (S : Finset (Set (Ix -> FA)))
        (a : Set (Ix -> FA) -> Ix -> FA) (b : Set (Ix -> FA) -> Complex),
      And (Not (d = 0)) (forall X : MA, f (xi X) * Phi (xf X) =
        S.sum (fun C => godementJacquetMatrixRectangle K (a C) d (HSMul.hSMul (b C) f) X)) := by
  classical
  intro xi xf
  choose d S b h using exists_locallyConstant_finiteAdelePrincipalRectangle_expansion K Ix Phi hPhi
  have hCenter (C : {C : Set (Ix -> FA) // Membership.mem S C}) := h.2.1 C.val C.property
  choose center hCenterEq using hCenter
  let a (C : Set (Ix -> FA)) := if hC : Membership.mem S C then center (Subtype.mk C hC) else 0
  refine Exists.intro d (Exists.intro S (Exists.intro a (Exists.intro b (And.intro h.1 ?_))))
  intro X
  rw [h.2.2.2 (xf X), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C hC
  let dd := algebraMap (RingOfIntegers K) K d
  have hSet : C = finiteAdelePrincipalRectangle K Ix (a C) dd := by
    simpa only [a, dif_pos hC] using hCenterEq (Subtype.mk C hC)
  let w (i : Ix) :=
    Set.indicator (heckeFiniteAdelePrincipalCoset (a C i) dd) (fun _ => (1 : Complex)) (xf X i)
  change f (xi X) * @ite Complex (Membership.mem C (xf X)) (Classical.propDecidable _) (b C) 0 =
    (HSMul.hSMul (b C) f) (xi X) * Finset.univ.prod w
  by_cases hX : Membership.mem C (xf X)
  . have hIn : Membership.mem (finiteAdelePrincipalRectangle K Ix (a C) dd) (xf X) := by
      rw [<- hSet]
      exact hX
    have hAll := (mem_finiteAdelePrincipalRectangle_iff K Ix (a C) (xf X) dd).mp hIn
    have hW (i : Ix) : w i = 1 := Set.indicator_of_mem (hAll i) _
    rw [if_pos hX]
    simp only [hW, Finset.prod_const_one, mul_one, smul_apply, smul_eq_mul]
    exact mul_comm _ _
  . have hNot : Not (forall i : Ix,
        Membership.mem (heckeFiniteAdelePrincipalCoset (a C i) dd) (xf X i)) := by
      intro hh
      apply hX
      rw [hSet]
      exact (mem_finiteAdelePrincipalRectangle_iff K Ix (a C) (xf X) dd).mpr hh
    choose i hi using not_forall.mp hNot
    have hz : w i = 0 := Set.indicator_of_notMem hi _
    rw [if_neg hX, Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero, mul_zero]

end

end Robin1984.GRH
