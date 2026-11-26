import Robin1984.GRH.HeckeTateDualSupport

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Tate theta sum over nonzero principal adeles and its descent to the norm-one idele class quotient.
- Formalization note: Reindexes the principal sum under multiplication by a field unit and transfers uniform bounds to the quotient.
- PROVENANCE-END
-/

/-!
# Theta sums on the norm-one idele class quotient

Multiplication by a principal idele permutes the field terms of the
theta sum. The resulting function on the norm-one idele class group
inherits the uniform decay bound for both the original and dual tests.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev FiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev MixedSpace (K : Type*) [Field K] :=
  NumberField.mixedEmbedding.mixedSpace K

/-- The complex theta summand at one field element, with the zero term removed. -/
noncomputable def heckeTateThetaNormOneTerm
    (f : SchwartzMap (MixedSpace K) Complex) (T : FiniteAdeles K -> Complex)
    (a : heckeNormOneIdeles K) (t : Real) (x : K) : Complex :=
  let E : Homeomorph (Units (AdeleRing (RingOfIntegers K) K))
      (Prod (Units (InfiniteAdeleRing K)) (Units (FiniteAdeles K))) := Homeomorph.prodUnits
  let b := E a.val
  let c := Real.exp (t / (Module.finrank Rat K : Real))
  if x = 0 then 0 else
    f (HSMul.hSMul c (InfiniteAdeleRing.ringEquiv_mixedSpace K b.1.val * mixedEmbedding K x)) *
      T (b.2.val * algebraMap K (FiniteAdeles K) x)

/-- The absolute value of the complex term is the summand controlled by uniform decay. -/
theorem norm_heckeTateThetaNormOneTerm
    (f : SchwartzMap (MixedSpace K) Complex) (T : FiniteAdeles K -> Complex)
    (a : heckeNormOneIdeles K) (t : Real) (x : K) :
    norm (heckeTateThetaNormOneTerm f T a t x) = heckeTateThetaNormOneAbsTerm f T a t x := by
  by_cases h : x = 0
  . simp only [heckeTateThetaNormOneTerm, heckeTateThetaNormOneAbsTerm, heckeTateThetaAbsTerm,
      if_pos h, norm_zero]
  . simp only [heckeTateThetaNormOneTerm, heckeTateThetaNormOneAbsTerm, heckeTateThetaAbsTerm,
      if_neg h, Complex.norm_mul]

private def principalMulEquiv (u : Units K) : Equiv K K where
  toFun x := u.val * x
  invFun x := u.inv * x
  left_inv x := by
    change u.inv * (u.val * x) = x
    rw [<- mul_assoc, u.inv_val, one_mul]
  right_inv x := by
    change u.val * (u.inv * x) = x
    rw [<- mul_assoc, u.val_inv, one_mul]

/-- Multiplication of the idele by a principal unit reindexes each field term by that unit. -/
theorem heckeTateThetaNormOneTerm_principal_mul
    (f : SchwartzMap (MixedSpace K) Complex) (T : FiniteAdeles K -> Complex)
    (u : Units K) (a : heckeNormOneIdeles K) (t : Real) (x : K) :
    heckeTateThetaNormOneTerm f T (heckePrincipalNormOneIdele K u * a) t x =
      heckeTateThetaNormOneTerm f T a t (u.val * x) := by
  let A := InfiniteAdeleRing K
  let F := FiniteAdeles K
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let b := MulEquiv.prodUnits a.val
  let s := Real.exp (t / (Module.finrank Rat K : Real))
  let e := mixedEmbedding K
  let g := algebraMap K F
  change (if x = 0 then 0 else
      f (HSMul.hSMul s (E (algebraMap K A u.val * b.1.val) * e x)) *
        T ((g u.val * b.2.val) * g x)) =
    (if u.val * x = 0 then 0 else
      f (HSMul.hSMul s (E b.1.val * e (u.val * x))) *
        T (b.2.val * g (u.val * x)))
  by_cases hx : x = 0
  . rw [hx, mul_zero, if_pos rfl, if_pos rfl]
  . have hux : Not (u.val * x = 0) := mul_ne_zero u.ne_zero hx
    rw [if_neg hx, if_neg hux, map_mul E, map_mul e, map_mul g]
    have hArch : E (algebraMap K A u.val) = e u.val :=
      (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := K)).symm
    rw [hArch, mul_comm (e u.val) (E b.1.val), mul_assoc (E b.1.val),
      mul_comm (g u.val) b.2.val, mul_assoc b.2.val]

/-- The Tate theta sum with its zero term removed. -/
noncomputable def heckeTateThetaNormOne
    (f : SchwartzMap (MixedSpace K) Complex) (T : FiniteAdeles K -> Complex)
    (a : heckeNormOneIdeles K) (t : Real) : Complex :=
  tsum (heckeTateThetaNormOneTerm f T a t)

/-- The theta sum is invariant under multiplication of the idele by a principal unit. -/
theorem heckeTateThetaNormOne_principal_mul
    (f : SchwartzMap (MixedSpace K) Complex) (T : FiniteAdeles K -> Complex)
    (u : Units K) (a : heckeNormOneIdeles K) (t : Real) :
    heckeTateThetaNormOne f T (heckePrincipalNormOneIdele K u * a) t =
      heckeTateThetaNormOne f T a t := by
  unfold heckeTateThetaNormOne
  calc
    _ = tsum (fun x : K => heckeTateThetaNormOneTerm f T a t (u.val * x)) :=
      tsum_congr (heckeTateThetaNormOneTerm_principal_mul f T u a t)
    _ = _ := (principalMulEquiv u).tsum_eq (heckeTateThetaNormOneTerm f T a t)

/-- The theta sum on a norm-one idele class at a given logarithmic scale. -/
noncomputable def heckeTateThetaNormOneClass
    (f : SchwartzMap (MixedSpace K) Complex) (T : FiniteAdeles K -> Complex)
    (t : Real) : heckeNormOneIdeleClass K -> Complex := by
  let P := heckePrincipalNormOneIdele K
  refine Quotient.lift (fun a : heckeNormOneIdeles K => heckeTateThetaNormOne f T a t) ?_
  intro a b h
  have hb : Membership.mem P.range (Inv.inv a * b) := (QuotientGroup.leftRel_apply).mp h
  choose u hu using hb
  have hEq : P u * a = b := by
    rw [hu, mul_comm (Inv.inv a * b) a, <- mul_assoc, mul_inv_cancel, one_mul]
  exact (heckeTateThetaNormOne_principal_mul f T u a t).symm.trans
    (congrArg (fun c : heckeNormOneIdeles K => heckeTateThetaNormOne f T c t) hEq)

/-- Evaluation on an idele class agrees with the theta sum on any representative. -/
theorem heckeTateThetaNormOneClass_mk
    (f : SchwartzMap (MixedSpace K) Complex) (T : FiniteAdeles K -> Complex)
    (t : Real) (a : heckeNormOneIdeles K) :
    heckeTateThetaNormOneClass f T t (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range a) =
      heckeTateThetaNormOne f T a t := rfl

/-- The theta sum on the norm-one quotient has a uniform exponential decay bound. -/
theorem exists_uniform_heckeTateThetaNormOneClass_bound
    (f : SchwartzMap (MixedSpace K) Complex)
    (T : FiniteAdeles K -> Complex) (S : Set (FiniteAdeles K)) (hS : IsCompact S)
    (hST : forall z : FiniteAdeles K, Not (Membership.mem S z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z : FiniteAdeles K, norm (T z) <= B)
    (N : Nat) (hN : (Module.finrank Int (NumberField.mixedEmbedding.integerLattice K) : Real) < (N : Real)) :
    Exists (fun D : Real => And (0 <= D)
      (forall (a : heckeNormOneIdeleClass K) (t : Real),
        norm (heckeTateThetaNormOneClass f T t a) <=
          D * Real.exp (-(N : Real) * (t / (Module.finrank Rat K : Real))))) := by
  let q := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
  choose C hC using exists_uniform_heckeTateTheta_bound_on_normOne_representatives
    f T S hS hST B hB hBT N hN
  choose D hD using hC.2.2
  refine Exists.intro D (And.intro hD.1 ?_)
  intro a t
  have ha : Membership.mem (Set.image q C) a := by
    have hCover : Set.image q C = Set.univ := hC.2.1
    rw [hCover]
    exact Set.mem_univ a
  choose r hr hrq using ha
  rw [<- hrq, heckeTateThetaNormOneClass_mk]
  have h := hD.2 r hr t
  have hEq : (fun x => norm (heckeTateThetaNormOneTerm f T r t x)) =
      heckeTateThetaNormOneAbsTerm f T r t := funext (norm_heckeTateThetaNormOneTerm f T r t)
  have hSum : Summable (fun x => norm (heckeTateThetaNormOneTerm f T r t x)) := by
    rw [hEq]
    exact h.1
  unfold heckeTateThetaNormOne
  refine (norm_tsum_le_tsum_norm hSum).trans ?_
  rw [hEq]
  exact h.2

/-- The original finite Hecke test gives a uniform bound on the quotient. -/
theorem exists_uniform_heckeTateThetaNormOneClass_character_bound
    (f : SchwartzMap (MixedSpace K) Complex) (chi : UnitaryHeckeCharacter K)
    (N : Nat) (hN : (Module.finrank Int (NumberField.mixedEmbedding.integerLattice K) : Real) < (N : Real)) :
    Exists (fun D : Real => And (0 <= D)
      (forall (a : heckeNormOneIdeleClass K) (t : Real),
        norm (heckeTateThetaNormOneClass f (heckeFiniteAdditiveTateTest chi) t a) <=
          D * Real.exp (-(N : Real) * (t / (Module.finrank Rat K : Real))))) := by
  refine exists_uniform_heckeTateThetaNormOneClass_bound f _ _ isCompact_integralFiniteAdeles
    ?_ 1 zero_le_one (norm_heckeFiniteAdditiveTateTest_le_one chi) N hN
  intro z hz
  have hz' : Not (Membership.mem (heckeIntegralFiniteAdeles (K := K)) z) := hz
  rw [heckeFiniteAdditiveTateTest, if_neg hz']

/-- The finite Fourier dual of a Hecke test gives a uniform bound on the quotient. -/
theorem exists_uniform_heckeTateThetaNormOneClass_dual_bound
    [MeasurableSpace (FiniteAdeles K)] [BorelSpace (FiniteAdeles K)]
    (mu : Measure (FiniteAdeles K)) [mu.IsAddHaarMeasure]
    (f : SchwartzMap (MixedSpace K) Complex) (chi : UnitaryHeckeCharacter K)
    (N : Nat) (hN : (Module.finrank Int (NumberField.mixedEmbedding.integerLattice K) : Real) < (N : Real)) :
    Exists (fun D : Real => And (0 <= D)
      (forall (a : heckeNormOneIdeleClass K) (t : Real),
        norm (heckeTateThetaNormOneClass f
          (fun y => heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) (-y)) t a) <=
            D * Real.exp (-(N : Real) * (t / (Module.finrank Rat K : Real))))) := by
  choose V hV using exists_compactSupport_heckeFiniteFourierIntegral_TateTest mu chi
  let W := Set.image (fun y : FiniteAdeles K => -y) V
  have hW : IsCompact W := hV.1.image continuous_neg
  have hV' (y : FiniteAdeles K) (hy : Not (Membership.mem W y)) : Not (Membership.mem V (-y)) := by
    intro h
    exact hy (Exists.intro (-y) (And.intro h (neg_neg y)))
  exact exists_uniform_heckeTateThetaNormOneClass_bound f _ W hW
    (fun y hy => hV.2 (-y) (hV' y hy)) _ ENNReal.toReal_nonneg
    (fun y => norm_heckeFiniteFourierIntegral_TateTest_le mu chi (-y)) N hN

end Robin1984.GRH
