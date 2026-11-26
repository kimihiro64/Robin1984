import Robin1984.GRH.HeckeTateAdelicEuler

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's adelic Poisson summation on the idele class group.
- Formalization note: Transports the mixed Schwartz and finite Fourier tests to logarithmic norm coordinates and retains both values at zero.
- PROVENANCE-END
-/

/-!
# Tate Poisson summation in idele class coordinates

This module identifies the two normalized Fourier tests and states the theta
identity at logarithmic norms `t` and `-t`, including the terms at zero.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open IsDedekindDomain NumberField MeasureTheory FourierTransform
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev Mix (K : Type*) [Field K] := mixedEmbedding.mixedSpace K
private abbrev FinAd (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private def heckeMinkowskiTest (f : SchwartzMap (Mix K) Complex) :
    SchwartzMap (DedekindZeta.Theta.minkowskiSpace K) Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (DedekindZeta.Theta.toMinkowski K).symm f

/-- The archimedean Fourier test in mixed trace coordinates. -/
def heckeTateDualInfiniteTest (f : SchwartzMap (Mix K) Complex) :
    SchwartzMap (Mix K) Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    ((DedekindZeta.Theta.toMinkowski K).trans (DedekindZeta.Theta.conjMink K))
    (fourier (heckeMinkowskiTest f))

theorem heckeTateDualInfiniteTest_apply (f : SchwartzMap (Mix K) Complex) (z : Mix K) :
    heckeTateDualInfiniteTest f z =
      fourier (heckeMinkowskiTest f : DedekindZeta.Theta.minkowskiSpace K -> Complex)
        (DedekindZeta.Theta.toMinkowski K (DedekindZeta.Theta.conjMixed K z)) := by
  rw [heckeTateDualInfiniteTest, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  simp only [Function.comp_apply, ContinuousLinearEquiv.trans_apply,
    DedekindZeta.Theta.conjMink_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

variable [MeasurableSpace (FinAd K)] [BorelSpace (FinAd K)]

/-- The finite Fourier test with the discriminant normalization carried by
the finite Haar measure and the sign used in the trace pairing. -/
def heckeTateDualFiniteTest (chi : UnitaryHeckeCharacter K) (z : FinAd K) : Complex :=
  Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
    heckeFiniteFourierIntegral heckeFiniteAdeleHaar (heckeFiniteAdditiveTateTest chi) (-z)

/-- Adelic Poisson summation expressed directly in terms of the mixed
Schwartz test and its two normalized dual test functions. -/
theorem tsum_heckeTateTest_eq_dual
    (chi : UnitaryHeckeCharacter K) (a : Units (InfiniteAdeleRing K)) (b : Units (FinAd K))
    (f : SchwartzMap (Mix K) Complex) :
    tsum (fun x : K => f (InfiniteAdeleRing.ringEquiv_mixedSpace K a.val * mixedEmbedding K x) *
      heckeFiniteAdditiveTateTest chi (algebraMap K (FinAd K) x * b.val)) =
      ((Inv.inv (heckeInfiniteIdeleNorm a) : Real) : Complex) *
      ((heckeFiniteIdeleNorm (Inv.inv b) : Real) : Complex) *
        tsum (fun x : K =>
          heckeTateDualInfiniteTest f (InfiniteAdeleRing.ringEquiv_mixedSpace K a.inv *
            mixedEmbedding K x) *
          heckeTateDualFiniteTest chi (algebraMap K (FinAd K) x * b.inv)) := by
  have h := tsum_heckeTateTest_ideleDilation_eq_fourier chi a b (heckeMinkowskiTest f)
  have hLeft (x : K) :
      heckeMinkowskiTest f (heckeInfiniteIdeleDilation a (DedekindZeta.Theta.eEmb K x)) =
        f (InfiniteAdeleRing.ringEquiv_mixedSpace K a.val * mixedEmbedding K x) := by
    rw [heckeMinkowskiTest, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, heckeInfiniteIdeleDilation_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    let E := DedekindZeta.Theta.toMinkowski K
    change f (InfiniteAdeleRing.ringEquiv_mixedSpace K a.val * E.symm (E (mixedEmbedding K x))) = _
    rw [E.symm_apply_apply]
  simp only [hLeft] at h
  rw [h, <- tsum_mul_left]
  apply tsum_congr
  intro x
  rw [heckeTateDualInfiniteTest_apply, heckeTateDualFiniteTest, map_neg, neg_mul]
  ring

private abbrev Ideles (K : Type*) [Field K] [NumberField K] := Units (AdeleRing (RingOfIntegers K) K)

/-- The full principal theta summand, including the value at zero. -/
def heckeTateFullThetaTerm
    (f : SchwartzMap (Mix K) Complex) (T : FinAd K -> Complex)
    (a : Ideles K) (x : K) : Complex :=
  f (InfiniteAdeleRing.ringEquiv_mixedSpace K a.val.1 * mixedEmbedding K x) *
    T (algebraMap K (FinAd K) x * a.val.2)

omit [MeasurableSpace (FinAd K)] [BorelSpace (FinAd K)] in
private theorem heckeTateFullThetaTerm_expSection
    (f : SchwartzMap (Mix K) Complex) (T : FinAd K -> Complex)
    (a : heckeNormOneIdeles K) (t : Real) (x : K) :
    heckeTateFullThetaTerm f T (heckeIdelicExpSection K t * a.val) x =
      f (HSMul.hSMul (Real.exp (t / (Module.finrank Rat K : Real)))
        (InfiniteAdeleRing.ringEquiv_mixedSpace K a.val.val.1 * mixedEmbedding K x)) *
      T (a.val.val.2 * algebraMap K (FinAd K) x) := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let c := Real.exp (t / (Module.finrank Rat K : Real))
  have hScale : (heckeIdelicExpSection K t).val =
      Prod.mk (E.symm (algebraMap Real (Mix K) c)) (1 : FinAd K) := rfl
  unfold heckeTateFullThetaTerm
  rw [Units.val_mul, hScale]
  change f (E (E.symm (algebraMap Real (Mix K) c) * a.val.val.1) * mixedEmbedding K x) *
    T (algebraMap K (FinAd K) x * (1 * a.val.val.2)) = _
  rw [E.map_mul, E.apply_symm_apply, Algebra.algebraMap_eq_smul_one]
  simp only [smul_mul_assoc, one_mul, mul_comm (algebraMap K (FinAd K) x)]
  rfl

omit [MeasurableSpace (FinAd K)] [BorelSpace (FinAd K)] in
/-- The principal Poisson sum differs from the norm-one theta sum by exactly
the term at zero, including at negative logarithmic scale. -/
theorem tsum_heckeTateFullThetaTerm_eq
    (f : SchwartzMap (Mix K) Complex) (T : FinAd K -> Complex)
    (S : Set (FinAd K)) (hS : IsCompact S)
    (hST : forall z, Not (Membership.mem S z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z, norm (T z) <= B)
    (a : heckeNormOneIdeles K) (t : Real) :
    tsum (heckeTateFullThetaTerm f T (heckeIdelicExpSection K t * a.val)) =
      heckeTateThetaNormOne f T a t + f 0 * T 0 := by
  let E : Homeomorph (Ideles K) (Prod (Units (InfiniteAdeleRing K)) (Units (FinAd K))) :=
    Homeomorph.prodUnits
  let b := E a.val
  let c := Real.exp (t / (Module.finrank Rat K : Real))
  let N := Module.finrank Int (mixedEmbedding.integerLattice K) + 1
  have hN : (Module.finrank Int (mixedEmbedding.integerLattice K) : Real) < (N : Real) := by
    exact_mod_cast Nat.lt_succ_self _
  choose M hM using exists_summable_heckeTateTheta_majorant
    (Set.singleton b.1) isCompact_singleton (Set.singleton b.2) isCompact_singleton
    f T S hS hST B hB hBT N hN
  have hSum : Summable (heckeTateThetaNormOneTerm f T a t) := by
    apply Summable.of_norm_bounded (hM.1.mul_right (Inv.inv (c ^ N)))
    intro x
    rw [norm_heckeTateThetaNormOneTerm]
    exact hM.2.2 b.1 (Set.mem_singleton _) b.2 (Set.mem_singleton _) c (Real.exp_pos _) x
  let Z (x : K) : Complex := if x = 0 then f 0 * T 0 else 0
  have hZ : HasSum Z (f 0 * T 0) := by
    have h := hasSum_single (f := Z) 0 (fun x hx => if_neg hx)
    simpa only [Z, if_pos rfl] using h
  have hTerms : heckeTateFullThetaTerm f T (heckeIdelicExpSection K t * a.val) =
      fun x => heckeTateThetaNormOneTerm f T a t x + Z x := by
    funext x
    rw [heckeTateFullThetaTerm_expSection]
    by_cases hx : x = 0
    . subst x
      simp [heckeTateThetaNormOneTerm, Z]
    . simp only [heckeTateThetaNormOneTerm, if_neg hx, Z, add_zero]
      rfl
  rw [hTerms, hSum.tsum_add hZ.summable, hZ.tsum_eq, heckeTateThetaNormOne]

/-- The discriminant-normalized finite Fourier test has a uniform bound
and compact support. -/
theorem heckeTateDualFiniteTest_support_and_bound (chi : UnitaryHeckeCharacter K) :
    exists V : Set (FinAd K), exists B : Real,
      And (IsCompact V) (And (0 <= B)
        (And (forall y, Not (Membership.mem V y) -> heckeTateDualFiniteTest chi y = 0)
          (forall y, norm (heckeTateDualFiniteTest chi y) <= B))) := by
  let D : Complex := Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex)
  let B := norm D * heckeFiniteAdeleHaar.real (heckeIntegralFiniteAdeles (K := K) : Set (FinAd K))
  let _ : LocallyCompactSpace (FinAd K) := locallyCompactSpace_heckeFiniteAdeles
  let : (heckeFiniteAdeleHaar (K := K)).IsAddHaarMeasure := by
    unfold heckeFiniteAdeleHaar
    infer_instance
  choose S hS using exists_compactSupport_heckeFiniteFourierIntegral_TateTest heckeFiniteAdeleHaar chi
  let V := Set.image (fun y : FinAd K => -y) S
  refine Exists.intro V (Exists.intro B
    (And.intro (hS.1.image continuous_neg) (And.intro (mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg) ?_)))
  constructor
  . intro y hy
    have hNot : Not (Membership.mem S (-y)) := by
      intro h
      exact hy (Exists.intro (-y) (And.intro h (neg_neg y)))
    rw [heckeTateDualFiniteTest, hS.2 (-y) hNot, mul_zero]
  . intro y
    rw [heckeTateDualFiniteTest, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_heckeFiniteFourierIntegral_TateTest_le heckeFiniteAdeleHaar chi (-y)) (norm_nonneg _)

private theorem tsum_heckeTateFullThetaTerm_eq_dual
    (chi : UnitaryHeckeCharacter K) (f : SchwartzMap (Mix K) Complex) (a : Ideles K) :
    tsum (heckeTateFullThetaTerm f (heckeFiniteAdditiveTateTest chi) a) =
      ((Inv.inv (heckeIdelicNorm a) : Real) : Complex) *
        tsum (heckeTateFullThetaTerm (heckeTateDualInfiniteTest f) (heckeTateDualFiniteTest chi) (Inv.inv a)) := by
  let e : Homeomorph (Ideles K) (Prod (Units (InfiniteAdeleRing K)) (Units (FinAd K))) :=
    Homeomorph.prodUnits
  let b := e a
  have h := tsum_heckeTateTest_eq_dual chi b.1 b.2 f
  have hScalar : ((Inv.inv (heckeInfiniteIdeleNorm b.1) : Real) : Complex) *
      ((heckeFiniteIdeleNorm (Inv.inv b.2) : Real) : Complex) =
        ((Inv.inv (heckeIdelicNorm a) : Real) : Complex) := by
    rw [<- Complex.ofReal_mul]
    congr 1
    change Inv.inv (heckeInfiniteIdeleNorm b.1) * heckeFiniteIdeleNorm (Inv.inv b.2) =
      Inv.inv (heckeInfiniteIdeleNorm b.1 * heckeFiniteIdeleNorm b.2)
    rw [map_inv]
    have hI := (heckeInfiniteIdeleNorm_pos b.1).ne'
    have hF := (heckeFiniteIdeleNorm_pos b.2).ne'
    field_simp
  rw [hScalar] at h
  exact h

/-- The Tate theta Poisson identity on the norm-one idele class group, with
the two terms at zero retained explicitly. -/
theorem heckeTateThetaNormOneClass_poisson
    (chi : UnitaryHeckeCharacter K) (f : SchwartzMap (Mix K) Complex)
    (t : Real) (z : heckeNormOneIdeleClass K) :
    heckeTateThetaNormOneClass f (heckeFiniteAdditiveTateTest chi) t z +
        f 0 * heckeFiniteAdditiveTateTest chi 0 =
      (Real.exp (-t) : Complex) *
        (heckeTateThetaNormOneClass (heckeTateDualInfiniteTest f) (heckeTateDualFiniteTest chi)
          (-t) (Inv.inv z) + heckeTateDualInfiniteTest f 0 * heckeTateDualFiniteTest chi 0) := by
  let q := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
  choose a ha using QuotientGroup.mk'_surjective (heckePrincipalNormOneIdele K).range z
  have ha' : q a = z := ha
  have hInv : q (Inv.inv a) = Inv.inv z := by
    change (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) (Inv.inv a) = Inv.inv z
    rw [map_inv, ha]
  rw [<- hInv, <- ha', heckeTateThetaNormOneClass_mk, heckeTateThetaNormOneClass_mk]
  let A := heckeIdelicExpSection K t * a.val
  have hNorm : heckeIdelicNorm A = Real.exp t := by
    change heckeIdelicNorm (heckeIdelicExpSection K t * a.val) = _
    rw [map_mul, heckeIdelicNorm_expSection,
      (mem_heckeNormOneIdeles K a.val).mp a.property, mul_one]
  have hNeg : Inv.inv A = heckeIdelicExpSection K (-t) * (Inv.inv a).val := by
    change Inv.inv (heckeIdelicExpSection K t * a.val) = _
    rw [mul_inv_rev, heckeIdelicExpSection_neg]
    exact mul_comm _ _
  have hMain := tsum_heckeTateFullThetaTerm_eq_dual chi f A
  rw [hNorm, <- Real.exp_neg, hNeg] at hMain
  have hPrim : tsum (heckeTateFullThetaTerm f (heckeFiniteAdditiveTateTest chi) A) =
      heckeTateThetaNormOne f (heckeFiniteAdditiveTateTest chi) a t +
        f 0 * heckeFiniteAdditiveTateTest chi 0 :=
    tsum_heckeTateFullThetaTerm_eq f (heckeFiniteAdditiveTateTest chi)
      (heckeIntegralFiniteAdeles (K := K)) isCompact_integralFiniteAdeles
      (fun y hy => by
        have hy' : Not (Membership.mem (heckeIntegralFiniteAdeles (K := K)) y) := hy
        rw [heckeFiniteAdditiveTateTest, if_neg hy']) 1 zero_le_one
      (norm_heckeFiniteAdditiveTateTest_le_one chi) a t
  choose V B hVB using heckeTateDualFiniteTest_support_and_bound chi
  have hDual := tsum_heckeTateFullThetaTerm_eq
    (heckeTateDualInfiniteTest f) (heckeTateDualFiniteTest chi) V hVB.1
    hVB.2.2.1 B hVB.2.1 hVB.2.2.2 (Inv.inv a) (-t)
  rw [hPrim, hDual] at hMain
  exact hMain


end Robin1984.GRH
