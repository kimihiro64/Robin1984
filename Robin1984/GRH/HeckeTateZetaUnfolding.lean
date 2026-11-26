import Mathlib.MeasureTheory.Group.Measure
import Robin1984.GRH.HeckeTateMellin
import Robin1984.GRH.HeckeTateQuotientIntegration

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's unfolding of an idelic zeta integral into a principal-idele theta sum.
- Formalization note: Identifies the weighted physical orbit sum with the theta series and unfolds the integral in the logarithmic norm coordinates.
- PROVENANCE-END
-/

/-!
# Unfolding the Tate zeta integral

The archimedean and finite additive tests evaluate the nonzero principal theta
terms. The full unitary character splits into its logarithmic-norm factor and
a norm-one class character. Under integrability, the zeta integral equals the
corresponding weighted theta integral on the actual idele class quotient.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev PhysicalFiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev PhysicalIdeles (K : Type*) [Field K] [NumberField K] :=
  Units (AdeleRing (RingOfIntegers K) K)

/-- The product of the archimedean and finite additive test functions on an idele. -/
noncomputable def heckeTateAdditiveIdelicTest
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : PhysicalFiniteAdeles K -> Complex) (a : PhysicalIdeles K) : Complex :=
  f (InfiniteAdeleRing.ringEquiv_mixedSpace K a.val.1) * T a.val.2

/-- A test value in logarithmic norm coordinates is the principal theta term at one. -/
theorem heckeTateAdditiveIdelicTest_expSection_mul
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : PhysicalFiniteAdeles K -> Complex) (a : heckeNormOneIdeles K) (t : Real) :
    heckeTateAdditiveIdelicTest f T (heckeIdelicExpSection K t * a.val) =
      heckeTateThetaNormOneTerm f T a t 1 := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let c := Real.exp (t / (Module.finrank Rat K : Real))
  have hScale : (heckeIdelicExpSection K t).val =
      Prod.mk (E.symm (algebraMap Real (mixedEmbedding.mixedSpace K) c))
        (1 : PhysicalFiniteAdeles K) := rfl
  unfold heckeTateAdditiveIdelicTest
  rw [Units.val_mul, hScale]
  simp only [heckeTateThetaNormOneTerm, if_neg one_ne_zero, map_one, mul_one]
  change f (E (E.symm (algebraMap Real (mixedEmbedding.mixedSpace K) c) * a.val.val.1)) *
    T (1 * a.val.val.2) = f (HSMul.hSMul c (E a.val.val.1)) * T a.val.val.2
  rw [map_mul, E.apply_symm_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul, one_mul]

/-- Principal multiplication in the full ideles evaluates the matching theta term. -/
theorem heckeTateAdditiveIdelicTest_expSection_principal_mul
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : PhysicalFiniteAdeles K -> Complex) (a : heckeNormOneIdeles K) (t : Real)
    (u : Units K) :
    heckeTateAdditiveIdelicTest f T
      ((heckeIdelicExpSection K t * a.val) * heckeFullPrincipalIdele K u) =
      heckeTateThetaNormOneTerm f T a t u.val := by
  have hEq : (heckeIdelicExpSection K t * a.val) * heckeFullPrincipalIdele K u =
      heckeIdelicExpSection K t * (heckePrincipalNormOneIdele K u * a).val := by
    change (heckeIdelicExpSection K t * a.val) * heckeFullPrincipalIdele K u =
      heckeIdelicExpSection K t * (heckeFullPrincipalIdele K u * a.val)
    ac_rfl
  rw [hEq, heckeTateAdditiveIdelicTest_expSection_mul,
    heckeTateThetaNormOneTerm_principal_mul, mul_one]

/-- The diagonal embedding of the field units into the full ideles is injective. -/
theorem heckeFullPrincipalIdele_injective :
    Function.Injective (heckeFullPrincipalIdele K) := by
  intro u v h
  have hv := congrArg (fun a : PhysicalIdeles K => a.val.1) h
  change algebraMap K (InfiniteAdeleRing K) u.val =
    algebraMap K (InfiniteAdeleRing K) v.val at hv
  exact Units.ext ((algebraMap K (InfiniteAdeleRing K)).injective hv)

private noncomputable def tateOppositePrincipalIdelesEquiv :
    Equiv (Units K) (heckeFullPrincipalIdele K).range.op := by
  let toRange : Units K -> (heckeFullPrincipalIdele K).range.op :=
    fun u => Subtype.mk (MulOpposite.op (heckeFullPrincipalIdele K u)) (Exists.intro u rfl)
  refine Equiv.ofBijective toRange ?_
  constructor
  case left =>
    intro a b h
    exact heckeFullPrincipalIdele_injective (MulOpposite.op_injective (congrArg Subtype.val h))
  case right =>
    intro g
    let u := Classical.choose g.property
    have hu := Classical.choose_spec g.property
    refine Exists.intro u (Subtype.ext ?_)
    exact MulOpposite.unop_injective hu

private def tateNonzeroFieldEquiv : Equiv (Units K) {x : K // Not (x = 0)} where
  toFun u := Subtype.mk u.val u.ne_zero
  invFun x := Units.mk0 x.val x.property
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The principal-idele orbit sum of a Tate test is its theta sum on the field. -/
theorem heckeTate_automorphize_eq_weight_mul_theta
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : PhysicalFiniteAdeles K -> Complex) (W : PhysicalIdeles K -> Complex)
    (hW : forall (a : PhysicalIdeles K) (u : Units K),
      W (a * heckeFullPrincipalIdele K u) = W a)
    (a : heckeNormOneIdeles K) (t : Real) :
    QuotientGroup.automorphize (fun b => W b * heckeTateAdditiveIdelicTest f T b)
        (QuotientGroup.mk' (heckeFullPrincipalIdele K).range (heckeIdelicExpSection K t * a.val)) =
      W (heckeIdelicExpSection K t * a.val) * heckeTateThetaNormOne f T a t := by
  let b : PhysicalIdeles K := heckeIdelicExpSection K t * a.val
  let E := tateOppositePrincipalIdelesEquiv (K := K)
  let G := tateNonzeroFieldEquiv (K := K)
  let term := heckeTateThetaNormOneTerm f T a t
  let summand : (heckeFullPrincipalIdele K).range.op -> Complex := fun g =>
    W (b * MulOpposite.unop g.val) * heckeTateAdditiveIdelicTest f T (b * MulOpposite.unop g.val)
  change tsum summand = W b * tsum term
  rw [<- E.tsum_eq summand]
  have hterm : forall u : Units K, summand (E u) = W b * term (G u).val := by
    intro u
    change W (b * heckeFullPrincipalIdele K u) *
      heckeTateAdditiveIdelicTest f T (b * heckeFullPrincipalIdele K u) = W b * term u.val
    rw [hW, heckeTateAdditiveIdelicTest_expSection_principal_mul]
  simp only [hterm, tsum_mul_left]
  congr 1
  rw [G.tsum_eq (fun u => term u.val)]
  let s : Set K := {x : K | Not (x = 0)}
  change tsum (fun x : s => term x.val) = tsum term
  rw [tsum_subtype]
  refine tsum_congr ?_
  intro x
  by_cases hx : x = 0
  case pos => simp [hx, term, heckeTateThetaNormOneTerm]
  case neg => simp [s, hx, term]

open MeasureTheory

/-- The unitary character and complex norm power in the Tate zeta integral. -/
noncomputable def heckeTateZetaWeight (chi : UnitaryHeckeCharacter K) (s : Complex)
    (b : PhysicalIdeles K) : Complex :=
  Complex.exp (s * (Real.log (heckeIdelicNorm b) : Complex)) * (chi.val b : Complex)

theorem heckeTateZetaWeight_principal_mul (chi : UnitaryHeckeCharacter K) (s : Complex)
    (b : PhysicalIdeles K) (u : Units K) :
    heckeTateZetaWeight chi s (b * heckeFullPrincipalIdele K u) =
      heckeTateZetaWeight chi s b := by
  have hn : heckeIdelicNorm (heckeFullPrincipalIdele K u) = 1 :=
    (mem_heckeNormOneIdeles K _).mp (heckePrincipalNormOneIdele K u).property
  have hc : chi.val (heckeFullPrincipalIdele K u) = 1 := chi.property u
  unfold heckeTateZetaWeight
  rw [map_mul heckeIdelicNorm, hn, mul_one, map_mul, hc, mul_one]

/-- The weighted Tate theta integral in logarithmic norm coordinates. -/
noncomputable def heckeTateClassZetaIntegrand (chi : UnitaryHeckeCharacter K) (s : Complex)
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : PhysicalFiniteAdeles K -> Complex) (p : Prod Real (heckeNormOneIdeleClass K)) : Complex :=
  (Complex.exp (s * (p.1 : Complex)) * (chi.val (heckeIdelicExpSection K p.1) : Complex) *
    (heckeNormOneClassCharacter chi p.2 : Complex)) *
  heckeTateThetaNormOneClass f T p.1 p.2

private theorem tateWeightedClassIntegrand_mk (chi : UnitaryHeckeCharacter K) (s : Complex)
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : PhysicalFiniteAdeles K -> Complex) (a : heckeNormOneIdeles K) (t : Real) :
    heckeTateClassZetaIntegrand chi s f T
        (Prod.mk t (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range a)) =
      heckeTateZetaWeight chi s (heckeIdelicExpSection K t * a.val) *
        heckeTateThetaNormOne f T a t := by
  unfold heckeTateClassZetaIntegrand heckeTateZetaWeight
  rw [heckeNormOneClassCharacter_mk, heckeTateThetaNormOneClass_mk, map_mul heckeIdelicNorm,
    heckeIdelicNorm_expSection, (mem_heckeNormOneIdeles K _).mp a.property, mul_one, Real.log_exp,
    map_mul, Circle.coe_mul]
  ac_rfl

/-- The original idelic integrand descends to the weighted norm-one theta sum. -/
theorem heckeTateZeta_automorphize_eq_classIntegrand
    (chi : UnitaryHeckeCharacter K) (s : Complex)
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : PhysicalFiniteAdeles K -> Complex) (q : heckeIdeleClass K) :
    QuotientGroup.automorphize
      (fun b => heckeTateZetaWeight chi s b * heckeTateAdditiveIdelicTest f T b) q =
      heckeTateClassZetaIntegrand chi s f T (heckeIdeleClassLogNormHomeomorph K q) := by
  refine Quotient.inductionOn q ?_
  intro b
  let e := heckeIdelicLogNormHomeomorph K
  let p := e b
  have hb : heckeIdelicExpSection K p.1 * p.2.val = b := e.symm_apply_apply b
  change QuotientGroup.automorphize
      (fun b => heckeTateZetaWeight chi s b * heckeTateAdditiveIdelicTest f T b)
      (QuotientGroup.mk b) = _
  rw [heckeIdeleClassLogNormHomeomorph_mk]
  change QuotientGroup.automorphize
      (fun b => heckeTateZetaWeight chi s b * heckeTateAdditiveIdelicTest f T b)
      (QuotientGroup.mk b) = heckeTateClassZetaIntegrand chi s f T
      (Prod.mk p.1 (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range p.2))
  rw [<- hb]
  change QuotientGroup.automorphize
    (fun b => heckeTateZetaWeight chi s b * heckeTateAdditiveIdelicTest f T b)
    (QuotientGroup.mk' (heckeFullPrincipalIdele K).range (heckeIdelicExpSection K p.1 * p.2.val)) = _
  rw [heckeTate_automorphize_eq_weight_mul_theta f T _
    (heckeTateZetaWeight_principal_mul chi s), tateWeightedClassIntegrand_mk]

theorem continuous_heckeTateClassZetaIntegrand (chi : UnitaryHeckeCharacter K) (s : Complex)
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : PhysicalFiniteAdeles K -> Complex) (hT : Continuous T)
    (U : Set (PhysicalFiniteAdeles K)) (hU : IsCompact U)
    (hUT : forall z : PhysicalFiniteAdeles K, Not (Membership.mem U z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z : PhysicalFiniteAdeles K, norm (T z) <= B) :
    Continuous (heckeTateClassZetaIntegrand chi s f T) := by
  have hExp : Continuous (fun p : Prod Real (heckeNormOneIdeleClass K) =>
      Complex.exp (s * (p.1 : Complex))) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))
  have hRadial : Continuous (fun p : Prod Real (heckeNormOneIdeleClass K) =>
      (chi.val (heckeIdelicExpSection K p.1) : Complex)) :=
    continuous_subtype_val.comp
      (chi.val.continuous.comp ((continuous_heckeIdelicExpSection K).comp continuous_fst))
  have hChar : Continuous (fun p : Prod Real (heckeNormOneIdeleClass K) =>
      (heckeNormOneClassCharacter chi p.2 : Complex)) :=
    continuous_subtype_val.comp ((heckeNormOneClassCharacter chi).continuous.comp continuous_snd)
  exact ((hExp.mul hRadial).mul hChar).mul
    (continuous_heckeTateThetaNormOneClass_joint f T hT U hU hUT B hB hBT)

/-- Unfold the weighted Tate zeta integral to the actual norm-one class theta integral. -/
theorem integral_heckeTateZeta_eq_classTheta
    [MeasurableSpace (PhysicalIdeles K)] [BorelSpace (PhysicalIdeles K)]
    [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]
    [MeasurableSpace (heckeIdeleClass K)] [BorelSpace (heckeIdeleClass K)]
    [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeles K)) [SFinite mu] [mu.IsMulRightInvariant]
    {S : Set (heckeNormOneIdeles K)} (hS : MeasurableSet S)
    (hInj : Set.InjOn (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S)
    (hSur : Set.image (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S = Set.univ)
    (chi : UnitaryHeckeCharacter K) (s : Complex)
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : PhysicalFiniteAdeles K -> Complex) (hT : Continuous T)
    (U : Set (PhysicalFiniteAdeles K)) (hU : IsCompact U)
    (hUT : forall z : PhysicalFiniteAdeles K, Not (Membership.mem U z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z : PhysicalFiniteAdeles K, norm (T z) <= B)
    (hInt : Integrable (fun b => heckeTateZetaWeight chi s b * heckeTateAdditiveIdelicTest f T b)
      (heckeIdelicLogNormMeasure K mu)) :
    integral (heckeIdelicLogNormMeasure K mu)
      (fun b => heckeTateZetaWeight chi s b * heckeTateAdditiveIdelicTest f T b) =
      integral (volume.prod (heckeNormOneClassQuotientMeasure K mu S))
        (heckeTateClassZetaIntegrand chi s f T) := by
  have hEq := funext (heckeTateZeta_automorphize_eq_classIntegrand chi s f T)
  have hCont := continuous_heckeTateClassZetaIntegrand chi s f T hT U hU hUT B hB hBT
  have hAuto : AEStronglyMeasurable (QuotientGroup.automorphize
      (fun b => heckeTateZetaWeight chi s b * heckeTateAdditiveIdelicTest f T b))
      (heckeFullTateQuotientMeasure K mu S) := by
    rw [hEq]
    exact (hCont.comp (heckeIdeleClassLogNormHomeomorph K).continuous).aestronglyMeasurable
  rw [integral_heckeIdelicLogNormMeasure_eq_integral_automorphize K mu hS hInj hSur _ hInt hAuto]
  congr 1
  funext p
  rw [heckeTateZeta_automorphize_eq_classIntegrand, Homeomorph.apply_symm_apply]

end Robin1984.GRH
