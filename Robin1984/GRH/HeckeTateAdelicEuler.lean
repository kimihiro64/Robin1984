import Robin1984.GRH.HeckeTateFiniteEuler
import Robin1984.GRH.HeckeTateInfiniteEuler
import Robin1984.GRH.HeckeTateZetaUnfolding

/-!
# The adelic Tate Euler integral

On the half-plane of absolute convergence, the global Tate test in product
coordinates integrates to the shifted Gamma factors times the Hecke Euler
product.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's global zeta integral and its product of local zeta integrals.
- Formalization note: Evaluates the actual idelic test in the normalized archimedean and finite product coordinates for real part greater than one.
- PROVENANCE-END
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open IsDedekindDomain NumberField MeasureTheory
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev TateEulerMixedSpace (K : Type*) [Field K] := mixedEmbedding.mixedSpace K
private abbrev TateEulerFiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private theorem heckeTateInfiniteWeight_on_idele (chi : UnitaryHeckeCharacter K)
    (s : Complex) (b : Units (InfiniteAdeleRing K)) :
    let x := InfiniteAdeleRing.ringEquiv_mixedSpace K b.val
    heckeTateInfiniteWeight chi s x =
      heckeTateInfiniteTest chi x *
        (chi.val (heckeInfiniteIdeleInclusion K b) : Complex) *
        (mixedEmbedding.norm x : Complex) ^ s := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let x := e b.val
  let u := Units.map e.toMonoidHom b
  have hx : IsUnit x := u.isUnit
  have hChoice : Units.map e.symm.toMonoidHom hx.unit = b := by
    apply Units.ext
    change e.symm hx.unit.val = b.val
    rw [IsUnit.unit_spec, e.symm_apply_apply]
  change heckeTateInfiniteWeight chi s x = _
  rw [heckeTateInfiniteWeight, dif_pos hx, hChoice]

private theorem heckeTateZetaWeight_split_into_components
    (chi : UnitaryHeckeCharacter K) (s : Complex)
    (b : Units (InfiniteAdeleRing K)) (u : Units (TateEulerFiniteAdeles K)) :
    let x := InfiniteAdeleRing.ringEquiv_mixedSpace K b.val
    let a := heckeInfiniteIdeleInclusion K b * heckeFiniteIdeleInclusion u
    heckeTateZetaWeight chi s a *
        (heckeTateInfiniteTest chi x * heckeFiniteAdditiveTateTest chi u.val) =
      heckeTateInfiniteWeight chi s x * heckeFiniteTateDensity chi s u := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let x := e b.val
  let a := heckeInfiniteIdeleInclusion K b * heckeFiniteIdeleInclusion u
  let pI := (RingHom.fst (InfiniteAdeleRing K) (TateEulerFiniteAdeles K)).toMonoidHom
  let pF := (RingHom.snd (InfiniteAdeleRing K) (TateEulerFiniteAdeles K)).toMonoidHom
  have hVal : a.val = Prod.mk b.val u.val := by
    apply Prod.ext
    . exact mul_one b.val
    . exact one_mul u.val
  have hI : Units.map pI a = b := Units.ext (congrArg Prod.fst hVal)
  have hF : Units.map pF a = u := Units.ext (congrArg Prod.snd hVal)
  have hNorm : heckeIdelicNorm a = mixedEmbedding.norm x * heckeFiniteIdeleNorm u := by
    change heckeInfiniteIdeleNorm (Units.map pI a) * heckeFiniteIdeleNorm (Units.map pF a) = _
    rw [hI, hF, mixedEmbedding_norm_infiniteIdele]
  have hP : 0 < mixedEmbedding.norm x := by
    rw [mixedEmbedding_norm_infiniteIdele]
    exact heckeInfiniteIdeleNorm_pos b
  have hQ : 0 < heckeFiniteIdeleNorm u := heckeFiniteIdeleNorm_pos u
  have hPow : (mixedEmbedding.norm x : Complex) ^ s =
      Complex.exp (s * (Real.log (mixedEmbedding.norm x) : Complex)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hP.ne'),
      <- Complex.ofReal_log hP.le, mul_comm]
  change heckeTateZetaWeight chi s a *
    (heckeTateInfiniteTest chi x * heckeFiniteAdditiveTateTest chi u.val) = _
  rw [heckeTateInfiniteWeight_on_idele chi s b, heckeFiniteTateDensity, hPow,
    heckeTateZetaWeight, hNorm, Real.log_mul hP.ne' hQ.ne', Complex.ofReal_add, mul_add,
    Complex.exp_add]
  have hChi : (chi.val a : Complex) =
      (chi.val (heckeInfiniteIdeleInclusion K b) : Complex) *
      (chi.val (heckeFiniteIdeleInclusion u) : Complex) := by
    simp only [a, map_mul, Circle.coe_mul]
  rw [hChi]
  ac_rfl

/-- The actual weighted Tate test expressed in archimedean mixed-space
and finite-idele coordinates. -/
def heckeTateWeightedProductTest (chi : UnitaryHeckeCharacter K) (s : Complex)
    (p : Prod (TateEulerMixedSpace K) (Units (TateEulerFiniteAdeles K))) : Complex :=
  if hx : IsUnit p.1 then
    let b := Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toMonoidHom hx.unit
    let a := heckeInfiniteIdeleInclusion K b * heckeFiniteIdeleInclusion p.2
    heckeTateZetaWeight chi s a *
      (heckeTateInfiniteTest chi p.1 * heckeFiniteAdditiveTateTest chi p.2.val)
  else 0

private theorem heckeTateWeightedProductTest_eq_local_product
    (chi : UnitaryHeckeCharacter K) (s : Complex) (p : Prod (TateEulerMixedSpace K) (Units (TateEulerFiniteAdeles K))) :
    heckeTateWeightedProductTest chi s p =
      heckeTateInfiniteWeight chi s p.1 * heckeFiniteTateDensity chi s p.2 := by
  unfold heckeTateWeightedProductTest
  by_cases hx : IsUnit p.1
  case pos =>
    rw [dif_pos hx]
    let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
    let b := Units.map e.symm.toMonoidHom hx.unit
    have hX : e b.val = p.1 := by
      change e (e.symm hx.unit.val) = p.1
      rw [e.apply_symm_apply, IsUnit.unit_spec]
    have h := heckeTateZetaWeight_split_into_components chi s b p.2
    change heckeTateZetaWeight chi s (heckeInfiniteIdeleInclusion K b * heckeFiniteIdeleInclusion p.2) *
      (heckeTateInfiniteTest chi (e b.val) * heckeFiniteAdditiveTateTest chi p.2.val) =
      heckeTateInfiniteWeight chi s (e b.val) * heckeFiniteTateDensity chi s p.2 at h
    rwa [hX] at h
  case neg =>
    rw [dif_neg hx, heckeTateInfiniteWeight, dif_neg hx, zero_mul]

/-- Under normalized finite Haar measure, the Tate test integrates to
the standard archimedean factor times the Hecke Euler product. -/
theorem integral_heckeTateWeightedProductTest
    [MeasurableSpace (TateEulerFiniteAdeles K)] [BorelSpace (TateEulerFiniteAdeles K)]
    [MeasurableSpace (Units (TateEulerFiniteAdeles K))] [BorelSpace (Units (TateEulerFiniteAdeles K))]
    [MeasurableSpace (Units (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))]
    [MeasurableSingletonClass (Units (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))]
    (mu : Measure (Units (TateEulerFiniteAdeles K))) [SFinite mu] [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (Units (TateEulerFiniteAdeles K))) = 1)
    (chi : UnitaryHeckeCharacter K) {s : Complex} (hs : 1 < s.re) :
    let nu := (DedekindZeta.GammaIntegral.mulHaar K).prod mu
    And (Integrable (heckeTateWeightedProductTest chi s) nu)
      (integral nu (heckeTateWeightedProductTest chi s) =
        ((Finset.univ.prod (fun v : {w : InfinitePlace K // w.IsReal} =>
          DedekindZeta.LReal (s + realInfiniteHeckeShift chi v.property))) *
        (Finset.univ.prod (fun v : {w : InfinitePlace K // w.IsComplex} =>
          DedekindZeta.LComplex (s + complexInfiniteHeckeShift chi v.property)))) *
        heckeEulerL K chi s) := by
  let _ : SFinite (DedekindZeta.GammaIntegral.mulHaar K) :=
    sFinite_of_absolutelyContinuous (withDensity_absolutelyContinuous volume _)
  have hA := integral_heckeTateInfiniteWeight chi (zero_lt_one.trans hs)
  have hF := integral_heckeFiniteTateDensity_eq_heckeEulerL mu hUnit chi hs
  have hEq := funext (heckeTateWeightedProductTest_eq_local_product chi s)
  dsimp only
  rw [hEq]
  refine And.intro (hA.1.mul_prod hF.1) ?_
  rw [integral_prod_mul, hA.2, hF.2]


end Robin1984.GRH
