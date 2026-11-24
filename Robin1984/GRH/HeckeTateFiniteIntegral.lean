import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Dirac
import Robin1984.GRH.HeckeFiniteIdealClass
import Robin1984.GRH.HeckeFiniteTateTest

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's finite local tests and multiplicative Haar measure on integral-unit cosets.
- Formalization note: Under absolute convergence, the actual finite Tate density integrates as a sum over the nonzero fractional ideals.
- PROVENANCE-END
-/

/-!
# The finite Tate integral as a fractional-ideal sum

The weighted finite density is constant on the integral-unit cosets.
The quotient identifies those cosets with the nonzero fractional
ideals, and normalized Haar measure pushes forward to counting measure.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory Set
open scoped nonZeroDivisors Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev FiniteZetaIdeles (K : Type*) [Field K] [NumberField K] :=
  Units (FiniteAdeleRing (RingOfIntegers K) K)

private abbrev FiniteZetaIdeals (K : Type*) [Field K] [NumberField K] :=
  Units (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)

def heckeFiniteIdealFiber (I : FiniteZetaIdeals K) : Set (FiniteZetaIdeles K) :=
  Set.preimage (heckeFiniteIdeleIdealHom (K := K)) {I}

theorem heckeFiniteIdealFiber_preimage_mul (I : FiniteZetaIdeals K)
    (b : FiniteZetaIdeles K) (hb : heckeFiniteIdeleIdealHom b = I) :
    Set.preimage (fun x => b * x) (heckeFiniteIdealFiber I) =
      (heckeIntegralFiniteUnitGroup (K := K) : Set (FiniteZetaIdeles K)) := by
  ext x
  change heckeFiniteIdeleIdealHom (b * x) = I <->
    Membership.mem heckeIntegralFiniteUnitGroup x
  rw [map_mul, hb, mul_eq_left, heckeFiniteIdeleIdealHom_eq_one_iff]

theorem measurableSet_heckeFiniteIdealFiber
    [MeasurableSpace (FiniteZetaIdeles K)] [BorelSpace (FiniteZetaIdeles K)]
    (I : FiniteZetaIdeals K) :
    MeasurableSet (heckeFiniteIdealFiber I) := by
  let b := Classical.choose (surjective_heckeFiniteIdeleIdealHom (K := K) I)
  have hb := Classical.choose_spec (surjective_heckeFiniteIdeleIdealHom (K := K) I)
  have hEq : heckeFiniteIdealFiber I =
      Set.preimage (fun x => Inv.inv b * x)
        (heckeIntegralFiniteUnitGroup (K := K) : Set (FiniteZetaIdeles K)) := by
    rw [<- heckeFiniteIdealFiber_preimage_mul I b hb, Set.preimage_preimage]
    have hId : (fun x : FiniteZetaIdeles K => b * (Inv.inv b * x)) = id := by
      funext x
      rw [<- mul_assoc, mul_inv_cancel, one_mul, id]
    rw [hId, Set.preimage_id]
  have hOpen : IsOpen (heckeIntegralFiniteUnitGroup (K := K) : Set (FiniteZetaIdeles K)) := by
    let A : Set (FiniteAdeleRing (RingOfIntegers K) K) := heckeIntegralFiniteAdeles (K := K)
    have hA : IsOpen A := isOpen_heckeIntegralFiniteAdeles (K := K)
    have hv : Continuous (fun x : FiniteZetaIdeles K => x.val) := Units.continuous_val
    have hi : Continuous (fun x : FiniteZetaIdeles K => (Inv.inv x).val) :=
      hv.comp continuous_inv
    have hG : (heckeIntegralFiniteUnitGroup (K := K) : Set (FiniteZetaIdeles K)) =
        (Set.preimage (fun x : FiniteZetaIdeles K => x.val) A).inter
        (Set.preimage (fun x : FiniteZetaIdeles K => (Inv.inv x).val) A) := by
      ext x
      exact mem_heckeIntegralFiniteUnitGroup x
    rw [hG]
    exact (hA.preimage hv).inter (hA.preimage hi)
  rw [hEq]
  exact hOpen.measurableSet.preimage (continuous_const.mul continuous_id).measurable

/-- Each fractional ideal fiber has Haar mass one after integral units are normalized to one. -/
theorem measure_heckeFiniteIdealFiber_eq_one
    [MeasurableSpace (FiniteZetaIdeles K)] [BorelSpace (FiniteZetaIdeles K)]
    (mu : Measure (FiniteZetaIdeles K)) [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (FiniteZetaIdeles K)) = 1)
    (I : FiniteZetaIdeals K) : mu (heckeFiniteIdealFiber I) = 1 := by
  let b := Classical.choose (surjective_heckeFiniteIdeleIdealHom (K := K) I)
  have hb := Classical.choose_spec (surjective_heckeFiniteIdeleIdealHom (K := K) I)
  have hm := (measurePreserving_mul_left mu b).map_eq
  have hm' : Measurable (fun x : FiniteZetaIdeles K => b * x) :=
    (continuous_const.mul continuous_id).measurable
  rw [<- hm, Measure.map_apply hm' (measurableSet_heckeFiniteIdealFiber I),
    heckeFiniteIdealFiber_preimage_mul I b hb]
  exact hUnit


/-- Fractional-ideal fibers are countable in a number field. -/
theorem countable_finiteZetaIdeals : Countable (FiniteZetaIdeals K) := by
  let e := (Module.finBasis Rat K).equivFun
  let : Countable K := e.injective.countable
  have hFG (I : FiniteZetaIdeals K) : exists s : Finset K,
      Submodule.span (RingOfIntegers K) (s : Set K) =
        (I.val : Submodule (RingOfIntegers K) K) := by
    choose s hs hSpan using Submodule.fg_def.mp (FractionalIdeal.fg_unit I)
    exact Exists.intro hs.toFinset (by rw [Set.Finite.coe_toFinset, hSpan])
  choose g hg using hFG
  have hInj : Function.Injective g := by
    intro I J h
    apply Units.ext
    apply FractionalIdeal.coe_ext
    rw [<- hg I, <- hg J, h]
  exact hInj.countable

theorem measurable_heckeFiniteIdeleIdealHom
    [MeasurableSpace (FiniteZetaIdeles K)] [BorelSpace (FiniteZetaIdeles K)]
    [MeasurableSpace (FiniteZetaIdeals K)] :
    Measurable (heckeFiniteIdeleIdealHom (K := K)) := by
  let : Countable (FiniteZetaIdeals K) := countable_finiteZetaIdeals
  intro s hs
  have hU : Set.preimage (heckeFiniteIdeleIdealHom (K := K)) s =
      Set.iUnion (fun j : s => heckeFiniteIdealFiber j.val) := by
    ext x
    change Membership.mem s (heckeFiniteIdeleIdealHom x) <->
      Membership.mem _ x
    rw [Set.mem_iUnion]
    constructor
    case mp =>
      intro hx
      exact Exists.intro (Subtype.mk (heckeFiniteIdeleIdealHom x) hx) rfl
    case mpr =>
      intro h
      choose j hj using h
      change heckeFiniteIdeleIdealHom x = j.val at hj
      rw [hj]
      exact j.property
  rw [hU]
  exact MeasurableSet.iUnion (fun j => measurableSet_heckeFiniteIdealFiber j.val)

/-- Haar measure of the finite ideles pushes forward to counting measure on fractional ideals. -/
theorem map_heckeFiniteIdeleIdealHom_eq_count
    [MeasurableSpace (FiniteZetaIdeles K)] [BorelSpace (FiniteZetaIdeles K)]
    [MeasurableSpace (FiniteZetaIdeals K)] [MeasurableSingletonClass (FiniteZetaIdeals K)]
    (mu : Measure (FiniteZetaIdeles K)) [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (FiniteZetaIdeles K)) = 1) :
    Measure.map (heckeFiniteIdeleIdealHom (K := K)) mu = Measure.count := by
  let : Countable (FiniteZetaIdeals K) := countable_finiteZetaIdeals
  apply Measure.ext_of_singleton
  intro I
  rw [Measure.map_apply measurable_heckeFiniteIdeleIdealHom (measurableSet_singleton I)]
  change mu (heckeFiniteIdealFiber I) = Measure.count {I}
  rw [measure_heckeFiniteIdealFiber_eq_one mu hUnit I]
  simp


/-- For a Tate density constant on finite unit cosets, integrability and
the integral are given by the absolutely convergent fractional-ideal sum. -/
theorem heckeFiniteIdealPullback_integrable_and_integral
    [MeasurableSpace (FiniteZetaIdeles K)] [BorelSpace (FiniteZetaIdeles K)]
    [MeasurableSpace (FiniteZetaIdeals K)] [MeasurableSingletonClass (FiniteZetaIdeals K)]
    (mu : Measure (FiniteZetaIdeles K)) [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (FiniteZetaIdeles K)) = 1)
    (c : FiniteZetaIdeals K -> Complex) (hc : Summable (fun I => norm (c I))) :
    And (Integrable (fun b : FiniteZetaIdeles K => c (heckeFiniteIdeleIdealHom b)) mu)
      (integral mu (fun b : FiniteZetaIdeles K => c (heckeFiniteIdeleIdealHom b)) = tsum c) := by
  let : Countable (FiniteZetaIdeals K) := countable_finiteZetaIdeals
  have hCount : Integrable c Measure.count := integrable_count_iff.mpr hc
  have hMap := map_heckeFiniteIdeleIdealHom_eq_count mu hUnit
  have hC : Integrable c (Measure.map (heckeFiniteIdeleIdealHom (K := K)) mu) := by
    rw [hMap]
    exact hCount
  have hIdeal : AEMeasurable (heckeFiniteIdeleIdealHom (K := K)) mu :=
    measurable_heckeFiniteIdeleIdealHom.aemeasurable
  refine And.intro ((integrable_map_measure hC.aestronglyMeasurable hIdeal).mp hC) ?_
  rw [<- integral_map hIdeal hC.aestronglyMeasurable, hMap, integral_countable hCount]
  apply tsum_congr
  intro I
  simp [measureReal_def]

private abbrev FullFactorIdeles (K : Type*) [Field K] [NumberField K] :=
  Units (AdeleRing (RingOfIntegers K) K)

/-- The local Tate test transforms by the inverse character under integral units. -/
theorem heckeLocalTateTest_mul_integralUnit {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (chi : UnitaryHeckeCharacter K)
    (a u : Units (p.adicCompletion K))
    (hu : (Valued.v (u : p.adicCompletion K) : WithZero (Multiplicative Int)) = 1) :
    heckeLocalTateTest p chi (a * u) =
      heckeLocalTateTest p chi a * (chi.val (localIdeleHom K p (Inv.inv u)) : Complex) := by
  have hVal :
      (Valued.v ((a * u : Units (p.adicCompletion K)) : p.adicCompletion K) :
        WithZero (Multiplicative Int)) = Valued.v (a : p.adicCompletion K) := by
    rw [Units.val_mul, Valuation.map_mul, hu, mul_one]
  have hUnit : Membership.mem (heckeLocalUnitShell p) (a * u) <->
      Membership.mem (heckeLocalUnitShell p) a := by
    change _ = (1 : WithZero (Multiplicative Int)) <-> _ = 1
    rw [hVal]
  have hIdx : heckeLocalValueIndex p (a * u) = heckeLocalValueIndex p a := by
    apply WithZero.coe_inj.mp
    rw [coe_heckeLocalValueIndex, coe_heckeLocalValueIndex, hVal]
  have hIntegral : Membership.mem (heckeLocalIntegralUnits p) (a * u) <->
      Membership.mem (heckeLocalIntegralUnits p) a := by
    change Multiplicative.toAdd (heckeLocalValueIndex p (a * u)) <= 0 <->
      Multiplicative.toAdd (heckeLocalValueIndex p a) <= 0
    rw [hIdx]
  by_cases hUnram : HeckeUnramifiedAt chi p
  case pos =>
    have huInv : (Valued.v ((Inv.inv u : Units (p.adicCompletion K)) : p.adicCompletion K) :
        WithZero (Multiplicative Int)) = 1 := by
      rw [Units.val_inv_eq_inv_val, Valuation.map_inv, hu, inv_one]
    simp only [heckeLocalTateTest, if_pos hUnram, hUnram (Inv.inv u) huInv,
      Circle.coe_one, mul_one, Set.indicator_apply, hIntegral]
  case neg =>
    simp only [heckeLocalTateTest, if_neg hUnram, heckeLocalRamifiedTest]
    by_cases ha : Membership.mem (heckeLocalUnitShell p) a
    case pos =>
      rw [Set.indicator_of_mem (hUnit.mpr ha), Set.indicator_of_mem ha]
      rw [mul_inv_rev, map_mul, map_mul, Circle.coe_mul, mul_comm]
    case neg =>
      rw [Set.indicator_of_notMem (fun h => ha (hUnit.mp h)), Set.indicator_of_notMem ha, zero_mul]


/-- Include a finite idele with archimedean component one. -/
def heckeFiniteIdeleInclusion :
    MonoidHom (FiniteZetaIdeles K) (FullFactorIdeles K) where
  toFun b :=
    { val := Prod.mk 1 b.val
      inv := Prod.mk 1 b.inv
      val_inv := Prod.ext (by
        change (1 : InfiniteAdeleRing K) * 1 = 1
        exact one_mul 1) b.val_inv
      inv_val := Prod.ext (by
        change (1 : InfiniteAdeleRing K) * 1 = 1
        exact one_mul 1) b.inv_val }
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext (Prod.ext (one_mul (1 : InfiniteAdeleRing K)).symm rfl)

private def integralFiniteUnitCoordinate
    (u : FiniteZetaIdeles K) (hu : Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) u)
    (p : HeightOneSpectrum (RingOfIntegers K)) : Units (p.adicCompletionIntegers K) := by
  have hv : forall q : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (q.adicCompletionIntegers K) (u.val q) :=
    ((mem_heckeIntegralFiniteUnitGroup u).mp hu).1
  have hi : forall q : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (q.adicCompletionIntegers K) (u.inv q) :=
    ((mem_heckeIntegralFiniteUnitGroup u).mp hu).2
  exact
    { val := Subtype.mk (u.val p) (hv p)
      inv := Subtype.mk (u.inv p) (hi p)
      val_inv := Subtype.ext (congrArg (fun x : FiniteAdeleRing (RingOfIntegers K) K => x p) u.val_inv)
      inv_val := Subtype.ext (congrArg (fun x : FiniteAdeleRing (RingOfIntegers K) K => x p) u.inv_val) }

private theorem finiteIntegralIdeleHom_coordinate_eq_finiteInclusion
    (u : FiniteZetaIdeles K) (hu : Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) u) :
    finiteIntegralIdeleHom K (integralFiniteUnitCoordinate u hu) = heckeFiniteIdeleInclusion u := by
  apply Units.ext
  refine Prod.ext (finiteIntegralIdeleHom_infinite K _) ?_
  apply DFunLike.ext
  intro p
  rw [finiteIntegralIdeleHom_finite_apply]
  rfl

/-- A finite integral unit contributes only the ramified local character values. -/
theorem heckeFiniteIdeleInclusion_character_eq_local_product
    (chi : UnitaryHeckeCharacter K) (u : FiniteZetaIdeles K)
    (hu : Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) u) :
    chi.val (heckeFiniteIdeleInclusion u) =
      (finite_heckeRamifiedPlaces chi).toFinset.prod (fun p =>
        chi.val (localIdeleHom K p (heckeFiniteIdeleComponent p u))) := by
  rw [<- finiteIntegralIdeleHom_coordinate_eq_finiteInclusion u hu,
    heckeCharacter_on_integralFiniteIdeles_eq_local_product]
  apply Finset.prod_congr rfl
  intro p _
  rfl

/-- Right translation by a finite integral unit multiplies the Tate test
by its inverse character value. -/
theorem heckeFiniteAdditiveTateTest_mul_integralUnit
    (chi : UnitaryHeckeCharacter K) (b u : FiniteZetaIdeles K)
    (hu : Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) u) :
    heckeFiniteAdditiveTateTest chi (b * u).val =
      heckeFiniteAdditiveTateTest chi b.val * (chi.val (heckeFiniteIdeleInclusion (Inv.inv u)) : Complex) := by
  let R := (finite_heckeRamifiedPlaces chi).toFinset
  have hVals := (mem_heckeIntegralFiniteUnitGroup u).mp hu
  have hSup : Membership.mem (heckeIntegralFiniteAdeles (K := K)) (b * u).val <->
      Membership.mem (heckeIntegralFiniteAdeles (K := K)) b.val := by
    constructor
    case mp =>
      intro h p
      have hProd := (p.adicCompletionIntegers K).mul_mem _ _ (h p) (hVals.2 p)
      change Membership.mem (p.adicCompletionIntegers K)
        ((b.val p * u.val p) * u.inv p) at hProd
      have hCancel : u.val p * u.inv p = 1 := congrArg
        (fun a : FiniteAdeleRing (RingOfIntegers K) K => a p) u.val_inv
      rw [mul_assoc, hCancel, mul_one] at hProd
      exact hProd
    case mpr =>
      intro h p
      exact (p.adicCompletionIntegers K).mul_mem _ _ (h p) (hVals.1 p)
  have hLocal (p : HeightOneSpectrum (RingOfIntegers K)) :
      heckeLocalAdditiveTateTest p chi ((b * u).val p) =
        heckeLocalAdditiveTateTest p chi (b.val p) *
          (chi.val (localIdeleHom K p (heckeFiniteIdeleComponent p (Inv.inv u))) : Complex) := by
    let a := heckeFiniteIdeleComponent p b
    let e := heckeFiniteIdeleComponent p u
    change heckeLocalAdditiveTateTest p chi ((a * e : Units (p.adicCompletion K)) : p.adicCompletion K) =
      heckeLocalAdditiveTateTest p chi (a : p.adicCompletion K) * _
    rw [heckeLocalAdditiveTateTest_coe_unit, heckeLocalAdditiveTateTest_coe_unit, map_inv]
    exact heckeLocalTateTest_mul_integralUnit p chi a e
      ((mem_heckeIntegralFiniteUnitGroup_iff_valued_one u).mp hu p)
  let f (p : HeightOneSpectrum (RingOfIntegers K)) : Circle :=
    chi.val (localIdeleHom K p (heckeFiniteIdeleComponent p (Inv.inv u)))
  have hChar : chi.val (heckeFiniteIdeleInclusion (Inv.inv u)) = R.prod f :=
    heckeFiniteIdeleInclusion_character_eq_local_product chi (Inv.inv u)
      ((heckeIntegralFiniteUnitGroup (K := K)).inv_mem hu)
  have hCharCast : (chi.val (heckeFiniteIdeleInclusion (Inv.inv u)) : Complex) =
      R.prod (fun p => (f p : Complex)) := by
    calc
      _ = Circle.coeHom (R.prod f) := congrArg Circle.coeHom hChar
      _ = _ := map_prod Circle.coeHom f R
  by_cases hb : Membership.mem (heckeIntegralFiniteAdeles (K := K)) b.val
  case pos =>
    rw [heckeFiniteAdditiveTateTest, if_pos (hSup.mpr hb), heckeFiniteAdditiveTateTest, if_pos hb, hCharCast]
    simp_rw [hLocal]
    exact Finset.prod_mul_distrib
  case neg =>
    have hNot : Not (Membership.mem (heckeIntegralFiniteAdeles (K := K)) (b * u).val) :=
      fun h => hb (hSup.mp h)
    rw [heckeFiniteAdditiveTateTest, if_neg hNot, heckeFiniteAdditiveTateTest, if_neg hb, zero_mul]

/-- The finite part of the weighted Tate density. -/
def heckeFiniteTateDensity (chi : UnitaryHeckeCharacter K) (s : Complex)
    (b : FiniteZetaIdeles K) : Complex :=
  heckeFiniteAdditiveTateTest chi b.val *
    (Complex.exp (s * (Real.log (heckeFiniteIdeleNorm b) : Complex)) *
      (chi.val (heckeFiniteIdeleInclusion b) : Complex))

/-- The weighted density descends to the cosets corresponding to fractional ideals. -/
theorem heckeFiniteTateDensity_mul_integralUnit
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (chi : UnitaryHeckeCharacter K) (s : Complex) (b u : FiniteZetaIdeles K)
    (hu : Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) u) :
    heckeFiniteTateDensity chi s (b * u) = heckeFiniteTateDensity chi s b := by
  have hCancel : chi.val (heckeFiniteIdeleInclusion (Inv.inv u)) *
      chi.val (heckeFiniteIdeleInclusion u) = 1 := by
    rw [<- map_mul, <- map_mul, inv_mul_cancel, map_one, map_one]
  have hCast := congrArg (fun x : Circle => (x : Complex)) hCancel
  simp only [Circle.coe_mul, Circle.coe_one] at hCast
  unfold heckeFiniteTateDensity
  rw [heckeFiniteAdditiveTateTest_mul_integralUnit chi b u hu,
    map_mul heckeFiniteIdeleNorm, heckeFiniteIdeleNorm_eq_one_of_integralUnit u hu, mul_one,
    map_mul heckeFiniteIdeleInclusion, map_mul, Circle.coe_mul]
  let T := heckeFiniteAdditiveTateTest chi b.val
  let W := Complex.exp (s * (Real.log (heckeFiniteIdeleNorm b) : Complex))
  let Cb : Complex := chi.val (heckeFiniteIdeleInclusion b)
  let Cu : Complex := chi.val (heckeFiniteIdeleInclusion u)
  let Ci : Complex := chi.val (heckeFiniteIdeleInclusion (Inv.inv u))
  change (T * Ci) * (W * (Cb * Cu)) = T * (W * Cb)
  have hUnit : Ci * Cu = 1 := hCast
  calc
    _ = (T * (W * Cb)) * (Ci * Cu) := by ac_rfl
    _ = _ := by rw [hUnit, mul_one]

/-- The coefficient of the weighted finite Tate density on a fractional ideal. -/
def heckeFiniteTateIdealWeight (chi : UnitaryHeckeCharacter K) (s : Complex)
    (I : FiniteZetaIdeals K) : Complex :=
  heckeFiniteTateDensity chi s
    (Classical.choose (surjective_heckeFiniteIdeleIdealHom (K := K) I))

/-- The finite Tate density is the pullback of its fractional-ideal coefficient. -/
theorem heckeFiniteTateDensity_eq_idealWeight
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (chi : UnitaryHeckeCharacter K) (s : Complex) (b : FiniteZetaIdeles K) :
    heckeFiniteTateDensity chi s b =
      heckeFiniteTateIdealWeight chi s (heckeFiniteIdeleIdealHom b) := by
  let mapI := heckeFiniteIdeleIdealHom (K := K)
  let I := mapI b
  let a := Classical.choose (surjective_heckeFiniteIdeleIdealHom (K := K) I)
  let u := Inv.inv a * b
  have hIa : mapI a = I :=
    Classical.choose_spec (surjective_heckeFiniteIdeleIdealHom (K := K) I)
  have hIu : mapI u = 1 := by
    unfold u
    rw [map_mul, map_inv, hIa]
    exact inv_mul_cancel I
  have hu : Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) u :=
    (heckeFiniteIdeleIdealHom_eq_one_iff u).mp hIu
  have hbu : a * u = b := by
    unfold u
    rw [<- mul_assoc, mul_inv_cancel, one_mul]
  change heckeFiniteTateDensity chi s b = heckeFiniteTateDensity chi s a
  rw [<- hbu]
  exact heckeFiniteTateDensity_mul_integralUnit chi s a u hu

/-- With normalized unit-coset measure, the finite Tate integral is the
fractional-ideal sum whenever that sum is absolutely convergent. -/
theorem integral_heckeFiniteTateDensity_eq_idealSum
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [MeasurableSpace (FiniteZetaIdeles K)] [BorelSpace (FiniteZetaIdeles K)]
    [MeasurableSpace (FiniteZetaIdeals K)] [MeasurableSingletonClass (FiniteZetaIdeals K)]
    (mu : Measure (FiniteZetaIdeles K)) [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (FiniteZetaIdeles K)) = 1)
    (chi : UnitaryHeckeCharacter K) (s : Complex)
    (hSum : Summable (fun I : FiniteZetaIdeals K => norm (heckeFiniteTateIdealWeight chi s I))) :
    And (Integrable (heckeFiniteTateDensity chi s) mu)
      (integral mu (heckeFiniteTateDensity chi s) = tsum (heckeFiniteTateIdealWeight chi s)) := by
  have hEq := funext (heckeFiniteTateDensity_eq_idealWeight chi s)
  rw [hEq]
  exact heckeFiniteIdealPullback_integrable_and_integral mu hUnit
    (heckeFiniteTateIdealWeight chi s) hSum

end Robin1984.GRH
