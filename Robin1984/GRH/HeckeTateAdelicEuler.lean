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

variable (K : Type*) [Field K] [NumberField K]

private abbrev TateProductGlobalAdeles :=
  AdeleRing (RingOfIntegers K) K

private def heckeTateGlobalFromProduct
    (p : Prod (Units (TateEulerMixedSpace K)) (Units (TateEulerFiniteAdeles K))) :
    Units (TateProductGlobalAdeles K) :=
  heckeInfiniteIdeleInclusion K
    (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toMonoidHom p.1) *
  heckeFiniteIdeleInclusion p.2

private def heckeTateProductFromGlobal (a : Units (TateProductGlobalAdeles K)) :
    Prod (Units (TateEulerMixedSpace K)) (Units (TateEulerFiniteAdeles K)) :=
  Prod.mk
    (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).toMonoidHom
      (Units.map (RingHom.fst (InfiniteAdeleRing K) (TateEulerFiniteAdeles K)).toMonoidHom a))
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (TateEulerFiniteAdeles K)).toMonoidHom a)

private theorem heckeTateGlobalFromProduct_val
    (p : Prod (Units (TateEulerMixedSpace K)) (Units (TateEulerFiniteAdeles K))) :
    (heckeTateGlobalFromProduct K p).val =
      Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm p.1.val) p.2.val := by
  apply Prod.ext
  . exact mul_one _
  . exact one_mul _

private theorem continuous_heckeTateGlobalFromProduct :
    Continuous (heckeTateGlobalFromProduct K) := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let F := TateEulerFiniteAdeles K
  let I := InfiniteAdeleRing K
  have hArch : Continuous (fun a : Units (TateEulerMixedSpace K) =>
      heckeInfiniteIdeleInclusion K (Units.map e.symm.toMonoidHom a)) := by
    have hCont : Continuous (fun a : I => Prod.mk a (1 : F)) :=
      continuous_id.prodMk continuous_const
    have h : Continuous (heckeInfiniteIdeleInclusion K) := Units.continuous_map hCont
    exact h.comp (Units.continuous_map (continuous_heckeInfiniteAdele_mixedSpace_symm K))
  have hFinite : Continuous (fun a : Units F => heckeFiniteIdeleInclusion a) := by
    let incl : MonoidHom F (TateProductGlobalAdeles K) :=
      (1 : MonoidHom F I).prod (MonoidHom.id F)
    have hEq : (fun a : Units F => heckeFiniteIdeleInclusion a) = Units.map incl := by
      funext a
      apply Units.ext
      rfl
    rw [hEq]
    exact Units.continuous_map (continuous_const.prodMk continuous_id)
  exact (hArch.comp continuous_fst).mul (hFinite.comp continuous_snd)

private theorem continuous_heckeTateProductFromGlobal :
    Continuous (heckeTateProductFromGlobal K) := by
  let I := InfiniteAdeleRing K
  let F := TateEulerFiniteAdeles K
  have hArch : Continuous (Units.map (RingHom.fst I F).toMonoidHom) :=
    Units.continuous_map (continuous_fst : Continuous (fun p : Prod I F => p.1))
  have hFinite : Continuous (Units.map (RingHom.snd I F).toMonoidHom) :=
    Units.continuous_map (continuous_snd : Continuous (fun p : Prod I F => p.2))
  exact ((Units.continuous_map (continuous_heckeInfiniteAdele_mixedSpace (K := K))).comp
    hArch).prodMk hFinite

/-- Splitting the full ideles into their mixed archimedean units and finite
ideles is a homeomorphism in the actual unit-group topologies. -/
def heckeTateProductIdelesHomeomorph :
    Homeomorph (Prod (Units (TateEulerMixedSpace K)) (Units (TateEulerFiniteAdeles K)))
      (Units (TateProductGlobalAdeles K)) where
  toFun := heckeTateGlobalFromProduct K
  invFun := heckeTateProductFromGlobal K
  left_inv p := by
    apply Prod.ext
    . apply Units.ext
      let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
      change e (heckeTateGlobalFromProduct K p).val.1 = p.1.val
      rw [heckeTateGlobalFromProduct_val]
      exact e.apply_symm_apply p.1.val
    . apply Units.ext
      change (heckeTateGlobalFromProduct K p).val.2 = p.2.val
      rw [heckeTateGlobalFromProduct_val]
  right_inv a := by
    apply Units.ext
    rw [heckeTateGlobalFromProduct_val]
    apply Prod.ext
    . let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
      change e.symm (e a.val.1) = a.val.1
      exact e.symm_apply_apply a.val.1
    . rfl
  continuous_toFun := continuous_heckeTateGlobalFromProduct K
  continuous_invFun := continuous_heckeTateProductFromGlobal K

theorem heckeTateProductIdelesHomeomorph_mul
    (p q : Prod (Units (TateEulerMixedSpace K)) (Units (TateEulerFiniteAdeles K))) :
    heckeTateProductIdelesHomeomorph K (p * q) =
      heckeTateProductIdelesHomeomorph K p * heckeTateProductIdelesHomeomorph K q := by
  change heckeTateGlobalFromProduct K (p * q) =
    heckeTateGlobalFromProduct K p * heckeTateGlobalFromProduct K q
  unfold heckeTateGlobalFromProduct
  change heckeInfiniteIdeleInclusion K
    (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toMonoidHom (p.1 * q.1)) *
      heckeFiniteIdeleInclusion (p.2 * q.2) = _
  simp only [map_mul]
  ac_rfl

section ProductMeasure

variable [MeasurableSpace (Units (TateEulerMixedSpace K))]
  [BorelSpace (Units (TateEulerMixedSpace K))]

private theorem sFinite_heckeInfiniteUnitMeasure : SFinite (heckeInfiniteUnitMeasure K) := by
  let H := DedekindZeta.GammaIntegral.mulHaar K
  let _ : SFinite H :=
    sFinite_of_absolutelyContinuous (withDensity_absolutelyContinuous volume _)
  let j (a : Units (TateEulerMixedSpace K)) := a.val
  have hj : MeasurableEmbedding j := measurableEmbedding_heckeInfiniteUnitVal
  let nu (n : Nat) := Measure.comap j (sfiniteSeq H n)
  have hn (n : Nat) : IsFiniteMeasure (nu n) := by
    constructor
    suffices nu n Set.univ <= sfiniteSeq H n Set.univ from
      lt_of_le_of_lt this (measure_lt_top _ _)
    dsimp only [nu]
    rw [Measure.comap_apply j hj.injective (fun _ => hj.measurableSet_image.mpr)
      _ MeasurableSet.univ]
    exact measure_mono (Set.subset_univ _)
  refine SFinite.mk (Exists.intro nu (And.intro hn ?_))
  apply Measure.ext
  intro s hs
  have hjS : MeasurableSet (j '' s) := hj.measurableSet_image.mpr hs
  change Measure.comap j H s = Measure.sum nu s
  rw [Measure.comap_apply j hj.injective (fun _ => hj.measurableSet_image.mpr) _ hs,
    Measure.sum_apply _ hs, <- sum_sfiniteSeq H, Measure.sum_apply _ hjS]
  congr 1
  funext n
  exact (Measure.comap_apply j hj.injective (fun _ => hj.measurableSet_image.mpr) _ hs).symm

variable [MeasurableSpace (Units (TateEulerFiniteAdeles K))]
  [BorelSpace (Units (TateEulerFiniteAdeles K))]
  [MeasurableSpace (Units (TateProductGlobalAdeles K))]
  [BorelSpace (Units (TateProductGlobalAdeles K))]

/-- The multiplicative coordinate map is a measurable equivalence. -/
def heckeTateProductIdelesMeasurableEquiv :
    MeasurableEquiv
      (Prod (Units (TateEulerMixedSpace K)) (Units (TateEulerFiniteAdeles K)))
      (Units (TateProductGlobalAdeles K)) := by
  let _ : SecondCountableTopology (Units (TateEulerMixedSpace K)) :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  exact (heckeTateProductIdelesHomeomorph K).toMeasurableEquiv

/-- The normalized full idelic measure given by the archimedean and finite
multiplicative measures. -/
def heckeTateProductIdelicMeasure (mu : Measure (Units (TateEulerFiniteAdeles K))) :
    Measure (Units (TateProductGlobalAdeles K)) :=
  Measure.map (heckeTateProductIdelesHomeomorph K) ((heckeInfiniteUnitMeasure K).prod mu)

variable [MeasurableSpace (TateEulerFiniteAdeles K)] [BorelSpace (TateEulerFiniteAdeles K)]

/-- The absolutely convergent Tate integral on the full ideles is the standard
product of the archimedean Gamma factors and the Hecke Euler product. -/
theorem integral_heckeTateProductIdelicMeasure
    [MeasurableSpace (Units (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))]
    [MeasurableSingletonClass (Units (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))]
    (mu : Measure (Units (TateEulerFiniteAdeles K))) [SFinite mu] [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (Units (TateEulerFiniteAdeles K))) = 1)
    (chi : UnitaryHeckeCharacter K)
    (f : SchwartzMap (TateEulerMixedSpace K) Complex)
    (hf : forall x, f x = heckeTateInfiniteTest chi x)
    {s : Complex} (hs : 1 < s.re) :
    let Z := fun a => heckeTateZetaWeight chi s a *
      heckeTateAdditiveIdelicTest f (heckeFiniteAdditiveTateTest chi) a
    let nu := heckeTateProductIdelicMeasure K mu
    And (Integrable Z nu)
      (integral nu Z =
        ((Finset.univ.prod (fun v : {w : InfinitePlace K // w.IsReal} =>
          DedekindZeta.LReal (s + realInfiniteHeckeShift chi v.property))) *
        (Finset.univ.prod (fun v : {w : InfinitePlace K // w.IsComplex} =>
          DedekindZeta.LComplex (s + complexInfiniteHeckeShift chi v.property)))) *
        heckeEulerL K chi s) := by
  let E := TateEulerMixedSpace K
  let F := TateEulerFiniteAdeles K
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let j : Prod (Units E) (Units F) -> Prod E (Units F) :=
    Prod.map (fun a : Units E => a.val) id
  let H := (heckeInfiniteUnitMeasure K).prod mu
  let T := heckeTateProductIdelesHomeomorph K
  let Z : Units (TateProductGlobalAdeles K) -> Complex := fun a =>
    heckeTateZetaWeight chi s a *
      heckeTateAdditiveIdelicTest f (heckeFiniteAdditiveTateTest chi) a
  let W := heckeTateWeightedProductTest chi s
  let _ : SFinite (heckeInfiniteUnitMeasure K) := sFinite_heckeInfiniteUnitMeasure K
  have hVal : MeasurableEmbedding (fun a : Units E => a.val) :=
    measurableEmbedding_heckeInfiniteUnitVal
  have hId : MeasurableEmbedding (id : Units F -> Units F) := MeasurableEmbedding.id
  have hj : MeasurableEmbedding j := hVal.prodMap hId
  have hT : MeasurableEmbedding T :=
    (heckeTateProductIdelesMeasurableEquiv K).measurableEmbedding
  have hMap : Measure.map j H = (DedekindZeta.GammaIntegral.mulHaar K).prod mu := by
    change Measure.map (Prod.map (fun a : Units E => a.val) id)
      ((heckeInfiniteUnitMeasure K).prod mu) = _
    rw [<- Measure.map_prod_map _ _ hVal.measurable hId.measurable,
      map_heckeInfiniteUnitMeasure_val, Measure.map_id]
  have hFun : Z.comp T = W.comp j := by
    funext p
    have hp : IsUnit p.1.val := p.1.isUnit
    have hu : hp.unit = p.1 := Units.ext hp.unit_spec
    change Z (T p) =
      (dite (IsUnit p.1.val)
        (fun hx => heckeTateZetaWeight chi s
          (heckeInfiniteIdeleInclusion K (Units.map e.symm.toMonoidHom hx.unit) *
            heckeFiniteIdeleInclusion p.2) *
          (heckeTateInfiniteTest chi p.1.val *
            heckeFiniteAdditiveTateTest chi p.2.val))
        (fun _ => 0))
    rw [dif_pos hp, hu]
    change heckeTateZetaWeight chi s (heckeTateGlobalFromProduct K p) *
      heckeTateAdditiveIdelicTest f (heckeFiniteAdditiveTateTest chi)
        (heckeTateGlobalFromProduct K p) = _
    unfold heckeTateAdditiveIdelicTest
    rw [heckeTateGlobalFromProduct_val]
    change _ * (f (e (e.symm p.1.val)) * _) = _
    rw [e.apply_symm_apply, hf]
    rfl
  have hValFormula := integral_heckeTateWeightedProductTest mu hUnit chi hs
  change And (Integrable Z (Measure.map T H)) _
  refine And.intro ?_ ?_
  . rw [hT.integrable_map_iff, hFun, <- hj.integrable_map_iff, hMap]
    exact hValFormula.1
  . change integral (Measure.map T H) Z = _
    rw [hT.integral_map Z]
    change integral H (Z.comp T) = _
    rw [hFun]
    change integral H (fun p => W (j p)) = _
    rw [<- hj.integral_map W, hMap]
    exact hValFormula.2

end ProductMeasure

end Robin1984.GRH
