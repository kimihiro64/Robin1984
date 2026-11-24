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

section EulerClassNormalization

open NumberField.InfinitePlace Filter TopologicalSpace

private theorem norm_heckeInfiniteUnit_pos (a : Units (TateEulerMixedSpace K)) :
    0 < mixedEmbedding.norm a.val := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let b := Units.map e.symm.toMonoidHom a
  have h : e b.val = a.val := e.apply_symm_apply a.val
  rw [<- h, mixedEmbedding_norm_infiniteIdele]
  exact heckeInfiniteIdeleNorm_pos b

private def archUnitDensity (x : TateEulerMixedSpace K) : ENNReal :=
  ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * Inv.inv (mixedEmbedding.norm x))

private theorem measurable_archUnitDensity : Measurable (archUnitDensity K) :=
  (measurable_const.mul (mixedEmbedding.continuous_norm K).measurable.inv).ennreal_ofReal

private theorem archUnitDensity_pos (a : Units (TateEulerMixedSpace K)) : 0 < archUnitDensity K a.val := by
  apply ENNReal.ofReal_pos.mpr
  exact mul_pos (pow_pos (div_pos (by norm_num) Real.pi_pos) _)
    (inv_pos.mpr (norm_heckeInfiniteUnit_pos K a))

section ArchimedeanHaar

variable [MeasurableSpace (Units (TateEulerMixedSpace K))] [BorelSpace (Units (TateEulerMixedSpace K))]

theorem isHaarMeasure_heckeInfiniteUnitMeasure : (heckeInfiniteUnitMeasure K).IsHaarMeasure := by
  let M := heckeInfiniteUnitMeasure K
  let j (a : Units (TateEulerMixedSpace K)) := a.val
  let rho := archUnitDensity K
  have hj : MeasurableEmbedding j := measurableEmbedding_heckeInfiniteUnitVal
  let _ : M.IsMulRightInvariant := isMulRightInvariant_heckeInfiniteUnitMeasure
  have hImage (s : Set (Units (TateEulerMixedSpace K))) (hs : MeasurableSet s) :
      M s = (volume.withDensity rho) (j '' s) :=
    Measure.comap_apply j hj.injective (fun _ => hj.measurableSet_image.mpr)
      (volume.withDensity rho) hs
  have hLeft : M.IsMulLeftInvariant := by
    constructor
    intro a
    change Measure.map (fun b : Units (TateEulerMixedSpace K) => a * b) M = M
    simp_rw [mul_comm a]
    exact (measurePreserving_mul_right M a).map_eq
  have hCompact : IsFiniteMeasureOnCompacts M := by
    constructor
    intro s hs
    let v (a : Units (TateEulerMixedSpace K)) : Real :=
      (2 / Real.pi) ^ nrComplexPlaces K * Inv.inv (mixedEmbedding.norm a.val)
    have hInv (a : Units (TateEulerMixedSpace K)) : mixedEmbedding.norm a.inv =
        Inv.inv (mixedEmbedding.norm a.val) := by
      apply eq_inv_of_mul_eq_one_left
      rw [<- map_mul, a.inv_val, map_one]
    have hv : Continuous v := by
      change Continuous (fun a : Units (TateEulerMixedSpace K) =>
        (2 / Real.pi) ^ nrComplexPlaces K * Inv.inv (mixedEmbedding.norm a.val))
      simp only [<- hInv]
      exact continuous_const.mul ((mixedEmbedding.continuous_norm K).comp Units.continuous_coe_inv)
    choose B hB using hs.bddAbove_image hv.continuousOn
    have hJ : IsCompact (j '' s) := hs.image Units.continuous_val
    rw [hImage s hs.measurableSet, withDensity_apply rho hJ.measurableSet]
    have hDom : Filter.EventuallyLE (ae (volume.restrict (j '' s))) rho
        (fun _ => ENNReal.ofReal B) := by
      apply (ae_restrict_mem hJ.measurableSet).mono
      intro y hy
      choose a ha hay using hy
      rw [<- hay]
      exact ENNReal.ofReal_le_ofReal (hB (Set.mem_image_of_mem v ha))
    apply lt_of_le_of_lt (lintegral_mono_ae hDom)
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.mul_lt_top (by simp) hJ.measure_lt_top
  have hOpen : M.IsOpenPosMeasure := by
    constructor
    intro s hs hne
    rw [hImage s hs.measurableSet]
    have hJ : IsOpen (j '' s) := Units.isOpenEmbedding_val.isOpenMap s hs
    have hSupport : Inter.inter {x | Not (rho x = 0)} (j '' s) = j '' s := by
      apply Set.inter_eq_right.mpr
      intro y hy
      choose a ha hay using hy
      rw [<- hay]
      exact (archUnitDensity_pos K a).ne'
    intro hz
    have hm : AEMeasurable rho (volume : Measure (TateEulerMixedSpace K)) :=
      (measurable_archUnitDensity K).aemeasurable
    have hv := (withDensity_apply_eq_zero' hm).mp hz
    rw [hSupport] at hv
    exact (hJ.measure_pos volume (hne.image j)).ne' hv
  exact { toIsMulLeftInvariant := hLeft
          toIsFiniteMeasureOnCompacts := hCompact
          toIsOpenPosMeasure := hOpen }

end ArchimedeanHaar

section FiniteHaar

theorem isOpen_heckeIntegralFiniteUnitGroup :
    IsOpen (heckeIntegralFiniteUnitGroup (K := K) : Set (Units (TateEulerFiniteAdeles K))) := by
  let O : Set (TateEulerFiniteAdeles K) := heckeIntegralFiniteAdeles (K := K)
  have hO : IsOpen O := isOpen_heckeIntegralFiniteAdeles
  exact (hO.preimage Units.continuous_val).inter (hO.preimage Units.continuous_coe_inv)

variable [MeasurableSpace (Units (TateEulerFiniteAdeles K))] [BorelSpace (Units (TateEulerFiniteAdeles K))]

theorem isHaarMeasure_heckeNormalizedFiniteUnitMeasure (mu : Measure (Units (TateEulerFiniteAdeles K)))
    [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (Units (TateEulerFiniteAdeles K))) = 1) :
    mu.IsHaarMeasure := by
  let U : Set (Units (TateEulerFiniteAdeles K)) := heckeIntegralFiniteUnitGroup (K := K)
  have hI : (interior U).Nonempty := by
    rw [(isOpen_heckeIntegralFiniteUnitGroup K).interior_eq]
    exact Exists.intro 1 (heckeIntegralFiniteUnitGroup (K := K)).one_mem
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior mu U
    isCompact_heckeIntegralFiniteUnitGroup hI
  . rw [show mu U = 1 from hUnit]
    exact one_ne_zero
  . rw [show mu U = 1 from hUnit]
    exact ENNReal.one_ne_top

end FiniteHaar

private theorem countable_numberField : Countable K := by
  exact (Module.finBasis Rat K).equivFun.injective.countable

private theorem countable_heckeFinitePlaces : Countable (HeightOneSpectrum (RingOfIntegers K)) := by
  let R := RingOfIntegers K
  let _ : Countable K := countable_numberField K
  let _ : Countable R := (IsFractionRing.injective R K).countable
  have hSpan : Function.Surjective (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    choose s hs using IsNoetherian.noetherian (R := R) I
    exact Exists.intro s hs
  let _ : Countable (Ideal R) := hSpan.countable
  have hPrime : Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum R -> Ideal R) :=
    fun _ _ h => HeightOneSpectrum.ext h
  exact hPrime.countable

private theorem secondCountable_heckeAdicCompletion (v : HeightOneSpectrum (RingOfIntegers K)) :
    SecondCountableTopology (v.adicCompletion K) := by
  let _ : Countable K := countable_numberField K
  let L := v.adicCompletion K
  let _ : (uniformity L).IsCountablyGenerated :=
    (Valued.hasBasis_uniformity L (WithZero (Multiplicative Int))).isCountablyGenerated
  let _ : SeparableSpace L :=
    SeparableSpace.mk (Exists.intro (Set.range (algebraMap K L))
      (And.intro (Set.countable_range _) (v.denseRange_algebraMap K)))
  infer_instance

/-- The finite adeles are second countable, by the countable cover by charts
that allow exceptions at a prescribed finite set of places. -/
theorem secondCountableTopology_heckeFiniteAdeles :
    SecondCountableTopology (FiniteAdeleRing (RingOfIntegers K) K) := by
  let V := HeightOneSpectrum (RingOfIntegers K)
  let L (v : V) := v.adicCompletion K
  let A (v : V) : Set (L v) := v.adicCompletionIntegers K
  let _ : Countable V := countable_heckeFinitePlaces K
  let _ (v : V) : SecondCountableTopology (L v) := secondCountable_heckeAdicCompletion K v
  have hA (v : V) : IsOpen (A v) := Valued.isOpen_valuationSubring _
  let C (s : Finset V) : Set V := Compl.compl (s : Set V)
  have hC (s : Finset V) : Filter.cofinite <= Filter.principal (C s) :=
    le_principal_iff.mpr (mem_cofinite.mpr (by simpa only [C, compl_compl] using s.finite_toSet))
  let f (s : Finset V) := RestrictedProduct.inclusion L A (hC s)
  have hf (s : Finset V) : Topology.IsOpenEmbedding (f s) :=
    RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hC s)
  let U (s : Finset V) := Set.range (f s)
  let _ (s : Finset V) : SecondCountableTopology (RestrictedProduct L A (Filter.principal (C s))) :=
    (RestrictedProduct.isEmbedding_coe_of_principal (R := L) (A := A) (S := C s)).secondCountableTopology
  let _ (s : Finset V) : SecondCountableTopology (U s) :=
    (hf s).isEmbedding.toHomeomorph.symm.secondCountableTopology
  change SecondCountableTopology (RestrictedProduct L A Filter.cofinite)
  apply secondCountableTopology_of_countable_cover (U := U) (fun s => (hf s).isOpen_range)
  apply Set.eq_univ_of_forall
  intro x
  have hbad : (Compl.compl {v : V | Membership.mem (A v) (x v)}).Finite :=
    mem_cofinite.mp x.2
  let s := hbad.toFinset
  have hx (v : V) (hv : Membership.mem (C s) v) : Membership.mem (A v) (x v) := by
    change Not (Membership.mem s v) at hv
    by_contra h
    exact hv (hbad.mem_toFinset.mpr h)
  choose y hy using RestrictedProduct.exists_inclusion_eq_of_eventually L A (hC s) hx
  exact Set.mem_iUnion.mpr (Exists.intro s (Exists.intro y hy))

/-- The actual finite ideles inherit second countability from the two-coordinate
embedding that records an adele and its inverse. -/
theorem secondCountableTopology_heckeFiniteIdeles :
    SecondCountableTopology (Units (FiniteAdeleRing (RingOfIntegers K) K)) := by
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let _ : SecondCountableTopology F := secondCountableTopology_heckeFiniteAdeles K
  let _ : SecondCountableTopology (MulOpposite F) :=
    (MulOpposite.opHomeomorph (M := F)).symm.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := F)).secondCountableTopology

section GlobalHaar

private abbrev TateEulerFiniteIdeles := Units (TateEulerFiniteAdeles K)
private abbrev TateEulerGlobalIdeles := Units (TateProductGlobalAdeles K)

private theorem secondCountable_heckeInfiniteUnits :
    SecondCountableTopology (Units (TateEulerMixedSpace K)) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable [MeasurableSpace (TateEulerGlobalIdeles K)] [BorelSpace (TateEulerGlobalIdeles K)]

section ProductHaar

variable [MeasurableSpace (Units (TateEulerMixedSpace K))] [BorelSpace (Units (TateEulerMixedSpace K))]
  [MeasurableSpace (TateEulerFiniteIdeles K)] [BorelSpace (TateEulerFiniteIdeles K)]

private theorem isHaarMeasure_heckeTateProductIdelicMeasure
    (mu : Measure (TateEulerFiniteIdeles K)) [SFinite mu] [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (TateEulerFiniteIdeles K)) = 1) :
    (heckeTateProductIdelicMeasure K mu).IsHaarMeasure := by
  let E := Units (TateEulerMixedSpace K)
  let F := TateEulerFiniteIdeles K
  let G := TateEulerGlobalIdeles K
  let _ : SecondCountableTopology E := secondCountable_heckeInfiniteUnits K
  let _ : SecondCountableTopology F := secondCountableTopology_heckeFiniteIdeles K
  let _ : LocallyCompactSpace E := Units.isOpenEmbedding_val.locallyCompactSpace
  let _ : (heckeInfiniteUnitMeasure K).IsHaarMeasure := isHaarMeasure_heckeInfiniteUnitMeasure K
  let _ : mu.IsHaarMeasure := isHaarMeasure_heckeNormalizedFiniteUnitMeasure K mu hUnit
  let _ : SFinite (heckeInfiniteUnitMeasure K) := inferInstance
  let e : ContinuousMulEquiv (Prod E F) G :=
    { heckeTateProductIdelesHomeomorph K with
      map_mul' := heckeTateProductIdelesHomeomorph_mul K }
  change (Measure.map e ((heckeInfiniteUnitMeasure K).prod mu)).IsHaarMeasure
  exact e.isHaarMeasure_map _

end ProductHaar

variable [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]

private theorem isHaarMeasure_heckeIdelicLogNormMeasure
    (mu : Measure (heckeNormOneIdeles K)) [SFinite mu] [mu.IsHaarMeasure] :
    (heckeIdelicLogNormMeasure K mu).IsHaarMeasure := by
  let E := Units (TateEulerMixedSpace K)
  let F := TateEulerFiniteIdeles K
  let G := TateEulerGlobalIdeles K
  let N := heckeNormOneIdeles K
  let _ : SecondCountableTopology E := secondCountable_heckeInfiniteUnits K
  let _ : SecondCountableTopology F := secondCountableTopology_heckeFiniteIdeles K
  let _ : SecondCountableTopology G :=
    (heckeTateProductIdelesHomeomorph K).symm.secondCountableTopology
  let _ : SecondCountableTopology N :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (fun a : N => a.val)).secondCountableTopology
  let _ : MeasurableSpace (Multiplicative Real) := (inferInstance : MeasurableSpace Real)
  let _ : BorelSpace (Multiplicative Real) := (inferInstance : BorelSpace Real)
  let rho : Measure (Multiplicative Real) := (volume : Measure Real)
  let _ : rho.IsHaarMeasure := by
    refine { toIsFiniteMeasureOnCompacts :=
              (inferInstance : IsFiniteMeasureOnCompacts (volume : Measure Real))
             toIsOpenPosMeasure := (inferInstance : Measure.IsOpenPosMeasure (volume : Measure Real))
             toIsMulLeftInvariant := ?_ }
    constructor
    intro a
    change Measure.map (fun x : Real => Multiplicative.toAdd a + x) volume = volume
    exact (measurePreserving_add_left volume (Multiplicative.toAdd a)).map_eq
  let _ : SFinite rho := (inferInstance : SFinite (volume : Measure Real))
  let e : ContinuousMulEquiv G (Prod (Multiplicative Real) N) :=
    { heckeIdelicLogNormHomeomorph K with
      map_mul' := heckeIdelicLogNormHomeomorph_mul K }
  change (Measure.map e.symm (rho.prod mu)).IsHaarMeasure
  exact e.symm.isHaarMeasure_map _

variable [MeasurableSpace (Units (TateEulerMixedSpace K))] [BorelSpace (Units (TateEulerMixedSpace K))]
  [MeasurableSpace (TateEulerFiniteIdeles K)] [BorelSpace (TateEulerFiniteIdeles K)]

/-- The Euler normalization and a logarithmic norm-one Haar normalization
differ by one strictly positive scalar, independent of the character and s. -/
theorem exists_heckeTateProductIdelicMeasure_eq_logNorm_smul
    (mu : Measure (TateEulerFiniteIdeles K)) [SFinite mu] [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (TateEulerFiniteIdeles K)) = 1)
    (nu : Measure (heckeNormOneIdeles K)) [SFinite nu] [nu.IsHaarMeasure] :
    exists c : NNReal, And (0 < c)
      (heckeTateProductIdelicMeasure K mu = HSMul.hSMul c (heckeIdelicLogNormMeasure K nu)) := by
  let E := Units (TateEulerMixedSpace K)
  let F := TateEulerFiniteIdeles K
  let G := TateEulerGlobalIdeles K
  let N := heckeNormOneIdeles K
  let _ : SecondCountableTopology E := secondCountable_heckeInfiniteUnits K
  let _ : SecondCountableTopology F := secondCountableTopology_heckeFiniteIdeles K
  let _ : SecondCountableTopology G :=
    (heckeTateProductIdelesHomeomorph K).symm.secondCountableTopology
  let _ : LocallyCompactSpace N := locallyCompactSpace_heckeNormOneIdeles K
  let _ : LocallyCompactSpace G :=
    (heckeIdelicLogNormHomeomorph K).isOpenEmbedding.locallyCompactSpace
  let P := heckeTateProductIdelicMeasure K mu
  let L := heckeIdelicLogNormMeasure K nu
  let _ : P.IsHaarMeasure := isHaarMeasure_heckeTateProductIdelicMeasure K mu hUnit
  let _ : L.IsHaarMeasure := isHaarMeasure_heckeIdelicLogNormMeasure K nu
  exact Exists.intro (Measure.haarScalarFactor P L)
    (And.intro (Measure.haarScalarFactor_pos_of_isHaarMeasure P L)
      (Measure.isMulLeftInvariant_eq_smul P L))

/-- Rescale the norm-one Haar measure so its logarithmic product is exactly
the Euler-normalized measure on the full ideles. -/
theorem exists_heckeTateProductIdelicMeasure_eq_logNorm
    (mu : Measure (TateEulerFiniteIdeles K)) [SFinite mu] [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (TateEulerFiniteIdeles K)) = 1)
    (nu : Measure (heckeNormOneIdeles K)) [SFinite nu] [nu.IsHaarMeasure] :
    exists nu' : Measure (heckeNormOneIdeles K), And (nu'.IsHaarMeasure)
      (And (SFinite nu')
        (heckeTateProductIdelicMeasure K mu = heckeIdelicLogNormMeasure K nu')) := by
  choose c hc using exists_heckeTateProductIdelicMeasure_eq_logNorm_smul K mu hUnit nu
  let nu' : Measure (heckeNormOneIdeles K) := HSMul.hSMul c nu
  have hHaar : nu'.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul nu hc.1.ne'
  have hScale : heckeIdelicLogNormMeasure K nu' =
      HSMul.hSMul c (heckeIdelicLogNormMeasure K nu) := by
    unfold heckeIdelicLogNormMeasure heckeLogProductMeasure
    change Measure.map _ ((volume : Measure Real).prod (HSMul.hSMul c nu)) = _
    rw [Measure.prod_smul_right, Measure.map_smul]
  exact Exists.intro nu' (And.intro hHaar (And.intro (by dsimp [nu']; infer_instance)
    (hc.2.trans hScale.symm)))

variable
  [MeasurableSpace (TateEulerFiniteAdeles K)] [BorelSpace (TateEulerFiniteAdeles K)]
  [MeasurableSpace (heckeIdeleClass K)] [BorelSpace (heckeIdeleClass K)]
  [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)]

/-- In Euler-normalized logarithmic coordinates, the canonical class theta
integral equals the Gamma factors times the Euler product for Re(s) > 1. -/
theorem integral_heckeTateEulerClassTheta
    [MeasurableSpace (Units (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))]
    [MeasurableSingletonClass (Units (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))]
    (mu : Measure (TateEulerFiniteIdeles K)) [SFinite mu] [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) : Set (TateEulerFiniteIdeles K)) = 1)
    (nu : Measure (heckeNormOneIdeles K)) [SFinite nu] [nu.IsMulRightInvariant]
    (hNorm : heckeTateProductIdelicMeasure K mu = heckeIdelicLogNormMeasure K nu)
    {S : Set (heckeNormOneIdeles K)} (hS : MeasurableSet S)
    (hInj : Set.InjOn (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S)
    (hSur : Set.image (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S = Set.univ)
    (chi : UnitaryHeckeCharacter K) (f : SchwartzMap (TateEulerMixedSpace K) Complex)
    (hf : forall x, f x = heckeTateInfiniteTest chi x)
    {s : Complex} (hs : 1 < s.re) :
    integral (volume.prod (heckeNormOneClassQuotientMeasure K nu S))
      (heckeTateClassZetaIntegrand chi s f (heckeFiniteAdditiveTateTest chi)) =
        ((Finset.univ.prod (fun v : {w : InfinitePlace K // w.IsReal} =>
          DedekindZeta.LReal (s + realInfiniteHeckeShift chi v.property))) *
        (Finset.univ.prod (fun v : {w : InfinitePlace K // w.IsComplex} =>
          DedekindZeta.LComplex (s + complexInfiniteHeckeShift chi v.property)))) *
        heckeEulerL K chi s := by
  have h := integral_heckeTateProductIdelicMeasure K mu hUnit chi f hf hs
  dsimp only at h
  rw [hNorm] at h
  let U : Set (TateEulerFiniteAdeles K) := heckeIntegralFiniteAdeles (K := K)
  have hSupport (z : TateEulerFiniteAdeles K) (hz : Not (Membership.mem U z)) :
      heckeFiniteAdditiveTateTest chi z = 0 := by
    have hz' : Not (Membership.mem (heckeIntegralFiniteAdeles (K := K)) z) := hz
    rw [heckeFiniteAdditiveTateTest, if_neg hz']
  have hTheta := integral_heckeTateZeta_eq_classTheta nu hS hInj hSur chi s f
    (heckeFiniteAdditiveTateTest chi) (continuous_heckeFiniteAdditiveTateTest chi)
    U isCompact_integralFiniteAdeles hSupport 1 zero_le_one
    (norm_heckeFiniteAdditiveTateTest_le_one chi) h.1
  exact hTheta.symm.trans h.2

end GlobalHaar

end EulerClassNormalization

end Robin1984.GRH
