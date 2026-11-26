import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Robin1984.GRH.HeckeTateThetaQuotient

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's thesis, the positive-norm adelic theta integral.
- Formalization note: Uses local uniform convergence and exponential bounds on the norm-one idele class quotient to prove absolute Mellin integrability.
- PROVENANCE-END
-/

/-!
# Mellin integrability of the Tate theta sum

The principal sum converges locally uniformly, including on the true idele
class quotient. Its positive-log-norm tail and the Fourier-dual tail have
all real absolute Mellin moments.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain Filter Topology
open MeasureTheory
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev TateFiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

/-- The nonzero principal theta sum is jointly continuous on log norm and norm-one ideles. -/
theorem continuous_heckeTateThetaNormOne_joint
    (f : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) Complex)
    (T : TateFiniteAdeles K -> Complex) (hT : Continuous T)
    (S : Set (TateFiniteAdeles K)) (hS : IsCompact S)
    (hST : forall z : TateFiniteAdeles K, Not (Membership.mem S z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z : TateFiniteAdeles K, norm (T z) <= B) :
    Continuous (fun p : Prod Real (heckeNormOneIdeles K) => heckeTateThetaNormOne f T p.2 p.1) := by
  let H := heckeNormOneIdeles K
  let P := Prod Real H
  let A := Units (InfiniteAdeleRing K)
  let F := Units (TateFiniteAdeles K)
  let E : Homeomorph (Units (AdeleRing (RingOfIntegers K) K)) (Prod A F) := Homeomorph.prodUnits
  let aInf (p : P) : A := (E p.2.val).1
  let aFin (p : P) : F := (E p.2.val).2
  have hCInf : Continuous aInf :=
    continuous_fst.comp (E.continuous.comp (continuous_subtype_val.comp continuous_snd))
  have hCFin : Continuous aFin :=
    continuous_snd.comp (E.continuous.comp (continuous_subtype_val.comp continuous_snd))
  let : T2Space (InfiniteAdeleRing K) :=
    show T2Space (forall v : InfinitePlace K, v.Completion) from inferInstance
  let d := (Module.finrank Rat K : Real)
  have hd : 0 < d := by
    change 0 < (Module.finrank Rat K : Real)
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank Rat K)
  let c (t : Real) := Real.exp (t / d)
  have hScale : Continuous (fun p : P => c p.1) :=
    Real.continuous_exp.comp (continuous_fst.div_const _)
  let U := heckeIntegralFiniteUnitGroup (K := K)
  have hU : IsOpen U.carrier := by
    have hSet : U.carrier =
        Set.inter
          (Set.preimage (fun a : F => a.val) (heckeIntegralFiniteAdeles (K := K) : Set (TateFiniteAdeles K)))
          (Set.preimage (fun a : F => a.inv) (heckeIntegralFiniteAdeles (K := K) : Set (TateFiniteAdeles K))) :=
      Set.ext (fun a => mem_heckeIntegralFiniteUnitGroup a)
    rw [hSet]
    exact (isOpen_heckeIntegralFiniteAdeles.preimage Units.continuous_val).inter
      (isOpen_heckeIntegralFiniteAdeles.preimage Units.continuous_coe_inv)
  choose N hN using exists_nat_gt (Module.finrank Int (NumberField.mixedEmbedding.integerLattice K) : Real)
  apply continuous_iff_continuousAt.mpr
  intro p0
  choose CI hCI using exists_compact_mem_nhds (aInf p0)
  let g := Homeomorph.mulLeft (aFin p0)
  let CF := Set.image g U.carrier
  have hCF : IsCompact CF := isCompact_heckeIntegralFiniteUnitGroup.image g.continuous
  have hCFnhds : Membership.mem (nhds (aFin p0)) CF := by
    apply (g.isOpenMap _ hU).mem_nhds
    exact Exists.intro 1 (And.intro U.one_mem (mul_one _))
  choose M hM using exists_summable_heckeTateTheta_majorant CI hCI.1 CF hCF f T S hS hST B hB hBT N hN
  let L := p0.1 - 1
  let W : Set P := Set.inter
    (Set.inter (Set.preimage aInf CI) (Set.preimage aFin CF))
    (Set.preimage Prod.fst (Set.Ioi L))
  have hL : L < p0.1 := sub_lt_self _ zero_lt_one
  have hW : Membership.mem (nhds p0) W := by
    refine inter_mem (inter_mem ?_ ?_) ?_
    . exact hCInf.continuousAt.preimage_mem_nhds hCI.2
    . exact hCFin.continuousAt.preimage_mem_nhds hCFnhds
    . exact continuous_fst.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hL)
  let c0 := c L
  have hc0 : 0 < c0 := Real.exp_pos _
  let majorant (x : K) := M x * Inv.inv (c0 ^ N)
  have hMajorant : Summable majorant := hM.1.mul_right _
  have hTerm (x : K) : Continuous (fun p : P => heckeTateThetaNormOneTerm f T p.2 p.1 x) := by
    by_cases hx : x = 0
    . simp only [heckeTateThetaNormOneTerm, if_pos hx]
      exact continuous_const
    . change Continuous (fun p : P => if x = 0 then 0 else
        f (HSMul.hSMul (c p.1)
          (InfiniteAdeleRing.ringEquiv_mixedSpace K (aInf p).val * mixedEmbedding K x)) *
        T ((aFin p).val * algebraMap K (TateFiniteAdeles K) x))
      simp only [if_neg hx]
      exact (f.continuous.comp (hScale.smul
        ((continuous_heckeInfiniteAdele_mixedSpace.comp (Units.continuous_val.comp hCInf)).mul
          continuous_const))).mul
        (hT.comp ((Units.continuous_val.comp hCFin).mul continuous_const))
  have hDom (x : K) (p : P) (hp : Membership.mem W p) :
      norm (heckeTateThetaNormOneTerm f T p.2 p.1 x) <= majorant x := by
    have hInf : Membership.mem CI (aInf p) := hp.1.1
    have hFin : Membership.mem CF (aFin p) := hp.1.2
    have hpL : L < p.1 := hp.2
    have hC : c0 <= c p.1 := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hpL.le hd.le)
    have hPow : c0 ^ N <= c p.1 ^ N := by gcongr
    have hInv : Inv.inv (c p.1 ^ N) <= Inv.inv (c0 ^ N) := by
      rw [<- one_div, <- one_div]
      exact one_div_le_one_div_of_le (pow_pos hc0 _) hPow
    rw [norm_heckeTateThetaNormOneTerm]
    change heckeTateThetaAbsTerm f T (aInf p) (aFin p) (c p.1) x <= _
    exact (hM.2.2 (aInf p) hInf (aFin p) hFin (c p.1) (Real.exp_pos _) x).trans
      (mul_le_mul_of_nonneg_left hInv (hM.2.1 x))
  have hOn : ContinuousOn (fun p : P => heckeTateThetaNormOne f T p.2 p.1) W :=
    continuousOn_tsum (fun x => (hTerm x).continuousOn) hMajorant hDom
  exact hOn.continuousAt hW

/-- Joint continuity descends through the open idele class quotient map. -/
theorem continuous_heckeTateThetaNormOneClass_joint
    (f : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) Complex)
    (T : TateFiniteAdeles K -> Complex) (hT : Continuous T)
    (S : Set (TateFiniteAdeles K)) (hS : IsCompact S)
    (hST : forall z : TateFiniteAdeles K, Not (Membership.mem S z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z : TateFiniteAdeles K, norm (T z) <= B) :
    Continuous (fun p : Prod Real (heckeNormOneIdeleClass K) => heckeTateThetaNormOneClass f T p.1 p.2) := by
  let H := heckeNormOneIdeles K
  let C := heckeNormOneIdeleClass K
  let q := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
  let j : Prod Real H -> Prod Real C := Prod.map id q
  have hC : Continuous j := continuous_id.prodMap QuotientGroup.continuous_mk
  have hId : IsOpenMap (id : Real -> Real) := (Homeomorph.refl Real).isOpenMap
  have hOpen : IsOpenMap j := hId.prodMap QuotientGroup.isOpenMap_coe
  have hSur : Function.Surjective j := by
    intro p
    choose a ha using (Quotient.mk_surjective p.2)
    exact Exists.intro (Prod.mk p.1 a) (Prod.ext rfl ha)
  have hQuot := hOpen.isQuotientMap hC hSur
  apply hQuot.continuous_iff.mpr
  exact continuous_heckeTateThetaNormOne_joint f T hT S hS hST B hB hBT

/-- An exponential bound with rate exceeding the moment gives absolute integrability. -/
theorem integrable_heckeExpMoment_of_decay
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (f : Prod Real X -> Complex)
    (hf : AEStronglyMeasurable f ((volume.restrict (Set.Ioi (0 : Real))).prod mu))
    (C a b : Real) (hab : a < b)
    (h : forall p : Prod Real X, norm (f p) <= C * Real.exp (-b * p.1)) :
    Integrable (fun p : Prod Real X => norm (f p) * (Real.exp p.1) ^ a)
      ((volume.restrict (Set.Ioi (0 : Real))).prod mu) := by
  let nu : Measure Real := volume.restrict (Set.Ioi (0 : Real))
  have hExp : Integrable (fun t : Real => Real.exp ((a - b) * t)) nu :=
    integrableOn_exp_mul_Ioi (sub_neg.mpr hab) 0
  have hDom : Integrable (fun p : Prod Real X => C * Real.exp ((a - b) * p.1)) (nu.prod mu) :=
    (hExp.const_mul C).comp_fst mu
  have hW : AEStronglyMeasurable (fun p : Prod Real X => (Real.exp p.1) ^ a) (nu.prod mu) :=
    ((Real.continuous_exp.measurable.comp measurable_fst).pow_const a).aestronglyMeasurable
  apply hDom.mono' (hf.norm.mul hW)
  filter_upwards with p
  change norm (norm (f p) * (Real.exp p.1) ^ a) <= _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Real.exp_pos _).le _))]
  have hPow : (Real.exp p.1) ^ a = Real.exp (a * p.1) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
  rw [hPow]
  calc
    _ <= (C * Real.exp (-b * p.1)) * Real.exp (a * p.1) :=
      mul_le_mul_of_nonneg_right (h p) (Real.exp_pos _).le
    _ = C * Real.exp ((a - b) * p.1) := by
      rw [mul_assoc, <- Real.exp_add]
      congr 2
      ring

/-- All real absolute Mellin moments of the positive theta tail converge. -/
theorem integrable_heckeTateThetaNormOneClass_expMoment
    [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeleClass K)) [IsFiniteMeasure mu]
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : TateFiniteAdeles K -> Complex) (hT : Continuous T)
    (S : Set (TateFiniteAdeles K)) (hS : IsCompact S)
    (hST : forall z, Not (Membership.mem S z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z, norm (T z) <= B) (a : Real) :
    Integrable (fun p : Prod Real (heckeNormOneIdeleClass K) =>
      norm (heckeTateThetaNormOneClass f T p.1 p.2) * (Real.exp p.1) ^ a)
      ((volume.restrict (Set.Ioi (0 : Real))).prod mu) := by
  let d : Real := Module.finrank Rat K
  have hd : 0 < d := by
    change 0 < (Module.finrank Rat K : Real)
    exact_mod_cast Module.finrank_pos (R := Rat) (M := K)
  let rank : Real := Module.finrank Int (mixedEmbedding.integerLattice K)
  choose N hN using exists_nat_gt (max rank (a * d))
  have hNrank : rank < (N : Real) := lt_of_le_of_lt (le_max_left _ _) hN
  have haN : a < (N : Real) / d := by
    calc
      a = a * d / d := by rw [mul_div_assoc, div_self hd.ne', mul_one]
      _ < (N : Real) / d := div_lt_div_of_pos_right (lt_of_le_of_lt (le_max_right _ _) hN) hd
  choose D hD using exists_uniform_heckeTateThetaNormOneClass_bound f T S hS hST B hB hBT N hNrank
  have hMeas : AEStronglyMeasurable
      (fun p : Prod Real (heckeNormOneIdeleClass K) => heckeTateThetaNormOneClass f T p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : Real))).prod mu) :=
    (continuous_heckeTateThetaNormOneClass_joint f T hT S hS hST B hB hBT).measurable.aestronglyMeasurable
  apply integrable_heckeExpMoment_of_decay mu _ hMeas D a ((N : Real) / d) haN
  intro p
  have he : -((N : Real) / d) * p.1 = -(N : Real) * (p.1 / d) := by ring
  rw [he]
  exact hD.2 p.2 p.1

/-- The original finite Hecke test has all real absolute Mellin moments. -/
theorem integrable_heckeTateThetaNormOneClass_character_expMoment
    [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeleClass K)) [IsFiniteMeasure mu]
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (chi : UnitaryHeckeCharacter K) (a : Real) :
    Integrable (fun p : Prod Real (heckeNormOneIdeleClass K) =>
      norm (heckeTateThetaNormOneClass f (heckeFiniteAdditiveTateTest chi) p.1 p.2) *
        (Real.exp p.1) ^ a)
      ((volume.restrict (Set.Ioi (0 : Real))).prod mu) := by
  refine integrable_heckeTateThetaNormOneClass_expMoment mu f _
    (continuous_heckeFiniteAdditiveTateTest chi) _ isCompact_integralFiniteAdeles
    ?_ 1 zero_le_one (norm_heckeFiniteAdditiveTateTest_le_one chi) a
  intro z hz
  have hz' : Not (Membership.mem (heckeIntegralFiniteAdeles (K := K)) z) := hz
  rw [heckeFiniteAdditiveTateTest, if_neg hz']

/-- The negative-frequency finite Fourier dual has all real absolute Mellin moments. -/
theorem integrable_heckeTateThetaNormOneClass_dual_expMoment
    [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)]
    [MeasurableSpace (TateFiniteAdeles K)] [BorelSpace (TateFiniteAdeles K)]
    (mu : Measure (heckeNormOneIdeleClass K)) [IsFiniteMeasure mu]
    (nu : Measure (TateFiniteAdeles K)) [nu.IsAddHaarMeasure]
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (chi : UnitaryHeckeCharacter K) (a : Real) :
    Integrable (fun p : Prod Real (heckeNormOneIdeleClass K) =>
      norm (heckeTateThetaNormOneClass f
        (fun y => heckeFiniteFourierIntegral nu (heckeFiniteAdditiveTateTest chi) (-y)) p.1 p.2) *
          (Real.exp p.1) ^ a)
      ((volume.restrict (Set.Ioi (0 : Real))).prod mu) := by
  choose V hV using exists_compactSupport_heckeFiniteFourierIntegral_TateTest nu chi
  let W := Set.image (fun y : TateFiniteAdeles K => -y) V
  have hW : IsCompact W := hV.1.image continuous_neg
  have hV' (y : TateFiniteAdeles K) (hy : Not (Membership.mem W y)) :
      Not (Membership.mem V (-y)) := by
    intro h
    exact hy (Exists.intro (-y) (And.intro h (neg_neg y)))
  exact integrable_heckeTateThetaNormOneClass_expMoment mu f _
    ((continuous_heckeFiniteFourierIntegral_TateTest nu chi).comp continuous_neg) W hW
    (fun y hy => hV.2 (-y) (hV' y hy)) _ ENNReal.toReal_nonneg
    (fun y => norm_heckeFiniteFourierIntegral_TateTest_le nu chi (-y)) a

/-- The restriction of a unitary Hecke character to norm one is a continuous class character. -/
noncomputable def heckeNormOneClassCharacter (chi : UnitaryHeckeCharacter K) :
    ContinuousMonoidHom (heckeNormOneIdeleClass K) Circle := by
  let H := heckeNormOneIdeles K
  let P := heckePrincipalNormOneIdele K
  let f := chi.val.toMonoidHom.comp H.subtype
  have h : P.range <= f.ker := by
    intro a ha
    choose b hb using ha
    rw [<- hb]
    exact chi.property b
  refine { toMonoidHom := QuotientGroup.lift P.range f h, continuous_toFun := ?_ }
  apply (QuotientGroup.isQuotientMap_mk P.range).continuous_iff.mpr
  exact chi.val.continuous.comp continuous_subtype_val

/-- Evaluating the class character on a representative recovers the Hecke character. -/
@[simp] theorem heckeNormOneClassCharacter_mk (chi : UnitaryHeckeCharacter K)
    (a : heckeNormOneIdeles K) :
    heckeNormOneClassCharacter chi
      (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range a) = chi.val a.val := rfl

/-- A nontrivial unitary character has zero integral against a left-invariant measure. -/
theorem integral_continuousCircleCharacter_eq_zero
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (chi : ContinuousMonoidHom G Circle)
    (b : G) (hb : Not (chi b = 1)) :
    (integral mu (fun a => ((chi a : Circle) : Complex))) = 0 := by
  let F (a : G) : Complex := chi a
  let I : Complex := integral mu F
  have h : integral mu (fun a => F (b * a)) = integral mu F :=
    integral_mul_left_eq_self F b
  have hMul : (fun a => F (b * a)) = (fun a => F b * F a) := by
    funext a
    change ((chi (b * a) : Circle) : Complex) = _
    rw [map_mul]
    rfl
  rw [hMul, integral_const_mul] at h
  change F b * I = I at h
  have hNe : Not (F b = 1) := by
    intro hOne
    apply hb
    exact Subtype.ext hOne
  have hZero : (F b - 1) * I = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp hZero).resolve_left (sub_ne_zero.mpr hNe)

private abbrev ClassCoordinates (K : Type*) [Field K] [NumberField K] :=
  Prod Real (heckeNormOneIdeleClass K)

/-- The positive logarithmic-norm half of product measure on the class coordinates. -/
noncomputable def heckePositiveThetaMeasure
    [MeasurableSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeleClass K)) : Measure (ClassCoordinates K) :=
  (volume.restrict (Set.Ioi (0 : Real))).prod mu

/-- The positive theta integral weighted by a norm-one Hecke class character. -/
noncomputable def heckeTateThetaMellinTail
    [MeasurableSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeleClass K))
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : TateFiniteAdeles K -> Complex) (chi : UnitaryHeckeCharacter K) :
    Complex -> Complex :=
  heckeMellinTail (heckePositiveThetaMeasure mu)
    (fun p => ((heckeNormOneClassCharacter chi p.2 : Circle) : Complex) *
      heckeTateThetaNormOneClass f T p.1 p.2) (fun p => Real.exp p.1)

/-- Absolute moments of the theta series give an entire character-weighted Mellin tail. -/
theorem differentiable_heckeTateThetaMellinTail
    [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeleClass K)) [IsFiniteMeasure mu]
    (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
    (T : TateFiniteAdeles K -> Complex) (hT : Continuous T)
    (S : Set (TateFiniteAdeles K)) (hS : IsCompact S)
    (hST : forall z, Not (Membership.mem S z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z, norm (T z) <= B)
    (chi : UnitaryHeckeCharacter K) :
    Differentiable Complex (heckeTateThetaMellinTail mu f T chi) := by
  let q := heckeNormOneClassCharacter chi
  let r (p : ClassCoordinates K) := Real.exp p.1
  have hr : Continuous r := Real.continuous_exp.comp continuous_fst
  have hq : Continuous (fun p : ClassCoordinates K => ((q p.2 : Circle) : Complex)) :=
    continuous_subtype_val.comp (q.continuous.comp continuous_snd)
  have hF := hq.mul (continuous_heckeTateThetaNormOneClass_joint f T hT S hS hST B hB hBT)
  have hPos : Filter.Eventually (fun t : Real => 0 < t)
      (ae (volume.restrict (Set.Ioi (0 : Real)))) := ae_restrict_mem measurableSet_Ioi
  have hP : Filter.Eventually (fun p : ClassCoordinates K => 0 < p.1)
      (ae (heckePositiveThetaMeasure mu)) := by
    change Filter.Eventually (fun p : ClassCoordinates K => 0 < p.1)
      (ae ((volume.restrict (Set.Ioi (0 : Real))).prod mu))
    have hSet : MeasurableSet (Set.ofPred (fun p : ClassCoordinates K => 0 < p.1)) :=
      measurableSet_Ioi.preimage measurable_fst
    exact (Measure.ae_prod_iff_ae_ae hSet).mpr
      (hPos.mono (fun _ ht => Filter.Eventually.of_forall (fun _ => ht)))
  have hRadius : Filter.Eventually (fun p => 1 <= r p) (ae (heckePositiveThetaMeasure mu)) :=
    hP.mono (fun p hp => Real.one_le_exp_iff.mpr hp.le)
  apply differentiable_heckeMellinTail _ _ r
    hF.measurable.aestronglyMeasurable hr.measurable.aemeasurable hRadius
  intro a
  have hEq : (fun p : ClassCoordinates K =>
      norm (((q p.2 : Circle) : Complex) * heckeTateThetaNormOneClass f T p.1 p.2) * r p ^ a) =
      (fun p : ClassCoordinates K => norm (heckeTateThetaNormOneClass f T p.1 p.2) * r p ^ a) := by
    funext p
    rw [norm_mul, Circle.norm_coe, one_mul]
  change Integrable (fun p : ClassCoordinates K =>
    norm (((q p.2 : Circle) : Complex) * heckeTateThetaNormOneClass f T p.1 p.2) * r p ^ a)
    (heckePositiveThetaMeasure mu)
  rw [hEq]
  exact integrable_heckeTateThetaNormOneClass_expMoment mu f T hT S hS hST B hB hBT a

end Robin1984.GRH
