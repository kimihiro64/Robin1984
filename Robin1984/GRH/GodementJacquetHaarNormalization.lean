import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Robin1984.GRH.GodementJacquetMatrixMeasure
import Robin1984.GRH.HeckeTateAdelicEuler

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's adelic Fourier analysis and the additive determinant modulus in the Godement-Jacquet zeta integral.
- Formalization note: Normalizes the additive adelic measure at the finite integral subgroup and the archimedean trace coordinates, then proves the inverse idelic determinant scaling law.
- PROVENANCE-END
-/

/-!
# Normalized additive measure on adelic matrices

The archimedean factor is Euclidean Lebesgue measure transported to the
infinite adeles. The finite factor gives the integral adeles mass one.
Their product scales under multiplication by an idele by the inverse
idelic norm.

Applying this scalar identity in the determinant scaling theorem gives
the change of variables for an invertible adelic matrix on any finite
index set.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure
open scoped Classical FourierTransform RealInnerProductSpace

variable {K : Type*} [Field K] [NumberField K]

private abbrev FiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev Minkowski (K : Type*) [Field K] := DedekindZeta.Theta.minkowskiSpace K

section FiniteHaar

variable [MeasurableSpace (FiniteAdeles K)] [BorelSpace (FiniteAdeles K)]

private theorem map_finiteAdele_mul_unit_haar
    (mu : Measure (FiniteAdeles K)) [mu.IsAddHaarMeasure] [mu.Regular]
    (b : Units (FiniteAdeles K)) :
    Measure.map (fun z : FiniteAdeles K => b.val * z) mu =
      HSMul.hSMul (Real.toNNReal (heckeFiniteIdeleNorm (Inv.inv b))) mu := by
  let : LocallyCompactSpace (FiniteAdeles K) := locallyCompactSpace_heckeFiniteAdeles
  have hb : (heckeFiniteAdditiveModulus (Inv.inv b)) =
      Real.toNNReal (heckeFiniteIdeleNorm (Inv.inv b)) := by
    rw [<- heckeFiniteAdditiveModulus_eq_ideleNorm]
    exact Real.toNNReal_coe.symm
  rw [<- hb]
  exact map_finiteAdele_mul_unit_additiveHaar mu b

end FiniteHaar

private theorem map_minkowski_idele_mul_haar (b : Units (InfiniteAdeleRing K)) :
    Measure.map (heckeInfiniteIdeleDilation b) (volume : Measure (Minkowski K)) =
      HSMul.hSMul (Real.toNNReal (heckeInfiniteIdeleNorm (Inv.inv b)))
        (volume : Measure (Minkowski K)) := by
  let f : LinearEquiv (RingHom.id Real) (Minkowski K) (Minkowski K) :=
    (heckeInfiniteIdeleDilation b).toLinearEquiv
  have hdet : Not (LinearMap.det f.toLinearMap = 0) :=
    f.isUnit_det'.ne_zero
  have h := map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Minkowski K)) hdet
  have hn : heckeInfiniteIdeleNorm (Inv.inv b) = Inv.inv (heckeInfiniteIdeleNorm b) := by
    rw [map_inv]
  change Measure.map (heckeInfiniteIdeleDilation b) (volume : Measure (Minkowski K)) =
    HSMul.hSMul (ENNReal.ofReal (heckeInfiniteIdeleNorm (Inv.inv b)))
      (volume : Measure (Minkowski K))
  rw [hn]
  have hf : (f.toLinearMap : Minkowski K -> Minkowski K) =
      (heckeInfiniteIdeleDilation b : Minkowski K -> Minkowski K) := rfl
  have ha : abs (LinearMap.det f.toLinearMap) = heckeInfiniteIdeleNorm b :=
    abs_det_heckeInfiniteIdeleDilation b
  rw [hf, abs_inv, ha] at h
  exact h

variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]

private def infiniteAdeleMinkowskiEquiv : MeasurableEquiv (InfiniteAdeleRing K) (Minkowski K) :=
  { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv.trans
      (DedekindZeta.Theta.toMinkowski K).toEquiv
    measurable_toFun := (DedekindZeta.Theta.toMinkowski K).continuous.measurable.comp
      (continuous_heckeInfiniteAdele_mixedSpace (K := K)).measurable
    measurable_invFun := (continuous_heckeInfiniteAdele_mixedSpace_symm K).measurable.comp
      (DedekindZeta.Theta.toMinkowski K).symm.continuous.measurable }

/-- The archimedean additive Haar measure in the Euclidean trace coordinates. -/
def heckeInfiniteAdeleAdditiveHaar : Measure (InfiniteAdeleRing K) :=
  Measure.map (infiniteAdeleMinkowskiEquiv (K := K)).symm
    (volume : Measure (Minkowski K))

instance : SigmaFinite (heckeInfiniteAdeleAdditiveHaar (K := K)) :=
  (infiniteAdeleMinkowskiEquiv (K := K)).symm.sigmaFinite_map

private theorem map_infiniteAdele_mul_unit_haar (b : Units (InfiniteAdeleRing K)) :
    Measure.map (fun x : InfiniteAdeleRing K => b.val * x) heckeInfiniteAdeleAdditiveHaar =
      HSMul.hSMul (Real.toNNReal (heckeInfiniteIdeleNorm (Inv.inv b)))
        heckeInfiniteAdeleAdditiveHaar := by
  let e := infiniteAdeleMinkowskiEquiv (K := K)
  let r := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let T := DedekindZeta.Theta.toMinkowski K
  let f := fun x : InfiniteAdeleRing K => b.val * x
  let g := heckeInfiniteIdeleDilation b
  have he (x : InfiniteAdeleRing K) : e x = T (r x) := rfl
  have hf : Measurable f := (continuous_const.mul continuous_id).measurable
  have hg : Measurable g := g.continuous.measurable
  have hcomp : Function.comp f e.symm = Function.comp e.symm g := by
    funext z
    apply e.injective
    change e (b.val * e.symm z) = e (e.symm (heckeInfiniteIdeleDilation b z))
    rw [e.apply_symm_apply, he, map_mul, heckeInfiniteIdeleDilation_apply]
    have he' : r (e.symm z) = T.symm z := by
      apply T.injective
      change e (e.symm z) = T (T.symm z)
      rw [e.apply_symm_apply, T.apply_symm_apply]
    rw [he']
  change Measure.map f (Measure.map e.symm (volume : Measure (Minkowski K))) =
    HSMul.hSMul (Real.toNNReal (heckeInfiniteIdeleNorm (Inv.inv b)))
      (Measure.map e.symm (volume : Measure (Minkowski K)))
  rw [Measure.map_map hf e.symm.measurable, hcomp, <- Measure.map_map e.symm.measurable hg]
  change Measure.map e.symm (Measure.map (heckeInfiniteIdeleDilation b) _) = _
  rw [map_minkowski_idele_mul_haar, Measure.map_smul (Real.toNNReal (heckeInfiniteIdeleNorm (Inv.inv b)))]

instance : (heckeInfiniteAdeleAdditiveHaar (K := K)).IsAddLeftInvariant := by
  constructor
  intro a
  let e := infiniteAdeleMinkowskiEquiv (K := K)
  let f := fun x : InfiniteAdeleRing K => a + x
  let g := fun z : Minkowski K => e a + z
  have he (x y : InfiniteAdeleRing K) : e (x + y) = e x + e y := by
    let r := InfiniteAdeleRing.ringEquiv_mixedSpace K
    let T := DedekindZeta.Theta.toMinkowski K
    change T (r (x + y)) = T (r x) + T (r y)
    rw [r.map_add, T.map_add]
  have hf : Measurable f := (continuous_const.add continuous_id).measurable
  have hg : Measurable g := (continuous_const.add continuous_id).measurable
  have hcomp : Function.comp f e.symm = Function.comp e.symm g := by
    funext z
    apply e.injective
    change e (a + e.symm z) = e (e.symm (e a + z))
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
  change Measure.map f (Measure.map e.symm (volume : Measure (Minkowski K))) =
    Measure.map e.symm (volume : Measure (Minkowski K))
  rw [Measure.map_map hf e.symm.measurable, hcomp, <- Measure.map_map e.symm.measurable hg,
    map_add_left_eq_self (volume : Measure (Minkowski K)) (e a)]

section ProductHaar

variable [MeasurableSpace (FiniteAdeles K)] [BorelSpace (FiniteAdeles K)]

private abbrev GlobalAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

local instance : MeasurableSpace (GlobalAdeles K) :=
  inferInstanceAs (MeasurableSpace (Prod (InfiniteAdeleRing K) (FiniteAdeles K)))

private instance : SigmaFinite (heckeFiniteAdeleHaar (K := K)) := by
  let : LocallyCompactSpace (FiniteAdeles K) := locallyCompactSpace_heckeFiniteAdeles
  let : SecondCountableTopology (FiniteAdeles K) := secondCountableTopology_heckeFiniteAdeles K
  unfold heckeFiniteAdeleHaar
  infer_instance

/-- Product additive measure with finite integral subgroup of mass one
and Lebesgue measure in the archimedean trace coordinates. -/
def heckeAdeleAdditiveHaar : Measure (GlobalAdeles K) :=
  (heckeInfiniteAdeleAdditiveHaar (K := K)).prod (heckeFiniteAdeleHaar (K := K))

instance : SigmaFinite (heckeAdeleAdditiveHaar (K := K)) :=
  @Measure.prod.instSigmaFinite (InfiniteAdeleRing K) (FiniteAdeles K) _
    (heckeInfiniteAdeleAdditiveHaar (K := K)) _ _
    (heckeFiniteAdeleHaar (K := K)) _

instance : (heckeAdeleAdditiveHaar (K := K)).IsAddLeftInvariant := by
  constructor
  intro a
  let f := fun x : InfiniteAdeleRing K => a.1 + x
  let g := fun x : FiniteAdeles K => a.2 + x
  let muI := heckeInfiniteAdeleAdditiveHaar (K := K)
  let muF := heckeFiniteAdeleHaar (K := K)
  have hf : Measurable f := (continuous_const.add continuous_id).measurable
  have hg : Measurable g := (continuous_const.add continuous_id).measurable
  change Measure.map (Prod.map f g) (muI.prod muF) = muI.prod muF
  rw [<- Measure.map_prod_map muI muF hf hg, map_add_left_eq_self muI a.1,
    map_add_left_eq_self muF a.2]

theorem map_adele_mul_unit_haar (a : Units (GlobalAdeles K)) :
    Measure.map (fun x : GlobalAdeles K => a.val * x) heckeAdeleAdditiveHaar =
      HSMul.hSMul (Real.toNNReal (heckeIdelicNorm (Inv.inv a))) heckeAdeleAdditiveHaar := by
  let p := (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeles K)).toMonoidHom
  let q := (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeles K)).toMonoidHom
  let i := Units.map p a
  let f := Units.map q a
  let muI := heckeInfiniteAdeleAdditiveHaar (K := K)
  let muF := heckeFiniteAdeleHaar (K := K)
  let : LocallyCompactSpace (FiniteAdeles K) := locallyCompactSpace_heckeFiniteAdeles
  let : muF.IsAddHaarMeasure := by
    unfold muF heckeFiniteAdeleHaar
    infer_instance
  let : muF.Regular := by
    unfold muF heckeFiniteAdeleHaar
    infer_instance
  have hI : Measurable (fun x : InfiniteAdeleRing K => i.val * x) :=
    (continuous_const.mul continuous_id).measurable
  have hF : Measurable (fun x : FiniteAdeles K => f.val * x) :=
    (continuous_const.mul continuous_id).measurable
  have hNorm : Real.toNNReal (heckeIdelicNorm (Inv.inv a)) =
      Real.toNNReal (heckeInfiniteIdeleNorm (Inv.inv i)) *
        Real.toNNReal (heckeFiniteIdeleNorm (Inv.inv f)) := by
    change Real.toNNReal (heckeInfiniteIdeleNorm (Units.map p (Inv.inv a)) *
      heckeFiniteIdeleNorm (Units.map q (Inv.inv a))) = _
    rw [show Units.map p (Inv.inv a) = Inv.inv i from map_inv _ _,
      show Units.map q (Inv.inv a) = Inv.inv f from map_inv _ _,
      Real.toNNReal_mul (heckeInfiniteIdeleNorm_pos (Inv.inv i)).le]
  change Measure.map
    (Prod.map (fun x : InfiniteAdeleRing K => i.val * x)
      (fun x : FiniteAdeles K => f.val * x)) (muI.prod muF) =
    HSMul.hSMul (Real.toNNReal (heckeIdelicNorm (Inv.inv a))) (muI.prod muF)
  rw [<- Measure.map_prod_map muI muF hI hF,
    map_infiniteAdele_mul_unit_haar i, map_finiteAdele_mul_unit_haar muF f,
    Measure.prod_smul_left (Real.toNNReal (heckeInfiniteIdeleNorm (Inv.inv i))),
    Measure.prod_smul_right (Real.toNNReal (heckeFiniteIdeleNorm (Inv.inv f))),
    smul_smul, hNorm]

private def extendUnitMultiplier {R : Type*} [CommMonoid R]
    (chi : MonoidHom (Units R) NNReal) : MonoidHom R NNReal := by
  classical
  let f (x : R) := if hx : IsUnit x then chi hx.unit else 0
  refine { toFun := f, map_one' := ?_, map_mul' := ?_ }
  . have hu : (isUnit_one : IsUnit (1 : R)).unit = 1 :=
      Units.ext (isUnit_one : IsUnit (1 : R)).unit_spec
    change f 1 = 1
    simp only [f, dif_pos isUnit_one, hu, map_one]
  . intro a b
    change f (a * b) = f a * f b
    by_cases ha : IsUnit a
    . by_cases hb : IsUnit b
      . have hab := ha.mul hb
        have h : hab.unit = ha.unit * hb.unit := by
          apply Units.ext
          rw [Units.val_mul, hab.unit_spec, ha.unit_spec, hb.unit_spec]
        simp only [f, dif_pos hab, dif_pos ha, dif_pos hb, h, map_mul]
      . have hab : Not (IsUnit (a * b)) := fun h => hb (isUnit_of_mul_isUnit_right h)
        simp only [f, dif_neg hab, dif_pos ha, dif_neg hb, mul_zero]
    . have hab : Not (IsUnit (a * b)) := fun h => ha (isUnit_of_mul_isUnit_left h)
      simp only [f, dif_neg hab, dif_neg ha, zero_mul]

private theorem extendUnitMultiplier_apply {R : Type*} [CommMonoid R]
    (chi : MonoidHom (Units R) NNReal) (u : Units R) :
    extendUnitMultiplier chi u.val = chi u := by
  classical
  change (if h : IsUnit u.val then chi h.unit else 0) = chi u
  rw [dif_pos u.isUnit, show u.isUnit.unit = u from Units.ext u.isUnit.unit_spec]

private def inverseIdelicNorm : MonoidHom (Units (AdeleRing (RingOfIntegers K) K)) NNReal where
  toFun a := Real.toNNReal (heckeIdelicNorm (Inv.inv a))
  map_one' := by simp
  map_mul' a b := by
    rw [mul_inv_rev, map_mul, Real.toNNReal_mul (heckeIdelicNorm_pos (Inv.inv b)).le, mul_comm]

/-- Pushforward by an invertible adelic matrix scales the product Haar
measure by the inverse idelic norm of the matrix determinant. -/
theorem map_adeleMatrix_mulVec_idelicNorm {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (GlobalAdeles K)) (hM : IsUnit M) :
    Measure.map M.mulVec (Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K))) =
      HSMul.hSMul (Real.toNNReal (heckeIdelicNorm
        (Inv.inv ((Matrix.isUnit_iff_isUnit_det M).mp hM).unit)))
        (Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K))) := by
  let e : Homeomorph (InfiniteAdeleRing K) (mixedEmbedding.mixedSpace K) :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
      continuous_toFun := continuous_heckeInfiniteAdele_mixedSpace (K := K)
      continuous_invFun := continuous_heckeInfiniteAdele_mixedSpace_symm K }
  let : SecondCountableTopology (InfiniteAdeleRing K) :=
    e.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (FiniteAdeles K) := secondCountableTopology_heckeFiniteAdeles K
  let : SecondCountableTopology (GlobalAdeles K) :=
    inferInstanceAs (SecondCountableTopology (Prod (InfiniteAdeleRing K) (FiniteAdeles K)))
  let : BorelSpace (GlobalAdeles K) :=
    inferInstanceAs (BorelSpace (Prod (InfiniteAdeleRing K) (FiniteAdeles K)))
  let : MeasurableAdd (GlobalAdeles K) := inferInstance
  let delta : MonoidHom (GlobalAdeles K) NNReal := extendUnitMultiplier inverseIdelicNorm
  let mu := heckeAdeleAdditiveHaar (K := K)
  let hD := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have hadd : Measurable (fun p : Prod (GlobalAdeles K) (GlobalAdeles K) => p.1 + p.2) :=
    (continuous_fst.add continuous_snd).measurable
  have hmul (a : GlobalAdeles K) : Measurable (fun x : GlobalAdeles K => a * x) :=
    (continuous_const.mul continuous_id).measurable
  have hscale (a : Units (GlobalAdeles K)) :
      Measure.map (fun x : GlobalAdeles K => a.val * x) mu =
        HSMul.hSMul (delta a.val) mu := by
    rw [show delta a.val = inverseIdelicNorm a from extendUnitMultiplier_apply _ _]
    exact map_adele_mul_unit_haar a
  have hDelta : delta M.det = Real.toNNReal (heckeIdelicNorm (Inv.inv hD.unit)) :=
    (congrArg delta hD.unit_spec.symm).trans (extendUnitMultiplier_apply _ _)
  have hs := map_adeleMatrix_mulVec_det mu delta hadd hmul hscale M hM
  rw [hDelta] at hs
  exact hs

end ProductHaar

end Robin1984.GRH
