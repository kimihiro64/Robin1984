import Robin1984.GRH.GodementJacquetArchimedeanIwasawaProduct


/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The exponential chart for positive real units and archimedean Iwasawa integration.
- Formalization note: Identifies positive diagonal Haar measure with Lebesgue measure in logarithmic coordinates.
- PROVENANCE-END
-/

/-!
# Logarithmic coordinates for diagonal Haar measure

Coordinatewise exponentiation turns real translations into multiplication
by positive diagonal units. Its pushforward measure gives the diagonal
factor in the archimedean Iwasawa chart.
-/

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure

namespace Robin1984.GRH

section

variable (F : Type*) [RCLike F] (n : Nat)

local notation "A" => Units (Fin n -> F)
local notation "P" => positiveDiagonalSubgroup F n

private noncomputable def archPositiveDiagonalExp (x : Fin n -> Real) : P := by
  let a : A :=
    { val := fun i => (Real.exp (x i) : F)
      inv := fun i => (Real.exp (-(x i)) : F)
      val_inv := by
        funext i
        change (Real.exp (x i) : F) * (Real.exp (-(x i)) : F) = 1
        rw [<- RCLike.ofReal_mul, <- Real.exp_add, add_neg_cancel, Real.exp_zero, RCLike.ofReal_one]
      inv_val := by
        funext i
        change (Real.exp (-(x i)) : F) * (Real.exp (x i) : F) = 1
        rw [<- RCLike.ofReal_mul, <- Real.exp_add, neg_add_cancel, Real.exp_zero, RCLike.ofReal_one] }
  exact Subtype.mk a (fun i => Exists.intro (Real.exp (x i)) (And.intro (Real.exp_pos _) rfl))

private theorem archPositiveDiagonalExp_add (x y : Fin n -> Real) :
    archPositiveDiagonalExp F n (x + y) =
      archPositiveDiagonalExp F n x * archPositiveDiagonalExp F n y := by
  apply Subtype.ext
  apply Units.ext
  funext i
  change (Real.exp (x i + y i) : F) = (Real.exp (x i) : F) * (Real.exp (y i) : F)
  rw [Real.exp_add, RCLike.ofReal_mul]

/-- Exponentiating coordinatewise identifies real logarithms with positive diagonal units. -/
noncomputable def positiveDiagonalExpHomeomorph : Homeomorph (Fin n -> Real) P := by
  let E := archPositiveDiagonalExp F n
  let L (p : P) (i : Fin n) := Real.log (RCLike.re (p.val.val i))
  refine
    { toEquiv := { toFun := E, invFun := L, left_inv := ?_, right_inv := ?_ }
      continuous_toFun := ?_, continuous_invFun := ?_ }
  . intro x
    funext i
    change Real.log (RCLike.re (Real.exp (x i) : F)) = x i
    rw [RCLike.ofReal_re, Real.log_exp]
  . intro p
    apply Subtype.ext
    apply Units.ext
    funext i
    choose a ha using p.property i
    change (Real.exp (Real.log (RCLike.re (p.val.val i))) : F) = p.val.val i
    rw [ha.2, RCLike.ofReal_re, Real.exp_log ha.1]
  . have h : Continuous (fun x : Fin n -> Real => (E x).val) := by
      apply Units.continuous_iff.mpr
      refine And.intro (continuous_pi (fun i => ?_)) (continuous_pi (fun i => ?_))
      . change Continuous (fun x : Fin n -> Real => (Real.exp (x i) : F))
        exact RCLike.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_apply i))
      . change Continuous (fun x : Fin n -> Real => (Real.exp (-(x i)) : F))
        exact RCLike.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_apply i).neg)
    exact h.subtype_mk _
  . apply continuous_pi
    intro i
    apply continuous_iff_continuousAt.mpr
    intro p
    choose a ha using p.property i
    have hp : Not (RCLike.re (p.val.val i) = 0) := by
      rw [ha.2, RCLike.ofReal_re]
      exact ne_of_gt ha.1
    have hV : Continuous (fun x : P => x.val.val) :=
      (@Units.continuous_val (Fin n -> F) _ _).comp continuous_subtype_val
    have hRe : Continuous (fun x : P => RCLike.re (x.val.val i)) :=
      RCLike.continuous_re.comp ((continuous_apply i).comp hV)
    exact ContinuousAt.comp (g := Real.log) (Real.continuousAt_log hp) hRe.continuousAt

private theorem isHaarMeasure_positiveDiagonalExp
    [MeasurableSpace P] [BorelSpace P] :
    (Measure.map (positiveDiagonalExpHomeomorph F n)
      (volume : Measure (Fin n -> Real))).IsHaarMeasure := by
  let E := positiveDiagonalExpHomeomorph F n
  let EM := E.toMeasurableEquiv
  let mu : Measure (Fin n -> Real) := volume
  let m := mu.comap EM.symm
  have hM : m = Measure.map E mu := by
    apply Measure.ext
    intro s hs
    change mu.comap EM.symm s = Measure.map EM mu s
    rw [EM.symm.measurableEmbedding.comap_apply, Measure.map_apply EM.measurable hs]
    exact congrArg (fun t => mu t) (Equiv.image_eq_preimage_symm EM.symm.toEquiv s)
  have hInv : m.IsMulLeftInvariant := by
    constructor
    intro p
    have hRel : Function.comp (fun y : P => p * y) E =
        Function.comp E (fun x : Fin n -> Real => E.symm p + x) := by
      funext x
      change p * E x = E (E.symm p + x)
      have h := archPositiveDiagonalExp_add F n (E.symm p) x
      change E (E.symm p + x) = E (E.symm p) * E x at h
      rw [E.apply_symm_apply] at h
      exact h.symm
    change Measure.map (fun y : P => p * y) m = m
    rw [hM, Measure.map_map (measurable_const_mul p) E.continuous.measurable, hRel,
      <- Measure.map_map E.continuous.measurable (measurable_const_add (E.symm p)),
      map_add_left_eq_self mu]
  rw [<- hM]
  exact
    { toIsFiniteMeasureOnCompacts :=
        IsFiniteMeasureOnCompacts.comap' mu E.symm.continuous EM.symm.measurableEmbedding
      toIsMulLeftInvariant := hInv
      toIsOpenPosMeasure := IsOpenPosMeasure.comap mu E.symm.isOpenEmbedding }

variable [ProperSpace F] [SecondCountableTopology F]

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "G" => Units M
local notation "N" => valuationUpperUnitriangularSubgroup F n
local notation "T" => positiveUpperTriangularMatrixSubgroup F n
local notation "K" => Matrix.unitaryGroup (Fin n) F
local notation "Y" => (Fin n -> Real)

/-- Haar measure in diagonal logarithms, unitriangular entries and the compact
unitary factor is a positive multiple of the product measure. -/
theorem exists_pos_smul_map_exponentialIwasawaHaar
    [SecondCountableTopology N]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace N] [BorelSpace N]
    [MeasurableSpace T] [BorelSpace T]
    [MeasurableSpace K] [BorelSpace K]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [mu.IsHaarMeasure] [mu.InnerRegular]
    (muN : Measure N) [muN.IsHaarMeasure] [SigmaFinite muN]
    (muK : Measure K) [muK.IsHaarMeasure] [SFinite muK] :
    exists E : Homeomorph (Prod (Prod Y N) K) G,
      And (forall p, (E p).val =
        (Matrix.diagonal (fun i : Fin n => (Real.exp (p.1.1 i) : F)) * p.1.2.val.val.val) *
          (Inv.inv p.2).val)
        (exists c : NNReal, And (0 < c)
          (mu = HSMul.hSMul c (Measure.map E
            (((volume : Measure Y).prod muN).prod muK)))) := by
  let D := positiveDiagonalExpHomeomorph F n
  let muD := Measure.map D (volume : Measure Y)
  let _ : SecondCountableTopology P := D.symm.isEmbedding.secondCountableTopology
  let _ : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> F))
  have hK : Topology.IsEmbedding (fun k : K => k.val) := Topology.IsEmbedding.subtypeVal
  let _ : SecondCountableTopology K := hK.secondCountableTopology
  let _ : muD.IsHaarMeasure := isHaarMeasure_positiveDiagonalExp F n
  let _ : SigmaFinite muD := D.measurableEmbedding.sigmaFinite_map
  choose e he hScale using exists_pos_smul_map_fullArchimedeanIwasawaHaar F n mu muD muN muK
  let J := (D.prodCongr (Homeomorph.refl N)).prodCongr (Homeomorph.refl K)
  let E := J.trans e
  refine Exists.intro E (And.intro ?_ ?_)
  . intro p
    change (e (J p)).val = _
    rw [he]
    rfl
  . choose c hc using hScale
    refine Exists.intro c (And.intro hc.1 ?_)
    have hD : MeasurePreserving D (volume : Measure Y) muD :=
      { measurable := D.continuous.measurable, map_eq := rfl }
    have hJ : MeasurePreserving J (((volume : Measure Y).prod muN).prod muK)
        ((muD.prod muN).prod muK) :=
      (hD.prod (MeasurePreserving.id muN)).prod (MeasurePreserving.id muK)
    have hE : Measure.map E (((volume : Measure Y).prod muN).prod muK) =
        Measure.map e ((muD.prod muN).prod muK) := by
      change Measure.map (Function.comp e J) (((volume : Measure Y).prod muN).prod muK) = _
      rw [<- Measure.map_map e.continuous.measurable hJ.measurable, hJ.map_eq]
    rw [hE]
    exact hc.2

end

end Robin1984.GRH
