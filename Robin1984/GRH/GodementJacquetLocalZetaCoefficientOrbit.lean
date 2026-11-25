import Mathlib.MeasureTheory.Group.ModularCharacter
import Robin1984.GRH.GodementJacquetLocalZetaRationality

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement-Jacquet local zeta integrals and the two-sided action on matrix coefficients.
- Formalization note: Transfers the reduced denominator of one coefficient to the vector and dual orbit spans by normalized Haar invariance and integer determinant weights.
- PROVENANCE-END
-/

/-!
# Local zeta denominators for matrix coefficient orbits

Right invariance of the normalized finite-place Haar measure and the
two-sided change of variables move all group translates into the same
test-function space. Integer determinant weights are cleared by powers
of the local Euler variable. The resulting denominator is preserved by
finite linear combinations and therefore by the vector and dual orbit spans.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField Topology

namespace Robin1984.GRH

private theorem isMulRightInvariant_heckeLocalMatrixUnitWeightedMeasure
    {K : Type*} [Field K] [NumberField K]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace (Units (Matrix I I (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix I I (p.adicCompletion K)))] :
    (heckeLocalMatrixUnitWeightedMeasure p I).IsMulRightInvariant := by
  let L := p.adicCompletion K
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let G := Units (Matrix I I L)
  let e : G -> I -> I -> L := heckeLocalMatrixUnitEntries
  let nu := heckeLocalDeterminantWeightedMeasure p I
  let mu := heckeLocalMatrixUnitWeightedMeasure p I
  have hE : MeasurableEmbedding e := isOpenEmbedding_heckeLocalMatrixUnitEntries.measurableEmbedding
  have hMap : Measure.map e mu = nu := map_heckeLocalMatrixUnitWeightedMeasure p
  constructor
  intro m
  let f (X : I -> I -> L) : I -> I -> L :=
    @Mul.mul (Matrix I I L) inferInstance (Matrix.of X) m.val
  have hm : Measurable (fun g : G => g * m) := (continuous_id.mul continuous_const).measurable
  have hf : Measurable f := by
    have hMat : Continuous (fun X : I -> I -> L => Matrix.of X) :=
      continuous_matrixOf.mpr continuous_id
    have hMul : Continuous (fun X : I -> I -> L => Matrix.of X * m.val) :=
      hMat.mul continuous_const
    exact (continuous_pi (fun i => continuous_pi (fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp hMul)))).measurable
  have hRel : Function.comp e (fun g : G => g * m) = Function.comp f e := by
    funext g
    rfl
  apply hE.map_injective
  change Measure.map e (Measure.map (fun g : G => g * m) mu) = Measure.map e mu
  rw [Measure.map_map hE.measurable hm, hRel, <- Measure.map_map hf hE.measurable, hMap]
  exact map_heckeLocalDeterminantWeightedMeasure_mul_right p m

/-- The normalized Haar measure on the finite-place matrix group is right
invariant. Its determinant-density realization is invariant under right
multiplication, and the normalization scalar is positive. -/
theorem isMulRightInvariant_heckeLocalMatrixHaar
    {K : Type*} [Field K] [NumberField K]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))) [mu.IsHaarMeasure]
    :
    let L := p.adicCompletion K
    let G := Units (Matrix (Fin n) (Fin n) L)
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let C := valuationIntegralMatrixSubgroup v n
    mu (C : Set G) = 1 -> mu.IsMulRightInvariant := by
  intro L G v C hNorm
  let nu := heckeLocalMatrixUnitWeightedMeasure p (Fin n)
  let e : G -> Fin n -> Fin n -> L := heckeLocalMatrixUnitEntries
  let O : Set L := p.adicCompletionIntegers K
  have hOpen : IsOpen O := Valued.isOpen_valuationSubring L
  have hCompact : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_heckeLocalIntegers p)
  have hZero : Membership.mem O (0 : L) := (p.adicCompletionIntegers K).zero_mem
  let : LocallyCompactSpace L :=
    hCompact.locallyCompactSpace_of_mem_nhds_of_addGroup (hOpen.mem_nhds hZero)
  let : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  have he : IsOpenEmbedding e := isOpenEmbedding_heckeLocalMatrixUnitEntries
  let : LocallyCompactSpace G := he.locallyCompactSpace
  let : SecondCountableTopology G := he.isEmbedding.secondCountableTopology
  have hCOpen : IsOpen (C : Set G) :=
    isOpen_valuationIntegralMatrixSubgroup Valued.v n hOpen
  have hCCompact : IsCompact (C : Set G) :=
    isCompact_valuationIntegralMatrixSubgroup Valued.v n hCompact
  have hCNonempty : (C : Set G).Nonempty := Exists.intro 1 C.one_mem
  have hDet (g : G) (hg : Membership.mem (C : Set G) g) : norm g.val.det = 1 := by
    have hVal : Valued.v g.val.det = 1 := valuation_det_integralMatrixUnit v n g hg
    rw [FinitePlace.norm_def, hVal]
    simp
  let base := Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => heckeLocalAdditiveMeasure p))
  let c := (base (Set.image e (C : Set G))).toNNReal
  have hc : 0 < c := heckeLocalMatrixHaar_additiveNormalization_pos p (C : Set G)
    hCOpen hCCompact hCNonempty
  have hScale : nu = HSMul.hSMul c mu :=
    heckeLocalMatrixUnitWeightedMeasure_eq_smul_haar p mu (C : Set G)
      hCOpen.measurableSet hNorm hDet
  constructor
  intro g
  have hn := isMulRightInvariant_heckeLocalMatrixUnitWeightedMeasure p (I := Fin n)
  have hWeight : Measure.map (fun x : G => x * g) nu = nu := by
    cases hn with
    | mk h => exact h g
  rw [hScale, Measure.map_smul c, Measure.map_right_mul_eq_modularCharacterFun_smul] at hWeight
  have heval := congrArg (fun m : Measure G => m (C : Set G)) hWeight
  simp only [Measure.coe_nnreal_smul_apply, hNorm, mul_one] at heval
  have hc0 : Not ((c : ENNReal) = 0) := by exact_mod_cast hc.ne'
  have hmod : Measure.modularCharacterFun g = 1 := by
    apply ENNReal.coe_injective
    rw [ENNReal.coe_one]
    exact (ENNReal.mul_eq_right hc0 ENNReal.coe_ne_top).mp ((mul_comm _ _).trans heval)
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul, hmod, one_smul]

/-- Changing both sides of a matrix coefficient by group elements is
equivalent to translating the matrix test and multiplying its integral
by a determinant weight. Absolute integrability is preserved. -/
theorem exists_heckeLocalZetaTest_twoSidedTranslate
    {L : Type*} [NormedField L] (n : Nat)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [MeasurableMul (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L)))
    [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
    (a b : Units (Matrix (Fin n) (Fin n) L))
    (Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex) :
    let G := Units (Matrix (Fin n) (Fin n) L)
    let d : Real := norm a.val.det * norm b.val.det
    let f (z : Complex) (g : G) :=
      (norm g.val.det : Complex) ^ z * (Phi g.val * c (a * g * b))
    exists Psi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex,
      And (HasCompactSupport (fun X => Psi X)) (forall z : Complex,
        let h (g : G) := (norm g.val.det : Complex) ^ z * (Psi g.val * c g)
        And (Iff (Integrable (f z) mu) (Integrable h mu))
          (integral mu (f z) = (d : Complex) ^ (-z) * integral mu h)) := by
  intro G d f
  let M := Matrix (Fin n) (Fin n) L
  let e : Homeomorph M M :=
    { toFun := fun X => a.inv * X * b.inv
      invFun := fun X => a.val * X * b.val
      left_inv := fun X => by
        change a.val * (a.inv * X * b.inv) * b.val = X
        calc
          _ = (a.val * a.inv) * X * (b.inv * b.val) := by simp only [mul_assoc]
          _ = _ := by rw [a.val_inv, b.inv_val, one_mul, mul_one]
      right_inv := fun X => by
        change a.inv * (a.val * X * b.val) * b.inv = X
        calc
          _ = (a.inv * a.val) * X * (b.val * b.inv) := by simp only [mul_assoc]
          _ = _ := by rw [a.inv_val, b.val_inv, one_mul, mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  let Psi := LocallyConstant.comap (ContinuousMap.mk e e.continuous) Phi
  have hCompact : IsCompact (Set.preimage e (tsupport (fun X : M => Phi X))) :=
    e.isEmbedding.isInducing.isCompact_preimage' hPhi
      (fun X _ => Set.mem_range.mpr (e.surjective X))
  have hSupport : Set.Subset (Function.support (fun X : M => Psi X))
      (Set.preimage e (tsupport (fun X : M => Phi X))) := by
    intro X hX
    exact subset_closure (show Membership.mem (Function.support (fun Y : M => Phi Y))
      (e X) from hX)
  have hPsi : HasCompactSupport (fun X => Psi X) :=
    hCompact.of_isClosed_subset isClosed_closure
      (closure_minimal hSupport (isClosed_closure.preimage e.continuous))
  refine Exists.intro Psi (And.intro hPsi ?_)
  intro z h
  have hDPos : 0 < d := mul_pos
    (norm_pos_iff.mpr (a.isUnit.map Matrix.detMonoidHom).ne_zero)
    (norm_pos_iff.mpr (b.isUnit.map Matrix.detMonoidHom).ne_zero)
  have hD : Not ((d : Complex) ^ z = 0) :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hDPos.ne'))
  have hPow (g : G) : (norm ((a * g * b).val.det) : Complex) ^ z =
      (d : Complex) ^ z * (norm g.val.det : Complex) ^ z := by
    have hm : ((a * g * b).val.det) = (a.val.det * g.val.det) * b.val.det := by
      change (a.val * g.val * b.val).det = _
      rw [Matrix.det_mul, Matrix.det_mul]
    rw [hm, norm_mul, norm_mul, mul_right_comm]
    change ((d * norm g.val.det : Real) : Complex) ^ z = _
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hDPos.le (norm_nonneg _) z]
  have hTest (g : G) : Psi (a * g * b).val = Phi g.val := by
    change Phi (e (e.symm g.val)) = Phi g.val
    exact congrArg Phi (e.apply_symm_apply g.val)
  have hEq (g : G) : f z g = (d : Complex) ^ (-z) * h (a * g * b) := by
    change (norm g.val.det : Complex) ^ z * (Phi g.val * c (a * g * b)) =
      (d : Complex) ^ (-z) * ((norm ((a * g * b).val.det) : Complex) ^ z *
        (Psi (a * g * b).val * c (a * g * b)))
    rw [hTest, Complex.cpow_neg, hPow]
    field_simp [hD]
  rw [funext hEq]
  refine And.intro ?_ ?_
  . refine Iff.intro ?_ (fun hf => ((hf.comp_mul_right b).comp_mul_left a).const_mul _)
    intro hf
    have hNeg : Not ((d : Complex) ^ (-z) = 0) := by
      rw [Complex.cpow_neg]
      exact inv_ne_zero hD
    have hRestore : (fun g : G => Inv.inv ((d : Complex) ^ (-z)) *
        ((d : Complex) ^ (-z) * h (a * (Inv.inv a * g * Inv.inv b) * b))) = h := by
      funext g
      have hA : a * Inv.inv a = (1 : G) := mul_inv_cancel a
      have hB : Inv.inv b * b = (1 : G) := inv_mul_cancel b
      have hg : a * (Inv.inv a * g * Inv.inv b) * b = g := by
        calc
          _ = (a * Inv.inv a) * g * (Inv.inv b * b) := by simp only [mul_assoc]
          _ = _ := by rw [hA, hB, one_mul, mul_one]
      rw [hg]
      field_simp [hNeg]
    change Integrable h mu
    rw [<- hRestore]
    exact ((hf.comp_mul_right (Inv.inv b)).comp_mul_left (Inv.inv a)).const_mul _
  . rw [integral_const_mul, integral_mul_left_eq_self (fun g : G => h (g * b)) a,
      integral_mul_right_eq_self h b]

/-- The determinant weight from a two-sided translation is an integer
power of the local Euler variable determined by the uniformizer. -/
theorem heckeLocal_twoSidedTranslate_weight
    {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    (pi : Units (p.adicCompletion K))
    (hpi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue)
    (a b : Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))) (s : Complex) :
    ((norm a.val.det * norm b.val.det : Real) : Complex) ^ (-s) =
      ((norm pi.val : Complex) ^ s) ^ heckeLocalDetValueIndex p n (a * b) := by
  let q : Real := dedekindPrimeNorm K p
  let k := heckeLocalDetValueIndex p n (a * b)
  have hq : 0 <= q := Nat.cast_nonneg _
  have hWeight : (norm pi.val : Complex) ^ s = (dedekindPrimeNorm K p : Complex) ^ (-s) := by
    rw [norm_eq_inv_of_valuation_finiteUniformizer p pi.val hpi, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hq s, Complex.cpow_neg, Complex.ofReal_natCast]
  have hDet : norm a.val.det * norm b.val.det = norm (a * b).val.det := by
    rw [show (a * b).val.det = a.val.det * b.val.det from Matrix.det_mul _ _, norm_mul]
  have hArg : (q : Complex).arg = 0 := Complex.arg_ofReal_of_nonneg hq
  have ha : -Real.pi < (k : Real) * (q : Complex).arg := by
    rw [hArg, mul_zero]
    exact neg_lt_zero.mpr Real.pi_pos
  have hb : (k : Real) * (q : Complex).arg <= Real.pi := by
    rw [hArg, mul_zero]
    exact Real.pi_pos.le
  rw [hDet, hWeight, norm_det_eq_primeNorm_zpow p n (a * b), Complex.ofReal_zpow]
  change (((q : Complex) ^ k) ^ (-s)) = _
  rw [<- Complex.cpow_int_mul' ha hb, Complex.cpow_int_mul, Complex.ofReal_natCast]

section CoefficientDenominator

variable {L : Type*} [NormedField L] {n : Nat}
variable [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]

private noncomputable def localZetaIntegrand
    (Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex)
    (s : Complex) (c : Units (Matrix (Fin n) (Fin n) L) -> Complex)
    (g : Units (Matrix (Fin n) (Fin n) L)) : Complex :=
  (norm g.val.det : Complex) ^ s * (Phi g.val * c g)

/-- Every compactly supported locally constant test has an absolutely
convergent right-half-plane certificate using denominator `D` and a
test-dependent nonnegative monomial clearing power. -/
def HasHeckeLocalZetaDenominator
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L))) (Z : Complex -> Complex)
    (D : Polynomial Complex) (c : Units (Matrix (Fin n) (Fin n) L) -> Complex) : Prop :=
  forall (Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex),
    HasCompactSupport (fun X => Phi X) ->
    exists k : Nat, exists sigma : Real, exists A : Polynomial Complex,
      forall s : Complex, sigma < s.re ->
        And (Integrable (localZetaIntegrand Phi s c) mu)
          (Z s ^ k * D.eval (Z s) * integral mu (localZetaIntegrand Phi s c) = A.eval (Z s))

private def heckeLocalZetaDenominatorSubmodule
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L))) (Z : Complex -> Complex)
    (D : Polynomial Complex) : Submodule Complex (Units (Matrix (Fin n) (Fin n) L) -> Complex) where
  carrier := {c | HasHeckeLocalZetaDenominator mu Z D c}
  zero_mem' := by
    change HasHeckeLocalZetaDenominator mu Z D 0
    intro Phi hPhi
    refine Exists.intro 0 (Exists.intro 0 (Exists.intro 0 ?_))
    intro s hs
    have h0 : localZetaIntegrand Phi s 0 = 0 := by
      funext g
      simp [localZetaIntegrand]
    rw [h0]
    exact And.intro (integrable_zero _ _ _) (by simp)
  add_mem' := by
    intro a b ha hb
    change HasHeckeLocalZetaDenominator mu Z D a at ha
    change HasHeckeLocalZetaDenominator mu Z D b at hb
    change HasHeckeLocalZetaDenominator mu Z D (a + b)
    intro Phi hPhi
    choose k sigma A hA using ha Phi hPhi
    choose l tau B hB using hb Phi hPhi
    refine Exists.intro (k + l) (Exists.intro (max sigma tau)
      (Exists.intro (Polynomial.X ^ l * A + Polynomial.X ^ k * B) ?_))
    intro s hs
    have hF : localZetaIntegrand Phi s (a + b) =
        localZetaIntegrand Phi s a + localZetaIntegrand Phi s b := by
      funext g
      simp only [localZetaIntegrand, Pi.add_apply, mul_add]
    have haS := hA s ((le_max_left _ _).trans_lt hs)
    have hbS := hB s ((le_max_right _ _).trans_lt hs)
    refine And.intro (by rw [hF]; exact haS.1.add hbS.1) ?_
    have hI : integral mu (localZetaIntegrand Phi s a + localZetaIntegrand Phi s b) =
        integral mu (localZetaIntegrand Phi s a) + integral mu (localZetaIntegrand Phi s b) :=
      integral_add haS.1 hbS.1
    rw [hF, hI]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [<- haS.2, <- hbS.2, pow_add]
    ring
  smul_mem' := by
    intro k c hc
    change HasHeckeLocalZetaDenominator mu Z D c at hc
    change HasHeckeLocalZetaDenominator mu Z D (HSMul.hSMul k c)
    intro Phi hPhi
    choose e sigma A hA using hc Phi hPhi
    refine Exists.intro e (Exists.intro sigma (Exists.intro (Polynomial.C k * A) ?_))
    intro s hs
    have hF : localZetaIntegrand Phi s (HSMul.hSMul k c) =
        fun g => k * localZetaIntegrand Phi s c g := by
      funext g
      change (norm g.val.det : Complex) ^ s * (Phi g.val * (k * c g)) =
        k * ((norm g.val.det : Complex) ^ s * (Phi g.val * c g))
      ring
    have ha := hA s hs
    rw [hF]
    refine And.intro (ha.1.const_mul k) ?_
    rw [integral_const_mul, Polynomial.eval_mul, Polynomial.eval_C, <- ha.2]
    ring

end CoefficientDenominator

private theorem pow_mul_zpow_eq_pow_toNat
    (w : Complex) (hw : Not (w = 0)) (j : Int) :
    w ^ (-j).toNat * w ^ j = w ^ j.toNat := by
  cases j with
  | ofNat k => simp
  | negSucc k =>
    change w ^ (k + 1) * w ^ Int.negSucc k = w ^ (0 : Nat)
    rw [zpow_negSucc, pow_zero]
    field_simp [pow_ne_zero (k + 1) hw]

/-- A common denominator for one coefficient also works for every finite
linear combination of its left and right translates. -/
theorem hasHeckeLocalZetaDenominator_of_mem_translateSpan
    {K : Type*} [Field K] [NumberField K]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))) [mu.IsHaarMeasure]
    (pi : Units (p.adicCompletion K))
    (hpi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue)
    (D : Polynomial Complex) :
    let L := p.adicCompletion K
    let G := Units (Matrix (Fin n) (Fin n) L)
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let C := valuationIntegralMatrixSubgroup v n
    let Z (s : Complex) := (norm pi.val : Complex) ^ s
    mu (C : Set G) = 1 ->
    forall (c0 c : G -> Complex), HasHeckeLocalZetaDenominator mu Z D c0 ->
      Membership.mem (Submodule.span Complex
        (Set.range (fun pair : Prod G G => fun g : G => c0 (pair.1 * g * pair.2)))) c ->
      HasHeckeLocalZetaDenominator mu Z D c := by
  intro L G v C Z hNorm c0 c hc0 hSpan
  let : mu.IsMulRightInvariant := isMulRightInvariant_heckeLocalMatrixHaar p n mu hNorm
  let W := heckeLocalZetaDenominatorSubmodule mu Z D
  have hLe : Submodule.span Complex
      (Set.range (fun pair : Prod G G => fun g : G => c0 (pair.1 * g * pair.2))) <= W := by
    apply Submodule.span_le.mpr
    intro f hf
    choose ab hab using hf
    rw [<- hab]
    change HasHeckeLocalZetaDenominator mu Z D (fun g : G => c0 (ab.1 * g * ab.2))
    intro Phi hPhi
    choose Psi hPsi using exists_heckeLocalZetaTest_twoSidedTranslate n mu
      ab.1 ab.2 Phi hPhi c0
    choose k sigma A hA using hc0 Psi hPsi.1
    let j := heckeLocalDetValueIndex p n (ab.1 * ab.2)
    refine Exists.intro (k + (-j).toNat) (Exists.intro sigma
      (Exists.intro (Polynomial.X ^ j.toNat * A) ?_))
    intro s hs
    have hSrc := hA s hs
    have hInt : Integrable (localZetaIntegrand Phi s (fun g : G => c0 (ab.1 * g * ab.2))) mu :=
      (hPsi.2 s).1.mpr hSrc.1
    have hEq : integral mu (localZetaIntegrand Phi s (fun g : G => c0 (ab.1 * g * ab.2))) =
        Z s ^ j * integral mu (localZetaIntegrand Psi s c0) := by
      have hChange := (hPsi.2 s).2
      change _ = ((norm ab.1.val.det * norm ab.2.val.det : Real) : Complex) ^ (-s) *
        integral mu (localZetaIntegrand Psi s c0) at hChange
      rw [heckeLocal_twoSidedTranslate_weight p n pi hpi ab.1 ab.2 s] at hChange
      exact hChange
    refine And.intro hInt ?_
    have hZ : Not (Z s = 0) := Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr pi.ne_zero)))
    calc
      _ = Z s ^ (-j).toNat * Z s ^ j *
          (Z s ^ k * D.eval (Z s) * integral mu (localZetaIntegrand Psi s c0)) := by
        rw [hEq, pow_add]
        ring
      _ = _ := by
        rw [pow_mul_zpow_eq_pow_toNat (Z s) hZ j, hSrc.2, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_X]
  exact hLe hSpan


private theorem matrixCoefficient_mem_twoSidedTranslateSpan
    {G V : Type*} [Group G] [AddCommGroup V] [Module Complex V]
    (rho : MonoidHom G (Module.End Complex V))
    (ell0 ell : LinearMap (RingHom.id Complex) V Complex) (u0 u : V)
    (hEll : Membership.mem (Submodule.span Complex
      (Set.range (fun a : G => ell0.comp (rho a)))) ell)
    (hU : Membership.mem (Submodule.span Complex (Set.range (fun b : G => rho b u0))) u) :
    Membership.mem (Submodule.span Complex
      (Set.range (fun ab : Prod G G => fun g : G => ell0 (rho (ab.1 * g * ab.2) u0))))
      (fun g : G => ell (rho g u)) := by
  let Y := Submodule.span Complex
    (Set.range (fun ab : Prod G G => fun g : G => ell0 (rho (ab.1 * g * ab.2) u0)))
  let F (v : V) : LinearMap (RingHom.id Complex) (LinearMap (RingHom.id Complex) V Complex)
      (G -> Complex) :=
    { toFun := fun d g => d (rho g v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let E (d : LinearMap (RingHom.id Complex) V Complex) :
      LinearMap (RingHom.id Complex) V (G -> Complex) :=
    { toFun := fun v g => d (rho g v)
      map_add' := fun v w => by
        funext g
        change d (rho g (v + w)) = d (rho g v) + d (rho g w)
        rw [map_add, map_add]
      map_smul' := fun k v => by
        funext g
        change d (rho g (HSMul.hSMul k v)) = HSMul.hSMul k (d (rho g v))
        rw [LinearMap.map_smul, LinearMap.map_smul] }
  have hCore (b : G) : Submodule.span Complex (Set.range (fun a : G => ell0.comp (rho a))) <=
      Submodule.comap (F (rho b u0)) Y := by
    apply Submodule.span_le.mpr
    intro d hd
    choose a ha using hd
    rw [<- ha]
    change Membership.mem Y (fun g : G => ell0 (rho a (rho g (rho b u0))))
    apply Submodule.subset_span
    refine Exists.intro (Prod.mk a b) ?_
    funext g
    change ell0 (rho (a * g * b) u0) = ell0 (rho a (rho g (rho b u0)))
    simp only [mul_assoc, map_mul, Module.End.mul_apply]
  have hExtend : Submodule.span Complex (Set.range (fun b : G => rho b u0)) <=
      Submodule.comap (E ell) Y := by
    apply Submodule.span_le.mpr
    intro v hv
    choose b hb using hv
    rw [<- hb]
    exact hCore b hEll
  exact hExtend hU

/-- The reduced denominator obtained from a normalized congruence-fixed
coefficient works for every coefficient formed from the vector orbit span
and the dual orbit span of its two defining entries. -/
theorem heckeLocal_matrixCoefficients_commonReducedDenominator_of_orbitSpans
    {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module Complex V]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (n R : Nat) (hR : 0 < R) (pi : Units (p.adicCompletion K))
    (hPi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue)
    (hLt : Valued.v (pi : p.adicCompletion K) < 1) (hp : norm pi.val < 1)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))) [mu.IsHaarMeasure]
    (rho : MonoidHom (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))) (Module.End Complex V))
    (P : HeckeLocalSubgroupAverage rho
      (valuationPrincipalCongruenceSubgroup Valued.v n (Valued.v (pi : p.adicCompletion K) ^ R)))
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (ell0 : LinearMap (RingHom.id Complex) V Complex) (u0 : V) :
    let L := p.adicCompletion K
    let G := Units (Matrix (Fin n) (Fin n) L)
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let C := valuationIntegralMatrixSubgroup v n
    let H := valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R)
    let Z (s : Complex) := (norm pi.val : Complex) ^ s
    (forall (h : H) (x : V), ell0 (rho h.val x) = ell0 x) ->
    (forall h : H, rho h.val u0 = u0) ->
    mu (C : Set G) = 1 ->
    ell0 u0 = 1 ->
    exists D : Polynomial Complex, And (D.eval 0 = 1)
      (forall (ell : LinearMap (RingHom.id Complex) V Complex) (u : V),
        Membership.mem (Submodule.span Complex (Set.range (fun a : G => ell0.comp (rho a)))) ell ->
        Membership.mem (Submodule.span Complex (Set.range (fun b : G => rho b u0))) u ->
        HasHeckeLocalZetaDenominator mu Z D (fun g : G => ell (rho g u))) := by
  intro L G v C H Z hEll0 hU0 hNorm hOne
  choose B D hBD using heckeLocal_compactlySupportedTest_reducedDenominator p n R hR
    pi hPi hLt hp mu rho P ell0 u0 hEll0 hU0 hNorm hOne
  have hSeed : HasHeckeLocalZetaDenominator mu Z D (fun g : G => ell0 (rho g u0)) :=
    hBD.2.2.2.2
  refine Exists.intro D (And.intro hBD.2.1 ?_)
  intro ell u hEll hU
  exact hasHeckeLocalZetaDenominator_of_mem_translateSpan p n mu pi hPi D hNorm
    (fun g : G => ell0 (rho g u0)) (fun g : G => ell (rho g u)) hSeed
    (matrixCoefficient_mem_twoSidedTranslateSpan rho ell0 ell u0 u hEll hU)
end Robin1984.GRH
