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
Comparing the numerator ideal with any competing certificate proves
leastness by divisibility for the normalized polynomial.
-/

set_option autoImplicit false

open Filter IsDedekindDomain MeasureTheory NumberField Topology

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

private theorem polynomial_eq_of_eval_cpow_on_rightHalfPlane
    {q : Real} (hq0 : 0 < q) (hq1 : q < 1) (sigma : Real)
    (A B : Polynomial Complex)
    (h : forall s : Complex, sigma < s.re ->
      A.eval ((q : Complex) ^ s) = B.eval ((q : Complex) ^ s)) :
    A = B := by
  classical
  let P := A - B
  by_contra! hAB
  have hP : Not (P = 0) := sub_ne_zero.mpr hAB
  let t (m : Nat) : Real := sigma + 1 + (m : Real)
  let z (m : Nat) : Complex := (q : Complex) ^ (t m : Complex)
  have hEval (m : Nat) : z m = (Real.exp (Real.log q * t m) : Complex) := by
    change (q : Complex) ^ (t m : Complex) = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq0.ne'),
      <- Complex.ofReal_log hq0.le, <- Complex.ofReal_mul, <- Complex.ofReal_exp]
  have hInj : Function.Injective z := by
    intro a b hab
    rw [hEval, hEval] at hab
    have he := Real.exp_injective (Complex.ofReal_injective hab)
    have hProd : Real.log q * (t a - t b) = 0 := by rw [mul_sub, he, sub_self]
    have ht : t a = t b :=
      sub_eq_zero.mp ((mul_eq_zero.mp hProd).resolve_left (Real.log_neg hq0 hq1).ne)
    have hc : (a : Real) = (b : Real) := by
      change sigma + 1 + (a : Real) = sigma + 1 + (b : Real) at ht
      linarith
    exact_mod_cast hc
  have hSub : Set.Subset (Set.range z) (P.roots.toFinset : Set Complex) := by
    intro x hx
    choose m hm using hx
    rw [<- hm]
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hP).mpr
    change (A - B).eval (z m) = 0
    have hRe : sigma < ((t m : Real) : Complex).re := by
      rw [Complex.ofReal_re]
      change sigma < sigma + 1 + (m : Real)
      have hm : 0 <= (m : Real) := Nat.cast_nonneg m
      linarith
    rw [Polynomial.eval_sub, h (t m : Complex) hRe, sub_self]
  exact (Set.infinite_range_of_injective hInj).not_finite
    (P.roots.toFinset.finite_toSet.subset hSub)

private theorem dvd_of_dvd_X_pow_mul_of_eval_zero_one
    (D P : Polynomial Complex) (hD : D.eval 0 = 1) (k : Nat)
    (h : Dvd.dvd D (Polynomial.X ^ k * P)) : Dvd.dvd D P := by
  have hX : Dvd.dvd Polynomial.X (D - 1) := by
    have h0 : D.coeff 0 = 1 := (Polynomial.coeff_zero_eq_eval_zero D).trans hD
    exact Polynomial.X_dvd_iff.mpr (by simp [h0])
  choose T hT using hX
  have hCoprime : IsCoprime D Polynomial.X := by
    refine Exists.intro 1 (Exists.intro (-T) ?_)
    rw [one_mul, neg_mul, mul_comm T Polynomial.X, <- hT]
    ring
  have hc : IsCoprime D (Polynomial.X ^ k) := hCoprime.pow_right
  exact hc.dvd_of_dvd_mul_left h


private theorem leastDenominator_dvd_of_numeratorIdeal
    {Test : Type*} {q : Real} (hq0 : 0 < q) (hq1 : q < 1)
    (F : Test -> Complex -> Complex) (Admissible : Test -> Prop) (Converges : Test -> Complex -> Prop)
    (Q B D E : Polynomial Complex) (hQ : Q.eval 0 = 1) (hB : B.eval 0 = 1)
    (hFactor : Q = B * D) :
    let Z (s : Complex) := (q : Complex) ^ s
    let S : Set (Polynomial Complex) := {N |
      exists (test : Test) (k : Nat) (sigma : Real), And (Admissible test)
        (forall s : Complex, sigma < s.re ->
          And (Converges test s)
            (Z s ^ k * Q.eval (Z s) * F test s = N.eval (Z s)))}
    Ideal.span S = Ideal.span (Set.singleton B) ->
    (forall test : Test, Admissible test -> exists (l : Nat) (tau : Real) (A : Polynomial Complex),
      forall s : Complex, tau < s.re ->
      And (Converges test s) (Z s ^ l * E.eval (Z s) * F test s = A.eval (Z s))) ->
    Dvd.dvd D E := by
  intro Z S hSpan hTest
  have hEach (N : Polynomial Complex) (hN : Membership.mem S N) : Dvd.dvd Q (E * N) := by
    choose test k sigma hSig using hN
    choose l tau A hTau using hTest test hSig.1
    have hCross : Polynomial.X ^ l * (E * N) = Polynomial.X ^ k * Q * A := by
      apply polynomial_eq_of_eval_cpow_on_rightHalfPlane hq0 hq1 (max sigma tau)
      intro s hs
      have hsSigma := (le_max_left sigma tau).trans_lt hs
      have hsTau := (le_max_right sigma tau).trans_lt hs
      change (Polynomial.X ^ l * (E * N)).eval (Z s) =
        (Polynomial.X ^ k * Q * A).eval (Z s)
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      rw [<- (hSig.2 s hsSigma).2, <- (hTau s hsTau).2]
      ring
    have hQDiv : Dvd.dvd Q (Polynomial.X ^ l * (E * N)) := by
      rw [hCross]
      exact Dvd.intro (Polynomial.X ^ k * A) (by ring)
    exact dvd_of_dvd_X_pow_mul_of_eval_zero_one Q (E * N) hQ l hQDiv
  let f : LinearMap (RingHom.id (Polynomial Complex)) (Polynomial Complex) (Polynomial Complex) :=
    { toFun := fun N => E * N
      map_add' := fun N M => mul_add E N M
      map_smul' := fun a N => by
        change E * (a * N) = a * (E * N)
        ring }
  let J : Ideal (Polynomial Complex) := Submodule.comap f (Ideal.span (Set.singleton Q))
  have hLe : Ideal.span S <= J := by
    apply Ideal.span_le.mpr
    intro N hN
    change Membership.mem (Ideal.span (Set.singleton Q)) (E * N)
    exact Ideal.mem_span_singleton.mpr (hEach N hN)
  have hBMem : Membership.mem (Ideal.span S) B := by
    rw [hSpan]
    exact Ideal.subset_span (Set.mem_singleton B)
  have hDiv : Dvd.dvd Q (E * B) := Ideal.mem_span_singleton.mp (hLe hBMem)
  choose C hC using hDiv
  have hB0 : Not (B = 0) := by
    intro hb
    rw [hb, Polynomial.eval_zero] at hB
    exact zero_ne_one hB
  have hProd : B * (E - D * C) = 0 := by
    rw [mul_sub, mul_comm B E, hC, hFactor]
    ring
  exact Dvd.intro C (sub_eq_zero.mp ((mul_eq_zero.mp hProd).resolve_left hB0)).symm

/-- The reduced denominator works throughout the two orbit spans and
divides every common denominator for the normalized seed coefficient. -/
theorem heckeLocal_matrixCoefficients_leastDenominator_of_orbitSpans
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
      (And (forall (ell : LinearMap (RingHom.id Complex) V Complex) (u : V),
        Membership.mem (Submodule.span Complex (Set.range (fun a : G => ell0.comp (rho a)))) ell ->
        Membership.mem (Submodule.span Complex (Set.range (fun b : G => rho b u0))) u ->
        HasHeckeLocalZetaDenominator mu Z D (fun g : G => ell (rho g u)))
        (forall E : Polynomial Complex,
          HasHeckeLocalZetaDenominator mu Z E (fun g : G => ell0 (rho g u0)) ->
          Dvd.dvd D E)) := by
  intro L G v C H Z hEll0 hU0 hNorm hOne
  choose B D hBD using heckeLocal_compactlySupportedTest_reducedDenominator p n R hR
    pi hPi hLt hp mu rho P ell0 u0 hEll0 hU0 hNorm hOne
  have hSeed : HasHeckeLocalZetaDenominator mu Z D (fun g : G => ell0 (rho g u0)) :=
    hBD.2.2.2.2
  refine Exists.intro D (And.intro hBD.2.1 (And.intro ?_ ?_))
  . intro ell u hEll hU
    exact hasHeckeLocalZetaDenominator_of_mem_translateSpan p n mu pi hPi D hNorm
      (fun g : G => ell0 (rho g u0)) (fun g : G => ell (rho g u)) hSeed
      (matrixCoefficient_mem_twoSidedTranslateSpan rho ell0 ell u0 u hEll hU)
  . intro E hE
    let hRad : v pi.val ^ R < 1 := (pow_lt_one_iff_of_nonneg (zero_le : 0 <= v pi.val) hR.ne').mpr hLt
    let alpha (i : Fin n) : Complex :=
      ((Inv.inv (norm pi.val) : Real) : Complex) ^ ((i.val + 1) * (n - (i.val + 1)))
    let Q := valuationUniformizerConeDenominator v n (v pi.val ^ R) hRad rho P pi hLt.le alpha
    have hF : Q = B * D := hBD.2.2.1
    have hQ0 : Q.eval 0 = 1 := by
      rw [hF, Polynomial.eval_mul, hBD.1, hBD.2.1, one_mul]
    let Test := LocallyConstant (Matrix (Fin n) (Fin n) L) Complex
    let f (Phi : Test) (s : Complex) (g : G) :=
      (norm g.val.det : Complex) ^ s * (Phi g.val * ell0 (rho g u0))
    exact leastDenominator_dvd_of_numeratorIdeal
      (norm_pos_iff.mpr pi.ne_zero) hp
      (fun Phi : Test => fun s => integral mu (f Phi s))
      (fun Phi : Test => HasCompactSupport (fun X => Phi X))
      (fun Phi : Test => fun s => Integrable (f Phi s) mu)
      Q B D E hQ0 hBD.1 hBD.2.2.1 hBD.2.2.2.1 hE

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
  choose D hD using heckeLocal_matrixCoefficients_leastDenominator_of_orbitSpans
    p n R hR pi hPi hLt hp mu rho P ell0 u0 hEll0 hU0 hNorm hOne
  exact Exists.intro D (And.intro hD.1 hD.2.1)
section

variable {G V : Type*} [Group G]
variable [AddCommGroup V] [Module Complex V]

local notation "DualV" => LinearMap (RingHom.id Complex) V Complex

private theorem dualOrbitSpan_separates
    (rho : MonoidHom G (Module.End Complex V))
    (ell0 : DualV) (u0 : V) (hOne : ell0 u0 = 1)
    (hIrred : forall x : V, Not (x = 0) ->
      Submodule.span Complex (Set.range (fun g : G => rho g x)) = Top.top) :
    let W := Submodule.span Complex (Set.range (fun a : G => ell0.comp (rho a)))
    forall x : V, (forall w : W, w.val x = 0) -> x = 0 := by
  intro W x hAnn
  by_contra! hx
  have hLe : Submodule.span Complex (Set.range (fun g : G => rho g x)) <=
      LinearMap.ker ell0 := by
    apply Submodule.span_le.mpr
    intro y hy
    choose g hg using hy
    have hOrbit : Membership.mem W (ell0.comp (rho g)) :=
      Submodule.subset_span (Exists.intro g rfl)
    rw [<- hg]
    exact hAnn (Subtype.mk _ hOrbit)
  have hu : Membership.mem (Submodule.span Complex (Set.range (fun g : G => rho g x))) u0 := by
    rw [hIrred x hx]
    exact Submodule.mem_top
  have hh : ell0 u0 = 0 := hLe hu
  exact one_ne_zero (hOne.symm.trans hh)

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem exists_dualOrbitAverage_pairing
    (rho : MonoidHom G (Module.End Complex V)) (ell0 : DualV)
    (hSeed : Membership.mem (heckeLocalSmoothDual rho) ell0)
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (P : HeckeLocalSubgroupAverage rho K) :
    let W := Submodule.span Complex (Set.range (fun a : G => ell0.comp (rho a)))
    exists T : Module.End Complex W, forall (w : W) (v : V),
      (T w).val v = w.val (P.proj v) := by
  intro W
  have hWSmooth : W <= heckeLocalSmoothDual rho := by
    apply Submodule.span_le.mpr
    intro w hw
    choose a ha using hw
    rw [<- ha]
    exact heckeLocalSmoothDual_comp_mem rho a ell0 hSeed
  let D (a : G) : Module.End Complex DualV :=
    { toFun := fun ell => ell.comp (rho (Inv.inv a))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hStable (a : G) : W <= Submodule.comap (D a) W := by
    apply Submodule.span_le.mpr
    intro ell hell
    choose b hb using hell
    rw [<- hb]
    change Membership.mem W ((ell0.comp (rho b)).comp (rho (Inv.inv a)))
    apply Submodule.subset_span
    refine Exists.intro (b * Inv.inv a) ?_
    ext v
    change ell0 (rho (b * Inv.inv a) v) = ell0 (rho b (rho (Inv.inv a) v))
    rw [map_mul, Module.End.mul_apply]
  let A (a : G) : Module.End Complex W :=
    { toFun := fun ell => Subtype.mk (D a ell.val) (hStable a ell.property)
      map_add' := fun ell eta => by
        apply Subtype.ext
        exact (D a).map_add ell.val eta.val
      map_smul' := fun k ell => by
        apply Subtype.ext
        exact (D a).map_smul k ell.val }
  let r : MonoidHom G (Module.End Complex W) :=
    { toFun := A
      map_one' := by
        ext ell v
        change ell.val (rho (Inv.inv (1 : G)) v) = ell.val v
        rw [inv_one, map_one, Module.End.one_apply]
      map_mul' := fun a b => by
        ext ell v
        change ell.val (rho (Inv.inv (a * b)) v) =
          ell.val (rho (Inv.inv b) (rho (Inv.inv a) v))
        rw [mul_inv_rev, map_mul, Module.End.mul_apply] }
  have hSmooth (ell : W) : Filter.Eventually (fun g : G => r g ell = ell) (nhds 1) := by
    have hb : Filter.Eventually (fun g : G => ell.val.comp (rho g) = ell.val) (nhds 1) :=
      hWSmooth ell.property
    have hc : Filter.Tendsto (fun g : G => Inv.inv g) (nhds (1 : G)) (nhds 1) := by
      simpa only [inv_one] using (continuous_inv.tendsto (1 : G))
    refine (hc.eventually hb).mono ?_
    intro g hg
    exact Subtype.ext hg
  let Q := HeckeLocalSubgroupAverage.ofCompactSmooth r K hK hSmooth
  refine Exists.intro Q.proj ?_
  intro w v
  have hInv (k : K) (x : V) : (Q.proj w).val (rho k.val x) = (Q.proj w).val x := by
    have h := congrArg (fun q : W => q.val x) (Q.fixed (Inv.inv k) w)
    change (Q.proj w).val (rho (Inv.inv (Inv.inv k.val)) x) = (Q.proj w).val x at h
    simpa only [inv_inv] using h
  let e : LinearMap (RingHom.id Complex) W Complex :=
    { toFun := fun q => q.val (P.proj v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hEval (k : K) (q : W) : e (r k.val q) = e q := by
    change q.val (rho (Inv.inv k.val) (P.proj v)) = q.val (P.proj v)
    exact congrArg q.val (P.fixed (Inv.inv k) v)
  calc
    (Q.proj w).val v = (Q.proj w).val (P.proj v) :=
      (P.pairing_proj (Q.proj w).val hInv v).symm
    _ = w.val (P.proj v) := Q.pairing_proj e hEval w


private theorem surjective_of_separating_finiteDimensional
    {X W : Type*} [AddCommGroup X] [Module Complex X] [FiniteDimensional Complex X]
    [AddCommGroup W] [Module Complex W]
    (f : LinearMap (RingHom.id Complex) W (Module.Dual Complex X))
    (hSep : forall x : X, (forall w : W, f w x = 0) -> x = 0) :
    Function.Surjective f := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro phi hPhi
  change f.dualMap phi = 0 at hPhi
  change phi = 0
  let e := Module.evalEquiv Complex X
  choose x hx using e.surjective phi
  have hx0 : x = 0 := by
    apply hSep
    intro w
    have hv : phi (f w) = 0 := DFunLike.congr_fun hPhi w
    rw [<- hx] at hv
    exact hv
  rw [<- hx, hx0, e.map_zero]

private theorem mem_dualOrbitSpan_of_invariant
    (rho : MonoidHom G (Module.End Complex V))
    (ell0 d : DualV) (u0 : V) (hOne : ell0 u0 = 1)
    (hSeed : Membership.mem (heckeLocalSmoothDual rho) ell0)
    (hIrred : forall x : V, Not (x = 0) ->
      Submodule.span Complex (Set.range (fun g : G => rho g x)) = Top.top)
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (P : HeckeLocalSubgroupAverage rho K)
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (hD : forall (k : K) (v : V), d (rho k.val v) = d v) :
    Membership.mem (Submodule.span Complex (Set.range (fun a : G => ell0.comp (rho a)))) d := by
  let W := Submodule.span Complex (Set.range (fun a : G => ell0.comp (rho a)))
  let X := LinearMap.range P.proj
  let R : LinearMap (RingHom.id Complex) W (Module.Dual Complex X) :=
    { toFun := fun w => w.val.domRestrict X
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hSep (x : X) (hx : forall w : W, R w x = 0) : x = 0 := by
    apply Subtype.ext
    change x.val = 0
    apply dualOrbitSpan_separates rho ell0 u0 hOne hIrred x.val
    exact hx
  have hR := surjective_of_separating_finiteDimensional R hSep
  choose w hw using hR (d.domRestrict X)
  choose T hT using exists_dualOrbitAverage_pairing rho ell0 hSeed K hK P
  have hEq : (T w).val = d := by
    ext v
    let xv : X := Subtype.mk (P.proj v) (LinearMap.mem_range.mpr (Exists.intro v rfl))
    have hVal : w.val (P.proj v) = d (P.proj v) := DFunLike.congr_fun hw xv
    calc
      (T w).val v = w.val (P.proj v) := hT w v
      _ = d (P.proj v) := hVal
      _ = d v := P.pairing_proj d hD v
  rw [<- hEq]
  exact (T w).property
end


section FinitePlace

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module Complex V]
variable (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
variable (pi : Units (p.adicCompletion K))

local notation "L" => p.adicCompletion K
local notation "G" => Units (Matrix (Fin n) (Fin n) L)
local notation "DualV" => LinearMap (RingHom.id Complex) V Complex
local notation "v" => (Valued.v : Valuation L (WithZero (Multiplicative Int)))

private theorem isCompact_finitePlacePrincipalCongruence (R : Nat) :
    IsCompact (valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R) : Set G) := by
  have hC : IsCompact (Valuation.integer v : Set L) :=
    isCompact_iff_compactSpace.mpr (compactSpace_heckeLocalIntegers p)
  have hPi : v (pi ^ R).val = v pi.val ^ R := Valuation.map_pow v _ _
  rw [<- hPi]
  exact isCompact_valuationPrincipalCongruenceSubgroup v n (pi ^ R) hC

/-- The orbit span of a nonzero smooth dual functional contains the
entire smooth dual for an irreducible admissible finite-place representation.
A normalized value on one vector supplies the nonzero seed. -/
theorem mem_dualOrbitSpan_of_smooth_admissible
    (hp : norm pi.val < 1) (rho : MonoidHom G (Module.End Complex V))
    (ell0 d : DualV) (u0 : V) (hOne : ell0 u0 = 1)
    (hSeed : Membership.mem (heckeLocalSmoothDual rho) ell0)
    (hD : Membership.mem (heckeLocalSmoothDual rho) d)
    (hIrred : forall x : V, Not (x = 0) ->
      Submodule.span Complex (Set.range (fun g : G => rho g x)) = Top.top)
    (hSmooth : forall x : V, Filter.Eventually (fun g : G => rho g x = x) (nhds 1))
    (hAdmissible : forall R : Nat, FiniteDimensional Complex (heckeLocalFixedSubmodule rho
      (valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R)))) :
    Membership.mem (Submodule.span Complex (Set.range (fun a : G => ell0.comp (rho a)))) d := by
  let U : Set G := {g | d.comp (rho g) = d}
  have hU : Membership.mem (nhds 1) U := hD
  choose R hR using exists_principalCongruence_in_neighborhood p n 0 pi hp U hU
  let H := valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R)
  have hHC : IsCompact (H : Set G) := isCompact_finitePlacePrincipalCongruence p n pi R
  let P := HeckeLocalSubgroupAverage.ofCompactSmooth rho H hHC hSmooth
  let : FiniteDimensional Complex (LinearMap.range P.proj) := by
    rw [range_average_eq_fixedSubmodule rho H P]
    exact hAdmissible R
  have hInv (k : H) (x : V) : d (rho k.val x) = d x :=
    DFunLike.congr_fun (hR.2.2 k.property) x
  exact mem_dualOrbitSpan_of_invariant rho ell0 d u0 hOne hSeed hIrred H hHC P hInv

private theorem exists_localZeta_normalizingFunctional (u : V) (hu : Not (u = 0)) :
    exists ell : DualV, ell u = 1 := by
  let f : LinearMap (RingHom.id Complex) Complex V :=
    { toFun := fun z => HSMul.hSMul z u
      map_add' := fun a b => add_smul a b u
      map_smul' := fun a b => mul_smul a b u }
  have hInj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    refine le_antisymm ?_ bot_le
    intro z hz
    change HSMul.hSMul z u = 0 at hz
    change z = 0
    exact (smul_eq_zero.mp hz).resolve_right hu
  have hSurj := LinearMap.dualMap_surjective_iff.mpr hInj
  choose ell hell using hSurj (LinearMap.id : Module.Dual Complex Complex)
  have hEval : ell (HSMul.hSMul (1 : Complex) u) = 1 := DFunLike.congr_fun hell 1
  rw [one_smul] at hEval
  exact Exists.intro ell hEval

/-- For a smooth irreducible admissible finite-place representation, the
local zeta integrals of all tests and smooth coefficients share a
denominator with constant term one. It divides every polynomial with
the same common-denominator property. -/
theorem heckeLocal_smoothIrreducible_leastDenominator
    [Nontrivial V]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [MeasurableSpace L] [BorelSpace L] [MeasurableSpace G] [BorelSpace G]
    (hPi : v pi.val = finiteUniformizerValue) (hLt : v pi.val < 1) (hp : norm pi.val < 1)
    (mu : Measure G) [mu.IsHaarMeasure]
    (rho : MonoidHom G (Module.End Complex V))
    (hIrred : forall x : V, Not (x = 0) ->
      Submodule.span Complex (Set.range (fun g : G => rho g x)) = Top.top)
    (hSmooth : forall x : V, Filter.Eventually (fun g : G => rho g x = x) (nhds 1))
    (hAdmissible : forall R : Nat, FiniteDimensional Complex (heckeLocalFixedSubmodule rho
      (valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R))))
    (hNorm : mu ((valuationIntegralMatrixSubgroup v n : Subgroup G) : Set G) = 1) :
    let Z (s : Complex) := (norm pi.val : Complex) ^ s
    exists D : Polynomial Complex, And (D.eval 0 = 1)
      (And (forall (ell : DualV) (u : V),
        Membership.mem (heckeLocalSmoothDual rho) ell ->
        HasHeckeLocalZetaDenominator mu Z D (fun g : G => ell (rho g u)))
        (forall E : Polynomial Complex, (forall (ell : DualV) (u : V),
        Membership.mem (heckeLocalSmoothDual rho) ell ->
        HasHeckeLocalZetaDenominator mu Z E (fun g : G => ell (rho g u))) -> Dvd.dvd D E)) := by
  intro Z
  choose u0 hu0 using exists_ne (0 : V)
  let U : Set G := {g | rho g u0 = u0}
  have hU : Membership.mem (nhds 1) U := hSmooth u0
  choose R hR using exists_principalCongruence_in_neighborhood p n 0 pi hp U hU
  let H := valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R)
  have hHC : IsCompact (H : Set G) := isCompact_finitePlacePrincipalCongruence p n pi R
  let P := HeckeLocalSubgroupAverage.ofCompactSmooth rho H hHC hSmooth
  let : FiniteDimensional Complex (LinearMap.range P.proj) := by
    rw [range_average_eq_fixedSubmodule rho H P]
    exact hAdmissible R
  choose d0 hd0 using exists_localZeta_normalizingFunctional u0 hu0
  let ell0 := d0.comp P.proj
  have hFixU (k : H) : rho k.val u0 = u0 := hR.2.2 k.property
  have hFixEll (k : H) (x : V) : ell0 (rho k.val x) = ell0 x :=
    congrArg (fun y : V => d0 y) (P.left_invariant k x)
  have hOne : ell0 u0 = 1 := by
    change d0 (P.proj u0) = 1
    rw [P.proj_eq_of_fixed u0 hFixU, hd0]
  have hHP : v (pi ^ R).val = v pi.val ^ R := Valuation.map_pow v _ _
  have hHOpen : IsOpen (H : Set G) := by
    change IsOpen (valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R) : Set G)
    rw [<- hHP]
    exact isOpen_valuationPrincipalCongruenceSubgroup v n (pi ^ R)
      (Valued.isOpen_valuationSubring L)
  have hSeed : Membership.mem (heckeLocalSmoothDual rho) ell0 := by
    change Filter.Eventually (fun g : G => ell0.comp (rho g) = ell0) (nhds 1)
    refine Filter.Eventually.mono (hHOpen.mem_nhds H.one_mem) ?_
    intro g hg
    ext x
    exact hFixEll (Subtype.mk g hg) x
  choose D hD using heckeLocal_matrixCoefficients_leastDenominator_of_orbitSpans
    p n R hR.1 pi hPi hLt hp mu rho P ell0 u0 hFixEll hFixU hNorm hOne
  refine Exists.intro D (And.intro hD.1 (And.intro ?_ ?_))
  . intro ell u hell
    have hEll := mem_dualOrbitSpan_of_smooth_admissible p n pi hp rho ell0 ell u0
      hOne hSeed hell hIrred hSmooth hAdmissible
    have hVec : Membership.mem (Submodule.span Complex (Set.range (fun b : G => rho b u0))) u := by
      rw [hIrred u0 hu0]
      exact Submodule.mem_top
    exact hD.2.1 ell u hEll hVec
  . intro E hE
    exact hD.2.2 E (hE ell0 u0 hSeed)

/-- A smooth irreducible admissible finite-place representation has one
normalized polynomial denominator for the local zeta integrals of all of its
smooth matrix coefficients and compactly supported locally constant tests. -/
theorem heckeLocal_smoothIrreducible_commonDenominator
    [Nontrivial V]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [MeasurableSpace L] [BorelSpace L] [MeasurableSpace G] [BorelSpace G]
    (hPi : v pi.val = finiteUniformizerValue) (hLt : v pi.val < 1) (hp : norm pi.val < 1)
    (mu : Measure G) [mu.IsHaarMeasure]
    (rho : MonoidHom G (Module.End Complex V))
    (hIrred : forall x : V, Not (x = 0) ->
      Submodule.span Complex (Set.range (fun g : G => rho g x)) = Top.top)
    (hSmooth : forall x : V, Filter.Eventually (fun g : G => rho g x = x) (nhds 1))
    (hAdmissible : forall R : Nat, FiniteDimensional Complex (heckeLocalFixedSubmodule rho
      (valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R))))
    (hNorm : mu ((valuationIntegralMatrixSubgroup v n : Subgroup G) : Set G) = 1) :
    let Z (s : Complex) := (norm pi.val : Complex) ^ s
    exists D : Polynomial Complex, And (D.eval 0 = 1)
      (forall (ell : DualV) (u : V),
        Membership.mem (heckeLocalSmoothDual rho) ell ->
        HasHeckeLocalZetaDenominator mu Z D (fun g : G => ell (rho g u))) := by
  intro Z
  choose D hD using heckeLocal_smoothIrreducible_leastDenominator
    p n pi hPi hLt hp mu rho hIrred hSmooth hAdmissible hNorm
  exact Exists.intro D (And.intro hD.1 hD.2.1)

end FinitePlace

end Robin1984.GRH
