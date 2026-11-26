import Robin1984.GRH.GodementJacquetCartanVolume
import Robin1984.GRH.GodementJacquetUnramifiedMeasure

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Reduction modulo the maximal ideal, normalized additive local Haar measure, and finite product measures.
- Formalization note: Evaluates the additive mass of the finite-place Cartan stabilizer by its admissible invertible residue matrices and uniformizer-power rectangles.
- PROVENANCE-END
-/

/-!
# Additive volume of Cartan stabilizers

A stabilizer residue class is determined by an invertible residue matrix
with zeros at the required upper entries. Each class is a rectangle of
uniformizer-power balls, and all admissible classes have the same mass.
-/

set_option autoImplicit false

namespace Robin1984.GRH

private theorem valuation_integer_residue_eq_zero_iff
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (a : v.integer) :
    IsLocalRing.residue v.integer a = 0 <-> v (a : F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  change Not (IsUnit a) <-> _
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

/-- An integral matrix has determinant of valuation one exactly when its
reduction over the residue field is invertible. -/
theorem valuation_det_eq_one_iff_residue_matrix_isUnit
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (A : Matrix (Fin n) (Fin n) v.integer) :
    v (A.det : F) = 1 <->
      IsUnit ((IsLocalRing.residue v.integer).mapMatrix A) := by
  rw [Matrix.isUnit_iff_isUnit_det, <- RingHom.map_det, isUnit_iff_ne_zero]
  constructor
  . intro hv hr
    have hLt := (valuation_integer_residue_eq_zero_iff v A.det).mp hr
    exact (not_lt_of_ge hv.ge) hLt
  . intro h
    exact le_antisymm A.det.property (le_of_not_gt
      (fun hLt => h ((valuation_integer_residue_eq_zero_iff v A.det).mpr hLt)))

open IsDedekindDomain MeasureTheory NumberField

/-- The size of the finite-completion residue field is the norm of the
corresponding prime ideal. -/
theorem natCard_heckeLocalResidueField_eq_absNorm
    {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    Nat.card (IsLocalRing.ResidueField (p.adicCompletionIntegers K)) = Ideal.absNorm p.asIdeal := by
  rw [Ideal.absNorm_apply]
  exact Nat.card_congr (heckeLocalResidueEquiv p).toEquiv.symm

private theorem valuation_le_unit_iff_inv_mul_le_one
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (c : Units F) (x : F) :
    v x <= v c.val <-> v ((Inv.inv c).val * x) <= 1 := by
  have hProd : v c.val * v (Inv.inv c).val = 1 := by
    rw [<- v.map_mul, show c.val * (Inv.inv c).val = 1 from c.val_inv, v.map_one]
  have hRev : v (Inv.inv c).val * v c.val = 1 := (mul_comm _ _).trans hProd
  rw [v.map_mul]
  constructor
  . intro h
    exact (mul_le_mul' (le_refl _) h).trans_eq hRev
  . intro h
    have h' := mul_le_mul' (le_refl (v c.val)) h
    simpa only [<- mul_assoc, hProd, one_mul, mul_one] using h'

private theorem cartanPower_le_base_of_pos
    {W : Type*} [LinearOrderedCommGroupWithZero W]
    (u : W) (hu : u <= 1) (m : Nat) (hm : 0 < m) :
    u ^ m <= u := by
  have hPow (k : Nat) : u ^ k <= 1 := by
    induction k with
    | zero => rw [pow_zero]
    | succ k hk =>
      rw [pow_succ]
      exact (mul_le_mul' hk hu).trans_eq (mul_one 1)
  cases m with
  | zero => exact False.elim ((lt_irrefl 0) hm)
  | succ k =>
    rw [pow_succ]
    exact (mul_le_mul' (hPow k) (le_refl _)).trans_eq (one_mul _)

/-- The additive mass of a local uniformizer-power ball is the corresponding
power of the normalized absolute value. -/
theorem heckeLocalAdditiveMeasure_uniformizerPowerBall
    {K : Type*} [Field K] [NumberField K]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (pi : Units (p.adicCompletion K)) (m : Nat) :
    heckeLocalAdditiveMeasure p (Set.ofPred (fun x : p.adicCompletion K =>
      (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) x <=
        Valued.v pi.val ^ m)) = (ENNReal.ofReal (norm pi.val)) ^ m := by
  let L := p.adicCompletion K
  let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
  let c := pi ^ m
  let a := Inv.inv c
  have hPow : v c.val = v pi.val ^ m := by
    change v (pi.val ^ m) = _
    exact v.map_pow _ _
  have hEq : Set.ofPred (fun x : L => v x <= v pi.val ^ m) =
      Set.ofPred (fun x : L => Membership.mem (p.adicCompletionIntegers K) (a.val * x)) := by
    ext x
    change (v x <= v pi.val ^ m) <-> v (a.val * x) <= 1
    rw [<- hPow]
    exact valuation_le_unit_iff_inv_mul_le_one v c x
  change heckeLocalAdditiveMeasure p (Set.ofPred (fun x : L => v x <= v pi.val ^ m)) = _
  rw [hEq, heckeLocalAdditiveMeasure_scaledIntegral p a]
  have hNorm : Inv.inv (norm a.val) = norm c.val := by
    change Inv.inv (norm (Inv.inv c).val) = norm c.val
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_inv]
  rw [hNorm]
  change ENNReal.ofReal (norm (pi.val ^ m)) = _
  rw [norm_pow, ENNReal.ofReal_pow (norm_nonneg _)]


/-- A rectangle of translated uniformizer balls has additive mass given by
the sum of its entrywise exponents. -/
theorem heckeLocalMatrixAdditiveMeasure_translatedPowerBallRectangle
    {K : Type*} [Field K] [NumberField K]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (n : Nat) (pi : Units (p.adicCompletion K))
    (a : Fin n -> Fin n -> p.adicCompletion K) (m : Fin n -> Fin n -> Nat) :
    let L := p.adicCompletion K
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let mu := heckeLocalAdditiveMeasure p
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => mu)))
      (Set.ofPred (fun X : Fin n -> Fin n -> L =>
        forall i j, v (X i j - a i j) <= v pi.val ^ m i j)) =
      (ENNReal.ofReal (norm pi.val)) ^
        Finset.univ.sum (fun i : Fin n => Finset.univ.sum (m i)) := by
  intro L v mu
  let _ : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let _ : SigmaFinite mu := sigmaFinite_heckeLocalAdditiveMeasure p
  let _ : mu.IsAddLeftInvariant := isAddLeftInvariant_heckeLocalAdditiveMeasure p
  let B (i j : Fin n) :=
    Set.ofPred (fun y : L => v y <= v pi.val ^ m i j)
  let C (i j : Fin n) :=
    Set.preimage (fun y : L => -(a i j) + y) (B i j)
  have hSet : Set.ofPred (fun X : Fin n -> Fin n -> L =>
      forall i j, v (X i j - a i j) <= v pi.val ^ m i j) =
      Set.pi Set.univ (fun i : Fin n => Set.pi Set.univ (C i)) := by
    ext X
    change (forall i j, v (X i j - a i j) <= v pi.val ^ m i j) <-> _
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    change (forall i j, v (X i j - a i j) <= v pi.val ^ m i j) <->
      (forall i j, v (-(a i j) + X i j) <= v pi.val ^ m i j)
    simp only [sub_eq_add_neg, add_comm]
  have hC (i j : Fin n) : mu (C i j) = (ENNReal.ofReal (norm pi.val)) ^ m i j := by
    change mu (Set.preimage (fun y : L => -(a i j) + y) (B i j)) = _
    rw [measure_preimage_add mu]
    exact heckeLocalAdditiveMeasure_uniformizerPowerBall p pi (m i j)
  rw [hSet, Measure.pi_pi]
  simp only [Measure.pi_pi, hC, Finset.prod_pow_eq_pow_sum]

private theorem valuation_le_uniformizer_of_lt_one
    {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative Int)))
    (pi : Units F) (hPi : v pi.val = finiteUniformizerValue)
    (hPiLt : v pi.val < 1) (x : F) (hx : v x < 1) :
    v x <= v pi.val := by
  by_cases hz : x = 0
  . rw [hz, v.map_zero]
    exact zero_le
  . choose m hm using exists_integral_valuation_eq_finiteUniformizerValue_pow v (Units.mk0 x hz) hx.le
    change v x = finiteUniformizerValue ^ m at hm
    rw [<- hPi] at hm
    cases m with
    | zero =>
      rw [hm, pow_zero] at hx
      exact False.elim ((lt_irrefl _) hx)
    | succ k =>
      rw [hm]
      exact cartanPower_le_base_of_pos _ hPiLt.le _ (Nat.zero_lt_succ k)

/-- Over a finite-completion valuation ring, equality of residues is
membership of the difference in the first uniformizer ball. -/
theorem valuation_integer_residue_eq_iff_uniformizerBall
    {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative Int)))
    (pi : Units F) (hPi : v pi.val = finiteUniformizerValue)
    (hPiLt : v pi.val < 1) (x y : v.integer) :
    IsLocalRing.residue v.integer x = IsLocalRing.residue v.integer y <->
      v ((x : F) - (y : F)) <= v pi.val := by
  rw [<- sub_eq_zero, <- map_sub, valuation_integer_residue_eq_zero_iff]
  change v ((x : F) - (y : F)) < 1 <-> _
  exact Iff.intro (valuation_le_uniformizer_of_lt_one v pi hPi hPiLt _)
    (fun h => h.trans_lt hPiLt)

/-- An entry needs one residue digit, with extra digits at a strictly
upper position where the diagonal exponent drops. -/
def cartanResidueEntryExponent {n : Nat} (e : Fin n -> Nat) (i j : Fin n) : Nat :=
  if And (i < j) (e j < e i) then e i - e j else 1

/-- Integral matrices in one residue class satisfying the Cartan
stabilizer's determinant and upper-entry conditions, in row coordinates. -/
def valuationCartanResidueFiber
    {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative Int)))
    (n : Nat) (pi : Units F) (e : Fin n -> Nat)
    (B : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField v.integer)) :
    Set (Fin n -> Fin n -> F) :=
  Set.image (fun X : Matrix (Fin n) (Fin n) v.integer =>
    fun i j => (X i j : F))
    (Set.ofPred (fun X : Matrix (Fin n) (Fin n) v.integer =>
      And (v (X.det : F) = 1)
        (And ((IsLocalRing.residue v.integer).mapMatrix X = B)
          (forall i j, i < j -> v (X i j : F) <= v pi.val ^ (e i - e j)))))

/-- An admissible invertible residue class is a rectangle of translated
uniformizer-power balls in the original matrix entries. -/
theorem valuationCartanResidueFiber_eq_rectangle
    {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative Int)))
    (n : Nat) (pi : Units F) (hPi : v pi.val = finiteUniformizerValue)
    (hPiLt : v pi.val < 1) (e : Fin n -> Nat)
    (A : Matrix (Fin n) (Fin n) v.integer)
    (hA : IsUnit ((IsLocalRing.residue v.integer).mapMatrix A))
    (hZero : forall i j, i < j -> e j < e i -> (A i j : F) = 0) :
    valuationCartanResidueFiber v n pi e ((IsLocalRing.residue v.integer).mapMatrix A) =
      Set.ofPred (fun X : Fin n -> Fin n -> F =>
        forall i j, v (X i j - (A i j : F)) <=
          v pi.val ^ cartanResidueEntryExponent e i j) := by
  let r := IsLocalRing.residue v.integer
  have hExp (i j : Fin n) : 0 < cartanResidueEntryExponent e i j := by
    by_cases h : And (i < j) (e j < e i)
    . rw [cartanResidueEntryExponent, if_pos h]
      exact Nat.sub_pos_iff_lt.mpr h.2
    . rw [cartanResidueEntryExponent, if_neg h]
      exact Nat.zero_lt_succ _
  ext X
  change (exists Y : Matrix (Fin n) (Fin n) v.integer,
    And (And (v (Y.det : F) = 1)
      (And (r.mapMatrix Y = r.mapMatrix A)
        (forall i j, i < j -> v (Y i j : F) <= v pi.val ^ (e i - e j))))
      ((fun i j => (Y i j : F)) = X)) <->
    (forall i j, v (X i j - (A i j : F)) <= v pi.val ^ cartanResidueEntryExponent e i j)
  constructor
  . intro h
    choose Y hY using h
    rw [<- hY.2]
    intro i j
    by_cases hPos : And (i < j) (e j < e i)
    . rw [cartanResidueEntryExponent, if_pos hPos, hZero i j hPos.1 hPos.2, sub_zero]
      exact hY.1.2.2 i j hPos.1
    . rw [cartanResidueEntryExponent, if_neg hPos, pow_one]
      apply (valuation_integer_residue_eq_iff_uniformizerBall v pi hPi hPiLt _ _).mp
      exact congrArg (fun M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField v.integer) =>
        M i j) hY.1.2.1
  . intro h
    have hDiff (i j : Fin n) : v (X i j - (A i j : F)) <= v pi.val :=
      (h i j).trans (cartanPower_le_base_of_pos _ hPiLt.le _ (hExp i j))
    have hVal (i j : Fin n) : v (X i j) <= 1 := by
      have hAij : v (A i j : F) <= 1 := (A i j).property
      calc
        v (X i j) = v ((X i j - (A i j : F)) + (A i j : F)) := by rw [sub_add_cancel]
        _ <= max (v (X i j - (A i j : F))) (v (A i j : F)) := v.map_add _ _
        _ <= 1 := max_le ((hDiff i j).trans hPiLt.le) hAij
    let Y : Matrix (Fin n) (Fin n) v.integer :=
      Matrix.of (fun i j => Subtype.mk (X i j) (hVal i j))
    have hRes : r.mapMatrix Y = r.mapMatrix A := by
      ext i j
      change r (Y i j) = r (A i j)
      exact (valuation_integer_residue_eq_iff_uniformizerBall v pi hPi hPiLt _ _).mpr (hDiff i j)
    have hDet : v (Y.det : F) = 1 := by
      apply (valuation_det_eq_one_iff_residue_matrix_isUnit v n Y).mpr
      change IsUnit (r.mapMatrix Y)
      rw [hRes]
      exact hA
    have hUpper (i j : Fin n) (hi : i < j) : v (Y i j : F) <= v pi.val ^ (e i - e j) := by
      change v (X i j) <= _
      by_cases hj : e j < e i
      . have hHere := h i j
        rw [cartanResidueEntryExponent, if_pos (And.intro hi hj), hZero i j hi hj, sub_zero] at hHere
        exact hHere
      . rw [Nat.sub_eq_zero_of_le (le_of_not_gt hj), pow_zero]
        exact hVal i j
    exact Exists.intro Y (And.intro (And.intro hDet (And.intro hRes hUpper)) rfl)

/-- The additive mass of one admissible stabilizer residue class is
independent of its admissible lift. -/
theorem heckeLocalMatrixAdditiveMeasure_valuationCartanResidueFiber
    {K : Type*} [Field K] [NumberField K]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (n : Nat) (pi : Units (p.adicCompletion K)) (e : Fin n -> Nat) :
    let v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
    v pi.val = finiteUniformizerValue -> v pi.val < 1 ->
    forall A : Matrix (Fin n) (Fin n) v.integer,
      IsUnit ((IsLocalRing.residue v.integer).mapMatrix A) ->
      (forall i j, i < j -> e j < e i -> (A i j : p.adicCompletion K) = 0) ->
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => heckeLocalAdditiveMeasure p)))
        (valuationCartanResidueFiber v n pi e ((IsLocalRing.residue v.integer).mapMatrix A)) =
      (ENNReal.ofReal (norm pi.val)) ^ Finset.univ.sum
        (fun i : Fin n => Finset.univ.sum (cartanResidueEntryExponent e i)) := by
  intro v hPi hPiLt A hA hZero
  rw [valuationCartanResidueFiber_eq_rectangle v n pi hPi hPiLt e A hA hZero]
  exact heckeLocalMatrixAdditiveMeasure_translatedPowerBallRectangle p n pi
    (fun i j => (A i j : p.adicCompletion K)) (cartanResidueEntryExponent e)

/-- Invertible residue matrices allowed by the strictly upper entry
conditions of a diagonal. -/
def valuationCartanAdmissibleResidueMatrix
    {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative Int)))
    (n : Nat) (e : Fin n -> Nat) : Type _ :=
  { B : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField v.integer) //
    And (IsUnit B) (forall i j, i < j -> e j < e i -> B i j = 0) }

private theorem exists_valuationCartanAdmissibleResidueMatrix_lift
    {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative Int)))
    (n : Nat) (e : Fin n -> Nat) (B : valuationCartanAdmissibleResidueMatrix v n e) :
    exists A : Matrix (Fin n) (Fin n) v.integer,
      And ((IsLocalRing.residue v.integer).mapMatrix A = B.val)
        (forall i j, i < j -> e j < e i -> (A i j : F) = 0) := by
  classical
  let r := IsLocalRing.residue v.integer
  have h : forall i j, exists x : v.integer, r x = B.val i j :=
    fun i j => IsLocalRing.residue_surjective (B.val i j)
  choose a ha using h
  let A : Matrix (Fin n) (Fin n) v.integer :=
    Matrix.of (fun i j => if And (i < j) (e j < e i) then 0 else a i j)
  refine Exists.intro A (And.intro ?_ ?_)
  . ext i j
    change r (if And (i < j) (e j < e i) then 0 else a i j) = B.val i j
    by_cases hij : And (i < j) (e j < e i)
    . rw [if_pos hij, map_zero]
      exact (B.property.2 i j hij.1 hij.2).symm
    . rw [if_neg hij]
      exact ha i j
  . intro i j hi hj
    change Subtype.val (if And (i < j) (e j < e i) then (0 : v.integer) else a i j) = (0 : F)
    rw [if_pos (And.intro hi hj)]
    rfl

private theorem pairwiseDisjoint_valuationCartanResidueFibers
    {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative Int)))
    (n : Nat) (pi : Units F) (e : Fin n -> Nat) :
    Pairwise (fun B C : valuationCartanAdmissibleResidueMatrix v n e =>
      Disjoint (valuationCartanResidueFiber v n pi e B.val)
        (valuationCartanResidueFiber v n pi e C.val)) := by
  intro B C hne
  apply Set.disjoint_left.mpr
  intro X hB hC
  choose Y hY using hB
  choose Z hZ using hC
  have hYZ : Y = Z := by
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    exact congrFun (congrFun (hY.2.trans hZ.2.symm) i) j
  have hY' : (IsLocalRing.residue v.integer).mapMatrix Y = B.val := hY.1.2.1
  have hZ' : (IsLocalRing.residue v.integer).mapMatrix Z = C.val := hZ.1.2.1
  rw [hYZ] at hY'
  exact hne (Subtype.ext (hY'.symm.trans hZ'))

/-- The ambient stabilizer in row coordinates is the union of the fibers
over its admissible invertible residue matrices. -/
theorem iUnion_valuationCartanResidueFiber_eq_stabilizerEntries
    {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative Int)))
    (n : Nat) (pi : Units F) (hPi : v pi.val < 1) (gaps : Fin n -> Nat) :
    let e := orderedValuationConeExponents n gaps
    let K := valuationIntegralMatrixSubgroup v n
    let a := valuationUniformizerGapDiagonal n pi gaps
    let d := (valuationDiagonalSection F n a).val
    Set.iUnion (fun B : valuationCartanAdmissibleResidueMatrix v n e =>
      valuationCartanResidueFiber v n pi e B.val) =
      Set.image (fun g : Units (Matrix (Fin n) (Fin n) F) => fun i j => g.val i j)
        ((cartanLeftCosetStabilizer K d).map K.subtype : Set (Units (Matrix (Fin n) (Fin n) F))) := by
  intro e K a d
  ext X
  constructor
  . intro h
    choose B hB using Set.mem_iUnion.mp h
    choose Y hY using hB
    have hDet : v (Y.det : F) = 1 := hY.1.1
    let M := v.integer.subtype.mapMatrix Y
    have hD : v M.det = 1 := by
      change v (v.integer.subtype.mapMatrix Y).det = 1
      rw [<- RingHom.map_det]
      exact hDet
    have hn : Not (M.det = 0) := by
      intro hz
      rw [hz, v.map_zero] at hD
      exact zero_ne_one hD
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero M hn
    have hMem := (mem_map_cartanLeftCosetStabilizer_uniformizerGapDiagonal_iff v n pi hPi.le gaps g)
    refine Exists.intro g (And.intro ?_ hY.2)
    apply hMem.mpr
    exact And.intro hD (And.intro (fun i j => (Y i j).property) hY.1.2.2)
  . intro h
    choose g hg using h
    have hk := (mem_map_cartanLeftCosetStabilizer_uniformizerGapDiagonal_iff v n pi hPi.le gaps g).mp hg.1
    let Y : Matrix (Fin n) (Fin n) v.integer :=
      Matrix.of (fun i j => Subtype.mk (g.val i j) (hk.2.1 i j))
    have hLift : v.integer.subtype.mapMatrix Y = g.val := by ext i j; rfl
    have hDet : v (Y.det : F) = 1 := by
      change v (v.integer.subtype Y.det) = 1
      rw [RingHom.map_det, hLift]
      exact hk.1
    let R := (IsLocalRing.residue v.integer).mapMatrix Y
    have hR : IsUnit R :=
      (valuation_det_eq_one_iff_residue_matrix_isUnit v n Y).mp hDet
    have hZero (i j : Fin n) (hi : i < j) (hj : e j < e i) : R i j = 0 := by
      apply (valuation_integer_residue_eq_zero_iff v (Y i j)).mpr
      exact (hk.2.2 i j hi).trans_lt
        ((cartanPower_le_base_of_pos _ hPi.le _ (Nat.sub_pos_iff_lt.mpr hj)).trans_lt hPi)
    let B : valuationCartanAdmissibleResidueMatrix v n e := Subtype.mk R (And.intro hR hZero)
    refine Set.mem_iUnion.mpr (Exists.intro B ?_)
    exact Exists.intro Y (And.intro (And.intro hDet (And.intro rfl hk.2.2)) hg.2)

private theorem isOpen_heckeLocalMatrix_uniformizerPowerRectangle
    {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    (pi : Units (p.adicCompletion K))
    (a : Fin n -> Fin n -> p.adicCompletion K) (m : Fin n -> Fin n -> Nat) :
    let L := p.adicCompletion K
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    IsOpen (Set.ofPred (fun X : Fin n -> Fin n -> L =>
      forall i j, v (X i j - a i j) <= v pi.val ^ m i j)) := by
  intro L v
  have hOpen : IsOpen (v.integer : Set L) := Valued.isOpen_valuationSubring L
  let t (i j : Fin n) := pi ^ m i j
  let D (i j : Fin n) := Set.preimage
    (fun X : Fin n -> Fin n -> L => (Inv.inv (t i j)).val * (X i j - a i j)) (v.integer : Set L)
  have hD (i j : Fin n) : IsOpen (D i j) := by
    have hEval : Continuous (fun X : Fin n -> Fin n -> L => X i j) :=
      (continuous_apply j).comp (continuous_apply i)
    change IsOpen (Set.preimage
      (fun X : Fin n -> Fin n -> L => (Inv.inv (t i j)).val * (X i j - a i j)) (v.integer : Set L))
    exact hOpen.preimage (continuous_const.mul (hEval.sub continuous_const))
  have hBox : Set.ofPred (fun X : Fin n -> Fin n -> L =>
      forall i j, v (X i j - a i j) <= v pi.val ^ m i j) =
      Set.iInter (fun i : Fin n => Set.iInter (D i)) := by
    ext X
    change (forall i j, v (X i j - a i j) <= v pi.val ^ m i j) <-> _
    simp only [Set.mem_iInter]
    have hEntry (i j : Fin n) :
        v (X i j - a i j) <= v pi.val ^ m i j <-> Membership.mem (D i j) X := by
      let c := t i j
      let b := Inv.inv c
      have hPow : v c.val = v pi.val ^ m i j := by
        change v (pi.val ^ m i j) = _
        exact v.map_pow _ _
      change v (X i j - a i j) <= v pi.val ^ m i j <-> v (b.val * (X i j - a i j)) <= 1
      rw [<- hPow]
      exact valuation_le_unit_iff_inv_mul_le_one v c (X i j - a i j)
    exact Iff.intro (fun h i j => (hEntry i j).mp (h i j))
      (fun h i j => (hEntry i j).mpr (h i j))
  rw [hBox]
  exact isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (hD i))

/-- The additive mass of the Cartan stabilizer is the number of admissible
invertible residue matrices times the mass of a single residue class. -/
theorem heckeLocalMatrixAdditiveMeasure_cartanStabilizerEntries
    {K : Type*} [Field K] [NumberField K]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (n : Nat) (pi : Units (p.adicCompletion K)) (gaps : Fin n -> Nat) :
    let L := p.adicCompletion K
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let e := orderedValuationConeExponents n gaps
    let K0 := valuationIntegralMatrixSubgroup v n
    let a := valuationUniformizerGapDiagonal n pi gaps
    let d := (valuationDiagonalSection L n a).val
    v pi.val = finiteUniformizerValue -> v pi.val < 1 ->
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => heckeLocalAdditiveMeasure p)))
      (Set.image (fun g : Units (Matrix (Fin n) (Fin n) L) => fun i j => g.val i j)
        ((cartanLeftCosetStabilizer K0 d).map K0.subtype : Set (Units (Matrix (Fin n) (Fin n) L)))) =
      (Nat.card (valuationCartanAdmissibleResidueMatrix v n e) : ENNReal) *
        (ENNReal.ofReal (norm pi.val)) ^ Finset.univ.sum
          (fun i : Fin n => Finset.univ.sum (cartanResidueEntryExponent e i)) := by
  intro L v e K0 a d hPi hPiLt
  let I := valuationCartanAdmissibleResidueMatrix v n e
  let D (b : I) := valuationCartanResidueFiber v n pi e b.val
  let _ : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let _ : Finite (IsLocalRing.ResidueField v.integer) := finite_heckeLocalResidueField p
  let _ : Finite (Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField v.integer)) :=
    inferInstanceAs (Finite (Fin n -> Fin n -> IsLocalRing.ResidueField v.integer))
  let _ : Finite I := Finite.of_injective (fun b : I => b.val) Subtype.val_injective
  let _ : Fintype I := Fintype.ofFinite I
  have hLift (b : I) := exists_valuationCartanAdmissibleResidueMatrix_lift v n e b
  have hMeas (b : I) : MeasurableSet (D b) := by
    choose A hA using hLift b
    have hu : IsUnit ((IsLocalRing.residue v.integer).mapMatrix A) := by
      rw [hA.1]
      exact b.property.1
    change MeasurableSet (valuationCartanResidueFiber v n pi e b.val)
    rw [<- hA.1, valuationCartanResidueFiber_eq_rectangle v n pi hPi hPiLt e A hu hA.2]
    exact (isOpen_heckeLocalMatrix_uniformizerPowerRectangle p n pi
      (fun i j => (A i j : L)) (cartanResidueEntryExponent e)).measurableSet
  let w := (ENNReal.ofReal (norm pi.val)) ^ Finset.univ.sum
    (fun i : Fin n => Finset.univ.sum (cartanResidueEntryExponent e i))
  let mu := Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => heckeLocalAdditiveMeasure p))
  have hMass (b : I) : mu (D b) = w := by
    choose A hA using hLift b
    have hu : IsUnit ((IsLocalRing.residue v.integer).mapMatrix A) := by
      rw [hA.1]
      exact b.property.1
    change mu (valuationCartanResidueFiber v n pi e b.val) = w
    rw [<- hA.1]
    exact heckeLocalMatrixAdditiveMeasure_valuationCartanResidueFiber p n pi e hPi hPiLt A hu hA.2
  have hUnion := iUnion_valuationCartanResidueFiber_eq_stabilizerEntries v n pi hPiLt gaps
  change mu (Set.image _ _) = (Nat.card I : ENNReal) * w
  rw [<- hUnion, measure_iUnion (pairwiseDisjoint_valuationCartanResidueFibers v n pi e) hMeas]
  change tsum (fun b : I => mu (D b)) = (Nat.card I : ENNReal) * w
  simp only [hMass, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, nsmul_eq_mul]

end Robin1984.GRH
