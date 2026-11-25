import Robin1984.GRH.GodementJacquetCartanResidueMeasure

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Cartan double cosets over nonarchimedean local fields, Haar normalization, and finite sums over the coordinates of a diagonal matrix.
- Formalization note: Computes normalized Cartan double-coset volume from the finite residue-class masses and expresses the sum of the entry exponents as a weighted gap sum.
- PROVENANCE-END
-/

/-!
# Normalized Haar volume of Cartan double cosets

The residue-class calculation gives the volumes of the integral subgroup
and the Cartan stabilizer in row coordinates. Their ratio gives the Haar
volume of the Cartan double coset.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField Topology

namespace Robin1984.GRH

private theorem mem_cartanStabilizer_iff
    {G : Type*} [Group G] (C : Subgroup G) (d g : G) :
    Membership.mem ((cartanLeftCosetStabilizer C d).map C.subtype) g <->
      And (Membership.mem C g) (Membership.mem C (MulAut.conj (Inv.inv d) g)) := by
  rw [Subgroup.mem_map]
  constructor
  . intro hg
    choose k hk using hg
    have he : k.val = g := hk.2
    rw [<- he]
    exact And.intro k.property hk.1
  . intro hg
    exact Exists.intro (Subtype.mk g hg.1) (And.intro hg.2 rfl)

private theorem cartanStabilizer_zeroGaps
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (pi : Units F) (hPi : v pi.val <= 1) :
    let C := valuationIntegralMatrixSubgroup v n
    let d := (valuationDiagonalSection F n (valuationUniformizerGapDiagonal n pi (fun _ => 0))).val
    (cartanLeftCosetStabilizer C d).map C.subtype = C := by
  intro C d
  ext g
  constructor
  . intro hg
    exact ((mem_cartanStabilizer_iff C d g).mp hg).1
  . intro hg
    apply (mem_map_cartanLeftCosetStabilizer_uniformizerGapDiagonal_iff v n pi hPi
      (fun _ => 0) g).mpr
    have he (i : Fin n) : orderedValuationConeExponents n (fun _ => 0) i = 0 := by
      rw [orderedValuationConeExponents_eq_sum]
      simp
    have hEntry (i j : Fin n) : v (g.val i j) <= 1 :=
      ((mem_valuationIntegralMatrixSubgroup_iff v n g).mp hg).1 i j
    refine And.intro (valuation_det_integralMatrixUnit v n g hg) (And.intro hEntry ?_)
    intro i j _
    simpa only [he, Nat.sub_zero, pow_zero] using hEntry i j

/-- For Haar measure normalized on the integral subgroup, the volume of a
Cartan double coset is the ratio of the two additive residue-class masses. -/
theorem measure_heckeLocal_valuationUniformizerGapDoubleCoset_eq_residueRatio
    {K : Type*} [Field K] [NumberField K]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (n : Nat) (pi : Units (p.adicCompletion K))
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    [mu.IsHaarMeasure] (gaps : Fin n -> Nat) :
    let L := p.adicCompletion K
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let C := valuationIntegralMatrixSubgroup v n
    let mass (z : Fin n -> Nat) :=
      let e := orderedValuationConeExponents n z
      (Nat.card (valuationCartanAdmissibleResidueMatrix v n e) : ENNReal) *
        (ENNReal.ofReal (norm pi.val)) ^ Finset.univ.sum
          (fun i : Fin n => Finset.univ.sum (cartanResidueEntryExponent e i))
    v pi.val = finiteUniformizerValue -> v pi.val < 1 ->
    mu (C : Set (Units (Matrix (Fin n) (Fin n) L))) = 1 ->
    mu (valuationIntegralDiagonalDoubleCoset v n (valuationUniformizerGapDiagonal n pi gaps)) =
      mass (fun _ => 0) / mass gaps := by
  intro L v C mass hPi hPiLt hMu
  let G := Units (Matrix (Fin n) (Fin n) L)
  let a := valuationUniformizerGapDiagonal n pi gaps
  let d := (valuationDiagonalSection L n a).val
  let H := (cartanLeftCosetStabilizer C d).map C.subtype
  let row : G -> Fin n -> Fin n -> L := heckeLocalMatrixUnitEntries
  let A := Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => heckeLocalAdditiveMeasure p))
  let _ : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  have hRow : IsOpenEmbedding row := isOpenEmbedding_heckeLocalMatrixUnitEntries
  let _ : SecondCountableTopology G := hRow.isEmbedding.secondCountableTopology
  have hIntegerOpen : IsOpen (v.integer : Set L) := Valued.isOpen_valuationSubring L
  have hIntCompact : IsCompact (v.integer : Set L) :=
    isCompact_iff_compactSpace.mpr (compactSpace_heckeLocalIntegers p)
  have hC := isOpen_valuationIntegralMatrixSubgroup v n hIntegerOpen
  have hCompact := isCompact_valuationIntegralMatrixSubgroup v n hIntCompact
  have hH : IsOpen (H : Set G) := by
    have he : (H : Set G) =
        Set.inter (C : Set G) (Set.preimage (fun g : G => MulAut.conj (Inv.inv d) g) (C : Set G)) :=
      Set.ext (mem_cartanStabilizer_iff C d)
    rw [he]
    exact hC.inter (hC.preimage (by
      simp only [MulAut.conj_apply]
      exact (continuous_const.mul continuous_id).mul continuous_const))
  have hFinite (z : Fin n -> Nat) : Not (mass z = (Top.top : ENNReal)) := by
    dsimp only [mass]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)
  have hResidue (z : Fin n -> Nat) :
      let dz := (valuationDiagonalSection L n (valuationUniformizerGapDiagonal n pi z)).val
      A (Set.image row ((cartanLeftCosetStabilizer C dz).map C.subtype : Set G)) = mass z :=
    heckeLocalMatrixAdditiveMeasure_cartanStabilizerEntries p n pi z hPi hPiLt
  have hMassC : A (Set.image row (C : Set G)) = mass (fun _ => 0) := by
    have hh := hResidue (fun _ => 0)
    dsimp only at hh
    rw [cartanStabilizer_zeroGaps v n pi hPiLt.le] at hh
    exact hh
  have hMassH : A (Set.image row (H : Set G)) = mass gaps := hResidue gaps
  have hNorm (g : G) (hg : Membership.mem C g) : norm g.val.det = 1 := by
    have hDet : Valued.v g.val.det = 1 := valuation_det_integralMatrixUnit v n g hg
    have hOne : norm (1 : L) = 1 := norm_one
    rw [FinitePlace.norm_def, map_one] at hOne
    rw [FinitePlace.norm_def, hDet]
    exact hOne
  have hScale := heckeLocalMatrixUnitWeightedMeasure_eq_smul_haar p mu (C : Set G)
    hC.measurableSet hMu hNorm
  have hImage : MeasurableSet (Set.image row (H : Set G)) :=
    hRow.measurableEmbedding.measurableSet_image' hH.measurableSet
  have hDetImage (X : Fin n -> Fin n -> L) (hX : Membership.mem
      (Set.image row (H : Set G)) X) : norm (Matrix.of X).det = 1 := by
    choose g hg using hX
    rw [<- hg.2]
    exact hNorm g ((mem_cartanStabilizer_iff C d g).mp hg.1).1
  have hWeighted := congrArg (fun m : Measure G => m (H : Set G)) hScale
  change (Measure.comap row (heckeLocalDeterminantWeightedMeasure p (Fin n))) (H : Set G) =
    (HSMul.hSMul (A (Set.image row (C : Set G))).toNNReal mu) (H : Set G) at hWeighted
  rw [hRow.measurableEmbedding.comap_apply,
    heckeLocalDeterminantWeightedMeasure_apply_of_detNorm_one p _ hImage hDetImage,
    Measure.coe_nnreal_smul_apply, hMassC, hMassH,
    ENNReal.coe_toNNReal (hFinite (fun _ => 0))] at hWeighted
  have hSet : valuationIntegralDiagonalDoubleCoset v n a =
      DoubleCoset.doubleCoset d (C : Set G) (C : Set G) := by
    ext g
    rw [DoubleCoset.mem_doubleCoset]
    change (exists l r : C, g = l.val * d * r.val) <-> _
    constructor
    . intro hg
      choose l r h using hg
      exact Exists.intro l.val (And.intro l.property (Exists.intro r.val (And.intro r.property h)))
    . intro hg
      choose l hl r hr h using hg
      exact Exists.intro (Subtype.mk l hl) (Exists.intro (Subtype.mk r hr) h)
  rw [hSet]
  have hMul : mu (DoubleCoset.doubleCoset d (C : Set G) (C : Set G)) * mu (H : Set G) = 1 := by
    simpa only [hMu, one_pow] using measure_cartanDoubleCoset_mul_stabilizerMeasure mu C
      hCompact hC d
  let E := orderedValuationConeExponents n gaps
  let I := valuationCartanAdmissibleResidueMatrix v n E
  let _ : Finite (IsLocalRing.ResidueField v.integer) := finite_heckeLocalResidueField p
  let _ : Finite (Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField v.integer)) :=
    inferInstanceAs (Finite (Fin n -> Fin n -> IsLocalRing.ResidueField v.integer))
  let _ : Finite I := Finite.of_injective (fun b : I => b.val) Subtype.val_injective
  let _ : Nonempty I := Nonempty.intro (Subtype.mk 1
    (And.intro isUnit_one (fun i j hij _ => Matrix.one_apply_ne (ne_of_lt hij))))
  have hCard : Not ((Nat.card I : ENNReal) = 0) := by
    norm_cast
    exact Nat.ne_of_gt Nat.card_pos
  have hNormPos : Not (ENNReal.ofReal (norm pi.val) = 0) :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr pi.ne_zero))
  have hDenom : Not (mass gaps = 0) := mul_ne_zero hCard (pow_ne_zero _ hNormPos)
  have hEq : mu (DoubleCoset.doubleCoset d (C : Set G) (C : Set G)) * mass gaps =
      mass (fun _ => 0) := by
    rw [hWeighted, mul_left_comm, hMul, mul_one]
  rw [<- hEq, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hDenom (hFinite gaps), mul_one]

/-- Two ordered diagonal exponents differ by the intervening gaps. -/
theorem orderedValuationConeExponents_sub
    (n : Nat) (gaps : Fin n -> Nat) (i j : Fin n) :
    orderedValuationConeExponents n gaps i - orderedValuationConeExponents n gaps j =
      Finset.univ.sum (fun k => if And (i <= k) (k < j) then gaps k else 0) := by
  by_cases hij : i <= j
  . have h : orderedValuationConeExponents n gaps i =
        Finset.univ.sum (fun k => if And (i <= k) (k < j) then gaps k else 0) +
          orderedValuationConeExponents n gaps j := by
      rw [orderedValuationConeExponents_eq_sum n gaps i,
        orderedValuationConeExponents_eq_sum n gaps j, <- Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hj : j <= k
      . simp [hj, hij.trans hj, not_lt_of_ge hj]
      . by_cases hi : i <= k <;> simp [hi, hj, lt_of_not_ge hj]
    rw [h, Nat.add_sub_cancel]
  . have hle : orderedValuationConeExponents n gaps i <= orderedValuationConeExponents n gaps j :=
      antitone_orderedValuationConeExponents n gaps (le_of_not_ge hij)
    rw [Nat.sub_eq_zero_of_le hle]
    symm
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have hZero : Not (And (i <= k) (k < j)) :=
      fun h => hij (h.1.trans h.2.le)
    rw [if_neg hZero]

/-- Strict inequality of ordered diagonal exponents depends on the positions
of the positive gaps. -/
theorem orderedValuationConeExponents_lt_iff
    (n : Nat) (gaps : Fin n -> Nat) (i j : Fin n) :
    orderedValuationConeExponents n gaps j < orderedValuationConeExponents n gaps i <->
      exists k : Fin n, And (i <= k) (And (k < j) (0 < gaps k)) := by
  rw [<- Nat.sub_pos_iff_lt, orderedValuationConeExponents_sub]
  constructor
  . intro h
    by_contra hn
    have hZero : Finset.univ.sum (fun k => if And (i <= k) (k < j) then gaps k else 0) = 0 := by
      refine Finset.sum_eq_zero (fun k _ => ?_)
      by_cases hk : And (i <= k) (k < j)
      . rw [if_pos hk]
        exact Nat.eq_zero_of_not_pos (fun hp => hn (Exists.intro k (And.intro hk.1 (And.intro hk.2 hp))))
      . rw [if_neg hk]
    exact (Nat.ne_of_gt h) hZero
  . intro h
    choose k hk using h
    have ht := Finset.single_le_sum
      (f := fun l : Fin n => if And (i <= l) (l < j) then gaps l else 0)
      (fun l _ => Nat.zero_le _) (Finset.mem_univ k)
    rw [if_pos (And.intro hk.1 hk.2.1)] at ht
    exact hk.2.2.trans_le ht

private theorem card_below_fin (n : Nat) (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => i <= k)).card = k.val + 1 := by
  have h : Finset.univ.filter (fun i : Fin n => i <= k) = Finset.Iic k := by
    ext i
    simp
  rw [h, Fin.card_Iic]

private theorem card_above_fin (n : Nat) (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => k < i)).card = n - (k.val + 1) := by
  have h : Finset.univ.filter (fun i : Fin n => k < i) = Finset.Ioi k := by
    ext i
    simp
  rw [h, Fin.card_Ioi, Nat.sub_sub, Nat.add_comm 1 k.val]

/-- Each gap contributes to the sum of positive exponent differences once for
each ordered pair of coordinates that it separates. -/
theorem sum_orderedValuationConeExponents_sub
    (n : Nat) (gaps : Fin n -> Nat) :
    Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n =>
      orderedValuationConeExponents n gaps i - orderedValuationConeExponents n gaps j)) =
      Finset.univ.sum (fun k : Fin n => ((k.val + 1) * (n - (k.val + 1))) * gaps k) := by
  let t (i j k : Fin n) := if And (i <= k) (k < j) then gaps k else 0
  have hSwap (i : Fin n) :
      Finset.univ.sum (fun j : Fin n => Finset.univ.sum (t i j)) =
        Finset.univ.sum (fun k : Fin n => Finset.univ.sum (fun j : Fin n => t i j k)) :=
    Finset.sum_comm
  have hConst (i k : Fin n) :
      Finset.univ.sum (fun j : Fin n => t i j k) =
        if i <= k then (n - (k.val + 1)) * gaps k else 0 := by
    by_cases hi : i <= k
    . simp only [t, hi, true_and, if_true]
      rw [<- Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, card_above_fin, Nat.cast_id]
    . simp [t, hi]
  calc
    _ = Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : Fin n => Finset.univ.sum (t i j))) := by
      simp only [orderedValuationConeExponents_sub, t]
    _ = Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun k : Fin n => Finset.univ.sum (fun j : Fin n => t i j k))) := by
      simp only [hSwap]
    _ = Finset.univ.sum (fun k : Fin n =>
        Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n => t i j k))) :=
      Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [hConst]
      rw [<- Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, card_below_fin, Nat.cast_id, mul_assoc]

/-- The sum of the entrywise ball exponents is the base dimension plus the
weighted gap sum, with one unit removed at each strictly constrained entry. -/
theorem sum_cartanResidueEntryExponent_add_positivePairCount
    (n : Nat) (gaps : Fin n -> Nat) :
    let e := orderedValuationConeExponents n gaps
    Finset.univ.sum (fun i : Fin n => Finset.univ.sum (cartanResidueEntryExponent e i)) +
      Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n =>
        if And (i < j) (e j < e i) then 1 else 0)) =
        n * n + Finset.univ.sum (fun k : Fin n => ((k.val + 1) * (n - (k.val + 1))) * gaps k) := by
  intro e
  have hPoint (i j : Fin n) :
      cartanResidueEntryExponent e i j + (if And (i < j) (e j < e i) then 1 else 0) =
        1 + (e i - e j) := by
    by_cases hij : i < j
    . by_cases he : e j < e i
      . simp [cartanResidueEntryExponent, hij, he, Nat.add_comm]
      . simp [cartanResidueEntryExponent, hij, he, Nat.sub_eq_zero_of_le (le_of_not_gt he)]
    . have he : e i <= e j := antitone_orderedValuationConeExponents n gaps (le_of_not_gt hij)
      simp [cartanResidueEntryExponent, hij, Nat.sub_eq_zero_of_le he]
  calc
    _ = Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n =>
        cartanResidueEntryExponent e i j + (if And (i < j) (e j < e i) then 1 else 0))) := by
      simp only [Finset.sum_add_distrib]
    _ = Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n =>
        1 + (e i - e j))) := by simp only [hPoint]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_id, mul_one, e, sum_orderedValuationConeExponents_sub]

end Robin1984.GRH
