import Robin1984.GRH.GodementJacquetCartanHaarVolume

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Local constancy on compact sets, valuation congruences, and a finite partition of nonnegative exponent gaps.
- Formalization note: Shows that the finite-place matrix test depends only on finitely truncated gaps uniformly over the integral factors, and identifies each truncated-gap class with its varying offsets.
- PROVENANCE-END
-/

/-!
# Finite partitions for local Cartan tests

A locally constant test on finite-place matrices has a uniform
congruence level on integral matrices. At that level, the truncated
Cartan gaps determine the test after multiplication by both integral
factors. Each truncation class is indexed by its nonnegative offsets
with zero offset at a fixed coordinate.
-/

set_option autoImplicit false

open Filter IsDedekindDomain NumberField

namespace Robin1984.GRH

private theorem isLocallyConstant_uniform_radius_on_isCompact
    {X Y : Type*} [PseudoMetricSpace X] (S : Set X) (hS : IsCompact S)
    (f : X -> Y) (hf : IsLocallyConstant f) :
    exists delta : Real, And (0 < delta)
      (forall x y, Membership.mem S x -> dist y x < delta -> f y = f x) := by
  classical
  have hLoc (x : X) : exists r : Real, And (0 < r)
      (forall y, dist y x < r -> f y = f x) := by
    have h := (IsLocallyConstant.iff_eventually_eq f).mp hf x
    exact Metric.mem_nhds_iff.mp h
  choose r hr using hLoc
  let U (x : X) := Metric.ball x (r x / 2)
  have hrHalf (x : X) : 0 < r x / 2 := div_pos (hr x).1 (by norm_num)
  have hCover : S <= Set.iUnion U := by
    intro x _
    exact Set.mem_iUnion_of_mem x (Metric.mem_ball_self (hrHalf x))
  choose T hT using hS.elim_finite_subcover U (fun x => Metric.isOpen_ball) hCover
  have hRadius (t : Finset X) : exists delta : Real, And (0 < delta)
      (forall x, Membership.mem t x -> delta <= r x / 2) := by
    induction t using Finset.induction_on with
    | empty => exact Exists.intro 1 (And.intro zero_lt_one
        (fun x hx => False.elim (Finset.notMem_empty x hx)))
    | insert a t ha ih =>
      choose delta hDelta using ih
      refine Exists.intro (min delta (r a / 2)) (And.intro (lt_min hDelta.1 (hrHalf a)) ?_)
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      . rw [h]
        exact min_le_right _ _
      . exact (min_le_left _ _).trans (hDelta.2 x h)
  choose delta hDelta using hRadius T
  refine Exists.intro delta (And.intro hDelta.1 ?_)
  intro x y hx hxy
  have hB := hT hx
  simp only [Set.mem_iUnion] at hB
  choose c hc hxc using hB
  have hxC : dist x c < r c / 2 := hxc
  have hyC : dist y c < r c := by
    calc
      _ <= dist y x + dist x c := dist_triangle _ _ _
      _ < r c / 2 + r c / 2 := add_lt_add (hxy.trans_le (hDelta.2 c hc)) hxC
      _ = _ := add_halves _
  have hxC' : dist x c < r c := hxC.trans (half_lt_self (hr c).1)
  exact ((hr c).2 y hyC).trans ((hr c).2 x hxC').symm

private theorem valuation_finset_sum_le_of_each
    {F W I : Type*} [Ring F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (s : Finset I) (f : I -> F) (r : W)
    (h : forall i, Membership.mem s i -> v (f i) <= r) :
    v (s.sum f) <= r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, v.map_zero]
    exact zero_le
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (v.map_add _ _).trans (max_le (h i (Finset.mem_insert_self i s))
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk))))

/-- Multiplication on either side by integral matrices preserves an entrywise valuation bound. -/
theorem valuation_integral_matrix_multipliers_preserve_congruence
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (r : W) (L A B R : Matrix (Fin n) (Fin n) F)
    (hL : forall i j, v (L i j) <= 1) (hR : forall i j, v (R i j) <= 1)
    (hAB : forall i j, v (A i j - B i j) <= r) :
    forall i j, v ((L * A * R) i j - (L * B * R) i j) <= r := by
  have hLeft (i j : Fin n) : v ((L * (A - B)) i j) <= r := by
    rw [Matrix.mul_apply]
    refine valuation_finset_sum_le_of_each v _ _ r (fun k _ => ?_)
    rw [v.map_mul]
    exact (mul_le_mul' (hL i k) (hAB k j)).trans_eq (one_mul _)
  intro i j
  change v ((L * A * R - L * B * R) i j) <= r
  rw [<- sub_mul, <- mul_sub, Matrix.mul_apply]
  refine valuation_finset_sum_le_of_each v _ _ r (fun k _ => ?_)
  rw [v.map_mul]
  exact (mul_le_mul' (hLeft i k) (hR k j)).trans_eq (mul_one _)

/-- A locally constant test has a uniform positive congruence level on the
compact space of integral matrices. -/
theorem exists_uniformizer_radius_local_matrix_test
    {K Y : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    (pi : Units (p.adicCompletion K)) (hPi : norm pi.val < 1)
    (f : (Fin n -> Fin n -> p.adicCompletion K) -> Y) (hf : IsLocallyConstant f) :
    let L := p.adicCompletion K
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    exists R : Nat, And (0 < R)
      (forall X Y0 : Fin n -> Fin n -> L, (forall i j, v (X i j) <= 1) ->
        (forall i j, v (Y0 i j - X i j) <= v pi.val ^ R) -> f Y0 = f X) := by
  intro L v
  let S := Set.ofPred (fun X : Fin n -> Fin n -> L => forall i j, v (X i j) <= 1)
  have hI : IsCompact (v.integer : Set L) :=
    isCompact_iff_compactSpace.mpr (compactSpace_heckeLocalIntegers p)
  have hS : IsCompact S :=
    isCompact_pi_infinite (fun _ : Fin n => isCompact_pi_infinite (fun _ : Fin n => hI))
  choose delta hDelta using isLocallyConstant_uniform_radius_on_isCompact S hS f hf
  have hPow := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg pi.val) hPi
  have hSmall : Filter.Eventually (fun m : Nat => norm pi.val ^ m < delta) atTop :=
    hPow.eventually (gt_mem_nhds hDelta.1)
  choose T hT using eventually_atTop.mp hSmall
  let R := T + 1
  refine Exists.intro R (And.intro (Nat.succ_pos _) ?_)
  intro X Y0 hX hDiff
  have hBound (w : L) (hw : v w <= v pi.val ^ R) : norm w <= norm pi.val ^ R := by
    let c := pi ^ R
    have hC : v c.val = v pi.val ^ R := v.map_pow _ _
    have hCInv : v (Inv.inv c).val * v c.val = 1 := by
      rw [<- v.map_mul, show (Inv.inv c).val * c.val = 1 from c.inv_val, v.map_one]
    have hW : v ((Inv.inv c).val * w) <= 1 := by
      rw [v.map_mul]
      have hLe : v w <= v c.val := by rw [hC]; exact hw
      exact (mul_le_mul' le_rfl hLe).trans_eq hCInv
    have hNorm : norm ((Inv.inv c).val * w) <= 1 := by
      rw [FinitePlace.norm_def]
      exact (WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal p)).mpr hW
    have he : c.val * ((Inv.inv c).val * w) = w := by
      rw [<- mul_assoc, show c.val * (Inv.inv c).val = 1 from c.val_inv, one_mul]
    calc
      norm w = norm c.val * norm ((Inv.inv c).val * w) := by rw [<- norm_mul, he]
      _ <= norm c.val := mul_le_of_le_one_right (norm_nonneg _) hNorm
      _ = _ := norm_pow _ _
  have hRadius : 0 <= norm pi.val ^ R := pow_nonneg (norm_nonneg _) _
  have hDist : dist Y0 X <= norm pi.val ^ R := by
    refine (dist_pi_le_iff hRadius).mpr (fun i => ?_)
    refine (dist_pi_le_iff hRadius).mpr (fun j => ?_)
    rw [dist_eq_norm]
    exact hBound _ (hDiff i j)
  exact hDelta.2 X Y0 hX (hDist.trans_lt (hT R (Nat.le_succ _)))

private theorem min_orderedValuationConeExponents_eq_of_min_gaps
    (n R : Nat) (gaps other : Fin n -> Nat)
    (h : forall k, min R (gaps k) = min R (other k)) (i : Fin n) :
    min R (orderedValuationConeExponents n gaps i) =
      min R (orderedValuationConeExponents n other i) := by
  rw [orderedValuationConeExponents_eq_sum, orderedValuationConeExponents_eq_sum]
  by_cases hLarge : exists k : Fin n, And (i <= k) (R <= gaps k)
  . choose k hk using hLarge
    have hOther : R <= other k := by
      have hk' := h k
      rw [min_eq_left hk.2] at hk'
      exact hk'.trans_le (min_le_right _ _)
    have hSum (g : Fin n -> Nat) (hg : R <= g k) :
        R <= Finset.univ.sum (fun j => if i <= j then g j else 0) := by
      have ht := Finset.single_le_sum
        (f := fun j : Fin n => if i <= j then g j else 0)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
      rw [if_pos hk.1] at ht
      exact hg.trans ht
    rw [min_eq_left (hSum gaps hk.2), min_eq_left (hSum other hOther)]
  . apply congrArg (min R)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hi : i <= k
    . have hlt : gaps k < R := lt_of_not_ge (fun hh => hLarge (Exists.intro k (And.intro hi hh)))
      have he : gaps k = min R (other k) := (min_eq_right hlt.le).symm.trans (h k)
      have hOther : other k < R := by
        by_contra hn
        rw [min_eq_left (le_of_not_gt hn)] at he
        exact hlt.ne he
      rw [min_eq_right hOther.le] at he
      simp only [hi, if_true, he]
    . simp only [hi, if_false]

private theorem valuation_sub_uniformizer_pow_le_of_min_eq
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (pi : Units F) (hPi : v pi.val <= 1)
    (R a b : Nat) (h : min R a = min R b) :
    v (pi.val ^ a - pi.val ^ b) <= v pi.val ^ R := by
  by_cases ha : a < R
  . have hEq : a = min R b := (min_eq_right ha.le).symm.trans h
    have hb : b < R := by
      by_contra hn
      rw [min_eq_left (le_of_not_gt hn)] at hEq
      exact ha.ne hEq
    rw [min_eq_right hb.le] at hEq
    rw [hEq, sub_self, v.map_zero]
    exact zero_le
  . have ha' : R <= a := le_of_not_gt ha
    have hb : R <= b := by
      rw [min_eq_left ha'] at h
      exact h.trans_le (min_le_right _ _)
    have hPow (m : Nat) : v pi.val ^ m <= 1 := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ]
        exact (mul_le_mul' ih hPi).trans_eq (one_mul 1)
    have hBound (m : Nat) (hm : R <= m) : v (pi.val ^ m) <= v pi.val ^ R := by
      rw [v.map_pow, <- Nat.add_sub_of_le hm, pow_add]
      exact (mul_le_mul' le_rfl (hPow (m - R))).trans_eq (mul_one _)
    exact (v.map_sub _ _).trans (max_le (hBound a ha') (hBound b hb))

/-- Matching truncated gaps gives diagonals congruent at that level. -/
theorem valuationUniformizerGapDiagonal_congruent_of_min_gaps
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n R : Nat) (pi : Units F) (hPi : v pi.val <= 1)
    (gaps other : Fin n -> Nat) (h : forall k, min R (gaps k) = min R (other k)) :
    let a := (valuationDiagonalSection F n (valuationUniformizerGapDiagonal n pi gaps)).val
    let b := (valuationDiagonalSection F n (valuationUniformizerGapDiagonal n pi other)).val
    forall i j, v (a.val i j - b.val i j) <= v pi.val ^ R := by
  intro a b i j
  change v (Matrix.diagonal (valuationUniformizerGapDiagonal n pi gaps).val i j -
    Matrix.diagonal (valuationUniformizerGapDiagonal n pi other).val i j) <= _
  by_cases hEq : i = j
  . subst j
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, valuationUniformizerGapDiagonal,
      valuationUniformizerGapDiagonal, valuationConePrefixUniformizer_prod_apply,
      valuationConePrefixUniformizer_prod_apply]
    exact valuation_sub_uniformizer_pow_le_of_min_eq v pi hPi R _ _
      (min_orderedValuationConeExponents_eq_of_min_gaps n R gaps other h i)
  . rw [Matrix.diagonal_apply_ne _ hEq, Matrix.diagonal_apply_ne _ hEq, sub_self, v.map_zero]
    exact zero_le

/-- At a positive truncation level, equal truncations have equal positive-gap positions. -/
theorem positiveGap_iff_of_min_gaps
    (n R : Nat) (hR : 0 < R) (gaps other : Fin n -> Nat)
    (h : forall k, min R (gaps k) = min R (other k)) (k : Fin n) :
    0 < gaps k <-> 0 < other k := by
  have hg : 0 < min R (gaps k) <-> 0 < gaps k :=
    Iff.intro (fun hh => hh.trans_le (min_le_right _ _)) (fun hh => lt_min hR hh)
  have ho : 0 < min R (other k) <-> 0 < other k :=
    Iff.intro (fun hh => hh.trans_le (min_le_right _ _)) (fun hh => lt_min hR hh)
  rw [<- hg, h k, ho]

/-- The test on the integral Cartan locus depends on a finite truncation of the
gaps, uniformly in both integral matrix factors. -/
theorem exists_cartan_localTest_truncation
    {K Y : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    (pi : Units (p.adicCompletion K))
    (hPi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue)
    (f : (Fin n -> Fin n -> p.adicCompletion K) -> Y) (hf : IsLocallyConstant f) :
    let L := p.adicCompletion K
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let C := valuationIntegralMatrixSubgroup v n
    let d (gaps : Fin n -> Nat) :=
      (valuationDiagonalSection L n (valuationUniformizerGapDiagonal n pi gaps)).val
    exists R : Nat, And (0 < R)
      (forall gaps other : Fin n -> Nat,
        (forall i, min R (gaps i) = min R (other i)) ->
        forall l r : C,
          f (fun i j => (l.val * d gaps * r.val).val i j) =
            f (fun i j => (l.val * d other * r.val).val i j)) := by
  intro L v C d
  have hNorm : norm pi.val < 1 := by
    rw [norm_eq_inv_of_valuation_finiteUniformizer p pi.val hPi, <- one_div]
    have hQ : (1 : Real) < dedekindPrimeNorm K p := by
      exact_mod_cast one_lt_dedekindPrimeNorm K p
    simpa only [div_one] using one_div_lt_one_div_of_lt (show (0 : Real) < 1 by norm_num) hQ
  have hp : v pi.val <= 1 := by
    have hn := hNorm.le
    rw [FinitePlace.norm_def] at hn
    exact (WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal p)).mp hn
  choose R hR using exists_uniformizer_radius_local_matrix_test p n pi hNorm f hf
  refine Exists.intro R (And.intro hR.1 ?_)
  intro gaps other hSame l r
  let X := l.val * d other * r.val
  let Y0 := l.val * d gaps * r.val
  let D (g : Fin n -> Nat) := valuationIntegralDiagonalDoubleCoset v n
    (valuationUniformizerGapDiagonal n pi g)
  have hX : forall i j, v (X.val i j) <= 1 := by
    have hMem : Membership.mem (D other) X := Exists.intro l (Exists.intro r rfl)
    have hUnion := iUnion_heckeLocal_valuationUniformizerGapDoubleCosets p n pi hPi
    change Membership.mem (Set.ofPred (fun g : Units (Matrix (Fin n) (Fin n) L) =>
      forall i j, v (g.val i j) <= 1)) X
    rw [<- hUnion]
    exact Set.mem_iUnion_of_mem other hMem
  have hL (i j : Fin n) : v (l.val.val i j) <= 1 :=
    ((mem_valuationIntegralMatrixSubgroup_iff v n l.val).mp l.property).1 i j
  have hRight (i j : Fin n) : v (r.val.val i j) <= 1 :=
    ((mem_valuationIntegralMatrixSubgroup_iff v n r.val).mp r.property).1 i j
  have hDiag : forall i j, v ((d gaps).val i j - (d other).val i j) <= v pi.val ^ R :=
    valuationUniformizerGapDiagonal_congruent_of_min_gaps v n R pi hp gaps other hSame
  have hDiff : forall i j, v (Y0.val i j - X.val i j) <= v pi.val ^ R := by
    intro i j
    simpa only [Y0, X, Units.val_mul] using
      valuation_integral_matrix_multipliers_preserve_congruence v n (v pi.val ^ R)
        l.val.val (d gaps).val (d other).val r.val.val hL hRight hDiag i j
  exact hR.2 (fun i j => X.val i j) (fun i j => Y0.val i j) hX hDiff

/-- Translate one truncated-gap class to offsets that vanish at its fixed coordinates. -/
def gapPatternFiber_equiv_zeroInactive
    (n R : Nat) (pat : Fin n -> Fin (R + 1)) :
    Equiv {g : Fin n -> Nat // forall i, min R (g i) = (pat i).val}
      {e : Fin n -> Nat // forall i, (pat i).val < R -> e i = 0} := by
  have hlo (i : Fin n) : (pat i).val <= R := Nat.le_of_lt_succ (pat i).isLt
  have hFixed (g : Fin n -> Nat) (i : Fin n) (h : min R (g i) = (pat i).val)
      (hi : (pat i).val < R) : g i = (pat i).val := by
    have hg : g i < R := by
      by_contra hn
      rw [min_eq_left (le_of_not_gt hn)] at h
      exact hi.ne h.symm
    rw [min_eq_right hg.le] at h
    exact h
  refine
    { toFun := fun g => Subtype.mk (fun i => g.val i - (pat i).val) (fun i hi => ?_)
      invFun := fun e => Subtype.mk (fun i => (pat i).val + e.val i) (fun i => ?_)
      left_inv := ?_
      right_inv := ?_ }
  . change g.val i - (pat i).val = 0
    rw [hFixed g.val i (g.property i) hi, Nat.sub_self]
  . change min R ((pat i).val + e.val i) = (pat i).val
    by_cases hi : (pat i).val < R
    . rw [e.property i hi, add_zero]
      exact min_eq_right (hlo i)
    . have he : (pat i).val = R := le_antisymm (hlo i) (le_of_not_gt hi)
      rw [he, min_eq_left (Nat.le_add_right _ _)]
  . intro g
    apply Subtype.ext
    funext i
    have hi : (pat i).val <= g.val i := (g.property i).symm.trans_le (min_le_right _ _)
    exact Nat.add_sub_of_le hi
  . intro e
    apply Subtype.ext
    funext i
    exact Nat.add_sub_cancel_left (pat i).val (e.val i)

/-- A zero geometric weight enforces the zero offset at a fixed coordinate. -/
theorem masked_gap_weights
    (n R : Nat) (pat : Fin n -> Fin (R + 1)) (alpha : Fin n -> Complex)
    (e : Fin n -> Nat) :
    Finset.univ.prod (fun i => (if (pat i).val < R then (0 : Complex) else alpha i) ^ e i) =
      if forall i, (pat i).val < R -> e i = 0 then
        Finset.univ.prod (fun i => alpha i ^ e i) else 0 := by
  classical
  by_cases h : forall i, (pat i).val < R -> e i = 0
  . rw [if_pos h]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : (pat i).val < R
    . rw [h i hi, pow_zero, pow_zero]
    . rw [if_neg hi]
  . rw [if_neg h]
    have hBad : exists i, And ((pat i).val < R) (Not (e i = 0)) := by
      by_contra hn
      apply h
      intro i hi
      by_contra he
      exact hn (Exists.intro i (And.intro hi he))
    choose i hi using hBad
    rw [<- Finset.prod_erase_mul Finset.univ
      (fun j => (if (pat j).val < R then (0 : Complex) else alpha j) ^ e j)
      (Finset.mem_univ i)]
    rw [if_pos hi.1, zero_pow hi.2, mul_zero]

end Robin1984.GRH
