import Robin1984.GRH.GodementJacquetUniformizerCone

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Cartan decomposition over valuation rings and finite ordinal comparison.
- Formalization note: Proves the uniqueness of ordered diagonal valuations and partitions entrywise integral invertible matrices into uniformizer double cosets.
- PROVENANCE-END
-/

/-!
# Integral diagonal double cosets

The integral left and right factors determine an ordered list of diagonal
valuations. When the integral scalar valuations are powers of a
uniformizer, the gaps between those exponents index a disjoint partition
of the entrywise integral invertible matrices.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

/-- Integral matrix units have determinant of valuation one. -/
theorem valuation_det_integralMatrixUnit
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (g : Units (Matrix (Fin n) (Fin n) F))
    (hg : Membership.mem (valuationIntegralMatrixSubgroup v n) g) :
    v g.val.det = 1 := by
  let O := v.integer
  have bound (A : Matrix (Fin n) (Fin n) F)
      (hA : forall i j, Membership.mem O (A i j)) : v A.det <= 1 := by
    let A0 : Matrix (Fin n) (Fin n) O := Matrix.of (fun i j => Subtype.mk (A i j) (hA i j))
    have hMap : O.subtype.mapMatrix A0 = A := by ext i j; rfl
    rw [<- hMap, <- RingHom.map_det]
    exact A0.det.property
  have hMem := (mem_valuationIntegralMatrixSubgroup_iff v n g).mp hg
  have hProd : v g.val.det * v g.inv.det = 1 := by
    rw [<- v.map_mul, <- Matrix.det_mul, g.val_inv, Matrix.det_one, v.map_one]
  apply le_antisymm (bound g.val hMem.1)
  calc
    1 = v g.val.det * v g.inv.det := hProd.symm
    _ <= v g.val.det * 1 := mul_le_mul' le_rfl (bound g.inv hMem.2)
    _ = _ := mul_one _

private theorem valuation_finset_sum_lt_one
    {F W I : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (s : Finset I) (f : I -> F)
    (hf : forall i, Membership.mem s i -> v (f i) < 1) : v (s.sum f) < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (v.map_add _ _).trans_lt (max_lt (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

/-- Some permutation of an integral matrix unit uses only entries of
valuation one. This follows from the nonarchimedean determinant bound. -/
theorem exists_valuation_one_permutation_of_integralMatrixUnit
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (g : Units (Matrix (Fin n) (Fin n) F))
    (hg : Membership.mem (valuationIntegralMatrixSubgroup v n) g) :
    exists p : Equiv.Perm (Fin n), forall i, v (g.val (p i) i) = 1 := by
  classical
  have hEntry := ((mem_valuationIntegralMatrixSubgroup_iff v n g).mp hg).1
  by_contra hNot
  have hTerm (p : Equiv.Perm (Fin n)) :
      v (((Equiv.Perm.sign p : Int) : F) * Finset.univ.prod (fun i => g.val (p i) i)) < 1 := by
    have hFail : Not (forall i, v (g.val (p i) i) = 1) :=
      fun h => hNot (Exists.intro p h)
    choose i hi using not_forall.mp hFail
    have hlt : v (g.val (p i) i) < 1 := lt_of_le_of_ne (hEntry (p i) i) hi
    have hSign : v ((Equiv.Perm.sign p : Int) : F) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp
      next => simp [hp]
      next => simp [hp, v.map_neg]
    rw [v.map_mul, hSign, one_mul, map_prod]
    rw [<- Finset.prod_erase_mul Finset.univ (fun j => v (g.val (p j) j)) (Finset.mem_univ i)]
    have hs : ((Finset.univ.erase i).prod (fun j => v (g.val (p j) j))) <= 1 :=
      Finset.prod_le_one (fun _ _ => zero_le) (fun j _ => hEntry (p j) j)
    exact (mul_le_mul' hs (le_refl (v (g.val (p i) i)))).trans_lt (by simpa only [one_mul] using hlt)
  have hDet := valuation_det_integralMatrixUnit v n g hg
  rw [Matrix.det_apply'] at hDet
  have hlt := valuation_finset_sum_lt_one v Finset.univ _ (fun p _ => hTerm p)
  exact (ne_of_lt hlt) hDet

private theorem monotone_le_of_perm_le
    {A : Type*} [LinearOrder A] {n : Nat} (x y : Fin n -> A)
    (hx : Monotone x) (hy : Monotone y) (p : Equiv.Perm (Fin n))
    (hp : forall j, x (p j) <= y j) : forall i, x i <= y i := by
  intro i
  by_contra h
  have hlt := lt_of_not_ge h
  let S := (Finset.univ : Finset (Fin n)).filter (fun j => j <= i)
  have hi : Membership.mem S i := Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) le_rfl)
  have hMap : (S.map p.toEmbedding).card <= (S.erase i).card := by
    apply Finset.card_le_card
    intro k hk
    choose j hj hpk using Finset.mem_map.mp hk
    have hjle : j <= i := (Finset.mem_filter.mp hj).2
    change p j = k at hpk
    have hklt : k < i := by
      apply lt_of_not_ge
      intro hik
      have hxle : x i <= x k := hx hik
      rw [<- hpk] at hxle
      exact (not_lt_of_ge (hxle.trans ((hp j).trans (hy hjle)))) hlt
    exact Finset.mem_erase.mpr (And.intro hklt.ne
      (Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) hklt.le)))
  rw [Finset.card_map] at hMap
  exact (not_lt_of_ge hMap) (Finset.card_erase_lt_of_mem hi)

private theorem valuation_le_of_diagonal_doubleFactor
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (a b : Units (Fin n -> F))
    (ha : Monotone (fun i => v (a.val i))) (hb : Monotone (fun i => v (b.val i)))
    (left right : Units (Matrix (Fin n) (Fin n) F))
    (hl : Membership.mem (valuationIntegralMatrixSubgroup v n) left)
    (hr : Membership.mem (valuationIntegralMatrixSubgroup v n) right)
    (h : Matrix.diagonal a.val = left.val * Matrix.diagonal b.val * right.val) :
    forall i, v (b.val i) <= v (a.val i) := by
  choose p hp using exists_valuation_one_permutation_of_integralMatrixUnit v n left hl
  have hMove : left.val * Matrix.diagonal b.val = Matrix.diagonal a.val * right.inv := by
    calc
      _ = (left.val * Matrix.diagonal b.val) * (right.val * right.inv) := by
        rw [right.val_inv, mul_one]
      _ = _ := by rw [<- mul_assoc, <- h]
  have hRight := ((mem_valuationIntegralMatrixSubgroup_iff v n right).mp hr).2
  have hRel (i : Fin n) : v (b.val i) <= v (a.val (p i)) := by
    have hEq := congrArg (fun A : Matrix (Fin n) (Fin n) F => A (p i) i) hMove
    change (left.val * Matrix.diagonal b.val) (p i) i =
      (Matrix.diagonal a.val * right.inv) (p i) i at hEq
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hEq
    have hv := congrArg v hEq
    rw [v.map_mul, v.map_mul, hp i, one_mul] at hv
    exact hv.trans_le ((mul_le_mul' (le_refl (v (a.val (p i)))) (hRight (p i) i)).trans_eq (mul_one _))
  apply monotone_le_of_perm_le (fun i => v (b.val i)) (fun i => v (a.val i)) hb ha p.symm
  intro i
  simpa only [p.apply_symm_apply] using hRel (p.symm i)

/-- The ordered diagonal valuations are uniquely determined by the double
coset of the integral matrix subgroup. -/
theorem eq_valuation_of_ordered_diagonal_doubleFactor
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (a b : Units (Fin n -> F))
    (ha : Monotone (fun i => v (a.val i))) (hb : Monotone (fun i => v (b.val i)))
    (left right : Units (Matrix (Fin n) (Fin n) F))
    (hl : Membership.mem (valuationIntegralMatrixSubgroup v n) left)
    (hr : Membership.mem (valuationIntegralMatrixSubgroup v n) right)
    (h : Matrix.diagonal a.val = left.val * Matrix.diagonal b.val * right.val) :
    forall i, v (a.val i) = v (b.val i) := by
  have hReverse : Matrix.diagonal b.val = left.inv * Matrix.diagonal a.val * right.inv := by
    calc
      _ = (left.inv * left.val) * Matrix.diagonal b.val * (right.val * right.inv) := by
        rw [left.inv_val, right.val_inv, one_mul, mul_one]
      _ = _ := by rw [h]; simp only [mul_assoc]
  let K := valuationIntegralMatrixSubgroup v n
  have hinv := valuation_le_of_diagonal_doubleFactor v n b a hb ha
    (Inv.inv left) (Inv.inv right) (K.inv_mem hl) (K.inv_mem hr) hReverse
  have hfwd := valuation_le_of_diagonal_doubleFactor v n a b ha hb left right hl hr h
  exact fun i => le_antisymm (hinv i) (hfwd i)


/-- The integral matrix double coset of the diagonal with coordinates a. -/
def valuationIntegralDiagonalDoubleCoset
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (a : Units (Fin n -> F)) :
    Set (Units (Matrix (Fin n) (Fin n) F)) :=
  Set.ofPred (fun g => exists left right : valuationIntegralMatrixSubgroup v n,
    g = left.val * valuationDiagonalSection F n a * right.val)

/-- An element shared by two ordered diagonal double cosets determines all
the diagonal valuations. -/
theorem eq_valuation_of_mem_valuationIntegralDiagonalDoubleCosets
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (a b : Units (Fin n -> F))
    (ha : Monotone (fun i => v (a.val i))) (hb : Monotone (fun i => v (b.val i)))
    (g : Units (Matrix (Fin n) (Fin n) F))
    (hgA : Membership.mem (valuationIntegralDiagonalDoubleCoset v n a) g)
    (hgB : Membership.mem (valuationIntegralDiagonalDoubleCoset v n b) g) :
    forall i, v (a.val i) = v (b.val i) := by
  change (exists l r : valuationIntegralMatrixSubgroup v n,
    g = l.val * valuationDiagonalSection F n a * r.val) at hgA
  change (exists l r : valuationIntegralMatrixSubgroup v n,
    g = l.val * valuationDiagonalSection F n b * r.val) at hgB
  choose lA rA hA using hgA
  choose lB rB hB using hgB
  let A := valuationDiagonalSection F n a
  let B := valuationDiagonalSection F n b
  let l := Inv.inv lA * lB
  let r := rB * Inv.inv rA
  have h : A = l.val * B * r.val := by
    calc
      A = Inv.inv lA.val * g * Inv.inv rA.val := by
        rw [hA]
        simp [A, mul_assoc]
      _ = l.val * B * r.val := by
        rw [hB]
        simp only [B, l, r, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  exact eq_valuation_of_ordered_diagonal_doubleFactor v n a b ha hb
    l.val r.val l.property r.property (congrArg Units.val h)

/-- Canonical diagonal indexed by the nonnegative gaps between exponents. -/
def valuationUniformizerGapDiagonal {F : Type*} [Field F]
    (n : Nat) (pi : Units F) (gaps : Fin n -> Nat) : Units (Fin n -> F) :=
  Finset.univ.prod (fun j => (valuationConePrefixUniformizer n pi j) ^ gaps j)

private theorem strictAnti_valuation_uniformizer_pow
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (pi : Units F) (hPi : v pi.val < 1) :
    StrictAnti (fun k : Nat => v pi.val ^ k) := by
  have hPos : 0 < v pi.val := pos_iff_ne_zero.mpr (fun h => pi.ne_zero ((v.zero_iff).mp h))
  apply strictAnti_nat_of_succ_lt
  intro k
  rw [pow_succ]
  exact (mul_lt_mul_of_pos_left hPi (pow_pos hPos k)).trans_eq (mul_one _)

private theorem valuation_uniformizerGapDiagonal_apply
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (pi : Units F) (gaps : Fin n -> Nat) (i : Fin n) :
    v ((valuationUniformizerGapDiagonal n pi gaps).val i) =
      v pi.val ^ orderedValuationConeExponents n gaps i := by
  rw [valuationUniformizerGapDiagonal, valuationConePrefixUniformizer_prod_apply, map_pow]

private theorem diagonalSection_mem_valuationIntegralMatrixSubgroup
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (a : Units (Fin n -> F))
    (ha : forall i, v (a.val i) = 1) :
    Membership.mem (valuationIntegralMatrixSubgroup v n) (valuationDiagonalSection F n a).val := by
  classical
  have hInv (i : Fin n) : v (a.inv i) = 1 := by
    have h := congrArg v (congrFun a.val_inv i)
    change v (a.val i * a.inv i) = v 1 at h
    simpa only [v.map_mul, ha i, one_mul, v.map_one] using h
  have hBound (f : Fin n -> F) (hf : forall i, v (f i) = 1) (i j : Fin n) :
      v (Matrix.diagonal f i j) <= 1 := by
    by_cases h : i = j
    . subst j
      rw [Matrix.diagonal_apply_eq, hf]
    . rw [Matrix.diagonal_apply_ne _ h, v.map_zero]
      exact zero_le_one
  apply (mem_valuationIntegralMatrixSubgroup_iff v n _).mpr
  exact And.intro (hBound a.val ha) (hBound a.inv hInv)

/-- The double cosets of the uniformizer gap diagonals are pairwise
disjoint. -/
theorem pairwiseDisjoint_valuationUniformizerGapDoubleCosets
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (pi : Units F) (hPi : v pi.val < 1) :
    Pairwise (fun gaps gaps' : Fin n -> Nat =>
      Disjoint (valuationIntegralDiagonalDoubleCoset v n (valuationUniformizerGapDiagonal n pi gaps))
        (valuationIntegralDiagonalDoubleCoset v n (valuationUniformizerGapDiagonal n pi gaps'))) := by
  have hPow := strictAnti_valuation_uniformizer_pow v pi hPi
  have hMono (gs : Fin n -> Nat) :
      Monotone (fun i => v ((valuationUniformizerGapDiagonal n pi gs).val i)) := by
    intro i j hij
    change v ((valuationUniformizerGapDiagonal n pi gs).val i) <=
      v ((valuationUniformizerGapDiagonal n pi gs).val j)
    rw [valuation_uniformizerGapDiagonal_apply, valuation_uniformizerGapDiagonal_apply]
    exact hPow.antitone (antitone_orderedValuationConeExponents n gs hij)
  intro gaps gaps' hne
  apply Set.disjoint_left.mpr
  intro g hg hg'
  have hVal := eq_valuation_of_mem_valuationIntegralDiagonalDoubleCosets v n
    (valuationUniformizerGapDiagonal n pi gaps) (valuationUniformizerGapDiagonal n pi gaps')
    (hMono gaps) (hMono gaps') g hg hg'
  have hExp : orderedValuationConeExponents n gaps' = orderedValuationConeExponents n gaps := by
    funext i
    have hi := hVal i
    rw [valuation_uniformizerGapDiagonal_apply, valuation_uniformizerGapDiagonal_apply] at hi
    exact hPow.injective hi.symm
  choose canon hc using existsUnique_orderedValuationConeExponents n
    (orderedValuationConeExponents n gaps) (antitone_orderedValuationConeExponents n gaps)
  exact hne ((hc.2 gaps rfl).trans (hc.2 gaps' hExp).symm)

private theorem valuation_matrix_mul_integral
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) {n : Nat} (A B : Matrix (Fin n) (Fin n) F)
    (hA : forall i j, v (A i j) <= 1) (hB : forall i j, v (B i j) <= 1) :
    forall i j, v ((A * B) i j) <= 1 := by
  let O := v.integer
  let A0 : Matrix (Fin n) (Fin n) O := Matrix.of (fun i j => Subtype.mk (A i j) (hA i j))
  let B0 : Matrix (Fin n) (Fin n) O := Matrix.of (fun i j => Subtype.mk (B i j) (hB i j))
  have hA0 : O.subtype.mapMatrix A0 = A := by ext i j; rfl
  have hB0 : O.subtype.mapMatrix B0 = B := by ext i j; rfl
  intro i j
  rw [<- hA0, <- hB0, <- map_mul]
  exact ((A0 * B0) i j).property

/-- The entrywise integral matrix units are the union of the canonical
uniformizer double cosets when every nonzero integral scalar valuation is a
nonnegative power of the uniformizer's valuation. -/
theorem iUnion_valuationUniformizerGapDoubleCosets
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (pi : Units F) (hPi : v pi.val < 1)
    (hDiscrete : forall x : Units F, v x.val <= 1 ->
      exists e : Nat, v x.val = v pi.val ^ e) :
    Set.iUnion (fun gaps : Fin n -> Nat =>
      valuationIntegralDiagonalDoubleCoset v n (valuationUniformizerGapDiagonal n pi gaps)) =
      Set.ofPred (fun g : Units (Matrix (Fin n) (Fin n) F) =>
        forall i j, v (g.val i j) <= 1) := by
  classical
  have hPow := strictAnti_valuation_uniformizer_pow v pi hPi
  ext g
  change (Membership.mem (Set.iUnion _) g) <-> (forall i j, v (g.val i j) <= 1)
  constructor
  . intro hg
    choose gaps hGaps using Set.mem_iUnion.mp hg
    change (exists l r : valuationIntegralMatrixSubgroup v n,
      g = l.val * valuationDiagonalSection F n (valuationUniformizerGapDiagonal n pi gaps) * r.val) at hGaps
    choose l r hr using hGaps
    let a := valuationUniformizerGapDiagonal n pi gaps
    have hDiag (i j : Fin n) : v (Matrix.diagonal a.val i j) <= 1 := by
      by_cases hij : i = j
      . subst j
        rw [Matrix.diagonal_apply_eq, valuation_uniformizerGapDiagonal_apply]
        exact (hPow.antitone (Nat.zero_le _)).trans_eq (pow_zero _)
      . rw [Matrix.diagonal_apply_ne _ hij, v.map_zero]
        exact zero_le_one
    have hL := ((mem_valuationIntegralMatrixSubgroup_iff v n l.val).mp l.property).1
    have hR := ((mem_valuationIntegralMatrixSubgroup_iff v n r.val).mp r.property).1
    rw [hr]
    exact valuation_matrix_mul_integral v (l.val.val * Matrix.diagonal a.val) r.val.val
      (valuation_matrix_mul_integral v l.val.val (Matrix.diagonal a.val) hL hDiag) hR
  . intro hg
    choose l r a ha using exists_valuationIntegralMatrix_ordered_doubleDiagonal v n g 1 hg
    have hScalar (i : Fin n) : exists e : Nat, v (a.val i) = v pi.val ^ e := by
      exact hDiscrete (Units.map (Pi.evalMonoidHom (fun _ : Fin n => F) i) a) (ha.2.2.2.2 i)
    choose ex hEx using hScalar
    have hAnti : Antitone ex := by
      intro i j hij
      by_contra h
      have hn : ex i < ex j := lt_of_not_ge h
      have hLt : v pi.val ^ ex j < v pi.val ^ ex i := hPow hn
      rw [<- hEx j, <- hEx i] at hLt
      exact (not_lt_of_ge (ha.2.2.2.1 hij)) hLt
    choose gaps hgaps using existsUnique_orderedValuationConeExponents n ex hAnti
    let b := valuationUniformizerGapDiagonal n pi gaps
    let u := a * Inv.inv b
    have hu (i : Fin n) : v (u.val i) = 1 := by
      have hb : v (b.val i) = v (a.val i) := by
        rw [valuation_uniformizerGapDiagonal_apply, hgaps.1, hEx]
      change v (a.val i * b.inv i) = 1
      rw [v.map_mul, <- hb, <- v.map_mul]
      have h := congrFun b.val_inv i
      change b.val i * b.inv i = 1 at h
      rw [h, v.map_one]
    let d := valuationDiagonalSection F n u
    let k : valuationIntegralMatrixSubgroup v n :=
      Subtype.mk d.val (diagonalSection_mem_valuationIntegralMatrixSubgroup v n u hu)
    let left : valuationIntegralMatrixSubgroup v n := Subtype.mk l ha.1
    let right : valuationIntegralMatrixSubgroup v n := Subtype.mk r ha.2.1
    have haEq : a = u * b := by simp [u, mul_assoc]
    apply Set.mem_iUnion.mpr
    refine Exists.intro gaps (Exists.intro (left * k) (Exists.intro right ?_))
    change g = (left * k).val * (valuationDiagonalSection F n b).val * right.val
    apply Units.ext
    change g.val = (l.val * d.val.val) * (valuationDiagonalSection F n b).val.val * r.val
    rw [ha.2.2.1, haEq]
    change l.val * (valuationDiagonalSection F n (u * b)).val.val * r.val = _
    rw [map_mul]
    simp only [d, Subgroup.coe_mul, Units.val_mul, mul_assoc]

end Robin1984.GRH
