import Robin1984.GRH.ValuationIwasawaCoordinates

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Principal congruence subgroups of the general linear group over a local field.
- Formalization note: Constructs compact open principal congruence subgroups and proves diagonal contraction on supported entries.
- PROVENANCE-END
-/

/-!
# Principal congruence subgroups of the local general linear group

Use the integral matrix subgroup for bounds on entries of each matrix
and its inverse. Imposing a further bound on the entries of the
difference from the identity defines the congruence subgroup.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

open TopologicalSpace

variable {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]

private theorem valuation_finset_sum_le (v : Valuation F V) {I : Type*}
    (s : Finset I) (f : I -> F) (r : V) (h : forall i, Membership.mem s i -> v (f i) <= r) :
    v (s.sum f) <= r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (v.map_add _ _).trans (max_le (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))

private theorem valuation_matrix_mul_le (v : Valuation F V) (n : Nat) (r : V)
    (a b : Matrix (Fin n) (Fin n) F)
    (ha : forall i j, v (a i j) <= 1) (hb : forall i j, v (b i j) <= r) :
    forall i j, v ((a * b) i j) <= r := by
  intro i j
  rw [Matrix.mul_apply]
  apply valuation_finset_sum_le
  intro k _
  rw [v.map_mul]
  exact (mul_le_mul' (ha i k) (hb k j)).trans_eq (one_mul r)

/-- The subgroup of integral units whose difference from the identity has
valuation at most the specified bound in each matrix entry. -/
def valuationPrincipalCongruenceSubgroup (v : Valuation F V) (n : Nat) (r : V) :
    Subgroup (Units (Matrix (Fin n) (Fin n) F)) where
  carrier := fun g => And (Membership.mem (valuationIntegralMatrixSubgroup v n) g)
    (forall i j, v ((g.val - 1) i j) <= r)
  one_mem' := And.intro (valuationIntegralMatrixSubgroup v n).one_mem (by
    intro i j
    change v (((1 : Matrix (Fin n) (Fin n) F) - 1) i j) <= r
    simp)
  mul_mem' := by
    intro a b ha hb
    refine And.intro ((valuationIntegralMatrixSubgroup v n).mul_mem ha.1 hb.1) ?_
    have hA : forall i j, v (a.val i j) <= 1 :=
      (mem_valuationIntegralMatrixSubgroup_iff v n a).mp ha.1 |>.1
    have hMul := valuation_matrix_mul_le v n r a.val (b.val - 1) hA hb.2
    have hId : (a * b).val - 1 = a.val * (b.val - 1) + (a.val - 1) := by
      change a.val * b.val - 1 = _
      rw [mul_sub, mul_one, sub_add_sub_cancel]
    intro i j
    rw [hId, Matrix.add_apply]
    exact (v.map_add _ _).trans (max_le (hMul i j) (ha.2 i j))
  inv_mem' := by
    intro a ha
    refine And.intro ((valuationIntegralMatrixSubgroup v n).inv_mem ha.1) ?_
    have hInv : forall i j, v (a.inv i j) <= 1 :=
      (mem_valuationIntegralMatrixSubgroup_iff v n a).mp ha.1 |>.2
    have hMul := valuation_matrix_mul_le v n r a.inv (a.val - 1) hInv ha.2
    have hId : a.inv - 1 = -(a.inv * (a.val - 1)) := by
      rw [mul_sub, mul_one, a.inv_val, neg_sub]
    intro i j
    change v ((a.inv - 1) i j) <= r
    rw [hId, Matrix.neg_apply, v.map_neg]
    exact hMul i j

/-- Membership records both integrality and the congruence bound. -/
theorem mem_valuationPrincipalCongruenceSubgroup_iff
    (v : Valuation F V) (n : Nat) (r : V) (g : Units (Matrix (Fin n) (Fin n) F)) :
    Membership.mem (valuationPrincipalCongruenceSubgroup v n r) g <->
      And (Membership.mem (valuationIntegralMatrixSubgroup v n) g)
        (forall i j, v ((g.val - 1) i j) <= r) :=
  Iff.rfl

/-- Tightening the valuation bound gives a smaller subgroup. -/
theorem valuationPrincipalCongruenceSubgroup_mono
    (v : Valuation F V) (n : Nat) {r s : V} (h : r <= s) :
    valuationPrincipalCongruenceSubgroup v n r <= valuationPrincipalCongruenceSubgroup v n s := by
  intro g hg
  exact And.intro hg.1 (fun i j => (hg.2 i j).trans h)

private theorem valuationBall_eq_unit_preimage (v : Valuation F V) (a : Units F) :
    {x | v x <= v a.val} =
      Set.preimage (fun x => a.inv * x) (v.integer : Set F) := by
  ext x
  change v x <= v a.val <-> v (a.inv * x) <= 1
  have ha : v a.inv * v a.val = 1 := by
    rw [<- v.map_mul, a.inv_val, v.map_one]
  have hx : v x = v a.val * v (a.inv * x) := by
    rw [<- v.map_mul, <- mul_assoc, a.val_inv, one_mul]
  constructor
  . intro h
    have hb := mul_le_mul' (le_refl (v a.inv)) h
    simpa only [hx, <- mul_assoc, ha, one_mul] using hb
  . intro h
    rw [hx]
    exact (mul_le_mul' (le_refl (v a.val)) h).trans_eq (mul_one _)

private theorem valuationPrincipalCongruenceSubgroup_carrier
    (v : Valuation F V) (n : Nat) (r : V) :
    (valuationPrincipalCongruenceSubgroup v n r : Set (Units (Matrix (Fin n) (Fin n) F))) =
      Set.inter (valuationIntegralMatrixSubgroup v n : Set (Units (Matrix (Fin n) (Fin n) F)))
        (Set.iInter (fun i : Fin n => Set.iInter (fun j : Fin n =>
          Set.preimage (fun g : Units (Matrix (Fin n) (Fin n) F) => (g.val - 1) i j)
            {x | v x <= r}))) := by
  ext g
  change Membership.mem (valuationPrincipalCongruenceSubgroup v n r) g <->
    And (Membership.mem (valuationIntegralMatrixSubgroup v n) g)
      (Membership.mem (Set.iInter (fun i : Fin n => Set.iInter (fun j : Fin n =>
        Set.preimage (fun x : Units (Matrix (Fin n) (Fin n) F) => (x.val - 1) i j)
          {x | v x <= r}))) g)
  simp only [mem_valuationPrincipalCongruenceSubgroup_iff, Set.mem_iInter, Set.mem_preimage,
    Set.mem_ofPred_eq]

private theorem continuous_valuationPrincipalCongruence_entry
    [TopologicalSpace F] [IsTopologicalRing F] {n : Nat} (i j : Fin n) :
    Continuous (fun g : Units (Matrix (Fin n) (Fin n) F) => (g.val - 1) i j) := by
  have h : Continuous (fun g : Units (Matrix (Fin n) (Fin n) F) => g.val - 1) :=
    Units.continuous_val.sub continuous_const
  exact (((continuous_apply j).comp (continuous_apply i))).comp h

/-- A principal congruence subgroup is open if the valuation ring is open. -/
theorem isOpen_valuationPrincipalCongruenceSubgroup
    [TopologicalSpace F] [IsTopologicalRing F]
    (v : Valuation F V) (n : Nat) (a : Units F) (hInteger : IsOpen (v.integer : Set F)) :
    IsOpen (valuationPrincipalCongruenceSubgroup v n (v a.val) :
      Set (Units (Matrix (Fin n) (Fin n) F))) := by
  have hBall : IsOpen {x | v x <= v a.val} := by
    rw [valuationBall_eq_unit_preimage]
    exact hInteger.preimage (continuous_const.mul continuous_id)
  rw [valuationPrincipalCongruenceSubgroup_carrier]
  exact (isOpen_valuationIntegralMatrixSubgroup v n hInteger).inter
    (isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j =>
      hBall.preimage (continuous_valuationPrincipalCongruence_entry i j))))

/-- A principal congruence subgroup is compact if the valuation ring is compact. -/
theorem isCompact_valuationPrincipalCongruenceSubgroup
    [TopologicalSpace F] [T2Space F] [IsTopologicalRing F]
    (v : Valuation F V) (n : Nat) (a : Units F) (hInteger : IsCompact (v.integer : Set F)) :
    IsCompact (valuationPrincipalCongruenceSubgroup v n (v a.val) :
      Set (Units (Matrix (Fin n) (Fin n) F))) := by
  have hBall : IsClosed {x | v x <= v a.val} := by
    rw [valuationBall_eq_unit_preimage]
    exact hInteger.isClosed.preimage (continuous_const.mul continuous_id)
  rw [valuationPrincipalCongruenceSubgroup_carrier]
  exact (isCompact_valuationIntegralMatrixSubgroup v n hInteger).inter_right
    (isClosed_iInter (fun i => isClosed_iInter (fun j =>
      hBall.preimage (continuous_valuationPrincipalCongruence_entry i j))))

/-- Ordered diagonal valuations give a contraction on the corresponding entries. -/
theorem valuation_diagonalEntryRatio_le_one (v : Valuation F V) (n : Nat)
    (a : Units (Fin n -> F)) (i j : Fin n) (h : v (a.val i) <= v (a.val j)) :
    v (a.val i * a.inv j) <= 1 := by
  have hinv : a.val j * a.inv j = 1 := congrFun a.val_inv j
  calc
    v (a.val i * a.inv j) = v (a.val i) * v (a.inv j) := v.map_mul _ _
    _ <= v (a.val j) * v (a.inv j) := mul_le_mul' h (le_refl _)
    _ = 1 := by rw [<- v.map_mul, hinv, v.map_one]

/-- Diagonal conjugation preserves the congruence subgroup when it contracts
the supported entries. Allowing all diagonal entries lets this apply to
both triangular directions, using the torus element or its inverse. -/
theorem valuationPrincipalCongruenceSubgroup_conj_of_entrywise_contraction
    (v : Valuation F V) (n : Nat) (r : V) (a : Units (Fin n -> F))
    (S : Fin n -> Fin n -> Prop) (hDiag : forall i, S i i)
    (hRatio : forall i j, S i j -> v (a.val i * a.inv j) <= 1)
    (g : Units (Matrix (Fin n) (Fin n) F))
    (hg : Membership.mem (valuationPrincipalCongruenceSubgroup v n r) g)
    (hSupport : forall i j, Not (S i j) -> g.val i j = 0)
    (hInvSupport : forall i j, Not (S i j) -> g.inv i j = 0) :
    let t := (valuationDiagonalSection F n a).val
    Membership.mem (valuationPrincipalCongruenceSubgroup v n r) (t * g * Inv.inv t) := by
  classical
  intro t
  let M := Matrix (Fin n) (Fin n) F
  let h := t * g * Inv.inv t
  have hEntry (X : M) (i j : Fin n) :
      (t.val * X * t.inv) i j = (a.val i * a.inv j) * X i j := by
    change (Matrix.diagonal a.val * X * Matrix.diagonal a.inv) i j = _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    ac_rfl
  have hTransfer (X : M) (s : V) (hX : forall i j, v (X i j) <= s)
      (hZero : forall i j, Not (S i j) -> X i j = 0) :
      forall i j, v ((t.val * X * t.inv) i j) <= s := by
    intro i j
    rw [hEntry]
    by_cases hs : S i j
    . rw [v.map_mul]
      exact (mul_le_mul' (hRatio i j hs) (hX i j)).trans_eq (one_mul s)
    . rw [hZero i j hs, mul_zero, v.map_zero]
      exact zero_le
  have hEntries := (mem_valuationIntegralMatrixSubgroup_iff v n g).mp hg.1
  have hInv : h.inv = t.val * g.inv * t.inv := by
    change t.val * (g.inv * t.inv) = _
    exact (mul_assoc _ _ _).symm
  have hInt : Membership.mem (valuationIntegralMatrixSubgroup v n) h := by
    apply (mem_valuationIntegralMatrixSubgroup_iff v n h).mpr
    refine And.intro (hTransfer g.val 1 hEntries.1 hSupport) ?_
    rw [hInv]
    exact hTransfer g.inv 1 hEntries.2 hInvSupport
  have hDiff : h.val - 1 = t.val * (g.val - 1) * t.inv := by
    change t.val * g.val * t.inv - 1 = _
    rw [mul_sub, sub_mul, mul_one, t.val_inv]
  have hDiffSupport (i j : Fin n) (hs : Not (S i j)) : (g.val - 1) i j = 0 := by
    have hij : Not (i = j) := by
      intro he
      subst j
      exact hs (hDiag i)
    rw [Matrix.sub_apply, Matrix.one_apply_ne hij, hSupport i j hs, sub_zero]
  refine And.intro hInt ?_
  change forall i j, v ((h.val - 1) i j) <= r
  rw [hDiff]
  exact hTransfer (g.val - 1) r hg.2 hDiffSupport

/-- A scalar that is strictly closer to one than to zero has valuation one. -/
theorem valuation_eq_one_of_sub_one_lt (v : Valuation F V) (d : F)
    (hd : v (d - 1) < 1) : v d = 1 := by
  have hUpper : v d <= 1 := by
    calc
      v d = v ((d - 1) + 1) := by rw [sub_add_cancel]
      _ <= max (v (d - 1)) (v (1 : F)) := v.map_add _ _
      _ = 1 := by rw [v.map_one, max_eq_right hd.le]
  have hLower : 1 <= v d := by
    by_contra h
    have hFlip : v (1 - d) = v (d - 1) := by rw [<- neg_sub, v.map_neg]
    have hBound : 1 <= max (v d) (v (1 - d)) := by
      have hOne : d + (1 - d) = 1 := by simp
      simpa only [hOne, v.map_one] using v.map_add d (1 - d)
    rw [hFlip] at hBound
    exact (not_lt_of_ge hBound) (max_lt (lt_of_not_ge h) hd)
  exact le_antisymm hUpper hLower

/-- Eliminating a unit pivot in a matrix close to the identity leaves the
Schur complement at the same congruence level. -/
theorem valuation_schurComplement_sub_one_le (v : Valuation F V) (n : Nat)
    (r : V) (hr : r <= 1) (A : Matrix (Fin n) (Fin n) F)
    (b c : Fin n -> F) (d : Units F) (hd : v d.val = 1)
    (hA : forall i j, v ((A - 1) i j) <= r)
    (hb : forall i, v (b i) <= r) (hc : forall j, v (c j) <= r) :
    forall i j, v ((Matrix.of (fun x y => A x y - b x * d.inv * c y) - 1) i j) <= r := by
  have hInv : v d.inv = 1 := by
    have h := v.map_mul d.inv d.val
    rw [d.inv_val, v.map_one, hd, mul_one] at h
    exact h.symm
  intro i j
  have hCorrection : v (b i * d.inv * c j) <= r := by
    calc
      v (b i * d.inv * c j) = v (b i) * v (c j) := by
        rw [v.map_mul, v.map_mul, hInv, mul_one]
      _ <= r * r := mul_le_mul' (hb i) (hc j)
      _ <= r := (mul_le_mul' (le_refl r) hr).trans_eq (mul_one r)
  change v ((A i j - b i * d.inv * c j) - (1 : Matrix (Fin n) (Fin n) F) i j) <= r
  rw [sub_right_comm, sub_eq_add_neg]
  exact (v.map_add _ _).trans
    (max_le (hA i j) (by rw [v.map_neg]; exact hCorrection))

end Robin1984.GRH
