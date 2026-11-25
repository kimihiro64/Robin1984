import Robin1984.GRH.ValuationPrincipalCongruence

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Block Gaussian elimination at a unit pivot and double cosets of principal congruence subgroups.
- Formalization note: Proves principal congruence factorization, the ordered diagonal double-coset identity, and Cartan decomposition over a valuation ring.
- PROVENANCE-END
-/

/-!
# Principal congruence factorization and Cartan decomposition

The last scalar pivot is a unit. Its Schur complement remains at the same
valuation bound, so eliminating the last row and column reduces the rank.
The triangular factors and their inverses have the supports needed for
diagonal conjugation in the two opposite directions. A maximal pivot also
gives the Cartan decomposition by integral left and right operations.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

/-- An elementary square-zero perturbation and its inverse lie at the same
congruence level when the perturbation entries do. -/
private theorem exists_valuationPrincipalCongruence_one_add_of_square_zero
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (n : Nat) (r : V) (hr : r <= 1)
    (X : Matrix (Fin n) (Fin n) F) (hXX : X * X = 0)
    (hX : forall i j, v (X i j) <= r) :
    exists g : Units (Matrix (Fin n) (Fin n) F),
      And (g.val = 1 + X) (And (g.inv = 1 - X)
        (Membership.mem (valuationPrincipalCongruenceSubgroup v n r) g)) := by
  let g : Units (Matrix (Fin n) (Fin n) F) :=
    { val := 1 + X
      inv := 1 - X
      val_inv := by simp [mul_sub, add_mul, hXX]
      inv_val := by simp [sub_mul, mul_add, hXX] }
  have hOne (i j : Fin n) : v ((1 : Matrix (Fin n) (Fin n) F) i j) <= 1 :=
    ((mem_valuationIntegralMatrixSubgroup_iff v n 1).mp
      (valuationIntegralMatrixSubgroup v n).one_mem).1 i j
  have hVal (i j : Fin n) : v (g.val i j) <= 1 := by
    change v ((1 + X) i j) <= 1
    rw [Matrix.add_apply]
    exact (v.map_add _ _).trans (max_le (hOne i j) ((hX i j).trans hr))
  have hInv (i j : Fin n) : v (g.inv i j) <= 1 := by
    change v ((1 - X) i j) <= 1
    rw [Matrix.sub_apply, sub_eq_add_neg]
    exact (v.map_add _ _).trans
      (max_le (hOne i j) (by rw [v.map_neg]; exact (hX i j).trans hr))
  have hInt : Membership.mem (valuationIntegralMatrixSubgroup v n) g :=
    (mem_valuationIntegralMatrixSubgroup_iff v n g).mpr (And.intro hVal hInv)
  have hDiff : g.val - 1 = X := by
    change 1 + X - 1 = X
    simp
  refine Exists.intro g (And.intro rfl (And.intro rfl (And.intro hInt ?_)))
  intro i j
  rw [hDiff]
  exact hX i j

/-- Eliminating the last column and row expresses the matrix through its
Schur complement and two elementary factors. -/
private theorem lastBlock_eq_upper_diagonal_lower
    {F : Type*} [Field F] (n : Nat)
    (A : Matrix (Fin n) (Fin n) F) (b : Fin n -> F) (c : Fin n -> F)
    (d : Units F) :
    let B : Matrix (Fin n) (Fin 1) F := Matrix.of (fun i _ => b i)
    let C : Matrix (Fin 1) (Fin n) F := Matrix.of (fun _ j => c j)
    let D : Matrix (Fin 1) (Fin 1) F := Matrix.of (fun _ _ => d.val)
    let U : Matrix (Fin n) (Fin 1) F := Matrix.of (fun i _ => b i * d.inv)
    let L : Matrix (Fin 1) (Fin n) F := Matrix.of (fun _ j => d.inv * c j)
    let S : Matrix (Fin n) (Fin n) F :=
      Matrix.of (fun i j => A i j - b i * d.inv * c j)
    Matrix.fromBlocks A B C D =
      Matrix.fromBlocks 1 U 0 1 * Matrix.fromBlocks S 0 0 D *
        Matrix.fromBlocks 1 0 L 1 := by
  intro B C D U L S
  have hUD : U * D = B := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    change b i * d.inv * d.val = b i
    rw [mul_assoc, d.inv_val, mul_one]
  have hDL : D * L = C := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    change d.val * (d.inv * c j) = c j
    calc
      d.val * (d.inv * c j) = (d.val * d.inv) * c j := (mul_assoc _ _ _).symm
      _ = c j := by rw [d.val_inv, one_mul]
  have hSB : S + B * L = A := by
    ext i j
    rw [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_one]
    change A i j - b i * d.inv * c j + b i * (d.inv * c j) = A i j
    rw [mul_assoc (b i) d.inv (c j), sub_add_cancel]
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hUD]
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, zero_add, hDL, hSB]

/-- The strict off-diagonal part of either elementary block factor squares
to zero. -/
private theorem lastBlock_upper_lower_square_zero
    {F : Type*} [Field F] (n : Nat)
    (U : Matrix (Fin n) (Fin 1) F) (L : Matrix (Fin 1) (Fin n) F) :
    let upper : Matrix (Sum (Fin n) (Fin 1)) (Sum (Fin n) (Fin 1)) F :=
      Matrix.fromBlocks 0 U 0 0
    let lower : Matrix (Sum (Fin n) (Fin 1)) (Sum (Fin n) (Fin 1)) F :=
      Matrix.fromBlocks 0 0 L 0
    And (upper * upper = 0) (lower * lower = 0) := by
  constructor <;> simp [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

/-- Adjoin the last scalar block while keeping the same congruence level. -/
private theorem exists_valuationPrincipalCongruence_lastBlock_diagonal
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (n : Nat) (r : V)
    (g : Units (Matrix (Fin n) (Fin n) F)) (d : Units F)
    (hg : Membership.mem (valuationPrincipalCongruenceSubgroup v n r) g)
    (hd : v d.val <= 1) (hdInv : v d.inv <= 1)
    (hdClose : v (d.val - 1) <= r) :
    let e : Equiv (Sum (Fin n) (Fin 1)) (Fin (n + 1)) := finSumFinEquiv
    let D : Matrix (Fin 1) (Fin 1) F := Matrix.of (fun _ _ => d.val)
    exists lifted : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) F),
      And (lifted.val = Matrix.reindexRingEquiv F e (Matrix.fromBlocks g.val 0 0 D))
        (Membership.mem (valuationPrincipalCongruenceSubgroup v (n + 1) r) lifted) := by
  intro e D
  let Dinv : Matrix (Fin 1) (Fin 1) F := Matrix.of (fun _ _ => d.inv)
  have hD (y : Units F) :
      let Y : Matrix (Fin 1) (Fin 1) F := Matrix.of (fun _ _ => y.val)
      let Yinv : Matrix (Fin 1) (Fin 1) F := Matrix.of (fun _ _ => y.inv)
      Y * Yinv = 1 := by
    intro Y Yinv
    ext i j
    have hji : j = i := Subsingleton.elim _ _
    subst j
    rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq]
    exact y.val_inv
  have hDD : D * Dinv = 1 := hD d
  have hDDinv : Dinv * D = 1 := hD (Inv.inv d)
  let block : Units (Matrix (Sum (Fin n) (Fin 1)) (Sum (Fin n) (Fin 1)) F) :=
    { val := Matrix.fromBlocks g.val 0 0 D
      inv := Matrix.fromBlocks g.inv 0 0 Dinv
      val_inv := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
          g.val_inv, hDD, Matrix.fromBlocks_one]
      inv_val := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
          g.inv_val, hDDinv, Matrix.fromBlocks_one] }
  let reindex := Matrix.reindexRingEquiv F e
  let lifted := Units.map reindex.toMonoidHom block
  have blockBound (A : Matrix (Fin n) (Fin n) F) (B : Matrix (Fin 1) (Fin 1) F)
      (bound : V) (hA : forall i j, v (A i j) <= bound)
      (hB : forall i j, v (B i j) <= bound) :
      forall i j, v (reindex (Matrix.fromBlocks A 0 0 B) i j) <= bound := by
    have hAt (i j : Sum (Fin n) (Fin 1)) :
        v (Matrix.fromBlocks A 0 0 B i j) <= bound := by
      cases i with
      | inl i =>
        cases j with
        | inl j => exact hA i j
        | inr j =>
          change v (0 : F) <= bound
          rw [v.map_zero]
          exact zero_le
      | inr i =>
        cases j with
        | inl j =>
          change v (0 : F) <= bound
          rw [v.map_zero]
          exact zero_le
        | inr j => exact hB i j
    exact fun i j => hAt (e.symm i) (e.symm j)
  have hgIntegral := (mem_valuationIntegralMatrixSubgroup_iff v n g).mp hg.1
  have hIntegral : Membership.mem (valuationIntegralMatrixSubgroup v (n + 1)) lifted :=
    (mem_valuationIntegralMatrixSubgroup_iff v (n + 1) lifted).mpr
      (And.intro (blockBound g.val D 1 hgIntegral.1 (fun _ _ => hd))
        (blockBound g.inv Dinv 1 hgIntegral.2 (fun _ _ => hdInv)))
  have hDiff : lifted.val - 1 =
      reindex (Matrix.fromBlocks (g.val - 1) 0 0 (D - 1)) := by
    change reindex (Matrix.fromBlocks g.val 0 0 D) - 1 = _
    rw [(map_one reindex).symm, (map_sub reindex _ _).symm]
    congr 1
    have hOne : (1 : Matrix (Sum (Fin n) (Fin 1)) (Sum (Fin n) (Fin 1)) F) =
        Matrix.fromBlocks 1 0 0 1 := Matrix.fromBlocks_one.symm
    rw [hOne]
    ext i j
    cases i <;> cases j <;> simp [Matrix.sub_apply, Matrix.fromBlocks]
  have hDclose (i j : Fin 1) : v ((D - 1) i j) <= r := by
    have hji : j = i := Subsingleton.elim _ _
    subst j
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
    exact hdClose
  refine Exists.intro lifted (And.intro rfl (And.intro hIntegral ?_))
  intro i j
  rw [hDiff]
  exact blockBound _ _ r hg.2 hDclose i j

private theorem lastBlock_upper_support
    {F : Type*} [Field F] (n : Nat)
    (A : Matrix (Fin n) (Fin n) F) (B : Matrix (Fin n) (Fin 1) F)
    (D : Matrix (Fin 1) (Fin 1) F)
    (hA : forall i j, j < i -> A i j = 0) :
    let e : Equiv (Sum (Fin n) (Fin 1)) (Fin (n + 1)) := finSumFinEquiv
    forall i j, j < i ->
      Matrix.reindexRingEquiv F e (Matrix.fromBlocks A B 0 D) i j = 0 := by
  intro e
  have atBlock (i j : Sum (Fin n) (Fin 1)) (h : e j < e i) :
      Matrix.fromBlocks A B 0 D i j = 0 := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hA i j h
      | inr j =>
        change n + j.val < i.val at h
        exact False.elim (by omega)
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j =>
        have hij : j = i := Subsingleton.elim _ _
        subst j
        exact (lt_irrefl _ h).elim
  intro i j h
  apply atBlock (e.symm i) (e.symm j)
  simpa only [e.apply_symm_apply] using h

private theorem lastBlock_lower_support
    {F : Type*} [Field F] (n : Nat)
    (A : Matrix (Fin n) (Fin n) F) (C : Matrix (Fin 1) (Fin n) F)
    (D : Matrix (Fin 1) (Fin 1) F)
    (hA : forall i j, i < j -> A i j = 0) :
    let e : Equiv (Sum (Fin n) (Fin 1)) (Fin (n + 1)) := finSumFinEquiv
    forall i j, i < j ->
      Matrix.reindexRingEquiv F e (Matrix.fromBlocks A 0 C D) i j = 0 := by
  intro e
  have atBlock (i j : Sum (Fin n) (Fin 1)) (h : e i < e j) :
      Matrix.fromBlocks A 0 C D i j = 0 := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hA i j h
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j =>
        change n + i.val < j.val at h
        exact False.elim (by omega)
      | inr j =>
        have hij : j = i := Subsingleton.elim _ _
        subst j
        exact (lt_irrefl _ h).elim
  intro i j h
  apply atBlock (e.symm i) (e.symm j)
  simpa only [e.apply_symm_apply] using h

/-- The upper and lower last-block elimination matrices remain at the
principal congruence level of their off-diagonal entries. -/
private theorem exists_valuationPrincipalCongruence_lastBlock_elementary
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (n : Nat) (r : V) (hr : r <= 1)
    (B : Matrix (Fin n) (Fin 1) F) (C : Matrix (Fin 1) (Fin n) F)
    (hB : forall i j, v (B i j) <= r) (hC : forall i j, v (C i j) <= r) :
    let e : Equiv (Sum (Fin n) (Fin 1)) (Fin (n + 1)) := finSumFinEquiv
    exists upper lower : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) F),
      And (upper.val = Matrix.reindexRingEquiv F e (Matrix.fromBlocks 1 B 0 1))
      (And (lower.val = Matrix.reindexRingEquiv F e (Matrix.fromBlocks 1 0 C 1))
      (And (Membership.mem (valuationPrincipalCongruenceSubgroup v (n + 1) r) upper)
        (Membership.mem (valuationPrincipalCongruenceSubgroup v (n + 1) r) lower))) := by
  intro e
  let reindex := Matrix.reindexRingEquiv F e
  let X : Matrix (Sum (Fin n) (Fin 1)) (Sum (Fin n) (Fin 1)) F :=
    Matrix.fromBlocks 0 B 0 0
  let Y : Matrix (Sum (Fin n) (Fin 1)) (Sum (Fin n) (Fin 1)) F :=
    Matrix.fromBlocks 0 0 C 0
  have hSquares : And (X * X = 0) (Y * Y = 0) :=
    lastBlock_upper_lower_square_zero n B C
  have hSquare (W : Matrix (Sum (Fin n) (Fin 1)) (Sum (Fin n) (Fin 1)) F)
      (hW : W * W = 0) : reindex W * reindex W = 0 := by
    rw [(map_mul reindex W W).symm, hW, map_zero]
  have zeroBound : v (0 : F) <= r := by rw [v.map_zero]; exact zero_le
  have boundX (i j : Sum (Fin n) (Fin 1)) : v (X i j) <= r := by
    cases i <;> cases j
    all_goals first | exact hB _ _ | exact zeroBound
  have boundY (i j : Sum (Fin n) (Fin 1)) : v (Y i j) <= r := by
    cases i <;> cases j
    all_goals first | exact hC _ _ | exact zeroBound
  choose upper hUpper using exists_valuationPrincipalCongruence_one_add_of_square_zero
    v (n + 1) r hr (reindex X) (hSquare X hSquares.1)
    (fun i j => boundX (e.symm i) (e.symm j))
  choose lower hLower using exists_valuationPrincipalCongruence_one_add_of_square_zero
    v (n + 1) r hr (reindex Y) (hSquare Y hSquares.2)
    (fun i j => boundY (e.symm i) (e.symm j))
  have hOne : (1 : Matrix (Sum (Fin n) (Fin 1)) (Sum (Fin n) (Fin 1)) F) =
      Matrix.fromBlocks 1 0 0 1 := Matrix.fromBlocks_one.symm
  have upperVal : upper.val = reindex (Matrix.fromBlocks 1 B 0 1) := by
    rw [hUpper.1, (map_one reindex).symm, (map_add reindex _ _).symm]
    congr 1
    rw [hOne]
    ext i j
    cases i <;> cases j <;> simp [X, Matrix.add_apply, Matrix.fromBlocks]
  have lowerVal : lower.val = reindex (Matrix.fromBlocks 1 0 C 1) := by
    rw [hLower.1, (map_one reindex).symm, (map_add reindex _ _).symm]
    congr 1
    rw [hOne]
    ext i j
    cases i <;> cases j <;> simp [Y, Matrix.add_apply, Matrix.fromBlocks]
  exact Exists.intro upper (Exists.intro lower
    (And.intro upperVal (And.intro lowerVal (And.intro hUpper.2.2 hLower.2.2))))

private theorem upper_support_mul
    {F : Type*} [Field F] (n : Nat) (A B : Matrix (Fin n) (Fin n) F)
    (hA : forall i j, j < i -> A i j = 0) (hB : forall i j, j < i -> B i j = 0) :
    forall i j, j < i -> (A * B) i j = 0 := by
  intro i j hji
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k < i
  next => rw [hA i k hki, zero_mul]
  next => rw [hB k j (hji.trans_le (le_of_not_gt hki)), mul_zero]

private theorem lower_support_mul
    {F : Type*} [Field F] (n : Nat) (A B : Matrix (Fin n) (Fin n) F)
    (hA : forall i j, i < j -> A i j = 0) (hB : forall i j, i < j -> B i j = 0) :
    forall i j, i < j -> (A * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i < k
  next => rw [hA i k hik, zero_mul]
  next => rw [hB k j ((le_of_not_gt hik).trans_lt hij), mul_zero]

/-- Every matrix in a principal congruence ball below level one factors
as an upper triangular, diagonal and lower triangular unit at that level. -/
theorem exists_valuationPrincipalCongruence_upper_diagonal_lower
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (n : Nat) (r : V) (hr : r < 1)
    (A : Matrix (Fin n) (Fin n) F) (hA : forall i j, v ((A - 1) i j) <= r) :
    exists upper diagonal lower : Units (Matrix (Fin n) (Fin n) F),
      And (A = upper.val * diagonal.val * lower.val)
      (And
        (And (Membership.mem (valuationPrincipalCongruenceSubgroup v n r) upper)
          (And (Membership.mem (valuationPrincipalCongruenceSubgroup v n r) diagonal)
            (Membership.mem (valuationPrincipalCongruenceSubgroup v n r) lower)))
        (And (forall i j, j < i -> upper.val i j = 0)
          (And (forall i j, Not (i = j) -> diagonal.val i j = 0)
            (forall i j, i < j -> lower.val i j = 0)))) := by
  induction n with
  | zero =>
    have hOne : A = 1 := by ext i; exact Fin.elim0 i
    refine Exists.intro 1 (Exists.intro 1 (Exists.intro 1 (And.intro ?_ ?_)))
    next => simpa only [Units.val_one, mul_one] using hOne
    next =>
      have hMem := (valuationPrincipalCongruenceSubgroup v 0 r).one_mem
      exact And.intro (And.intro hMem (And.intro hMem hMem))
        (And.intro (fun i => Fin.elim0 i)
          (And.intro (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)))
  | succ n ih =>
    let e : Equiv (Sum (Fin n) (Fin 1)) (Fin (n + 1)) := finSumFinEquiv
    let reindex := Matrix.reindexRingEquiv F e
    let M := reindex.symm A
    let A0 : Matrix (Fin n) (Fin n) F := Matrix.of (fun i j => M (Sum.inl i) (Sum.inl j))
    let b : Fin n -> F := fun i => M (Sum.inl i) (Sum.inr 0)
    let c : Fin n -> F := fun j => M (Sum.inr 0) (Sum.inl j)
    let d0 := M (Sum.inr 0) (Sum.inr 0)
    have hM (i j : Sum (Fin n) (Fin 1)) : v ((M - 1) i j) <= r := by
      have hDiff : M - 1 = reindex.symm (A - 1) := by simp [M]
      rw [hDiff]
      exact hA (e i) (e j)
    have hOne : (1 : Matrix (Sum (Fin n) (Fin 1)) (Sum (Fin n) (Fin 1)) F) =
        Matrix.fromBlocks 1 0 0 1 := Matrix.fromBlocks_one.symm
    have hA0 (i j : Fin n) : v ((A0 - 1) i j) <= r := by
      have h := hM (Sum.inl i) (Sum.inl j)
      rw [hOne, Matrix.sub_apply] at h
      exact h
    have hb (i : Fin n) : v (b i) <= r := by
      have h := hM (Sum.inl i) (Sum.inr 0)
      rw [hOne, Matrix.sub_apply] at h
      change v (b i - 0) <= r at h
      simpa only [sub_zero] using h
    have hc (j : Fin n) : v (c j) <= r := by
      have h := hM (Sum.inr 0) (Sum.inl j)
      rw [hOne, Matrix.sub_apply] at h
      change v (c j - 0) <= r at h
      simpa only [sub_zero] using h
    have hd0 : v (d0 - 1) <= r := by
      have h := hM (Sum.inr 0) (Sum.inr 0)
      rw [hOne, Matrix.sub_apply] at h
      change v (d0 - (1 : Matrix (Fin 1) (Fin 1) F) 0 0) <= r at h
      simpa only [Matrix.one_apply_eq] using h
    have hd0one : v d0 = 1 := valuation_eq_one_of_sub_one_lt v d0 (hd0.trans_lt hr)
    have hd0ne : Not (d0 = 0) := by
      intro h
      rw [h, v.map_zero] at hd0one
      exact zero_ne_one hd0one
    let d := Units.mk0 d0 hd0ne
    have hd : v d.val = 1 := hd0one
    have hdInv : v d.inv = 1 := by
      have h := v.map_mul d.inv d.val
      rw [d.inv_val, v.map_one, hd, mul_one] at h
      exact h.symm
    let S : Matrix (Fin n) (Fin n) F :=
      Matrix.of (fun i j => A0 i j - b i * d.inv * c j)
    have hS := valuation_schurComplement_sub_one_le v n r hr.le A0 b c d hd hA0 hb hc
    choose up diag low hSmall using ih S hS
    let D : Matrix (Fin 1) (Fin 1) F := Matrix.of (fun _ _ => d.val)
    let B : Matrix (Fin n) (Fin 1) F := Matrix.of (fun i _ => b i * d.inv)
    let C : Matrix (Fin 1) (Fin n) F := Matrix.of (fun _ j => d.inv * c j)
    have hB (i : Fin n) (j : Fin 1) : v (B i j) <= r := by
      change v (b i * d.inv) <= r
      rw [v.map_mul, hdInv, mul_one]
      exact hb i
    have hC (i : Fin 1) (j : Fin n) : v (C i j) <= r := by
      change v (d.inv * c j) <= r
      rw [v.map_mul, hdInv, one_mul]
      exact hc j
    choose upElim lowElim hElim using
      exists_valuationPrincipalCongruence_lastBlock_elementary v n r hr.le B C hB hC
    have hUnity : v (1 : F) <= 1 := by rw [v.map_one]
    have hUnityClose : v ((1 : F) - 1) <= r := by
      rw [sub_self, v.map_zero]
      exact zero_le
    choose upLift hUpLift using exists_valuationPrincipalCongruence_lastBlock_diagonal
      v n r up 1 hSmall.2.1.1 hUnity hUnity hUnityClose
    choose lowLift hLowLift using exists_valuationPrincipalCongruence_lastBlock_diagonal
      v n r low 1 hSmall.2.1.2.2 hUnity hUnity hUnityClose
    choose diagLift hDiagLift using exists_valuationPrincipalCongruence_lastBlock_diagonal
      v n r diag d hSmall.2.1.2.1 hd.le hdInv.le hd0
    have hUpLiftVal : upLift.val = reindex (Matrix.fromBlocks up.val 0 0 1) := by
      convert hUpLift.1 using 3
      ext i j
      have hji : j = i := Subsingleton.elim _ _
      subst j
      rw [Matrix.one_apply_eq]
      rfl
    have hLowLiftVal : lowLift.val = reindex (Matrix.fromBlocks low.val 0 0 1) := by
      convert hLowLift.1 using 3
      ext i j
      have hji : j = i := Subsingleton.elim _ _
      subst j
      rw [Matrix.one_apply_eq]
      rfl
    have hMiddle : upLift.val * diagLift.val * lowLift.val =
        reindex (Matrix.fromBlocks S 0 0 D) := by
      rw [hUpLiftVal, hDiagLift.1, hLowLiftVal, <- map_mul, <- map_mul]
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
        hSmall.1.symm]
      rfl
    have hBlock : M = Matrix.fromBlocks A0
        (Matrix.of (fun i _ => b i)) (Matrix.of (fun _ j => c j)) D := by
      ext i j
      cases i <;> cases j
      next => rfl
      next =>
        rename_i j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
      next =>
        rename_i i j
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      next =>
        rename_i i j
        have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        subst i
        subst j
        rfl
    have hFactor : A = (upElim * upLift).val * diagLift.val * (lowLift * lowElim).val := by
      calc
        A = reindex M := (reindex.apply_symm_apply A).symm
        _ = reindex (Matrix.fromBlocks 1 B 0 1 * Matrix.fromBlocks S 0 0 D *
            Matrix.fromBlocks 1 0 C 1) :=
          congrArg reindex (hBlock.trans (lastBlock_eq_upper_diagonal_lower n A0 b c d))
        _ = upElim.val * (upLift.val * diagLift.val * lowLift.val) * lowElim.val := by
          rw [map_mul, map_mul, hElim.1, hElim.2.1, hMiddle]
        _ = (upElim * upLift).val * diagLift.val * (lowLift * lowElim).val := by
          simp only [Units.val_mul, mul_assoc]
    have upperOne (i j : Fin n) (h : j < i) :
        (1 : Matrix (Fin n) (Fin n) F) i j = 0 := Matrix.one_apply_ne h.ne.symm
    have lowerOne (i j : Fin n) (h : i < j) :
        (1 : Matrix (Fin n) (Fin n) F) i j = 0 := Matrix.one_apply_ne h.ne
    have upElimSupport : forall i j, j < i -> upElim.val i j = 0 := by
      rw [hElim.1]
      exact lastBlock_upper_support n 1 B 1 upperOne
    have lowElimSupport : forall i j, i < j -> lowElim.val i j = 0 := by
      rw [hElim.2.1]
      exact lastBlock_lower_support n 1 C 1 lowerOne
    have upLiftSupport : forall i j, j < i -> upLift.val i j = 0 := by
      rw [hUpLiftVal]
      exact lastBlock_upper_support n up.val 0 1 hSmall.2.2.1
    have lowLiftSupport : forall i j, i < j -> lowLift.val i j = 0 := by
      rw [hLowLiftVal]
      exact lastBlock_lower_support n low.val 0 1 hSmall.2.2.2.2
    have diagSupport (i j : Fin (n + 1)) (h : Not (i = j)) : diagLift.val i j = 0 := by
      rw [hDiagLift.1]
      rcases lt_or_gt_of_ne h with hij | hji
      next =>
        exact lastBlock_lower_support n diag.val 0 D
          (fun a b hab => hSmall.2.2.2.1 a b hab.ne) i j hij
      next =>
        exact lastBlock_upper_support n diag.val 0 D
          (fun a b hba => hSmall.2.2.2.1 a b hba.ne.symm) i j hji
    let K := valuationPrincipalCongruenceSubgroup v (n + 1) r
    have upMem : Membership.mem K (upElim * upLift) := K.mul_mem hElim.2.2.1 hUpLift.2
    have lowMem : Membership.mem K (lowLift * lowElim) := K.mul_mem hLowLift.2 hElim.2.2.2
    exact Exists.intro (upElim * upLift) (Exists.intro diagLift (Exists.intro (lowLift * lowElim)
      (And.intro hFactor (And.intro (And.intro upMem (And.intro hDiagLift.2 lowMem))
        (And.intro (upper_support_mul (n + 1) _ _ upElimSupport upLiftSupport)
          (And.intro diagSupport (lower_support_mul (n + 1) _ _ lowLiftSupport lowElimSupport)))))))

private theorem inverse_order_support
    {F : Type*} [Field F] (n : Nat) (g : Units (Matrix (Fin n) (Fin n) F))
    (key : Fin n -> Nat) (hKey : Function.Injective key)
    (hDiag : forall i, Not (g.val i i = 0))
    (hSupport : forall i j, key i < key j -> g.val i j = 0) :
    forall i j, key i < key j -> g.inv i j = 0 := by
  intro i j hij
  suffices h : forall m i, key i = m -> key i < key j -> g.inv i j = 0 from
    h (key i) i rfl hij
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro i hi hij
    have hSum : (g.val * g.inv) i j = g.val i i * g.inv i j := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_single i
      next =>
        intro k _ hki
        have hkne : Not (key k = key i) := fun h => hki (hKey h)
        rcases lt_or_gt_of_ne hkne with hki' | hik'
        next =>
          have hk : key k < m := hki'.trans_eq hi
          rw [ih (key k) hk k rfl (hki'.trans hij), mul_zero]
        next => rw [hSupport i k hik', zero_mul]
      next =>
        intro h
        exact False.elim (h (Finset.mem_univ i))
    have hNe : Not (i = j) := fun h => hij.ne (congrArg key h)
    have hMul := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i j) g.val_inv
    change (g.val * g.inv) i j = (1 : Matrix (Fin n) (Fin n) F) i j at hMul
    rw [hSum, Matrix.one_apply_ne hNe] at hMul
    exact (mul_eq_zero.mp hMul).resolve_left (hDiag i)

/-- Below congruence level one, the inverse preserves any triangular
support indexed by an injective natural-number key. -/
private theorem valuationPrincipalCongruence_inv_order_support
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (n : Nat) (r : V) (hr : r < 1)
    (g : Units (Matrix (Fin n) (Fin n) F))
    (hg : Membership.mem (valuationPrincipalCongruenceSubgroup v n r) g)
    (key : Fin n -> Nat) (hKey : Function.Injective key)
    (hSupport : forall i j, key i < key j -> g.val i j = 0) :
    forall i j, key i < key j -> g.inv i j = 0 := by
  apply inverse_order_support n g key hKey _ hSupport
  intro i hi
  have h := hg.2 i i
  rw [Matrix.sub_apply, Matrix.one_apply_eq] at h
  have hOne := valuation_eq_one_of_sub_one_lt v (g.val i i) (h.trans_lt hr)
  rw [hi, v.map_zero] at hOne
  exact zero_ne_one hOne

/-- Two diagonal elements ordered in the same valuation chamber multiply
their principal congruence double cosets without creating another coset. -/
theorem exists_valuationPrincipalCongruence_doubleCoset_factor_of_ordered
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (n : Nat) (r : V) (hr : r < 1)
    (a b : Units (Fin n -> F))
    (hOrdered : forall i j, i <= j -> v (a.val i) <= v (a.val j))
    (hOrderedB : forall i j, i <= j -> v (b.val i) <= v (b.val j))
    (k : valuationPrincipalCongruenceSubgroup v n r) :
    let K := valuationPrincipalCongruenceSubgroup v n r
    let t := (valuationDiagonalSection F n a).val
    let s := (valuationDiagonalSection F n b).val
    exists u l : K, t * k.val * s = u.val * (t * s) * l.val := by
  intro K t s
  choose upper diagonal lower hFactor using
    exists_valuationPrincipalCongruence_upper_diagonal_lower v n r hr k.val.val k.property.2
  have hk : k.val = upper * diagonal * lower := Units.ext hFactor.1
  let key (i : Fin n) := n - i.val
  have keyInj : Function.Injective key := by
    intro i j h
    apply Fin.ext
    change n - i.val = n - j.val at h
    have hi := i.isLt
    have hj := j.isLt
    omega
  have upperInv (g : Units (Matrix (Fin n) (Fin n) F))
      (hg : Membership.mem K g) (hs : forall i j, j < i -> g.val i j = 0) :
      forall i j, j < i -> g.inv i j = 0 := by
    have hsKey (i j : Fin n) (h : key i < key j) : g.val i j = 0 := by
      apply hs i j
      change n - i.val < n - j.val at h
      change j.val < i.val
      omega
    have hInv := valuationPrincipalCongruence_inv_order_support v n r hr g hg key keyInj hsKey
    intro i j hij
    apply hInv i j
    change n - i.val < n - j.val
    change j.val < i.val at hij
    have hi := i.isLt
    omega
  have lowerInv (g : Units (Matrix (Fin n) (Fin n) F))
      (hg : Membership.mem K g) (hs : forall i j, i < j -> g.val i j = 0) :
      forall i j, i < j -> g.inv i j = 0 :=
    valuationPrincipalCongruence_inv_order_support v n r hr g hg Fin.val Fin.val_injective hs
  have hUp := hFactor.2.2.1
  have hDiag := hFactor.2.2.2.1
  have hLow := hFactor.2.2.2.2
  have hUpMem : Membership.mem K upper := hFactor.2.1.1
  have hDiagMem : Membership.mem K diagonal := hFactor.2.1.2.1
  have hLowMem : Membership.mem K lower := hFactor.2.1.2.2
  have hUpConj : Membership.mem K (t * upper * Inv.inv t) :=
    valuationPrincipalCongruenceSubgroup_conj_of_entrywise_contraction
      v n r a (fun i j => i <= j) le_refl
      (fun i j h => valuation_diagonalEntryRatio_le_one v n a i j (hOrdered i j h))
      upper hUpMem (fun i j h => hUp i j (lt_of_not_ge h))
      (fun i j h => upperInv upper hUpMem hUp i j (lt_of_not_ge h))
  have hDiagInv (i j : Fin n) (h : Not (i = j)) : diagonal.inv i j = 0 := by
    rcases lt_or_gt_of_ne h with hij | hji
    next =>
      exact lowerInv diagonal hDiagMem (fun a b hab => hDiag a b hab.ne) i j hij
    next =>
      exact upperInv diagonal hDiagMem (fun a b hba => hDiag a b hba.ne.symm) i j hji
  have hDiagConj : Membership.mem K (t * diagonal * Inv.inv t) := by
    apply valuationPrincipalCongruenceSubgroup_conj_of_entrywise_contraction
      v n r a (fun i j => i = j) (fun _ => rfl) _ diagonal hDiagMem hDiag hDiagInv
    intro i j h
    subst j
    exact valuation_diagonalEntryRatio_le_one v n a i i le_rfl
  have hInvS : (valuationDiagonalSection F n (Inv.inv b)).val = Inv.inv s := by
    apply Units.ext
    rfl
  have hLowConj : Membership.mem K (Inv.inv s * lower * s) := by
    have hRatio (i j : Fin n) (h : j <= i) :
        v ((Inv.inv b).val i * (Inv.inv b).inv j) <= 1 := by
      change v (b.inv i * b.val j) <= 1
      rw [mul_comm]
      exact valuation_diagonalEntryRatio_le_one v n b j i (hOrderedB j i h)
    have h := valuationPrincipalCongruenceSubgroup_conj_of_entrywise_contraction
      v n r (Inv.inv b) (fun i j => j <= i) le_refl hRatio lower hLowMem
      (fun i j h => hLow i j (lt_of_not_ge h))
      (fun i j h => lowerInv lower hLowMem hLow i j (lt_of_not_ge h))
    change Membership.mem K
      ((valuationDiagonalSection F n (Inv.inv b)).val * lower *
        Inv.inv ((valuationDiagonalSection F n (Inv.inv b)).val)) at h
    simpa only [hInvS, inv_inv] using h
  let u : K := Subtype.mk ((t * upper * Inv.inv t) * (t * diagonal * Inv.inv t))
    (K.mul_mem hUpConj hDiagConj)
  let l : K := Subtype.mk (Inv.inv s * lower * s) hLowConj
  refine Exists.intro u (Exists.intro l ?_)
  change t * k.val * s =
    ((t * upper * Inv.inv t) * (t * diagonal * Inv.inv t)) *
      (t * s) * (Inv.inv s * lower * s)
  simp [hk, mul_assoc]

/-- The ordered diagonal double-coset identity applied to powers of a
single diagonal element. -/
theorem exists_valuationPrincipalCongruence_doubleCoset_factor_pow
    {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
    (v : Valuation F V) (n : Nat) (r : V) (hr : r < 1)
    (a : Units (Fin n -> F))
    (hOrdered : forall i j, i <= j -> v (a.val i) <= v (a.val j))
    (m : Nat) (k : valuationPrincipalCongruenceSubgroup v n r) :
    let K := valuationPrincipalCongruenceSubgroup v n r
    let t := (valuationDiagonalSection F n a).val
    exists u l : K, t * k.val * t ^ m = u.val * (t * t ^ m) * l.val := by
  intro K t
  have hOrderedPow (i j : Fin n) (hij : i <= j) :
      v ((a ^ m).val i) <= v ((a ^ m).val j) := by
    rw [Units.val_pow_eq_pow_val, Pi.pow_apply, Pi.pow_apply, map_pow, map_pow]
    exact pow_le_pow_left' (hOrdered i j hij) m
  have ht : (valuationDiagonalSection F n (a ^ m)).val = t ^ m :=
    map_pow ((valuationUpperTriangularSubgroup F n).subtype.comp
      (valuationDiagonalSection F n)) a m
  have h := exists_valuationPrincipalCongruence_doubleCoset_factor_of_ordered
    v n r hr a (a ^ m) hOrdered hOrderedPow k
  change exists u l : K,
    t * k.val * (valuationDiagonalSection F n (a ^ m)).val =
      u.val * (t * (valuationDiagonalSection F n (a ^ m)).val) * l.val at h
  simpa only [ht] using h

/-- If the last pivot has maximal valuation, integral elementary factors
split off that pivot. The remaining invertible block stays bounded by the
pivot valuation. -/
private theorem exists_valuationIntegralMatrix_maximalLastPivot
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat)
    (g : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (hPivot : Not (g.val (Fin.last n) (Fin.last n) = 0))
    (hMax : forall i j, v (g.val i j) <= v (g.val (Fin.last n) (Fin.last n))) :
    let e : Equiv (Sum (Fin n) (Fin 1)) (Fin (n + 1)) := finSumFinEquiv
    let D : Matrix (Fin 1) (Fin 1) F := Matrix.of (fun _ _ => g.val (Fin.last n) (Fin.last n))
    exists upper lower : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) F),
      exists block : Units (Matrix (Fin n) (Fin n) F),
        And (Membership.mem (valuationIntegralMatrixSubgroup v (n + 1)) upper)
        (And (Membership.mem (valuationIntegralMatrixSubgroup v (n + 1)) lower)
          (And (g.val = upper.val * Matrix.reindexRingEquiv F e
              (Matrix.fromBlocks block.val 0 0 D) * lower.val)
            (forall i j, v (block.val i j) <= v (g.val (Fin.last n) (Fin.last n))))) := by
  intro e D
  let reindex := Matrix.reindexRingEquiv F e
  let M := reindex.symm g.val
  have eLeft (i : Fin n) : e (Sum.inl i) = i.castSucc := by
    apply Fin.ext
    rfl
  have eRight : e (Sum.inr 0) = Fin.last n := by
    apply Fin.ext
    simp [e]
  let A : Matrix (Fin n) (Fin n) F := Matrix.of (fun i j => M (Sum.inl i) (Sum.inl j))
  let b (i : Fin n) := M (Sum.inl i) (Sum.inr 0)
  let c (j : Fin n) := M (Sum.inr 0) (Sum.inl j)
  let pivot := g.val (Fin.last n) (Fin.last n)
  let d := Units.mk0 pivot hPivot
  have hD : M (Sum.inr 0) (Sum.inr 0) = pivot := by
    change g.val (e (Sum.inr 0)) (e (Sum.inr 0)) = _
    rw [eRight]
  have boundM (i j : Sum (Fin n) (Fin 1)) : v (M i j) <= v pivot :=
    hMax (e i) (e j)
  have hRatio (x : F) (hx : v x <= v pivot) : v (x * d.inv) <= 1 := by
    calc
      _ = v x * v d.inv := v.map_mul _ _
      _ <= v d.val * v d.inv := mul_le_mul' hx (le_refl _)
      _ = 1 := by rw [<- v.map_mul, d.val_inv, v.map_one]
  let B : Matrix (Fin n) (Fin 1) F := Matrix.of (fun i _ => b i * d.inv)
  let C : Matrix (Fin 1) (Fin n) F := Matrix.of (fun _ j => d.inv * c j)
  let S : Matrix (Fin n) (Fin n) F := Matrix.of (fun i j => A i j - b i * d.inv * c j)
  have bBound (i : Fin n) : v (b i * d.inv) <= 1 :=
    hRatio (b i) (boundM (Sum.inl i) (Sum.inr 0))
  have hB (i : Fin n) (j : Fin 1) : v (B i j) <= 1 := bBound i
  have hC (i : Fin 1) (j : Fin n) : v (C i j) <= 1 := by
    change v (d.inv * c j) <= 1
    rw [mul_comm]
    exact hRatio (c j) (boundM (Sum.inr 0) (Sum.inl j))
  have boundS (i j : Fin n) : v (S i j) <= v pivot := by
    have hc : v (b i * d.inv * c j) <= v pivot := by
      rw [v.map_mul]
      exact (mul_le_mul' (bBound i) (boundM (Sum.inr 0) (Sum.inl j))).trans_eq
        (one_mul _)
    change v (A i j - b i * d.inv * c j) <= _
    rw [sub_eq_add_neg]
    exact (v.map_add _ _).trans (max_le (boundM (Sum.inl i) (Sum.inl j))
      (by rw [v.map_neg]; exact hc))
  choose upper lower hElim using exists_valuationPrincipalCongruence_lastBlock_elementary
    v n 1 le_rfl B C hB hC
  have hBlock : M = Matrix.fromBlocks A
      (Matrix.of (fun i _ => b i)) (Matrix.of (fun _ j => c j)) D := by
    ext i j
    cases i <;> cases j
    next => rfl
    next =>
      rename_i j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
    next =>
      rename_i i j
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    next =>
      rename_i i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i
      subst j
      exact hD
  have hFactor : g.val = upper.val * reindex (Matrix.fromBlocks S 0 0 D) * lower.val := by
    calc
      _ = reindex M := (reindex.apply_symm_apply _).symm
      _ = reindex (Matrix.fromBlocks 1 B 0 1 * Matrix.fromBlocks S 0 0 D *
          Matrix.fromBlocks 1 0 C 1) :=
        congrArg reindex (hBlock.trans (lastBlock_eq_upper_diagonal_lower n A b c d))
      _ = _ := by rw [hElim.1, hElim.2.1, map_mul, map_mul]
  let mid := Inv.inv upper * g * Inv.inv lower
  have hMid : mid.val = reindex (Matrix.fromBlocks S 0 0 D) := by
    change upper.inv * g.val * lower.inv = _
    rw [hFactor]
    calc
      _ = (upper.inv * upper.val) * reindex (Matrix.fromBlocks S 0 0 D) *
          (lower.val * lower.inv) := by simp only [mul_assoc]
      _ = _ := by rw [upper.inv_val, lower.val_inv, one_mul, mul_one]
  have hEntry (i j : Sum (Fin n) (Fin 1)) :
      mid.val (e i) (e j) = Matrix.fromBlocks S 0 0 D i j := by
    rw [hMid]
    change Matrix.fromBlocks S 0 0 D (e.symm (e i)) (e.symm (e j)) = _
    rw [e.symm_apply_apply, e.symm_apply_apply]
  have hRow (j : Fin n) : mid.val (Fin.last n) j.castSucc = 0 := by
    have h := hEntry (Sum.inr 0) (Sum.inl j)
    rw [eRight, eLeft] at h
    exact h
  have hMidPivot : Not (mid.val (Fin.last n) (Fin.last n) = 0) := by
    have h := hEntry (Sum.inr 0) (Sum.inr 0)
    rw [eRight] at h
    change mid.val (Fin.last n) (Fin.last n) = pivot at h
    rwa [h]
  choose block hCorner using exists_unitUpperLeftCorner_of_lastRow n mid hRow hMidPivot
  have hS : block.val = S := by
    ext i j
    rw [hCorner, <- eLeft i, <- eLeft j]
    exact hEntry (Sum.inl i) (Sum.inl j)
  refine Exists.intro upper (Exists.intro lower (Exists.intro block
    (And.intro hElim.2.2.1.1 (And.intro hElim.2.2.2.1 ?_))))
  rw [hS]
  exact And.intro hFactor boundS

private def valuationPivotPermutationUnit
    {F : Type*} [Field F] {n : Nat} (s : Equiv.Perm (Fin n)) :
    Units (Matrix (Fin n) (Fin n) F) where
  val := s.permMatrix F
  inv := (Inv.inv s).permMatrix F
  val_inv := by rw [<- Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  inv_val := by rw [<- Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

private theorem valuationPivotPermutationUnit_mem
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (s : Equiv.Perm (Fin n)) :
    Membership.mem (valuationIntegralMatrixSubgroup v n) (valuationPivotPermutationUnit s) := by
  apply (mem_valuationIntegralMatrixSubgroup_iff v n _).mpr
  have h (p : Equiv.Perm (Fin n)) (i j : Fin n) : v (p.permMatrix F i j) <= 1 := by
    by_cases hp : p i = j
    next => simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.toPEquiv_apply, hp]
    next =>
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.toPEquiv_apply, hp]
  exact And.intro (h s) (h (Inv.inv s))

/-- Integral row and column operations split off a pivot of maximal
valuation from any invertible matrix of positive rank. -/
private theorem exists_valuationIntegralMatrix_maximalPivot
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat)
    (g : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    let e : Equiv (Sum (Fin n) (Fin 1)) (Fin (n + 1)) := finSumFinEquiv
    exists left right : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) F),
      exists block : Units (Matrix (Fin n) (Fin n) F),
      exists d : Units F,
        And (Membership.mem (valuationIntegralMatrixSubgroup v (n + 1)) left)
        (And (Membership.mem (valuationIntegralMatrixSubgroup v (n + 1)) right)
        (And (g.val = left.val * Matrix.reindexRingEquiv F e
            (Matrix.fromBlocks block.val 0 0 (Matrix.of (fun _ _ => d.val))) * right.val)
        (And (exists i j, d.val = g.val i j)
          (And (forall i j, v (g.val i j) <= v d.val)
            (forall i j, v (block.val i j) <= v d.val))))) := by
  intro e
  let J := Fin (n + 1)
  let pmax : Prod J J -> W := fun p => v (g.val p.1 p.2)
  have hUniv : (Finset.univ : Finset (Prod J J)).Nonempty :=
    Exists.intro (0,0) (Finset.mem_univ _)
  choose p hp using Finset.exists_max_image (Finset.univ : Finset (Prod J J)) pmax hUniv
  have hMax (i j : J) : v (g.val i j) <= v (g.val p.1 p.2) := hp.2 (i,j) (Finset.mem_univ _)
  have hp0 : Not (g.val p.1 p.2 = 0) := by
    intro h0
    have hZero (i j : J) : g.val i j = 0 := by
      have h := hMax i j
      rw [h0, v.map_zero] at h
      have hz := le_antisymm h zero_le
      exact (map_eq_zero v).mp hz
    have hMat : g.val = 0 := by
      ext i j
      exact hZero i j
    have hInv := g.val_inv
    rw [hMat, zero_mul] at hInv
    exact zero_ne_one hInv
  let sl : Equiv.Perm J := Equiv.swap (Fin.last n) p.1
  let sr : Equiv.Perm J := (Equiv.swap (Fin.last n) p.2).symm
  let L : Units (Matrix J J F) := valuationPivotPermutationUnit sl
  let R : Units (Matrix J J F) := valuationPivotPermutationUnit sr
  let gp := L * g * R
  have hEntry (i j : J) : gp.val i j = g.val (sl i) (sr.symm j) := by
    change Matrix.vecMul (fun k => (L.val * g.val) i k) (sr.permMatrix F) j = _
    rw [Matrix.vecMul_permMatrix]
    change Matrix.mulVec (sl.permMatrix F) (fun k => g.val k (sr.symm j)) i = _
    simp only [Matrix.permMatrix_mulVec, Function.comp_apply]
  have hP : gp.val (Fin.last n) (Fin.last n) = g.val p.1 p.2 := by
    rw [hEntry]
    change g.val (Equiv.swap (Fin.last n) p.1 (Fin.last n))
      (Equiv.swap (Fin.last n) p.2 (Fin.last n)) = _
    simp only [Equiv.swap_apply_left]
  have hGpMax (i j : J) : v (gp.val i j) <= v (gp.val (Fin.last n) (Fin.last n)) := by
    rw [hEntry, hP]
    exact hMax (sl i) (sr.symm j)
  have hGpNZ : Not (gp.val (Fin.last n) (Fin.last n) = 0) := by rwa [hP]
  choose upper lower block hFactor using exists_valuationIntegralMatrix_maximalLastPivot
    v n gp hGpNZ hGpMax
  let d := Units.mk0 (gp.val (Fin.last n) (Fin.last n)) hGpNZ
  let K := valuationIntegralMatrixSubgroup v (n + 1)
  have hLeft : Membership.mem K (Inv.inv L * upper) :=
    K.mul_mem (K.inv_mem (valuationPivotPermutationUnit_mem v (n + 1) sl)) hFactor.1
  have hRight : Membership.mem K (lower * Inv.inv R) :=
    K.mul_mem hFactor.2.1 (K.inv_mem (valuationPivotPermutationUnit_mem v (n + 1) sr))
  have hRestore : g.val = L.inv * gp.val * R.inv := by
    change g.val = L.inv * (L.val * g.val * R.val) * R.inv
    calc
      _ = (L.inv * L.val) * g.val * (R.val * R.inv) := by
        rw [L.inv_val, R.val_inv, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  have hProduct : g.val = (Inv.inv L * upper).val * Matrix.reindexRingEquiv F e
      (Matrix.fromBlocks block.val 0 0 (Matrix.of (fun _ _ => d.val))) *
        (lower * Inv.inv R).val := by
    change g.val = (L.inv * upper.val) * Matrix.reindexRingEquiv F e
      (Matrix.fromBlocks block.val 0 0 (Matrix.of (fun _ _ => d.val))) *
        (lower.val * R.inv)
    rw [hRestore, hFactor.2.2.1]
    simp only [mul_assoc]
    rfl
  exact Exists.intro (Inv.inv L * upper) (Exists.intro (lower * Inv.inv R)
    (Exists.intro block (Exists.intro d (And.intro hLeft (And.intro hRight
      (And.intro hProduct (And.intro (Exists.intro p.1 (Exists.intro p.2 hP))
        (And.intro (fun i j => (hMax i j).trans_eq (congrArg v hP).symm) hFactor.2.2.2))))))))

private theorem exists_valuationIntegralMatrix_embedOne
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (g : Units (Matrix (Fin n) (Fin n) F))
    (hg : Membership.mem (valuationIntegralMatrixSubgroup v n) g) :
    let e : Equiv (Sum (Fin n) (Fin 1)) (Fin (n + 1)) := finSumFinEquiv
    exists lifted : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) F),
      And (lifted.val = Matrix.reindexRingEquiv F e (Matrix.fromBlocks g.val 0 0 1))
        (Membership.mem (valuationIntegralMatrixSubgroup v (n + 1)) lifted) := by
  intro e
  have hVal := ((mem_valuationIntegralMatrixSubgroup_iff v n g).mp hg).1
  have hId := ((mem_valuationIntegralMatrixSubgroup_iff v n 1).mp
    (valuationIntegralMatrixSubgroup v n).one_mem).1
  have hDiff (i j : Fin n) : v ((g.val - 1) i j) <= 1 := by
    rw [Matrix.sub_apply, sub_eq_add_neg]
    exact (v.map_add _ _).trans (max_le (hVal i j) (by rw [v.map_neg]; exact hId i j))
  have hMem : Membership.mem (valuationPrincipalCongruenceSubgroup v n 1) g :=
    And.intro hg hDiff
  have hOne : v (1 : F) <= 1 := by rw [v.map_one]
  have hClose : v ((1 : F) - 1) <= 1 := by
    rw [sub_self, v.map_zero]
    exact zero_le
  choose lifted hl using exists_valuationPrincipalCongruence_lastBlock_diagonal
    v n 1 g 1 hMem hOne hOne hClose
  have hScalar : Matrix.of (fun _ _ : Fin 1 => (1 : F)) = 1 := by
    ext i j
    have hji : j = i := Subsingleton.elim _ _
    subst j
    rw [Matrix.one_apply_eq]
    rfl
  exact Exists.intro lifted (And.intro (by simpa only [Units.val_one, hScalar] using hl.1) hl.2.1)

/-- Integral left and right factors give a diagonal representative with
ordered valuations bounded by the original entrywise bound. -/
theorem exists_valuationIntegralMatrix_ordered_doubleDiagonal
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat)
    (g : Units (Matrix (Fin n) (Fin n) F)) (bound : W)
    (hBound : forall i j, v (g.val i j) <= bound) :
    exists left right : Units (Matrix (Fin n) (Fin n) F), exists a : Units (Fin n -> F),
      And (Membership.mem (valuationIntegralMatrixSubgroup v n) left)
      (And (Membership.mem (valuationIntegralMatrixSubgroup v n) right)
      (And (g.val = left.val * Matrix.diagonal a.val * right.val)
      (And (Monotone (fun i => v (a.val i))) (forall i, v (a.val i) <= bound)))) := by
  induction n generalizing bound with
  | zero =>
    have h := (valuationIntegralMatrixSubgroup v 0).one_mem
    refine Exists.intro 1 (Exists.intro 1 (Exists.intro 1
      (And.intro h (And.intro h (And.intro ?_ (And.intro ?_ ?_))))))
    next => ext i; exact Fin.elim0 i
    next => intro i; exact Fin.elim0 i
    next => intro i; exact Fin.elim0 i
  | succ n ih =>
    let e : Equiv (Sum (Fin n) (Fin 1)) (Fin (n + 1)) := finSumFinEquiv
    let reindex := Matrix.reindexRingEquiv F e
    choose outerLeft outerRight block d hPivot using exists_valuationIntegralMatrix_maximalPivot v n g
    choose i j hEntry using hPivot.2.2.2.1
    have hDBound : v d.val <= bound := by
      rw [hEntry]
      exact hBound i j
    choose innerLeft innerRight a hBlock using ih block (v d.val) hPivot.2.2.2.2.2
    choose liftLeft hLiftLeft using exists_valuationIntegralMatrix_embedOne v n innerLeft hBlock.1
    choose liftRight hLiftRight using exists_valuationIntegralMatrix_embedOne v n innerRight hBlock.2.1
    let D : Matrix (Fin 1) (Fin 1) F := Matrix.of (fun _ _ => d.val)
    let appended : Units (Fin (n + 1) -> F) :=
      { val := fun i => Sum.elim a.val (fun _ => d.val) (e.symm i)
        inv := fun i => Sum.elim a.inv (fun _ => d.inv) (e.symm i)
        val_inv := by
          funext i
          change Sum.elim a.val (fun _ => d.val) (e.symm i) *
            Sum.elim a.inv (fun _ => d.inv) (e.symm i) = 1
          cases e.symm i with
          | inl i => exact congrFun a.val_inv i
          | inr i => exact d.val_inv
        inv_val := by
          funext i
          change Sum.elim a.inv (fun _ => d.inv) (e.symm i) *
            Sum.elim a.val (fun _ => d.val) (e.symm i) = 1
          cases e.symm i with
          | inl i => exact congrFun a.inv_val i
          | inr i => exact d.inv_val }
    have hAt (i : Sum (Fin n) (Fin 1)) :
        appended.val (e i) = Sum.elim a.val (fun _ => d.val) i := by
      change Sum.elim a.val (fun _ => d.val) (e.symm (e i)) = _
      rw [e.symm_apply_apply]
    have hInside : reindex (Matrix.fromBlocks block.val 0 0 D) =
        liftLeft.val * reindex (Matrix.fromBlocks (Matrix.diagonal a.val) 0 0 D) *
          liftRight.val := by
      rw [hLiftLeft.1, hLiftRight.1, <- map_mul, <- map_mul]
      simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
        add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, hBlock.2.2.1.symm]
      rfl
    have hDiag : reindex (Matrix.fromBlocks (Matrix.diagonal a.val) 0 0 D) =
        Matrix.diagonal appended.val := by
      have hEntry (i j : Sum (Fin n) (Fin 1)) :
          Matrix.fromBlocks (Matrix.diagonal a.val) 0 0 D i j =
            Matrix.diagonal appended.val (e i) (e j) := by
        by_cases h : i = j
        next =>
          subst j
          rw [Matrix.diagonal_apply_eq, hAt]
          cases i with
          | inl i => exact Matrix.diagonal_apply_eq a.val i
          | inr i => rfl
        next =>
          rw [Matrix.diagonal_apply_ne _ (fun he => h (e.injective he))]
          cases i with
          | inl i =>
            cases j with
            | inl j =>
              exact Matrix.diagonal_apply_ne a.val
                (fun hij => h (congrArg (Sum.inl : Fin n -> Sum (Fin n) (Fin 1)) hij))
            | inr j => rfl
          | inr i =>
            cases j with
            | inl j => rfl
            | inr j =>
              have hEq : i = j := Subsingleton.elim _ _
              subst j
              exact False.elim (h rfl)
      ext i j
      change Matrix.fromBlocks (Matrix.diagonal a.val) 0 0 D (e.symm i) (e.symm j) = _
      have h := hEntry (e.symm i) (e.symm j)
      simpa only [e.apply_symm_apply] using h
    have hOrder : Monotone (fun i => v (appended.val i)) := by
      have atBlock (i j : Sum (Fin n) (Fin 1)) (h : e i <= e j) :
          v (appended.val (e i)) <= v (appended.val (e j)) := by
        rw [hAt, hAt]
        cases i with
        | inl i =>
          cases j with
          | inl j => exact hBlock.2.2.2.1 h
          | inr j => exact hBlock.2.2.2.2 i
        | inr i =>
          cases j with
          | inl j =>
            change n + i.val <= j.val at h
            exact False.elim (by omega)
          | inr j => exact le_rfl
      intro i j hij
      have he : e (e.symm i) <= e (e.symm j) := by simpa only [e.apply_symm_apply] using hij
      simpa only [e.apply_symm_apply] using atBlock (e.symm i) (e.symm j) he
    have hAppBound (i : Fin (n + 1)) : v (appended.val i) <= bound := by
      change v (Sum.elim a.val (fun _ => d.val) (e.symm i)) <= bound
      cases e.symm i with
      | inl i => exact (hBlock.2.2.2.2 i).trans hDBound
      | inr i => exact hDBound
    have hProduct : g.val = (outerLeft * liftLeft).val * Matrix.diagonal appended.val *
        (liftRight * outerRight).val := by
      have hStep : g.val = outerLeft.val * reindex (Matrix.fromBlocks block.val 0 0 D) *
          outerRight.val := hPivot.2.2.1
      rw [hStep, hInside, hDiag]
      simp only [Units.val_mul, mul_assoc]
    let K := valuationIntegralMatrixSubgroup v (n + 1)
    exact Exists.intro (outerLeft * liftLeft) (Exists.intro (liftRight * outerRight)
      (Exists.intro appended (And.intro (K.mul_mem hPivot.1 hLiftLeft.2)
        (And.intro (K.mul_mem hLiftRight.2 hPivot.2.1)
          (And.intro hProduct (And.intro hOrder hAppBound))))))

end Robin1984.GRH
