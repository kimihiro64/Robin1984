import Robin1984.Lagarias.Elementary

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jeffrey C. Lagarias, An Elementary Problem Equivalent
  to the Riemann Hypothesis (2001), Lemma 3.2.
- Formalization note: The proof follows Lagarias' harmonic, exponential, and
  logarithmic estimates, with the relaxed explicit constant 24 in place of 7.
- PROVENANCE-END
-/

/-! # The elementary upper estimate in Lagarias' converse -/

namespace Robin1984

private theorem lagarias_div_le_iff_pos {a b c : Real} (hc : 0 < c) :
    a / c <= b <-> a <= b * c := by
  constructor
  . intro h
    calc
      a = (a / c) * c := by field_simp
      _ <= b * c := mul_le_mul_of_nonneg_right h hc.le
  . intro h
    calc
      a / c <= (b * c) / c := div_le_div_of_nonneg_right h hc.le
      _ = b := by field_simp

private theorem lagarias_le_div_iff_pos {a b c : Real} (hc : 0 < c) :
    a <= b / c <-> a * c <= b := by
  constructor
  . intro h
    calc
      a * c <= (b / c) * c := mul_le_mul_of_nonneg_right h hc.le
      _ = b := by field_simp
  . intro h
    calc
      a = (a * c) / c := by field_simp
      _ <= b / c := div_le_div_of_nonneg_right h hc.le

/-- A relaxed-constant form of Lagarias (2001), Lemma 3.2. The paper's
constant 7 is not needed for the equivalence; any fixed constant suffices. -/
theorem lagarias_upper_bound
    {n : Nat} (hn : 20 <= n) :
    (harmonic n : Real) +
        Real.exp (harmonic n : Real) * Real.log (harmonic n : Real) <=
      Real.exp Real.eulerMascheroniConstant * (n : Real) *
          Real.log (Real.log (n : Real)) +
        24 * (n : Real) / Real.log (n : Real) := by
  let N : Real := n
  let L : Real := Real.log N
  let H : Real := harmonic n
  let G : Real := Real.eulerMascheroniConstant
  have hN20 : (20 : Real) <= N := by
    dsimp [N]
    exact_mod_cast hn
  have hNPos : 0 < N := lt_of_lt_of_le (by norm_num) hN20
  have hNOne : 1 < N := lt_of_lt_of_le (by norm_num) hN20
  have hExpTwo : Real.exp 2 < N := by
    have hExpOnePos : 0 < Real.exp 1 := Real.exp_pos 1
    have hExpOneLt : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hSq : Real.exp 1 * Real.exp 1 < 9 := by nlinarith
    rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
    exact hSq.trans_le (by linarith)
  have hLTwo : 2 < L :=
    (Real.lt_log_iff_exp_lt hNPos).2 hExpTwo
  have hLPos : 0 < L := lt_trans (by norm_num) hLTwo
  have hLOne : 1 < L := lt_trans (by norm_num) hLTwo
  have hLogNLeH : L <= H := by
    dsimp [L, H, N]
    have hCast : (n : Real) <= ((n + 1 : Nat) : Real) := by
      exact_mod_cast Nat.le_succ n
    exact (Real.log_le_log hNPos hCast).trans (log_add_one_le_harmonic n)
  have hHPos : 0 < H := by
    exact hLPos.trans_le hLogNLeH
  have hHUpper : H <= L + 1 := by
    dsimp [H, L, N]
    linarith [harmonic_le_one_add_log n]
  have hLogHMono : Real.log H <= Real.log (L + 1) :=
    Real.log_le_log hHPos hHUpper
  have hLFactor : L + 1 = L * (1 + 1 / L) := by
    field_simp
  have hOneInvLPos : 0 < 1 + 1 / L := by positivity
  have hLogOneInvL : Real.log (1 + 1 / L) <= 1 / L := by
    have h := Real.log_le_sub_one_of_pos hOneInvLPos
    linarith
  have hLogHUpper : Real.log H <= Real.log L + 1 / L := by
    rw [hLFactor, Real.log_mul hLPos.ne' hOneInvLPos.ne'] at hLogHMono
    linarith
  have hEulerUpper : H - Real.log (N + 1) < G := by
    have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
    simp only [Real.eulerMascheroniSeq] at h
    simpa [H, N, G, Nat.cast_add, Nat.cast_one] using h
  have hNFactor : N + 1 = N * (1 + 1 / N) := by
    field_simp
  have hOneInvNPos : 0 < 1 + 1 / N := by positivity
  have hLogOneInvN : Real.log (1 + 1 / N) <= 1 / N := by
    have h := Real.log_le_sub_one_of_pos hOneInvNPos
    linarith
  have hLogNOne : Real.log (N + 1) <= L + 1 / N := by
    rw [hNFactor, Real.log_mul hNPos.ne' hOneInvNPos.ne']
    dsimp [L]
    linarith
  have hHPrecise : H <= G + L + 1 / N := by linarith
  have hExpMono : Real.exp H <= Real.exp (G + L + 1 / N) :=
    Real.exp_le_exp.mpr hHPrecise
  have hExpSplit :
      Real.exp (G + L + 1 / N) =
        Real.exp G * N * Real.exp (1 / N) := by
    rw [show G + L + 1 / N = (G + L) + 1 / N by ring,
      Real.exp_add, Real.exp_add]
    dsimp [L]
    rw [Real.exp_log hNPos]
  have hInvNNonneg : 0 <= 1 / N := by positivity
  have hInvNLtOne : 1 / N < 1 := (div_lt_one hNPos).2 hNOne
  have hExpInv : Real.exp (1 / N) <= 1 + 2 / N := by
    have hBasic : Real.exp (1 / N) <= 1 / (1 - 1 / N) :=
      Real.exp_bound_div_one_sub_of_interval hInvNNonneg hInvNLtOne
    have hRational : 1 / (1 - 1 / N) <= 1 + 2 / N := by
      have hDenPos : 0 < 1 - 1 / N := sub_pos.mpr hInvNLtOne
      apply (lagarias_div_le_iff_pos hDenPos).2
      field_simp [hNPos.ne']
      nlinarith
    exact hBasic.trans hRational
  have hExpUpper : Real.exp H <= Real.exp G * N * (1 + 2 / N) := by
    rw [hExpSplit] at hExpMono
    exact hExpMono.trans (mul_le_mul_of_nonneg_left hExpInv
      (mul_nonneg (Real.exp_pos G).le hNPos.le))
  have hHOne : 1 < H := lt_of_lt_of_le hLOne hLogNLeH
  have hLogHNonneg : 0 <= Real.log H := (Real.log_pos hHOne).le
  have hProduct :
      Real.exp H * Real.log H <=
        (Real.exp G * N * (1 + 2 / N)) *
          (Real.log L + 1 / L) :=
    mul_le_mul hExpUpper hLogHUpper hLogHNonneg (by positivity)
  have hGOne : G < 1 :=
    Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  have hExpG : Real.exp G < 3 :=
    (Real.exp_lt_exp.mpr hGOne).trans Real.exp_one_lt_three
  have hLogLLe : Real.log L <= L := by
    have h := Real.log_le_sub_one_of_pos hLPos
    linarith
  have hSeries := Real.sum_le_exp_of_nonneg hLPos.le 3
  norm_num [Finset.sum_range_succ] at hSeries
  rw [Real.exp_log hNPos] at hSeries
  have hLSq : L ^ 2 <= 2 * N := by nlinarith
  have hLLeN : L <= N := by
    have h := Real.log_le_sub_one_of_pos hNPos
    dsimp [L]
    linarith
  have hHError : H <= 3 * N / L := by
    have hHL : H * L <= 3 * N := by nlinarith
    calc
      H = (H * L) * (1 / L) := by field_simp
      _ <= (3 * N) * (1 / L) :=
        mul_le_mul_of_nonneg_right hHL (by positivity)
      _ = 3 * N / L := by ring
  have hErrorOne : Real.exp G * N / L <= 3 * N / L := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hExpG.le hNPos.le) hLPos.le
  have hErrorTwo : 2 * Real.exp G * Real.log L <= 12 * N / L := by
    have hLogLNonneg : 0 <= Real.log L := (Real.log_pos hLOne).le
    have hTwoExpNonneg : 0 <= 2 * Real.exp G := by positivity
    have hStepOne : 2 * Real.exp G * Real.log L <= 2 * Real.exp G * L :=
      mul_le_mul_of_nonneg_left hLogLLe hTwoExpNonneg
    have hStepTwo : 2 * Real.exp G * L <= 6 * L := by
      apply mul_le_mul_of_nonneg_right _ hLPos.le
      nlinarith
    have hMul : (2 * Real.exp G * Real.log L) * L <= 12 * N := by
      calc
        (2 * Real.exp G * Real.log L) * L <=
            (2 * Real.exp G * L) * L :=
          mul_le_mul_of_nonneg_right hStepOne hLPos.le
        _ <= (6 * L) * L := mul_le_mul_of_nonneg_right hStepTwo hLPos.le
        _ = 6 * L ^ 2 := by ring
        _ <= 6 * (2 * N) :=
          mul_le_mul_of_nonneg_left hLSq (by norm_num)
        _ = 12 * N := by ring
    exact (lagarias_le_div_iff_pos hLPos).2 hMul
  have hErrorThree : 2 * Real.exp G / L <= 6 * N / L := by
    apply div_le_div_of_nonneg_right _ hLPos.le
    have hTwoExp : 2 * Real.exp G <= 6 := by
      calc
        2 * Real.exp G <= 2 * 3 :=
          mul_le_mul_of_nonneg_left hExpG.le (by norm_num)
        _ = 6 := by norm_num
    have hSixLe : (6 : Real) <= 6 * N := by
      exact (by norm_num : (6 : Real) <= 6 * 20).trans
        (mul_le_mul_of_nonneg_left hN20 (by norm_num))
    exact hTwoExp.trans hSixLe
  calc
    H + Real.exp H * Real.log H <=
        H + (Real.exp G * N * (1 + 2 / N)) *
          (Real.log L + 1 / L) := by
      simpa only [add_comm] using add_le_add_left hProduct H
    _ = H + Real.exp G * N * Real.log L +
          Real.exp G * N / L + 2 * Real.exp G * Real.log L +
          2 * Real.exp G / L := by
      field_simp
      ring
    _ <= Real.exp G * N * Real.log L + 24 * N / L := by
      have hErrors :
          H + Real.exp G * N / L + 2 * Real.exp G * Real.log L +
              2 * Real.exp G / L <= 24 * N / L := by
        calc
          H + Real.exp G * N / L + 2 * Real.exp G * Real.log L +
              2 * Real.exp G / L <=
              3 * N / L + 3 * N / L + 12 * N / L + 6 * N / L :=
            add_le_add (add_le_add (add_le_add hHError hErrorOne) hErrorTwo)
              hErrorThree
          _ = 24 * N / L := by ring
      calc
        H + Real.exp G * N * Real.log L + Real.exp G * N / L +
            2 * Real.exp G * Real.log L + 2 * Real.exp G / L =
            Real.exp G * N * Real.log L +
              (H + Real.exp G * N / L + 2 * Real.exp G * Real.log L +
                2 * Real.exp G / L) := by ring
        _ <= Real.exp G * N * Real.log L + 24 * N / L :=
          add_le_add_right hErrors _
    _ = Real.exp Real.eulerMascheroniConstant * (n : Real) *
          Real.log (Real.log (n : Real)) +
        24 * (n : Real) / Real.log (n : Real) := by
      rfl

end Robin1984
