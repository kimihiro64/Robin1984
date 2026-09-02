/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
module

public import Robin1984.Mathlib.NumberTheory.Chebyshev.PrimeLogAbel

/-!
# Abel summation for reciprocal squares over primes

This file specializes the prime-log Abel identity to the kernel
`x ↦ 1 / (x ^ 2 * log x)` and rewrites its derivative as a positive tail
kernel.
-/

@[expose] public section

open Finset MeasureTheory

namespace Chebyshev

noncomputable section

/-- Kernel that converts the prime-log coefficient into reciprocal squares. -/
noncomputable def primeSquareKernel (x : Real) : Real :=
  1 / (x ^ 2 * Real.log x)

/-- Positive kernel obtained from `-d/dt (1/(t^2 log t))`. -/
noncomputable def primeSquareTailKernel (x : Real) : Real :=
  (2 * Real.log x + 1) / (x ^ 3 * Real.log x ^ 2)

theorem primeSquareKernel_mul_primeLogCoeff (n : Nat) :
    primeSquareKernel n * primeLogCoeff n =
      if Nat.Prime n then (n : Real)⁻¹ ^ 2 else 0 := by
  by_cases hp : Nat.Prime n
  · have hnpos : 0 < (n : Real) := by exact_mod_cast hp.pos
    have hn : (n : Real) ≠ 0 := ne_of_gt hnpos
    have hlog : Real.log (n : Real) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
    simp [primeSquareKernel, primeLogCoeff, hp, div_eq_mul_inv]
    field_simp [hn, hlog]
  · simp [primeSquareKernel, primeLogCoeff, hp]

/-- The Abel left-hand side for `1/(t^2 log t)` is the reciprocal-square prime sum. -/
theorem sum_primeSquareKernel_mul_primeLogCoeff (s : Finset Nat) :
    (∑ n ∈ s, primeSquareKernel n * primeLogCoeff n) =
      ∑ n ∈ s with Nat.Prime n, (n : Real)⁻¹ ^ 2 := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeSquareKernel_mul_primeLogCoeff n]

theorem differentiableAt_primeSquareKernel (x : Real)
    (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    DifferentiableAt Real primeSquareKernel x := by
  have hden : x ^ 2 * Real.log x ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx) hlog
  have hdiff :
      DifferentiableAt Real (fun y : Real => y ^ 2 * Real.log y) x := by
    exact (differentiableAt_id.pow 2).mul (Real.differentiableAt_log hx)
  have hfun : primeSquareKernel =
      (fun y : Real => Inv.inv (y ^ 2 * Real.log y)) := by
    funext y
    unfold primeSquareKernel
    rw [one_div]
  rw [hfun]
  exact hdiff.inv hden

/-- Derivative of the reciprocal-square Abel kernel on the nonsingular region. -/
theorem deriv_primeSquareKernel (x : Real)
    (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    deriv primeSquareKernel x =
      - (2 * Real.log x + 1) / (x ^ 3 * Real.log x ^ 2) := by
  have hden : x ^ 2 * Real.log x ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx) hlog
  have hdiff :
      DifferentiableAt Real (fun y : Real => y ^ 2 * Real.log y) x := by
    exact (differentiableAt_id.pow 2).mul (Real.differentiableAt_log hx)
  have hsq : HasDerivAt (fun y : Real => y ^ 2) (2 * x) x := by
    refine ((hasDerivAt_id' x).pow 2).congr_deriv ?_
    ring
  have hden_deriv :
      HasDerivAt (fun y : Real => y ^ 2 * Real.log y)
        (x * (2 * Real.log x + 1)) x := by
    refine (hsq.mul (Real.hasDerivAt_log hx)).congr_deriv ?_
    field_simp [hx]
  have hfun : primeSquareKernel =
      (fun y : Real => Inv.inv (y ^ 2 * Real.log y)) := by
    funext y
    unfold primeSquareKernel
    rw [one_div]
  rw [hfun]
  rw [deriv_fun_inv'' hdiff hden, hden_deriv.deriv]
  field_simp [hx, hlog]

theorem deriv_primeSquareKernel_eq_neg_tailKernel (x : Real)
    (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    deriv primeSquareKernel x = -primeSquareTailKernel x := by
  rw [deriv_primeSquareKernel x hx hlog]
  simp [primeSquareTailKernel]
  ring

theorem continuousAt_primeSquareTailKernel {x : Real}
    (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    ContinuousAt primeSquareTailKernel x := by
  change ContinuousAt
    (fun y : Real =>
      (2 * Real.log y + 1) / (y ^ 3 * Real.log y ^ 2)) x
  have hden : x ^ 3 * Real.log x ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hx) (pow_ne_zero 2 hlog)
  exact
    (((Real.continuousAt_log hx).const_mul 2).add continuousAt_const).div
      ((continuousAt_id.pow 3).mul ((Real.continuousAt_log hx).pow 2))
      hden

theorem continuousOn_primeSquareTailKernel {a b : Real} (ha : 1 < a) :
    ContinuousOn primeSquareTailKernel (Set.Icc a b) := by
  intro x hx
  have hx_gt_one : 1 < x := lt_of_lt_of_le ha hx.1
  have hx_pos : 0 < x := lt_trans zero_lt_one hx_gt_one
  exact (continuousAt_primeSquareTailKernel
    (ne_of_gt hx_pos)
    (ne_of_gt (Real.log_pos hx_gt_one))).continuousWithinAt

theorem integrableOn_deriv_primeSquareKernel_Icc {a b : Real} (ha : 1 < a) :
    IntegrableOn (deriv primeSquareKernel) (Set.Icc a b) := by
  have hK :
      IntegrableOn (fun t : Real => -primeSquareTailKernel t)
        (Set.Icc a b) :=
    (continuousOn_primeSquareTailKernel (a := a) (b := b) ha).neg.integrableOn_Icc
  refine hK.congr_fun ?_ measurableSet_Icc
  intro x hx
  have hx_gt_one : 1 < x := lt_of_lt_of_le ha hx.1
  have hx_pos : 0 < x := lt_trans zero_lt_one hx_gt_one
  rw [deriv_primeSquareKernel_eq_neg_tailKernel x
    (ne_of_gt hx_pos) (ne_of_gt (Real.log_pos hx_gt_one))]

/-- Abel summation for reciprocal squares over primes. -/
theorem primeSquareKernel_abel
    {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hk_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt Real primeSquareKernel t)
    (hk_int : IntegrableOn (deriv primeSquareKernel) (Set.Icc a b)) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime k, (k : Real)⁻¹ ^ 2) =
      primeSquareKernel b * theta b -
        primeSquareKernel a * theta a -
          ∫ t in Set.Ioc a b, deriv primeSquareKernel t * theta t := by
  rw [← sum_primeSquareKernel_mul_primeLogCoeff
    (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊)]
  exact primeLogCoeff_abel ha hab hk_diff hk_int

/-- Reciprocal-square Abel identity on intervals past `1`. -/
theorem primeSquareKernel_abel_gt_one
    {a b : Real}
    (ha : 1 < a) (hab : a ≤ b)
    (hk_int : IntegrableOn (deriv primeSquareKernel) (Set.Icc a b)) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime k, (k : Real)⁻¹ ^ 2) =
      primeSquareKernel b * theta b -
        primeSquareKernel a * theta a -
          ∫ t in Set.Ioc a b, deriv primeSquareKernel t * theta t := by
  refine primeSquareKernel_abel (le_trans zero_le_one ha.le) hab ?_ hk_int
  intro t ht
  have ht_gt_one : 1 < t := lt_of_lt_of_le ha ht.1
  have ht_pos : 0 < t := lt_trans zero_lt_one ht_gt_one
  exact differentiableAt_primeSquareKernel t
    (ne_of_gt ht_pos)
    (ne_of_gt (Real.log_pos ht_gt_one))

/-- Abel summation for reciprocal squares with the positive tail kernel displayed. -/
theorem primeSquareKernel_abel_tailKernel_form
    {a b : Real}
    (ha : 1 < a) (hab : a ≤ b)
    (hk_int : IntegrableOn (deriv primeSquareKernel) (Set.Icc a b)) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime k, (k : Real)⁻¹ ^ 2) =
      primeSquareKernel b * theta b -
        primeSquareKernel a * theta a +
          ∫ t in Set.Ioc a b, primeSquareTailKernel t * theta t := by
  have hAbel := primeSquareKernel_abel_gt_one ha hab hk_int
  have hDerivInt :
      (∫ t in Set.Ioc a b, deriv primeSquareKernel t * theta t) =
        -∫ t in Set.Ioc a b, primeSquareTailKernel t * theta t := by
    rw [← integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht_gt_one : 1 < t := lt_trans ha ht.1
    have ht_pos : 0 < t := lt_trans zero_lt_one ht_gt_one
    change deriv primeSquareKernel t * theta t =
      -(primeSquareTailKernel t * theta t)
    rw [deriv_primeSquareKernel_eq_neg_tailKernel t
      (ne_of_gt ht_pos) (ne_of_gt (Real.log_pos ht_gt_one))]
    ring
  rw [hDerivInt] at hAbel
  linarith

/-- Abel summation for reciprocal squares on finite intervals past `1`. -/
theorem primeSquareKernel_abel_tailKernel_form_finite
    {a b : Real} (ha : 1 < a) (hab : a ≤ b) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime k, (k : Real)⁻¹ ^ 2) =
      primeSquareKernel b * theta b -
        primeSquareKernel a * theta a +
          ∫ t in Set.Ioc a b, primeSquareTailKernel t * theta t :=
  primeSquareKernel_abel_tailKernel_form
    ha hab (integrableOn_deriv_primeSquareKernel_Icc (a := a) (b := b) ha)

end

end Chebyshev
