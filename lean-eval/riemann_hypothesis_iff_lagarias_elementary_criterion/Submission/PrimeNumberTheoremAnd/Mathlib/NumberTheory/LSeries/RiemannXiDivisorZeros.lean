/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Submission.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber
public import Submission.PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-!
# Divisor-indexed zeros of Riemann's xi function

This file gives an ASCII-facing name to the nonzero divisor index of riemannXi
and proves that every indexed divisor value is an actual zero.  The divisor
index retains analytic multiplicity.
-/

@[expose] public section

noncomputable section

open Complex Set

/-- The nonzero xi divisor, indexed with analytic multiplicity. -/
abbrev RiemannXiDivisorZeroIndex : Type :=
  Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)

/-- The complex value carried by a xi divisor index. -/
abbrev riemannXiDivisorZeroValue (p : RiemannXiDivisorZeroIndex) : ℂ :=
  Complex.Hadamard.divisorZeroIndex₀_val p

@[simp]
theorem riemannXiDivisorZeroValue_ne_zero
    (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue p ≠ 0 :=
  Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p

/-- Every nonzero xi divisor index is supported at an actual zero of xi. -/
theorem riemannXiDivisorZeroValue_eq_zero
    (p : RiemannXiDivisorZeroIndex) :
    riemannXi (riemannXiDivisorZeroValue p) = 0 := by
  have hDivisor :
      MeromorphicOn.divisor riemannXi (Set.univ : Set ℂ)
          (riemannXiDivisorZeroValue p) ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support p
  have hOrder :
      analyticOrderNatAt riemannXi (riemannXiDivisorZeroValue p) ≠ 0 := by
    intro hOrderZero
    apply hDivisor
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      differentiable_riemannXi]
    simp [hOrderZero]
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hOrder

/-- ASCII-facing expansion of the completed zeta factor away from zero. -/
theorem completedRiemannZeta_eq_cpow_mul_Gamma_mul_riemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hGamma : Gamma (s / 2) ≠ 0) :
    completedRiemannZeta s =
      (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs0, Gammaℝ_def]
  field_simp [hGamma]

/-- The inverse-square norm weights of the multiplicity-carrying xi divisor
are summable. -/
theorem summable_riemannXiDivisorZero_norm_inv_sq :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)) := by
  simpa using summable_riemannXi_divisorZeroIndex₀_norm_inv_sq

/-- The logarithmic derivative of xi at zero gives Robin's exact zero-sum
value. -/
theorem neg_two_mul_logDeriv_riemannXi_zero_eq :
    (-2 : ℂ) * logDeriv riemannXi 0 =
      (Real.eulerMascheroniConstant : ℂ) + 2 -
        (Real.log (4 * Real.pi) : ℂ) := by
  have hCompletedDeriv :
      HasDerivAt completedRiemannZeta₀
        (deriv completedRiemannZeta₀ 0) 0 :=
    differentiable_completedZeta₀.differentiableAt.hasDerivAt
  have hQuadratic :
      HasDerivAt (fun s : ℂ => s * (s - 1)) (-1) 0 := by
    have hRaw :=
      (hasDerivAt_id (0 : ℂ)).mul
        ((hasDerivAt_id (0 : ℂ)).sub
          (hasDerivAt_const (0 : ℂ) (1 : ℂ)))
    refine
      (hRaw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall ?_)).congr_deriv ?_
    . intro s
      rfl
    . simp [id_eq]
  have hXiDeriv :
      HasDerivAt riemannXi (-completedRiemannZeta₀ 0 / 2) 0 := by
    have hRaw :=
      (((hQuadratic.mul hCompletedDeriv).add
        (hasDerivAt_const (0 : ℂ) (1 : ℂ))).div_const 2)
    refine
      (hRaw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall ?_)).congr_deriv ?_
    . intro s
      rfl
    . ring
  rw [logDeriv_apply, hXiDeriv.deriv, riemannXi_zero,
    completedRiemannZeta₀_zero_eq_one, completedRiemannZeta₀_one]
  rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
  push_cast
  ring
