import Submission.PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannXiDivisorZeros

/-!
# Absolute fractional moments of the multiplicity-counted xi divisor

These moments justify integration of the Hadamard series against the
continuous cutoff Mellin test.  They are not substituted for the sharper
inverse-square moment in Robin's final estimate.
-/

noncomputable section

open Complex

theorem summable_riemannXiDivisorZero_norm_inv_rpow
    {a : Real} (ha : 1 < a) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ a) := by
  have hMid : (1 : Real) < (1 + a) / 2 := by linarith
  have hMidNonneg : (0 : Real) <= (1 + a) / 2 := by linarith
  have hMidLt : (1 + a) / 2 < a := by linarith
  exact Complex.Hadamard.summable_norm_inv_rpow_divisorZeroIndex₀_of_growth
    hMidNonneg hMidLt differentiable_riemannXi riemannXi_nontrivial
    (riemannXi_entireOfOrderAtMost_one.exists_log_growth hMid hMidNonneg)
