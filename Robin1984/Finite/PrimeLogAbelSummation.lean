import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.NumberTheory.Chebyshev

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# Abel summation for the prime-log coefficient

The partial sums of the prime-log coefficient are Chebyshev's theta function.
This identifies the coefficient sequence needed to specialize Mathlib's Abel
summation theorem.
-/

namespace Robin1984.FiniteSupport

open Finset
open MeasureTheory

noncomputable section

/-- Coefficient sequence whose partial sums are Chebyshev theta. -/
noncomputable def primeLogCoeff (n : Nat) : Real :=
  if Nat.Prime n then Real.log (n : Real) else 0


/-- Partial sums of `primeLogCoeff` are exactly `Chebyshev.theta`. -/
theorem sum_primeLogCoeff_Icc_eq_theta (x : Real) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogCoeff n) =
      Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp [primeLogCoeff, Finset.sum_filter]

/-- Abel summation specialized to the prime-log coefficient.  The analytic
choice `f(t)=1/(t log t)` will turn the left side into a reciprocal-prime
sum; this theorem keeps `f` abstract so the first bridge stays lightweight. -/
theorem primeLogCoeff_abel
    {f : Real → Real} {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * primeLogCoeff k =
      f b * Chebyshev.theta b - f a * Chebyshev.theta a -
        ∫ t in Set.Ioc a b, deriv f t * Chebyshev.theta t := by
  rw [sum_mul_eq_sub_sub_integral_mul primeLogCoeff ha hab hf_diff hf_int]
  rw [sum_primeLogCoeff_Icc_eq_theta b, sum_primeLogCoeff_Icc_eq_theta a]
  have hInt :
      ∫ t in Set.Ioc a b,
          deriv f t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogCoeff k) =
        ∫ t in Set.Ioc a b, deriv f t * Chebyshev.theta t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t _ht
    change deriv f t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogCoeff k) =
      deriv f t * Chebyshev.theta t
    rw [sum_primeLogCoeff_Icc_eq_theta t]
  rw [hInt]


end

end Robin1984.FiniteSupport
