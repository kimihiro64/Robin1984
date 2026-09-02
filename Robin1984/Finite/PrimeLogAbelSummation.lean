import Robin1984.Mathlib.NumberTheory.Chebyshev.PrimeLogAbel

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

/-- Compatibility alias for the upstream-ready prime-log coefficient. -/
noncomputable abbrev primeLogCoeff : Nat → Real := Chebyshev.primeLogCoeff

/-- Compatibility theorem for the upstream-ready partial-sum identity. -/
theorem sum_primeLogCoeff_Icc_eq_theta (x : Real) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogCoeff n) =
      Chebyshev.theta x :=
  Chebyshev.sum_primeLogCoeff_Icc_eq_theta x

/-- Compatibility theorem for the upstream-ready prime-log Abel identity. -/
theorem primeLogCoeff_abel
    {f : Real → Real} {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt Real f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * primeLogCoeff k =
      f b * Chebyshev.theta b - f a * Chebyshev.theta a -
        ∫ t in Set.Ioc a b, deriv f t * Chebyshev.theta t :=
  Chebyshev.primeLogCoeff_abel ha hab hf_diff hf_int

end

end Robin1984.FiniteSupport
