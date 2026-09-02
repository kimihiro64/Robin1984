import Robin1984.Finite.PrimeLogAbelSummation
import Robin1984.Mathlib.NumberTheory.Chebyshev.PrimeSquareAbel

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# Prime-square Abel identity

The finite estimate uses a lower bound for the two-layer contribution

```text
theta(P_2)/sqrt(P)
  + sqrt(P) log(P) * sum_{P_2 < q <= P} -log(1-q^-2).
```

The numerical lower bound starts by controlling `sum q^-2` with Abel
summation.  This file proves the corresponding finite identity.
-/

namespace Robin1984.FiniteSupport

open Finset
open MeasureTheory

noncomputable section

/-- Compatibility alias for the upstream-ready reciprocal-square kernel. -/
noncomputable abbrev primeSquareKernel : Real → Real :=
  Chebyshev.primeSquareKernel

/-- Compatibility alias for the upstream-ready positive tail kernel. -/
noncomputable abbrev primeSquareTailKernel : Real → Real :=
  Chebyshev.primeSquareTailKernel

theorem primeSquareKernel_mul_primeLogCoeff (n : Nat) :
    primeSquareKernel n * primeLogCoeff n =
      if Nat.Prime n then (n : Real)⁻¹ ^ 2 else 0 :=
  Chebyshev.primeSquareKernel_mul_primeLogCoeff n

theorem sum_primeSquareKernel_mul_primeLogCoeff
    (s : Finset Nat) :
    (∑ n ∈ s, primeSquareKernel n * primeLogCoeff n) =
      ∑ n ∈ s with Nat.Prime n, (n : Real)⁻¹ ^ 2 :=
  Chebyshev.sum_primeSquareKernel_mul_primeLogCoeff s

theorem differentiableAt_primeSquareKernel (x : Real)
    (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    DifferentiableAt Real primeSquareKernel x :=
  Chebyshev.differentiableAt_primeSquareKernel x hx hlog

theorem deriv_primeSquareKernel (x : Real)
    (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    deriv primeSquareKernel x =
      -(2 * Real.log x + 1) / (x ^ 3 * Real.log x ^ 2) :=
  Chebyshev.deriv_primeSquareKernel x hx hlog

theorem deriv_primeSquareKernel_eq_neg_tailKernel (x : Real)
    (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    deriv primeSquareKernel x = -primeSquareTailKernel x :=
  Chebyshev.deriv_primeSquareKernel_eq_neg_tailKernel x hx hlog

theorem continuousAt_primeSquareTailKernel {x : Real}
    (hx : x ≠ 0) (hlog : Real.log x ≠ 0) :
    ContinuousAt primeSquareTailKernel x :=
  Chebyshev.continuousAt_primeSquareTailKernel hx hlog

theorem continuousOn_primeSquareTailKernel
    {a b : Real} (ha : 1 < a) :
    ContinuousOn primeSquareTailKernel (Set.Icc a b) :=
  Chebyshev.continuousOn_primeSquareTailKernel ha

theorem integrableOn_deriv_primeSquareKernel_Icc
    {a b : Real} (ha : 1 < a) :
    IntegrableOn (deriv primeSquareKernel) (Set.Icc a b) :=
  Chebyshev.integrableOn_deriv_primeSquareKernel_Icc ha

theorem primeSquareKernel_abel
    {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hk_diff :
      ∀ t ∈ Set.Icc a b, DifferentiableAt Real primeSquareKernel t)
    (hk_int : IntegrableOn (deriv primeSquareKernel) (Set.Icc a b)) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime k, (k : Real)⁻¹ ^ 2) =
      primeSquareKernel b * Chebyshev.theta b -
        primeSquareKernel a * Chebyshev.theta a -
          ∫ t in Set.Ioc a b, deriv primeSquareKernel t * Chebyshev.theta t :=
  Chebyshev.primeSquareKernel_abel ha hab hk_diff hk_int

theorem primeSquareKernel_abel_gt_one
    {a b : Real}
    (ha : 1 < a) (hab : a ≤ b)
    (hk_int : IntegrableOn (deriv primeSquareKernel) (Set.Icc a b)) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime k, (k : Real)⁻¹ ^ 2) =
      primeSquareKernel b * Chebyshev.theta b -
        primeSquareKernel a * Chebyshev.theta a -
          ∫ t in Set.Ioc a b, deriv primeSquareKernel t * Chebyshev.theta t :=
  Chebyshev.primeSquareKernel_abel_gt_one ha hab hk_int

theorem primeSquareKernel_abel_tailKernel_form
    {a b : Real}
    (ha : 1 < a) (hab : a ≤ b)
    (hk_int : IntegrableOn (deriv primeSquareKernel) (Set.Icc a b)) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime k, (k : Real)⁻¹ ^ 2) =
      primeSquareKernel b * Chebyshev.theta b -
        primeSquareKernel a * Chebyshev.theta a +
          ∫ t in Set.Ioc a b,
            primeSquareTailKernel t * Chebyshev.theta t :=
  Chebyshev.primeSquareKernel_abel_tailKernel_form ha hab hk_int

theorem primeSquareKernel_abel_tailKernel_form_finite
    {a b : Real}
    (ha : 1 < a) (hab : a ≤ b) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime k, (k : Real)⁻¹ ^ 2) =
      primeSquareKernel b * Chebyshev.theta b -
        primeSquareKernel a * Chebyshev.theta a +
          ∫ t in Set.Ioc a b,
            primeSquareTailKernel t * Chebyshev.theta t :=
  Chebyshev.primeSquareKernel_abel_tailKernel_form_finite ha hab

end

end Robin1984.FiniteSupport
