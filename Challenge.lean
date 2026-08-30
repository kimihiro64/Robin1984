import Mathlib

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann (1984).
- Formalization note: The retained statement or source-level argument is Robin's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Robin's 1984 criterion for the Riemann hypothesis

This is the small statement surface audited by Palomar Comparator.  The first
theorem is Robin's published equivalence.  The second records the classical
reduction to colossally abundant integers.  All definitions below have their
ordinary number-theoretic meanings and depend only on Mathlib.
-/

namespace Robin1984

/-- The sum of the positive divisors of `n`. -/
noncomputable def sigmaOneNat (n : Nat) : Nat :=
  ArithmeticFunction.sigma 1 n

/-- Robin's inequality
`sigma(n) < exp(gamma) * n * log(log n)` at the integer `n`. -/
noncomputable def robinInequality (n : Nat) : Prop :=
  (sigmaOneNat n : Real) <
    Real.exp Real.eulerMascheroniConstant * (n : Real) *
      Real.log (Real.log (n : Real))

/-- The objective maximized by a colossally abundant integer at parameter
`eps > 0`. -/
noncomputable def caObjective (eps : Real) (n : Nat) : Real :=
  (sigmaOneNat n : Real) / ((n : Real) ^ (1 + eps))

/-- `n` is colossally abundant at parameter `eps` when `eps > 0`, `n > 1`,
and `sigma(k) / k^(1+eps) <= sigma(n) / n^(1+eps)` for every `k > 1`. -/
noncomputable def IsColossallyAbundantWith (n : Nat) (eps : Real) : Prop :=
  0 < eps ∧ 1 < n ∧
    forall k : Nat, 1 < k -> caObjective eps k <= caObjective eps n

/-- Robin's 1984 theorem: the strict divisor-sum inequality above `5040` is
equivalent to Mathlib's Riemann-hypothesis predicate. -/
theorem robin_inequality_iff_riemannHypothesis :
    (forall n : Nat, 5040 < n -> robinInequality n) <->
      RiemannHypothesis := by
  sorry

/-- It is enough, and necessary, to check Robin's inequality on colossally
abundant integers above `5040`. -/
theorem riemannHypothesis_iff_colossallyAbundant_robin :
    RiemannHypothesis <->
      (forall n : Nat, forall eps : Real, 5040 < n ->
        IsColossallyAbundantWith n eps -> robinInequality n) := by
  sorry

end Robin1984
