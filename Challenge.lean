import Robin1984.ColossallyAbundant.CAProfile
import Robin1984.Public

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
reduction to colossally abundant integers.  Both statements use the same
authoritative public definitions imported by `Solution.lean`.
-/

namespace Robin1984

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
