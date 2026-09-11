import Robin1984.Lagarias.Certificates.All
import Robin1984.Lagarias.Forward
import Robin1984.Lagarias.Reverse

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jeffrey C. Lagarias, An Elementary Problem Equivalent
  to the Riemann Hypothesis (2001), Theorem 1.1.
- Formalization note: The forward implication composes Robin's theorem,
  Lagarias' Lemma 3.1, and the finite certificate; the converse composes
  Lagarias' Lemma 3.2 with the established Robin--Nicolas oscillation.
- PROVENANCE-END
-/

/-! # Lagarias' elementary criterion is equivalent to RH -/

namespace Robin1984

/-- Lagarias (2001), Theorem 1.1. -/
theorem riemannHypothesis_iff_lagariasElementaryCriterion :
    RiemannHypothesis <-> LagariasElementaryCriterion := by
  constructor
  . intro hRH
    unfold LagariasElementaryCriterion
    intro n hn
    by_cases hOne : n = 1
    . subst n
      exact lagariasElementaryCriterion_one
    by_cases hFinite : n <= 5040
    . exact lagarias_finite_two_to_5040 (by omega) hFinite
    . exact lagariasElementaryCriterion_of_riemannHypothesis_of_5040_lt
        hRH (by omega)
  . exact riemannHypothesis_of_lagariasElementaryCriterion

end Robin1984
