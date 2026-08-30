import Robin1984.Helpers.Lyapunov

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# Exact initial prime-tower support

The transition residence theorem starts after the terminal base packet.  This
module keeps the lower-layer events already active at that base explicit.
Their complete gain, together with the actual factorization tower tail, is
exactly the tower reserve of `lcmUpto P`.  Splitting the active gain into the
full lower-layer contribution and the exact prime-power correction is also an
equality, so no prime in `(sqrt P, P]` is assigned exponent one by an auxiliary
approximation.
-/

namespace Robin1984

noncomputable section

theorem factorization_lcmUpto_support_eq_primesUpToSet (P : Nat) :
    (Nat.lcmUpto P).factorization.support = Robin1984.primesUpToSet P := by
  rw [Nat.support_factorization, Nat.primeFactors_lcmUpto]
  ext p
  simp [Robin1984.primesUpToSet, Nat.mem_primesLE]


end

end Robin1984
