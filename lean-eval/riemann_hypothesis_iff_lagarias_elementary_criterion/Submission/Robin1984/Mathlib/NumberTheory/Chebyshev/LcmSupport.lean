/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
module

public import Mathlib.NumberTheory.Chebyshev

/-!
# Factorization support of the least common multiple up to a bound

This file identifies the support of the prime factorization of `Nat.lcmUpto n`
with the primes at most `n`.
-/

@[expose] public section

namespace Nat

/-- The prime factorization of `lcmUpto n` is supported exactly on the primes
at most `n`. -/
theorem support_factorization_lcmUpto (n : ℕ) :
    (lcmUpto n).factorization.support = primesLE n := by
  rw [support_factorization, primeFactors_lcmUpto]

end Nat
