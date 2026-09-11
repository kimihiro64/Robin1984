/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
module

public import Mathlib.NumberTheory.Chebyshev

/-!
# Finite Mertens products

This file defines the finite product of `1 - 1 / p` over primes up to a real
frontier and records its invariance under replacing that frontier by its
natural floor.
-/

@[expose] public section

namespace Chebyshev

noncomputable section

/-- The finite Mertens product over primes not exceeding the real frontier
`x`. -/
def mertensProduct (x : Real) : Real := by
  classical
  exact Finset.prod (Nat.primesLE (Nat.floor x))
    (fun p => 1 - 1 / (p : Real))

/-- The finite Mertens product is unchanged when a real frontier is replaced
by its natural floor. -/
theorem mertensProduct_natFloor (x : Real) :
    mertensProduct (Nat.floor x : Real) = mertensProduct x := by
  unfold mertensProduct
  simp only [Nat.floor_natCast]

end

end Chebyshev
