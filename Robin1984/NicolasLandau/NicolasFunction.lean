import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# Nicolas's finite Mertens function

This is the source-exact arithmetic function in Nicolas 1983, Theorem 3(c),
and Nicolas 2012, equation (1.9).  It is also the oscillating main term used
in Robin 1984, Section 4.
-/

namespace Robin1984

noncomputable section

/-- The finite Mertens product over primes not exceeding the real frontier
`x`. -/
def nicolasMertensProduct (x : Real) : Real := by
  classical
  exact Finset.prod (Nat.primesLE (Nat.floor x))
    (fun p => 1 - 1 / (p : Real))

/-- Nicolas's function
`exp(gamma) * log(theta(x)) * product_{p <= x} (1 - 1/p)`. -/
def nicolasFunction (x : Real) : Real :=
  Real.exp Real.eulerMascheroniConstant *
    Real.log (Chebyshev.theta x) * nicolasMertensProduct x

/-- The signed logarithmic term whose two-sided oscillation is the imported
content of Nicolas 1983, Theorem 3(c). -/
def nicolasLogMertensOscillation (x : Real) : Real :=
  Real.log (nicolasFunction x)


/-- The finite Mertens product is unchanged when a real frontier is replaced
by its natural floor. -/
theorem nicolasMertensProduct_natFloor (x : Real) :
    nicolasMertensProduct (Nat.floor x : Real) = nicolasMertensProduct x := by
  unfold nicolasMertensProduct
  simp only [Nat.floor_natCast]

/-- Nicolas's function is unchanged when a real frontier is replaced by its
natural floor. -/
theorem nicolasFunction_natFloor (x : Real) :
    nicolasFunction (Nat.floor x : Real) = nicolasFunction x := by
  unfold nicolasFunction
  rw [nicolasMertensProduct_natFloor]
  have hTheta :
      Chebyshev.theta (Nat.floor x : Real) = Chebyshev.theta x :=
    (Chebyshev.theta_eq_theta_coe_floor x).symm
  rw [hTheta]

/-- The logarithmic Nicolas oscillation is unchanged when a real frontier is
replaced by its natural floor. -/
theorem nicolasLogMertensOscillation_natFloor (x : Real) :
    nicolasLogMertensOscillation (Nat.floor x : Real) =
      nicolasLogMertensOscillation x := by
  unfold nicolasLogMertensOscillation
  rw [nicolasFunction_natFloor]


end

end Robin1984
