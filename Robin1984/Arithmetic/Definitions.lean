import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann (1984).
- Formalization note: The retained statement or source-level argument is Robin's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Core Robin definitions

This module gives the divisor sum, Robin's pointwise inequality, and its
quantified form above the exceptional cutoff `5040`.
-/

namespace Robin1984.Core

/-- Sum of divisors `sigma(n)`, using Mathlib's arithmetic-function definition. -/
noncomputable def sigmaOneNat (n : Nat) : Nat :=
  ArithmeticFunction.sigma 1 n

/-- Robin's inequality for a single natural number. -/
noncomputable def NativeRobinInequality (n : Nat) : Prop :=
  (sigmaOneNat n : Real) <
    Real.exp Real.eulerMascheroniConstant * (n : Real) *
      Real.log (Real.log (n : Real))

/-- Robin's inequality for every natural number greater than `5040`. -/
noncomputable def NativeRobinInequalityAll : Prop :=
  forall n : Nat, 5040 < n -> NativeRobinInequality n


end Robin1984.Core
