import Robin1984.Arithmetic.Definitions
import Robin1984.Arithmetic.RobinBounds
import Robin1984.ColossallyAbundant.CAProfile
import Robin1984.Finite.RobinFiniteStartupComplete
import Robin1984.Finite.RobinTangentExplicitCutoff
import Robin1984.Finite.RobinTangentStartupComplete
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann (1984).
- Formalization note: The retained statement or source-level argument is Robin's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Robin's inequality reduces to colossally abundant integers

The finite exceptions are discharged, not retained as a premise. The right
side quantifies over all positive CA parameters and their actual maximizers.
-/

namespace Robin1984

theorem nativeRobinInequalityAll_iff_colossallyAbundant :
    Robin1984.Core.NativeRobinInequalityAll <->
      (forall n : Nat, forall eps : Real, 5040 < n ->
        IsColossallyAbundantWith n eps -> Robin1984.Core.NativeRobinInequality n) := by
  constructor
  . intro h n _ hn _
    exact h n hn
  . intro h
    apply nativeRobinInequalityAll_iff_tangentCoverage_720720.mpr
    constructor
    . intro n hn hUpper
      exact nativeRobinInequality_finite_startup hn hUpper
    . intro n q hn hLower hCA
      have hCut := tangentCAMaximizer_above_5040_at_startup_cutoff hn
        (robinFrontierCutoff_lt_ca5040To55440Cutoff_of_720720_le hLower) hCA
      exact h q (robinFrontierCutoff n) hCut hCA

end Robin1984
