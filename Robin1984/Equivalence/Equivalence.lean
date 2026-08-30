import Robin1984.Arithmetic.Definitions
import Robin1984.Equivalence.LargeHeightRobin
import Robin1984.Finite.FiniteComplete
import Robin1984.NicolasLandau.NicolasLandauRobinBridge
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann (1984).
- Formalization note: The retained statement or source-level argument is Robin's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Robin's 1984 equivalence

The finite range is unconditional. RH -> Robin uses RH only for the analytic tail.
Robin -> RH is the proved Nicolas-Landau oscillation argument.
-/

namespace Robin1984

theorem nativeRobinInequalityAll_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Robin1984.Core.NativeRobinInequalityAll := by
  intro n hn
  by_cases hLarge : 100000 <= Real.log (n : Real)
  . exact nativeRobinInequality_of_RH_large_log hRH hLarge
  . exact nativeRobinInequality_finite_log hn (lt_of_not_ge hLarge)


theorem riemannHypothesis_iff_nativeRobinInequalityAll :
    RiemannHypothesis <-> Robin1984.Core.NativeRobinInequalityAll :=
  Iff.intro nativeRobinInequalityAll_of_riemannHypothesis
    riemannHypothesis_of_nativeRobinInequalityAll

end Robin1984
