import Robin1984.Arithmetic.Definitions
import Robin1984.ColossallyAbundant.CAProfile
import Robin1984.ColossallyAbundant.CAReduction
import Robin1984.Equivalence.Equivalence
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann (1984).
- Formalization note: The retained statement or source-level argument is Robin's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Robin's theorem and its colossally-abundant reduction

The inequality aliases below use mathlib's divisor sum and Euler constant.
Both directions and all finite exceptions are proved in the source modules.
-/

namespace Robin1984

abbrev NativeRobinInequality : Nat -> Prop :=
  Robin1984.Core.NativeRobinInequality


/-- Mathlib's RH predicate is equivalent to the restriction to colossally
abundant integers above the exceptional cutoff. -/
theorem riemannHypothesis_iff_colossallyAbundantRobin :
    RiemannHypothesis <->
      (forall n : Nat, forall eps : Real, 5040 < n ->
        IsColossallyAbundantWith n eps -> NativeRobinInequality n) :=
  riemannHypothesis_iff_nativeRobinInequalityAll.trans
    nativeRobinInequalityAll_iff_colossallyAbundant

end Robin1984
