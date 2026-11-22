import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Euler product limits via dominated convergence for summable series.
- Formalization note: The finite prime collections are directed by inclusion, so every individual ideal factorization is eventually included with its full support.
- PROVENANCE-END
-/

/-!
# Extending finite Euler products by support

An absolutely summable series indexed by finite factorizations is the
limit of the subseries supported by finite collections of primes.
-/

open Filter

namespace Robin1984.GRH

/-- A finite Euler-factor expansion and absolute summability imply the
full unordered Euler product. The support records the primes used by
each index of the Dirichlet series. -/
theorem hasProd_of_finsetSupportExpansion {P Q : Type*} [DecidableEq P]
    (a : P -> Complex) (support : Q -> Finset P) (c : Q -> Complex)
    (hSum : Summable (fun q => norm (c q)))
    (hFinite : forall S : Finset P, S.prod a =
      tsum (fun q : Q => if support q <= S then c q else 0)) :
    HasProd a (tsum c) := by
  let masked : Finset P -> Q -> Complex :=
    fun S q => if support q <= S then c q else 0
  have hEach (q : Q) : Tendsto (fun S => masked S q) atTop (nhds (c q)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (support q)] with S hS
    exact (if_pos hS).symm
  have hDom : Filter.Eventually (fun S => forall q, norm (masked S q) <= norm (c q)) atTop := by
    refine Filter.Eventually.of_forall (fun S q => ?_)
    by_cases h : support q <= S
    case pos => exact le_of_eq (congrArg norm (if_pos h))
    case neg =>
      change norm (if support q <= S then c q else 0) <= norm (c q)
      rw [if_neg h, norm_zero]
      exact norm_nonneg _
  change Tendsto (fun S : Finset P => S.prod a) atTop (nhds (tsum c))
  exact (tendsto_tsum_of_dominated_convergence hSum hEach hDom).congr'
    (Filter.Eventually.of_forall (fun S => (hFinite S).symm))

end Robin1984.GRH
