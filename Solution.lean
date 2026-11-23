import Mathlib.NumberTheory.LSeries.RiemannZeta
import Robin1984.Equivalence.Theorem
import Robin1984.GRH.CyclotomicFactorization
import Robin1984.GRH.DedekindTriangular
import Robin1984.GRH.StandardAutomorphicFamily
import Robin1984.Lagarias.Theorem
import Robin1984.Public

set_option autoImplicit false

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984) and Jeffrey C. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis (2001).
- Formalization note: The retained statements are Robin's and Lagarias's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Proved solution

The release Comparator checks the three classical equivalences and the
Dirichlet GRH and Dedekind ERH equivalences against `Challenge.lean`.
The supplied-family Grand RH criterion below uses the stated analytic data.
-/

namespace Robin1984

theorem robin_inequality_iff_riemannHypothesis :
    (forall n : Nat, 5040 < n -> robinInequality n) <->
      RiemannHypothesis := by
  exact riemannHypothesis_iff_nativeRobinInequalityAll.symm

theorem riemannHypothesis_iff_colossallyAbundant_robin :
    RiemannHypothesis <->
      (forall n : Nat, forall eps : Real, 5040 < n ->
        IsColossallyAbundantWith n eps -> robinInequality n) := by
  exact riemannHypothesis_iff_colossallyAbundantRobin

theorem riemann_hypothesis_iff_lagarias_elementary_criterion :
    RiemannHypothesis <-> LagariasElementaryCriterion := by
  exact riemannHypothesis_iff_lagariasElementaryCriterion

namespace GRH

universe u

/-! ## Dirichlet GRH and Dedekind ERH -/

/-- The critical-line assertion for every Dirichlet L-function is equivalent
to the corrected ideal Robin inequality in every cyclotomic field. -/
theorem dirichletGRH_iff_cyclotomicCorrectedIdealRobin :
    (forall (modulus : Nat) [NeZero modulus]
      (chi : DirichletCharacter Complex modulus) (s : Complex),
      0 < s.re -> s.re < 1 -> DirichletCharacter.LFunction chi s = 0 ->
        s.re = 1 / 2) <->
    (forall (modulus : Nat) [NeZero modulus],
      CorrectedIdealRobin (CyclotomicField modulus Rat)) := by
  change DirichletGRH <-> _
  refine dirichletGRH_iff_cyclotomicDedekindRH.trans (Iff.intro ?forward ?reverse)
  case forward =>
    intro h modulus _
    exact correctedIdealRobin_of_dedekindRH (CyclotomicField modulus Rat) (h modulus)
  case reverse =>
    intro h modulus _
    exact dedekindRH_of_correctedIdealRobin (CyclotomicField modulus Rat) (h modulus)

/-- Dedekind ERH for every number field is equivalent to the corrected
ideal Robin inequality in every number field. -/
theorem dedekindERH_iff_correctedIdealRobin :
    (forall (K : Type u) [Field K] [NumberField K], DedekindRH K) <->
      (forall (K : Type u) [Field K] [NumberField K], CorrectedIdealRobin K) := by
  refine Iff.intro ?forward ?reverse
  case forward =>
    intro h K _ _
    exact correctedIdealRobin_of_dedekindRH K (h K)
  case reverse =>
    intro h K _ _
    exact dedekindRH_of_correctedIdealRobin K (h K)

/-! ## Grand RH -/

/-- For a supplied standard family, every zero of each pole-cleared completed
L-function lies on the critical line exactly when every paired prime-power
remainder has a square-root upper bound. -/
theorem grandRH_iff_triangularPrimePowerBound {index : Type u} {powers : index -> Type u}
    [forall pi, Countable (powers pi)]
    (family : StandardAutomorphicFamilyData index powers)
    (analytics : HasStandardAutomorphicAnalytics family) :
    (forall (pi : index) (s : Complex), family.completedL pi s = 0 -> s.re = 1 / 2) <->
      (forall pi, StandardFamilyTriangularBound family pi) := by
  let data (pi : index) : GrandRobinEulerData (powers pi) :=
    { normPower := fun i => family.primePowerNorm pi i
      coefficient := family.coefficient pi
      poleOrder := family.poleOrder pi
      poleRemoved := family.poleRemoved pi }
  change CompletedFamilyRH family.completedL <-> forall pi, GrandRobinTriangularBound (data pi)
  exact grandRobinCompletedCriterion_of_eulerProduct
    family.completedL family.equationFactor family.dual data
    family.conductor family.poleOrder family.realShift family.complexShift
    analytics.conductor_pos analytics.real_shift analytics.complex_shift (fun _ => rfl)
    analytics.norm_ge_two analytics.norms_locally_finite analytics.log_derivative_summable
    analytics.ordinary_entire analytics.completed_order_one analytics.euler_product
    analytics.completion analytics.functional_equation

/-! ## Supporting statements -/

/-- In each number field, Dedekind RH is equivalent to the corrected ideal
Robin inequality above a field-dependent norm cutoff. -/
theorem dedekindRH_iff_correctedIdealRobin (K : Type u) [Field K] [NumberField K] :
    DedekindRH K <-> CorrectedIdealRobin K :=
  Iff.intro (correctedIdealRobin_of_dedekindRH K) (dedekindRH_of_correctedIdealRobin K)

end GRH

end Robin1984
