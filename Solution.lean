import Mathlib.NumberTheory.LSeries.RiemannZeta
import Robin1984.Equivalence.Theorem
import Robin1984.GRH.CyclotomicFactorization
import Robin1984.GRH.DedekindTriangular
import Robin1984.GRH.RiemannMultiplicity
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

The Comparator checks the classical, Dirichlet GRH, and Dedekind ERH
headlines listed in its manifest against `Challenge.lean`.
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

/-! ## Classical RH and zero multiplicity -/

section

open MeasureTheory

/-- The signed von Mangoldt remainder with triangular weights and residue one. -/
noncomputable def riemannMultiplicityPrimePowerRemainder (x : Real) : Real :=
  1 / 2 * x - tsum (fun n : Nat =>
    let q : Real := ((max 1 n : Nat) : Real)
    (Set.Ioi q).indicator (fun y : Real =>
      ArithmeticFunction.vonMangoldt n * (1 - q / y)) x)

/-- The logarithmic square-root normalization of the classical arithmetic remainder. -/
noncomputable def riemannMultiplicityLogInput (t : Real) : Complex :=
  if t < 0 then 0 else (Real.exp (-t / 2) : Complex) *
    (riemannMultiplicityPrimePowerRemainder (Real.exp t) : Complex)

/-- The Gaussian smoothing with the two differential factors of the triangular kernel. -/
noncomputable def riemannPrimePowerSmoothing (a t : Real) : Complex :=
  MeasureTheory.integral MeasureTheory.volume (fun v : Real =>
    let g := Real.exp (-(v ^ 2) / (4 * a)) / Real.sqrt (4 * Real.pi * a)
    let k : Real := (v ^ 2 / (4 * a ^ 2) - v / a + 3 / 4 - 1 / (2 * a)) * g
    (k : Complex) * riemannMultiplicityLogInput (t - v))

/-- The long-time mean-square inequality for the classical prime-power remainder. -/
def RiemannPrimePowerMultiplicityInequality : Prop :=
  Filter.limsup (fun T : Real =>
    (Inv.inv (T : Complex) * intervalIntegral
      (fun t => ((norm (riemannPrimePowerSmoothing 1 t) ^ 2 : Real) : Complex))
      0 T MeasureTheory.volume).re) Filter.atTop <=
    Filter.limsup (fun t : Real => (riemannPrimePowerSmoothing 2 t).re) Filter.atTop

/-- **Classical RH and simple zeros.** Under the Riemann hypothesis,
every nontrivial zero of the Riemann zeta function is simple exactly when
the Gaussian-smoothed von Mangoldt remainder satisfies the global
mean-square inequality. -/
theorem riemannRH_iff_globalPrimePowerMultiplicityInequality
    (hRH : RiemannHypothesis) :
    (forall z : Complex, 0 < z.re -> z.re < 1 -> riemannZeta z = 0 ->
      analyticOrderNatAt riemannZeta z = 1) <-> RiemannPrimePowerMultiplicityInequality := by
  have hDef : RiemannPrimePowerMultiplicityInequality = RiemannMultiplicityInequality := rfl
  rw [hDef]
  exact riemannRH_simpleZeros_iff_globalMultiplicityInequality hRH

end

/-! ## Supporting statements -/

/-- In each number field, Dedekind RH is equivalent to the corrected ideal
Robin inequality above a field-dependent norm cutoff. -/
theorem dedekindRH_iff_correctedIdealRobin (K : Type u) [Field K] [NumberField K] :
    DedekindRH K <-> CorrectedIdealRobin K :=
  Iff.intro (correctedIdealRobin_of_dedekindRH K) (dedekindRH_of_correctedIdealRobin K)

end GRH

end Robin1984
