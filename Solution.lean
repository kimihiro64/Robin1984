import Mathlib.NumberTheory.LSeries.RiemannZeta
import Robin1984.Equivalence.Theorem
import Robin1984.GRH.CyclotomicFactorization
import Robin1984.GRH.DedekindTriangular
import Robin1984.GRH.DirichletMultiplicity
import Robin1984.GRH.RiemannMultiplicity
import Robin1984.GRH.StandardAutomorphicFamily
import Robin1984.GRH.StandardAutomorphicMultiplicity
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

/-- **Grand RH for a standard family and triangular prime powers.**
For a standard family with the stated analytic data, every nontrivial
zero of every member lies on the critical line if and only if each
member's triangular prime-power remainder has an eventual square-root
upper bound. The project constructs the standard family in rank one
over every number field. -/
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
  1 / (Nat.cast 2 : Real) * x - tsum (fun n : Nat =>
    let q : Real := ((max 1 n : Nat) : Real)
    (Set.Ioi q).indicator (fun y : Real =>
      ArithmeticFunction.vonMangoldt n * (1 - q / y)) x)

/-- The logarithmic square-root normalization of the classical arithmetic remainder. -/
noncomputable def riemannMultiplicityLogInput (t : Real) : Complex :=
  if t < 0 then 0 else (Real.exp (-t / (Nat.cast 2 : Real)) : Complex) *
    (riemannMultiplicityPrimePowerRemainder (Real.exp t) : Complex)

/-- The Gaussian smoothing with the two differential factors of the triangular kernel. -/
noncomputable def riemannPrimePowerSmoothing (a t : Real) : Complex :=
  MeasureTheory.integral MeasureTheory.volume (fun v : Real =>
    let g := Real.exp (-(v ^ 2) / ((Nat.cast 4 : Real) * a)) / Real.sqrt ((Nat.cast 4 : Real) * Real.pi * a)
    let k : Real := (v ^ 2 / ((Nat.cast 4 : Real) * a ^ 2) - v / a + (Nat.cast 3 : Real) / (Nat.cast 4 : Real) - 1 / ((Nat.cast 2 : Real) * a)) * g
    (k : Complex) * riemannMultiplicityLogInput (t - v))

/-- The long-time mean-square inequality for the classical prime-power remainder. -/
def RiemannPrimePowerMultiplicityInequality : Prop :=
  Filter.limsup (fun T : Real =>
    (Inv.inv (T : Complex) * intervalIntegral
      (fun t => ((norm (riemannPrimePowerSmoothing 1 t) ^ 2 : Real) : Complex))
      0 T MeasureTheory.volume).re) Filter.atTop <=
    Filter.limsup (fun t : Real => (riemannPrimePowerSmoothing (Nat.cast 2 : Real) t).re) Filter.atTop

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

/-! ## Dirichlet GRH and zero multiplicity -/

section

open MeasureTheory
open scoped Classical

/-- The Gaussian smoothing of a square-root normalized prime-power signal. -/
noncomputable def primePowerGaussianSmoothing (A : Real -> Complex) (a t : Real) : Complex :=
  MeasureTheory.integral MeasureTheory.volume (fun v : Real =>
    let g := Real.exp (-(v ^ 2) / ((Nat.cast 4 : Real) * a)) / Real.sqrt ((Nat.cast 4 : Real) * Real.pi * a)
    let k : Real := (v ^ 2 / ((Nat.cast 4 : Real) * a ^ 2) - v / a + (Nat.cast 3 : Real) / (Nat.cast 4 : Real) - 1 / ((Nat.cast 2 : Real) * a)) * g
    (k : Complex) * A (t - v))

/-- The global mean-square inequality for a prime-power signal. -/
def PrimePowerGaussianInequality (A : Real -> Complex) : Prop :=
  Filter.limsup (fun T : Real =>
    (Inv.inv (T : Complex) * intervalIntegral
      (fun t => ((norm (primePowerGaussianSmoothing A 1 t) ^ 2 : Real) : Complex))
      0 T MeasureTheory.volume).re) Filter.atTop <=
    Filter.limsup (fun t : Real => (primePowerGaussianSmoothing A (Nat.cast 2 : Real) t).re) Filter.atTop

/-- The signed triangular remainder with the twisted von Mangoldt coefficients. -/
noncomputable def dirichletMultiplicityPrimePowerRemainder {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (x : Real) : Complex :=
  let m : Real := if chi = 1 then 1 else 0
  ((m / (Nat.cast 2 : Real) : Real) : Complex) * (x : Complex) -
    tsum (fun n : Nat =>
      let q : Real := ((max 1 n : Nat) : Real)
      (Set.Ioi q).indicator (fun y : Real =>
        (chi (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : Complex)) *
          (1 - (q : Complex) / (y : Complex))) x)

/-- The normalized Dirichlet remainder extended by zero to negative log time. -/
noncomputable def dirichletMultiplicityLogInput {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (t : Real) : Complex :=
  if t < 0 then 0 else (Real.exp (-t / (Nat.cast 2 : Real)) : Complex) *
    dirichletMultiplicityPrimePowerRemainder chi (Real.exp t)

/-- The arithmetic multiplicity inequality for an individual Dirichlet L-function. -/
def DirichletPrimePowerMultiplicityInequality {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) : Prop :=
  PrimePowerGaussianInequality (dirichletMultiplicityLogInput chi)

/-- **Dirichlet GRH and simple zeros.** Under Dirichlet GRH, every
nontrivial zero of every Dirichlet L-function is simple exactly when each
character satisfies the global Gaussian-smoothed prime-power inequality. -/
theorem dirichletGRH_iff_globalPrimePowerMultiplicityInequality (hGRH : DirichletGRH) :
    (forall (N : Nat) [NeZero N] (chi : DirichletCharacter Complex N) (z : Complex),
      0 < z.re -> z.re < 1 -> DirichletCharacter.LFunction chi z = 0 ->
        analyticOrderNatAt (DirichletCharacter.LFunction chi) z = 1) <->
    (forall (N : Nat) [NeZero N] (chi : DirichletCharacter Complex N),
      DirichletPrimePowerMultiplicityInequality chi) := by
  have hDef (N : Nat) [NeZero N] (chi : DirichletCharacter Complex N) :
      DirichletPrimePowerMultiplicityInequality chi = DirichletMultiplicityInequality chi := rfl
  simp only [hDef]
  exact dirichletGRH_simpleZeros_iff_globalMultiplicityInequality hGRH

end

/-! ## Dedekind ERH and zero multiplicity -/

section

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical

/-- The signed triangular signal on the logarithmic scale. The sum ranges
over powers of nonzero prime ideals of the given field. -/
noncomputable def dedekindPrimeIdealMultiplicitySignal
    (K : Type u) [Field K] [NumberField K] (t : Real) : Complex :=
  if t < 0 then 0 else
    let x := Real.exp t
    (Real.exp (-t / (Nat.cast 2 : Real)) : Complex) *
      (((1 / (Nat.cast 2 : Real) : Real) : Complex) * (x : Complex) -
        tsum (fun pn : Prod (HeightOneSpectrum (RingOfIntegers K)) Nat =>
          let q := Ideal.absNorm pn.1.asIdeal
          let a : Real := (q ^ (pn.2 + 1) : Nat)
          (Set.Ioi a).indicator
            (fun y : Real => (Real.log (q : Real) : Complex) *
              (1 - (a : Complex) / (y : Complex))) x))

/-- One global inequality between the squared mean at Gaussian width one
and the upper limit at width two, using the actual prime-ideal powers. -/
def DedekindPrimePowerMultiplicityInequality
    (K : Type u) [Field K] [NumberField K] : Prop :=
  Filter.limsup (fun T : Real =>
    (Inv.inv (T : Complex) * intervalIntegral
      (fun t => ((norm (primePowerGaussianSmoothing
        (dedekindPrimeIdealMultiplicitySignal K) 1 t) ^ 2 : Real) : Complex))
      0 T volume).re) Filter.atTop <=
    Filter.limsup (fun t : Real =>
      (primePowerGaussianSmoothing (dedekindPrimeIdealMultiplicitySignal K)
        (Nat.cast 2 : Real) t).re) Filter.atTop

/-- **Dedekind ERH and simple zeros.** For every number field, assume
Dedekind RH for that field. All its nontrivial Dedekind zeta zeros are
simple if and only if its global prime-ideal multiplicity inequality holds. -/
theorem dedekindERH_iff_globalPrimePowerMultiplicityInequality
    (K : Type u) [Field K] [NumberField K] (hERH : DedekindRH K) :
    DedekindPrimeIdealSimpleZeros K <-> DedekindPrimePowerMultiplicityInequality K := by
  change DedekindPrimeIdealSimpleZeros K <-> DedekindPrimeIdealMultiplicityInequality K
  exact dedekindERH_iff_primeIdealMultiplicityInequality K hERH

end

/-! ## Grand RH and zero multiplicity -/

section

open MeasureTheory
open scoped Classical

universe v

/-- The global inequality after removing exceptional frequencies and adding the
penalty for prescribed orders. -/
def GrandPrimePowerMultiplicityInequality (A : Real -> Complex)
    (E J : Finset Real) (order : Real -> Nat) : Prop :=
  let H1 := primePowerGaussianSmoothing A 1
  let H2 := primePowerGaussianSmoothing A (Nat.cast 2 : Real)
  Filter.limsup (fun T : Real =>
    (Inv.inv (T : Complex) * intervalIntegral
      (fun t => ((norm (removeMultiplicityFrequencies E H1 t) ^ 2 : Real) : Complex))
      0 T MeasureTheory.volume).re) Filter.atTop +
    J.sum (fun delta => norm (arithmeticMultiplicityCoefficient H1 delta -
      (order delta : Complex) * (Real.exp (-(delta ^ 2)) : Complex)) ^ 2) <=
    Filter.limsup (fun t => (removeMultiplicityFrequencies E H2 t).re) Filter.atTop

/-- **Grand RH for a standard family and prescribed zero orders.**
Assume the stated analytic data and the critical-line hypothesis for
the family. The zeros of each individual completion are simple outside
its finite exceptional set and have the designated exact orders if
and only if it satisfies its global prime-power inequality. The
rank-one construction includes the Dedekind norm twists. -/
theorem grandRH_iff_globalPrimePowerMultiplicityInequality
    {index : Type u} {powers : index -> Type v} [forall pi, Countable (powers pi)]
    (family : StandardMultiplicityFamilyData index powers)
    (analytics : HasStandardMultiplicityAnalytics family)
    (E J : index -> Finset Real) (order : index -> Real -> Nat)
    (hRH : forall pi s, family.completedL pi s = 0 -> s.re = 1 / 2) :
    (forall pi, HasPrescribedZeroOrders (family.completedL pi) (E pi) (J pi) (order pi)) <->
    (forall pi, GrandPrimePowerMultiplicityInequality (standardMultiplicityLogSignal family pi)
      (E pi) (J pi) (order pi)) := by
  have hDef (pi : index) :
      GrandPrimePowerMultiplicityInequality (standardMultiplicityLogSignal family pi)
          (E pi) (J pi) (order pi) =
        ExceptionalPrimePowerMultiplicityInequality (standardMultiplicityLogSignal family pi)
          (E pi) (J pi) (order pi) := rfl
  simp only [hDef]
  exact grandRH_prescribedOrders_iff_globalMultiplicityInequality family analytics E J order hRH

end

/-! ## Supporting statements -/

/-- In each number field, Dedekind RH is equivalent to the corrected ideal
Robin inequality above a field-dependent norm cutoff. -/
theorem dedekindRH_iff_correctedIdealRobin (K : Type u) [Field K] [NumberField K] :
    DedekindRH K <-> CorrectedIdealRobin K :=
  Iff.intro (correctedIdealRobin_of_dedekindRH K) (dedekindRH_of_correctedIdealRobin K)

end GRH

end Robin1984
