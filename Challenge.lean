import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

set_option autoImplicit false

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984) and Jeffrey C. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis (2001).
- Formalization note: The retained statements are Robin's and Lagarias's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Robin's criterion and generalized Riemann hypotheses

The headline theorems are collected below the definitions. They cover
classical RH, Dirichlet GRH, Dedekind ERH, and grand RH for standard
automorphic L-functions. This file uses only Mathlib. The proofs live in
the project, and the Comparator manifest lists the currently audited
Challenge/Solution pairs.
-/

namespace Robin1984

/-- The sum of the positive divisors of `n`. -/
noncomputable def sigmaOneNat (n : Nat) : Nat :=
  ArithmeticFunction.sigma 1 n

/-- Robin's inequality
`sigma(n) < exp(gamma) * n * log(log n)` at the integer `n`. -/
noncomputable def robinInequality (n : Nat) : Prop :=
  (sigmaOneNat n : Real) <
    Real.exp Real.eulerMascheroniConstant * (n : Real) *
      Real.log (Real.log (n : Real))

/-- The objective maximized by a colossally abundant integer at parameter
`eps > 0`. -/
noncomputable def caObjective (eps : Real) (n : Nat) : Real :=
  (sigmaOneNat n : Real) / ((n : Real) ^ (1 + eps))

/-- `n` is colossally abundant at parameter `eps` when `eps > 0`, `n > 1`,
and `sigma(k) / k^(1+eps) <= sigma(n) / n^(1+eps)` for every `k > 1`. -/
noncomputable def IsColossallyAbundantWith (n : Nat) (eps : Real) : Prop :=
  0 < eps /\ 1 < n /\
    forall k : Nat, 1 < k -> caObjective eps k <= caObjective eps n

/-- Lagarias's elementary divisor-sum criterion. -/
def LagariasElementaryCriterion : Prop :=
  forall n : Nat,
    0 < n ->
      ((ArithmeticFunction.sigma 1 n : Nat) : Real) <=
        (harmonic n : Real) +
          Real.exp (harmonic n : Real) * Real.log (harmonic n : Real)

/-! ## Definitions for the generalized criteria -/

namespace GRH

universe u u_2

/-- Sum of the absolute norms of the integral ideal divisors of a nonzero ideal.
Comparator checks the universe parameter name against the implementation. -/
noncomputable def idealDivisorNormSum {K : Type u_2} [Field K] [NumberField K]
    (a : Ideal (NumberField.RingOfIntegers K)) (ha : Not (a = 0)) : Nat := by
  classical
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
  exact Finset.univ.sum (fun d : {d // Dvd.dvd d a} => Ideal.absNorm d.val)

/-- The corrected ideal divisor-sum inequality holds above a field-dependent cutoff. -/
def CorrectedIdealRobin (K : Type u) [Field K] [NumberField K] : Prop :=
  exists cutoff : Nat,
    forall (a : Ideal (NumberField.RingOfIntegers K)) (ha : Not (a = 0)),
      cutoff <= Ideal.absNorm a ->
      let x := Real.log (Ideal.absNorm a : Real)
      (idealDivisorNormSum a ha : Real) / (Ideal.absNorm a : Real) <=
        Real.exp Real.eulerMascheroniConstant * NumberField.dedekindZeta_residue K *
          (Real.log x + (12 + 3 * Real.log ((NumberField.discr K).natAbs : Real)) /
            Real.sqrt x)

/-- The continuation agrees with the Dedekind zeta series on its half-plane of convergence. -/
def IsDedekindZetaContinuation (K : Type u) [Field K] [NumberField K]
    (zeta : Complex -> Complex) : Prop :=
  DifferentiableOn Complex zeta {s : Complex | Not (s = 1)} /\
    forall s : Complex, 1 < s.re -> zeta s = NumberField.dedekindZeta K s

/-- Dedekind RH for the analytic continuation belonging to a single field. -/
def DedekindRH (K : Type u) [Field K] [NumberField K] : Prop :=
  exists zeta : Complex -> Complex,
    IsDedekindZetaContinuation K zeta /\
      forall s : Complex, 0 < s.re -> s.re < 1 -> zeta s = 0 -> s.re = 1 / 2

/-- Dirichlet GRH for all positive moduli and all complex characters. -/
def DirichletGRH : Prop :=
  forall (m : Nat) [NeZero m] (chi : DirichletCharacter Complex m) (s : Complex),
    0 < s.re -> s.re < 1 -> DirichletCharacter.LFunction chi s = 0 -> s.re = 1 / 2

/-! ## Analytic data for the completed automorphic family -/

/-- The completed L-functions and paired prime-power data for a family
of standard L-functions. The index identifies the members of the family. -/
structure StandardAutomorphicFamilyData (index : Type u) (powers : index -> Type u) where
  completedL : index -> Complex -> Complex
  dual : index -> index
  equationFactor : index -> Complex -> Complex
  primePowerNorm : forall pi, powers pi -> Nat
  coefficient : forall pi, powers pi -> Real
  poleOrder : index -> Nat
  poleRemoved : index -> Complex -> Complex
  conductor : index -> Real
  realFactorCount : index -> Nat
  complexFactorCount : index -> Nat
  realShift : forall pi, Fin (realFactorCount pi) -> Complex
  complexShift : forall pi, Fin (complexFactorCount pi) -> Complex

/-- The signed triangular remainder for the member indexed by `pi`. -/
noncomputable def standardFamilyTriangularRemainder {index : Type u} {powers : index -> Type u}
    (family : StandardAutomorphicFamilyData index powers) (pi : index) (x : Real) : Real :=
  (family.poleOrder pi : Real) / ((2 : Nat) : Real) * x -
    tsum (fun i => (Set.Ioi (family.primePowerNorm pi i : Real)).indicator
      (fun y => family.coefficient pi i * (1 - (family.primePowerNorm pi i : Real) / y)) x)

/-- The triangular remainder has a square-root upper bound above a cutoff. -/
def StandardFamilyTriangularBound {index : Type u} {powers : index -> Type u}
    (family : StandardAutomorphicFamilyData index powers) (pi : index) : Prop :=
  exists cutoff C : Real, 1 <= cutoff /\
    forall x : Real, cutoff <= x ->
      standardFamilyTriangularRemainder family pi x <= C * Real.sqrt x

/-- The logarithm of the paired Euler product on its half-plane of convergence. -/
noncomputable def standardFamilyEulerLog {index : Type u} {powers : index -> Type u}
    (family : StandardAutomorphicFamilyData index powers) (pi : index) (s : Complex) : Complex :=
  tsum (fun i => ((family.coefficient pi i : Complex) /
    (Real.log (family.primePowerNorm pi i : Real) : Complex)) *
    ((family.primePowerNorm pi i : Real) : Complex) ^ (-s))

/-- The conductor, pole clearing at the origin, and the finite products of
real and complex Gamma factors for the paired completion. -/
noncomputable def standardFamilyCompletionFactor {index : Type u} {powers : index -> Type u}
    (family : StandardAutomorphicFamilyData index powers) (pi : index) (s : Complex) : Complex :=
  s ^ family.poleOrder pi * (family.conductor pi : Complex) ^ (s / ((2 : Nat) : Complex)) *
    (Finset.univ.prod (fun j =>
      (Real.pi : Complex) ^ (-(s + family.realShift pi j) / ((2 : Nat) : Complex)) *
        Complex.Gamma ((s + family.realShift pi j) / ((2 : Nat) : Complex)))) *
    (Finset.univ.prod (fun j =>
      ((2 : Nat) : Complex) * (((2 : Nat) : Complex) * (Real.pi : Complex)) ^ (-(s + family.complexShift pi j)) *
        Complex.Gamma (s + family.complexShift pi j)))

/-- The analytic properties used by the criterion. The Euler product and
completion identify the paired functions, and the completed functional
equation relates a function to its contragredient. -/
structure HasStandardAutomorphicAnalytics {index : Type u} {powers : index -> Type u}
    (family : StandardAutomorphicFamilyData index powers) : Prop where
  conductor_pos : forall pi, 0 < family.conductor pi
  real_shift : forall pi j, -(1 : Real) / 2 < (family.realShift pi j).re
  complex_shift : forall pi j, -(1 : Real) / 2 < (family.complexShift pi j).re
  norm_ge_two : forall pi i, (2 : Real) <= (family.primePowerNorm pi i : Real)
  norms_locally_finite : forall pi (T : Real), Set.Finite {i : powers pi |
    (family.primePowerNorm pi i : Real) < T}
  log_derivative_summable : forall pi (r : Real), 1 < r ->
    Summable (fun i => norm (family.coefficient pi i) * (family.primePowerNorm pi i : Real) ^ (-r))
  ordinary_entire : forall pi, Differentiable Complex (family.poleRemoved pi)
  completed_order_one : forall pi, Differentiable Complex (family.completedL pi) /\
    forall eps : Real, 0 < eps -> exists C : Real, 0 < C /\
      forall z : Complex, norm (family.completedL pi z) <= Real.exp (C * (1 + norm z) ^ (1 + eps))
  euler_product : forall pi s, 1 < s.re ->
    family.poleRemoved pi s =
      (s - 1) ^ family.poleOrder pi * Complex.exp (standardFamilyEulerLog family pi s)
  completion : forall pi s, (1 : Real) / 2 < s.re ->
    family.completedL pi s * family.completedL (family.dual pi) s =
      standardFamilyCompletionFactor family pi s * family.poleRemoved pi s
  functional_equation : forall pi s, family.completedL (family.dual pi) (1 - s) =
    family.equationFactor pi s * family.completedL pi s

end GRH

/-!
# Headline theorems

Robin, the colossally abundant extension, and Lagarias concern classical RH.
Dirichlet GRH and Dedekind ERH use the same corrected ideal divisor-sum
bound over different ranges of number fields. Grand RH uses a signed
triangular prime-power bound.
-/

/-! ## Classical RH -/

/-- **Robin's criterion.** The Riemann hypothesis holds exactly when the
sum of divisors of every integer above 5040 is strictly below Robin's
bound involving Euler's constant and the iterated logarithm. -/
theorem robin_inequality_iff_riemannHypothesis :
    (forall n : Nat, 5040 < n -> robinInequality n) <->
      RiemannHypothesis := by
  sorry

/-- **Colossally abundant reduction.** The Riemann hypothesis holds
exactly when Robin's inequality is true on the colossally abundant
integers above 5040. -/
theorem riemannHypothesis_iff_colossallyAbundant_robin :
    RiemannHypothesis <->
      (forall n : Nat, forall eps : Real, 5040 < n ->
        IsColossallyAbundantWith n eps -> robinInequality n) := by
  sorry

/-- **Lagarias's criterion.** The Riemann hypothesis is equivalent to
the harmonic-number bound for the sum of divisors of every positive
integer. -/
theorem riemann_hypothesis_iff_lagarias_elementary_criterion :
    RiemannHypothesis <-> LagariasElementaryCriterion := by
  sorry

namespace GRH

universe u

/-! ## Dirichlet GRH and Dedekind ERH -/


/-- **Dirichlet GRH.** Every zero in the open critical strip of every
Dirichlet L-function has real part one half if and only if the corrected
ideal Robin inequality holds in every cyclotomic field. Each field has
its own norm cutoff. -/
theorem dirichletGRH_iff_cyclotomicCorrectedIdealRobin :
    (forall (modulus : Nat) [NeZero modulus]
      (chi : DirichletCharacter Complex modulus) (s : Complex),
      0 < s.re -> s.re < 1 -> DirichletCharacter.LFunction chi s = 0 ->
        s.re = 1 / 2) <->
    (forall (modulus : Nat) [NeZero modulus],
      CorrectedIdealRobin (CyclotomicField modulus Rat)) := by
  sorry

/-- **Dedekind ERH.** Every number field has its Dedekind zeta zeros in
the critical strip on the critical line exactly when every number field
satisfies the corrected ideal Robin inequality. Each field has its own
norm cutoff. -/
theorem dedekindERH_iff_correctedIdealRobin :
    (forall (K : Type u) [Field K] [NumberField K], DedekindRH K) <->
      (forall (K : Type u) [Field K] [NumberField K], CorrectedIdealRobin K) := by
  sorry

/-! ## Grand RH -/

/-- **Grand RH and triangular prime powers.** For any family with the
stated analytic data, all of its nontrivial zeros lie on the critical line
exactly when each member's triangular prime-power remainder has an eventual
square-root upper bound. The full Grand RH equivalence requires the data
for every automorphic L-function. -/
theorem grandRH_iff_triangularPrimePowerBound {index : Type u} {powers : index -> Type u}
    [forall pi, Countable (powers pi)]
    (family : StandardAutomorphicFamilyData index powers)
    (analytics : HasStandardAutomorphicAnalytics family) :
    (forall (pi : index) (s : Complex), family.completedL pi s = 0 -> s.re = 1 / 2) <->
      (forall pi, StandardFamilyTriangularBound family pi) := by
  sorry

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
  sorry

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
  sorry

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

/-- Every zero in the open critical strip of the Dedekind zeta continuation
of this field has analytic order exactly one. -/
def DedekindPrimeIdealSimpleZeros.{u_1}
    (K : Type u_1) [Field K] [NumberField K] : Prop :=
  forall zeta : Complex -> Complex, IsDedekindZetaContinuation K zeta ->
    forall s : Complex, 0 < s.re -> s.re < 1 -> zeta s = 0 ->
      analyticOrderNatAt zeta s = 1

/-- **Dedekind ERH and simple zeros.** For every number field, assume
Dedekind RH for that field. All its nontrivial Dedekind zeta zeros are
simple if and only if its global prime-ideal multiplicity inequality holds. -/
theorem dedekindERH_iff_globalPrimePowerMultiplicityInequality
    (K : Type u) [Field K] [NumberField K] (hERH : DedekindRH K) :
    DedekindPrimeIdealSimpleZeros K <-> DedekindPrimePowerMultiplicityInequality K := by
  sorry

end

/-! ## Grand RH and zero multiplicity -/

section

open MeasureTheory
open scoped Classical

universe v

/-- Individual standard L-functions and their arithmetic and archimedean data. -/
structure StandardMultiplicityFamilyData (index : Type u) (powers : index -> Type v) where
  completedL : index -> Complex -> Complex
  poleRemoved : index -> Complex -> Complex
  primePowerNorm : forall pi, powers pi -> Nat
  coefficient : forall pi, powers pi -> Complex
  poleOrder : index -> Nat
  conductor : index -> Real
  realFactorCount : index -> Nat
  complexFactorCount : index -> Nat
  realShift : forall pi, Fin (realFactorCount pi) -> Complex
  complexShift : forall pi, Fin (complexFactorCount pi) -> Complex

/-- The conductor, cleared pole at zero, and Gamma factors of a standard completion. -/
noncomputable def standardMultiplicityCompletionFactor {index : Type u} {powers : index -> Type v}
    (family : StandardMultiplicityFamilyData index powers) (pi : index) (s : Complex) : Complex :=
  s ^ family.poleOrder pi * (family.conductor pi : Complex) ^ (s / ((2 : Nat) : Complex)) *
    (Finset.univ.prod (fun j =>
      (Real.pi : Complex) ^ (-(s + family.realShift pi j) / ((2 : Nat) : Complex)) *
        Complex.Gamma ((s + family.realShift pi j) / ((2 : Nat) : Complex)))) *
    (Finset.univ.prod (fun j =>
      ((2 : Nat) : Complex) * (((2 : Nat) : Complex) * (Real.pi : Complex)) ^ (-(s + family.complexShift pi j)) *
        Complex.Gamma (s + family.complexShift pi j)))

/-- Standard completion, growth, and Euler logarithm for an individual family.
The pole order refers to normalization at zero and one. -/
structure HasStandardMultiplicityAnalytics {index : Type u} {powers : index -> Type v}
    (family : StandardMultiplicityFamilyData index powers) : Prop where
  conductor_pos : forall pi, 0 < family.conductor pi
  real_shift : forall pi j, -(1 : Real) / 2 < (family.realShift pi j).re
  complex_shift : forall pi j, -(1 : Real) / 2 < (family.complexShift pi j).re
  norm_ge_two : forall pi i, (2 : Real) <= (family.primePowerNorm pi i : Real)
  norms_locally_finite : forall pi (T : Real), Set.Finite {i : powers pi |
    (family.primePowerNorm pi i : Real) < T}
  log_derivative_summable : forall pi (r : Real), 1 < r ->
    Summable (fun i => norm (family.coefficient pi i) * (family.primePowerNorm pi i : Real) ^ (-r))
  ordinary_entire : forall pi, Differentiable Complex (family.poleRemoved pi)
  completed_order_one : forall pi, Differentiable Complex (family.completedL pi) /\
    forall eps : Real, 0 < eps -> exists C : Real, 0 < C /\
      forall z : Complex, norm (family.completedL pi z) <= Real.exp (C * (1 + norm z) ^ (1 + eps))
  completion : forall pi s, (1 : Real) / 2 < s.re ->
    family.completedL pi s = standardMultiplicityCompletionFactor family pi s * family.poleRemoved pi s
  euler_log_derivative : forall pi s, 1 < s.re ->
    logDeriv (family.poleRemoved pi) s = (family.poleOrder pi : Complex) / (s - 1) -
      tsum (fun n => family.coefficient pi n * ((family.primePowerNorm pi n : Real) : Complex) ^ (-s))

/-- The signed triangular prime-power signal of an individual standard L-function. -/
noncomputable def standardMultiplicityLogSignal {index : Type u} {powers : index -> Type v}
    (family : StandardMultiplicityFamilyData index powers) (pi : index) (t : Real) : Complex :=
  if t < 0 then 0 else
    let x := Real.exp t
    (Real.exp (-t / (Nat.cast 2 : Real)) : Complex) *
      ((((family.poleOrder pi : Real) / (Nat.cast 2 : Real) : Real) : Complex) * (x : Complex) -
        tsum (fun n : powers pi => (Set.Ioi (family.primePowerNorm pi n : Real)).indicator
          (fun y : Real => family.coefficient pi n *
            (1 - ((family.primePowerNorm pi n : Real) : Complex) / (y : Complex))) x))

/-- The point on the critical line of a specified ordinate. -/
noncomputable def multiplicityCriticalPoint (delta : Real) : Complex :=
  Complex.mk (1 / (Nat.cast 2 : Real)) delta

/-- Simple zeros outside the omitted ordinates and exact orders at the prescribed ones. -/
def HasPrescribedZeroOrders (F : Complex -> Complex)
    (E J : Finset Real) (order : Real -> Nat) : Prop :=
  (forall delta, Not (Membership.mem E delta) ->
    analyticOrderNatAt F (multiplicityCriticalPoint delta) <= 1) /\
  (forall delta, Membership.mem J delta ->
    analyticOrderNatAt F (multiplicityCriticalPoint delta) = order delta)

/-- The mean Fourier coefficient extracted from the arithmetic signal. -/
noncomputable def arithmeticMultiplicityCoefficient (H : Real -> Complex) (delta : Real) :
    Complex :=
  Filter.limUnder Filter.atTop (fun T : Real => Inv.inv (T : Complex) *
    intervalIntegral
      (fun t : Real => H t * Complex.exp (-(delta : Complex) * Complex.I * (t : Complex)))
      0 T MeasureTheory.volume)

/-- Delete the measured contribution of each exceptional ordinate. -/
noncomputable def removeMultiplicityFrequencies (E : Finset Real) (H : Real -> Complex) (t : Real) :
    Complex :=
  H t - E.sum (fun delta => arithmeticMultiplicityCoefficient H delta *
    Complex.exp ((delta : Complex) * Complex.I * (t : Complex)))

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

/-- **Grand RH and prescribed zero orders.** For an automorphic family
with the stated analytic data and all of its nontrivial zeros on the
critical line, the zeros are simple outside the chosen finite sets and
have the designated exact orders exactly when each member satisfies the
global prime-power inequality with those exceptions. -/
theorem grandRH_iff_globalPrimePowerMultiplicityInequality
    {index : Type u} {powers : index -> Type v} [forall pi, Countable (powers pi)]
    (family : StandardMultiplicityFamilyData index powers)
    (analytics : HasStandardMultiplicityAnalytics family)
    (E J : index -> Finset Real) (order : index -> Real -> Nat)
    (hRH : forall pi s, family.completedL pi s = 0 -> s.re = 1 / 2) :
    (forall pi, HasPrescribedZeroOrders (family.completedL pi) (E pi) (J pi) (order pi)) <->
    (forall pi, GrandPrimePowerMultiplicityInequality (standardMultiplicityLogSignal family pi)
      (E pi) (J pi) (order pi)) := by
  sorry

end

/-! # Supporting statements -/

/-- The single-field Dedekind equivalence used to prove the family criteria.
For each number field, the critical-line property for its Dedekind zeta
function is equivalent to the corrected ideal Robin inequality above a
field-dependent norm cutoff. -/
theorem dedekindRH_iff_correctedIdealRobin (K : Type u) [Field K] [NumberField K] :
    DedekindRH K <-> CorrectedIdealRobin K := by
  sorry

end GRH

end Robin1984
