import Robin1984.GRH.AutomorphicEulerLog

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The Euler product and completion data used by the triangular prime-power equivalent of the critical-line property.
- Formalization note: Defines the completed standard family and its analytic input using the same Mathlib expressions as the independent Challenge.
- PROVENANCE-END
-/

/-!
# Analytic data for the completed automorphic family

The public criterion uses the completed zero condition and the triangular
remainder associated with the supplied pair of standard Euler products.
These are the fixed definitions stated independently in the Challenge.
-/

set_option autoImplicit false

namespace Robin1984.GRH

universe u

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

end Robin1984.GRH
