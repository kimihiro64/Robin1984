import Robin1984.GRH.AutomorphicCompletion
import Robin1984.GRH.MultiplicityExceptions

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Standard automorphic Gamma completion and the Gaussian criterion for prescribed analytic orders.
- Formalization note: Reduces the completed zero-order comparison for an individual supplied family to its signed prime-power series.
- PROVENANCE-END
-/

/-!
# Zero orders for a supplied standard automorphic family

The critical-line property allows the ordinary prime-power expansions to
recover the zero orders of the completed standard L-functions.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Complex.Hadamard Filter
open scoped Topology Classical

universe u v

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
  standardCompletionFactor (family.conductor pi) (family.poleOrder pi)
    (family.realShift pi) (family.complexShift pi) s

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
def standardMultiplicityLogSignal {index : Type u} {powers : index -> Type v}
    (family : StandardMultiplicityFamilyData index powers) (pi : index) : Real -> Complex :=
  triangularLogSignal (complexTriangularRemainder
    (fun i => (family.primePowerNorm pi i : Real)) (family.coefficient pi) (family.poleOrder pi : Real))

/-- Under Grand RH for the supplied standard family, the completed functions
have simple zeros outside finite exceptional sets and the prescribed orders
at designated exceptions exactly when their prime-power inequalities hold. -/
theorem grandRH_prescribedOrders_iff_globalMultiplicityInequality
    {index : Type u} {powers : index -> Type v} [forall pi, Countable (powers pi)]
    (family : StandardMultiplicityFamilyData index powers)
    (analytics : HasStandardMultiplicityAnalytics family)
    (E J : index -> Finset Real) (order : index -> Real -> Nat)
    (hRH : forall pi s, family.completedL pi s = 0 -> s.re = 1 / 2) :
    (forall pi, HasPrescribedZeroOrders (family.completedL pi) (E pi) (J pi) (order pi)) <->
    (forall pi, ExceptionalPrimePowerMultiplicityInequality (standardMultiplicityLogSignal family pi)
      (E pi) (J pi) (order pi)) := by
  have hFactor (pi : index) :
      EntireOfOrderAtMost 1 (family.poleRemoved pi) :=
    entireOrderOne_of_standardCompletion (analytics.conductor_pos pi) (family.poleOrder pi)
      (family.realShift pi) (family.complexShift pi) (analytics.real_shift pi)
      (analytics.complex_shift pi) (analytics.ordinary_entire pi) (analytics.completed_order_one pi)
      (analytics.completion pi)
  have hRight (pi : index) (s : Complex) (hZero : family.poleRemoved pi s = 0) :
      s.re <= 1 / 2 := by
    by_contra hn
    have hs := lt_of_not_ge hn
    have hz : family.completedL pi s = 0 := by
      rw [analytics.completion pi s hs, hZero, mul_zero]
    exact (ne_of_gt hs) (hRH pi s hz)
  have hNZ (pi : index) : exists s, Not (family.poleRemoved pi s = 0) := by
    refine Exists.intro 2 ?_
    intro hz
    have h := hRight pi 2 hz
    norm_num at h
  have hOrd (pi : index) (delta : Real) :
      analyticOrderNatAt (family.poleRemoved pi) (multiplicityCriticalPoint delta) =
        analyticOrderNatAt (family.completedL pi) (multiplicityCriticalPoint delta) :=
    analyticOrderNatAt_eq_of_standardCompletion (analytics.conductor_pos pi) (family.poleOrder pi)
      (family.realShift pi) (family.complexShift pi) (analytics.real_shift pi)
      (analytics.complex_shift pi) (analytics.ordinary_entire pi) (analytics.completed_order_one pi).1
      (analytics.completion pi) le_rfl
  have hEach (pi : index) :
      HasPrescribedZeroOrders (family.completedL pi) (E pi) (J pi) (order pi) <->
      ExceptionalPrimePowerMultiplicityInequality (standardMultiplicityLogSignal family pi)
        (E pi) (J pi) (order pi) := by
    have hNorm (i : powers pi) : (1 : Real) <= (family.primePowerNorm pi i : Real) :=
      (by norm_num : (1 : Real) <= 2).trans (analytics.norm_ge_two pi i)
    have h := complexArithmeticMultiplicityWithExceptions
      (fun i => (family.primePowerNorm pi i : Real)) (family.coefficient pi) (family.poleOrder pi : Real)
      (family.poleRemoved pi) (E pi) (J pi) (order pi) hNorm (analytics.norms_locally_finite pi)
      (analytics.log_derivative_summable pi) (hFactor pi) (hNZ pi) (hRight pi)
      (by simpa only [Complex.ofReal_natCast] using analytics.euler_log_derivative pi)
    unfold HasPrescribedZeroOrders at h
    simp_rw [hOrd pi] at h
    exact h
  exact forall_congr' hEach

end Robin1984.GRH
