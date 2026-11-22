import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Robin1984.GRH.DedekindSeries
import Robin1984.GRH.SmoothedCriterion
import Robin1984.GRH.SupportingLine

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The corrected ideal Robin criterion is the project's extension of Guy Robin's divisor-sum criterion to number fields.
- Formalization note: This module states the fieldwise, cyclotomic-family, and all-field equivalences without supplying proofs.
- PROVENANCE-END
-/

/-!
# Corrected ideal Robin criterion

These propositions state the fieldwise equivalence and its Dirichlet and
Dedekind family forms. Mathlib's Dedekind zeta definition is a Dirichlet
series. We specify the analytic continuation by its agreement with that
series on the half-plane of absolute convergence.
-/

universe u

namespace Robin1984.GRH

/-- The sum of the absolute norms of the divisors of a nonzero integral ideal. -/
noncomputable def idealDivisorNormSum {K : Type u} [Field K] [NumberField K]
    (a : Ideal (NumberField.RingOfIntegers K)) (ha : Not (a = 0)) : Nat := by
  classical
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
  exact Finset.univ.sum (fun d : {d // Dvd.dvd d a} => Ideal.absNorm d.val)

/-- The corrected divisor-sum inequality eventually holds on all integral ideals. -/
def CorrectedIdealRobin (K : Type u) [Field K] [NumberField K] : Prop :=
  exists cutoff : Nat,
    forall (a : Ideal (NumberField.RingOfIntegers K)) (ha : Not (a = 0)),
      cutoff <= Ideal.absNorm a ->
      let x := Real.log (Ideal.absNorm a : Real)
      (idealDivisorNormSum a ha : Real) / (Ideal.absNorm a : Real) <=
        Real.exp Real.eulerMascheroniConstant * NumberField.dedekindZeta_residue K *
          (Real.log x + (12 + 3 * Real.log ((NumberField.discr K).natAbs : Real)) /
            Real.sqrt x)

/-- A holomorphic function away from 1 that agrees with the Dedekind zeta series. -/
def IsDedekindZetaContinuation (K : Type u) [Field K] [NumberField K]
    (zeta : Complex -> Complex) : Prop :=
  DifferentiableOn Complex zeta {s : Complex | Not (s = 1)} /\
    forall s : Complex, 1 < s.re -> zeta s = NumberField.dedekindZeta K s

/-- RH for the analytic continuation of the Dedekind zeta function of one field. -/
def DedekindRH (K : Type u) [Field K] [NumberField K] : Prop :=
  exists zeta : Complex -> Complex,
    IsDedekindZetaContinuation K zeta /\
      forall s : Complex, 0 < s.re -> s.re < 1 -> zeta s = 0 -> s.re = 1 / 2

/-- The fieldwise equivalence between Dedekind RH and the corrected ideal bound. -/
def FieldwiseRobinEquivalence (K : Type u) [Field K] [NumberField K] : Prop :=
  DedekindRH K <-> CorrectedIdealRobin K

/-- Dirichlet GRH over all moduli and characters, with zeros in the open strip. -/
def DirichletGRH : Prop :=
  forall (m : Nat) [NeZero m] (chi : DirichletCharacter Complex m) (s : Complex),
    0 < s.re -> s.re < 1 -> DirichletCharacter.LFunction chi s = 0 -> s.re = 1 / 2

/-- Dirichlet GRH corresponds to the corrected bound over all cyclotomic fields. -/
def DirichletRobinEquivalence : Prop :=
  DirichletGRH <->
    forall (m : Nat) [NeZero m], CorrectedIdealRobin (CyclotomicField m Rat)

/-- Dedekind GRH corresponds to the corrected bound over all number fields. -/
def DedekindRobinEquivalence : Prop :=
  (forall (K : Type u) [Field K] [NumberField K], DedekindRH K) <->
    (forall (K : Type u) [Field K] [NumberField K], CorrectedIdealRobin K)

end Robin1984.GRH
