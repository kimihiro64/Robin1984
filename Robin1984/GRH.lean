import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Robin1984.GRH.DedekindLogDerivative
import Robin1984.GRH.DedekindTailCriterion
import Robin1984.GRH.SmoothedCriterion
import Robin1984.GRH.SmoothedForward
import Robin1984.GRH.SupportingLine

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The corrected ideal Robin criterion is the project's extension of Guy Robin's divisor-sum criterion to number fields.
- Formalization note: This module states the headline equivalences and proves the continuation uniqueness and Dirichlet level reductions.
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

/-- The values of an analytic Dedekind zeta continuation away from its
pole are determined by the convergent Dirichlet series. -/
theorem eqOn_of_dedekindZetaContinuations {K : Type u} [Field K] [NumberField K]
    {f g : Complex -> Complex}
    (hf : IsDedekindZetaContinuation K f) (hg : IsDedekindZetaContinuation K g) :
    Set.EqOn f g {s : Complex | Not (s = 1)} := by
  let U : Set Complex := {s : Complex | Not (s = 1)}
  have hOpen : IsOpen U := isOpen_ne
  have hConnected : IsPreconnected U := by
    have hRank : 1 < Module.rank Real Complex := by
      rw [Complex.rank_real_complex]
      exact Nat.one_lt_ofNat
    exact (isConnected_compl_singleton_of_one_lt_rank hRank (1 : Complex)).isPreconnected
  have hRe : 1 < (((2 : Real) : Complex)).re := by
    rw [Complex.ofReal_re]
    exact one_lt_two
  have hTwo : Membership.mem U ((2 : Real) : Complex) := by
    change Not (((2 : Real) : Complex) = 1)
    intro h
    have he := congrArg Complex.re h
    rw [Complex.ofReal_re, Complex.one_re] at he
    exact (ne_of_gt (one_lt_two : (1 : Real) < 2)) he
  have hAgree : Filter.EventuallyEq (nhds ((2 : Real) : Complex)) f g := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hRe] with s hs
    exact (hf.2 s hs).trans (hg.2 s hs).symm
  exact (hf.1.analyticOnNhd hOpen).eqOn_of_preconnected_of_eventuallyEq
    (hg.1.analyticOnNhd hOpen) hConnected hTwo hAgree

/-- A chosen Dedekind zeta continuation has critical-line zeros exactly
when the continuation-independent RH predicate holds for the field. -/
theorem dedekindRH_iff_zeros_of_continuation {K : Type u} [Field K] [NumberField K]
    {f : Complex -> Complex} (hf : IsDedekindZetaContinuation K f) :
    DedekindRH K <->
      forall s : Complex, 0 < s.re -> s.re < 1 -> f s = 0 -> s.re = 1 / 2 := by
  constructor
  case mp =>
    intro h s hs0 hs1 hs
    choose g hg using h
    have hsNe : Not (s = 1) := fun hEq => by simp [hEq] at hs1
    have hEq := eqOn_of_dedekindZetaContinuations hg.1 hf hsNe
    exact hg.2 s hs0 hs1 (hEq.trans hs)
  case mpr =>
    intro h
    exact Exists.intro f (And.intro hf h)

/-- Cyclotomic zeta factorization, including the nonvanishing finite
Euler factors for imprimitive characters, identifies the two RH families. -/
theorem dirichletGRH_iff_cyclotomicDedekindRH_of_factorization
    (zeta E : forall (m : Nat) [NeZero m], Complex -> Complex)
    (hContinuation : forall (m : Nat) [NeZero m],
      IsDedekindZetaContinuation (CyclotomicField m Rat) (zeta m))
    (hEuler : forall (m : Nat) [NeZero m] (s : Complex),
      0 < s.re -> s.re < 1 -> Not (E m s = 0))
    (hFactor : forall (m : Nat) [NeZero m] (s : Complex), 0 < s.re -> s.re < 1 ->
      (Finset.univ.prod (fun chi : DirichletCharacter Complex m =>
        DirichletCharacter.LFunction chi s)) = E m s * zeta m s) :
    DirichletGRH <-> forall (m : Nat) [NeZero m], DedekindRH (CyclotomicField m Rat) := by
  classical
  constructor
  case mp =>
    intro h m hm
    apply (dedekindRH_iff_zeros_of_continuation (hContinuation m)).mpr
    intro s hs0 hs1 hzero
    have hProduct : (Finset.univ.prod (fun chi : DirichletCharacter Complex m =>
        DirichletCharacter.LFunction chi s)) = 0 := by
      rw [hFactor m s hs0 hs1, hzero, mul_zero]
    choose chi hChi using Finset.prod_eq_zero_iff.mp hProduct
    exact h m chi s hs0 hs1 hChi.2
  case mpr =>
    intro h m hm chi s hs0 hs1 hzero
    have hProduct : (Finset.univ.prod (fun chi : DirichletCharacter Complex m =>
        DirichletCharacter.LFunction chi s)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ chi) hzero
    have hZeta := (mul_eq_zero.mp ((hFactor m s hs0 hs1).symm.trans hProduct)).resolve_left
      (hEuler m s hs0 hs1)
    exact (dedekindRH_iff_zeros_of_continuation (hContinuation m)).mp (h m) s hs0 hs1 hZeta

/-- Euler factors removed when a primitive Dirichlet character is raised
to the level of the specified character. -/
noncomputable def dirichletLevelEulerFactor {m : Nat} (chi : DirichletCharacter Complex m)
    (s : Complex) : Complex :=
  m.primeFactors.prod (fun p => 1 - chi.primitiveCharacter (p : ZMod chi.conductor) *
    (p : Complex) ^ (-s))

/-- Level-change Euler factors do not add zeros in the open right half-plane. -/
theorem dirichletLevelEulerFactor_ne_zero {m : Nat} [NeZero m]
    (chi : DirichletCharacter Complex m) {s : Complex} (hs : 0 < s.re) :
    Not (dirichletLevelEulerFactor chi s = 0) := by
  classical
  unfold dirichletLevelEulerFactor
  intro hProduct
  choose p hp using Finset.prod_eq_zero_iff.mp hProduct
  have hPrime := Nat.prime_of_mem_primeFactors hp.1
  have hpRe : (1 : Real) < p := Nat.one_lt_cast.mpr hPrime.one_lt
  have hCpow : norm ((p : Complex) ^ (-s)) < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hPrime.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpRe (neg_neg_of_pos hs)
  have hTerm : norm (chi.primitiveCharacter (p : ZMod chi.conductor) *
       (p : Complex) ^ (-s)) < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (chi.primitiveCharacter.norm_le_one _)).trans_lt
      hCpow
  rw [<- sub_eq_zero.mp hp.2, norm_one] at hTerm
  exact lt_irrefl _ hTerm

/-- The primitive-character level-change formula away from the possible pole. -/
theorem LFunction_eq_primitive_mul_levelEulerFactor {m : Nat} [NeZero m]
    (chi : DirichletCharacter Complex m) {s : Complex} (hs : Not (s = 1)) :
    DirichletCharacter.LFunction chi s =
      @DirichletCharacter.LFunction chi.conductor (NeZero.mk chi.conductor_ne_zero)
        chi.primitiveCharacter s * dirichletLevelEulerFactor chi s := by
  let _ : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  have h := DirichletCharacter.LFunction_changeLevel chi.conductor_dvd_level
    chi.primitiveCharacter (Or.inr hs)
  rw [chi.changeLevel_primitiveCharacter] at h
  exact h

/-- The cyclotomic factorization into primitive Dirichlet L-functions
suffices for equivalence of Dirichlet GRH and cyclotomic Dedekind RH. -/
theorem dirichletGRH_iff_cyclotomicDedekindRH_of_primitive_factorization
    (zeta : forall (m : Nat) [NeZero m], Complex -> Complex)
    (hContinuation : forall (m : Nat) [NeZero m],
      IsDedekindZetaContinuation (CyclotomicField m Rat) (zeta m))
    (hFactor : forall (m : Nat) [NeZero m] (s : Complex), 0 < s.re -> s.re < 1 ->
      zeta m s = (Finset.univ.prod (fun chi : DirichletCharacter Complex m =>
        @DirichletCharacter.LFunction chi.conductor (NeZero.mk chi.conductor_ne_zero)
          chi.primitiveCharacter s))) :
    DirichletGRH <-> forall (m : Nat) [NeZero m], DedekindRH (CyclotomicField m Rat) := by
  classical
  let E : forall (m : Nat) [NeZero m], Complex -> Complex :=
    fun m _ s => Finset.univ.prod (fun chi : DirichletCharacter Complex m =>
      dirichletLevelEulerFactor chi s)
  refine dirichletGRH_iff_cyclotomicDedekindRH_of_factorization zeta E hContinuation ?_ ?_
  case refine_1 =>
    intro m hm s hs0 _
    exact Finset.prod_ne_zero_iff.mpr (fun chi _ => dirichletLevelEulerFactor_ne_zero chi hs0)
  case refine_2 =>
    intro m hm s hs0 hs1
    have hsNe : Not (s = 1) := fun h => by simp [h] at hs1
    calc
      _ = Finset.univ.prod (fun chi : DirichletCharacter Complex m =>
          @DirichletCharacter.LFunction chi.conductor (NeZero.mk chi.conductor_ne_zero)
            chi.primitiveCharacter s * dirichletLevelEulerFactor chi s) :=
        Finset.prod_congr rfl (fun chi _ => LFunction_eq_primitive_mul_levelEulerFactor chi hsNe)
      _ = _ := by
        rw [Finset.prod_mul_distrib, <- hFactor m s hs0 hs1]
        exact mul_comm _ _

end Robin1984.GRH
