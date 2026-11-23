import Robin1984.GRH.DedekindCompletedGrowth
import Robin1984.GRH.DedekindCompletedZeroDistribution

/-!
# Hadamard logarithmic derivative of the completed Dedekind zeta

The genus-one canonical product runs through the zeros with their actual
multiplicities. Off the zero set its logarithmic derivative consists of a
constant and an absolutely convergent sum of zero terms.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Hadamard factorization for an entire function of order at most one.
- Formalization note: Use the pinned PrimeNumberTheoremAnd canonical product for the completed Dedekind zeta.
- Content basis: The actual theta growth bound, pole-cleared functional equation, and off-zero logarithmic derivative.
- Dependency status: Optional GRH extension and PrimeNumberTheoremAnd.
-/

open Complex.Hadamard DedekindZeta NumberField Set

namespace Robin1984.GRH

/-- The nonzero divisor indices of the completed Dedekind function,
with one index for each unit of multiplicity. -/
abbrev DedekindCompletedZeroIndex (K : Type*) [Field K] [NumberField K] :=
  Subtype (fun i : divisorZeroIndex (completedDedekindPoleCleared K) (univ : Set Complex) =>
    Not (i.1 = 0))

/-- The point corresponding to a completed Dedekind zero index. -/
def completedDedekindZero (K : Type*) [Field K] [NumberField K]
    (i : DedekindCompletedZeroIndex K) : Complex := i.val.1

variable (K : Type*) [Field K] [NumberField K]

theorem completedDedekindZero_is_zero (i : DedekindCompletedZeroIndex K) :
    completedDedekindPoleCleared K (completedDedekindZero K i) = 0 := by
  by_contra h
  let z := completedDedekindZero K i
  have ha : AnalyticOnNhd Complex (completedDedekindPoleCleared K) univ :=
    fun s _ => analyticAt_completedDedekindPoleCleared K s
  have ho : analyticOrderAt (completedDedekindPoleCleared K) z = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr h)
  have hd : MeromorphicOn.divisor (completedDedekindPoleCleared K) univ z = 0 := by
    rw [MeromorphicOn.divisor_apply ha.meromorphicOn (mem_univ z),
      (ha z (mem_univ z)).meromorphicOrderAt_eq, ho]
    simp
  have hi : Fin (Int.toNat (MeromorphicOn.divisor (completedDedekindPoleCleared K) univ z)) :=
    i.val.2
  rw [hd, Int.toNat_zero] at hi
  exact Fin.elim0 hi

private theorem completedDedekindPoleCleared_ne_zero_at_one :
    Not (completedDedekindPoleCleared K 1 = 0) :=
  completedDedekindPoleCleared_ne_zero_of_one_le_re K (by norm_num)

/-- The reciprocal squared norms of the indexed completed zeros are summable. -/
theorem summable_completedDedekindZero_inv_sq :
    Summable (fun i : DedekindCompletedZeroIndex K =>
      (Inv.inv (norm (completedDedekindZero K i))) ^ (2 : Nat)) := by
  have hOrder := completedDedekindPoleCleared_entireOfOrderAtMost_one K
  have hNontrivial : exists z : Complex, Not (completedDedekindPoleCleared K z = 0) :=
    Exists.intro 1 (completedDedekindPoleCleared_ne_zero_at_one K)
  -- The pinned provider's last character is subscript zero (U+2080).
  run_tac do
    let provider := Lean.mkIdent (Lean.Name.str `Complex.Hadamard.EntireOfOrderAtMost
      ("summable_norm_inv_pow_divisorZeroIndex".push (Char.ofNat 8320)))
    let orderProof := Lean.mkIdent `hOrder
    let nontrivialProof := Lean.mkIdent `hNontrivial
    let result := Lean.mkIdent `hProvider
    Lean.Elab.Tactic.evalTactic
      ( <- `(tactic| have $result := $provider $orderProof zero_le_one $nontrivialProof))
  rw [Nat.floor_one] at hProvider
  exact hProvider

/-- The entire completion is a genus-one Hadamard product with an affine
exponential factor. Its nonzero value at the origin removes the monomial. -/
private theorem completedDedekindPoleCleared_hadamard :
    exists P : Polynomial Complex, And (P.degree <= 1)
      (forall s : Complex, completedDedekindPoleCleared K s =
        Complex.exp (P.eval s) *
          divisorCanonicalProduct 1 (completedDedekindPoleCleared K) univ s) := by
  have hZero : Not (completedDedekindPoleCleared K 0 = 0) := by
    rw [completedDedekindPoleCleared_functionalEquation K 0, sub_zero]
    exact completedDedekindPoleCleared_ne_zero_at_one K
  have hOrigin : analyticOrderNatAt (completedDedekindPoleCleared K) 0 = 0 := by
    by_contra h
    exact hZero (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
  have hNontrivial : exists z : Complex, Not (completedDedekindPoleCleared K z = 0) :=
    Exists.intro 0 hZero
  choose P hP using hadamard_factorization_of_order zero_le_one hNontrivial
    (completedDedekindPoleCleared_entireOfOrderAtMost_one K)
  refine Exists.intro P (And.intro ?_ ?_)
  case refine_1 => simpa only [Nat.floor_one, Nat.cast_one] using hP.1
  case refine_2 =>
    intro s
    simpa only [Nat.floor_one, hOrigin, pow_zero, mul_one] using hP.2 s

/-- Away from zeros, the completed logarithmic derivative equals an affine
factor's constant derivative plus the convergent Hadamard zero terms. -/
theorem completedDedekindPoleCleared_logDeriv_eq_zeroSum :
    exists b : Complex, forall s : Complex, Not (completedDedekindPoleCleared K s = 0) ->
      logDeriv (completedDedekindPoleCleared K) s =
        b + tsum (fun i : DedekindCompletedZeroIndex K =>
          1 / (s - completedDedekindZero K i) + 1 / completedDedekindZero K i) := by
  choose P hP using completedDedekindPoleCleared_hadamard K
  have hPD : P.natDegree <= 1 := Polynomial.natDegree_le_iff_degree_le.mpr hP.1
  have hPC : P.derivative = Polynomial.C (P.coeff 1) := by
    apply Polynomial.ext
    intro n
    cases n with
    | zero => simp [Polynomial.coeff_derivative]
    | succ n =>
      have hN : P.natDegree < n + 1 + 1 := hPD.trans_lt (by omega)
      have h0 : P.coeff (n + 1 + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hN
      simp [Polynomial.coeff_derivative, h0]
  refine Exists.intro (P.coeff 1) ?_
  intro s hs
  let f := completedDedekindPoleCleared K
  let G := divisorCanonicalProduct 1 f (univ : Set Complex)
  have hFunctions : f = fun z => Complex.exp (P.eval z) * G z := funext hP.2
  have hAway (i : DedekindCompletedZeroIndex K) :
      Not (s = completedDedekindZero K i) := by
    intro h
    apply hs
    rw [h]
    exact completedDedekindZero_is_zero K i
  have hSum := summable_completedDedekindZero_inv_sq K
  have hExp : HasDerivAt (fun z => Complex.exp (P.eval z))
      (Complex.exp (P.eval s) * P.derivative.eval s) s :=
    (Complex.hasDerivAt_exp (P.eval s)).comp s (P.hasDerivAt s)
  have hExpLog : logDeriv (fun z => Complex.exp (P.eval z)) s = P.derivative.eval s := by
    rw [logDeriv_apply, hExp.deriv]
    field_simp [Complex.exp_ne_zero]
  have hG : Not (G s = 0) :=
    divisorCanonicalProduct_ne_zero_of_forall_ne 1 f hSum hAway
  have hGD : DifferentiableAt Complex G s :=
    differentiableAt_divisorCanonicalProduct_univ 1 f hSum s
  change logDeriv f s = _
  rw [hFunctions, logDeriv_mul (f := fun z => Complex.exp (P.eval z))
    s (Complex.exp_ne_zero _) hG hExp.differentiableAt hGD]
  rw [hExpLog, hPC, Polynomial.eval_C]
  congr 1
  exact logDeriv_divisorCanonicalProduct_one_eq_tsum hSum hAway hG

/-- The separate Hadamard terms are summable at any point off the zero set. -/
theorem summable_completedDedekindZero_logDerivTerm {s : Complex}
    (hs : Not (completedDedekindPoleCleared K s = 0)) :
    Summable (fun i : DedekindCompletedZeroIndex K =>
      1 / (s - completedDedekindZero K i) + 1 / completedDedekindZero K i) := by
  have hAway (i : DedekindCompletedZeroIndex K) :
      Not (s = completedDedekindZero K i) := by
    intro h
    apply hs
    rw [h]
    exact completedDedekindZero_is_zero K i
  have hSum := summable_completedDedekindZero_inv_sq K
  run_tac do
    let name := ("summable_logDerivTerms_divisorZeroIndex".push (Char.ofNat 8320)) ++
      "_of_summable_inv_sq"
    let provider := Lean.mkIdent (Lean.Name.str `Complex.Hadamard name)
    let sumProof := Lean.mkIdent `hSum
    let awayProof := Lean.mkIdent `hAway
    let cmd <- `(tactic| exact $provider $sumProof $awayProof)
    Lean.Elab.Tactic.evalTactic cmd

end Robin1984.GRH
