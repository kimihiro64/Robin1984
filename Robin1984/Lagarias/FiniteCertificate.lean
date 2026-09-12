import Mathlib.NumberTheory.Harmonic.Bounds
import Robin1984.Analytic.EulerLower
import Robin1984.Arithmetic.Definitions
import Robin1984.Lagarias.Definitions

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Lagarias (2001) supplies the finite range and
  elementary target inequality.
- Formalization note: The factor rows and rational analytic certificates are
  a kernel-checkable encoding of the finite verification.
- PROVENANCE-END
-/

/-!
# Finite certificates for Lagarias' criterion

A block combines exact prime-power factorizations with rational lower bounds
for `H_n`, `exp(H_n)`, and `log(H_n)`. The soundness theorem reduces every
finite case to small decidable arithmetic plus standard analytic bounds.
-/

namespace Robin1984

/-- The first `terms` terms of the exponential power series over rationals. -/
def lagariasExpSeriesLower (q : Rat) (terms : Nat) : Rat :=
  Finset.sum (Finset.range terms)
    (fun i => q ^ i / (Nat.factorial i : Nat))

/-- The rational exponential truncation is a lower bound for real exp on the
nonnegative half-line. -/
theorem lagariasExpSeriesLower_le_exp
    {q : Rat} (hq : 0 <= q) (terms : Nat) :
    (lagariasExpSeriesLower q terms : Real) <= Real.exp (q : Real) := by
  unfold lagariasExpSeriesLower
  push_cast
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hq) terms

/-- Harmonic numbers are monotone in their natural index. -/
theorem lagariasHarmonic_monotone : Monotone harmonic := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ]
  exact le_add_of_nonneg_right (by positivity)

/-- A rational gamma-plus-log lower certificate is below the harmonic number. -/
theorem lagariasHarmonicLower_of_euler_log
    {n : Nat} (hn : Not (n = 0)) {harmonicLower : Rat}
    {logLower : Real}
    (hValue :
      (harmonicLower : Real) = (57721 / 100000 : Real) + logLower)
    (hLog : logLower <= Real.log (n : Real)) :
    (harmonicLower : Real) <= (harmonic n : Real) := by
  have hEuler :=
    Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [Real.eulerMascheroniSeq', if_neg hn] at hEuler
  have hGamma := robin_euler_constant_lower
  rw [hValue]
  linarith

/-- Boolean checker for a consecutive divisor-sum range. -/
noncomputable def lagariasSigmaRangeValidBool (first bound : Nat) : Nat -> Bool
  | 0 => true
  | count + 1 =>
      decide (Robin1984.Core.sigmaOneNat first <= bound) &&
        lagariasSigmaRangeValidBool (first + 1) bound count

/-- Consecutive valid ranges concatenate. -/
theorem lagariasSigmaRangeValidBool_add
    (first bound left right : Nat)
    (hLeft : lagariasSigmaRangeValidBool first bound left = true)
    (hRight :
      lagariasSigmaRangeValidBool (first + left) bound right = true) :
    lagariasSigmaRangeValidBool first bound (left + right) = true := by
  induction left generalizing first with
  | zero =>
      simpa using hRight
  | succ left ih =>
      rw [Nat.succ_add, lagariasSigmaRangeValidBool]
      rw [lagariasSigmaRangeValidBool] at hLeft
      have hParts := (Bool.and_eq_true _ _).mp hLeft
      rw [hParts.1, Bool.true_and]
      apply ih (first := first + 1) hParts.2
      convert hRight using 1 <;> omega

/-- Soundness of the direct divisor-sum range checker. -/
theorem sigmaOneNat_le_of_lagariasSigmaRangeValidBool
    {first bound count n : Nat}
    (hRange : lagariasSigmaRangeValidBool first bound count = true)
    (hLower : first <= n) (hUpper : n < first + count) :
    Robin1984.Core.sigmaOneNat n <= bound := by
  induction count generalizing first n with
  | zero =>
      simp only [add_zero] at hUpper
      omega
  | succ count ih =>
      rw [lagariasSigmaRangeValidBool] at hRange
      have hParts := (Bool.and_eq_true _ _).mp hRange
      by_cases hEq : n = first
      case pos =>
        subst n
        exact of_decide_eq_true hParts.1
      case neg =>
        apply ih hParts.2
        . omega
        . omega

/-- One finite interval with its arithmetic and analytic lower certificates. -/
structure LagariasFiniteBlock where
  first : Nat
  sigmaBound : Nat
  harmonicLower : Rat
  expTerms : Nat
  outerLogTerms : Nat
  count : Nat

/-- The fixed-size analytic validity predicate for a finite block. -/
def LagariasFiniteBlock.AnalyticValid (block : LagariasFiniteBlock) : Prop :=
  2 <= block.first /\
    1 <= block.harmonicLower /\
      0 <= lagariasExpSeriesLower block.harmonicLower block.expTerms /\
        0 <=
          Rat.logSeriesLower block.harmonicLower block.outerLogTerms /\
          (block.sigmaBound : Rat) <=
            block.harmonicLower +
              lagariasExpSeriesLower block.harmonicLower block.expTerms *
                Rat.logSeriesLower block.harmonicLower block.outerLogTerms

/-- A block is valid when its analytic and Boolean row checks are valid. -/
def LagariasFiniteBlock.Valid (block : LagariasFiniteBlock) : Prop :=
  block.AnalyticValid /\
    lagariasSigmaRangeValidBool block.first block.sigmaBound block.count = true

/-- Mechanical guard for the fixed-size analytic decidability surface. -/
example : Decidable
    (({ first := 2, sigmaBound := 3, harmonicLower := 1, expTerms := 1,
        outerLogTerms := 1, count := 0 } : LagariasFiniteBlock).AnalyticValid) := by
  simp only [LagariasFiniteBlock.AnalyticValid]
  infer_instance

/-- Mechanical late-range probe for the direct arithmetic checker. -/
example : lagariasSigmaRangeValidBool 5040 19344 1 = true := by
  decide +kernel

/-- A valid block proves Lagarias' inequality throughout its interval. -/
theorem LagariasFiniteBlock.sound
    {block : LagariasFiniteBlock} (hValid : block.Valid)
    (hHarmonicStart :
      (block.harmonicLower : Real) <= (harmonic block.first : Real))
    {n : Nat} (hLower : block.first <= n)
    (hUpper : n < block.first + block.count) :
    ((ArithmeticFunction.sigma 1 n : Nat) : Real) <=
      (harmonic n : Real) +
        Real.exp (harmonic n : Real) * Real.log (harmonic n : Real) := by
  have hAnalytic := hValid.1
  have hRange := hValid.2
  have hHarmonicOne := hAnalytic.2.1
  have hExpNonneg := hAnalytic.2.2.1
  have hOuterLogNonneg := hAnalytic.2.2.2.1
  have hNumeric := hAnalytic.2.2.2.2
  have hSigmaNat : Robin1984.Core.sigmaOneNat n <= block.sigmaBound :=
    sigmaOneNat_le_of_lagariasSigmaRangeValidBool hRange hLower hUpper
  have hSigma :
      ((ArithmeticFunction.sigma 1 n : Nat) : Real) <=
        (block.sigmaBound : Real) := by
    change (Robin1984.Core.sigmaOneNat n : Real) <=
      (block.sigmaBound : Real)
    exact_mod_cast hSigmaNat
  have hHarmonicMono :
      (harmonic block.first : Real) <= (harmonic n : Real) := by
    exact_mod_cast lagariasHarmonic_monotone hLower
  have hHarmonic :
      (block.harmonicLower : Real) <= (harmonic n : Real) :=
    hHarmonicStart.trans hHarmonicMono
  have hHarmonicLowerNonneg : (0 : Real) <= block.harmonicLower := by
    exact_mod_cast (le_trans (by norm_num : (0 : Rat) <= 1) hHarmonicOne)
  have hExpLower :
      (lagariasExpSeriesLower block.harmonicLower block.expTerms : Real) <=
        Real.exp (harmonic n : Real) := by
    exact (lagariasExpSeriesLower_le_exp
      (by exact_mod_cast hHarmonicLowerNonneg) block.expTerms).trans
      (Real.exp_le_exp.mpr hHarmonic)
  have hHarmonicLowerPos : (0 : Real) < block.harmonicLower := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1)
      hHarmonicOne)
  have hLogLower :
      (Rat.logSeriesLower block.harmonicLower
          block.outerLogTerms : Real) <=
        Real.log (harmonic n : Real) := by
    exact (Rat.logSeriesLower_le_log hHarmonicOne
      block.outerLogTerms).trans
      (Real.log_le_log hHarmonicLowerPos hHarmonic)
  have hExpLowerNonneg :
      (0 : Real) <=
        lagariasExpSeriesLower block.harmonicLower block.expTerms := by
    exact_mod_cast hExpNonneg
  have hOuterLowerNonneg :
      (0 : Real) <=
        Rat.logSeriesLower block.harmonicLower block.outerLogTerms := by
    exact_mod_cast hOuterLogNonneg
  have hNumericReal :
      (block.sigmaBound : Real) <=
        (block.harmonicLower : Real) +
          (lagariasExpSeriesLower block.harmonicLower block.expTerms : Real) *
            (Rat.logSeriesLower block.harmonicLower
              block.outerLogTerms : Real) := by
    exact_mod_cast hNumeric
  calc
    ((ArithmeticFunction.sigma 1 n : Nat) : Real) <=
        (block.sigmaBound : Real) := hSigma
    _ <= (block.harmonicLower : Real) +
        (lagariasExpSeriesLower block.harmonicLower block.expTerms : Real) *
          (Rat.logSeriesLower block.harmonicLower
            block.outerLogTerms : Real) := hNumericReal
    _ <= (harmonic n : Real) +
        Real.exp (harmonic n : Real) * Real.log (harmonic n : Real) :=
      add_le_add hHarmonic
        (mul_le_mul hExpLower hLogLower hOuterLowerNonneg
          (Real.exp_pos _).le)

end Robin1984
