import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Robin1984.Analytic.EulerLower
import Submission.Robin1984.Lagarias.Definitions

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jeffrey C. Lagarias, An Elementary Problem Equivalent
  to the Riemann Hypothesis (2001), Lemma 3.1.
- Formalization note: The proof follows Lagarias' comparison of the harmonic
  number with log(n) plus Euler's constant.
- PROVENANCE-END
-/

/-!
# Elementary comparisons for Lagarias' criterion

This module formalizes the elementary analytic bridge from Robin's bound to
Lagarias' harmonic-number expression.
-/

namespace Robin1984

/-- Lagarias (2001), Lemma 3.1: Robin's comparison term is bounded by the
exponential-harmonic term. -/
theorem robinBound_le_exp_harmonic_mul_log_harmonic
    {n : Nat} (hn : 3 <= n) :
    Real.exp Real.eulerMascheroniConstant * (n : Real) *
        Real.log (Real.log (n : Real)) <=
      Real.exp (harmonic n : Real) * Real.log (harmonic n : Real) := by
  have hnPos : (0 : Real) < (n : Real) := by
    exact_mod_cast (by omega : 0 < n)
  have hnNe : Not (n = 0) := by omega
  have hGamma := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [Real.eulerMascheroniSeq', if_neg hnNe] at hGamma
  have hHarmonic :
      Real.log (n : Real) + Real.eulerMascheroniConstant <
        (harmonic n : Real) := by
    linarith
  have hExp :
      Real.exp Real.eulerMascheroniConstant * (n : Real) <=
        Real.exp (harmonic n : Real) := by
    calc
      Real.exp Real.eulerMascheroniConstant * (n : Real) =
          Real.exp (Real.eulerMascheroniConstant + Real.log (n : Real)) := by
        rw [Real.exp_add, Real.exp_log hnPos]
      _ <= Real.exp (harmonic n : Real) :=
        Real.exp_le_exp.mpr (by linarith)
  have hLogNOne : (1 : Real) < Real.log (n : Real) := by
    rw [Real.lt_log_iff_exp_lt hnPos]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)
  have hLogNPos : (0 : Real) < Real.log (n : Real) :=
    lt_trans zero_lt_one hLogNOne
  have hLogNLeHarmonic :
      Real.log (n : Real) <= (harmonic n : Real) := by
    have hCast : (n : Real) <= ((n + 1 : Nat) : Real) := by
      exact_mod_cast Nat.le_succ n
    exact (Real.log_le_log hnPos hCast).trans (log_add_one_le_harmonic n)
  have hLog :
      Real.log (Real.log (n : Real)) <=
        Real.log (harmonic n : Real) :=
    Real.log_le_log hLogNPos hLogNLeHarmonic
  exact mul_le_mul hExp hLog (Real.log_pos hLogNOne).le
    (Real.exp_pos _).le

end Robin1984
