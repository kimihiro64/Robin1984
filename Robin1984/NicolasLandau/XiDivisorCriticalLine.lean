import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannXiDivisorZeros

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# Multiplicity-aware xi zeros on the critical line

The xi divisor index records every zero with its analytic multiplicity.  This
module converts each indexed xi zero to a nontrivial zeta zero and applies RH.
-/

namespace Robin1984

noncomputable section

open Complex

/-- Away from zero and one, a zero of xi is a zero of completed zeta. -/
theorem completedRiemannZeta_eq_zero_of_riemannXi_eq_zero
    {z : Complex} (hzZero : Not (z = 0)) (hzOne : Not (z = 1))
    (hXi : riemannXi z = 0) :
    completedRiemannZeta z = 0 := by
  rw [riemannXi_eq_mul_completedRiemannZeta hzZero hzOne] at hXi
  have hNumerator :
      z * (z - 1) * completedRiemannZeta z = 0 :=
    (div_eq_zero_iff.mp hXi).resolve_right (by norm_num)
  rcases mul_eq_zero.mp hNumerator with hFactor | hCompleted
  . rcases mul_eq_zero.mp hFactor with hz | hzSub
    . exact (hzZero hz).elim
    . exact (hzOne (sub_eq_zero.mp hzSub)).elim
  . exact hCompleted

/-- Away from zero and one, a zero of xi is a zero of zeta. -/
theorem riemannZeta_eq_zero_of_riemannXi_eq_zero
    {z : Complex} (hzZero : Not (z = 0)) (hzOne : Not (z = 1))
    (hXi : riemannXi z = 0) :
    riemannZeta z = 0 := by
  have hCompleted :
      completedRiemannZeta z = 0 :=
    completedRiemannZeta_eq_zero_of_riemannXi_eq_zero
      hzZero hzOne hXi
  rw [riemannZeta_def_of_ne_zero hzZero, hCompleted, zero_div]

/-- Under RH, every multiplicity-carrying xi divisor value lies on the
critical line. -/
theorem riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis
    (hRH : RiemannHypothesis) (p : RiemannXiDivisorZeroIndex) :
    (riemannXiDivisorZeroValue p).re = (1 / 2 : Real) := by
  let z : Complex := riemannXiDivisorZeroValue p
  have hzZero : Not (z = 0) :=
    riemannXiDivisorZeroValue_ne_zero p
  have hXi : riemannXi z = 0 :=
    riemannXiDivisorZeroValue_eq_zero p
  have hXiOne : riemannXi (1 : Complex) = 1 / 2 := by
    simpa [riemannXi_zero] using (riemannXi_one_sub (0 : Complex))
  have hzOne : Not (z = 1) := by
    intro hz
    rw [hz, hXiOne] at hXi
    norm_num at hXi
  have hZeta : riemannZeta z = 0 :=
    riemannZeta_eq_zero_of_riemannXi_eq_zero hzZero hzOne hXi
  have hPos : 0 < z.re := by
    by_contra hNotPos
    have hNonpos : z.re <= 0 := le_of_not_gt hNotPos
    have hMirrorXi : riemannXi (1 - z) = 0 := by
      rw [riemannXi_one_sub]
      exact hXi
    have hMirrorZero : Not (1 - z = 0) :=
      sub_ne_zero.mpr (Ne.symm hzOne)
    have hMirrorOne : Not (1 - z = 1) := by
      intro h
      apply hzZero
      exact sub_eq_self.mp h
    have hMirrorZeta : riemannZeta (1 - z) = 0 :=
      riemannZeta_eq_zero_of_riemannXi_eq_zero
        hMirrorZero hMirrorOne hMirrorXi
    have hMirrorRe : 1 <= (1 - z).re := by
      change 1 <= 1 - z.re
      linarith
    exact (riemannZeta_ne_zero_of_one_le_re hMirrorRe hMirrorZeta).elim
  apply hRH z hZeta
  . intro hTrivial
    choose n hn using hTrivial
    rw [hn] at hPos
    norm_num at hPos
    have hFactorNonneg :
        (0 : Real) <= 2 * ((n : Real) + 1) := by
      positivity
    exact (not_lt_of_ge hFactorNonneg) hPos
  . exact hzOne

end

end Robin1984
