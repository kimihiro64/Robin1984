import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import Robin1984.NicolasLandau.XiZeroConstant

/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: The Hadamard factorization and logarithmic derivative of Riemann's xi function.
- Formalization note: The published analytic expansion is imported through the pinned PrimeNumberTheoremAnd development; this module proves the exact identifications required by Robin's weighted formula.
- PROVENANCE-END
-/

/-!
# Multiplicity-aware logarithmic derivative of zeta

This module identifies Kadiri's completed zeta factor with Riemann's xi
function in the half-plane `1 < re s`, then inserts the divisor-indexed
Hadamard expansion.  The zero sum therefore retains analytic multiplicity.
-/

namespace Robin1984

noncomputable section

open Complex
open scoped BigOperators

/-- Kadiri's exponential pi factor is the usual complex power. -/
theorem zetaPiFactor_eq_cpow_ascii (s : Complex) :
    Kadiri.zetaPiFactor s = (Real.pi : Complex) ^ (-(s / 2)) := by
  unfold Kadiri.zetaPiFactor
  rw [Complex.cpow_def_of_ne_zero, Complex.ofReal_log Real.pi_pos.le]
  . ring_nf
  . exact_mod_cast Real.pi_ne_zero

/-- In the Euler-product half-plane, Kadiri's completed factor is xi. -/
theorem completedZetaFactor_eq_riemannXi_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    Kadiri.completedZetaFactor s = riemannXi s := by
  have hsZero : Not (s = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
    linarith
  have hsOne : Not (s = 1) := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
    linarith
  have hHalfRe : 0 < (s / 2).re := by
    simp
    linarith
  have hGammaHalf : Not (Gamma (s / 2) = 0) :=
    Complex.Gamma_ne_zero_of_re_pos hHalfRe
  have hGammaShift :
      Gamma (s / 2 + 1) = (s / 2) * Gamma (s / 2) :=
    Gamma_add_one (s / 2) (div_ne_zero hsZero two_ne_zero)
  have hCompleted :=
    completedRiemannZeta_eq_cpow_mul_Gamma_mul_riemannZeta
      hsZero hGammaHalf
  calc
    Kadiri.completedZetaFactor s =
        (s * (s - 1) / 2) *
          ((Real.pi : Complex) ^ (-s / 2) *
            Gamma (s / 2) * riemannZeta s) := by
      rw [Kadiri.completedZetaFactor, Kadiri.zetaPoleFactor,
        Kadiri.zetaGammaFactor, zetaPiFactor_eq_cpow_ascii,
        hGammaShift]
      rw [show (-(s / 2)) = -s / 2 by ring]
      ring
    _ = (s * (s - 1) / 2) * completedRiemannZeta s := by
      rw [hCompleted]
    _ = riemannXi s := by
      rw [riemannXi_eq_mul_completedRiemannZeta hsZero hsOne]
      ring

/-- The logarithmic derivatives of Kadiri's completed factor and xi agree in
the Euler-product half-plane. -/
theorem logDeriv_completedZetaFactor_eq_riemannXi_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    logDeriv Kadiri.completedZetaFactor s = logDeriv riemannXi s := by
  have hEventually :
      Filter.EventuallyEq (nhds s)
        Kadiri.completedZetaFactor riemannXi := by
    filter_upwards [
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with w hw
    exact completedZetaFactor_eq_riemannXi_of_one_lt_re hw
  exact (logDeriv_congr_nhds hEventually).self_of_nhds

/-- The exact multiplicity-aware Hadamard formula for `-zeta'/zeta` in the
Euler-product half-plane. -/
theorem neg_riemannZeta_logDeriv_eq_xiDivisor_tsum
    {s : Complex} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      -logDeriv riemannXi 0 -
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          1 / (s - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p) +
      1 / (s - 1) -
      (1 / 2 : Complex) * Real.log Real.pi +
      (1 / 2 : Complex) * digamma (s / 2 + 1) := by
  have hsZero : Not (s = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
    linarith
  have hsOne : Not (s = 1) := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num at hRe
    linarith
  have hZeta : Not (riemannZeta s = 0) :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have hGammaDiff :
      forall m : Nat, Not (s / 2 + 1 = -(m : Complex)) := by
    intro m h
    have hRe := congrArg Complex.re h
    simp at hRe
    have hmNonneg : (0 : Real) <= m := by
      exact_mod_cast Nat.zero_le m
    linarith
  have hGamma : Not (Kadiri.zetaGammaFactor s = 0) := by
    unfold Kadiri.zetaGammaFactor
    exact Gamma_ne_zero hGammaDiff
  have hZeroAway :
      forall p : RiemannXiDivisorZeroIndex,
        Not (s = riemannXiDivisorZeroValue p) := by
    intro p hEqual
    have hXi : riemannXi s = 0 := by
      rw [hEqual]
      exact riemannXiDivisorZeroValue_eq_zero p
    have hZetaZero : riemannZeta s = 0 :=
      riemannZeta_eq_zero_of_riemannXi_eq_zero hsZero hsOne hXi
    exact hZeta hZetaZero
  choose P hP using riemannXi_hadamard_factorization_no_monomial
  have hXiLog :=
    logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
      (P := P) (z := s) hP.2 hZeroAway
  have hPolynomial :
      Polynomial.eval s P.derivative = logDeriv riemannXi 0 :=
    riemannXi_hadamardPolynomialDerivative_eval_eq_logDeriv_zero
      hP.1 hP.2 s
  have hHadamard :
      logDeriv Kadiri.completedZetaFactor s =
        logDeriv riemannXi 0 +
          tsum (fun p : RiemannXiDivisorZeroIndex =>
            1 / (s - riemannXiDivisorZeroValue p) +
              1 / riemannXiDivisorZeroValue p) := by
    rw [logDeriv_completedZetaFactor_eq_riemannXi_of_one_lt_re hs,
      hXiLog, hPolynomial]
  exact Kadiri.neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv
    s (logDeriv riemannXi 0)
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
        1 / (s - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))
    hsOne hGammaDiff hGamma hZeta hHadamard

end

end Robin1984
