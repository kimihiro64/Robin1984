import Robin1984.NicolasLandau.XiDivisorCriticalLine

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# Robin's multiplicity-counted xi zero constant

This module evaluates the complete xi divisor sum under RH.  Its index is the
analytic divisor index, so every zero occurs with its proved multiplicity.
-/

namespace Robin1984

noncomputable section

open Complex
open scoped BigOperators
open scoped ComplexConjugate

/-- The functional equation gives xi(1) = xi(0) = 1/2. -/
theorem riemannXi_one_eq_half :
    riemannXi (1 : Complex) = 1 / 2 := by
  simpa [riemannXi_zero] using (riemannXi_one_sub (0 : Complex))

/-- The xi functional equation reverses the logarithmic derivative at the
endpoints zero and one. -/
theorem logDeriv_riemannXi_one_eq_neg_zero :
    logDeriv riemannXi (1 : Complex) = -logDeriv riemannXi 0 := by
  have hOuter :
      HasDerivAt riemannXi
        (deriv riemannXi (1 - (0 : Complex))) (1 - (0 : Complex)) :=
    differentiable_riemannXi.differentiableAt.hasDerivAt
  have hInner :
      HasDerivAt (fun z : Complex => 1 - z) (-1) 0 :=
    (hasDerivAt_id (0 : Complex)).const_sub 1
  have hRaw := hOuter.comp (0 : Complex) hInner
  have hComposite :
      HasDerivAt (fun z : Complex => riemannXi (1 - z))
        (-deriv riemannXi (1 : Complex)) 0 := by
    refine
      (hRaw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall ?_)).congr_deriv ?_
    . intro z
      rfl
    . simp
  have hFunction :
      (fun z : Complex => riemannXi (1 - z)) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  have hDerivZero :
      deriv riemannXi 0 = -deriv riemannXi (1 : Complex) := by
    have h := hComposite.deriv
    rw [hFunction] at h
    exact h
  have hDerivOne :
      deriv riemannXi (1 : Complex) = -deriv riemannXi 0 := by
    have h := congrArg Neg.neg hDerivZero
    simpa using h.symm
  rw [logDeriv_apply, logDeriv_apply, hDerivOne,
    riemannXi_one_eq_half, riemannXi_zero]
  ring

/-- On the RH critical line, the symmetric xi zero term is the real
inverse-square norm weight. -/
theorem riemannXiDivisor_symmetricTerm_eq_norm_inv_sq
    (hRH : RiemannHypothesis) (p : RiemannXiDivisorZeroIndex) :
    1 / (1 - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p =
      (((Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat) : Real) :
        Complex) := by
  let rho : Complex := riemannXiDivisorZeroValue p
  have hRhoZero : Not (rho = 0) :=
    riemannXiDivisorZeroValue_ne_zero p
  have hRe : rho.re = (1 / 2 : Real) :=
    riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
  have hConj : 1 - rho = conj rho := by
    apply Complex.ext
    . rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hRe]
      norm_num
    . simp
  have hOneSubZero : Not (1 - rho = 0) := by
    intro h
    rw [hConj] at h
    apply hRhoZero
    have h' := congrArg conj h
    simpa using h'
  have hNormZero : Not (norm rho = 0) :=
    norm_ne_zero_iff.mpr hRhoZero
  change
    1 / (1 - rho) + 1 / rho =
      (((Inv.inv (norm rho)) ^ (2 : Nat) : Real) : Complex)
  calc
    1 / (1 - rho) + 1 / rho =
        1 / (rho * (1 - rho)) := by
          field_simp [hRhoZero, hOneSubZero]
          ring
    _ = (((Inv.inv (norm rho)) ^ (2 : Nat) : Real) : Complex) := by
      rw [hConj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      field_simp [hNormZero]

/-- Robin's inverse-square xi divisor weights are summable with analytic
multiplicity. -/
theorem summable_robinXiZeroWeight :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) :=
  summable_riemannXiDivisorZero_norm_inv_sq

/-- The derivative of any degree-one xi Hadamard polynomial is the
logarithmic derivative of xi at zero. -/
theorem riemannXi_hadamardPolynomialDerivative_eval_eq_logDeriv_zero
    {P : Polynomial Complex} (hDegree : P.degree <= 1)
    (hFactorization : forall z : Complex,
      riemannXi z =
        Complex.exp (Polynomial.eval z P) *
          Complex.Hadamard.divisorCanonicalProduct 1 riemannXi Set.univ z)
    (z : Complex) :
    Polynomial.eval z P.derivative = logDeriv riemannXi 0 := by
  have hZeroAway :
      forall p : RiemannXiDivisorZeroIndex,
        Not ((0 : Complex) = riemannXiDivisorZeroValue p) := by
    intro p
    exact (riemannXiDivisorZeroValue_ne_zero p).symm
  have hAtZero :=
    logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
      (P := P) (z := (0 : Complex)) hFactorization hZeroAway
  have hZeroFunction :
      (fun p : RiemannXiDivisorZeroIndex =>
        (1 / ((0 : Complex) - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) =
        (fun _p : RiemannXiDivisorZeroIndex => (0 : Complex)) := by
    funext p
    have hpZero : Not (riemannXiDivisorZeroValue p = 0) :=
      riemannXiDivisorZeroValue_ne_zero p
    field_simp [hpZero]
    ring
  have hAtZeroExact :
      logDeriv riemannXi 0 = Polynomial.eval 0 P.derivative := by
    rw [hZeroFunction] at hAtZero
    simpa using hAtZero
  calc
    Polynomial.eval z P.derivative =
        Polynomial.eval 0 P.derivative :=
      Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one
        hDegree z
    _ = logDeriv riemannXi 0 := hAtZeroExact.symm

/-- Under RH, the complete multiplicity-counted xi zero sum equals Robin's
exact value gamma + 2 - log(4*pi). -/
theorem robinXiZeroConstant_eq_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    tsum (fun p : RiemannXiDivisorZeroIndex =>
        (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) =
      Real.eulerMascheroniConstant + 2 -
        Real.log (4 * Real.pi) := by
  choose P hP using riemannXi_hadamard_factorization_no_monomial
  have hDegree : P.degree <= 1 := hP.1
  have hFactorization := hP.2
  have hZeroAway :
      forall p : RiemannXiDivisorZeroIndex,
        Not ((0 : Complex) = riemannXiDivisorZeroValue p) := by
    intro p
    exact (riemannXiDivisorZeroValue_ne_zero p).symm
  have hOneAway :
      forall p : RiemannXiDivisorZeroIndex,
        Not ((1 : Complex) = riemannXiDivisorZeroValue p) := by
    intro p hOne
    have hXi := riemannXiDivisorZeroValue_eq_zero p
    rw [<- hOne, riemannXi_one_eq_half] at hXi
    norm_num at hXi
  have hAtZero :=
    logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
      (P := P) (z := (0 : Complex)) hFactorization hZeroAway
  have hAtOne :=
    logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
      (P := P) (z := (1 : Complex)) hFactorization hOneAway
  have hZeroSum :
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        (1 / ((0 : Complex) - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) = 0 := by
    have hZeroFunction :
        (fun p : RiemannXiDivisorZeroIndex =>
          (1 / ((0 : Complex) - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p)) =
          (fun _p : RiemannXiDivisorZeroIndex => (0 : Complex)) := by
      funext p
      have hpZero : Not (riemannXiDivisorZeroValue p = 0) :=
        riemannXiDivisorZeroValue_ne_zero p
      field_simp [hpZero]
      ring
    rw [hZeroFunction]
    simp
  have hPolynomialZero :
      logDeriv riemannXi 0 = Polynomial.eval 0 P.derivative := by
    rw [hZeroSum, add_zero] at hAtZero
    exact hAtZero
  have hDerivativeConstant :
      Polynomial.eval (1 : Complex) P.derivative =
        Polynomial.eval 0 P.derivative :=
    Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one
      hDegree 1
  have hSymmetricSum :
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        (1 / (1 - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) =
        (-2 : Complex) * logDeriv riemannXi 0 := by
    calc
      tsum (fun p : RiemannXiDivisorZeroIndex =>
          (1 / (1 - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p)) =
          logDeriv riemannXi 1 -
            Polynomial.eval 1 P.derivative := by
              rw [hAtOne]
              ring
      _ = -logDeriv riemannXi 0 -
            Polynomial.eval 0 P.derivative := by
              rw [logDeriv_riemannXi_one_eq_neg_zero,
                hDerivativeConstant]
      _ = (-2 : Complex) * logDeriv riemannXi 0 := by
              rw [hPolynomialZero]
              ring
  have hSymmetricConstant :
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        (1 / (1 - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) =
        (Real.eulerMascheroniConstant : Complex) + 2 -
          (Real.log (4 * Real.pi) : Complex) :=
    hSymmetricSum.trans neg_two_mul_logDeriv_riemannXi_zero_eq
  have hComplex :
      ((tsum (fun p : RiemannXiDivisorZeroIndex =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) :
          Real) :
          Complex) =
        (Real.eulerMascheroniConstant : Complex) + 2 -
          (Real.log (4 * Real.pi) : Complex) := by
    rw [Complex.ofReal_tsum]
    calc
      tsum (fun p : RiemannXiDivisorZeroIndex =>
          (((Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat) : Real) :
            Complex)) =
          tsum (fun p : RiemannXiDivisorZeroIndex =>
            (1 / (1 - riemannXiDivisorZeroValue p) +
              1 / riemannXiDivisorZeroValue p)) := by
                apply tsum_congr
                intro p
                exact
                  (riemannXiDivisor_symmetricTerm_eq_norm_inv_sq
                    hRH p).symm
      _ = (Real.eulerMascheroniConstant : Complex) + 2 -
          (Real.log (4 * Real.pi) : Complex) :=
            hSymmetricConstant
  exact Complex.ofReal_inj.mp (by simpa using hComplex)

end

end Robin1984
