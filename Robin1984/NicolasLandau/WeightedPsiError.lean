import Robin1984.NicolasLandau.RobinWeightedIntegral
import Robin1984.NicolasLandau.WeightedExplicitFormula
import Robin1984.NicolasLandau.WeightedPsiIntegral
import Robin1984.NicolasLandau.WeightedTrivialCorrection
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# The weighted psi error in Robin's Lemma 2

This module integrates `psi(t) - t` against Robin's real weight and evaluates
the result through the weighted explicit formula. The main identity expresses
the integral as the complete nontrivial-zero contribution plus the exact pole,
archimedean, and trivial-zero corrections, and defines its real scalar form.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set

def robinPsiWeightedErrorIntegral (n : Nat) (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    (Chebyshev.psi t - t) * robinRealWeight n t)

theorem complex_t_mul_robinRealWeight_eq
    (n : Nat) {t : Real} (ht : 1 < t) :
    ((t * robinRealWeight n t : Real) : Complex) =
      (t : Complex)^(-(n : Complex)) *
        (((n : Real) * Real.log t + 1) / (Real.log t)^2 : Real) := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have hPower : t * t^(-(n : Real) - 1) = t^(-(n : Real)) := by
    calc
      t * t^(-(n : Real) - 1) = t^(1 : Real) * t^(-(n : Real) - 1) := by rw [Real.rpow_one]
      _ = t^((1 : Real) + (-(n : Real) - 1)) := (Real.rpow_add htPos _ _).symm
      _ = _ := by congr 1; ring
  have hReal : t * robinRealWeight n t =
      t^(-(n : Real)) * (((n : Real) * Real.log t + 1) / (Real.log t)^2) := by
    unfold robinRealWeight
    rw [<- mul_assoc, hPower]
  rw [hReal, Complex.ofReal_mul, Complex.ofReal_cpow htPos.le]
  simp

theorem robinZeroKernel_one_eq_integral_t_weight
    (n : Nat) {x : Real} (hx : 1 < x) :
    robinZeroKernel n 1 x = integral (volume.restrict (Ioi x))
      (fun t : Real => ((t * robinRealWeight n t : Real) : Complex)) := by
  unfold robinZeroKernel
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show (1 : Complex) - (n : Complex) - 1 = -(n : Complex) by ring]
  exact (complex_t_mul_robinRealWeight_eq n (lt_trans hx ht)).symm

theorem integrableOn_complex_t_robinRealWeight
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real => ((t * robinRealWeight n t : Real) : Complex)) (Ioi x) := by
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hExp : (-(n : Complex)).re < -1 := by simp; linarith
  have hOne := integrableOn_cpow_div_log_pow hx hExp 1
  have hTwo := integrableOn_cpow_div_log_pow hx hExp 2
  have hInt : IntegrableOn (fun t : Real =>
      (n : Complex) * ((t : Complex)^(-(n : Complex)) *
        (((Inv.inv ((Real.log t)^1) : Real) : Complex))) +
      (t : Complex)^(-(n : Complex)) * (((Inv.inv ((Real.log t)^2) : Real) : Complex)))
      (Ioi x) := (hOne.const_mul (n : Complex)).add hTwo
  apply hInt.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [complex_t_mul_robinRealWeight_eq n (lt_trans hx ht)]
  simp only [pow_one]
  push_cast
  have hLog : Not (((Real.log t : Real) : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (lt_trans hx ht)))
  field_simp [hLog] <;> ring

theorem integrableOn_robinPsiWeightedError
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real => (Chebyshev.psi t - t) * robinRealWeight n t) (Ioi x) := by
  have hPsi := integrableOn_complex_psi_robinRealWeight hn hx
  have hMain := integrableOn_complex_t_robinRealWeight hn hx
  have hRaw := (hPsi.sub hMain).re
  have hInt : IntegrableOn (fun t : Real =>
      (((Chebyshev.psi t * robinRealWeight n t : Real) : Complex) -
        ((t * robinRealWeight n t : Real) : Complex)).re) (Ioi x) := by
    simpa only [Pi.sub_apply, RCLike.re_to_complex] using! hRaw
  apply hInt.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  simp only [Complex.sub_re, Complex.ofReal_re]
  ring

/-- The complete weighted explicit formula for n>=2.  The n=1 endpoint is
not included in this theorem. -/
theorem robinPsiWeightedErrorIntegral_eq_zero_sum_correction
    (hRH : RiemannHypothesis) {n : Nat} (hn : 2 <= n) {x : Real} (hx : 2 <= x) :
    (robinPsiWeightedErrorIntegral n x : Complex) =
      -tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) -
          (robinTrivialZeroCorrection n x : Complex) := by
  have hxOne : 1 < x := by linarith
  have hnOne : 1 <= n := by omega
  have hPsi := integrableOn_complex_psi_robinRealWeight hn hxOne
  have hMain := integrableOn_complex_t_robinRealWeight hn hxOne
  have hError : (robinPsiWeightedErrorIntegral n x : Complex) =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        ((Chebyshev.psi t * robinRealWeight n t : Real) : Complex)) -
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        ((t * robinRealWeight n t : Real) : Complex)) := by
    rw [robinPsiWeightedErrorIntegral, <- integral_complex_ofReal]
    have hFunction : (fun t : Real => (((Chebyshev.psi t - t) * robinRealWeight n t : Real) : Complex)) =
        (fun t : Real => ((Chebyshev.psi t * robinRealWeight n t : Real) : Complex) -
          ((t * robinRealWeight n t : Real) : Complex)) := by
      funext t
      push_cast
      ring
    rw [hFunction]
    exact integral_sub hPsi hMain
  rw [hError, <- robinPrimePowerSum_eq_integral_psi_weight hn hxOne,
    <- robinZeroKernel_one_eq_integral_t_weight n hxOne,
    robinPrimePowerSum_eq_weighted_explicit_series hRH hn hxOne]
  have hCorrection := robin_explicit_correction_eq hnOne hx
  linear_combination hCorrection

/-- Robin's printed scalar bound for the nontrivial-zero contribution. -/
def robinPsiWeightedErrorScalar (n : Nat) (x : Real) : Real :=
  (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
    (x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) *
      ((n : Real) + Inv.inv (Real.log x) +
        4 * Inv.inv (((2 * n - 1 : Nat) : Real) * (Real.log x)^2)))


end

end Robin1984
