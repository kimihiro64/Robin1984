import Robin1984.Analytic.PrimePowerSecondWeightBounds
import Robin1984.Finite.PrimeSquareAbel
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 analytic implication supplies the surrounding mathematical target.
- Formalization note: The exact coefficient normalization, explicit cutoff choices, and proof interfaces in this module are primarily project-authored.
- PROVENANCE-END
-/

/-!
# The complete prime-square block after endpoint cancellation

The weighted theta tail is decomposed into its main term and explicit error
integrals. Bounds for the zero kernel then identify the second Robin weight
with the prime-square tail kernel. The final theorems retain the endpoint
cancellation and give the lower bound for the complete prime-square block.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

def robinThetaWeightedTailTwo (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.theta t * robinRealWeight 2 t)

theorem integrableOn_robinThetaWeightedTailTwo {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real => Chebyshev.theta t * robinRealWeight 2 t) (Ioi x) := by
  have hMain : IntegrableOn (fun t : Real => t * robinRealWeight 2 t) (Ioi x) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_robinRealWeight (n := 2) (r := 1) hx (by norm_num)
  have hJ := integrableOn_robinPsiWeightedError (n := 2) (by omega) hx
  have hK := integrableOn_robinPrimePowerWeightedTail (n := 2) (by omega) hx
  apply ((hJ.add hMain).sub hK).congr_fun _ measurableSet_Ioi
  intro t _
  dsimp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem robinThetaWeightedTailTwo_eq_main_add_errors {x : Real} (hx : 1 < x) :
    robinThetaWeightedTailTwo x = (robinZeroKernel 2 (1 : Complex) x).re +
      robinPsiWeightedErrorIntegral 2 x - robinPrimePowerWeightedTail 2 x := by
  have hMain : IntegrableOn (fun t : Real => t * robinRealWeight 2 t) (Ioi x) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_robinRealWeight (n := 2) (r := 1) hx (by norm_num)
  have hMainEq : integral (volume.restrict (Ioi x)) (fun t : Real => t * robinRealWeight 2 t) =
      (robinZeroKernel 2 (1 : Complex) x).re := by
    simpa only [Real.rpow_one, Complex.ofReal_one] using integral_rpow_mul_robinRealWeight 2 1 hx
  have hJ := integrableOn_robinPsiWeightedError (n := 2) (by omega) hx
  have hK := integrableOn_robinPrimePowerWeightedTail (n := 2) (by omega) hx
  have hEq : robinThetaWeightedTailTwo x =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (t * robinRealWeight 2 t + (Chebyshev.psi t - t) * robinRealWeight 2 t) -
          (Chebyshev.psi t - Chebyshev.theta t) * robinRealWeight 2 t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    ring
  have hPlus : IntegrableOn (fun t : Real =>
      t * robinRealWeight 2 t + (Chebyshev.psi t - t) * robinRealWeight 2 t) (Ioi x) := hMain.add hJ
  rw [hEq, integral_sub hPlus hK, integral_add hMain hJ, hMainEq]
  rfl

theorem robinZeroKernel_one_two_bounds {x : Real} (hx : 1 < x) :
    And (2 * x^(-(1 : Real)) * Inv.inv (Real.log x) -
        x^(-(1 : Real)) * Inv.inv ((Real.log x)^2) <=
          (robinZeroKernel 2 (1 : Complex) x).re)
      ((robinZeroKernel 2 (1 : Complex) x).re <=
        2 * x^(-(1 : Real)) * Inv.inv (Real.log x)) := by
  have hF := robinZeroKernel_ofReal_eq_main_add_signed_tail 2
    (r := (1 : Real)) (by norm_num) hx
  have hNonneg := robinCpowLogTail_ofReal_re_nonneg (-(1 : Real)) 2 hx
  have hBound := robinCpowLogTail_ofReal_re_le (a := -(1 : Real)) (by norm_num) 2 hx
  norm_num at hF hNonneg hBound
  constructor <;> linarith

theorem robinPrimePowerWeightedTail_nonneg
    {n : Nat} {x : Real} (hx : 1 <= x) :
    0 <= robinPrimePowerWeightedTail n x := by
  unfold robinPrimePowerWeightedTail
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t))
    (robinRealWeight_nonneg (n := n) (lt_of_le_of_lt hx ht))

theorem robinThetaWeightedTailTwo_upper
    (hRH : RiemannHypothesis) {x : Real} (hx : 2 <= x) :
    robinThetaWeightedTailTwo x <=
      2 * x^(-(1 : Real)) * Inv.inv (Real.log x) +
        robinPsiWeightedErrorScalar 2 x := by
  have hxOne : 1 < x := by linarith
  have hIdentity := robinThetaWeightedTailTwo_eq_main_add_errors hxOne
  have hZero := (robinZeroKernel_one_two_bounds hxOne).2
  have hPsi :=
    (robinPsiWeightedErrorIntegral_bounds_all hRH
      (n := 2) (by omega) hx).2
  have hPrime := robinPrimePowerWeightedTail_nonneg
    (n := 2) (by linarith : (1 : Real) <= x)
  rw [hIdentity]
  linarith

theorem robinThetaWeightedTailTwo_lower
    (hRH : RiemannHypothesis) {x : Real} (hx : 366 <= x) :
    2 * x^(-(1 : Real)) * Inv.inv (Real.log x) -
      x^(-(1 : Real)) * Inv.inv ((Real.log x)^2) -
      (9 / 4 : Real) * x^(-(3 / 2 : Real)) * Inv.inv (Real.log x) -
      Real.log (2 * Real.pi) * x^(-(2 : Real)) * Inv.inv (Real.log x) <=
        robinThetaWeightedTailTwo x := by
  have hxOne : 1 < x := by linarith
  have hMain := (robinZeroKernel_one_two_bounds hxOne).1
  have hErrors := robin_second_theta_error_tail_lower hRH hx
  rw [robinThetaWeightedTailTwo_eq_main_add_errors hxOne]
  linarith

theorem robinRealWeight_two_eq_primeSquareTailKernel {t : Real} (ht : 1 < t) :
    robinRealWeight 2 t = Robin1984.FiniteSupport.primeSquareTailKernel t := by
  have htPos : 0 < t := by linarith
  unfold robinRealWeight Robin1984.FiniteSupport.primeSquareTailKernel
  norm_num [Real.rpow_neg htPos.le]
  field_simp

/-- The lower endpoint occurs once with each sign and cancels exactly. The
upper endpoint remains in the identity. -/
theorem robin_complete_prime_square_block_eq
    {s b : Real} (hs : 1 < s) (hsb : s <= b) :
    Chebyshev.theta s / (s^2 * Real.log s) +
        Finset.sum ((Finset.Ioc (Nat.floor s) (Nat.floor b)).filter Nat.Prime)
          (fun p => (Inv.inv (p : Real))^2) =
      Chebyshev.theta b / (b^2 * Real.log b) +
        robinThetaWeightedTailTwo s - robinThetaWeightedTailTwo b := by
  have hAbel := Robin1984.FiniteSupport.primeSquareKernel_abel_tailKernel_form_finite hs hsb
  have hSplit := intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_robinThetaWeightedTailTwo hs) hsb
  rw [intervalIntegral.integral_of_le hsb] at hSplit
  have hKernel : integral (volume.restrict (Ioc s b)) (fun t : Real =>
        Robin1984.FiniteSupport.primeSquareTailKernel t * Chebyshev.theta t) =
      integral (volume.restrict (Ioc s b)) (fun t : Real => Chebyshev.theta t * robinRealWeight 2 t) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [robinRealWeight_two_eq_primeSquareTailKernel (lt_trans hs ht.1)]
    exact mul_comm _ _
  rw [hKernel] at hAbel
  unfold Robin1984.FiniteSupport.primeSquareKernel at hAbel
  change robinThetaWeightedTailTwo s - robinThetaWeightedTailTwo b = _ at hSplit
  rw [<- hSplit] at hAbel
  rw [hAbel]
  ring

theorem robin_complete_prime_square_block_lower
    (hRH : RiemannHypothesis) {s b : Real} (hs : 366 <= s) (hsb : s <= b) :
    2 * s^(-(1 : Real)) * Inv.inv (Real.log s) -
      s^(-(1 : Real)) * Inv.inv ((Real.log s)^2) -
      (9 / 4 : Real) * s^(-(3 / 2 : Real)) * Inv.inv (Real.log s) -
      Real.log (2 * Real.pi) * s^(-(2 : Real)) * Inv.inv (Real.log s) -
      2 * b^(-(1 : Real)) * Inv.inv (Real.log b) -
      robinPsiWeightedErrorScalar 2 b <=
        Chebyshev.theta s / (s^2 * Real.log s) +
          Finset.sum ((Finset.Ioc (Nat.floor s) (Nat.floor b)).filter Nat.Prime)
            (fun p => (Inv.inv (p : Real))^2) := by
  have hsOne : 1 < s := by linarith
  have hbOne : 1 < b := lt_of_lt_of_le hsOne hsb
  have hbLog := Real.log_pos hbOne
  have hBoundary : 0 <= Chebyshev.theta b / (b^2 * Real.log b) := by
    exact div_nonneg (Chebyshev.theta_nonneg b) (by positivity)
  have hLower := robinThetaWeightedTailTwo_lower hRH hs
  have hUpper := robinThetaWeightedTailTwo_upper hRH (by linarith : 2 <= b)
  rw [robin_complete_prime_square_block_eq hsOne hsb]
  linarith

end

end Robin1984
