import Robin1984.NicolasLandau.WeightedEndpointArithmetic
import Robin1984.NicolasLandau.WeightedEndpointZeros
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann (1984).
- Formalization note: The retained statement or source-level argument is Robin's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Robin 1984 Lemma 2, including the endpoint n = 1

The weighted psi-error identity was initially proved for the ordinary
positive-weight range. This module establishes the missing endpoint case
`n = 1`, combines it with the existing result for `n >= 2`, and exposes the
zero-sum correction identity and bounds uniformly for every positive `n`.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

theorem robinPsiWeightedErrorIntegral_one_eq_zero_sum_correction
    (hRH : RiemannHypothesis) {x : Real} (hx : 2 <= x) :
    (robinPsiWeightedErrorIntegral 1 x : Complex) =
      -tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel 1 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) -
          (robinTrivialZeroCorrection 1 x : Complex) := by
  have hxOne : 1 < x := by linarith
  let Z (t : Real) : Complex := tsum (fun p : RiemannXiDivisorZeroIndex =>
    robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p)
  have hJ := robinPsiWeightedErrorIntegral_one_reweight hx
  have hC := robinTrivialZeroCorrection_one_reweight hx
  have hZ := robin_complete_zero_sum_one_reweight hRH hxOne
  have hInside : integral (volume.restrict (Ioi x)) (fun t : Real =>
      (robinEndpointReweightDerivative t : Complex) * (robinPsiWeightedErrorIntegral 2 t : Complex)) =
      -integral (volume.restrict (Ioi x)) (fun t : Real =>
        (robinEndpointReweightDerivative t : Complex) * Z t) -
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (robinEndpointReweightDerivative t : Complex) * (robinTrivialZeroCorrection 2 t : Complex)) := by
    calc
      _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
          -((robinEndpointReweightDerivative t : Complex) * Z t) -
            (robinEndpointReweightDerivative t : Complex) * (robinTrivialZeroCorrection 2 t : Complex)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [robinPsiWeightedErrorIntegral_eq_zero_sum_correction hRH
          (by norm_num : 2 <= (2 : Nat)) (le_trans hx ht.le)]
        dsimp only [Z]
        ring
      _ = _ := by
        have hNeg : IntegrableOn (fun t : Real =>
            -((robinEndpointReweightDerivative t : Complex) * Z t)) (Ioi x) := hZ.1.neg
        rw [integral_sub hNeg hC.1, integral_neg]
  rw [hJ.2, robinPsiWeightedErrorIntegral_eq_zero_sum_correction hRH
    (by norm_num : 2 <= (2 : Nat)) hx, hInside, hZ.2, hC.2]
  dsimp only [Z]
  ring

/-- The weighted explicit formula has no missing natural-number endpoint. -/
theorem robinPsiWeightedErrorIntegral_eq_zero_sum_correction_all
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    (robinPsiWeightedErrorIntegral n x : Complex) =
      -tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) -
          (robinTrivialZeroCorrection n x : Complex) := by
  by_cases hOne : n = 1
  . subst n
    exact robinPsiWeightedErrorIntegral_one_eq_zero_sum_correction hRH hx
  . exact robinPsiWeightedErrorIntegral_eq_zero_sum_correction hRH (by omega) hx

/-- Both printed bounds of Robin 1984 Lemma 2 for every n>=1 and x>=2. -/
theorem robinPsiWeightedErrorIntegral_bounds_all
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    And (-robinPsiWeightedErrorScalar n x -
        Real.log (2 * Real.pi) * x^(-(n : Real)) * Inv.inv (Real.log x) <=
          robinPsiWeightedErrorIntegral n x)
      (robinPsiWeightedErrorIntegral n x <= robinPsiWeightedErrorScalar n x) := by
  have hxOne : 1 < x := by linarith
  let Z : Complex := tsum (fun p : RiemannXiDivisorZeroIndex =>
    robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p)
  have hNorm : norm Z <= robinPsiWeightedErrorScalar n x :=
    norm_tsum_robinZeroKernel_div_rho_le_paper hRH hn hxOne
  have hReal := abs_le.mp ((Complex.abs_re_le_norm Z).trans hNorm)
  have hIdentity := congrArg Complex.re
    (robinPsiWeightedErrorIntegral_eq_zero_sum_correction_all hRH hn hx)
  change robinPsiWeightedErrorIntegral n x =
    -Z.re - robinTrivialZeroCorrection n x at hIdentity
  have hCorr := robinTrivialZeroCorrection_bounds hn hx
  constructor <;> linarith [hReal.1, hReal.2, hCorr.1, hCorr.2]

end

end Robin1984
