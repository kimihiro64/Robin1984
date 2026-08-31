import Robin1984.NicolasLandau.WeightedGammaPairing
import Robin1984.NicolasLandau.XiLogDerivative
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# Robin's weighted explicit formula on the arithmetic side

Every infinite sum is integrated with a proved summable norm majorant.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set

theorem robin_weighted_explicit_constant :
    -logDeriv riemannXi 0 - (1 / 2 : Complex) * (Real.log Real.pi : Complex) -
      (Real.eulerMascheroniConstant : Complex) / 2 - 1 =
        -(Real.log (2 * Real.pi) : Complex) := by
  have hLogs : Real.log (4 * Real.pi) + Real.log Real.pi =
      2 * Real.log (2 * Real.pi) := by
    rw [Real.log_mul (by norm_num : Not ((4 : Real) = 0)) Real.pi_ne_zero,
      Real.log_mul (by norm_num : Not ((2 : Real) = 0)) Real.pi_ne_zero]
    have hFour : Real.log (4 : Real) = Real.log 2 + Real.log 2 := by
      rw [show (4 : Real) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (by norm_num : Not ((2 : Real) = 0))]
    rw [hFour]
    ring
  have hLogsC := congrArg Complex.ofReal hLogs
  push_cast at hLogsC
  have hXi := neg_two_mul_logDeriv_riemannXi_zero_eq
  linear_combination (1 / 2 : Complex) * hXi - (1 / 2 : Complex) * hLogsC

theorem countable_robinXiDivisorZeroIndex : Countable RiemannXiDivisorZeroIndex := by
  have hSupport : Function.support (fun p : RiemannXiDivisorZeroIndex =>
      (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) = Set.univ := by
    ext p
    simp only [Function.mem_support, mem_univ, iff_true]
    exact pow_ne_zero _ (inv_ne_zero (norm_ne_zero_iff.mpr
      (riemannXiDivisorZeroValue_ne_zero p)))
  have hCount := summable_riemannXiDivisorZero_norm_inv_sq.countable_support
  rw [hSupport] at hCount
  exact Set.countable_univ_iff.mp hCount

theorem integrable_complete_xi_test
    (hRH : RiemannHypothesis) {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    Integrable (fun t : Real => H t *
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) := by
  letI := countable_robinXiDivisorZeroIndex
  have hInt := integrable_complex_series_of_integral_norm
    (fun p => integrable_paired_xi_atom hH
      (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p))
    (summable_integral_norm_paired_xi_atoms hRH hH hC hBound)
  apply hInt.congr
  filter_upwards with t
  rw [tsum_mul_left]

/-- The exact arithmetic weighted explicit formula, retaining every zero
with analytic multiplicity and every negative-even gamma term. -/
theorem robinPrimePowerSum_eq_weighted_explicit_series
    (hRH : RiemannHypothesis) {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
      robinCutoffMellinTest n x (m : Real)) =
      robinZeroKernel n 1 x -
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) -
        (Real.log (2 * Real.pi) : Complex) * robinCutoffMellinTest n x 1 +
        tsum (fun k : Nat =>
          robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1))) := by
  choose C hC hBound using exists_robinCutoffMellin_safeLine_majorant hn hx
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcPos : (0 : Real) < 3 / 2 := by norm_num
  have hc : (1 : Real) < 3 / 2 := by norm_num
  have hcLt : (3 / 2 : Real) < n := by linarith
  let K : Complex := (((1 / (2 * Real.pi) : Real) : Complex))
  let H : Real -> Complex := fun t =>
    mellin (robinCutoffMellinTest n x) ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let C0 : Complex := -logDeriv riemannXi 0 -
    (1 / 2 : Complex) * (Real.log Real.pi : Complex) -
      (Real.eulerMascheroniConstant : Complex) / 2
  let Z : Real -> Complex := fun t => H t *
    tsum (fun p : RiemannXiDivisorZeroIndex =>
      1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p)
  let B : Real -> Complex := fun t =>
    H t / ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1)
  let G : Real -> Complex := fun t => H t *
    ((1 / 2 : Complex) * Complex.digamma
      (((3 / 2 : Complex) + (t : Complex) * Complex.I) / 2 + 1) +
        (Real.eulerMascheroniConstant : Complex) / 2)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using! verticalIntegrable_mellin_robinCutoffMellinTest
      hnOne hx hcPos hcLt
  have hZ : Integrable Z := integrable_complete_xi_test hRH hH hC hBound
  have hB : Integrable B := by
    simpa [B] using! integrable_vertical_resolvent hH
      (c := (3 / 2 : Real)) (rho := 1) (by norm_num)
  have hG : Integrable G := integrable_shifted_gamma_test hH hC hBound
  have hConst : Integrable (fun t : Real => C0 * H t) := hH.const_mul C0
  have hSource : forall t : Real,
      (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
        riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t =
        C0 * H t - Z t + B t + G t := by
    intro t
    rw [neg_riemannZeta_logDeriv_eq_xiDivisor_tsum (by simp; norm_num)]
    dsimp only [C0, Z, B, G]
    ring
  have hArithmetic : tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
      robinCutoffMellinTest n x (m : Real)) =
      K * integral volume (fun t : Real =>
        (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
          riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t) := by
    simpa [K, H] using! robinPrimePowerSum_eq_safeLineIntegral hnOne hx hc hcLt
  have hIntegral : integral volume (fun t : Real =>
      (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
        riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t) =
      C0 * integral volume H - integral volume Z + integral volume B + integral volume G := by
    calc
      integral volume (fun t : Real =>
          (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
            riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t) =
          integral volume (fun t : Real => C0 * H t - Z t + B t + G t) :=
        integral_congr_ae (Filter.Eventually.of_forall hSource)
      _ = _ := by
        have hAdd := integral_add ((hConst.sub hZ).add hB) hG
        have hMid := integral_add (hConst.sub hZ) hB
        have hSub := integral_sub hConst hZ
        simp only [Pi.add_apply, Pi.sub_apply] at hAdd hMid hSub
        rw [hAdd, hMid, hSub, integral_const_mul]
  have hAtOne : K * integral volume H = robinCutoffMellinTest n x 1 := by
    have h := mellinInv_mellin_robinCutoffMellinTest hnOne hx hcPos hcLt Real.zero_lt_one
    simpa [mellinInv, RCLike.real_smul_eq_coe_mul, smul_eq_mul, H, K] using! h
  have hZeros : K * integral volume Z =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) := by
    simpa [K, Z, H] using! robinCutoffMellin_complete_zero_pairing hRH hn hx
  have hGamma : K * integral volume G =
      tsum (fun k : Nat =>
        robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1))) := by
    simpa [K, G, H] using! robinCutoffMellin_complete_gamma_pairing hn hx
  have hPole : K * integral volume B = robinZeroKernel n 1 x - robinCutoffMellinTest n x 1 := by
    have h := robinCutoffMellin_resolvent_pairing hnOne hx hcPos hcLt
      (rho := 1) (by norm_num)
    rw [robinCutoffMellinTest_power_tail_eq hx (by norm_num : Not ((1 : Complex) = 0))
      (by simp; linarith : (1 : Complex).re < (n : Real))] at h
    simpa [K, B, H] using! h
  have hC0 : C0 - 1 = -(Real.log (2 * Real.pi) : Complex) := robin_weighted_explicit_constant
  rw [hArithmetic, hIntegral]
  have hAlgebra : K * (C0 * integral volume H - integral volume Z +
      integral volume B + integral volume G) =
      C0 * (K * integral volume H) - K * integral volume Z +
        K * integral volume B + K * integral volume G := by ring
  rw [hAlgebra, hAtOne, hZeros, hPole, hGamma]
  linear_combination robinCutoffMellinTest n x 1 * hC0

end

end Robin1984
