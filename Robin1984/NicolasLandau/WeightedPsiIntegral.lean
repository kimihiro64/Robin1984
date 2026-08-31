import Mathlib.NumberTheory.Chebyshev
import Robin1984.NicolasLandau.WeightedGammaPairing

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# Arithmetic reconstruction of Robin's weighted Chebyshev integral

Prime-power indicator functions express the von Mangoldt sum under Robin's
cutoff weight. Their integrability and a summable norm bound justify exchanging
the series and integral. The resulting identity reconstructs the weighted
prime-power sum as the integral of `psi` against the same weight.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set

theorem norm_robinCutoffMellinTest_le
    (n : Nat) {x y : Real} (hx : 1 < x) (hy : 0 < y) :
    norm (robinCutoffMellinTest n x y) <=
      Inv.inv (Real.log x) * y ^ (-(n : Real)) := by
  have hNorm : forall r : Real, 1 < r ->
      norm ((r : Complex)^(-(n : Complex)) *
        (((Inv.inv (Real.log r) : Real) : Complex))) =
      r ^ (-(n : Real)) * Inv.inv (Real.log r) := by
    intro r hr
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans Real.zero_lt_one hr),
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.log_pos hr))]
    simp
  by_cases hxy : y <= x
  . simp only [robinCutoffMellinTest, if_pos hxy]
    rw [hNorm x hx]
    have hPow : x ^ (-(n : Real)) <= y ^ (-(n : Real)) :=
      Real.rpow_le_rpow_of_nonpos hy hxy (neg_nonpos.mpr (Nat.cast_nonneg n))
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hPow (inv_nonneg.mpr (Real.log_pos hx).le)
  . have hyOne : 1 < y := lt_trans hx (lt_of_not_ge hxy)
    simp only [robinCutoffMellinTest, if_neg hxy]
    rw [hNorm y hyOne]
    have hLog : Real.log x <= Real.log y :=
      (Real.log_le_log_iff (lt_trans Real.zero_lt_one hx) hy).mpr (le_of_not_ge hxy)
    have hInv : Inv.inv (Real.log y) <= Inv.inv (Real.log x) := by
      simpa only [one_div] using one_div_le_one_div_of_le (Real.log_pos hx) hLog
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hInv (Real.rpow_nonneg hy.le _)

/-- Absolute convergence of the prime-power cutoff sum follows from the
ordinary von Mangoldt Dirichlet series, including both sides of the cutoff. -/
theorem summable_robinPrimePowerCutoff
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    Summable (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
      robinCutoffMellinTest n x (m : Real)) := by
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hnRe : 1 < (n : Complex).re := by simp; linarith
  have hMajor := (robin_summable_vonMangoldt_cpow hnRe).norm.mul_left (Inv.inv (Real.log x))
  apply hMajor.of_norm_bounded
  intro m
  by_cases hm : m = 0
  . simp [hm]
  . have hmPos : 0 < (m : Real) := by exact_mod_cast Nat.pos_of_ne_zero hm
    rw [norm_mul]
    calc
      norm (ArithmeticFunction.vonMangoldt m : Complex) * norm (robinCutoffMellinTest n x m) <=
          norm (ArithmeticFunction.vonMangoldt m : Complex) *
            (Inv.inv (Real.log x) * (m : Real) ^ (-(n : Real))) :=
        mul_le_mul_of_nonneg_left (norm_robinCutoffMellinTest_le n hx hmPos) (norm_nonneg _)
      _ = Inv.inv (Real.log x) *
          norm ((ArithmeticFunction.vonMangoldt m : Complex) / (m : Complex) ^ (n : Complex)) := by
        rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm)]
        simp only [Complex.natCast_re]
        rw [Real.rpow_neg hmPos.le]
        ring

def robinPrimePowerIndicator (n m : Nat) (t : Real) : Real :=
  (Ici (m : Real)).indicator
    (fun u : Real => ArithmeticFunction.vonMangoldt m * robinRealWeight n u) t

theorem robinPrimePowerIndicator_nonneg
    {n m : Nat} {t : Real} (ht : 1 < t) :
    0 <= robinPrimePowerIndicator n m t := by
  unfold robinPrimePowerIndicator
  by_cases hm : (m : Real) <= t
  . rw [Set.indicator_of_mem (s := Ici (m : Real)) hm]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (robinRealWeight_nonneg ht)
  . rw [Set.indicator_of_notMem (s := Ici (m : Real)) hm]

theorem integrableOn_robinPrimePowerIndicator
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) (m : Nat) :
    IntegrableOn (robinPrimePowerIndicator n m) (Ioi x) := by
  exact ((integrableOn_robinRealWeight hn hx).const_mul (ArithmeticFunction.vonMangoldt m)).indicator
    measurableSet_Ici

theorem complex_integral_robinRealWeight
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    ((integral (volume.restrict (Ioi x)) (robinRealWeight n) : Real) : Complex) =
      (x : Complex) ^ (-(n : Complex)) * (((Inv.inv (Real.log x) : Real) : Complex)) := by
  rw [integral_robinRealWeight hn hx, Complex.ofReal_mul,
    Complex.ofReal_cpow (lt_trans Real.zero_lt_one hx).le]
  simp

/-- One prime-power contribution is exactly the integral of its surviving
step against Robin's weight. -/
theorem integral_robinPrimePowerIndicator
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) (m : Nat) :
    integral (volume.restrict (Ioi x))
        (fun t : Real => (robinPrimePowerIndicator n m t : Complex)) =
      (ArithmeticFunction.vonMangoldt m : Complex) * robinCutoffMellinTest n x (m : Real) := by
  rw [integral_complex_ofReal]
  by_cases hm : (m : Real) <= x
  . have hIntegral : integral (volume.restrict (Ioi x)) (robinPrimePowerIndicator n m) =
        ArithmeticFunction.vonMangoldt m *
          integral (volume.restrict (Ioi x)) (robinRealWeight n) := by
      calc
        integral (volume.restrict (Ioi x)) (robinPrimePowerIndicator n m) =
            integral (volume.restrict (Ioi x)) (fun t : Real =>
              ArithmeticFunction.vonMangoldt m * robinRealWeight n t) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          exact Set.indicator_of_mem (s := Ici (m : Real)) (le_trans hm (le_of_lt ht)) _
        _ = _ := integral_const_mul _ _
    rw [hIntegral, Complex.ofReal_mul, complex_integral_robinRealWeight hn hx]
    simp only [robinCutoffMellinTest, if_pos hm]
  . have hmGt : x < (m : Real) := lt_of_not_ge hm
    have hmOne : 1 < (m : Real) := lt_trans hx hmGt
    have hSet : Set.inter (Ioi x) (Ici (m : Real)) = Ici (m : Real) := by
      apply inter_eq_right.mpr
      intro t ht
      exact lt_of_lt_of_le hmGt ht
    have hIntegral : integral (volume.restrict (Ioi x)) (robinPrimePowerIndicator n m) =
        ArithmeticFunction.vonMangoldt m *
          integral (volume.restrict (Ioi (m : Real))) (robinRealWeight n) := by
      unfold robinPrimePowerIndicator
      rw [setIntegral_indicator measurableSet_Ici]
      change integral (volume.restrict (Set.inter (Ioi x) (Ici (m : Real))))
        (fun t : Real => ArithmeticFunction.vonMangoldt m * robinRealWeight n t) = _
      rw [hSet, integral_Ici_eq_integral_Ioi, integral_const_mul]
    rw [hIntegral, Complex.ofReal_mul, complex_integral_robinRealWeight hn hmOne]
    simp only [robinCutoffMellinTest, if_neg hm]

theorem summable_integral_norm_robinPrimePowerIndicators
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    Summable (fun m : Nat => integral (volume.restrict (Ioi x))
      (fun t : Real => norm (robinPrimePowerIndicator n m t : Complex))) := by
  have hnOne : 1 <= n := by omega
  have hMajor := (summable_robinPrimePowerCutoff hn hx).norm
  apply Summable.of_nonneg_of_le
    (fun m => integral_nonneg (fun t => norm_nonneg (robinPrimePowerIndicator n m t : Complex)))
    (fun m => ?_) hMajor
  have hReal := integrableOn_robinPrimePowerIndicator hnOne hx m
  have hComplex : IntegrableOn
      (fun t : Real => (robinPrimePowerIndicator n m t : Complex)) (Ioi x) := hReal.ofReal
  calc
    integral (volume.restrict (Ioi x)) (fun t : Real => norm (robinPrimePowerIndicator n m t : Complex)) =
        integral (volume.restrict (Ioi x)) (robinPrimePowerIndicator n m) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (robinPrimePowerIndicator_nonneg (lt_trans hx ht))]
    _ = (integral (volume.restrict (Ioi x))
        (fun t : Real => (robinPrimePowerIndicator n m t : Complex))).re := by
      rw [integral_complex_ofReal, Complex.ofReal_re]
    _ = ((ArithmeticFunction.vonMangoldt m : Complex) *
        robinCutoffMellinTest n x (m : Real)).re := by
      rw [integral_robinPrimePowerIndicator hnOne hx]
    _ <= norm ((ArithmeticFunction.vonMangoldt m : Complex) *
        robinCutoffMellinTest n x (m : Real)) :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)

theorem tsum_robinPrimePowerIndicators
    (n : Nat) {t : Real} (ht : 0 <= t) :
    tsum (fun m : Nat => (robinPrimePowerIndicator n m t : Complex)) =
      (Chebyshev.psi t : Complex) * (robinRealWeight n t : Complex) := by
  have hSupport : forall m : Nat, Not (Membership.mem (Finset.Icc 0 (Nat.floor t)) m) ->
      (robinPrimePowerIndicator n m t : Complex) = 0 := by
    intro m hm
    have hmFloor : Not (m <= Nat.floor t) := by
      intro hmLe
      exact hm (Finset.mem_Icc.mpr (And.intro (Nat.zero_le m) hmLe))
    have hmT : Not ((m : Real) <= t) := by
      intro hmLe
      exact hmFloor ((Nat.le_floor_iff ht).mpr hmLe)
    simp only [robinPrimePowerIndicator,
      Set.indicator_of_notMem (s := Ici (m : Real)) hmT, Complex.ofReal_zero]
  rw [tsum_eq_sum hSupport]
  calc
    Finset.sum (Finset.Icc 0 (Nat.floor t)) (fun m : Nat =>
        (robinPrimePowerIndicator n m t : Complex)) =
      Finset.sum (Finset.Icc 0 (Nat.floor t)) (fun m : Nat =>
        (ArithmeticFunction.vonMangoldt m : Complex) * (robinRealWeight n t : Complex)) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmT : (m : Real) <= t := (Nat.le_floor_iff ht).mp (Finset.mem_Icc.mp hm).2
      simp only [robinPrimePowerIndicator,
        Set.indicator_of_mem (s := Ici (m : Real)) hmT, Complex.ofReal_mul]
    _ = _ := by
      rw [<- Finset.sum_mul, Chebyshev.psi_eq_sum_Icc]
      push_cast
      rfl

/-- The arithmetic cutoff sum equals the complete weighted Chebyshev
integral, including every prime power at its actual threshold. -/
theorem robinPrimePowerSum_eq_integral_psi_weight
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
        robinCutoffMellinTest n x (m : Real)) =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        ((Chebyshev.psi t * robinRealWeight n t : Real) : Complex)) := by
  have hnOne : 1 <= n := by omega
  have hF : forall m : Nat, IntegrableOn
      (fun t : Real => (robinPrimePowerIndicator n m t : Complex)) (Ioi x) := by
    intro m
    exact (integrableOn_robinPrimePowerIndicator hnOne hx m).ofReal
  calc
    tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
        robinCutoffMellinTest n x (m : Real)) =
      tsum (fun m : Nat => integral (volume.restrict (Ioi x))
        (fun t : Real => (robinPrimePowerIndicator n m t : Complex))) := by
      apply tsum_congr
      intro m
      exact (integral_robinPrimePowerIndicator hnOne hx m).symm
    _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
        tsum (fun m : Nat => (robinPrimePowerIndicator n m t : Complex))) :=
      integral_tsum_of_summable_integral_norm hF (summable_integral_norm_robinPrimePowerIndicators hn hx)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [tsum_robinPrimePowerIndicators n (lt_trans (lt_trans Real.zero_lt_one hx) ht).le,
        Complex.ofReal_mul]

theorem integrableOn_complex_psi_robinRealWeight
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real => ((Chebyshev.psi t * robinRealWeight n t : Real) : Complex))
      (Ioi x) := by
  have hnOne : 1 <= n := by omega
  have hF : forall m : Nat, IntegrableOn
      (fun t : Real => (robinPrimePowerIndicator n m t : Complex)) (Ioi x) := by
    intro m
    exact (integrableOn_robinPrimePowerIndicator hnOne hx m).ofReal
  have hInt : IntegrableOn (fun t : Real =>
      tsum (fun m : Nat => (robinPrimePowerIndicator n m t : Complex))) (Ioi x) :=
    integrable_complex_series_of_integral_norm hF (summable_integral_norm_robinPrimePowerIndicators hn hx)
  apply hInt.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [tsum_robinPrimePowerIndicators n (lt_trans (lt_trans Real.zero_lt_one hx) ht).le,
    Complex.ofReal_mul]

end

end Robin1984
