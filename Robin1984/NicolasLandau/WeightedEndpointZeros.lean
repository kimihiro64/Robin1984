import Robin1984.NicolasLandau.RobinWeightedIntegral
import Robin1984.NicolasLandau.WeightedEndpoint
import Robin1984.NicolasLandau.WeightedExplicitFormula
import Robin1984.NicolasLandau.WeightedGammaPairing
import Robin1984.NicolasLandau.XiDivisorCriticalLine
import Robin1984.NicolasLandau.XiZeroConstant
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# Absolute interchange of the complete zero sum at n = 1

An integrable majorant bounds every reweighted zero atom uniformly by the
inverse-square xi-zero sum. Summability of the integrated norms justifies
interchanging the complete multiplicity-counted zero series with the endpoint
integral, yielding the reweighted zero-sum identity at `n = 1`.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

def robinEndpointZeroMajorant (t : Real) : Real :=
  2 * (t^(-(3 / 2 : Real)) * Inv.inv (Real.log t)) +
    t^(-(3 / 2 : Real)) * Inv.inv ((Real.log t)^2) +
    (4 / 3 : Real) * (t^(-(3 / 2 : Real)) * Inv.inv ((Real.log t)^3))

theorem integrableOn_robinEndpointZeroMajorant {x : Real} (hx : 1 < x) :
    IntegrableOn robinEndpointZeroMajorant (Ioi x) := by
  have hTerm (k : Nat) : IntegrableOn (fun t : Real =>
      t^(-(3 / 2 : Real)) * Inv.inv ((Real.log t)^k)) (Ioi x) := by
    have hRaw := (integrableOn_cpow_div_log_pow (a := -(3 / 2 : Complex)) hx (by norm_num) k).norm
    apply IntegrableOn.congr_fun hRaw _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans Real.zero_lt_one (lt_trans hx ht)),
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (Real.log_pos (lt_trans hx ht)).le k))]
    norm_num
  have hRaw := ((hTerm 1).const_mul 2).add (hTerm 2) |>.add ((hTerm 3).const_mul (4 / 3 : Real))
  simpa only [robinEndpointZeroMajorant, Pi.add_apply, pow_one] using! hRaw

theorem norm_robinEndpointZeroAtom_le
    {rho : Complex} (hRho : Not (rho = 0)) (hRe : rho.re = (1 / 2 : Real))
    {t : Real} (ht : 1 < t) :
    norm ((robinEndpointReweightDerivative t : Complex) * (robinZeroKernel 2 rho t / rho)) <=
      (Inv.inv (norm rho))^2 * robinEndpointZeroMajorant t := by
  have hDerivative := robinEndpointReweightDerivative_bounds ht
  have hKernel := norm_robinZeroKernel_div_rho_le_robinXiZeroWeight
    (n := 2) (by norm_num) hRho hRe ht
  have hKernel' : norm (robinZeroKernel 2 rho t / rho) <=
      (Inv.inv (norm rho))^2 * robinEndpointZeroMajorant t := by
    convert hKernel using 1
    unfold robinEndpointZeroMajorant
    norm_num
    ring_nf
    simp
  calc
    _ = robinEndpointReweightDerivative t * norm (robinZeroKernel 2 rho t / rho) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hDerivative.1]
    _ <= 1 * norm (robinZeroKernel 2 rho t / rho) :=
      mul_le_mul_of_nonneg_right hDerivative.2 (norm_nonneg _)
    _ <= _ := by simpa only [one_mul] using hKernel'

theorem integrableOn_robinEndpointZeroAtom
    {rho : Complex} {x : Real} (hx : 1 < x) (hRe : rho.re < 1) :
    IntegrableOn (fun t : Real =>
      (robinEndpointReweightDerivative t : Complex) * (robinZeroKernel 2 rho t / rho)) (Ioi x) := by
  have hRaw := (robinZeroKernel_one_reweight hx hRe).1.div_const rho
  apply IntegrableOn.congr_fun hRaw _ measurableSet_Ioi
  intro t ht
  dsimp only
  ring

/-- The n=1 transfer may be integrated through all zeros, with analytic
multiplicity, because the integrated absolute norms are summable. -/
theorem summable_integral_norm_robinEndpointZeroAtoms
    (hRH : RiemannHypothesis) {x : Real} (hx : 1 < x) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm ((robinEndpointReweightDerivative t : Complex) *
          (robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p)))) := by
  have hM := integrableOn_robinEndpointZeroMajorant hx
  have hMajor (p : RiemannXiDivisorZeroIndex) :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm ((robinEndpointReweightDerivative t : Complex) *
          (robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p))) <=
      (Inv.inv (norm (riemannXiDivisorZeroValue p)))^2 *
        integral (volume.restrict (Ioi x)) robinEndpointZeroMajorant := by
    have hRe := riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
    have hInt := integrableOn_robinEndpointZeroAtom hx (show (riemannXiDivisorZeroValue p).re < 1 by linarith)
    calc
      _ <= integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p)))^2 * robinEndpointZeroMajorant t) := by
        apply integral_mono_ae hInt.norm (hM.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact norm_robinEndpointZeroAtom_le (riemannXiDivisorZeroValue_ne_zero p) hRe (lt_trans hx ht)
      _ = _ := integral_const_mul _ _
  exact Summable.of_nonneg_of_le
    (fun p => integral_nonneg (fun t => norm_nonneg _)) hMajor
    (summable_robinXiZeroWeight.mul_right _)

theorem robin_complete_zero_sum_one_reweight
    (hRH : RiemannHypothesis) {x : Real} (hx : 1 < x) :
    And (IntegrableOn (fun t : Real => (robinEndpointReweightDerivative t : Complex) *
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p)) (Ioi x))
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
          robinZeroKernel 1 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) =
        (robinEndpointReweight x : Complex) * tsum (fun p : RiemannXiDivisorZeroIndex =>
          robinZeroKernel 2 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (robinEndpointReweightDerivative t : Complex) * tsum (fun p : RiemannXiDivisorZeroIndex =>
            robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p))) := by
  letI := countable_robinXiDivisorZeroIndex
  let Z (p : RiemannXiDivisorZeroIndex) (t : Real) : Complex :=
    (robinEndpointReweightDerivative t : Complex) *
      (robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p)
  have hInt (p : RiemannXiDivisorZeroIndex) : IntegrableOn (Z p) (Ioi x) := by
    have hRe := riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
    exact integrableOn_robinEndpointZeroAtom hx (by linarith)
  have hNorm : Summable (fun p : RiemannXiDivisorZeroIndex =>
      integral (volume.restrict (Ioi x)) (fun t : Real => norm (Z p t))) :=
    summable_integral_norm_robinEndpointZeroAtoms hRH hx
  have hSumInt : Summable (fun p : RiemannXiDivisorZeroIndex =>
      integral (volume.restrict (Ioi x)) (Z p)) :=
    hNorm.of_norm_bounded (fun p => norm_integral_le_integral_norm _)
  have hSeries := integrable_complex_series_of_integral_norm hInt hNorm
  have hWholeInt : IntegrableOn (fun t : Real => (robinEndpointReweightDerivative t : Complex) *
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel 2 (riemannXiDivisorZeroValue p) t / riemannXiDivisorZeroValue p)) (Ioi x) := by
    apply IntegrableOn.congr_fun hSeries _ measurableSet_Ioi
    intro t ht
    dsimp only [Z]
    rw [tsum_mul_left]
  have hAtom (p : RiemannXiDivisorZeroIndex) :
      robinZeroKernel 1 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p =
        (robinEndpointReweight x : Complex) *
          (robinZeroKernel 2 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) +
          integral (volume.restrict (Ioi x)) (Z p) := by
    have hRe := riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
    have hRaw := (robinZeroKernel_one_reweight hx (show (riemannXiDivisorZeroValue p).re < 1 by linarith)).2
    rw [hRaw, add_div, mul_div_assoc]
    congr 1
    rw [<- integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [Z]
    ring
  refine And.intro hWholeInt ?_
  calc
    _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
        (robinEndpointReweight x : Complex) *
          (robinZeroKernel 2 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) +
          integral (volume.restrict (Ioi x)) (Z p)) := tsum_congr hAtom
    _ = (robinEndpointReweight x : Complex) * tsum (fun p : RiemannXiDivisorZeroIndex =>
          robinZeroKernel 2 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) +
          tsum (fun p : RiemannXiDivisorZeroIndex => integral (volume.restrict (Ioi x)) (Z p)) := by
      rw [((summable_robinZeroKernel_div_rho hRH (by norm_num : 1 <= (2 : Nat)) hx).mul_left
        (robinEndpointReweight x : Complex)).tsum_add hSumInt, tsum_mul_left]
    _ = _ := by
      rw [integral_tsum_of_summable_integral_norm hInt hNorm]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only [Z]
      rw [tsum_mul_left]

end

end Robin1984
