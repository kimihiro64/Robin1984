import Robin1984.NicolasLandau.NicolasOscillation
import Robin1984.NicolasLandau.WeightedEndpoint
import Robin1984.NicolasLandau.WeightedPsiError
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Arithmetic integrability at Robin's n=1 endpoint

The Nicolas tail's integrability uses the proved unconditional MediumPNT
through RS_prime.integrableOn_deriv_inv_div_log. It does not use the
unproved Rosser-Schoenfeld theorem_12.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

theorem robinRealWeight_one_eq_nicolasTailKernel {t : Real} (ht : 1 < t) :
    robinRealWeight 1 t = nicolasTailKernel t := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  unfold robinRealWeight nicolasTailKernel
  norm_num [Real.rpow_neg htPos.le]
  field_simp [htPos.ne', (Real.log_pos ht).ne'] <;> ring

theorem integrableOn_robinPsiWeightedError_one
    {x : Real} (hx : 2 <= x) :
    IntegrableOn (fun t : Real => (Chebyshev.psi t - t) * robinRealWeight 1 t) (Ioi x) := by
  have hTail : IntegrableOn (fun t : Real =>
      (Chebyshev.psi t - t) * robinRealWeight 1 t) (Ioi 3) := by
    apply nicolasPsiTail_integrableOn_Ioi_three.congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [robinRealWeight_one_eq_nicolasTailKernel (lt_trans (by norm_num : (1 : Real) < 3) ht)]
    rfl
  have hWeight : IntegrableOn (robinRealWeight 1) (Ioc 2 3) :=
    (integrableOn_robinRealWeight (by norm_num : 1 <= (1 : Nat)) (by norm_num : (1 : Real) < 2)).mono_set
      Ioc_subset_Ioi_self
  have hProduct : IntegrableOn (fun t : Real =>
      robinRealWeight 1 t * (Chebyshev.psi t - t)) (Ioc 2 3) := by
    apply hWeight.mul_bdd (c := Chebyshev.psi 3 + 3)
    . exact (Chebyshev.psi_mono.measurable.sub measurable_id).aestronglyMeasurable
    . filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs]
      calc
        abs (Chebyshev.psi t - t) <= abs (Chebyshev.psi t) + abs t := abs_sub _ _
        _ = Chebyshev.psi t + t := by
          rw [abs_of_nonneg (Chebyshev.psi_nonneg t), abs_of_nonneg (by linarith [ht.1])]
        _ <= Chebyshev.psi 3 + 3 := add_le_add (Chebyshev.psi_mono ht.2) ht.2
  have hCompact : IntegrableOn (fun t : Real =>
      (Chebyshev.psi t - t) * robinRealWeight 1 t) (Ioc 2 3) := by
    simpa only [mul_comm] using hProduct
  have hAll := hCompact.union hTail
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (2 : Real) <= 3)] at hAll
  exact hAll.mono_set (Ioi_subset_Ioi hx)

theorem complex_integral_mul_robinRealWeight
    (g : Real -> Real) (n : Nat) (x : Real) :
    integral (volume.restrict (Ioi x)) (fun t : Real =>
        (g t : Complex) * (robinRealWeight n t : Complex)) =
      ((integral (volume.restrict (Ioi x)) (fun t : Real => g t * robinRealWeight n t) : Real) : Complex) := by
  simp_rw [<- Complex.ofReal_mul]
  exact integral_complex_ofReal

theorem robinPsiWeightedErrorIntegral_one_reweight {x : Real} (hx : 2 <= x) :
    And (IntegrableOn (fun t : Real => (robinEndpointReweightDerivative t : Complex) *
        (robinPsiWeightedErrorIntegral 2 t : Complex)) (Ioi x))
      ((robinPsiWeightedErrorIntegral 1 x : Complex) =
        (robinEndpointReweight x : Complex) * (robinPsiWeightedErrorIntegral 2 x : Complex) +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (robinEndpointReweightDerivative t : Complex) * (robinPsiWeightedErrorIntegral 2 t : Complex))) := by
  have hxOne : 1 < x := by linarith
  have hOne : IntegrableOn (fun t : Real =>
      ((Chebyshev.psi t - t : Real) : Complex) * (robinRealWeight 1 t : Complex)) (Ioi x) := by
    have hCast : IntegrableOn (fun t : Real =>
        (((Chebyshev.psi t - t) * robinRealWeight 1 t : Real) : Complex)) (Ioi x) :=
      (integrableOn_robinPsiWeightedError_one hx).ofReal
    simpa only [Complex.ofReal_mul] using! hCast
  have hTwo : IntegrableOn (fun t : Real =>
      ((Chebyshev.psi t - t : Real) : Complex) * (robinRealWeight 2 t : Complex)) (Ioi x) := by
    have hCast : IntegrableOn (fun t : Real =>
        (((Chebyshev.psi t - t) * robinRealWeight 2 t : Real) : Complex)) (Ioi x) :=
      (integrableOn_robinPsiWeightedError (by norm_num : 2 <= (2 : Nat)) hxOne).ofReal
    simpa only [Complex.ofReal_mul] using! hCast
  have hRaw := robin_weighted_integral_reweight hxOne
    (G := fun t : Real => ((Chebyshev.psi t - t : Real) : Complex))
    (Complex.continuous_ofReal.measurable.comp (Chebyshev.psi_mono.measurable.sub measurable_id)) hOne hTwo
  simpa only [complex_integral_mul_robinRealWeight, robinPsiWeightedErrorIntegral] using! hRaw

theorem robinTrivialZeroCorrection_one_reweight {x : Real} (hx : 2 <= x) :
    And (IntegrableOn (fun t : Real => (robinEndpointReweightDerivative t : Complex) *
        (robinTrivialZeroCorrection 2 t : Complex)) (Ioi x))
      ((robinTrivialZeroCorrection 1 x : Complex) =
        (robinEndpointReweight x : Complex) * (robinTrivialZeroCorrection 2 x : Complex) +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (robinEndpointReweightDerivative t : Complex) * (robinTrivialZeroCorrection 2 t : Complex))) := by
  have hxOne : 1 < x := by linarith
  have hInt (n : Nat) (hn : 1 <= n) : IntegrableOn (fun t : Real =>
      (robinTrivialZeroCorrectionFactor t : Complex) * (robinRealWeight n t : Complex)) (Ioi x) := by
    have hCast : IntegrableOn (fun t : Real =>
        ((robinRealWeight n t * robinTrivialZeroCorrectionFactor t : Real) : Complex)) (Ioi x) :=
      (integrableOn_robinTrivialZeroCorrection_integrand hn hx).ofReal
    simpa only [Complex.ofReal_mul, mul_comm] using! hCast
  have hEq (n : Nat) (a : Real) :
      integral (volume.restrict (Ioi a)) (fun t : Real =>
        (robinTrivialZeroCorrectionFactor t : Complex) * (robinRealWeight n t : Complex)) =
        (robinTrivialZeroCorrection n a : Complex) := by
    rw [complex_integral_mul_robinRealWeight]
    unfold robinTrivialZeroCorrection
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    exact mul_comm _ _
  have hRaw := robin_weighted_integral_reweight hxOne
    (G := fun t : Real => (robinTrivialZeroCorrectionFactor t : Complex))
    (by unfold robinTrivialZeroCorrectionFactor; fun_prop)
    (hInt 1 (by norm_num)) (hInt 2 (by norm_num))
  simpa only [hEq] using! hRaw

end

end Robin1984
