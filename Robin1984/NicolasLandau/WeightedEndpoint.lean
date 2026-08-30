import Robin1984.Equivalence.WeightedTailReweight
import Robin1984.NicolasLandau.RobinWeightedIntegral
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# Exact transfer of Robin's weight from n = 2 to n = 1

The endpoint reweight and its derivative implement an integration-by-parts
identity between Robin's second and first weights. After proving the derivative
bounds and boundary behavior, the module transfers both the arithmetic
integral and the zero kernel to the endpoint `n = 1`.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

def robinEndpointReweight (t : Real) : Real :=
  t * (Real.log t + 1) / (2 * Real.log t + 1)

def robinEndpointReweightDerivative (t : Real) : Real :=
  Real.log t * (2 * Real.log t + 3) / (2 * Real.log t + 1)^2

theorem hasDerivAt_robinEndpointReweight {t : Real} (ht : 1 < t) :
    HasDerivAt robinEndpointReweight (robinEndpointReweightDerivative t) t := by
  have htZero : Not (t = 0) := ne_of_gt (lt_trans Real.zero_lt_one ht)
  have hLog := Real.log_pos ht
  have hDenom : Not (2 * Real.log t + 1 = 0) := by positivity
  have hNumerator := (hasDerivAt_id t).mul ((Real.hasDerivAt_log htZero).add_const 1)
  have hDenominator := ((Real.hasDerivAt_log htZero).const_mul 2).add_const 1
  have hRaw := hNumerator.div hDenominator hDenom
  change HasDerivAt robinEndpointReweight _ t at hRaw
  apply hRaw.congr_deriv
  unfold robinEndpointReweightDerivative
  dsimp only [Pi.mul_apply, id_eq]
  field_simp [htZero, hDenom] <;> ring

theorem robinEndpointReweightDerivative_bounds {t : Real} (ht : 1 < t) :
    And (0 <= robinEndpointReweightDerivative t) (robinEndpointReweightDerivative t <= 1) := by
  have hLog := Real.log_pos ht
  have hDenom : 0 < (2 * Real.log t + 1)^2 := by positivity
  unfold robinEndpointReweightDerivative
  constructor
  . positivity
  . apply (div_le_one hDenom).mpr
    nlinarith [sq_nonneg (Real.log t)]


theorem robinEndpointReweight_mul_weight_two {t : Real} (ht : 1 < t) :
    robinEndpointReweight t * robinRealWeight 2 t = robinRealWeight 1 t := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have hDenom : Not (2 * Real.log t + 1 = 0) := by
    have hLog := Real.log_pos ht
    positivity
  have hDenom' : Not (Real.log t * 2 + 1 = 0) := by
    simpa only [mul_comm] using hDenom
  unfold robinEndpointReweight robinRealWeight
  norm_num only [Nat.cast_ofNat, Nat.cast_one, one_mul]
  have hTwo : t^(-2 : Real) = Inv.inv (t^2) := by
    norm_num [Real.rpow_neg htPos.le]
  have hThree : t^(-3 : Real) = Inv.inv (t^3) := by
    norm_num [Real.rpow_neg htPos.le]
  rw [hTwo, hThree]
  field_simp [htPos.ne', hDenom, hDenom', (Real.log_pos ht).ne'] <;> ring

theorem continuousOn_robinEndpointReweightDerivative {x : Real} (hx : 1 < x) :
    ContinuousOn robinEndpointReweightDerivative (Ici x) := by
  intro t ht
  have htOne : 1 < t := lt_of_lt_of_le hx ht
  have htZero : Not (t = 0) := ne_of_gt (lt_trans Real.zero_lt_one htOne)
  have hDenom : Not (2 * Real.log t + 1 = 0) := by
    have hLog := Real.log_pos htOne
    positivity
  have hPow : Not ((2 * Real.log t + 1)^2 = 0) := pow_ne_zero 2 hDenom
  apply ContinuousAt.continuousWithinAt
  unfold robinEndpointReweightDerivative
  fun_prop (disch := assumption)

theorem integral_robinEndpointReweightDerivative
    {x t : Real} (hx : 1 < x) (ht : x <= t) :
    integral (volume.restrict (Ioc x t)) robinEndpointReweightDerivative =
      robinEndpointReweight t - robinEndpointReweight x := by
  have hCont : ContinuousOn robinEndpointReweightDerivative (Icc x t) :=
    (continuousOn_robinEndpointReweightDerivative hx).mono (fun a ha => ha.1)
  have hInt : IntervalIntegrable robinEndpointReweightDerivative volume x t :=
    hCont.intervalIntegrable_of_Icc ht
  rw [<- intervalIntegral.integral_of_le ht]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hInt
  intro a ha
  rw [uIcc_of_le ht] at ha
  exact hasDerivAt_robinEndpointReweight (lt_of_lt_of_le hx ha.1)

/-- The same exact transfer applies to the arithmetic error, every zero
kernel, and the complete logarithmic correction. -/
theorem robin_weighted_integral_reweight
    {x : Real} (hx : 1 < x) {G : Real -> Complex} (hG : Measurable G)
    (hOne : IntegrableOn (fun t : Real => G t * (robinRealWeight 1 t : Complex)) (Ioi x))
    (hTwo : IntegrableOn (fun t : Real => G t * (robinRealWeight 2 t : Complex)) (Ioi x)) :
    And (IntegrableOn (fun a : Real => (robinEndpointReweightDerivative a : Complex) *
        integral (volume.restrict (Ioi a))
          (fun t : Real => G t * (robinRealWeight 2 t : Complex))) (Ioi x))
      (integral (volume.restrict (Ioi x))
          (fun t : Real => G t * (robinRealWeight 1 t : Complex)) =
        (robinEndpointReweight x : Complex) * integral (volume.restrict (Ioi x))
          (fun t : Real => G t * (robinRealWeight 2 t : Complex)) +
        integral (volume.restrict (Ioi x)) (fun a : Real =>
          (robinEndpointReweightDerivative a : Complex) * integral (volume.restrict (Ioi a))
            (fun t : Real => G t * (robinRealWeight 2 t : Complex)))) := by
  have hProduct (t : Real) (ht : x < t) :
      (robinEndpointReweight t : Complex) * (G t * (robinRealWeight 2 t : Complex)) =
        G t * (robinRealWeight 1 t : Complex) := by
    calc
      _ = G t * ((robinEndpointReweight t * robinRealWeight 2 t : Real) : Complex) := by
        push_cast
        ring
      _ = _ := by rw [robinEndpointReweight_mul_weight_two (lt_trans hx ht)]
  have hWeighted : IntegrableOn (fun t : Real =>
      (robinEndpointReweight t : Complex) * (G t * (robinRealWeight 2 t : Complex))) (Ioi x) := by
    apply hOne.congr_fun _ measurableSet_Ioi
    intro t ht
    exact (hProduct t ht).symm
  have hResult := robin_complete_tail_reweight
    (h := robinEndpointReweight) (v := robinEndpointReweightDerivative)
    (F := fun t : Real => G t * (robinRealWeight 2 t : Complex))
    (by unfold robinEndpointReweightDerivative; fun_prop)
    (by unfold robinRealWeight; fun_prop)
    (fun a ha => (robinEndpointReweightDerivative_bounds (lt_trans hx ha)).1)
    (fun t ht => ((continuousOn_robinEndpointReweightDerivative hx).mono
      (show Icc x t <= Ici x from fun a ha => ha.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (fun t ht => integral_robinEndpointReweightDerivative hx ht.le) hTwo hWeighted
  refine And.intro hResult.1 ?_
  rw [<- hResult.2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (hProduct t ht).symm

theorem cpow_mul_robinRealWeight_eq
    (n : Nat) (rho : Complex) {t : Real} (ht : 1 < t) :
    (t : Complex)^rho * (robinRealWeight n t : Complex) =
      (t : Complex)^(rho - (n : Complex) - 1) *
        (((n : Real) * Real.log t + 1) / (Real.log t)^2 : Real) := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have htZero : Not ((t : Complex) = 0) := Complex.ofReal_ne_zero.mpr htPos.ne'
  unfold robinRealWeight
  rw [Complex.ofReal_mul, Complex.ofReal_cpow htPos.le]
  push_cast
  rw [<- mul_assoc, <- Complex.cpow_add _ _ htZero]
  congr 2
  ring

theorem robinZeroKernel_eq_integral_cpow_weight
    (n : Nat) (rho : Complex) {x : Real} (hx : 1 < x) :
    robinZeroKernel n rho x = integral (volume.restrict (Ioi x))
      (fun t : Real => (t : Complex)^rho * (robinRealWeight n t : Complex)) := by
  unfold robinZeroKernel
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (cpow_mul_robinRealWeight_eq n rho (lt_trans hx ht)).symm

theorem integrableOn_cpow_mul_robinRealWeight
    {n : Nat} {rho : Complex} {x : Real} (hx : 1 < x) (hRe : rho.re < n) :
    IntegrableOn (fun t : Real => (t : Complex)^rho * (robinRealWeight n t : Complex)) (Ioi x) := by
  have hExp : (rho - (n : Complex) - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re]
    linarith
  have hOne := integrableOn_cpow_div_log_pow hx hExp 1
  have hTwo := integrableOn_cpow_div_log_pow hx hExp 2
  have hRaw := (hOne.const_mul (n : Complex)).add hTwo
  apply IntegrableOn.congr_fun hRaw _ measurableSet_Ioi
  intro t ht
  dsimp only [Pi.add_apply]
  rw [cpow_mul_robinRealWeight_eq n rho (lt_trans hx ht)]
  simp only [pow_one]
  push_cast
  have hLog : Not ((Real.log t : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (lt_trans hx ht)).ne'
  field_simp [hLog] <;> ring

/-- The endpoint transfer is exact for each complex power, including every
nontrivial zero under RH. -/
theorem robinZeroKernel_one_reweight
    {rho : Complex} {x : Real} (hx : 1 < x) (hRe : rho.re < 1) :
    And (IntegrableOn (fun a : Real =>
        (robinEndpointReweightDerivative a : Complex) * robinZeroKernel 2 rho a) (Ioi x))
      (robinZeroKernel 1 rho x = (robinEndpointReweight x : Complex) * robinZeroKernel 2 rho x +
        integral (volume.restrict (Ioi x)) (fun a : Real =>
          (robinEndpointReweightDerivative a : Complex) * robinZeroKernel 2 rho a)) := by
  have hOne : rho.re < (1 : Nat) := by simpa using hRe
  have hTwo : rho.re < (2 : Nat) := by norm_num; linarith
  have hRaw := robin_weighted_integral_reweight hx
    (G := fun t : Real => (t : Complex)^rho) (by fun_prop)
    (integrableOn_cpow_mul_robinRealWeight hx hOne)
    (integrableOn_cpow_mul_robinRealWeight hx hTwo)
  have hInt : IntegrableOn (fun a : Real =>
      (robinEndpointReweightDerivative a : Complex) * robinZeroKernel 2 rho a) (Ioi x) := by
    apply hRaw.1.congr_fun _ measurableSet_Ioi
    intro a ha
    dsimp only
    rw [robinZeroKernel_eq_integral_cpow_weight 2 rho (lt_trans hx ha)]
  refine And.intro hInt ?_
  rw [robinZeroKernel_eq_integral_cpow_weight 1 rho hx,
    robinZeroKernel_eq_integral_cpow_weight 2 rho hx]
  rw [hRaw.2]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro a ha
  dsimp only
  rw [robinZeroKernel_eq_integral_cpow_weight 2 rho (lt_trans hx ha)]

end

end Robin1984
