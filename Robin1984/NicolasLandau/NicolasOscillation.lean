import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime
import Robin1984.Equivalence.OmegaScaleTransfer
import Robin1984.NicolasLandau.NicolasFunction

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# Nicolas's oscillation integrals

This file introduces the exact functions used in Nicolas 1983, Theorem 3(c).
The negative oscillation is the sign used by the `lcmUpto` transfer to Robin's
inequality.
-/

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

/-- Nicolas's first Chebyshev error, denoted `S(x) = theta(x) - x` in the
source. -/
def nicolasThetaError (x : Real) : Real :=
  Chebyshev.theta x - x

/-- Nicolas's second Chebyshev error, denoted `R(x) = psi(x) - x` in the
source. -/
def nicolasPsiError (x : Real) : Real :=
  Chebyshev.psi x - x

/-- The common positive tail kernel in Nicolas's definitions of `K` and `J`:
`t^(-2) * (1 / log t + 1 / log^2 t)`. -/
def nicolasTailKernel (t : Real) : Real :=
  (1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2

/-- Nicolas's theta-error tail `K(x)`. -/
def nicolasK (x : Real) : Real :=
  integral (volume.restrict (Ioi x))
    (fun t => nicolasThetaError t * nicolasTailKernel t)

/-- Nicolas's psi-error tail `J(x)`. -/
def nicolasJ (x : Real) : Real :=
  integral (volume.restrict (Ioi x))
    (fun t => nicolasPsiError t * nicolasTailKernel t)

/-- The complete prime-power tail separating Nicolas's `J` and `K`. -/
def nicolasPrimePowerTail (x : Real) : Real :=
  integral (volume.restrict (Ioi x))
    (fun t => (Chebyshev.psi t - Chebyshev.theta t) * nicolasTailKernel t)

theorem nicolasPsiError_sub_thetaError (x : Real) :
    nicolasPsiError x - nicolasThetaError x =
      Chebyshev.psi x - Chebyshev.theta x := by
  unfold nicolasPsiError nicolasThetaError
  ring


theorem nicolasTailKernel_nonneg {t : Real} (ht : 1 <= t) :
    0 <= nicolasTailKernel t := by
  unfold nicolasTailKernel
  have hLog : 0 <= Real.log t := Real.log_nonneg ht
  positivity

theorem nicolasPrimePowerTail_nonneg {x : Real} (hx : 1 <= x) :
    0 <= nicolasPrimePowerTail x := by
  unfold nicolasPrimePowerTail
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t))
    (nicolasTailKernel_nonneg (le_trans hx ht.le))

/-- PNT+'s proved Mertens summand tail, restated with Mathlib's Euler value
and an ASCII declaration name. -/
theorem nicolasMertensSummandTail_le {x : Real} (hx : 2 <= x) :
    |Finset.sum (Finset.Ioc 0 (Nat.floor x))
        (fun n => Mertens.M_eq_summand n) -
      (Mertens.M - Real.eulerMascheroniConstant)| <= 4 / x := by
  have hTail := Mertens.sum_M_eq_summand_le' hx
  simpa only [Mertens.gamma_eq_eulerMascheroni] using hTail

theorem nicolasMertensProduct_pos (x : Real) :
    0 < nicolasMertensProduct x := by
  classical
  unfold nicolasMertensProduct
  apply Finset.prod_pos
  intro p hp
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primesLE hp
  have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hpOne : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
  have hFrac : (1 : Real) / p < 1 := (div_lt_one hpPos).2 hpOne
  linarith

theorem nicolasLogMertensProduct_eq_summandPrefix_sub_primeReciprocal
    (x : Real) :
    Real.log (nicolasMertensProduct x) =
      Finset.sum (Finset.Ioc 0 (Nat.floor x))
          (fun n => Mertens.M_eq_summand n) -
        Finset.sum (Nat.primesLE (Nat.floor x))
          (fun p => 1 / (p : Real)) := by
  classical
  unfold nicolasMertensProduct
  have hFactors : forall p : Nat,
      Membership.mem (Nat.primesLE (Nat.floor x)) p ->
      Not (1 - 1 / (p : Real) = 0) := by
    intro p hp
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primesLE hp
    have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
    have hpOne : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
    have hFrac : (1 : Real) / p < 1 := (div_lt_one hpPos).2 hpOne
    linarith
  rw [Real.log_prod hFactors]
  change Finset.sum (Nat.primesLE (Nat.floor x))
      (fun p => Real.log (1 - 1 / (p : Real))) = _
  simp only [Mertens.M_eq_summand]
  rw [<- Finset.sum_filter]
  rw [<- Nat.primesLE_eq_filter_Ioc_zero]
  rw [Finset.sum_add_distrib]
  ring

theorem meisselMertensConstant_eq_mertensM :
    meisselMertensConstant = Mertens.M := by
  have hFinset (N : Nat) :
      Finset.filter Nat.Prime (Finset.Iic N) = Nat.primesLE N := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Nat.mem_primesLE]
  have hRS : Tendsto
      (fun x : Real =>
        Finset.sum (Nat.primesLE (Nat.floor x))
          (fun p => 1 / (p : Real)) - Real.log (Real.log x))
      atTop (nhds meisselMertensConstant) := by
    simpa only [hFinset] using RS_prime.mertens_second_theorem
  have hError : Tendsto
      (fun x : Real =>
        Finset.sum (Nat.primesLE (Nat.floor x))
            (fun p => 1 / (p : Real)) -
          Real.log (Real.log x) - Mertens.M)
      atTop (nhds 0) :=
    Mertens.primeReciprocalError_primesLE_isLittleO_one.tendsto_zero_of_tendsto
      (tendsto_const_nhds : Tendsto (fun _ : Real => (1 : Real)) atTop (nhds 1))
  have hMRaw := hError.add
    (tendsto_const_nhds :
      Tendsto (fun _ : Real => Mertens.M) atTop (nhds Mertens.M))
  have hM : Tendsto
      (fun x : Real =>
        Finset.sum (Nat.primesLE (Nat.floor x))
          (fun p => 1 / (p : Real)) - Real.log (Real.log x))
      atTop (nhds Mertens.M) := by
    convert hMRaw using 1
    . funext x
      ring
    . ring
  exact tendsto_nhds_unique hRS hM

theorem nicolasPrimeReciprocalSum_eq
    {x : Real} (hx : 2 <= x) :
    Finset.sum (Nat.primesLE (Nat.floor x))
        (fun p => 1 / (p : Real)) =
      Real.log (Real.log x) + Mertens.M +
        nicolasThetaError x / (x * Real.log x) - nicolasK x := by
  have hFinset :
      Finset.filter Nat.Prime (Finset.Iic (Nat.floor x)) =
        Nat.primesLE (Nat.floor x) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Nat.mem_primesLE]
  have hRS := RS_prime.eq_419 hx
  rw [hFinset, meisselMertensConstant_eq_mertensM] at hRS
  have hIntegral :
      integral (volume.restrict (Ioi x))
          (fun y => (Chebyshev.theta y - y) * (1 + Real.log y) /
            (y ^ 2 * Real.log y ^ 2)) =
        integral (volume.restrict (Ioi x))
          (fun y => nicolasThetaError y * nicolasTailKernel y) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hyPos : 0 < y := lt_trans (by norm_num) (lt_of_le_of_lt hx hy)
    have hyOne : Not (y = 1) := by
      exact ne_of_gt (lt_trans (by norm_num) (lt_of_le_of_lt hx hy))
    have hLog : Not (Real.log y = 0) :=
      Real.log_ne_zero_of_pos_of_ne_one hyPos hyOne
    unfold nicolasThetaError nicolasTailKernel
    field_simp
    ring
  rw [hIntegral] at hRS
  simpa only [nicolasThetaError, nicolasK] using hRS

theorem log_sub_log_le_sub_div
    {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b <= (a - b) / b := by
  calc
    Real.log a - Real.log b = Real.log (a / b) := by
      rw [Real.log_div ha.ne' hb.ne']
    _ <= a / b - 1 :=
      Real.log_le_sub_one_of_pos (div_pos ha hb)
    _ = (a - b) / b := by
      field_simp [hb.ne']

theorem one_lt_chebyshevTheta_of_three_le
    {x : Real} (hx : 3 <= x) :
    1 < Chebyshev.theta x := by
  have hThetaThree : Chebyshev.theta (3 : Real) = Real.log 6 := by
    rw [Chebyshev.theta_eq_log_primorial]
    have hPrimorial : primorial 3 = 6 := by decide
    have hFloor : Nat.floor (3 : Real) = 3 := by norm_num
    rw [hFloor, hPrimorial]
    norm_num
  have hLogSix : (1 : Real) < Real.log 6 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : Real) < 6)]
    exact lt_trans Real.exp_one_lt_three (by norm_num)
  have hThetaMono := Chebyshev.theta_mono hx
  rw [hThetaThree] at hThetaMono
  exact lt_of_lt_of_le hLogSix hThetaMono

theorem nicolasHeightShift_le_thetaEndpoint
    {x : Real} (hx : 3 <= x) :
    Real.log (Real.log (Chebyshev.theta x)) -
        Real.log (Real.log x) <=
      nicolasThetaError x / (x * Real.log x) := by
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : Real) < 3) hx
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num : (1 : Real) < 3) hx
  have hThetaOne : 1 < Chebyshev.theta x :=
    one_lt_chebyshevTheta_of_three_le hx
  have hLogX : 0 < Real.log x := Real.log_pos hxOne
  have hLogTheta : 0 < Real.log (Chebyshev.theta x) :=
    Real.log_pos hThetaOne
  have hOuter := log_sub_log_le_sub_div hLogTheta hLogX
  have hInner := log_sub_log_le_sub_div
    (lt_trans (by norm_num : (0 : Real) < 1) hThetaOne) hxPos
  calc
    Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x)
        <= (Real.log (Chebyshev.theta x) - Real.log x) / Real.log x := hOuter
    _ <= ((Chebyshev.theta x - x) / x) / Real.log x :=
      (div_le_div_iff_of_pos_right hLogX).2 hInner
    _ = nicolasThetaError x / (x * Real.log x) := by
      unfold nicolasThetaError
      field_simp [hxPos.ne', hLogX.ne'] <;> ring

/-- The finite Nicolas logarithm splits exactly into the Mertens summand
remainder, the concave height remainder, and Nicolas's theta-error tail. -/
theorem nicolasLogMertensOscillation_eq_components
    {x : Real} (hx : 3 <= x) :
    nicolasLogMertensOscillation x =
      (Finset.sum (Finset.Ioc 0 (Nat.floor x))
          (fun n => Mertens.M_eq_summand n) -
        (Mertens.M - Real.eulerMascheroniConstant)) +
      (Real.log (Real.log (Chebyshev.theta x)) -
        Real.log (Real.log x) -
        nicolasThetaError x / (x * Real.log x)) +
      nicolasK x := by
  have hxTwo : (2 : Real) <= x := le_trans (by norm_num) hx
  have hThetaOne : 1 < Chebyshev.theta x :=
    one_lt_chebyshevTheta_of_three_le hx
  have hLogTheta : 0 < Real.log (Chebyshev.theta x) :=
    Real.log_pos hThetaOne
  have hProduct : 0 < nicolasMertensProduct x :=
    nicolasMertensProduct_pos x
  unfold nicolasLogMertensOscillation nicolasFunction
  rw [Real.log_mul
      (mul_ne_zero (Real.exp_pos _).ne' hLogTheta.ne') hProduct.ne',
    Real.log_mul (Real.exp_pos _).ne' hLogTheta.ne', Real.log_exp,
    nicolasLogMertensProduct_eq_summandPrefix_sub_primeReciprocal,
    nicolasPrimeReciprocalSum_eq hxTwo]
  ring

/-- Nicolas's finite logarithm is bounded above by its complete theta-error
tail plus the explicit Mertens summand remainder. -/
theorem nicolasLogMertensOscillation_le_K_add_four_div
    {x : Real} (hx : 3 <= x) :
    nicolasLogMertensOscillation x <= nicolasK x + 4 / x := by
  have hxTwo : (2 : Real) <= x := le_trans (by norm_num) hx
  have hSummand := nicolasMertensSummandTail_le hxTwo
  have hSummandUpper :
      Finset.sum (Finset.Ioc 0 (Nat.floor x))
          (fun n => Mertens.M_eq_summand n) -
        (Mertens.M - Real.eulerMascheroniConstant) <= 4 / x :=
    le_trans (le_abs_self _) hSummand
  have hHeight := nicolasHeightShift_le_thetaEndpoint hx
  rw [nicolasLogMertensOscillation_eq_components hx]
  linarith

/-- Nicolas's tail kernel is the negative derivative of `1 / (t * log t)`
on the range relevant to the improper integral. -/
theorem nicolasTailKernel_eq_neg_deriv_inv_mul_log
    {t : Real} (ht : 1 < t) :
    nicolasTailKernel t =
      -deriv (fun s : Real => 1 / s / Real.log s) t := by
  have htPos : 0 < t := lt_trans (by norm_num) ht
  have hLog : 0 < Real.log t := Real.log_pos ht
  have hDeriv := deriv_fun_inv''
    (t.hasDerivAt_mul_log htPos.ne').differentiableAt
    (mul_ne_zero htPos.ne' hLog.ne')
  have hMulDeriv :
      deriv (fun s : Real => s * Real.log s) t = 1 + Real.log t := by
    have hMul := (hasDerivAt_id t).mul (Real.hasDerivAt_log htPos.ne')
    have hMulValue := hMul.deriv
    have hFun : (id * Real.log : Real -> Real) =
        (fun s : Real => s * Real.log s) := by
      funext s
      rfl
    rw [hFun] at hMulValue
    simp only [id_eq, one_mul] at hMulValue
    rw [hMulValue]
    field_simp [htPos.ne']
    ring
  simp only [div_div, fun s : Real => one_div (s * Real.log s), hDeriv,
    hMulDeriv]
  unfold nicolasTailKernel
  field_simp [htPos.ne', hLog.ne']
  ring

/-- The theta-error integrand defining `K` is integrable on its complete
tail.  This is the integrability estimate already proved inside RS (4.19),
transported through the exact derivative identity above. -/
theorem nicolasThetaTail_integrableOn_Ioi_two :
    IntegrableOn
      (fun t => nicolasThetaError t * nicolasTailKernel t) (Ioi 2) := by
  have hBase := RS_prime.integrableOn_deriv_inv_div_log.1.neg
  apply hBase.congr_fun
  . intro t ht
    have htOne : 1 < t := lt_trans (by norm_num) ht
    change -((Chebyshev.theta t - t) *
        deriv (fun s : Real => 1 / s / Real.log s) t) =
      nicolasThetaError t * nicolasTailKernel t
    rw [nicolasTailKernel_eq_neg_deriv_inv_mul_log htOne]
    unfold nicolasThetaError
    ring
  . exact measurableSet_Ioi

theorem nicolasPrimePowerIntegrand_norm_le
    {t : Real} (ht : 3 < t) :
    norm ((Chebyshev.psi t - Chebyshev.theta t) * nicolasTailKernel t) <=
      4 * t ^ (-(3 / 2 : Real)) := by
  have htPos : 0 < t := lt_trans (by norm_num) ht
  have htOne : 1 < t := lt_trans (by norm_num) ht
  have hLog : 0 < Real.log t := Real.log_pos htOne
  have hLogOne : 1 < Real.log t := by
    rw [Real.lt_log_iff_exp_lt htPos]
    exact lt_trans Real.exp_one_lt_three ht
  have hGapNonneg : 0 <= Chebyshev.psi t - Chebyshev.theta t :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi t)
  have hKernelNonneg : 0 <= nicolasTailKernel t :=
    nicolasTailKernel_nonneg htOne.le
  have hGap := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log
    (le_trans (by norm_num) ht.le)
  rw [abs_of_nonneg hGapNonneg] at hGap
  have hInvLog : 1 / Real.log t <= 1 :=
    (div_le_one hLog).2 hLogOne.le
  have hPower : Real.sqrt t / t ^ 2 = t ^ (-(3 / 2 : Real)) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_natCast t 2, div_eq_mul_inv,
      <- Real.rpow_neg htPos.le, <- Real.rpow_add htPos]
    norm_num
  calc
    norm ((Chebyshev.psi t - Chebyshev.theta t) * nicolasTailKernel t) =
        (Chebyshev.psi t - Chebyshev.theta t) * nicolasTailKernel t := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg hGapNonneg hKernelNonneg)]
    _ <= (2 * Real.sqrt t * Real.log t) * nicolasTailKernel t :=
      mul_le_mul_of_nonneg_right hGap hKernelNonneg
    _ = (2 * Real.sqrt t / t ^ 2) *
        (1 + 1 / Real.log t) := by
      unfold nicolasTailKernel
      field_simp [htPos.ne', hLog.ne']
    _ <= (2 * Real.sqrt t / t ^ 2) * 2 := by
      apply mul_le_mul_of_nonneg_left
      . linarith
      . positivity
    _ = 4 * t ^ (-(3 / 2 : Real)) := by
      rw [show 2 * Real.sqrt t / t ^ 2 =
        2 * (Real.sqrt t / t ^ 2) by ring, hPower]
      ring

/-- The complete prime-power tail separating `J` from `K` is integrable. -/
theorem nicolasPrimePowerIntegrand_integrableOn_Ioi_three :
    IntegrableOn
      (fun t => (Chebyshev.psi t - Chebyshev.theta t) *
        nicolasTailKernel t) (Ioi 3) := by
  apply Integrable.mono'
    (g := fun t : Real => 4 * t ^ (-(3 / 2 : Real)))
  . exact (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul 4
  . have hKernelMeas : Measurable nicolasTailKernel := by
      unfold nicolasTailKernel
      measurability
    exact ((Chebyshev.psi_mono.measurable.sub
      Chebyshev.theta_mono.measurable).mul hKernelMeas).aestronglyMeasurable
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact nicolasPrimePowerIntegrand_norm_le ht

/-- The psi-error integrand defining `J` is integrable on the complete tail
starting at three. -/
theorem nicolasPsiTail_integrableOn_Ioi_three :
    IntegrableOn
      (fun t => nicolasPsiError t * nicolasTailKernel t) (Ioi 3) := by
  have hTheta := nicolasThetaTail_integrableOn_Ioi_two.mono_set
    (Ioi_subset_Ioi (by norm_num : (2 : Real) <= 3))
  have hSum := hTheta.add nicolasPrimePowerIntegrand_integrableOn_Ioi_three
  apply hSum.congr_fun
  . intro t ht
    change nicolasThetaError t * nicolasTailKernel t +
        (Chebyshev.psi t - Chebyshev.theta t) * nicolasTailKernel t =
      nicolasPsiError t * nicolasTailKernel t
    unfold nicolasPsiError nicolasThetaError
    ring
  . exact measurableSet_Ioi

/-- Both complete Nicolas tails are integrable at every sufficiently large
frontier. -/
theorem nicolasTails_integrableEventually :
    Filter.Eventually (fun x : Real =>
      And
        (IntegrableOn
          (fun t => nicolasThetaError t * nicolasTailKernel t) (Ioi x))
        (IntegrableOn
          (fun t => nicolasPsiError t * nicolasTailKernel t) (Ioi x))) atTop := by
  filter_upwards [eventually_ge_atTop (3 : Real)] with x hx
  exact And.intro
    (nicolasThetaTail_integrableOn_Ioi_two.mono_set
      (Ioi_subset_Ioi (le_trans (by norm_num) hx)))
    (nicolasPsiTail_integrableOn_Ioi_three.mono_set (Ioi_subset_Ioi hx))

/-- Whenever the two source tails are integrable, their exact difference is
the complete nonnegative prime-power tail. -/
theorem nicolasJ_eq_K_add_primePowerTail
    {x : Real}
    (hK : IntegrableOn
      (fun t => nicolasThetaError t * nicolasTailKernel t) (Ioi x))
    (hJ : IntegrableOn
      (fun t => nicolasPsiError t * nicolasTailKernel t) (Ioi x)) :
    nicolasJ x = nicolasK x + nicolasPrimePowerTail x := by
  have hGap : IntegrableOn
      (fun t => (Chebyshev.psi t - Chebyshev.theta t) *
        nicolasTailKernel t) (Ioi x) := by
    have hSub := hJ.sub hK
    apply hSub.congr_fun
    . intro t ht
      change nicolasPsiError t * nicolasTailKernel t -
        nicolasThetaError t * nicolasTailKernel t =
          (Chebyshev.psi t - Chebyshev.theta t) * nicolasTailKernel t
      rw [<- sub_mul, nicolasPsiError_sub_thetaError]
    . exact measurableSet_Ioi
  unfold nicolasJ nicolasK nicolasPrimePowerTail
  rw [<- integral_add hK hGap]
  apply integral_congr_ae
  filter_upwards with t
  unfold nicolasPsiError nicolasThetaError
  ring

theorem nicolasK_le_J
    {x : Real} (hx : 1 <= x)
    (hK : IntegrableOn
      (fun t => nicolasThetaError t * nicolasTailKernel t) (Ioi x))
    (hJ : IntegrableOn
      (fun t => nicolasPsiError t * nicolasTailKernel t) (Ioi x)) :
    nicolasK x <= nicolasJ x := by
  rw [nicolasJ_eq_K_add_primePowerTail hK hJ]
  exact le_add_of_nonneg_right (nicolasPrimePowerTail_nonneg hx)

/-- The finite Nicolas logarithm is bounded by the complete psi-error tail
whenever both improper tails are integrable. -/
theorem nicolasLogMertensOscillation_le_J_add_four_div
    {x : Real} (hx : 3 <= x)
    (hK : IntegrableOn
      (fun t => nicolasThetaError t * nicolasTailKernel t) (Ioi x))
    (hJ : IntegrableOn
      (fun t => nicolasPsiError t * nicolasTailKernel t) (Ioi x)) :
    nicolasLogMertensOscillation x <= nicolasJ x + 4 / x := by
  exact (nicolasLogMertensOscillation_le_K_add_four_div hx).trans
    (add_le_add (nicolasK_le_J (le_trans (by norm_num) hx) hK hJ)
      (le_refl (4 / x)))

/-- Negative Omega excursions pass from an eventual upper bound to the
bounded function. -/
theorem AtTopOmegaMinus.of_eventuallyLE
    {f g h : Real -> Real}
    (hg : AtTopOmegaMinus g h)
    (hfg : Filter.Eventually (fun x => f x <= g x) atTop) :
    AtTopOmegaMinus f h := by
  unfold AtTopOmegaMinus at hg
  unfold AtTopOmegaMinus
  choose c hc hLarge using hg
  refine Exists.intro c (And.intro hc ?_)
  intro X
  choose Y hY using eventually_atTop.mp hfg
  choose x hx hMain using hLarge (max X Y)
  refine Exists.intro x (And.intro (le_trans (le_max_left X Y) hx) ?_)
  have hxY : Y <= x := le_trans (le_max_right X Y) hx
  exact hMain.trans (neg_le_neg (hY x hxY))

/-- The reciprocal scale is little-o of `x^(-b)` whenever `b < 1`. -/
theorem rpow_neg_one_isLittleO_rpow_neg
    {b : Real} (hb : b < 1) :
    IsLittleO atTop
      (fun x : Real => x ^ (-(1 : Real)))
      (fun x : Real => x ^ (-b)) := by
  apply IsLittleO.of_bound
  intro c hc
  have hDecay : Tendsto
      (fun x : Real => x ^ (-(1 - b))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hSmall : Filter.Eventually
      (fun x : Real => x ^ (-(1 - b)) < c) atTop :=
    hDecay.eventually_lt_const hc
  filter_upwards [hSmall, eventually_gt_atTop (0 : Real)] with x hxSmall hxPos
  have hRecipPos : 0 < x ^ (-(1 : Real)) :=
    Real.rpow_pos_of_pos hxPos _
  have hMainPos : 0 < x ^ (-b) := Real.rpow_pos_of_pos hxPos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hRecipPos,
    abs_of_pos hMainPos]
  have hFactor :
      x ^ (-(1 : Real)) = x ^ (-b) * x ^ (-(1 - b)) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  rw [hFactor]
  calc
    x ^ (-b) * x ^ (-(1 - b)) <= x ^ (-b) * c :=
      mul_le_mul_of_nonneg_left hxSmall.le hMainPos.le
    _ = c * x ^ (-b) := by ring

/-- The explicit Mertens summand error `4 / x` is negligible on every
Nicolas source scale `x^(-b)` with `b < 1`. -/
theorem four_div_isLittleO_rpow_neg
    {b : Real} (hb : b < 1) :
    IsLittleO atTop
      (fun x : Real => 4 / x)
      (fun x : Real => x ^ (-b)) := by
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
    (rpow_neg_one_isLittleO_rpow_neg hb).const_mul_left 4


/-- This is the exact final sign transfer needed from Nicolas's analytic
argument: a negative excursion of `J` survives a little-o upper error and
forces a negative excursion of the finite Nicolas logarithm. -/
theorem nicolasLogMertensOscillation_omegaMinus_of_J
    {b : Real} {e : Real -> Real}
    (hJ : AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)))
    (he : IsLittleO atTop e (fun x : Real => x ^ (-b)))
    (hUpper : Filter.Eventually (fun x =>
      nicolasLogMertensOscillation x <= nicolasJ x + e x) atTop) :
    AtTopOmegaMinus nicolasLogMertensOscillation
      (fun x : Real => x ^ (-b)) := by
  have hScalePos : Filter.Eventually
      (fun x : Real => 0 < x ^ (-b)) atTop := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    exact Real.rpow_pos_of_pos hx _
  exact (hJ.add_isLittleO hScalePos he).of_eventuallyLE hUpper

/-- Once tail integrability is available eventually, the proved finite
Mertens estimate transfers every negative `J` excursion to Nicolas's finite
Euler product without an additional source inequality. -/
theorem nicolasLogMertensOscillation_omegaMinus_of_J_integrable
    {b : Real} (hb : b < 1)
    (hJ : AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)))
    (hIntegrable : Filter.Eventually (fun x : Real =>
      And
        (IntegrableOn
          (fun t => nicolasThetaError t * nicolasTailKernel t) (Ioi x))
        (IntegrableOn
          (fun t => nicolasPsiError t * nicolasTailKernel t) (Ioi x))) atTop) :
    AtTopOmegaMinus nicolasLogMertensOscillation
      (fun x : Real => x ^ (-b)) := by
  apply nicolasLogMertensOscillation_omegaMinus_of_J hJ
    (four_div_isLittleO_rpow_neg hb)
  filter_upwards [hIntegrable, eventually_ge_atTop (3 : Real)] with x hInt hx
  exact nicolasLogMertensOscillation_le_J_add_four_div hx hInt.1 hInt.2

/-- The complete finite-product side of Nicolas's negative oscillation
argument: a negative Omega excursion of `J` alone now suffices. -/
theorem nicolasLogMertensOscillation_omegaMinus_of_J_proved_upper
    {b : Real} (hb : b < 1)
    (hJ : AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b))) :
    AtTopOmegaMinus nicolasLogMertensOscillation
      (fun x : Real => x ^ (-b)) := by
  exact nicolasLogMertensOscillation_omegaMinus_of_J_integrable hb hJ
    nicolasTails_integrableEventually


end

end Robin1984
