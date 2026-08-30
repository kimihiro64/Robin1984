import Robin1984.Equivalence.OmegaScaleTransfer
import Robin1984.NicolasLandau.NicolasOscillation
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# The Landau source for Nicolas's negative oscillation

This module develops the Mellin and complex-analytic continuation used in the
Landau argument for Nicolas's negative oscillation.
-/

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

theorem riemannZeta_one_sub_eq_zero_of_nontrivial_zero
    {s : Complex} (hz : riemannZeta s = 0)
    (hNontrivial : Not (Exists fun n : Nat => s = -2 * (n + 1)))
    (hOne : Not (s = 1)) :
    riemannZeta (1 - s) = 0 := by
  have hsZero : Not (s = 0) := by
    intro hs
    subst s
    norm_num [riemannZeta_zero] at hz
  have hCompleted : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hsZero] at hz
    rcases div_eq_zero_iff.mp hz with hCompleted | hGammaFactor
    . exact hCompleted
    . change
        (Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2) = 0 at hGammaFactor
      rcases mul_eq_zero.mp hGammaFactor with hPiPower | hGamma
      . have hPi : Not ((Real.pi : Complex) = 0) :=
          Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hPi) hPiPower).elim
      . choose m hm using (Complex.Gamma_eq_zero_iff (s / 2)).mp hGamma
        have hsEq : s = -2 * (m : Complex) := by
          calc
            s = 2 * (s / 2) := by ring
            _ = 2 * (-(m : Complex)) := by rw [hm]
            _ = -2 * (m : Complex) := by ring
        cases m with
        | zero => exact (hsZero (by simpa using hsEq)).elim
        | succ n =>
            exact (hNontrivial (Exists.intro n (by
              simpa [Nat.cast_add, Nat.cast_one] using hsEq))).elim
  have hMirrorCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hCompleted
  have hMirrorNeZero : Not (1 - s = 0) :=
    sub_ne_zero.mpr (Ne.symm hOne)
  rw [riemannZeta_def_of_ne_zero hMirrorNeZero, hMirrorCompleted, zero_div]

/-- Failure of RH supplies a zeta zero strictly to the right of the critical
line and strictly inside the critical strip. -/
theorem exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis
    (hNotRH : Not RiemannHypothesis) :
    Exists fun rho : Complex =>
      And (riemannZeta rho = 0)
        (And ((1 / 2 : Real) < rho.re) (rho.re < 1)) := by
  unfold RiemannHypothesis at hNotRH
  push_neg at hNotRH
  choose z hz hNontrivial hzOne hzOff using hNotRH
  have hNontrivialExists :
      Not (Exists fun n : Nat => z = -2 * (n + 1)) := by
    intro hExists
    choose n hn using hExists
    exact hNontrivial n hn
  have hzLt : z.re < 1 := by
    by_contra hNotLt
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hNotLt) hz
  have hMirrorZero : riemannZeta (1 - z) = 0 :=
    riemannZeta_one_sub_eq_zero_of_nontrivial_zero hz hNontrivialExists hzOne
  have hzPos : 0 < z.re := by
    by_contra hNotPos
    have hMirrorRe : 1 <= (1 - z).re := by
      change 1 <= 1 - z.re
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hMirrorRe hMirrorZero
  by_cases hRight : (1 / 2 : Real) < z.re
  . exact Exists.intro z (And.intro hz (And.intro hRight hzLt))
  . have hzLeft : z.re < (1 / 2 : Real) :=
      lt_of_le_of_ne (le_of_not_gt hRight) hzOff
    refine Exists.intro (1 - z) (And.intro hMirrorZero (And.intro ?_ ?_))
    . change (1 / 2 : Real) < 1 - z.re
      linarith
    . change 1 - z.re < (1 : Real)
      linarith


/-- The complete von Mangoldt partial sums have the exact linear growth
needed for Abel's integral representation of their Dirichlet series. -/
theorem nicolasVonMangoldtPartialSums_isBigO :
    (fun n : Nat =>
      Finset.sum (Finset.Icc 1 n)
        (fun k => ArithmeticFunction.vonMangoldt k)) =O[atTop]
      (fun n : Nat => (n : Real) ^ (1 : Real)) := by
  apply (IsBigOWith.of_bound
    (c := Real.log 4 + 4) (Eventually.of_forall fun n => ?_)).isBigO
  have hSum :
      Finset.sum (Finset.Icc 1 n)
          (fun k => ArithmeticFunction.vonMangoldt k) =
        Chebyshev.psi (n : Real) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    rw [Nat.floor_natCast]
    symm
    rw [<- Finset.insert_Icc_add_one_left_eq_Icc n.zero_le,
      Finset.sum_insert (by aesop)]
    simp
  rw [hSum, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.psi_nonneg (n : Real)), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) 1), Real.rpow_one]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

/-- Abel's exact Mellin representation of the logarithmic derivative of
zeta, with the complete Chebyshev psi partial sum retained. -/
theorem nicolasLogDeriv_eq_psiMellin
    {s : Complex} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (Chebyshev.psi t : Complex) *
          (t : Complex) ^ (-(s + 1))) := by
  have hAbel := LSeries_eq_mul_integral_of_nonneg
    (fun n : Nat => ArithmeticFunction.vonMangoldt n)
    (r := (1 : Real)) (by norm_num) hs
    nicolasVonMangoldtPartialSums_isBigO
    (fun n => ArithmeticFunction.vonMangoldt_nonneg)
  calc
    -deriv riemannZeta s / riemannZeta s =
        LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex)) s := by
      symm
      exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
    _ = s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (Finset.sum (Finset.Icc 1 (Nat.floor t))
          (fun k => (ArithmeticFunction.vonMangoldt k : Complex))) *
          (t : Complex) ^ (-(s + 1))) := hAbel
    _ = s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (Chebyshev.psi t : Complex) *
          (t : Complex) ^ (-(s + 1))) := by
      have hIntegral :
          integral (volume.restrict (Ioi (1 : Real)))
              (fun t => (Finset.sum (Finset.Icc 1 (Nat.floor t))
                (fun k => (ArithmeticFunction.vonMangoldt k : Complex))) *
                (t : Complex) ^ (-(s + 1))) =
            integral (volume.restrict (Ioi (1 : Real)))
              (fun t => (Chebyshev.psi t : Complex) *
                (t : Complex) ^ (-(s + 1))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change
          (Finset.sum (Finset.Icc 1 (Nat.floor t))
              (fun k => (ArithmeticFunction.vonMangoldt k : Complex))) *
              (t : Complex) ^ (-(s + 1)) =
            (Chebyshev.psi t : Complex) *
              (t : Complex) ^ (-(s + 1))
        congr 1
        rw [Chebyshev.psi_eq_sum_Icc]
        push_cast
        symm
        rw [<- Finset.insert_Icc_add_one_left_eq_Icc
            (Nat.zero_le (Nat.floor t)),
          Finset.sum_insert (by aesop)]
        simp
      rw [hIntegral]

theorem nicolasPsiMellin_integrable
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (Chebyshev.psi t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  let c : Real := Real.log 4 + 4
  have hcPos : 0 < c := by
    dsimp [c]
    positivity
  have hPower : IntegrableOn
      (fun t : Real => (c : Complex) * (t : Complex) ^ (-s)) (Ioi 1) := by
    exact (integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith) (by norm_num)).const_mul (c : Complex)
  apply Integrable.mono
    (g := fun t : Real => (c : Complex) * (t : Complex) ^ (-s)) hPower
  . have hCpow : ContinuousOn
        (fun t : Real => (t : Complex) ^ (-(s + 1))) (Ioi 1) :=
      continuousOn_of_forall_continuousAt fun t ht =>
        Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
          (Or.inr (ne_of_gt (lt_trans (by norm_num) ht)))
    exact ((Complex.measurable_ofReal.comp
      Chebyshev.psi_mono.measurable).aestronglyMeasurable.mul
        (hCpow.aestronglyMeasurable measurableSet_Ioi))
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := lt_trans (by norm_num) ht
    have hPsi := Chebyshev.psi_le_const_mul_self htPos.le
    have hPowNonneg : 0 <= t ^ (-(s + 1)).re :=
      Real.rpow_nonneg htPos.le _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Chebyshev.psi_nonneg t), abs_of_pos hcPos,
      Complex.norm_cpow_eq_rpow_re_of_pos htPos]
    calc
      Chebyshev.psi t * t ^ (-(s + 1)).re <=
          (c * t) * t ^ (-(s + 1)).re :=
        mul_le_mul_of_nonneg_right hPsi hPowNonneg
      _ = c * t ^ (-s).re := by
        calc
          (c * t) * t ^ (-(s + 1)).re =
              c * (t ^ (1 : Real) * t ^ (-(s + 1)).re) := by
            rw [Real.rpow_one]
            ring
          _ = c * t ^ ((1 : Real) + (-(s + 1)).re) := by
            rw [Real.rpow_add htPos]
          _ = c * t ^ (-s).re := by
            congr 2
            simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
            ring

theorem nicolasLinearMellin_integrable
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  have hPower : IntegrableOn
      (fun t : Real => (t : Complex) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith) (by norm_num)
  apply hPower.congr_fun
  . intro t ht
    have htZero : Not ((t : Complex) = 0) := by
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_trans (by norm_num) ht))
    change (t : Complex) ^ (-s) =
      (t : Complex) * (t : Complex) ^ (-(s + 1))
    symm
    calc
      (t : Complex) * (t : Complex) ^ (-(s + 1)) =
          (t : Complex) ^ (1 : Complex) *
            (t : Complex) ^ (-(s + 1)) := by
        rw [Complex.cpow_one]
      _ = (t : Complex) ^ ((1 : Complex) + -(s + 1)) := by
        rw [Complex.cpow_add _ _ htZero]
      _ = (t : Complex) ^ (-s) := by
        congr 1
        ring
  . exact measurableSet_Ioi

/-- The exact Mellin transform of Nicolas's psi error on its initial
half-plane of convergence.  This is the expression whose continuation
inherits the nonreal singularities of the logarithmic derivative of zeta. -/
theorem nicolasPsiErrorMellin_eq_logDeriv
    {s : Complex} (hs : 1 < s.re) :
    integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) =
      (-deriv riemannZeta s / riemannZeta s) / s -
        1 / (s - 1) := by
  have hsZero : Not (s = 0) := by
    intro hZero
    subst s
    norm_num at hs
  have hsOne : Not (s = 1) := by
    intro hOne
    subst s
    norm_num at hs
  have hLinear :
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t => (t : Complex) * (t : Complex) ^ (-(s + 1))) =
        1 / (s - 1) := by
    calc
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t => (t : Complex) * (t : Complex) ^ (-(s + 1))) =
          integral (volume.restrict (Ioi (1 : Real)))
            (fun t => (t : Complex) ^ (-s)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have htZero : Not ((t : Complex) = 0) := by
          exact Complex.ofReal_ne_zero.mpr
            (ne_of_gt (lt_trans (by norm_num) ht))
        change (t : Complex) * (t : Complex) ^ (-(s + 1)) =
          (t : Complex) ^ (-s)
        calc
          (t : Complex) * (t : Complex) ^ (-(s + 1)) =
              (t : Complex) ^ (1 : Complex) *
                (t : Complex) ^ (-(s + 1)) := by
            rw [Complex.cpow_one]
          _ = (t : Complex) ^ ((1 : Complex) + -(s + 1)) := by
            rw [Complex.cpow_add _ _ htZero]
          _ = (t : Complex) ^ (-s) := by
            congr 1
            ring
      _ = 1 / (s - 1) := by
        rw [integral_Ioi_cpow_of_lt
          (by simp only [Complex.neg_re]; linarith) (by norm_num)]
        rw [Complex.ofReal_one, Complex.one_cpow]
        rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  rw [show (fun t : Real => (nicolasPsiError t : Complex) *
      (t : Complex) ^ (-(s + 1))) =
      (fun t : Real =>
        (Chebyshev.psi t : Complex) * (t : Complex) ^ (-(s + 1)) -
        (t : Complex) * (t : Complex) ^ (-(s + 1))) by
      funext t
      unfold nicolasPsiError
      push_cast
      ring]
  rw [integral_sub (nicolasPsiMellin_integrable hs)
    (nicolasLinearMellin_integrable hs), hLinear]
  have hLog := nicolasLogDeriv_eq_psiMellin hs
  congr 1
  symm
  apply (div_eq_iff hsZero).2
  rw [hLog]
  ring

theorem nicolasPsiErrorMellin_integrable
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  have hSub := (nicolasPsiMellin_integrable hs).sub
    (nicolasLinearMellin_integrable hs)
  apply hSub.congr_fun
  . intro t ht
    change
      (Chebyshev.psi t : Complex) * (t : Complex) ^ (-(s + 1)) -
          (t : Complex) * (t : Complex) ^ (-(s + 1)) =
        (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1))
    unfold nicolasPsiError
    push_cast
    ring
  . exact measurableSet_Ioi

/-- The meromorphic expression agreeing with the complete psi-error Mellin
transform on `re s > 1`. -/
def nicolasPsiMellinContinuation (s : Complex) : Complex :=
  (-deriv riemannZeta s / riemannZeta s) / s - 1 / (s - 1)

/-- The finite startup interval removed when the psi-error Mellin tail begins
from `x` instead of from one. -/
def nicolasPsiMellinStartup (x : Real) (s : Complex) : Complex :=
  integral (volume.restrict (Ioc (1 : Real) x))
    (fun t : Real => (nicolasPsiError t : Complex) *
      (t : Complex) ^ (-(s + 1)))

/-- Analytic continuation candidate for the psi-error Mellin tail beginning
from `x`: complete meromorphic transform minus its finite startup interval. -/
def nicolasPsiMellinTailContinuation (x : Real) (s : Complex) : Complex :=
  nicolasPsiMellinContinuation s - nicolasPsiMellinStartup x s

theorem nicolasPsiErrorTailMellin_eq_continuation
    {x : Real} (hx : 1 <= x) {s : Complex} (hs : 1 < s.re) :
    integral (volume.restrict (Ioi x))
        (fun t : Real => (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) =
      nicolasPsiMellinTailContinuation x s := by
  have hFull := nicolasPsiErrorMellin_integrable hs
  have hStartup : IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioc 1 x) :=
    hFull.mono_set Ioc_subset_Ioi_self
  have hTail : IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi x) :=
    hFull.mono_set (Ioi_subset_Ioi hx)
  have hSplit :
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t : Real => (nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1))) =
        integral (volume.restrict (Ioc (1 : Real) x))
            (fun t : Real => (nicolasPsiError t : Complex) *
              (t : Complex) ^ (-(s + 1))) +
          integral (volume.restrict (Ioi x))
            (fun t : Real => (nicolasPsiError t : Complex) *
              (t : Complex) ^ (-(s + 1))) := by
    rw [<- Ioc_union_Ioi_eq_Ioi hx,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
    . exact hStartup
    . exact hTail
  unfold nicolasPsiMellinTailContinuation nicolasPsiMellinContinuation
    nicolasPsiMellinStartup
  rw [<- nicolasPsiErrorMellin_eq_logDeriv hs]
  rw [hSplit]
  ring

theorem integrableOn_mul_exp_neg_mul_Ioi_zero
    {r : Real} (hr : 0 < r) :
    IntegrableOn (fun u : Real => u * Real.exp (-(r * u))) (Ioi 0) := by
  have hGamma : IntegrableOn
      (fun u : Real => Real.exp (-u) * u ^ ((2 : Real) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num)
  have hScaled : IntegrableOn
      (fun u : Real =>
        Real.exp (-(r * u)) * (r * u) ^ ((2 : Real) - 1)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun u : Real => Real.exp (-u) * u ^ ((2 : Real) - 1)) 0 hr).2
    simpa using hGamma
  have hDiv := hScaled.const_mul (1 / r)
  change Integrable (fun u : Real => u * Real.exp (-(r * u)))
    (volume.restrict (Ioi 0))
  apply hDiv.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  calc
    (1 / r) *
        (Real.exp (-(r * u)) * (r * u) ^ ((2 : Real) - 1)) =
        (1 / r) * (Real.exp (-(r * u)) * (r * u)) := by
      rw [show (2 : Real) - 1 = 1 by norm_num, Real.rpow_one]
    _ = u * Real.exp (-(r * u)) := by
      field_simp [hr.ne']

theorem integral_exp_neg_mul_Ioi_zero
    {r : Real} (hr : 0 < r) :
    integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => Real.exp (-(r * u))) =
      1 / r := by
  have hValue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 : Real)) (r := r) (by norm_num) hr
  simpa using hValue

theorem integral_mul_exp_neg_mul_Ioi_zero
    {r : Real} (hr : 0 < r) :
    integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => u * Real.exp (-(r * u))) =
      1 / r ^ 2 := by
  have hValue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : Real)) (r := r) (by norm_num) hr
  convert hValue using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change u * Real.exp (-(r * u)) =
    u ^ ((2 : Real) - 1) * Real.exp (-(r * u))
  rw [show (2 : Real) - 1 = 1 by norm_num, Real.rpow_one]
  norm_num [Real.Gamma_ofNat_eq_factorial, div_pow]

/-- Nicolas's kernel is a positive Frullani/Gamma mixture of pure powers.
This exact identity exposes the zeta logarithmic derivative inside `J`. -/
theorem nicolasTailKernel_eq_frullani
    {t : Real} (ht : 1 < t) :
    nicolasTailKernel t =
      integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => (u + 1) * t ^ (-(u + 2))) := by
  have htPos : 0 < t := lt_trans (by norm_num) ht
  have hLog : 0 < Real.log t := Real.log_pos ht
  have hPoint : forall u : Real,
      (u + 1) * t ^ (-(u + 2)) =
        t ^ (-(2 : Real)) *
          (u * Real.exp (-(Real.log t * u)) +
            Real.exp (-(Real.log t * u))) := by
    intro u
    have hPower : t ^ (-(u + 2)) =
        t ^ (-(2 : Real)) * Real.exp (-(Real.log t * u)) := by
      rw [Real.rpow_def_of_pos htPos, Real.rpow_def_of_pos htPos]
      rw [<- Real.exp_add]
      congr 1
      ring
    rw [hPower]
    ring
  have hExpInt : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log t * u))) (Ioi 0) := by
    have hBase := integrableOn_exp_mul_Ioi
      (a := -Real.log t) (by linarith) 0
    apply hBase.congr_fun
    . intro u hu
      congr 1
      ring
    . exact measurableSet_Ioi
  have hMulInt := integrableOn_mul_exp_neg_mul_Ioi_zero hLog
  calc
    nicolasTailKernel t =
        t ^ (-(2 : Real)) *
          (1 / (Real.log t) ^ 2 + 1 / Real.log t) := by
      unfold nicolasTailKernel
      rw [Real.rpow_neg htPos.le, Real.rpow_two]
      field_simp [htPos.ne', hLog.ne']
      ring
    _ = t ^ (-(2 : Real)) *
        (integral (volume.restrict (Ioi (0 : Real)))
            (fun u : Real => u * Real.exp (-(Real.log t * u))) +
          integral (volume.restrict (Ioi (0 : Real)))
            (fun u : Real => Real.exp (-(Real.log t * u)))) := by
      rw [integral_mul_exp_neg_mul_Ioi_zero hLog,
        integral_exp_neg_mul_Ioi_zero hLog]
    _ = integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => (u + 1) * t ^ (-(u + 2))) := by
      rw [<- integral_add hMulInt hExpInt, <- integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      symm
      exact hPoint u

theorem nicolasFrullaniKernel_integrable
    {t : Real} (ht : 1 < t) :
    IntegrableOn (fun u : Real => (u + 1) * t ^ (-(u + 2))) (Ioi 0) := by
  have htPos : 0 < t := lt_trans (by norm_num) ht
  have hLog : 0 < Real.log t := Real.log_pos ht
  have hExpInt : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log t * u))) (Ioi 0) := by
    have hBase := integrableOn_exp_mul_Ioi
      (a := -Real.log t) (by linarith) 0
    apply hBase.congr_fun
    . intro u hu
      congr 1
      ring
    . exact measurableSet_Ioi
  have hMulInt := integrableOn_mul_exp_neg_mul_Ioi_zero hLog
  have hSumInt := hMulInt.add hExpInt
  have hScaled := hSumInt.const_mul (t ^ (-(2 : Real)))
  change Integrable (fun u : Real => (u + 1) * t ^ (-(u + 2)))
    (volume.restrict (Ioi 0))
  apply hScaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hPower : t ^ (-(u + 2)) =
      t ^ (-(2 : Real)) * Real.exp (-(Real.log t * u)) := by
    rw [Real.rpow_def_of_pos htPos, Real.rpow_def_of_pos htPos]
    rw [<- Real.exp_add]
    congr 1
    ring
  calc
    t ^ (-(2 : Real)) *
        (u * Real.exp (-(Real.log t * u)) +
          Real.exp (-(Real.log t * u))) =
        (u + 1) * t ^ (-(u + 2)) := by
      rw [hPower]
      ring

/-- The complete Nicolas `J` tail as a two-variable Frullani integral.  No
Schedule, endpoint, or tail is discarded; this is the exact surface on which
Fubini connects `J` to the zeta logarithmic derivative. -/
theorem nicolasJ_eq_frullaniDouble
    {x : Real} (hx : 1 <= x) :
    nicolasJ x =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
          nicolasPsiError t * (u + 1) * t ^ (-(u + 2)))) := by
  unfold nicolasJ
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have htOne : 1 < t := lt_of_le_of_lt hx ht
  change nicolasPsiError t * nicolasTailKernel t =
    integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
      nicolasPsiError t * (u + 1) * t ^ (-(u + 2)))
  rw [nicolasTailKernel_eq_frullani htOne]
  rw [<- integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  ring

/-- Absolute integrability of the complete two-variable Frullani carrier.
This is the Tonelli/Fubini gate needed to turn the exact `J` representation
into the zeta-logarithmic-derivative integral. -/
theorem nicolasFrullaniDouble_integrable
    {x : Real} (hx : 3 <= x) :
    Integrable
      (fun p : Prod Real Real =>
        nicolasPsiError p.1 * (p.2 + 1) * p.1 ^ (-(p.2 + 2)))
      ((volume.restrict (Ioi x)).prod
        (volume.restrict (Ioi (0 : Real)))) := by
  let f : Prod Real Real -> Real := fun p =>
    nicolasPsiError p.1 * (p.2 + 1) * p.1 ^ (-(p.2 + 2))
  have hMeas : AEStronglyMeasurable f
      ((volume.restrict (Ioi x)).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    apply AEMeasurable.aestronglyMeasurable
    have hFst : AEMeasurable (fun p : Prod Real Real => p.1)
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      measurable_fst.aemeasurable
    have hSnd : AEMeasurable (fun p : Prod Real Real => p.2)
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      measurable_snd.aemeasurable
    have hPsi : AEMeasurable
        (fun p : Prod Real Real => nicolasPsiError p.1)
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) := by
      unfold nicolasPsiError
      exact ((Chebyshev.psi_mono.measurable.comp_aemeasurable hFst).sub hFst)
    have hExponent : AEMeasurable
        (fun p : Prod Real Real => -(p.2 + 2))
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      (hSnd.add_const 2).neg
    have hPower : AEMeasurable
        (fun p : Prod Real Real => p.1 ^ (-(p.2 + 2)))
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      hFst.pow hExponent
    exact (hPsi.mul (hSnd.add_const 1)).mul hPower
  change Integrable f
    ((volume.restrict (Ioi x)).prod
      (volume.restrict (Ioi (0 : Real))))
  apply (integrable_prod_iff hMeas).2
  constructor
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t :=
      lt_trans (by norm_num) (lt_of_le_of_lt hx ht)
    have hKernel := nicolasFrullaniKernel_integrable htOne
    have hScaled := hKernel.const_mul (nicolasPsiError t)
    change Integrable (fun u : Real => f (t, u))
      (volume.restrict (Ioi (0 : Real)))
    apply hScaled.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    dsimp [f]
    ring
  . have hTail := nicolasPsiTail_integrableOn_Ioi_three.mono_set
      (Ioi_subset_Ioi hx)
    have hTailNorm := hTail.norm
    change Integrable
      (fun t : Real => integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => norm (f (t, u))))
      (volume.restrict (Ioi x))
    apply hTailNorm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t :=
      lt_trans (by norm_num) (lt_of_le_of_lt hx ht)
    have hKernelNonneg : 0 <= nicolasTailKernel t :=
      nicolasTailKernel_nonneg htOne.le
    change norm (nicolasPsiError t * nicolasTailKernel t) =
      integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => norm (f (t, u)))
    calc
      norm (nicolasPsiError t * nicolasTailKernel t) =
          |nicolasPsiError t| * nicolasTailKernel t := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hKernelNonneg]
      _ = |nicolasPsiError t| *
          integral (volume.restrict (Ioi (0 : Real)))
            (fun u : Real => (u + 1) * t ^ (-(u + 2))) := by
        rw [nicolasTailKernel_eq_frullani htOne]
      _ = integral (volume.restrict (Ioi (0 : Real)))
          (fun u : Real => |nicolasPsiError t| *
            ((u + 1) * t ^ (-(u + 2)))) := by
        rw [integral_const_mul]
      _ = integral (volume.restrict (Ioi (0 : Real)))
          (fun u : Real => norm (f (t, u))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        have huPos : 0 < u := hu
        have huNonneg : 0 <= u + 1 := by linarith
        have htPos : 0 < t := lt_trans (by norm_num) htOne
        have hPowerNonneg : 0 <= t ^ (-(u + 2)) :=
          Real.rpow_nonneg htPos.le _
        dsimp [f]
        rw [abs_mul, abs_mul,
          abs_of_nonneg huNonneg, abs_of_nonneg hPowerNonneg]
        ring


/-- The finite Mellin cell used when the `x`-integral is exchanged with a
psi-error tail.  Positivity of the lower endpoint removes the branch issue
for complex powers. -/
theorem integral_Ioc_cpow_sub_one
    {a b : Real} {z : Complex} (ha : 0 < a) (hab : a <= b)
    (hz : Not (z = 0)) :
    integral (volume.restrict (Ioc a b)) (fun x : Real =>
        (x : Complex) ^ (z - 1)) =
      ((b : Complex) ^ z - (a : Complex) ^ z) / z := by
  rw [<- intervalIntegral.integral_of_le hab]
  have hExponent : Not (z - 1 = -1) := by
    intro h
    apply hz
    calc
      z = (z - 1) + 1 := by ring
      _ = -1 + 1 := by rw [h]
      _ = 0 := by ring
  have hZeroOutside : Not (And (a <= 0) (0 <= b)) := by
    intro h
    linarith
  rw [integral_cpow (Or.inr (And.intro hExponent (by
    simpa only [uIcc_of_le hab, mem_Icc] using hZeroOutside)))]
  congr 3 <;> ring


theorem nicolasPsiErrorMellinCell_eq_shift
    {a : Real} {s z : Complex} (ha : 1 <= a) (hs : 1 < s.re)
    (hzRe : z.re < 0) :
    integral (volume.restrict (Ioi a)) (fun t : Real =>
        ((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) *
          (((t : Complex) ^ z - (a : Complex) ^ z) / z)) =
      (nicolasPsiMellinTailContinuation a (s - z) -
        (a : Complex) ^ z * nicolasPsiMellinTailContinuation a s) / z := by
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hzZero : Not (z = 0) := by
    intro hz
    subst z
    norm_num at hzRe
  have hsShift : 1 < (s - z).re := by
    simp only [Complex.sub_re]
    linarith
  let hfun : Real -> Complex := fun t =>
    (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1))
  let hShift : Real -> Complex := fun t =>
    (nicolasPsiError t : Complex) *
      (t : Complex) ^ (-((s - z) + 1))
  have hH : Integrable hfun (volume.restrict (Ioi a)) := by
    dsimp [hfun]
    exact (nicolasPsiErrorMellin_integrable hs).mono_set
      (Ioi_subset_Ioi ha)
  have hHShift : Integrable hShift (volume.restrict (Ioi a)) := by
    dsimp [hShift]
    exact (nicolasPsiErrorMellin_integrable hsShift).mono_set
      (Ioi_subset_Ioi ha)
  have hPowerShift : forall t : Real, a < t ->
      hfun t * (t : Complex) ^ z = hShift t := by
    intro t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans haPos ht))
    dsimp [hfun, hShift]
    calc
      ((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) * (t : Complex) ^ z =
          (nicolasPsiError t : Complex) *
            ((t : Complex) ^ (-(s + 1)) * (t : Complex) ^ z) := by
        ring
      _ = (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1) + z) := by
        rw [Complex.cpow_add _ _ htZero]
      _ = (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-((s - z) + 1)) := by
        congr 2
        ring
  change integral (volume.restrict (Ioi a)) (fun t : Real =>
      hfun t * (((t : Complex) ^ z - (a : Complex) ^ z) / z)) = _
  calc
    integral (volume.restrict (Ioi a)) (fun t : Real =>
        hfun t * (((t : Complex) ^ z - (a : Complex) ^ z) / z)) =
        integral (volume.restrict (Ioi a)) (fun t : Real =>
          (hShift t - (a : Complex) ^ z * hfun t) / z) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      calc
        hfun t * (((t : Complex) ^ z - (a : Complex) ^ z) / z) =
            (hfun t * (t : Complex) ^ z -
              (a : Complex) ^ z * hfun t) / z := by
          ring
        _ = (hShift t - (a : Complex) ^ z * hfun t) / z := by
          rw [hPowerShift t ht]
    _ = (integral (volume.restrict (Ioi a)) hShift -
        (a : Complex) ^ z * integral (volume.restrict (Ioi a)) hfun) / z := by
      rw [integral_div]
      rw [integral_sub hHShift (hH.const_mul ((a : Complex) ^ z))]
      rw [integral_const_mul]
    _ = (nicolasPsiMellinTailContinuation a (s - z) -
        (a : Complex) ^ z * nicolasPsiMellinTailContinuation a s) / z := by
      dsimp [hShift, hfun]
      rw [nicolasPsiErrorTailMellin_eq_continuation ha hsShift,
        nicolasPsiErrorTailMellin_eq_continuation ha hs]

/-- Mellin transform of Nicolas's complete `J` tail from the fixed startup
frontier three. -/
def nicolasJMellin (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
    (x : Complex) ^ (z - 1) * (nicolasJ x : Complex))

/-- Absolute integrability of the complete three-variable carrier
`3 < x < t`, `u > 0`.  This is the Fubini license for lifting the shifted-tail
identity through the Frullani mixture defining `J`. -/
theorem nicolasJMellinTriple_integrable
    {z : Complex} (hzRe : z.re < 0) :
    Integrable
      ({p : Prod Real (Prod Real Real) | p.1 < p.2.1}.indicator
        (fun p : Prod Real (Prod Real Real) =>
          (p.1 : Complex) ^ (z - 1) *
            ((nicolasPsiError p.2.1 * (p.2.2 + 1) *
              p.2.1 ^ (-(p.2.2 + 2)) : Real) : Complex)))
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))) := by
  have hG : Integrable
      (fun x : Real => (x : Complex) ^ (z - 1))
      (volume.restrict (Ioi (3 : Real))) := by
    exact integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.sub_re, Complex.one_re]; linarith) (by norm_num)
  have hBaseReal : Integrable
      (fun p : Prod Real Real =>
        nicolasPsiError p.1 * (p.2 + 1) * p.1 ^ (-(p.2 + 2)))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) :=
    nicolasFrullaniDouble_integrable (by norm_num)
  have hBaseComplex : Integrable
      (fun p : Prod Real Real =>
        ((nicolasPsiError p.1 * (p.2 + 1) *
          p.1 ^ (-(p.2 + 2)) : Real) : Complex))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    exact Complex.ofRealCLM.integrable_comp hBaseReal
  have hProduct := hG.mul_prod hBaseComplex
  have hDomain : MeasurableSet
      {p : Prod Real (Prod Real Real) | p.1 < p.2.1} :=
    measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd)
  exact hProduct.indicator hDomain

theorem nicolasJMellinTriple_inner_eq
    {z : Complex} {x : Real} (hx : 3 <= x) :
    integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
            (fun q : Prod Real (Prod Real Real) =>
              (q.1 : Complex) ^ (z - 1) *
                ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                  q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
            (x, p)) =
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex) := by
  let g : Complex := (x : Complex) ^ (z - 1)
  let baseReal : Prod Real Real -> Real := fun p =>
    nicolasPsiError p.1 * (p.2 + 1) * p.1 ^ (-(p.2 + 2))
  let baseComplex : Prod Real Real -> Complex := fun p =>
    (baseReal p : Complex)
  let dx : Set (Prod Real Real) := {p | x < p.1}
  have hBaseReal : Integrable baseReal
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    dsimp [baseReal]
    exact nicolasFrullaniDouble_integrable (by norm_num)
  have hBaseComplex : Integrable baseComplex
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    dsimp [baseComplex]
    exact Complex.ofRealCLM.integrable_comp hBaseReal
  have hdx : MeasurableSet dx := by
    dsimp [dx]
    exact measurableSet_lt measurable_const measurable_fst
  have hSection : Integrable (dx.indicator (fun p => g * baseComplex p))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) :=
    (hBaseComplex.const_mul g).indicator hdx
  have hCast :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u))) =
        ((integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseReal (t, u))) : Real) : Complex) := by
    calc
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u))) =
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            ((integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
              baseReal (t, u)) : Real) : Complex)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp [baseComplex]
        exact integral_ofReal
      _ = ((integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseReal (t, u))) : Real) : Complex) := by
        exact integral_ofReal
  change integral
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real))))
      (dx.indicator (fun p => g * baseComplex p)) =
    g * (nicolasJ x : Complex)
  calc
    integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (dx.indicator (fun p => g * baseComplex p)) =
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            dx.indicator (fun p => g * baseComplex p) (t, u))) := by
      exact integral_prod _ hSection
    _ = integral (volume.restrict (Ioi (3 : Real)))
        ((Ioi x).indicator (fun t : Real =>
          g * integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u)))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      by_cases hxt : x < t
      . simp [dx, Set.indicator, hxt, integral_const_mul]
      . simp [dx, Set.indicator, hxt]
    _ = integral (volume.restrict (Set.inter (Ioi (3 : Real)) (Ioi x)))
        (fun t : Real =>
          g * integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u))) := by
      rw [setIntegral_indicator measurableSet_Ioi]
      rfl
    _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
        g * integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
          baseComplex (t, u))) := by
      have hInter : Set.inter (Ioi (3 : Real)) (Ioi x) = Ioi x :=
        inter_eq_right.mpr (Ioi_subset_Ioi hx)
      rw [hInter]
    _ = g * integral (volume.restrict (Ioi x)) (fun t : Real =>
        integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
          baseComplex (t, u))) := by
      rw [integral_const_mul]
    _ = g * (nicolasJ x : Complex) := by
      rw [hCast]
      rw [nicolasJ_eq_frullaniDouble (le_trans (by norm_num) hx)]

theorem nicolasJMellinTriple_x_inner_eq
    {z : Complex} {t u : Real} (hzRe : z.re < 0) (ht : 3 < t) :
    integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
          (fun q : Prod Real (Prod Real Real) =>
            (q.1 : Complex) ^ (z - 1) *
              ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
          (x, (t, u))) =
      ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex) *
        (((t : Complex) ^ z - (3 : Complex) ^ z) / z) := by
  let c : Complex :=
    ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex)
  let g : Real -> Complex := fun x => (x : Complex) ^ (z - 1)
  let dt : Set Real := Iio t
  change integral (volume.restrict (Ioi (3 : Real)))
      (dt.indicator (fun x : Real => g x * c)) =
    c * (((t : Complex) ^ z - (3 : Complex) ^ z) / z)
  rw [setIntegral_indicator measurableSet_Iio]
  have hInter : Set.inter (Ioi (3 : Real)) (Iio t) = Ioo 3 t := by
    ext x
    simp [Set.inter]
  change integral
      (volume.restrict (Set.inter (Ioi (3 : Real)) (Iio t)))
      (fun x : Real => g x * c) = _
  rw [hInter]
  calc
    integral (volume.restrict (Ioo (3 : Real) t)) (fun x : Real =>
        g x * c) =
        integral (volume.restrict (Ioo (3 : Real) t)) (fun x : Real =>
          c * g x) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      ring
    _ = c * integral (volume.restrict (Ioo (3 : Real) t)) g := by
      rw [integral_const_mul]
    _ = c * integral (volume.restrict (Ioc (3 : Real) t)) g := by
      rw [integral_Ioc_eq_integral_Ioo]
    _ = c * (((t : Complex) ^ z - (3 : Complex) ^ z) / z) := by
      dsimp [g]
      rw [integral_Ioc_cpow_sub_one (by norm_num) ht.le (by
        intro hz
        subst z
        norm_num at hzRe)]
      norm_num

theorem nicolasJMellin_eq_tripleSwapped
    {z : Complex} (hzRe : z.re < 0) :
    nicolasJMellin z =
      integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
              (fun q : Prod Real (Prod Real Real) =>
                (q.1 : Complex) ^ (z - 1) *
                  ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                    q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
              (x, p))) := by
  have hUncurried : Integrable
      (Function.uncurry (fun x : Real => fun p : Prod Real Real =>
        {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
          (fun q : Prod Real (Prod Real Real) =>
            (q.1 : Complex) ^ (z - 1) *
              ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
          (x, p)))
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))) := by
    change Integrable
      ({p : Prod Real (Prod Real Real) | p.1 < p.2.1}.indicator
        (fun p : Prod Real (Prod Real Real) =>
          (p.1 : Complex) ^ (z - 1) *
            ((nicolasPsiError p.2.1 * (p.2.2 + 1) *
              p.2.1 ^ (-(p.2.2 + 2)) : Real) : Complex)))
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real)))))
    exact nicolasJMellinTriple_integrable hzRe
  unfold nicolasJMellin
  calc
    integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) =
        integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          integral
            ((volume.restrict (Ioi (3 : Real))).prod
              (volume.restrict (Ioi (0 : Real))))
            (fun p : Prod Real Real =>
              {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
                (fun q : Prod Real (Prod Real Real) =>
                  (q.1 : Complex) ^ (z - 1) *
                    ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                      q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
                (x, p))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (nicolasJMellinTriple_inner_eq hx.le).symm
    _ = integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
              (fun q : Prod Real (Prod Real Real) =>
                (q.1 : Complex) ^ (z - 1) *
                  ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                    q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
              (x, p))) := integral_integral_swap hUncurried

theorem nicolasJMellinTriple_t_inner_eq
    {z : Complex} {u : Real} (hzRe : z.re < 0) (hu : 0 < u) :
    integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex) *
          (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) =
      ((u + 1 : Real) : Complex) *
        ((nicolasPsiMellinTailContinuation 3
            (((u + 1 : Real) : Complex) - z) -
          (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
            ((u + 1 : Real) : Complex)) / z) := by
  let s : Complex := ((u + 1 : Real) : Complex)
  let c : Complex := ((u + 1 : Real) : Complex)
  have hs : 1 < s.re := by
    dsimp [s]
    linarith
  have hPoint : forall t : Real, 3 < t ->
      ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex) *
          (((t : Complex) ^ z - (3 : Complex) ^ z) / z) =
        c * (((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) *
            (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) := by
    intro t ht
    have htPos : 0 < t := lt_trans (by norm_num) ht
    have hPower :
        ((t ^ (-(u + 2)) : Real) : Complex) =
          (t : Complex) ^ (-(s + 1)) := by
      rw [Complex.ofReal_cpow htPos.le]
      congr 1
      dsimp [s]
      push_cast
      ring
    dsimp [c]
    push_cast
    rw [hPower]
    ring
  calc
    integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex) *
          (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) =
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          c * (((nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1))) *
              (((t : Complex) ^ z - (3 : Complex) ^ z) / z))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hPoint t ht
    _ = c * integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        ((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) *
            (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) := by
      rw [integral_const_mul]
    _ = c *
        ((nicolasPsiMellinTailContinuation 3 (s - z) -
          (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3 s) / z) := by
      congr 1
      simpa using (nicolasPsiErrorMellinCell_eq_shift
        (a := (3 : Real)) (s := s) (z := z) (by norm_num) hs hzRe)
    _ = ((u + 1 : Real) : Complex) *
        ((nicolasPsiMellinTailContinuation 3
            (((u + 1 : Real) : Complex) - z) -
          (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
            ((u + 1 : Real) : Complex)) / z) := by
      rfl

/-- Exact Mellin transform of Nicolas's `J` tail on its half-plane of
absolute convergence.  The shifted tail continuation is now explicit under
the complete Frullani parameter integral. -/
theorem nicolasJMellin_eq_integral_shift
    {z : Complex} (hzRe : z.re < 0) :
    nicolasJMellin z =
      integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        ((u + 1 : Real) : Complex) *
          ((nicolasPsiMellinTailContinuation 3
              (((u + 1 : Real) : Complex) - z) -
            (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
              ((u + 1 : Real) : Complex)) / z)) := by
  let triple : Prod Real (Prod Real Real) -> Complex := fun q =>
    {p : Prod Real (Prod Real Real) | p.1 < p.2.1}.indicator
      (fun p : Prod Real (Prod Real Real) =>
        (p.1 : Complex) ^ (z - 1) *
          ((nicolasPsiError p.2.1 * (p.2.2 + 1) *
            p.2.1 ^ (-(p.2.2 + 2)) : Real) : Complex)) q
  have hTriple : Integrable triple
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))) := by
    dsimp [triple]
    exact nicolasJMellinTriple_integrable hzRe
  have hOuter : Integrable
      (fun p : Prod Real Real =>
        integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          triple (x, p)))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) :=
    hTriple.integral_prod_right
  calc
    nicolasJMellin z = integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            triple (x, p))) := by
      rw [nicolasJMellin_eq_tripleSwapped hzRe]
    _ = integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            triple (x, (t, u))))) := by
      exact integral_prod_symm _ hOuter
    _ = integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex) *
            (((t : Complex) ^ z - (3 : Complex) ^ z) / z))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp [triple]
      exact nicolasJMellinTriple_x_inner_eq hzRe ht
    _ = integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        ((u + 1 : Real) : Complex) *
          ((nicolasPsiMellinTailContinuation 3
              (((u + 1 : Real) : Complex) - z) -
            (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
              ((u + 1 : Real) : Complex)) / z)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact nicolasJMellinTriple_t_inner_eq hzRe hu

/-- Every critical-strip zero of zeta gives a genuine simple pole of its
logarithmic derivative, without assuming that the zero itself is simple. -/
theorem nicolasRiemannZetaLogDeriv_order_eq_neg_one
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hOne : Not (rho = 1)) :
    meromorphicOrderAt (logDeriv riemannZeta) rho = -1 := by
  have hAnalyticRho : AnalyticAt Complex riemannZeta rho :=
    analyticOn_riemannZeta rho (by simpa using hOne)
  have hMeromorphicRho : MeromorphicAt riemannZeta rho :=
    hAnalyticRho.meromorphicAt
  have hTendstoZero : Tendsto riemannZeta
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    have hCont : Tendsto riemannZeta
        (nhdsWithin rho (Set.compl {rho})) (nhds (riemannZeta rho)) :=
      hAnalyticRho.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [hZero] using hCont
  have hOrderPos : 0 < meromorphicOrderAt riemannZeta rho :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hMeromorphicRho).1 hTendstoZero
  have hAnalyticTwo : AnalyticAt Complex riemannZeta 2 :=
    analyticOn_riemannZeta 2 (by norm_num)
  have hMeromorphicTwo : MeromorphicAt riemannZeta 2 :=
    hAnalyticTwo.meromorphicAt
  have hZetaTwo : Not (riemannZeta 2 = 0) :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hTendstoTwo : Tendsto riemannZeta
      (nhdsWithin (2 : Complex) (Set.compl {(2 : Complex)}))
      (nhds (riemannZeta 2)) :=
    hAnalyticTwo.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hOrderTwo : meromorphicOrderAt riemannZeta 2 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hMeromorphicTwo).1
      (Exists.intro (riemannZeta 2)
        (And.intro hZetaTwo hTendstoTwo))
  have hMeromorphicOn : MeromorphicOn riemannZeta (Set.compl {1}) :=
    analyticOn_riemannZeta.meromorphicOn
  apply meromorphicOrderAt_logDeriv_eq_neg_one hMeromorphicRho
    (ne_of_gt hOrderPos)
  apply hMeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (x := (2 : Complex))
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  . exact Set.mem_compl_singleton_iff.mpr (by norm_num)
  . exact Set.mem_compl_singleton_iff.mpr hOne
  . rw [hOrderTwo]
    simp

theorem nicolasPsiMellinContinuation_order_eq_neg_one
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRhoZero : Not (rho = 0)) (hOne : Not (rho = 1)) :
    meromorphicOrderAt nicolasPsiMellinContinuation rho = -1 := by
  let logF : Complex -> Complex := fun w => logDeriv riemannZeta w
  let negLogF : Complex -> Complex := fun w => -logF w
  let idF : Complex -> Complex := fun w => w
  let first : Complex -> Complex := fun w => negLogF w / idF w
  let regular : Complex -> Complex := fun w => -(Inv.inv (w - 1))
  have hZetaMeromorphic : MeromorphicAt riemannZeta rho :=
    (analyticOn_riemannZeta rho
      (Set.mem_compl_singleton_iff.mpr hOne)).meromorphicAt
  have hLogMeromorphic : MeromorphicAt logF rho := by
    dsimp [logF]
    exact hZetaMeromorphic.logDeriv
  have hNegLogMeromorphic : MeromorphicAt negLogF rho := by
    dsimp [negLogF]
    exact hLogMeromorphic.neg
  have hIdMeromorphic : MeromorphicAt idF rho := by
    dsimp [idF]
    fun_prop
  have hFirstMeromorphic : MeromorphicAt first rho := by
    dsimp [first]
    exact hNegLogMeromorphic.div hIdMeromorphic
  have hDen : Not (rho - 1 = 0) := sub_ne_zero.mpr hOne
  have hRegularAnalytic : AnalyticAt Complex regular rho := by
    dsimp [regular]
    have hOneAnalytic : AnalyticAt Complex
        (fun _ : Complex => (1 : Complex)) rho := analyticAt_const
    exact ((analyticAt_id.sub hOneAnalytic).inv hDen).neg
  have hRegularMeromorphic : MeromorphicAt regular rho :=
    hRegularAnalytic.meromorphicAt
  have hLogOrder : meromorphicOrderAt logF rho = -1 := by
    dsimp [logF]
    exact nicolasRiemannZetaLogDeriv_order_eq_neg_one hZero hOne
  have hNegLogOrder : meromorphicOrderAt negLogF rho = -1 := by
    dsimp [negLogF]
    rw [<- meromorphicOrderAt_fun_neg]
    exact hLogOrder
  have hIdTendsto : Tendsto idF
      (nhdsWithin rho (Set.compl {rho})) (nhds rho) := by
    dsimp [idF]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hIdOrder : meromorphicOrderAt idF rho = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hIdMeromorphic).1
      (Exists.intro rho (And.intro hRhoZero hIdTendsto))
  have hFirstOrder : meromorphicOrderAt first rho = -1 := by
    change meromorphicOrderAt (negLogF / idF) rho = -1
    rw [meromorphicOrderAt_div hNegLogMeromorphic hIdMeromorphic,
      hNegLogOrder, hIdOrder]
    norm_num
  have hRegularNonneg : 0 <= meromorphicOrderAt regular rho :=
    hRegularAnalytic.meromorphicOrderAt_nonneg
  have hOrdersNe : Not (meromorphicOrderAt first rho =
      meromorphicOrderAt regular rho) := by
    intro hEq
    rw [hFirstOrder] at hEq
    rw [<- hEq] at hRegularNonneg
    have hNegOne : ((-1 : Int) : WithTop Int) <
        ((0 : Int) : WithTop Int) := WithTop.coe_lt_coe.mpr (by norm_num)
    exact (not_lt_of_ge hRegularNonneg) hNegOne
  have hSumOrder : meromorphicOrderAt (first + regular) rho = -1 := by
    rw [meromorphicOrderAt_add_of_ne hFirstMeromorphic
      hRegularMeromorphic hOrdersNe, hFirstOrder]
    rw [min_eq_left]
    have hNegOne : ((-1 : Int) : WithTop Int) <
        ((0 : Int) : WithTop Int) := WithTop.coe_lt_coe.mpr (by norm_num)
    exact le_of_lt (lt_of_lt_of_le hNegOne hRegularNonneg)
  have hOrderCongr :
      meromorphicOrderAt nicolasPsiMellinContinuation rho =
        meromorphicOrderAt (first + regular) rho := by
    apply meromorphicOrderAt_congr
    exact Filter.Eventually.of_forall fun w => by
      unfold nicolasPsiMellinContinuation
      dsimp [first, regular, negLogF, logF, idF]
      rw [logDeriv_apply]
      ring
  exact hOrderCongr.trans hSumOrder

/-- The finite startup contribution on `(1, 3]` is continuous in the Mellin
parameter.  Consequently it cannot remove a pole of the complete Mellin
continuation. -/
theorem nicolasPsiMellinStartup_three_continuousAt (s0 : Complex) :
    ContinuousAt (nicolasPsiMellinStartup 3) s0 := by
  let base : Real -> Complex := fun t =>
    (nicolasPsiError t : Complex) * (t : Complex) ^ (-3 : Complex)
  let ratio : Complex -> Real -> Complex := fun s t =>
    (t : Complex) ^ ((2 : Complex) - s)
  let majorant : Real -> Real := fun t =>
    norm (base t) * (3 : Real) ^ (abs s0.re + 4)
  have hBaseIntegrable : Integrable base
      (volume.restrict (Ioc (1 : Real) 3)) := by
    dsimp [base]
    change IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-3 : Complex)) (Ioc (1 : Real) 3)
    have h :=
      (nicolasPsiErrorMellin_integrable (s := (2 : Complex)) (by norm_num)).mono_set
        (show Ioc (1 : Real) 3 <= Ioi 1 from Ioc_subset_Ioi_self)
    apply h.congr_fun
    . intro t ht
      congr 2
      norm_num
    . exact measurableSet_Ioc
  have hMajorantIntegrable : Integrable majorant
      (volume.restrict (Ioc (1 : Real) 3)) := by
    have h := hBaseIntegrable.norm.const_mul
      ((3 : Real) ^ (abs s0.re + 4))
    simpa [majorant, mul_comm] using h
  have hMeasurable : forall s : Complex, AEStronglyMeasurable
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1)))
      (volume.restrict (Ioc (1 : Real) 3)) := by
    intro s
    have hRatioContinuous : ContinuousOn (ratio s) (Ioc (1 : Real) 3) := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      dsimp [ratio]
      have htPos : 0 < t := lt_trans zero_lt_one ht.1
      exact (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 htPos)).comp
          Complex.continuous_ofReal.continuousAt
    have hProduct := hBaseIntegrable.aestronglyMeasurable.mul
      (hRatioContinuous.aestronglyMeasurable measurableSet_Ioc)
    apply hProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one ht.1))
    dsimp [base, ratio]
    rw [mul_assoc, <- Complex.cpow_add _ _ htZero]
    congr 2
    ring
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall t : Real, 1 < t -> t <= 3 ->
        norm ((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) <= majorant t := by
    intro s hs t htOneStrict htThree
    have hDist : norm (s - s0) < 1 := by
      simpa [dist_eq_norm] using hs
    have hReAbs : abs (s.re - s0.re) <= norm (s - s0) := by
      simpa using Complex.abs_re_le_norm (s - s0)
    have hReLower : s0.re - 1 < s.re := by
      have hAbsLt : abs (s.re - s0.re) < 1 := lt_of_le_of_lt hReAbs hDist
      linarith [(abs_lt.mp hAbsLt).1]
    have htPos : 0 < t := lt_trans zero_lt_one htOneStrict
    have htOne : 1 <= t := le_of_lt htOneStrict
    have hExponent : 2 - s.re <= abs s0.re + 4 := by
      have hNeg : -s0.re <= abs s0.re := neg_le_abs s0.re
      linarith
    have hExponentNonneg : 0 <= abs s0.re + 4 := by positivity
    have hRatioBound : norm (ratio s t) <=
        (3 : Real) ^ (abs s0.re + 4) := by
      dsimp [ratio]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htPos]
      calc
        t ^ (2 - s.re) <= t ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow_of_exponent_le htOne hExponent
        _ <= (3 : Real) ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow (le_of_lt htPos) htThree hExponentNonneg
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt htPos)
    rw [show -(s + 1) = (-3 : Complex) + ((2 : Complex) - s) by ring,
      Complex.cpow_add _ _ htZero, norm_mul]
    dsimp [majorant, base]
    simp only [norm_mul]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hRatioBound
        (mul_nonneg (norm_nonneg
          ((nicolasPsiError t : Complex)))
          (norm_nonneg ((t : Complex) ^ (-3 : Complex)))))
  unfold nicolasPsiMellinStartup
  apply continuousAt_of_dominated
      (F := fun s : Complex => fun t : Real =>
        (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1)))
      (bound := majorant)
  . exact Eventually.of_forall hMeasurable
  . filter_upwards [Metric.ball_mem_nhds s0 zero_lt_one] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hBound s (by simpa [Metric.mem_ball] using hs) t ht.1 ht.2
  . exact hMajorantIntegrable
  . filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_trans zero_lt_one ht.1))
    have hExponent : ContinuousAt (fun s : Complex => -(s + 1)) s0 := by
      fun_prop
    exact continuousAt_const.mul
      ((continuousAt_const_cpow htZero).comp hExponent)


/-- The surviving pole has a nonzero first Laurent coefficient.  This is the
exact fixed-direction information needed at the endpoint of the Landau
integral; mere growth of the norm would not be enough. -/
theorem nicolasPsiMellinTailContinuation_three_simplePoleLimit
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRhoZero : Not (rho = 0)) (hOne : Not (rho = 1)) :
    Exists fun c : Complex => And (Not (c = 0))
      (Tendsto
        (fun s : Complex => (s - rho) *
          nicolasPsiMellinTailContinuation 3 s)
        (nhdsWithin rho (Set.compl {rho})) (nhds c)) := by
  have hOrder : meromorphicOrderAt nicolasPsiMellinContinuation rho = -1 :=
    nicolasPsiMellinContinuation_order_eq_neg_one hZero hRhoZero hOne
  have hOrderNeg : meromorphicOrderAt nicolasPsiMellinContinuation rho < 0 := by
    rw [hOrder]
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  have hMeromorphic : MeromorphicAt nicolasPsiMellinContinuation rho :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero hOrderNeg.ne
  choose g hgAnalytic hgZero hgFactor using
    (meromorphicOrderAt_eq_int_iff hMeromorphic).1 hOrder
  have hFullScaled : Tendsto
      (fun s : Complex => (s - rho) * nicolasPsiMellinContinuation s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (g rho)) := by
    apply hgAnalytic.continuousAt.continuousWithinAt.tendsto.congr'
    filter_upwards [hgFactor, self_mem_nhdsWithin] with s hs hsrho
    have hsNe : Not (s - rho = 0) := by
      exact sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsrho)
    rw [hs]
    simp [zpow_neg_one, hsNe]
  have hDifference : Tendsto (fun s : Complex => s - rho)
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    have hContinuous : ContinuousAt (fun s : Complex => s - rho) rho := by
      fun_prop
    simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hStartup : Tendsto (nicolasPsiMellinStartup 3)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (nicolasPsiMellinStartup 3 rho)) :=
    (nicolasPsiMellinStartup_three_continuousAt rho).tendsto.mono_left
      nhdsWithin_le_nhds
  have hStartupScaled : Tendsto
      (fun s : Complex => (s - rho) * nicolasPsiMellinStartup 3 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    simpa using hDifference.mul hStartup
  refine Exists.intro (g rho) (And.intro hgZero ?_)
  have hTail := hFullScaled.sub hStartupScaled
  convert hTail using 1
  . funext s
    unfold nicolasPsiMellinTailContinuation
    ring
  . ring

/-- The nonzero Laurent coefficient remains visible on the positive real ray
entering the zeta zero. -/
theorem nicolasPsiMellinTailContinuation_three_simplePoleLimit_Ioi
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRhoZero : Not (rho = 0)) (hOne : Not (rho = 1)) :
    Exists fun c : Complex => And (Not (c = 0))
      (Tendsto
        (fun u : Real => (u : Complex) *
          nicolasPsiMellinTailContinuation 3 (rho + (u : Complex)))
        (nhdsWithin 0 (Ioi 0)) (nhds c)) := by
  choose c hc hLimit using
    nicolasPsiMellinTailContinuation_three_simplePoleLimit
      hZero hRhoZero hOne
  have hRay : Tendsto (fun u : Real => rho + (u : Complex))
      (nhdsWithin 0 (Ioi 0))
      (nhdsWithin rho (Set.compl {rho})) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    . have hContinuous : ContinuousAt
          (fun u : Real => rho + (u : Complex)) 0 := by
        fun_prop
      simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
    . filter_upwards [self_mem_nhdsWithin] with u hu
      apply Set.mem_compl_singleton_iff.mpr
      intro hEq
      have huZero : ((u : Real) : Complex) = 0 := by
        apply add_left_cancel (a := rho)
        simpa using hEq
      exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hu)) huZero
  refine Exists.intro c (And.intro hc ?_)
  simpa [Function.comp_def] using hLimit.comp hRay


/-- The removable regular part of zeta at one.  Away from one this is exactly
`zeta(s) - 1 / (s - 1)`; at one it is assigned its punctured limit. -/
def nicolasZetaRegularPart (s : Complex) : Complex :=
  Function.update
    (fun w : Complex => riemannZeta w - 1 / (w - 1)) 1
    (limUnder (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (fun w : Complex => riemannZeta w - 1 / (w - 1))) s

theorem nicolasZetaRegularPart_eq_of_ne_one
    {s : Complex} (hs : Not (s = 1)) :
    nicolasZetaRegularPart s = riemannZeta s - 1 / (s - 1) := by
  simp [nicolasZetaRegularPart, hs]

/-- The regular part is entire after filling the removable singularity. -/
theorem nicolasZetaRegularPart_differentiable :
    Differentiable Complex nicolasZetaRegularPart := by
  intro s
  let f : Complex -> Complex := fun w => riemannZeta w - 1 / (w - 1)
  by_cases hs : s = 1
  . subst s
    have hDiffAway : DifferentiableOn Complex f
        (Set.univ \ {1}) := by
      intro w hw
      have hwOne : Not (w = 1) := by
        exact Set.mem_compl_singleton_iff.mp hw.2
      have hNumerator : DifferentiableAt Complex
          (fun _ : Complex => (1 : Complex)) w := by fun_prop
      have hDenominator : DifferentiableAt Complex
          (fun z : Complex => z - 1) w := by fun_prop
      dsimp [f]
      exact ((differentiableAt_riemannZeta hwOne).sub
        (hNumerator.div hDenominator (sub_ne_zero.mpr hwOne))).differentiableWithinAt
    have hLittleO : (fun w : Complex => f w - f 1) =o[
        nhdsWithin 1 (Set.compl {(1 : Complex)})]
        (fun w : Complex => Inv.inv (w - 1)) := by
      refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
      . filter_upwards [self_mem_nhdsWithin] with w hw hwInv
        rw [inv_eq_zero, sub_eq_zero] at hwInv
        tauto
      . simp_rw [div_eq_mul_inv, inv_inv, sub_mul,
          (by ring_nf : nhds (0 : Complex) =
            nhds ((1 - 1) - f 1 * (1 - 1)))]
        apply Tendsto.sub
        . simp_rw [mul_comm (f _), f, mul_sub]
          apply riemannZeta_residue_one.sub
          refine Tendsto.congr' ?_
            (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)
          filter_upwards [self_mem_nhdsWithin] with w hw
          field_simp [sub_ne_zero.mpr
            (Set.mem_compl_singleton_iff.mp hw)]
        . exact ((tendsto_id.sub tendsto_const_nhds).mono_left
            nhdsWithin_le_nhds).const_mul _
    have hFilled := Complex.differentiableOn_update_limUnder_of_isLittleO
      (s := Set.univ) (c := (1 : Complex)) univ_mem hDiffAway hLittleO
    change DifferentiableAt Complex
      (Function.update f 1
        (limUnder (nhdsWithin 1 (Set.compl {(1 : Complex)})) f)) 1
    exact (hFilled 1 (Set.mem_univ 1)).differentiableAt Filter.univ_mem
  . have hBase : DifferentiableAt Complex f s := by
      have hNumerator : DifferentiableAt Complex
          (fun _ : Complex => (1 : Complex)) s := by fun_prop
      have hDenominator : DifferentiableAt Complex
          (fun z : Complex => z - 1) s := by fun_prop
      dsimp [f]
      exact (differentiableAt_riemannZeta hs).sub
        (hNumerator.div hDenominator (sub_ne_zero.mpr hs))
    change DifferentiableAt Complex
      (Function.update f 1
        (limUnder (nhdsWithin 1 (Set.compl {(1 : Complex)})) f)) s
    apply hBase.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    simp [Function.update_of_ne
      (Set.mem_compl_singleton_iff.mp hw)]

/-- The entire factor left after extracting zeta's simple pole at one. -/
def nicolasZetaPoleFactor (s : Complex) : Complex :=
  1 + (s - 1) * nicolasZetaRegularPart s

theorem nicolasZetaPoleFactor_differentiable :
    Differentiable Complex nicolasZetaPoleFactor := by
  intro s
  unfold nicolasZetaPoleFactor
  have hConst : DifferentiableAt Complex
      (fun _ : Complex => (1 : Complex)) s := by fun_prop
  have hDifference : DifferentiableAt Complex
      (fun w : Complex => w - 1) s := by fun_prop
  exact hConst.add
    (hDifference.mul (nicolasZetaRegularPart_differentiable s))

@[simp] theorem nicolasZetaPoleFactor_one :
    nicolasZetaPoleFactor 1 = 1 := by
  unfold nicolasZetaPoleFactor
  ring

theorem riemannZeta_eq_nicolasZetaPoleFactor_div
    {s : Complex} (hs : Not (s = 1)) :
    riemannZeta s = nicolasZetaPoleFactor s / (s - 1) := by
  unfold nicolasZetaPoleFactor
  rw [nicolasZetaRegularPart_eq_of_ne_one hs]
  field_simp [sub_ne_zero.mpr hs]
  ring

theorem logDeriv_riemannZeta_eq_poleFactor_sub
    {s : Complex} (hs : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    logDeriv riemannZeta s =
      logDeriv nicolasZetaPoleFactor s - 1 / (s - 1) := by
  have hLocal : Filter.EventuallyEq (nhds s) riemannZeta
      (fun w : Complex => nicolasZetaPoleFactor w / (w - 1)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    exact riemannZeta_eq_nicolasZetaPoleFactor_div
      (Set.mem_compl_singleton_iff.mp hw)
  have hLogCongr := logDeriv_congr_nhds hLocal
  have hLogAt : logDeriv riemannZeta s =
      logDeriv (fun w : Complex => nicolasZetaPoleFactor w / (w - 1)) s :=
    hLogCongr.self_of_nhds
  have hFactor : Not (nicolasZetaPoleFactor s = 0) := by
    intro hFactorZero
    have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hs
    rw [hFactorZero, zero_div] at hIdentity
    exact hZeta hIdentity
  calc
    logDeriv riemannZeta s =
        logDeriv (fun w : Complex =>
          nicolasZetaPoleFactor w / (w - 1)) s := hLogAt
    _ = logDeriv nicolasZetaPoleFactor s -
        logDeriv (fun w : Complex => w - 1) s :=
      logDeriv_div s hFactor (sub_ne_zero.mpr hs)
        (nicolasZetaPoleFactor_differentiable s) (by fun_prop)
    _ = logDeriv nicolasZetaPoleFactor s - 1 / (s - 1) := by
      congr 1
      simp [logDeriv_apply]

/-- After the pole at one is extracted, the complete psi Mellin continuation
is the regular logarithmic derivative of the pole factor. -/
theorem nicolasPsiMellinContinuation_eq_poleFactor
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    nicolasPsiMellinContinuation s =
      -(logDeriv nicolasZetaPoleFactor s + 1) / s := by
  unfold nicolasPsiMellinContinuation
  have hLog := logDeriv_riemannZeta_eq_poleFactor_sub hsOne hZeta
  rw [show -deriv riemannZeta s / riemannZeta s =
      -(logDeriv riemannZeta s) by
        rw [logDeriv_apply]
        ring,
    hLog]
  field_simp [hsZero, sub_ne_zero.mpr hsOne]
  ring

theorem logDeriv_nicolasZetaPoleFactor_continuousAt_one :
    ContinuousAt (logDeriv nicolasZetaPoleFactor) 1 := by
  rw [show logDeriv nicolasZetaPoleFactor =
      (fun s : Complex => deriv nicolasZetaPoleFactor s /
        nicolasZetaPoleFactor s) by rfl]
  exact (nicolasZetaPoleFactor_differentiable.deriv 1).continuousAt.div
    (nicolasZetaPoleFactor_differentiable 1).continuousAt (by simp)

/-- The complete psi Mellin continuation has a finite punctured limit at one.
This is the endpoint cancellation complementary to the genuine pole at a
nontrivial zeta zero. -/
theorem nicolasPsiMellinContinuation_tendsto_one :
    Tendsto nicolasPsiMellinContinuation
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1))) := by
  have hRegular : Tendsto
      (fun s : Complex => -(logDeriv nicolasZetaPoleFactor s + 1) / s)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1))) := by
    have hContinuous : ContinuousAt
        (fun s : Complex => -(logDeriv nicolasZetaPoleFactor s + 1) / s) 1 :=
      (logDeriv_nicolasZetaPoleFactor_continuousAt_one.add
        continuousAt_const).neg.div continuousAt_id (by norm_num)
    simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hZeroNeighborhood :
      Membership.mem (nhds (1 : Complex)) (Set.compl {(0 : Complex)}) :=
    isOpen_compl_singleton.mem_nhds
      (Set.mem_compl_singleton_iff.mpr (by norm_num))
  have hZeroWithin : Membership.mem
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (Set.compl {(0 : Complex)}) :=
    nhdsWithin_le_nhds hZeroNeighborhood
  apply hRegular.congr'
  filter_upwards
      [riemannZeta_eventually_ne_zero_nhds_one.filter_mono
        nhdsWithin_le_nhds,
      hZeroWithin,
      self_mem_nhdsWithin] with s hZeta hsZeroMem hs
  have hsOne : Not (s = 1) := Set.mem_compl_singleton_iff.mp hs
  have hsZero : Not (s = 0) :=
    Set.mem_compl_singleton_iff.mp hsZeroMem
  exact (nicolasPsiMellinContinuation_eq_poleFactor
    hsZero hsOne hZeta).symm

theorem nicolasPsiMellinTailContinuation_three_tendsto_one :
    Tendsto (nicolasPsiMellinTailContinuation 3)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1) -
        nicolasPsiMellinStartup 3 1)) := by
  have hStartup : Tendsto (nicolasPsiMellinStartup 3)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (nicolasPsiMellinStartup 3 1)) :=
    (nicolasPsiMellinStartup_three_continuousAt 1).tendsto.mono_left
      nhdsWithin_le_nhds
  have hDifference := nicolasPsiMellinContinuation_tendsto_one.sub hStartup
  convert hDifference using 1
  . rfl


/-- The exact integrand in the shifted representation of `nicolasJMellin`. -/
def nicolasJMellinShiftIntegrand (z : Complex) (u : Real) : Complex :=
  ((u + 1 : Real) : Complex) *
    ((nicolasPsiMellinTailContinuation 3
          (((u + 1 : Real) : Complex) - z) -
        (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
          ((u + 1 : Real) : Complex)) / z)


/-- Negating the required negative excursion gives the exact eventual
one-sided bound used by Landau's positivity argument. -/
theorem eventually_nicolasJ_add_rpow_pos_of_not_omegaMinus
    {b : Real}
    (hNot : Not (AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)))) :
    Filter.Eventually
      (fun x : Real => 0 < nicolasJ x + x ^ (-b)) atTop := by
  unfold AtTopOmegaMinus AtTopOmegaPlus at hNot
  push Not at hNot
  specialize hNot 1 zero_lt_one
  choose X hX using hNot
  filter_upwards [eventually_ge_atTop X] with x hx
  have hStrict := hX x hx
  linarith

/-- The eventual Landau sign can be represented by one finite startup
frontier, chosen beyond the fixed Mellin startup at three. -/
theorem exists_nicolasLandauPositiveTail_start
    {b : Real}
    (hNot : Not (AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)))) :
    Exists fun X : Real => And (3 <= X)
      (forall x : Real, X < x -> 0 <= nicolasJ x + x ^ (-b)) := by
  have hEventually :=
    eventually_nicolasJ_add_rpow_pos_of_not_omegaMinus hNot
  choose X hX using eventually_atTop.1 hEventually
  refine Exists.intro (max 3 X) (And.intro (le_max_left 3 X) ?_)
  intro x hx
  exact (hX x ((le_max_right 3 X).trans hx.le)).le


end

end Robin1984
