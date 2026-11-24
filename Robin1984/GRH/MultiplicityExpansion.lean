import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Robin1984.GRH.SmoothedForward

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Mellin inversion and the canonical triangular zero expansion on the positive real axis.
- Formalization note: The logarithmic rescaling isolates the critical-line frequencies, and continuity upgrades the almost-everywhere triangular expansion to pointwise equality.
- PROVENANCE-END
-/

/-!
# Logarithmic triangular zero expansion

The normalized triangular expansion splits into its critical-line Fourier
series and a remainder that tends to zero.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Filter MeasureTheory
open scoped Topology Classical

/-- The zero term at x = exp t, divided by the square root of x. -/
def logScaledTriangularZeroTerm (rho : Complex) (t : Real) : Complex :=
  (Real.exp (-t / 2) : Complex) * triangularZeroTerm rho (Real.exp t)

/-- The limiting Fourier term of a zero on the critical line. -/
def triangularCriticalSpectrumTerm (rho : Complex) (t : Real) : Complex :=
  if rho.re = 1 / 2 then
    Complex.exp ((rho - 1 / 2) * (t : Complex)) / (rho * (rho + 1))
  else 0

theorem logScaledTriangularZeroTerm_eq (rho : Complex) (t : Real) :
    logScaledTriangularZeroTerm rho t =
      (Complex.exp ((rho - 1 / 2) * (t : Complex)) -
        Complex.exp ((-(3 / 2) : Complex) * (t : Complex))) / (rho * (rho + 1)) := by
  have hp (z : Complex) :
      ((Real.exp t : Real) : Complex) ^ z = Complex.exp (z * (t : Complex)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
      <- Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp, mul_comm]
  have he : (Real.exp (-t / 2) : Complex) =
      Complex.exp (-(1 / 2 : Complex) * (t : Complex)) := by
    rw [Complex.ofReal_exp]
    congr 1
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  unfold logScaledTriangularZeroTerm triangularZeroTerm
  simp only [hp, he]
  calc
    _ = (Complex.exp (-(1 / 2 : Complex) * (t : Complex)) *
          Complex.exp (rho * (t : Complex)) -
        Complex.exp (-(1 / 2 : Complex) * (t : Complex)) *
          Complex.exp ((-1 : Complex) * (t : Complex))) / (rho * (rho + 1)) := by ring
    _ = _ := by
      have hPos : -(1 / 2 : Complex) * (t : Complex) + rho * (t : Complex) =
          (rho - 1 / 2) * (t : Complex) := by ring
      have hNeg : -(1 / 2 : Complex) * (t : Complex) + (-1 : Complex) * (t : Complex) =
          (-(3 / 2) : Complex) * (t : Complex) := by ring
      rw [<- Complex.exp_add, <- Complex.exp_add, hPos, hNeg]

private theorem tendsto_cexp_pureLinear_atTop_zero (c : Complex) (hc : c.re < 0) :
    Tendsto (fun t : Real => Complex.exp (c * (t : Complex))) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h : Tendsto (fun t : Real => Real.exp (c.re * t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc)
  simpa only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, id] using h

theorem tendsto_logarithmicTriangularZeroError (rho : Complex) (hR : rho.re <= 1 / 2) :
    Tendsto (fun t => logScaledTriangularZeroTerm rho t - triangularCriticalSpectrumTerm rho t)
      atTop (nhds 0) := by
  have hD : Tendsto (fun t : Real => Complex.exp ((-(3 / 2) : Complex) * (t : Complex)))
      atTop (nhds 0) :=
    tendsto_cexp_pureLinear_atTop_zero _ (by norm_num [Complex.div_re])
  by_cases h : rho.re = 1 / 2
  case pos =>
    have he : (fun t => logScaledTriangularZeroTerm rho t -
        triangularCriticalSpectrumTerm rho t) = fun t : Real =>
      -Complex.exp ((-(3 / 2) : Complex) * (t : Complex)) / (rho * (rho + 1)) := by
      funext t
      rw [logScaledTriangularZeroTerm_eq, triangularCriticalSpectrumTerm, if_pos h]
      ring
    rw [he]
    simpa only [neg_zero, zero_div] using hD.neg.div_const (rho * (rho + 1))
  case neg =>
    have hr : (rho - 1 / 2).re < 0 := by
      have hp := lt_of_le_of_ne hR h
      norm_num [Complex.sub_re, Complex.div_re]
      linarith
    have hE := tendsto_cexp_pureLinear_atTop_zero (rho - 1 / 2) hr
    simp only [logScaledTriangularZeroTerm_eq, triangularCriticalSpectrumTerm, if_neg h, sub_zero]
    simpa only [sub_self, zero_div] using (hE.sub hD).div_const (rho * (rho + 1))

private theorem norm_cexp_pureLinear_le_one (c : Complex) (hc : c.re <= 0) (t : Real)
    (ht : 0 <= t) : norm (Complex.exp (c * (t : Complex))) <= 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    mul_nonpos_of_nonpos_of_nonneg hc ht

/-- Strictly left zeros and the inverse-power subtraction vanish in the log-scale limit. -/
theorem tendsto_tsum_logarithmicTriangularZeroError {i : Type*} (rho : i -> Complex)
    (hR : forall j, (rho j).re <= 1 / 2)
    (hSum : Summable (fun j => Inv.inv (norm (rho j * (rho j + 1))))) :
    Tendsto (fun t => tsum (fun j =>
      logScaledTriangularZeroTerm (rho j) t - triangularCriticalSpectrumTerm (rho j) t))
      atTop (nhds 0) := by
  have hDom : Filter.Eventually (fun t : Real => forall j : i,
      norm (logScaledTriangularZeroTerm (rho j) t - triangularCriticalSpectrumTerm (rho j) t) <=
        3 * Inv.inv (norm (rho j * (rho j + 1)))) atTop := by
    filter_upwards [eventually_ge_atTop (0 : Real)] with t ht
    intro j
    let z := rho j
    let d := norm (z * (z + 1))
    have hc : (z - 1 / 2).re <= 0 := by
      have h := hR j
      norm_num [Complex.sub_re, Complex.div_re]
      linarith
    have ha := norm_cexp_pureLinear_le_one (z - 1 / 2) hc t ht
    have hb := norm_cexp_pureLinear_le_one (-(3 / 2)) (by norm_num [Complex.div_re]) t ht
    have hn : norm (logScaledTriangularZeroTerm z t) <= 2 / d := by
      rw [logScaledTriangularZeroTerm_eq, norm_div]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      have h := norm_sub_le (Complex.exp ((z - 1 / 2) * (t : Complex)))
        (Complex.exp ((-(3 / 2) : Complex) * (t : Complex)))
      linarith
    have hs : norm (triangularCriticalSpectrumTerm z t) <= 1 / d := by
      unfold triangularCriticalSpectrumTerm
      by_cases h : z.re = 1 / 2
      case pos => rw [if_pos h, norm_div]; exact div_le_div_of_nonneg_right ha (norm_nonneg _)
      case neg => rw [if_neg h, norm_zero]; exact div_nonneg zero_le_one (norm_nonneg _)
    have htot := norm_sub_le (logScaledTriangularZeroTerm z t) (triangularCriticalSpectrumTerm z t)
    change norm (logScaledTriangularZeroTerm z t - triangularCriticalSpectrumTerm z t) <=
      3 * Inv.inv d
    rw [<- div_eq_mul_inv]
    linarith only [htot, hn, hs, show 2 / d + 1 / d = 3 / d from by rw [<- add_div]; norm_num]
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
    (hSum.mul_left 3) (fun j => tendsto_logarithmicTriangularZeroError (rho j) (hR j)) hDom

/-- The full triangular zero series is continuous on the open positive tail. -/
theorem continuousOn_triangularZeroSeries_of_weight_bound {i : Type*} (rho : i -> Complex)
    (hR : forall j, (rho j).re <= 1 / 2)
    (hSum : Summable (fun j => Inv.inv (norm (rho j * (rho j + 1))))) :
    ContinuousOn (fun x : Real => tsum (fun j => triangularZeroTerm (rho j) x))
      (Set.Ioi (1 : Real)) := by
  let S (t : Real) := tsum (fun j => logScaledTriangularZeroTerm (rho j) t)
  have hScaleBound (j : i) (t : Real) (ht : 0 <= t) :
      norm (logScaledTriangularZeroTerm (rho j) t) <=
        2 * Inv.inv (norm (rho j * (rho j + 1))) := by
    have hr : (rho j - 1 / 2).re <= 0 := by
      have h := hR j
      norm_num [Complex.sub_re, Complex.div_re]
      linarith
    have h1 := norm_cexp_pureLinear_le_one (rho j - 1 / 2) hr t ht
    have h2 := norm_cexp_pureLinear_le_one (-(3 / 2)) (by norm_num [Complex.div_re]) t ht
    rw [logScaledTriangularZeroTerm_eq, norm_div, <- div_eq_mul_inv]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    have h := norm_sub_le (Complex.exp ((rho j - 1 / 2) * (t : Complex)))
      (Complex.exp ((-(3 / 2) : Complex) * (t : Complex)))
    linarith only [h, h1, h2]
  have hTerm (j : i) : Continuous (logScaledTriangularZeroTerm (rho j)) := by
    simp only [show logScaledTriangularZeroTerm (rho j) = (fun t : Real =>
      (Complex.exp ((rho j - 1 / 2) * (t : Complex)) -
        Complex.exp ((-(3 / 2) : Complex) * (t : Complex))) /
          (rho j * (rho j + 1))) from funext (logScaledTriangularZeroTerm_eq (rho j))]
    have hExp (z : Complex) : Continuous (fun t : Real => Complex.exp (z * (t : Complex))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact ((hExp _).sub (hExp _)).div_const _
  have hS : ContinuousOn S (Set.Ioi 0) := by
    intro t ht
    have hNonneg : Filter.Eventually (fun v : Real => 0 <= v)
        (nhdsWithin t (Set.Ioi (0 : Real))) :=
      (show Filter.Eventually (fun v : Real => 0 < v) (nhdsWithin t (Set.Ioi (0 : Real))) from
        self_mem_nhdsWithin).mono (fun x hx => hx.le)
    have hDom := hNonneg.mono (fun v hv j => hScaleBound j v hv)
    have hEach (j : i) : Tendsto (logScaledTriangularZeroTerm (rho j))
        (nhdsWithin t (Set.Ioi (0 : Real))) (nhds (logScaledTriangularZeroTerm (rho j) t)) :=
      (hTerm j).continuousWithinAt
    have hLim := tendsto_tsum_of_dominated_convergence (hSum.mul_left 2) hEach hDom
    exact hLim
  have hLog : ContinuousOn Real.log (Set.Ioi (1 : Real)) := by
    intro x hx
    exact (Real.continuousAt_log (ne_of_gt (zero_lt_one.trans hx))).continuousWithinAt
  have hMap : Set.MapsTo Real.log (Set.Ioi (1 : Real)) (Set.Ioi 0) := by
    intro x hx
    exact Real.log_pos hx
  have hScale : Continuous (fun x : Real => (Real.exp (x / 2) : Complex)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2))
  refine (((hScale.continuousOn.comp hLog hMap)).mul (hS.comp hLog hMap)).congr ?_
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  change tsum (fun j => triangularZeroTerm (rho j) x) =
    (Real.exp (Real.log x / 2) : Complex) * S (Real.log x)
  unfold S
  rw [<- tsum_mul_left]
  refine tsum_congr ?_
  intro j
  unfold logScaledTriangularZeroTerm
  rw [Real.exp_log hx0, <- mul_assoc, <- Complex.ofReal_mul, <- Real.exp_add]
  have h : Real.log x / 2 + -(Real.log x) / 2 = 0 := by ring
  rw [h, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- Continuity gives the triangular zero expansion at every point of the
open tail. -/
theorem eqOn_triangularZeroSeries_of_ae {i : Type*} (rho : i -> Complex)
    (hRho : forall j, (rho j).re <= 1 / 2)
    (hSum : Summable (fun j => Inv.inv (norm (rho j * (rho j + 1)))))
    {R E : Real -> Complex} (hR : ContinuousOn R (Set.Ioi 1))
    (hE : ContinuousOn E (Set.Ioi 1))
    (hAE : Filter.EventuallyEq (ae (volume.restrict (Set.Ioi (1 : Real)))) R
      (fun x => E x + tsum (fun j => triangularZeroTerm (rho j) x))) :
    Set.EqOn R (fun x => E x + tsum (fun j => triangularZeroTerm (rho j) x))
      (Set.Ioi 1) := by
  let U (x : Real) := norm (R x - (E x + tsum (fun j => triangularZeroTerm (rho j) x)))
  have hCont : ContinuousOn U (Set.Ioi 1) :=
    (hR.sub (hE.add (continuousOn_triangularZeroSeries_of_weight_bound rho hRho hSum))).norm
  have hBound : Filter.Eventually (fun x => U x <= 0 * Real.sqrt x)
      (ae (volume.restrict (Set.Ioi (1 : Real)))) := hAE.mono (fun x hx => by
    simp only [U, hx, sub_self, norm_zero, zero_mul, le_refl])
  intro x hx
  have hU := pointwise_sqrtBound_of_ae hCont hBound hx
  rw [zero_mul] at hU
  have hz := le_antisymm hU (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end Robin1984.GRH
