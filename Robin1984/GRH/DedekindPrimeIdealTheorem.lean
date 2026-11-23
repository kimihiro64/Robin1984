import PrimeNumberTheoremAnd.Wiener
import Robin1984.GRH.DedekindIntegratedTailBridge
import Robin1984.GRH.DedekindLineBridge

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Wiener-Ikehara proof of the prime ideal theorem.
- Formalization note: Prime-ideal Chebyshev asymptotics.
- PROVENANCE-END
-/

/-!
# Prime-ideal Chebyshev asymptotics

The pinned Wiener-Ikehara theorem acts on the natural-index norm
coefficients of the actual Dedekind Dirichlet series.
-/

open Filter NumberField Robin1984.GRH Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

private theorem initial_regularizedLogDeriv {s : Complex} (hs : 1 < s.re) :
    -logDeriv (entirePoleFreeDedekindZeta K) s =
      (-deriv (dedekindZeta K) s / dedekindZeta K s) - 1 / (s - 1) := by
  have hs0 : Not (s = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs1 : Not (s - 1 = 0) := Complex.ne_zero_of_re_pos (by
    simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hs)
  let L := logDeriv (entirePoleFreeDedekindZeta K) s
  let A := -deriv (dedekindZeta K) s / dedekindZeta K s
  have h : A / s - 1 / (s - 1) = -(L + 1) / s := actualDedekindError_logDeriv_identity K hs
  have hA : A - s / (s - 1) = -(L + 1) := by
    have hProd := congrArg (fun z : Complex => z * s) h
    have hCancel (a : Complex) : a / s * s = a := by field_simp [hs0]
    have hCross : 1 / (s - 1) * s = s / (s - 1) := by ring
    rwa [sub_mul, hCancel, hCancel, hCross] at hProd
  have hRat : s / (s - 1) = 1 + 1 / (s - 1) := by
    field_simp [hs1]
    ring
  rw [hRat] at hA
  change -L = A - 1 / (s - 1)
  calc
    -L = -(L + 1) + 1 := by ring
    _ = A - (1 + 1 / (s - 1)) + 1 := congrArg (fun z : Complex => z + 1) hA.symm
    _ = A - 1 / (s - 1) := by ring

private theorem tendsto_cast_floor_succ_div :
    Tendsto (fun x : Real => ((Nat.floor x + 1 : Nat) : Real) / x) atTop (nhds 1) := by
  have hDiv : Tendsto (fun x : Real => 1 / x) atTop (nhds (0 : Real)) :=
    (tendsto_inv_atTop_zero : Tendsto (fun x : Real => Inv.inv x) atTop (nhds 0)).congr'
      (Filter.Eventually.of_forall (fun x => (one_div x).symm))
  have hUpper : Tendsto (fun x : Real => 1 + 1 / x) atTop (nhds 1) := by
    have h : Tendsto (fun x : Real => 1 + 1 / x) atTop (nhds ((1 : Real) + 0)) :=
      (tendsto_const_nhds : Tendsto (fun _ : Real => 1) atTop (nhds (1 : Real))).add hDiv
    simpa only [add_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Real => 1) atTop (nhds (1 : Real))) hUpper ?lower ?upper
  case lower =>
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    rw [<- div_self hx.ne']
    have hFloor : x <= ((Nat.floor x + 1 : Nat) : Real) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one x).le
    exact div_le_div_of_nonneg_right hFloor hx.le
  case upper =>
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    rw [Nat.cast_add, Nat.cast_one, add_div]
    apply add_le_add _ (le_refl _)
    calc
      (Nat.floor x : Real) / x <= x / x :=
        div_le_div_of_nonneg_right (Nat.floor_le hx.le) hx.le
      _ = 1 := div_self hx.ne'

theorem dedekindChebyshev_div_tendsto_one :
    Tendsto (fun x : Real => dedekindChebyshev K x / x) atTop (nhds 1) := by
  let a := dedekindNormCoeff K
  let G := fun s : Complex => -logDeriv (entirePoleFreeDedekindZeta K) s
  have hPos : 0 <= a := dedekindNormCoeff_nonneg K
  have hSum (sigma : Real) (hs : 1 < sigma) :
      Summable (nterm (fun n => (a n : Complex)) sigma) := by
    have h := hasSum_dedekindNormCoeff K (s := (sigma : Complex)) (by
      simpa only [Complex.ofReal_re] using hs)
    have hTerms : Summable (LSeries.term (fun n => (a n : Complex)) (sigma : Complex)) :=
      h.LSeriesSummable
    exact hTerms.norm.congr (fun n =>
      (nterm_eq_norm_term (f := fun m => (a m : Complex)) (n := n)).symm)
  have hG : ContinuousOn G {s : Complex | 1 <= s.re} := by
    intro s hs
    have hf := analyticAt_entirePoleFreeDedekindZeta K s
    have hNonzero := entirePoleFreeDedekindZeta_ne_zero_of_one_le_re K hs
    have hg : AnalyticAt Complex G s := by
      unfold G
      simp only [logDeriv_apply]
      exact (hf.deriv.div hf hNonzero).neg
    exact hg.continuousAt.continuousWithinAt
  have hEq : Set.EqOn G
      (fun s : Complex => LSeries (fun n => (a n : Complex)) s - (1 : Complex) / (s - 1))
      {s : Complex | 1 < s.re} := by
    intro s hs
    change G s = LSeries (fun n => (dedekindNormCoeff K n : Complex)) s - 1 / (s - 1)
    rw [(hasSum_dedekindNormCoeff K hs).LSeries_eq]
    exact initial_regularizedLogDeriv K hs
  have hNatural : Tendsto (fun N : Nat => cumsum a N / N) atTop (nhds 1) :=
    WienerIkeharaTheorem'' hPos hSum hG hEq
  have hTop : Tendsto (fun x : Real => Nat.floor x + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop (n : Real)] with x hx
    exact (Nat.le_floor hx).trans (Nat.le_succ _)
  have hMul := (hNatural.comp hTop).mul tendsto_cast_floor_succ_div
  have hNormalized : Tendsto (fun x : Real =>
      cumsum a (Nat.floor x + 1) / ((Nat.floor x + 1 : Nat) : Real) *
        (((Nat.floor x + 1 : Nat) : Real) / x)) atTop (nhds 1) := by
    change Tendsto (fun x : Real =>
      cumsum a (Nat.floor x + 1) / ((Nat.floor x + 1 : Nat) : Real) *
        (((Nat.floor x + 1 : Nat) : Real) / x)) atTop (nhds ((1 : Real) * 1)) at hMul
    simpa only [one_mul] using hMul
  apply hNormalized.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  have hN : Not (((Nat.floor x + 1 : Nat) : Real) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  rw [dedekindChebyshev_eq_sum_normCoeff K]
  change cumsum a (Nat.floor x + 1) / ((Nat.floor x + 1 : Nat) : Real) *
      (((Nat.floor x + 1 : Nat) : Real) / x) = cumsum a (Nat.floor x + 1) / x
  field_simp [hx.ne', hN]

end DedekindZeta
