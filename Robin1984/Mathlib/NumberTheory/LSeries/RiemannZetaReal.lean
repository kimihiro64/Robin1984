/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Robin1984.Mathlib.Probability.Moments.MGFAnalyticContinuation

/-!
# The Riemann zeta function on the positive real axis

This file fills the removable part of the pole at one, represents the Euler
summation remainder as a nonnegative moment-generating transform, and proves
nonvanishing of the Riemann zeta function on the positive real axis.
-/

@[expose] public section

namespace RiemannZeta

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The removable regular part of zeta at one.  Away from one this is exactly
`zeta(s) - 1 / (s - 1)`; at one it is assigned its punctured limit. -/
def regularPart (s : Complex) : Complex :=
  Function.update
    (fun w : Complex => riemannZeta w - 1 / (w - 1)) 1
    (limUnder (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (fun w : Complex => riemannZeta w - 1 / (w - 1))) s

theorem regularPart_eq_of_ne_one
    {s : Complex} (hs : Not (s = 1)) :
    regularPart s = riemannZeta s - 1 / (s - 1) := by
  simp [regularPart, hs]

/-- The regular part is entire after filling the removable singularity. -/
theorem regularPart_differentiable :
    Differentiable Complex regularPart := by
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
def poleFactor (s : Complex) : Complex :=
  1 + (s - 1) * regularPart s

theorem poleFactor_differentiable :
    Differentiable Complex poleFactor := by
  intro s
  unfold poleFactor
  have hConst : DifferentiableAt Complex
      (fun _ : Complex => (1 : Complex)) s := by fun_prop
  have hDifference : DifferentiableAt Complex
      (fun w : Complex => w - 1) s := by fun_prop
  exact hConst.add
    (hDifference.mul (regularPart_differentiable s))

@[simp] theorem poleFactor_one :
    poleFactor 1 = 1 := by
  unfold poleFactor
  ring

theorem eq_poleFactor_div
    {s : Complex} (hs : Not (s = 1)) :
    riemannZeta s = poleFactor s / (s - 1) := by
  unfold poleFactor
  rw [regularPart_eq_of_ne_one hs]
  field_simp [sub_ne_zero.mpr hs]
  ring

/-- The pole factor is nonzero wherever zeta is nonzero away from its pole. -/
theorem poleFactor_ne_zero_of_riemannZeta_ne_zero
    {s : Complex} (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    Not (poleFactor s = 0) := by
  intro hFactor
  have hIdentity := eq_poleFactor_div hsOne
  rw [hFactor, zero_div] at hIdentity
  exact hZeta hIdentity

def eulerSaw (x : Real) : Real :=
  x + 1 - (Int.ceil x : Real)

theorem eulerSaw_pos (x : Real) :
    0 < eulerSaw x := by
  unfold eulerSaw
  have h := Int.ceil_lt_add_one x
  linarith

theorem eulerSaw_le_one (x : Real) :
    eulerSaw x <= 1 := by
  unfold eulerSaw
  have h := Int.le_ceil x
  linarith

theorem eulerSaw_eq_sub_nat_on_cell
    (n : Nat) {x : Real}
    (hx : Membership.mem (Ioc ((n : Real) + 1) ((n : Real) + 2)) x) :
    eulerSaw x = x - ((n : Real) + 1) := by
  have hCeil : Int.ceil x = (n : Int) + 2 := by
    apply Int.ceil_eq_iff.mpr
    constructor
    case left =>
      push_cast
      linarith [hx.1]
    case right =>
      push_cast
      linarith [hx.2]
  unfold eulerSaw
  rw [hCeil]
  push_cast
  ring

theorem iUnion_eulerCells :
    (iUnion fun n : Nat =>
      Ioc ((n : Real) + 1) ((n : Real) + 2)) = Ioi (1 : Real) := by
  apply Set.ext
  intro x
  constructor
  case mp =>
    intro hx
    rw [mem_iUnion] at hx
    choose n hn using hx
    have hnNonneg : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
    have hOneLe : (1 : Real) <= (n : Real) + 1 := by linarith
    exact hOneLe.trans_lt hn.1
  case mpr =>
    intro hx
    change 1 < x at hx
    have hxNonneg : 0 <= x := le_trans (by norm_num) hx.le
    let m : Nat := Nat.ceil x
    have hUpper : x <= (m : Real) := by
      exact Nat.le_ceil x
    have hLower : (m : Real) - 1 < x := by
      have h := Nat.ceil_lt_add_one hxNonneg
      dsimp [m] at hUpper h
      linarith
    have hmTwo : 2 <= m := by
      by_contra hm
      have hmLe : m <= 1 := by omega
      have hmCast : (m : Real) <= 1 := by exact_mod_cast hmLe
      exact (not_lt_of_ge (hUpper.trans hmCast)) hx
    let n : Nat := m - 2
    rw [mem_iUnion]
    refine Exists.intro n ?_
    have hnOne : n + 1 = m - 1 := by
      dsimp [n]
      omega
    have hnTwo : n + 2 = m := by
      dsimp [n]
      omega
    have hmOne : 1 <= m := le_trans (by norm_num) hmTwo
    constructor
    case left =>
      calc
        (n : Real) + 1 = ((n + 1 : Nat) : Real) := by push_cast; rfl
        _ = ((m - 1 : Nat) : Real) := congrArg Nat.cast hnOne
        _ = (m : Real) - 1 := by rw [Nat.cast_sub hmOne]; norm_num
        _ < x := hLower
    case right =>
      calc
        x <= (m : Real) := hUpper
        _ = ((n + 2 : Nat) : Real) := congrArg Nat.cast hnTwo.symm
        _ = (n : Real) + 2 := by push_cast; rfl

theorem pairwise_disjoint_eulerCells :
    Pairwise (Function.onFun Disjoint fun n : Nat =>
      Ioc ((n : Real) + 1) ((n : Real) + 2)) := by
  intro i j hij
  obtain hijLt | hjiLt := lt_or_gt_of_ne hij
  case inl =>
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hCast : (i : Real) + 2 <= (j : Real) + 1 := by
      have hNat : i + 2 <= j + 1 := by omega
      exact_mod_cast hNat
    linarith [hxi.2, hxj.1]
  case inr =>
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hCast : (j : Real) + 2 <= (i : Real) + 1 := by
      have hNat : j + 2 <= i + 1 := by omega
      exact_mod_cast hNat
    linarith [hxj.2, hxi.1]

def eulerRemainderIntegrand (s x : Real) : Real :=
  eulerSaw x / x ^ (s + 1)

def eulerRemainder (s : Real) : Real :=
  integral (volume.restrict (Ioi 1))
    (fun x : Real => eulerRemainderIntegrand s x)

theorem eulerRemainderIntegrable
    {s : Real} (hs : 0 < s) :
    IntegrableOn (eulerRemainderIntegrand s) (Ioi 1) := by
  have hMajorant : IntegrableOn (fun x : Real => x ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  apply hMajorant.mono'
  case hf =>
    apply Measurable.aestronglyMeasurable
    unfold eulerRemainderIntegrand eulerSaw
    measurability
  case h =>
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx
    have hDenomNonneg : 0 <= x ^ (s + 1) :=
      Real.rpow_nonneg hxPos.le _
    have hValueNonneg : 0 <= eulerRemainderIntegrand s x := by
      unfold eulerRemainderIntegrand
      exact div_nonneg (eulerSaw_pos x).le hDenomNonneg
    calc
      norm (eulerRemainderIntegrand s x) =
          eulerRemainderIntegrand s x := abs_of_nonneg hValueNonneg
      _ <= 1 / x ^ (s + 1) := by
        unfold eulerRemainderIntegrand
        exact div_le_div_of_nonneg_right (eulerSaw_le_one x) hDenomNonneg
      _ = x ^ (-(s + 1)) := by
        rw [Real.rpow_neg hxPos.le]
        simp only [one_div]

theorem integral_eulerCell_eq_term
    (n : Nat) (s : Real) :
    integral (volume.restrict (Ioc ((n : Real) + 1) ((n : Real) + 2)))
        (fun x : Real => eulerRemainderIntegrand s x) =
      ZetaAsymptotics.term (n + 1) s := by
  unfold ZetaAsymptotics.term
  rw [intervalIntegral.integral_of_le (by linarith :
    ((n + 1 : Nat) : Real) <= ((n + 1 : Nat) : Real) + 1)]
  push_cast
  ring_nf
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hxCell : Membership.mem
      (Ioc ((n : Real) + 1) ((n : Real) + 2)) x := by
    simpa [add_comm] using hx
  unfold eulerRemainderIntegrand
  rw [eulerSaw_eq_sub_nat_on_cell n hxCell]
  push_cast
  ring

theorem eulerRemainder_eq_termTSum
    {s : Real} (hs : 0 < s) :
    eulerRemainder s = ZetaAsymptotics.termTSum s := by
  unfold eulerRemainder ZetaAsymptotics.termTSum
  rw [iUnion_eulerCells.symm]
  rw [MeasureTheory.integral_iUnion
    (fun _ => measurableSet_Ioc)
    pairwise_disjoint_eulerCells
    (by simpa [iUnion_eulerCells] using
      eulerRemainderIntegrable hs)]
  apply tsum_congr
  intro n
  exact integral_eulerCell_eq_term n s

def eulerDensity (x : Real) : NNReal :=
  Real.toNNReal (eulerSaw x / x)

theorem measurable_eulerDensity :
    Measurable eulerDensity := by
  unfold eulerDensity eulerSaw
  measurability

def eulerMeasure : Measure Real :=
  (volume.restrict (Ioi 1)).withDensity
    (fun x : Real => eulerDensity x)

theorem eulerDensity_coe
    {x : Real} (hx : 1 < x) :
    (eulerDensity x : Real) = eulerSaw x / x := by
  unfold eulerDensity
  rw [Real.coe_toNNReal]
  exact div_nonneg (eulerSaw_pos x).le (le_trans (by norm_num) hx.le)

theorem eulerDensity_mul_exp_eq_integrand
    {t x : Real} (hx : 1 < x) :
    (eulerDensity x : Real) * Real.exp (t * Real.log x) =
      eulerRemainderIntegrand (-t) x := by
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  rw [eulerDensity_coe hx]
  unfold eulerRemainderIntegrand
  rw [Real.rpow_def_of_pos hxPos]
  have hExp : Real.exp (t * Real.log x) *
      Real.exp (Real.log x * (-t + 1)) = x := by
    calc
      Real.exp (t * Real.log x) * Real.exp (Real.log x * (-t + 1)) =
          Real.exp (t * Real.log x + Real.log x * (-t + 1)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp (Real.log x) := by congr 1; ring
      _ = x := Real.exp_log hxPos
  field_simp [Real.exp_ne_zero, hxPos.ne']
  calc
    eulerSaw x * Real.exp (t * Real.log x) *
        Real.exp (Real.log x * (-t + 1)) =
      eulerSaw x *
        (Real.exp (t * Real.log x) *
          Real.exp (Real.log x * (-t + 1))) := by ring
    _ = eulerSaw x * x := by rw [hExp]

theorem mgf_eulerMeasure_neg_eq_remainder
    {s : Real} (_hs : 0 < s) :
    ProbabilityTheory.mgf Real.log eulerMeasure (-s) =
      eulerRemainder s := by
  unfold ProbabilityTheory.mgf eulerMeasure eulerRemainder
  rw [integral_withDensity_eq_integral_smul measurable_eulerDensity]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  change (eulerDensity x : Real) * Real.exp (-s * Real.log x) =
    eulerRemainderIntegrand s x
  simpa using eulerDensity_mul_exp_eq_integrand (t := -s) hx

theorem integrable_exp_log_eulerMeasure_of_neg
    {t : Real} (ht : t < 0) :
    Integrable (fun x : Real => Real.exp (t * Real.log x))
      eulerMeasure := by
  unfold eulerMeasure
  rw [integrable_withDensity_iff_integrable_smul measurable_eulerDensity]
  apply (eulerRemainderIntegrable (neg_pos.mpr ht)).congr_fun
  case hst =>
    intro x hx
    change eulerRemainderIntegrand (-t) x =
      (eulerDensity x : Real) * Real.exp (t * Real.log x)
    exact (eulerDensity_mul_exp_eq_integrand (t := t) hx).symm
  case hs =>
    exact measurableSet_Ioi

theorem neg_mem_eulerIntegrableExpSet
    {t : Real} (ht : t < 0) :
    Membership.mem
      (ProbabilityTheory.integrableExpSet Real.log eulerMeasure) t :=
  integrable_exp_log_eulerMeasure_of_neg ht

theorem termTSum_analyticAt_of_pos
    {s : Real} (hs : 0 < s) :
    AnalyticAt Real ZetaAsymptotics.termTSum s := by
  have hLeft := neg_mem_eulerIntegrableExpSet
    (t := -2 * s) (by linarith)
  have hRight := neg_mem_eulerIntegrableExpSet
    (t := -s / 2) (by linarith)
  have hInterior := mem_interior_integrableExpSet_of_two_sided
    hLeft hRight (by linarith : -2 * s < -s) (by linarith : -s < -s / 2)
  have hMgf : AnalyticAt Real
      (ProbabilityTheory.mgf Real.log eulerMeasure) (-s) :=
    ProbabilityTheory.analyticAt_mgf hInterior
  have hComp : AnalyticAt Real
      (fun u : Real =>
        ProbabilityTheory.mgf Real.log eulerMeasure (-u)) s := by
    simpa [Function.comp_def] using hMgf.comp (analyticAt_id.neg)
  have hEq : Filter.EventuallyEq (nhds s)
      (fun u : Real =>
        ProbabilityTheory.mgf Real.log eulerMeasure (-u))
      ZetaAsymptotics.termTSum := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    rw [mgf_eulerMeasure_neg_eq_remainder hu]
    exact eulerRemainder_eq_termTSum hu
  exact (analyticAt_congr hEq).mp hComp


theorem termTSum_nonneg
    {s : Real} (_hs : 0 < s) :
    0 <= ZetaAsymptotics.termTSum s := by
  unfold ZetaAsymptotics.termTSum
  exact tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) s)

set_option maxHeartbeats 300000 in
theorem poleFactor_eq_termTSum_of_one_lt
    {s : Real} (hs : 1 < s) :
    poleFactor (s : Complex) =
      (s * (1 - (s - 1) * ZetaAsymptotics.termTSum s) : Real) := by
  let Z : Real := tsum fun n : Nat =>
    1 / ((n : Real) + 1) ^ s
  let T : Real := ZetaAsymptotics.termTSum s
  change poleFactor (s : Complex) =
    ((s * (1 - (s - 1) * T) : Real) : Complex)
  have hRealSummable : Summable (fun n : Nat =>
      1 / ((n : Real) + 1) ^ s) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_rpow.mpr hs))
  have hCast : (Z : Complex) = tsum fun n : Nat =>
      1 / ((n : Complex) + 1) ^ (s : Complex) := by
    dsimp [Z]
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one]
    rw [Complex.ofReal_cpow (by positivity : 0 <= (n : Real) + 1) s]
    push_cast
    rfl
  have hZeta : riemannZeta (s : Complex) = (Z : Complex) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    exact hCast.symm
  have hLimit := ZetaAsymptotics.zeta_limit_aux1 hs
  change Z - 1 / (s - 1) =
    1 - s * T at hLimit
  have hsOne : Not ((s : Complex) = 1) := by
    exact Complex.ofReal_ne_one.mpr (ne_of_gt hs)
  have hPole := eq_poleFactor_div hsOne
  rw [hZeta] at hPole
  have hsSub : Not (s - 1 = 0) := sub_ne_zero.mpr (ne_of_gt hs)
  have hPoleMul : poleFactor (s : Complex) =
      (Z : Complex) * ((s : Complex) - 1) := by
    exact (div_eq_iff (sub_ne_zero.mpr hsOne)).mp hPole.symm
  have hReal : Z * (s - 1) =
      s * (1 - (s - 1) * T) := by
    have hZ : Z = 1 / (s - 1) +
        (1 - s * T) := by
      linarith [hLimit]
    calc
      Z * (s - 1) =
          (1 / (s - 1) +
            (1 - s * T)) * (s - 1) := by
        rw [hZ]
      _ = 1 + (1 - s * T) * (s - 1) := by
        rw [add_mul]
        simp [hsSub]
      _ = s * (1 - (s - 1) * T) := by
        ring
  calc
    poleFactor (s : Complex) =
        (Z : Complex) * ((s : Complex) - 1) := hPoleMul
    _ = ((Z * (s - 1) : Real) : Complex) := by push_cast; rfl
    _ = ((s * (1 - (s - 1) * T) : Real) : Complex) :=
      congrArg Complex.ofReal hReal

theorem poleFactor_re_eq_termTSum_of_pos
    {s : Real} (hs : 0 < s) :
    (poleFactor (s : Complex)).re =
      s * (1 - (s - 1) * ZetaAsymptotics.termTSum s) := by
  let F : Real -> Real := fun u => (poleFactor (u : Complex)).re
  let G : Real -> Real := fun u =>
    u * (1 - (u - 1) * ZetaAsymptotics.termTSum u)
  have hF : AnalyticOnNhd Real F (Ioi 0) := by
    intro u hu
    exact poleFactor_differentiable.analyticAt (u : Complex) |>.re_ofReal
  have hG : AnalyticOnNhd Real G (Ioi 0) := by
    intro u hu
    have hTerm := termTSum_analyticAt_of_pos hu
    have hSub : AnalyticAt Real (fun v : Real => v - 1) u :=
      analyticAt_id.sub analyticAt_const
    have hProduct : AnalyticAt Real
        (fun v : Real => (v - 1) * ZetaAsymptotics.termTSum v) u :=
      hSub.mul hTerm
    have hBracket : AnalyticAt Real
        (fun v : Real => 1 -
          (v - 1) * ZetaAsymptotics.termTSum v) u :=
      analyticAt_const.sub hProduct
    have hReal : AnalyticAt Real
        (fun v : Real => v *
          (1 - (v - 1) * ZetaAsymptotics.termTSum v)) u :=
      analyticAt_id.mul hBracket
    exact hReal
  have hEqNhd : Filter.EventuallyEq (nhds (2 : Real)) F G := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 : Real) < 2)] with u hu
    have hIdentity := poleFactor_eq_termTSum_of_one_lt hu
    simpa [F, G] using congrArg Complex.re hIdentity
  have hEqOn : EqOn F G (Ioi 0) :=
    hF.eqOn_of_preconnected_of_eventuallyEq
      hG (convex_Ioi (0 : Real)).isPreconnected (by norm_num) hEqNhd
  exact hEqOn hs

theorem poleFactor_ne_zero_of_mem_Ioo_zero_one
    {s : Real} (hs : Membership.mem (Ioo (0 : Real) 1) s) :
    Not (poleFactor (s : Complex) = 0) := by
  have hIdentity := poleFactor_re_eq_termTSum_of_pos hs.1
  have hTermNonneg := termTSum_nonneg hs.1
  have hCoefficientNonpos :
      (s - 1) * ZetaAsymptotics.termTSum s <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.2.le) hTermNonneg
  have hRealPos :
      0 < s * (1 - (s - 1) * ZetaAsymptotics.termTSum s) := by
    apply mul_pos hs.1
    linarith
  intro hZero
  have hReZero : (poleFactor (s : Complex)).re = 0 := by
    rw [hZero]
    exact Complex.zero_re
  rw [hIdentity] at hReZero
  linarith

theorem real_ne_zero_of_mem_Ioo_zero_one
    {s : Real} (hs : Membership.mem (Ioo (0 : Real) 1) s) :
    Not (riemannZeta (s : Complex) = 0) := by
  have hsOne : Not ((s : Complex) = 1) := by
    exact Complex.ofReal_ne_one.mpr (ne_of_lt hs.2)
  rw [eq_poleFactor_div hsOne]
  exact div_ne_zero
    (poleFactor_ne_zero_of_mem_Ioo_zero_one hs)
    (sub_ne_zero.mpr hsOne)

theorem poleFactor_ne_zero_of_pos_real
    {s : Real} (hs : 0 < s) :
    Not (poleFactor (s : Complex) = 0) := by
  by_cases hsLt : s < 1
  case pos =>
    exact poleFactor_ne_zero_of_mem_Ioo_zero_one
      (And.intro hs hsLt)
  case neg =>
    by_cases hsEq : s = 1
    case pos =>
      subst s
      simp
    case neg =>
      have hsGt : 1 < s := lt_of_le_of_ne (not_lt.mp hsLt) (Ne.symm hsEq)
      have hsOne : Not ((s : Complex) = 1) :=
        Complex.ofReal_ne_one.mpr (ne_of_gt hsGt)
      have hZeta : Not (riemannZeta (s : Complex) = 0) :=
        riemannZeta_ne_zero_of_one_lt_re (by simpa using hsGt)
      exact poleFactor_ne_zero_of_riemannZeta_ne_zero hsOne hZeta
/-- The Riemann zeta function is nonzero at every positive real argument. -/
theorem real_ne_zero_of_pos {s : Real} (hs : 0 < s) :
    Not (riemannZeta (s : Complex) = 0) := by
  by_cases hsLt : s < 1
  case pos =>
    exact real_ne_zero_of_mem_Ioo_zero_one (And.intro hs hsLt)
  case neg =>
    by_cases hsEq : s = 1
    case pos =>
      subst s
      exact riemannZeta_one_ne_zero
    case neg =>
      have hsGt : 1 < s := lt_of_le_of_ne (not_lt.mp hsLt) (Ne.symm hsEq)
      exact riemannZeta_ne_zero_of_one_lt_re (by simpa using hsGt)

end

end RiemannZeta
