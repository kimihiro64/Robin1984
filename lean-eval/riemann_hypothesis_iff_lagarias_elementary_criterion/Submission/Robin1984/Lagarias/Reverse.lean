import Submission.Robin1984.Lagarias.Upper
import Submission.Robin1984.NicolasLandau.NicolasLandauRobinBridge

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jeffrey C. Lagarias (2001), converse implication,
  using the Robin--Nicolas--Landau oscillation theorem already formalized
  in this repository.
- Formalization note: The logarithmic lcm margin supplies the hard oscillation;
  Lagarias' Lemma 3.2 supplies the little-o comparison.
- PROVENANCE-END
-/

/-! # The converse Lagarias implication -/

namespace Robin1984

open Asymptotics Filter

noncomputable section

/-- The normalized Lagarias error on a floor-sampled lcm packet. -/
def lcmLagariasErrorFloor (x : Real) : Real :=
  24 / Real.log (Nat.lcmUpto (Nat.floor x) : Real)

/-- The reciprocal lcm-height error is negligible on every Nicolas scale
with exponent below one half. -/
theorem lcmLagariasErrorFloor_isLittleO_rpow_neg
    {b : Real} (hb : b < 1 / 2) :
    IsLittleO atTop lcmLagariasErrorFloor
      (fun x : Real => x ^ (-b)) := by
  have hbOne : b < 1 := lt_trans hb (by norm_num)
  have hLogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNatBigO : IsBigO (atTop : Filter Nat)
      (fun P : Nat => 24 / Real.log (Nat.lcmUpto P : Real))
      (fun P : Nat => (P : Real) ^ (-(1 : Real))) := by
    apply IsBigO.of_bound (48 / Real.log 2)
    filter_upwards [eventually_log_two_div_two_mul_le_chebyshevTheta_nat,
      Filter.eventually_atTop.2 (Exists.intro 1 (fun _ h => h))]
        with P hTheta hPOne
    have hPPos : 0 < (P : Real) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hPOne)
    have hCoeffPos : 0 < (Real.log 2 / 2) * (P : Real) := by positivity
    have hThetaPsi : Chebyshev.theta (P : Real) <=
        Chebyshev.psi (P : Real) := Chebyshev.theta_le_psi (P : Real)
    have hLogLower : (Real.log 2 / 2) * (P : Real) <=
        Real.log (Nat.lcmUpto P : Real) := by
      rw [<- Chebyshev.psi_eq_log_lcmUpto P]
      exact hTheta.trans hThetaPsi
    have hLogPos : 0 < Real.log (Nat.lcmUpto P : Real) :=
      lt_of_lt_of_le hCoeffPos hLogLower
    have hErrorNonneg : 0 <= 24 / Real.log (Nat.lcmUpto P : Real) := by
      positivity
    have hKernelPos : 0 < (P : Real) ^ (-(1 : Real)) :=
      Real.rpow_pos_of_pos hPPos _
    have hBound :
        24 / Real.log (Nat.lcmUpto P : Real) <=
          (48 / Real.log 2) * (P : Real) ^ (-(1 : Real)) := by
      have hStep :
          24 / Real.log (Nat.lcmUpto P : Real) <=
            24 / ((Real.log 2 / 2) * (P : Real)) :=
        div_le_div_of_nonneg_left (by norm_num) hCoeffPos hLogLower
      calc
        24 / Real.log (Nat.lcmUpto P : Real) <=
            24 / ((Real.log 2 / 2) * (P : Real)) := hStep
        _ = (48 / Real.log 2) * (P : Real) ^ (-(1 : Real)) := by
          rw [Real.rpow_neg_one]
          field_simp
          ring
    simpa only [Real.norm_eq_abs, abs_of_nonneg hErrorNonneg,
      abs_of_pos hKernelPos, mul_assoc] using hBound
  have hNatLittleO : IsLittleO (atTop : Filter Nat)
      (fun P : Nat => 24 / Real.log (Nat.lcmUpto P : Real))
      (fun P : Nat => (P : Real) ^ (-b)) :=
    hNatBigO.trans_isLittleO
      ((rpow_neg_one_isLittleO_rpow_neg hbOne).natCast_atTop)
  have hComposed : IsLittleO atTop lcmLagariasErrorFloor
      (fun x : Real => (Nat.floor x : Real) ^ (-b)) := by
    exact hNatLittleO.comp_tendsto tendsto_nat_floor_atTop
  have hFloorNonneg : Filter.Eventually
      (fun x : Real => 0 <= (Nat.floor x : Real)) atTop :=
    Filter.Eventually.of_forall (fun _ => by positivity)
  have hRealNonneg : Filter.Eventually (fun x : Real => 0 <= x) atTop :=
    eventually_ge_atTop 0
  have hScaleTheta : IsTheta atTop
      (fun x : Real => (Nat.floor x : Real) ^ (-b))
      (fun x : Real => x ^ (-b)) :=
    Asymptotics.isEquivalent_nat_floor.isTheta.rpow
      hFloorNonneg hRealNonneg
  exact hComposed.trans_isBigO hScaleTheta.1

/-- A positive logarithmic Robin margin is no larger than the corresponding
additive abundancy excess. -/
theorem lcmRobinLogMargin_le_abundancy_sub_robinBoundRatio
    {P : Nat} (hCut : 5040 < Nat.lcmUpto P)
    (hMargin : 0 <= lcmRobinLogMargin P) :
    lcmRobinLogMargin P <=
      abundancy (Nat.lcmUpto P) - robinBoundRatio (Nat.lcmUpto P) := by
  let n := Nat.lcmUpto P
  have hnPos : 0 < n := Nat.lcmUpto_pos P
  have hApos : 0 < abundancy n := abundancy_pos hnPos
  have hRpos : 0 < robinBoundRatio n :=
    robinBoundRatio_pos_of_cutoff hCut
  have hLogR := log_robinBoundRatio_eq_of_cutoff hCut
  have hMarginEq :
      lcmRobinLogMargin P =
        Real.log (abundancy n) - Real.log (robinBoundRatio n) := by
    unfold lcmRobinLogMargin
    rw [hLogR]
    ring
  have hExpEq :
      Real.exp (lcmRobinLogMargin P) =
        abundancy n / robinBoundRatio n := by
    rw [hMarginEq, Real.exp_sub, Real.exp_log hApos, Real.exp_log hRpos]
  have hGammaNonneg : (0 : Real) <= Real.eulerMascheroniConstant :=
    (by norm_num : (0 : Real) <= 57721 / 100000).trans
      robin_euler_constant_lower
  have hExpGammaOne : 1 <= Real.exp Real.eulerMascheroniConstant := by
    simpa using Real.exp_le_exp.mpr hGammaNonneg
  have hnRealPos : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
  have hExpThree : Real.exp 3 < (n : Real) := by
    have hExpOnePos : 0 < Real.exp 1 := Real.exp_pos 1
    have hExpOneLt : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hCube : Real.exp 1 * Real.exp 1 * Real.exp 1 < 27 := by nlinarith
    rw [show (3 : Real) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    exact hCube.trans_le (by exact_mod_cast (by omega : 27 <= n))
  have hLogThree : 3 < Real.log (n : Real) :=
    (Real.lt_log_iff_exp_lt hnRealPos).2 hExpThree
  have hLogPos : 0 < Real.log (n : Real) := lt_trans (by norm_num) hLogThree
  have hLogLogOne : 1 < Real.log (Real.log (n : Real)) := by
    apply (Real.lt_log_iff_exp_lt hLogPos).2
    exact Real.exp_one_lt_three.trans hLogThree
  have hROne : 1 <= robinBoundRatio n := by
    unfold robinBoundRatio
    have hMul := mul_le_mul hExpGammaOne hLogLogOne.le
      (by norm_num) (Real.exp_pos _).le
    simpa using hMul
  have hOneExp :
      1 + lcmRobinLogMargin P <=
        Real.exp (lcmRobinLogMargin P) := by
    simpa only [add_comm] using Real.add_one_le_exp (lcmRobinLogMargin P)
  have hScaled := mul_le_mul_of_nonneg_left hOneExp hRpos.le
  rw [hExpEq] at hScaled
  have hCancel :
      robinBoundRatio n *
          (abundancy n / robinBoundRatio n) = abundancy n := by
    field_simp
  rw [hCancel] at hScaled
  have hMarginScaled :
      lcmRobinLogMargin P <=
        robinBoundRatio n * lcmRobinLogMargin P :=
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right hROne hMargin
  ring_nf at hScaled
  linarith only [hScaled, hMarginScaled]

/-- Lagarias' criterion forces RH, using the repository's established
Robin--Nicolas--Landau oscillation theorem. -/
theorem riemannHypothesis_of_lagariasElementaryCriterion
    (hCriterion : LagariasElementaryCriterion) : RiemannHypothesis := by
  by_contra hNotRH
  choose b hbPos hbHalf hJ using
    exists_nicolasJ_omegaMinus_of_not_riemannHypothesis hNotRH
  have hbOne : b < 1 := lt_trans hbHalf (by norm_num)
  have hNicolas : AtTopOmegaMinus nicolasLogMertensOscillation
      (fun x : Real => x ^ (-b)) :=
    nicolasLogMertensOscillation_omegaMinus_of_J_proved_upper hbOne hJ
  have hMarginOmega : AtTopOmegaPlus lcmRobinLogMarginFloor
      (fun x : Real => x ^ (-b)) :=
    lcmRobinLogMarginFloor_atTopOmegaPlus_of_nicolasOmegaMinus
      hbHalf hNicolas
  have hError : IsLittleO atTop lcmLagariasErrorFloor
      (fun x : Real => x ^ (-b)) :=
    lcmLagariasErrorFloor_isLittleO_rpow_neg hbHalf
  have hScalePos : Filter.Eventually (fun x : Real => 0 < x ^ (-b)) atTop := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    exact Real.rpow_pos_of_pos hx _
  have hDiffOmega : AtTopOmegaPlus
      (fun x => lcmRobinLogMarginFloor x - lcmLagariasErrorFloor x)
      (fun x : Real => x ^ (-b)) := by
    simpa only [sub_eq_add_neg] using
      hMarginOmega.add_isLittleO hScalePos hError.neg_left
  have hEventualUpper : Filter.Eventually
      (fun x : Real =>
        lcmRobinLogMarginFloor x <= lcmLagariasErrorFloor x) atTop := by
    filter_upwards [eventually_ge_atTop (5041 : Real)] with x hx
    let P := Nat.floor x
    let n := Nat.lcmUpto P
    have hxPos : 0 <= x := le_trans (by norm_num) hx
    have hP : 5041 <= P := (Nat.le_floor_iff hxPos).2 hx
    have hPOne : 1 <= P := by omega
    have hPn : P <= n := frontier_le_lcmUpto hPOne
    have hCut : 5040 < n := by omega
    have hTwenty : 20 <= n := by omega
    have hnPos : 0 < n := Nat.lcmUpto_pos P
    have hPoint := hCriterion n hnPos
    have hUpper := lagarias_upper_bound hTwenty
    have hNumerator := hPoint.trans hUpper
    have hnRealPos : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
    have hRatio :
        abundancy n <= robinBoundRatio n +
          24 / Real.log (n : Real) := by
      have hDiv := div_le_div_of_nonneg_right hNumerator hnRealPos.le
      unfold abundancy robinBoundRatio Core.sigmaOneNat
      calc
        ((ArithmeticFunction.sigma 1 n : Nat) : Real) / (n : Real) <=
            (Real.exp Real.eulerMascheroniConstant * (n : Real) *
                Real.log (Real.log (n : Real)) +
              24 * (n : Real) / Real.log (n : Real)) / (n : Real) := hDiv
        _ = Real.exp Real.eulerMascheroniConstant *
              Real.log (Real.log (n : Real)) +
            24 / Real.log (n : Real) := by
          field_simp [hnRealPos.ne']
    by_cases hMargin : 0 <= lcmRobinLogMargin P
    . have hMarginBound :
          lcmRobinLogMargin P <=
            abundancy n - robinBoundRatio n :=
        lcmRobinLogMargin_le_abundancy_sub_robinBoundRatio
          hCut hMargin
      unfold lcmRobinLogMarginFloor lcmLagariasErrorFloor
      dsimp [P, n] at hRatio hMarginBound
      linarith
    . have hStrict : lcmRobinLogMargin P < 0 := lt_of_not_ge hMargin
      have hLogPos : 0 < Real.log (n : Real) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hErrorNonneg : 0 <= 24 / Real.log (n : Real) := by positivity
      unfold lcmRobinLogMarginFloor lcmLagariasErrorFloor
      dsimp [P, n] at hStrict hErrorNonneg
      linarith
  choose c hc hLarge using hDiffOmega
  choose Y hY using eventually_atTop.mp hEventualUpper
  choose x hx hExcursion using hLarge (max Y 1)
  have hxY : Y <= x := le_trans (le_max_left Y 1) hx
  have hxOne : (1 : Real) <= x := le_trans (le_max_right Y 1) hx
  have hUpperX := hY x hxY
  have hScaleX : 0 < x ^ (-b) := by
    have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hxOne
    exact Real.rpow_pos_of_pos hxPos _
  change c * x ^ (-b) <=
    lcmRobinLogMarginFloor x - lcmLagariasErrorFloor x at hExcursion
  have hCScalePos : 0 < c * x ^ (-b) := mul_pos hc hScaleX
  linarith only [hExcursion, hUpperX, hCScalePos]

end

end Robin1984
