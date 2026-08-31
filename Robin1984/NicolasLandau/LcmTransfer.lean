import Robin1984.Analytic.FactorizationEulerReserve
import Robin1984.ColossallyAbundant.LCMPrimeTowerBounds
import Robin1984.Equivalence.OmegaScaleTransfer
import Robin1984.Helpers.LCMPrimeSupport
import Robin1984.NicolasLandau.NicolasFunction

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# LCM transfer from Nicolas's oscillation to Robin's inequality

This file keeps the complete prime-power correction of `Nat.lcmUpto P`.
The support is split by the actual `lcmUpto` exponent: deep primes pay the
uniform reciprocal-frontier bound, while exponent-one primes pay the complete
reciprocal-square tail.  No prime or tower layer is omitted.
-/

namespace Robin1984

open Asymptotics Filter

noncomputable section

/-- The complete tower correction of `lcmUpto P` is bounded by a square-root
split with no prime-counting estimate. -/
theorem factorizationTowerReserve_lcmUpto_le_natSqrt_split
    {P : Nat} (hP : 0 < P) (hSqrt : 0 < Nat.sqrt P) :
    factorizationTowerReserve (Nat.lcmUpto P) <=
      (((Nat.sqrt P + 1 : Nat) : Real) * (2 / (P : Real)) +
        2 * (1 / (Nat.sqrt P : Real))) := by
  classical
  let d := (Nat.lcmUpto P).factorization.support
  let deep := d.filter (fun p => 2 <= (Nat.lcmUpto P).factorization p)
  let shallow := d.filter (fun p =>
    Not (2 <= (Nat.lcmUpto P).factorization p))
  let term := fun p => primeTowerTopCorrection p
    ((Nat.lcmUpto P).factorization p)
  have hReserve :
      factorizationTowerReserve (Nat.lcmUpto P) = d.sum term := by
    unfold factorizationTowerReserve
    rw [Finsupp.sum]
  have hSplit : d.sum term = deep.sum term + shallow.sum term := by
    dsimp [deep, shallow]
    simpa only using
      (Finset.sum_filter_add_sum_filter_not d
        (fun p => 2 <= (Nat.lcmUpto P).factorization p) term).symm
  have hDeepPoint : forall p, Membership.mem deep p ->
      term p <= 2 / (P : Real) := by
    intro p hpDeep
    have hpSupport : Membership.mem d p := (Finset.mem_filter.mp hpDeep).1
    have hpPrime : Nat.Prime p := by
      have hpSet : Membership.mem (Robin1984.primesUpToSet P) p := by
        rw [<- factorization_lcmUpto_support_eq_primesUpToSet P]
        exact hpSupport
      exact (Finset.mem_filter.mp hpSet).2
    exact primeTowerTopCorrection_lcm_le_two_div_frontier hP hpPrime
  have hDeepRaw : deep.sum term <=
      (deep.card : Real) * (2 / (P : Real)) := by
    calc
      deep.sum term <= deep.sum (fun _p => 2 / (P : Real)) :=
        Finset.sum_le_sum hDeepPoint
      _ = (deep.card : Real) * (2 / (P : Real)) := by simp
  have hDeepSubset : forall p, Membership.mem deep p ->
      Membership.mem (Finset.range (Nat.sqrt P + 1)) p := by
    intro p hpDeep
    have hpSupport : Membership.mem d p := (Finset.mem_filter.mp hpDeep).1
    have hpDepth : 2 <= (Nat.lcmUpto P).factorization p :=
      (Finset.mem_filter.mp hpDeep).2
    have hpPrime : Nat.Prime p := by
      have hpSet : Membership.mem (Robin1984.primesUpToSet P) p := by
        rw [<- factorization_lcmUpto_support_eq_primesUpToSet P]
        exact hpSupport
      exact (Finset.mem_filter.mp hpSet).2
    have hpSq : p * p <= P := by
      apply Nat.not_lt.mp
      intro hPSq
      have hpOne := (factorization_lcmUpto_le_one_iff_lt_sq hpPrime).2
        (by simpa [pow_two] using hPSq)
      omega
    have hpRoot : p <= Nat.sqrt P := (Nat.le_sqrt).2 hpSq
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpRoot)
  have hDeepCard : deep.card <= Nat.sqrt P + 1 := by
    simpa using Finset.card_le_card hDeepSubset
  have hDeep : deep.sum term <=
      (((Nat.sqrt P + 1 : Nat) : Real) * (2 / (P : Real))) := by
    have hCardReal : (deep.card : Real) <=
        ((Nat.sqrt P + 1 : Nat) : Real) := by
      exact_mod_cast hDeepCard
    exact hDeepRaw.trans
      (mul_le_mul_of_nonneg_right hCardReal (by positivity))
  have hShallowPoint : forall p, Membership.mem shallow p ->
      term p <= 2 * (1 / (p : Real)) ^ 2 := by
    intro p hpShallow
    have hpSupport : Membership.mem d p := (Finset.mem_filter.mp hpShallow).1
    have hpNotDeep := (Finset.mem_filter.mp hpShallow).2
    have hpPrime : Nat.Prime p := by
      have hpSet : Membership.mem (Robin1984.primesUpToSet P) p := by
        rw [<- factorization_lcmUpto_support_eq_primesUpToSet P]
        exact hpSupport
      exact (Finset.mem_filter.mp hpSet).2
    have hpNonzero : Not ((Nat.lcmUpto P).factorization p = 0) :=
      Finsupp.mem_support_iff.mp hpSupport
    have hpOne : (Nat.lcmUpto P).factorization p = 1 := by omega
    dsimp [term]
    rw [hpOne]
    simpa [one_div] using
      (primeTowerTopCorrection_le_two_inv_pow_succ (p := p) (k := 1) hpPrime)
  have hShallowSubset : forall p, Membership.mem shallow p ->
      Membership.mem (Finset.Ioc (Nat.sqrt P) P) p := by
    intro p hpShallow
    have hpSupport : Membership.mem d p := (Finset.mem_filter.mp hpShallow).1
    have hpNotDeep := (Finset.mem_filter.mp hpShallow).2
    have hpSet : Membership.mem (Robin1984.primesUpToSet P) p := by
      rw [<- factorization_lcmUpto_support_eq_primesUpToSet P]
      exact hpSupport
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hpSet).2
    have hpLeP : p <= P := by
      have hpRange := (Finset.mem_filter.mp hpSet).1
      exact Nat.le_of_lt_succ (by simpa using hpRange)
    have hpOne : (Nat.lcmUpto P).factorization p <= 1 := by omega
    have hPSq : P < p ^ 2 :=
      (factorization_lcmUpto_le_one_iff_lt_sq hpPrime).1 hpOne
    have hpRootLt : Nat.sqrt P < p := by
      by_contra hNot
      have hpLeRoot : p <= Nat.sqrt P := Nat.le_of_not_gt hNot
      have hpSqLe : p ^ 2 <= (Nat.sqrt P) ^ 2 :=
        pow_le_pow_left' hpLeRoot 2
      exact (not_lt_of_ge (hpSqLe.trans (Nat.sqrt_le' P))) hPSq
    exact Finset.mem_Ioc.mpr (And.intro hpRootLt hpLeP)
  have hShallowRaw : shallow.sum term <=
      2 * (Finset.Ioc (Nat.sqrt P) P).sum
        (fun p => 1 / ((p : Real) ^ 2)) := by
    calc
      shallow.sum term <= shallow.sum (fun p => 2 * (1 / (p : Real)) ^ 2) :=
        Finset.sum_le_sum hShallowPoint
      _ = 2 * shallow.sum (fun p => 1 / ((p : Real) ^ 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _hp
        simp only [one_div, inv_pow]
      _ <= 2 * (Finset.Ioc (Nat.sqrt P) P).sum
          (fun p => 1 / ((p : Real) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg hShallowSubset
          (by intro p _hp _hNot; positivity)
  have hRootLeP : Nat.sqrt P <= P := by
    exact (Nat.sqrt_le_self P)
  have hSquareTail :
      (Finset.Ioc (Nat.sqrt P) P).sum
          (fun p => 1 / ((p : Real) ^ 2)) <=
        1 / (Nat.sqrt P : Real) - 1 / (P : Real) :=
    by
      have hRaw :
          (Finset.Ioc (Nat.sqrt P) P).sum
              (fun p => Inv.inv ((p : Real) ^ 2)) <=
            Inv.inv (Nat.sqrt P : Real) - Inv.inv (P : Real) :=
        sum_Ioc_inv_sq_le_sub hSqrt.ne' hRootLeP
      simpa only [one_div] using hRaw
  have hShallow : shallow.sum term <=
      2 * (1 / (Nat.sqrt P : Real)) := by
    calc
      shallow.sum term <=
          2 * (1 / (Nat.sqrt P : Real) - 1 / (P : Real)) :=
        hShallowRaw.trans
          (mul_le_mul_of_nonneg_left hSquareTail (by norm_num))
      _ <= 2 * (1 / (Nat.sqrt P : Real)) := by
        have hPInvNonneg : 0 <= 1 / (P : Real) := by positivity
        linarith
  rw [hReserve, hSplit]
  exact add_le_add hDeep hShallow

/-- A uniform square-root bound for the complete `lcmUpto` tower correction. -/
theorem factorizationTowerReserve_lcmUpto_le_eight_mul_rpow
    {P : Nat} (hP : 4 <= P) :
    factorizationTowerReserve (Nat.lcmUpto P) <=
      8 * (P : Real) ^ (-(1 / 2 : Real)) := by
  have hPPos : 0 < P := by omega
  have hRootPosNat : 0 < Nat.sqrt P := Nat.sqrt_pos.2 (by omega)
  have hSplit := factorizationTowerReserve_lcmUpto_le_natSqrt_split
    hPPos hRootPosNat
  let c : Real := (Nat.sqrt P : Real)
  let s : Real := Real.sqrt (P : Real)
  have hcPos : 0 < c := by
    dsimp [c]
    exact_mod_cast hRootPosNat
  have hcOne : 1 <= c := by
    dsimp [c]
    exact_mod_cast hRootPosNat
  have hPRealPos : 0 < (P : Real) := by exact_mod_cast hPPos
  have hsPos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hPRealPos
  have hcLeS : c <= s := by
    apply Real.le_sqrt_of_sq_le
    dsimp [c]
    exact_mod_cast Nat.sqrt_le' P
  have hsLtCOne : s < c + 1 := by
    apply (Real.sqrt_lt' (by positivity : 0 < c + 1)).2
    dsimp [c, s]
    exact_mod_cast Nat.lt_succ_sqrt' P
  have hcOneLeTwoS : c + 1 <= 2 * s := by
    nlinarith
  have hsLeTwoC : s <= 2 * c := by
    nlinarith
  have hPEq : (P : Real) = s ^ 2 := by
    dsimp [s]
    exact (Real.sq_sqrt hPRealPos.le).symm
  have hFirst :
      (((Nat.sqrt P + 1 : Nat) : Real) * (2 / (P : Real))) <=
        4 / s := by
    have hCast : ((Nat.sqrt P + 1 : Nat) : Real) = c + 1 := by
      simp [c]
    rw [hCast]
    calc
      (c + 1) * (2 / (P : Real)) = (2 * (c + 1)) / (P : Real) := by ring
      _ <= 4 / s := by
        have hMul := mul_le_mul_of_nonneg_right hcOneLeTwoS hsPos.le
        have hCross : 2 * (c + 1) * s <= 4 * (P : Real) := by
          rw [hPEq]
          nlinarith
        have hDenPos : 0 < (P : Real) * s := mul_pos hPRealPos hsPos
        calc
          (2 * (c + 1)) / (P : Real) =
              (2 * (c + 1) * s) / ((P : Real) * s) := by
            field_simp [ne_of_gt hPRealPos, ne_of_gt hsPos]
          _ <= (4 * (P : Real)) / ((P : Real) * s) :=
            (div_le_div_iff_of_pos_right hDenPos).2 hCross
          _ = 4 / s := by
            field_simp [ne_of_gt hPRealPos, ne_of_gt hsPos]
  have hSecond : 2 * (1 / (Nat.sqrt P : Real)) <= 4 / s := by
    change 2 * (1 / c) <= 4 / s
    have hTwoDiv : 2 * (1 / c) = 2 / c := by ring
    rw [hTwoDiv]
    have hCross : 2 * s <= 4 * c := by nlinarith
    have hDenPos : 0 < c * s := mul_pos hcPos hsPos
    calc
      2 / c = (2 * s) / (c * s) := by
        field_simp [ne_of_gt hcPos, ne_of_gt hsPos]
      _ <= (4 * c) / (c * s) :=
        (div_le_div_iff_of_pos_right hDenPos).2 hCross
      _ = 4 / s := by
        field_simp [ne_of_gt hcPos, ne_of_gt hsPos]
  have hEightSqrt : factorizationTowerReserve (Nat.lcmUpto P) <= 8 / s := by
    calc
      factorizationTowerReserve (Nat.lcmUpto P) <=
          (((Nat.sqrt P + 1 : Nat) : Real) * (2 / (P : Real)) +
            2 * (1 / (Nat.sqrt P : Real))) := hSplit
      _ <= 4 / s + 4 / s := add_le_add hFirst hSecond
      _ = 8 / s := by ring
  have hScale : 8 / s = 8 * (P : Real) ^ (-(1 / 2 : Real)) := by
    dsimp [s]
    rw [Real.sqrt_eq_rpow]
    rw [Real.rpow_neg hPRealPos.le]
    simp only [div_eq_mul_inv]
  rw [hScale] at hEightSqrt
  exact hEightSqrt

/-- On natural frontiers, the complete `lcmUpto` tower correction is
`O(P^(-1/2))`. -/
theorem factorizationTowerReserve_lcmUpto_isBigO_rpow_neg_oneHalf :
    Asymptotics.IsBigO (Filter.atTop : Filter Nat)
      (fun P : Nat => factorizationTowerReserve (Nat.lcmUpto P))
      (fun P : Nat => (P : Real) ^ (-(1 / 2 : Real))) := by
  apply Asymptotics.IsBigO.of_bound 8
  filter_upwards [Filter.eventually_atTop.2 (Exists.intro 4 (fun _ h => h))]
    with P hP
  have hBound := factorizationTowerReserve_lcmUpto_le_eight_mul_rpow hP
  have hReserveNonneg := factorizationTowerReserve_nonneg (Nat.lcmUpto P)
  have hPPos : 0 < P := by omega
  have hScalePos : 0 < (P : Real) ^ (-(1 / 2 : Real)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hPPos) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hReserveNonneg,
    abs_of_pos hScalePos] using hBound

/-- The unconditional elementary Chebyshev lower bound gives an eventual
positive linear lower bound for `theta` on natural frontiers. -/
theorem eventually_log_two_div_two_mul_le_chebyshevTheta_nat :
    Filter.Eventually
      (fun P : Nat =>
        (Real.log 2 / 2) * (P : Real) <= Chebyshev.theta (P : Real))
      Filter.atTop := by
  have hLogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hEpsPos : 0 < Real.log 2 / 8 := div_pos hLogTwoPos (by norm_num)
  have hLogLinear := Real.isLittleO_log_id_atTop.natCast_atTop.bound hEpsPos
  have hLogSqrt :=
    (isLittleO_log_rpow_atTop
      (by norm_num : (0 : Real) < 1 / 2)).natCast_atTop.bound hEpsPos
  filter_upwards [hLogLinear, hLogSqrt,
    Filter.eventually_atTop.2 (Exists.intro 8 (fun _ h => h))]
      with P hLinear hSqrt hPEight
  have hPPos : 0 < P := by omega
  have hPRealPos : 0 < (P : Real) := by exact_mod_cast hPPos
  have hPOne : (1 : Real) <= (P : Real) := by exact_mod_cast hPPos
  have hLogPNonneg : 0 <= Real.log (P : Real) := Real.log_nonneg hPOne
  have hSqrtPPos : 0 < Real.sqrt (P : Real) := Real.sqrt_pos.2 hPRealPos
  have hLinear' :
      Real.log (P : Real) <= (Real.log 2 / 8) * (P : Real) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hLogPNonneg,
      abs_of_pos hPRealPos, id_eq] using hLinear
  have hSqrt' :
      Real.log (P : Real) <=
        (Real.log 2 / 8) * Real.sqrt (P : Real) := by
    have hRpowPos : 0 < (P : Real) ^ (1 / 2 : Real) :=
      Real.rpow_pos_of_pos hPRealPos _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hLogPNonneg,
      abs_of_pos hRpowPos, Real.sqrt_eq_rpow] using hSqrt
  have hPPlusLe : ((P + 1 : Nat) : Real) <= 2 * (P : Real) := by
    exact_mod_cast (by omega : P + 1 <= 2 * P)
  have hLogPPlus :
      Real.log ((P + 1 : Nat) : Real) <=
        Real.log 2 + Real.log (P : Real) := by
    calc
      Real.log ((P + 1 : Nat) : Real) <= Real.log (2 * (P : Real)) :=
        Real.log_le_log (by positivity) hPPlusLe
      _ = Real.log 2 + Real.log (P : Real) := by
        rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hPRealPos.ne']
  have hConst : Real.log 2 <= (Real.log 2 / 8) * (P : Real) := by
    have hEightReal : (8 : Real) <= (P : Real) := by exact_mod_cast hPEight
    nlinarith
  have hLogPPlusQuarter :
      Real.log ((P + 1 : Nat) : Real) <=
        (Real.log 2 / 4) * (P : Real) := by
    linarith
  have hSqrtLogQuarter :
      2 * Real.sqrt (P : Real) * Real.log (P : Real) <=
        (Real.log 2 / 4) * (P : Real) := by
    have hMul := mul_le_mul_of_nonneg_left hSqrt'
      (mul_nonneg (by norm_num : (0 : Real) <= 2) hSqrtPPos.le)
    have hSq : (Real.sqrt (P : Real)) ^ 2 = (P : Real) :=
      Real.sq_sqrt hPRealPos.le
    nlinarith
  have hTheta := Chebyshev.theta_ge P
  rw [Nat.cast_add, Nat.cast_one] at hLogPPlusQuarter
  nlinarith

/-- The exact logarithmic height loss incurred when `log (lcmUpto P)` is
`psi(P)` rather than `theta(P)`. -/
def lcmHeightLoss (P : Nat) : Real :=
  Real.log (Real.log (Chebyshev.psi (P : Real))) -
    Real.log (Real.log (Chebyshev.theta (P : Real)))

/-- Eventually the complete lcm height loss is nonnegative and bounded by the
elementary `log(P)/sqrt(P)` scale. -/
theorem eventually_lcmHeightLoss_nonneg_and_le_log_mul_rpow :
    Filter.Eventually
      (fun P : Nat =>
        0 <= lcmHeightLoss P /\
          lcmHeightLoss P <=
            (4 / Real.log 2) * Real.log (P : Real) *
              (P : Real) ^ (-(1 / 2 : Real)))
      Filter.atTop := by
  have hLogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCoeffPos : 0 < Real.log 2 / 2 := div_pos hLogTwoPos (by norm_num)
  have hLinearTendsto : Filter.Tendsto
      (fun P : Nat => (Real.log 2 / 2) * (P : Real))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hCoeffPos
  have hAboveExp : Filter.Eventually
      (fun P : Nat => Real.exp 1 < (Real.log 2 / 2) * (P : Real))
      Filter.atTop := hLinearTendsto.eventually_gt_atTop (Real.exp 1)
  filter_upwards [eventually_log_two_div_two_mul_le_chebyshevTheta_nat,
    hAboveExp, Filter.eventually_atTop.2 (Exists.intro 1 (fun _ h => h))]
      with P hThetaLinear hCoeffAbove hPOne
  let th : Real := Chebyshev.theta (P : Real)
  let ps : Real := Chebyshev.psi (P : Real)
  have hPRealOne : (1 : Real) <= (P : Real) := by exact_mod_cast hPOne
  have hPRealPos : 0 < (P : Real) := lt_of_lt_of_le zero_lt_one hPRealOne
  have hLogPNonneg : 0 <= Real.log (P : Real) := Real.log_nonneg hPRealOne
  have hThetaLower : (Real.log 2 / 2) * (P : Real) <= th := by
    exact hThetaLinear
  have hThetaExp : Real.exp 1 < th := lt_of_lt_of_le hCoeffAbove hThetaLower
  have hThetaPos : 0 < th := lt_trans (Real.exp_pos 1) hThetaExp
  have hLogThetaOne : 1 < Real.log th :=
    (Real.lt_log_iff_exp_lt hThetaPos).2 hThetaExp
  have hLogThetaPos : 0 < Real.log th := lt_trans zero_lt_one hLogThetaOne
  have hThetaPsi : th <= ps := by
    exact Chebyshev.theta_le_psi (P : Real)
  have hPsiPos : 0 < ps := lt_of_lt_of_le hThetaPos hThetaPsi
  have hLogThetaPsi : Real.log th <= Real.log ps :=
    Real.log_le_log hThetaPos hThetaPsi
  have hLogPsiPos : 0 < Real.log ps := lt_of_lt_of_le hLogThetaPos hLogThetaPsi
  have hHeightNonneg : 0 <= lcmHeightLoss P := by
    unfold lcmHeightLoss
    exact sub_nonneg.mpr (Real.log_le_log hLogThetaPos hLogThetaPsi)
  have hOuterRatioPos : 0 < Real.log ps / Real.log th :=
    div_pos hLogPsiPos hLogThetaPos
  have hOuter := Real.log_le_sub_one_of_pos hOuterRatioPos
  have hOuterLogEq :
      Real.log (Real.log ps / Real.log th) = lcmHeightLoss P := by
    rw [Real.log_div hLogPsiPos.ne' hLogThetaPos.ne']
    rfl
  have hOuterSubEq :
      Real.log ps / Real.log th - 1 =
        (Real.log ps - Real.log th) / Real.log th := by
    field_simp [hLogThetaPos.ne']
  rw [hOuterLogEq, hOuterSubEq] at hOuter
  have hLogDiffNonneg : 0 <= Real.log ps - Real.log th :=
    sub_nonneg.mpr hLogThetaPsi
  have hHeightLeLogDiff :
      lcmHeightLoss P <= Real.log ps - Real.log th :=
    hOuter.trans (div_le_self hLogDiffNonneg hLogThetaOne.le)
  have hInnerRatioPos : 0 < ps / th := div_pos hPsiPos hThetaPos
  have hInner := Real.log_le_sub_one_of_pos hInnerRatioPos
  have hInnerLogEq : Real.log (ps / th) = Real.log ps - Real.log th := by
    rw [Real.log_div hPsiPos.ne' hThetaPos.ne']
  have hInnerSubEq : ps / th - 1 = (ps - th) / th := by
    field_simp [hThetaPos.ne']
  rw [hInnerLogEq, hInnerSubEq] at hInner
  have hHeightLeGap : lcmHeightLoss P <= (ps - th) / th :=
    hHeightLeLogDiff.trans hInner
  have hPsiThetaBound : ps - th <=
      2 * Real.sqrt (P : Real) * Real.log (P : Real) := by
    exact Chebyshev.psi_sub_theta_le hPRealOne
  have hGapNumerator : 0 <= ps - th := sub_nonneg.mpr hThetaPsi
  have hKernelNumerator :
      0 <= 2 * Real.sqrt (P : Real) * Real.log (P : Real) := by positivity
  have hNumeratorStep : (ps - th) / th <=
      (2 * Real.sqrt (P : Real) * Real.log (P : Real)) / th :=
    div_le_div_of_nonneg_right hPsiThetaBound hThetaPos.le
  have hDenominatorStep :
      (2 * Real.sqrt (P : Real) * Real.log (P : Real)) / th <=
        (2 * Real.sqrt (P : Real) * Real.log (P : Real)) /
          ((Real.log 2 / 2) * (P : Real)) := by
    have hLowerDenPos : 0 < (Real.log 2 / 2) * (P : Real) :=
      mul_pos hCoeffPos hPRealPos
    exact div_le_div_of_nonneg_left hKernelNumerator hLowerDenPos hThetaLower
  have hSqrtPos : 0 < Real.sqrt (P : Real) := Real.sqrt_pos.2 hPRealPos
  have hKernelEq :
      (2 * Real.sqrt (P : Real) * Real.log (P : Real)) /
          ((Real.log 2 / 2) * (P : Real)) =
        (4 / Real.log 2) * Real.log (P : Real) *
          (P : Real) ^ (-(1 / 2 : Real)) := by
    rw [Real.rpow_neg hPRealPos.le, <- Real.sqrt_eq_rpow]
    have hSq : (Real.sqrt (P : Real)) ^ 2 = (P : Real) :=
      Real.sq_sqrt hPRealPos.le
    field_simp [hLogTwoPos.ne', hPRealPos.ne', hSqrtPos.ne']
    nlinarith
  refine And.intro hHeightNonneg ?_
  calc
    lcmHeightLoss P <= (ps - th) / th := hHeightLeGap
    _ <= (2 * Real.sqrt (P : Real) * Real.log (P : Real)) / th :=
      hNumeratorStep
    _ <= (2 * Real.sqrt (P : Real) * Real.log (P : Real)) /
        ((Real.log 2 / 2) * (P : Real)) := hDenominatorStep
    _ = (4 / Real.log 2) * Real.log (P : Real) *
        (P : Real) ^ (-(1 / 2 : Real)) := hKernelEq

/-- The elementary height kernel is little-o of every Nicolas scale with
exponent below one half. -/
theorem log_mul_rpow_neg_oneHalf_isLittleO_rpow_neg
    {b : Real} (hb : b < 1 / 2) :
    Asymptotics.IsLittleO (Filter.atTop : Filter Nat)
      (fun P : Nat =>
        Real.log (P : Real) * (P : Real) ^ (-(1 / 2 : Real)))
      (fun P : Nat => (P : Real) ^ (-b)) := by
  let d : Real := 1 / 2 - b
  have hd : 0 < d := by dsimp [d]; linarith
  have hLog : Asymptotics.IsLittleO (Filter.atTop : Filter Nat)
      (fun P : Nat => Real.log (P : Real))
      (fun P : Nat => (P : Real) ^ d) :=
    (isLittleO_log_rpow_atTop hd).natCast_atTop
  have hProduct : Asymptotics.IsLittleO (Filter.atTop : Filter Nat)
      (fun P : Nat =>
        Real.log (P : Real) * (P : Real) ^ (-(1 / 2 : Real)))
      (fun P : Nat =>
        (P : Real) ^ d * (P : Real) ^ (-(1 / 2 : Real))) := by
    exact hLog.mul_isBigO
      (isBigO_refl (fun P : Nat =>
        (P : Real) ^ (-(1 / 2 : Real))) Filter.atTop)
  have hRightEq : Filter.Eventually
      (fun P : Nat =>
        (P : Real) ^ d * (P : Real) ^ (-(1 / 2 : Real)) =
          (P : Real) ^ (-b)) Filter.atTop := by
    filter_upwards [Filter.eventually_atTop.2
      (Exists.intro 1 (fun _ h => h))] with P hPOne
    have hPPos : 0 < (P : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hPOne)
    rw [<- Real.rpow_add hPPos]
    congr 1
    dsimp [d]
    ring
  exact hProduct.congr' (Filter.Eventually.of_forall (fun _ => rfl)) hRightEq

/-- The complete lcm height loss is negligible relative to every Nicolas
oscillation scale `P^(-b)` with `b < 1/2`. -/
theorem lcmHeightLoss_isLittleO_rpow_neg
    {b : Real} (hb : b < 1 / 2) :
    Asymptotics.IsLittleO (Filter.atTop : Filter Nat)
      lcmHeightLoss (fun P : Nat => (P : Real) ^ (-b)) := by
  have hLogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCoeffPos : 0 < 4 / Real.log 2 := div_pos (by norm_num) hLogTwoPos
  have hBigO : Asymptotics.IsBigO (Filter.atTop : Filter Nat)
      lcmHeightLoss
      (fun P : Nat =>
        Real.log (P : Real) * (P : Real) ^ (-(1 / 2 : Real))) := by
    apply Asymptotics.IsBigO.of_bound (4 / Real.log 2)
    filter_upwards [eventually_lcmHeightLoss_nonneg_and_le_log_mul_rpow,
      Filter.eventually_atTop.2 (Exists.intro 1 (fun _ h => h))]
        with P hHeight hPOne
    have hPRealOne : (1 : Real) <= (P : Real) := by exact_mod_cast hPOne
    have hPRealPos : 0 < (P : Real) := lt_of_lt_of_le zero_lt_one hPRealOne
    have hLogPNonneg : 0 <= Real.log (P : Real) := Real.log_nonneg hPRealOne
    have hRpowPos : 0 < (P : Real) ^ (-(1 / 2 : Real)) :=
      Real.rpow_pos_of_pos hPRealPos _
    have hKernelNonneg :
        0 <= Real.log (P : Real) * (P : Real) ^ (-(1 / 2 : Real)) :=
      mul_nonneg hLogPNonneg hRpowPos.le
    simpa only [Real.norm_eq_abs, abs_of_nonneg hHeight.1,
      abs_of_nonneg hKernelNonneg, mul_assoc] using hHeight.2
  exact hBigO.trans_isLittleO
    (log_mul_rpow_neg_oneHalf_isLittleO_rpow_neg hb)

/-- The repository's finite prime set agrees with Mathlib's `primesLE`. -/
theorem primesUpToSet_eq_primesLE (P : Nat) :
    Robin1984.primesUpToSet P = Nat.primesLE P := by
  ext p
  simp [Robin1984.primesUpToSet, Nat.mem_primesLE]

/-- Every finite Nicolas Mertens product at a natural frontier is positive. -/
theorem nicolasMertensProduct_natCast_pos (P : Nat) :
    0 < nicolasMertensProduct (P : Real) := by
  unfold nicolasMertensProduct
  simp only [Nat.floor_natCast]
  apply Finset.prod_pos
  intro p hp
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primesLE hp
  have hpRealPos : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
  have hpRealOne : (1 : Real) < (p : Real) := by exact_mod_cast hpPrime.one_lt
  exact sub_pos.mpr ((div_lt_one hpRealPos).2 hpRealOne)

/-- The saturated Euler potential of `lcmUpto P` is exactly the negative
logarithm of Nicolas's finite Mertens product. -/
theorem factorizationEulerSaturation_lcmUpto_eq_neg_log_nicolasMertensProduct
    (P : Nat) :
    factorizationEulerSaturation (Nat.lcmUpto P) =
      -Real.log (nicolasMertensProduct (P : Real)) := by
  classical
  have hFactorNonzero : forall p, Membership.mem (Nat.primesLE P) p ->
      Not ((1 - 1 / (p : Real)) = 0) := by
    intro p hp
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primesLE hp
    have hpRealPos : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have hpRealOne : (1 : Real) < (p : Real) := by exact_mod_cast hpPrime.one_lt
    exact (sub_pos.mpr ((div_lt_one hpRealPos).2 hpRealOne)).ne'
  unfold factorizationEulerSaturation
  rw [Finsupp.sum, factorization_lcmUpto_support_eq_primesUpToSet,
    primesUpToSet_eq_primesLE]
  unfold nicolasMertensProduct
  simp only [Nat.floor_natCast]
  rw [Real.log_prod hFactorNonzero]
  unfold primeTowerTopCorrection
  rw [Finset.sum_neg_distrib]
  apply congrArg (fun z : Real => -z)
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Nat.cast_zero, zero_add, Int.natCast_one, neg_neg,
    zpow_neg, zpow_one, one_div]

/-- On the positive natural-frontier domain, Nicolas's logarithm expands into
Euler's constant, the theta height, and the finite Mertens product exactly. -/
theorem nicolasLogMertensOscillation_natCast_eq_expanded
    (P : Nat) (hTheta : 1 < Chebyshev.theta (P : Real)) :
    nicolasLogMertensOscillation (P : Real) =
      Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (P : Real))) +
          Real.log (nicolasMertensProduct (P : Real)) := by
  have hLogThetaPos : 0 < Real.log (Chebyshev.theta (P : Real)) :=
    Real.log_pos hTheta
  have hProductPos := nicolasMertensProduct_natCast_pos P
  unfold nicolasLogMertensOscillation nicolasFunction
  rw [Real.log_mul
    (mul_ne_zero (Real.exp_ne_zero _) hLogThetaPos.ne') hProductPos.ne']
  rw [Real.log_mul (Real.exp_ne_zero _) hLogThetaPos.ne']
  rw [Real.log_exp]

/-- The logarithmic Robin margin of the complete `lcmUpto P` packet. -/
def lcmRobinLogMargin (P : Nat) : Real :=
  Real.log (abundancy (Nat.lcmUpto P)) - Real.eulerMascheroniConstant -
    Real.log (Real.log (Real.log (Nat.lcmUpto P : Real)))

/-- Exact signed Nicolas-to-Robin identity for `lcmUpto P`.  The two terms
besides `-nicolasLogMertensOscillation` are precisely the complete height and
prime-power losses estimated above. -/
theorem lcmRobinLogMargin_eq_neg_nicolasLog_sub_height_sub_tower
    (P : Nat) (hTheta : 1 < Chebyshev.theta (P : Real)) :
    lcmRobinLogMargin P =
      -nicolasLogMertensOscillation (P : Real) - lcmHeightLoss P -
        factorizationTowerReserve (Nat.lcmUpto P) := by
  have hDecomp := factorizationEulerSaturation_eq_log_abundancy_add_reserve
    (Nat.lcmUpto_ne_zero P)
  have hSaturation :=
    factorizationEulerSaturation_lcmUpto_eq_neg_log_nicolasMertensProduct P
  rw [hSaturation] at hDecomp
  have hLogAbundancy :
      Real.log (abundancy (Nat.lcmUpto P)) =
        -Real.log (nicolasMertensProduct (P : Real)) -
          factorizationTowerReserve (Nat.lcmUpto P) := by
    linarith
  have hNicolas :=
    nicolasLogMertensOscillation_natCast_eq_expanded P hTheta
  unfold lcmRobinLogMargin lcmHeightLoss
  rw [hLogAbundancy, hNicolas]
  rw [<- Chebyshev.psi_eq_log_lcmUpto P]
  ring

/-- The complete lower-order loss in the exact lcm transfer identity. -/
def lcmTransferLoss (P : Nat) : Real :=
  lcmHeightLoss P + factorizationTowerReserve (Nat.lcmUpto P)

/-- The combined height and prime-power loss is negligible relative to every
Nicolas scale below exponent one half. -/
theorem lcmTransferLoss_isLittleO_rpow_neg
    {b : Real} (hb : b < 1 / 2) :
    Asymptotics.IsLittleO (Filter.atTop : Filter Nat)
      lcmTransferLoss (fun P : Nat => (P : Real) ^ (-b)) := by
  have hTowerScale : Asymptotics.IsLittleO (Filter.atTop : Filter Nat)
      (fun P : Nat => (P : Real) ^ (-(1 / 2 : Real)))
      (fun P : Nat => (P : Real) ^ (-b)) :=
    (rpow_neg_oneHalf_isLittleO_rpow_neg hb).natCast_atTop
  have hTower : Asymptotics.IsLittleO (Filter.atTop : Filter Nat)
      (fun P : Nat => factorizationTowerReserve (Nat.lcmUpto P))
      (fun P : Nat => (P : Real) ^ (-b)) :=
    factorizationTowerReserve_lcmUpto_isBigO_rpow_neg_oneHalf.trans_isLittleO
      hTowerScale
  unfold lcmTransferLoss
  exact (lcmHeightLoss_isLittleO_rpow_neg hb).add hTower

/-- The logarithmic lcm Robin margin sampled at the natural floor of a real
frontier. -/
def lcmRobinLogMarginFloor (x : Real) : Real :=
  lcmRobinLogMargin (Nat.floor x)

/-- The complete natural lcm transfer loss remains little-o after sampling at
the floor of a real frontier. -/
theorem lcmTransferLoss_natFloor_isLittleO_rpow_neg
    {b : Real} (hb : b < 1 / 2) :
    Asymptotics.IsLittleO Filter.atTop
      (fun x : Real => lcmTransferLoss (Nat.floor x))
      (fun x : Real => x ^ (-b)) := by
  have hComposed : Asymptotics.IsLittleO Filter.atTop
      (fun x : Real => lcmTransferLoss (Nat.floor x))
      (fun x : Real => (Nat.floor x : Real) ^ (-b)) :=
    (lcmTransferLoss_isLittleO_rpow_neg (b := b) hb).comp_tendsto
      tendsto_nat_floor_atTop
  have hFloorNonneg : Filter.Eventually
      (fun x : Real => 0 <= (Nat.floor x : Real)) Filter.atTop :=
    Filter.Eventually.of_forall (fun _ => by positivity)
  have hRealNonneg : Filter.Eventually (fun x : Real => 0 <= x) Filter.atTop :=
    Filter.eventually_ge_atTop 0
  have hScaleTheta : Asymptotics.IsTheta Filter.atTop
      (fun x : Real => (Nat.floor x : Real) ^ (-b))
      (fun x : Real => x ^ (-b)) :=
    Asymptotics.isEquivalent_nat_floor.isTheta.rpow hFloorNonneg hRealNonneg
  exact hComposed.trans_isBigO hScaleTheta.1

/-- Positive Omega excursions are invariant under eventual equality. -/
theorem AtTopOmegaPlus.congr_eventually
    {g1 g2 h : Real -> Real}
    (hg : AtTopOmegaPlus g1 h)
    (hEq : Filter.Eventually (fun x => g1 x = g2 x) Filter.atTop) :
    AtTopOmegaPlus g2 h := by
  choose c hc hLarge using hg
  refine Exists.intro c (And.intro hc ?_)
  intro X
  choose Y hY using Filter.eventually_atTop.mp hEq
  choose x hx hMain using hLarge (max X Y)
  refine Exists.intro x (And.intro (le_trans (le_max_left X Y) hx) ?_)
  have hxY : Y <= x := le_trans (le_max_right X Y) hx
  rw [<- hY x hxY]
  exact hMain

/-- Eventually the floor-sampled lcm Robin margin is exactly Nicolas's
negative logarithmic oscillation minus the complete transfer loss. -/
theorem eventually_lcmRobinLogMarginFloor_eq_neg_nicolasLog_sub_loss :
    Filter.Eventually
      (fun x : Real =>
        lcmRobinLogMarginFloor x =
          -nicolasLogMertensOscillation x - lcmTransferLoss (Nat.floor x))
      Filter.atTop := by
  have hLogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCoeffPos : 0 < Real.log 2 / 2 := div_pos hLogTwoPos (by norm_num)
  have hLinearTendsto : Filter.Tendsto
      (fun P : Nat => (Real.log 2 / 2) * (P : Real))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hCoeffPos
  have hCoeffAboveOne : Filter.Eventually
      (fun P : Nat => 1 < (Real.log 2 / 2) * (P : Real)) Filter.atTop :=
    hLinearTendsto.eventually_gt_atTop 1
  have hThetaNat : Filter.Eventually
      (fun P : Nat => 1 < Chebyshev.theta (P : Real)) Filter.atTop := by
    filter_upwards [eventually_log_two_div_two_mul_le_chebyshevTheta_nat,
      hCoeffAboveOne] with P hTheta hCoeff
    exact lt_of_lt_of_le hCoeff hTheta
  have hThetaFloor : Filter.Eventually
      (fun x : Real => 1 < Chebyshev.theta (Nat.floor x : Real)) Filter.atTop :=
    tendsto_nat_floor_atTop.eventually hThetaNat
  filter_upwards [hThetaFloor] with x hTheta
  have hIdentity :=
    lcmRobinLogMargin_eq_neg_nicolasLog_sub_height_sub_tower
      (Nat.floor x) hTheta
  unfold lcmRobinLogMarginFloor lcmTransferLoss
  rw [hIdentity, nicolasLogMertensOscillation_natFloor]
  ring

/-- Negative Nicolas excursions survive both complete lcm transfer losses and
become positive excursions of the exact lcm Robin logarithmic margin. -/
theorem lcmRobinLogMarginFloor_atTopOmegaPlus_of_nicolasOmegaMinus
    {b : Real} (hb : b < 1 / 2)
    (hOmega : AtTopOmegaMinus nicolasLogMertensOscillation
      (fun x : Real => x ^ (-b))) :
    AtTopOmegaPlus lcmRobinLogMarginFloor
      (fun x : Real => x ^ (-b)) := by
  unfold AtTopOmegaMinus at hOmega
  have hScalePos : Filter.Eventually
      (fun x : Real => 0 < x ^ (-b)) Filter.atTop := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    exact Real.rpow_pos_of_pos hx _
  have hLoss := lcmTransferLoss_natFloor_isLittleO_rpow_neg (b := b) hb
  have hCombined := hOmega.add_isLittleO hScalePos hLoss.neg_left
  apply hCombined.congr_eventually
  filter_upwards [eventually_lcmRobinLogMarginFloor_eq_neg_nicolasLog_sub_loss]
    with x hIdentity
  rw [hIdentity]
  ring

/-- Positive excursions of the floor-sampled lcm margin yield arbitrarily
large natural frontiers with positive exact lcm Robin logarithmic margin. -/
theorem arbitrarilyLarge_nat_lcmRobinLogMargin_pos_of_atTopOmegaPlus
    {b : Real}
    (hOmega : AtTopOmegaPlus lcmRobinLogMarginFloor
      (fun x : Real => x ^ (-b))) :
    forall N : Nat, Exists fun P : Nat =>
      N <= P /\ 0 < lcmRobinLogMargin P := by
  choose c hc hLarge using hOmega
  intro N
  choose x hx hExcursion using hLarge (max (N : Real) 1)
  have hxN : (N : Real) <= x := le_trans (le_max_left _ _) hx
  have hxOne : (1 : Real) <= x := le_trans (le_max_right _ _) hx
  have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hxOne
  let P := Nat.floor x
  have hNP : N <= P := (Nat.le_floor_iff hxPos.le).2 hxN
  have hScalePos : 0 < x ^ (-b) := Real.rpow_pos_of_pos hxPos _
  have hMarginFloor : 0 < lcmRobinLogMarginFloor x :=
    lt_of_lt_of_le (mul_pos hc hScalePos) hExcursion
  refine Exists.intro P (And.intro hNP ?_)
  exact hMarginFloor

/-- Every positive frontier is bounded by its complete `lcmUpto` packet. -/
theorem frontier_le_lcmUpto {P : Nat} (hP : 1 <= P) :
    P <= Nat.lcmUpto P := by
  apply Nat.le_of_dvd (Nat.lcmUpto_pos P)
  unfold Nat.lcmUpto
  simpa only [id_eq] using
    (Finset.dvd_lcm (s := Finset.Icc 1 P) (f := id)
      (Finset.mem_Icc.mpr (And.intro hP le_rfl)))

/-- Positivity of the exact lcm logarithmic margin is a literal failure of
Robin's inequality once the lcm packet lies above the cutoff. -/
theorem not_nativeRobinInequality_lcmUpto_of_logMargin_pos
    {P : Nat} (hCut : 5040 < Nat.lcmUpto P)
    (hMargin : 0 < lcmRobinLogMargin P) :
    Not (Robin1984.Core.NativeRobinInequality (Nat.lcmUpto P)) := by
  let n := Nat.lcmUpto P
  have hnPos : 0 < n := Nat.lcmUpto_pos P
  have hBoundPos : 0 < robinBoundRatio n := robinBoundRatio_pos_of_cutoff hCut
  have hAbundancyPos : 0 < abundancy n := abundancy_pos hnPos
  have hLogBound := log_robinBoundRatio_eq_of_cutoff hCut
  have hLogLt : Real.log (robinBoundRatio n) < Real.log (abundancy n) := by
    unfold lcmRobinLogMargin at hMargin
    dsimp [n] at hBoundPos hAbundancyPos hLogBound
    rw [hLogBound]
    linarith
  have hExpLt := Real.exp_lt_exp.mpr hLogLt
  have hBoundLt : robinBoundRatio n < abundancy n := by
    rw [Real.exp_log hBoundPos, Real.exp_log hAbundancyPos] at hExpLt
    exact hExpLt
  intro hRobin
  have hRobinRatio :=
    (nativeRobinInequality_iff_abundancy_lt_bound hnPos).mp hRobin
  exact (not_lt_of_ge hBoundLt.le) hRobinRatio

/-- Negative Nicolas Omega excursions below exponent one half force actual
Robin counterexamples at arbitrarily large `lcmUpto` packets. -/
theorem arbitrarilyLarge_lcmUpto_robinCounterexample_of_nicolasOmegaMinus
    {b : Real} (hb : b < 1 / 2)
    (hOmega : AtTopOmegaMinus nicolasLogMertensOscillation
      (fun x : Real => x ^ (-b))) :
    forall N : Nat, Exists fun P : Nat =>
      N <= P /\ 5040 < Nat.lcmUpto P /\
        Not (Robin1984.Core.NativeRobinInequality (Nat.lcmUpto P)) := by
  have hMarginOmega :=
    lcmRobinLogMarginFloor_atTopOmegaPlus_of_nicolasOmegaMinus hb hOmega
  intro N
  choose P hNP hMargin using
    arbitrarilyLarge_nat_lcmRobinLogMargin_pos_of_atTopOmegaPlus hMarginOmega
      (max N 5041)
  have hNLe : N <= P := le_trans (le_max_left N 5041) hNP
  have hPMin : 5041 <= P := le_trans (le_max_right N 5041) hNP
  have hPPositive : 1 <= P := by omega
  have hPLcm : P <= Nat.lcmUpto P := frontier_le_lcmUpto hPPositive
  have hCut : 5040 < Nat.lcmUpto P := by omega
  exact Exists.intro P (And.intro hNLe (And.intro hCut
    (not_nativeRobinInequality_lcmUpto_of_logMargin_pos hCut hMargin)))

/-- Conditional arithmetic half of Robin's source theorem: Nicolas's negative
oscillation conclusion contradicts `NativeRobinInequalityAll`. -/
theorem not_nativeRobinInequalityAll_of_nicolasOmegaMinus
    {b : Real} (hb : b < 1 / 2)
    (hOmega : AtTopOmegaMinus nicolasLogMertensOscillation
      (fun x : Real => x ^ (-b))) :
    Not Robin1984.Core.NativeRobinInequalityAll := by
  intro hAll
  choose P _hP hCut hNot using
    arbitrarilyLarge_lcmUpto_robinCounterexample_of_nicolasOmegaMinus
      hb hOmega 0
  exact hNot (hAll (Nat.lcmUpto P) hCut)

end

end Robin1984
