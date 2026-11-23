import Robin1984.GRH.DedekindMertensNormalization
import Robin1984.GRH.DedekindRobinSupportingLine
import Robin1984.GRH.MertensTailUpperBound

/-!
# From the Dedekind primitive-tail estimate to the corrected Robin inequality

The finite ideal comparison cancels the Mertens boundary contribution. A
strict gap between the primitive-tail coefficient and the advertised Robin
correction absorbs the smaller term from the Mertens weight.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Abel summation and the eventual elementary logarithmic comparison.
- Formalization note: A positive coefficient gap gives a field-dependent cutoff.
- Content basis: The supporting line, residue normalization, and signed tail estimate.
- Dependency status: Optional GRH extension and existing Mathlib APIs.
-/

open DedekindZeta Filter MeasureTheory NumberField Set Topology

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

/-- An eventual bound for the absolute primitive tail with coefficient
strictly below the Robin correction implies the corrected ideal inequality. -/
theorem correctedIdealRobin_of_abs_primitiveTail {c B X : Real}
    (hB : 0 <= B)
    (hGap : B < 12 + 3 * Real.log ((NumberField.discr K).natAbs : Real))
    (hLimit : Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c))
    (hTail : forall t : Real, X <= t ->
      abs (primitiveTail (dedekindChebyshevErrorRatio K) c t) <= B / Real.sqrt t) :
    CorrectedIdealRobin K := by
  let C : Real := 12 + 3 * Real.log ((NumberField.discr K).natAbs : Real)
  let e : Real := (C - B) / 2
  let T := primitiveTail (dedekindChebyshevErrorRatio K) c
  have hC : 0 < C := hB.trans_lt hGap
  have he : 0 < e := half_pos (sub_pos.mpr hGap)
  have hSlack : B + e + e = C := by unfold e; ring
  have hEarly : forall (x : Real), max X 2 <= x -> 1 < x :=
    fun _ hx => (by norm_num : (1 : Real) < 2).trans_le ((le_max_right X 2).trans hx)
  have hFar : Filter.Eventually (fun x : Real => And (max X 2 <= x)
      (And (1 + 7 * B / e <= Real.log x) (C ^ (2 : Nat) / e <= Real.sqrt x))) atTop := by
    filter_upwards [eventually_ge_atTop (max X 2),
      (tendsto_atTop.mp Real.tendsto_log_atTop) (1 + 7 * B / e),
      (tendsto_atTop.mp Real.tendsto_sqrt_atTop) (C ^ (2 : Nat) / e)] with x hx hl hs
    exact And.intro hx (And.intro hl hs)
  choose M hM using eventually_atTop.mp hFar
  refine Exists.intro (Nat.ceil (Real.exp M)) ?_
  intro a ha hNorm
  let x := Real.log (Ideal.absNorm a : Real)
  let L := Real.log x
  let y := Real.sqrt x
  let D := y * L
  have hN : Real.exp M <= (Ideal.absNorm a : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNorm)
  have hxM : M <= x := by
    have h := Real.log_le_log (Real.exp_pos M) hN
    rw [Real.log_exp] at h
    exact h
  have hGood := hM x hxM
  have hx := hEarly x hGood.1
  have hy : 0 < y := Real.sqrt_pos.mpr (zero_lt_one.trans hx)
  have hL1 : 1 <= L := (le_add_of_nonneg_right (div_nonneg (by positivity) he.le)).trans
    hGood.2.1
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hD : 0 < D := mul_pos hy hL
  have hX : X <= x := (le_max_left X 2).trans hGood.1
  have hMeas : AEStronglyMeasurable T (volume.restrict (Ioi x)) :=
    ((continuousOn_dedekindPrimitiveTail K c).mono (fun _ ht => hx.trans ht)).aestronglyMeasurable
      measurableSet_Ioi
  have hWeighted := signed_mertensTail_le_of_abs_primitiveTail hx hL1 hB hMeas
    (fun t ht => hTail t (hX.trans ht))
  change dedekindMertensWeightedTail K c x <=
    B / D + 7 * B / (y * L ^ (2 : Nat)) at hWeighted
  have hSmall : 7 * B / L <= e := by
    have h7 : 7 * B / e <= L := by linarith only [hGood.2.1]
    have hm := mul_le_mul_of_nonneg_right h7 he.le
    rw [show 7 * B / e * e = 7 * B from by field_simp [he.ne']] at hm
    have hd := div_le_div_of_nonneg_right hm hL.le
    rw [show L * e / L = e from by field_simp [hL.ne']] at hd
    exact hd
  have hTailUpper : dedekindMertensWeightedTail K c x <= (B + e) / D := calc
    _ <= B / D + 7 * B / (y * L ^ (2 : Nat)) := hWeighted
    _ = B / D + (7 * B / L) / D := by unfold D; ring
    _ <= B / D + e / D := add_le_add le_rfl (div_le_div_of_nonneg_right hSmall hD.le)
    _ = _ := by rw [add_div]
  have hCsmall : C ^ (2 : Nat) <= e * D := by
    have hScale := mul_le_mul_of_nonneg_right hGood.2.2 he.le
    rw [show C ^ (2 : Nat) / e * e = C ^ (2 : Nat) from by field_simp [he.ne']] at hScale
    have hDy : y <= D := by
      change y <= y * L
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hL1 hy.le
    exact hScale.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hDy he.le)
  have hDen : 0 < D + C := add_pos hD hC
  have hz : 0 < 1 + C / D := by positivity
  have hCorrection : (B + e) / D <= Real.log (1 + C / D) := calc
    _ <= C / (D + C) := by
      apply le_of_mul_le_mul_right _ (mul_pos hD hDen)
      have hc := mul_nonneg hC.le (show 0 <= C - (B + e) by linarith only [hSlack, he])
      have hBC : (B + e) * C <= e * D :=
        (show (B + e) * C <= C ^ (2 : Nat) by nlinarith only [hc]).trans hCsmall
      calc
        _ = (B + e) * (D + C) := by field_simp [hD.ne']
        _ = (B + e) * D + (B + e) * C := mul_add _ _ _
        _ <= (B + e) * D + e * D := add_le_add le_rfl hBC
        _ = C * D := by rw [<- add_mul, hSlack]
        _ = (C / (D + C)) * (D * (D + C)) := by field_simp [hDen.ne']
    _ = 1 - Inv.inv (1 + C / D) := by field_simp [hDen.ne', hD.ne', hz.ne'] <;> ring
    _ <= _ := Real.one_sub_inv_le_log_of_pos hz
  have hMertens := dedekindMertensPrimePowerSum_eq_residue_weightedTail K
    (by norm_num : (1 : Real) < 3 / 2) (by norm_num : (3 / 2 : Real) < 2)
    ((by norm_num : (3 / 2 : Real) <= 2).trans ((le_max_right X 2).trans hGood.1)) hLimit
  have hIdeal := log_idealDivisorRatio_le_mertensSupportingLine K a ha hx
  change Real.log ((idealDivisorNormSum a ha : Real) / (Ideal.absNorm a : Real)) <=
    dedekindMertensPrimePowerSum K x + (x - dedekindChebyshev K x) / (x * L) at hIdeal
  rw [hMertens] at hIdeal
  have hCancel :
      mertensPrimePowerWeight x * (dedekindChebyshev K x - x) +
        (x - dedekindChebyshev K x) / (x * L) = 0 := by
    change Inv.inv (x * L) * (dedekindChebyshev K x - x) +
      (x - dedekindChebyshev K x) / (x * L) = 0
    ring
  have hLogIdeal :
      Real.log ((idealDivisorNormSum a ha : Real) / (Ideal.absNorm a : Real)) <=
        Real.log L + (Real.eulerMascheroniConstant + Real.log (dedekindZeta_residue K)) +
          Real.log (1 + C / D) :=
    (by linarith only [hIdeal, hCancel, hTailUpper, hCorrection])
  let ratio := (idealDivisorNormSum a ha : Real) / (Ideal.absNorm a : Real)
  let target := Real.exp Real.eulerMascheroniConstant * dedekindZeta_residue K * (L + C / y)
  change ratio <= target
  have hPref : 0 < Real.exp Real.eulerMascheroniConstant * dedekindZeta_residue K :=
    mul_pos (Real.exp_pos _) (dedekindZeta_residue_pos K)
  have hFactor : L + C / y = L * (1 + C / D) := by
    unfold D
    field_simp [hL.ne', hy.ne'] <;> ring
  have hTarget : 0 < target := by
    unfold target
    rw [hFactor]
    exact mul_pos hPref (mul_pos hL hz)
  by_cases hRatio : 0 < ratio
  case pos =>
    apply (Real.log_le_log_iff hRatio hTarget).mp
    unfold target
    rw [hFactor, Real.log_mul hPref.ne' (mul_pos hL hz).ne',
      Real.log_mul (Real.exp_pos _).ne' (dedekindZeta_residue_pos K).ne',
      Real.log_exp, Real.log_mul hL.ne' hz.ne']
    change Real.log ratio <= _
    linarith only [hLogIdeal]
  case neg => exact (le_of_not_gt hRatio).trans hTarget.le

end Robin1984.GRH
