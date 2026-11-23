import Robin1984.GRH.DedekindMertensAbel
import Robin1984.GRH.PrimeIdealPrimorial

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The truncated real logarithm series and the geometric Euler factors of the prime-power cutoff ideal.
- Formalization note: Reindex the finite prime-power sum by prime ideal and predecessor exponent, then compare with the logarithm of the divisor ratio.
- PROVENANCE-END
-/

/-!
# Mertens sum versus the divisor ratio of the cutoff ideal

The positive logarithm series bounds each finite prime-power contribution
by the logarithm of the corresponding geometric factor plus its truncation
loss. The losses remain indexed by the actual prime ideals.
-/

open IsDedekindDomain NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "PP" => Prod P Nat

private theorem pow_succ_le_half {r : Real} (hr : 0 < r)
    (hHalf : r <= 1 / 2) (k : Nat) : r ^ (k + 1) <= 1 / 2 := by
  have hOne : r <= 1 := hHalf.trans (by norm_num)
  have hPow : forall j : Nat, r ^ j <= 1 := by
    intro j
    induction j with
    | zero => rw [pow_zero]
    | succ j ih =>
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right ih hr.le).trans (by simpa only [one_mul] using hOne)
  rw [pow_succ]
  exact (mul_le_mul_of_nonneg_right (hPow k) hr.le).trans
    (by simpa only [one_mul] using hHalf)

private theorem primePowerLogSeries_le_logGeomFactor {r : Real} (hr : 0 < r)
    (hHalf : r <= 1 / 2) (k : Nat) :
    (Finset.range k).sum (fun j => r ^ (j + 1) / ((j + 1 : Nat) : Real)) <=
      Real.log ((1 - r ^ (k + 1)) / (1 - r)) + 2 * r ^ (k + 1) := by
  have hr1 : r < 1 := hHalf.trans_lt (by norm_num)
  have hTrunc := pow_succ_le_half hr hHalf k
  have hz : 0 <= r ^ (k + 1) := pow_nonneg hr.le _
  have hDen : 0 < 1 - r ^ (k + 1) := by linarith only [hTrunc]
  have hAbs : abs r < 1 := by rw [abs_of_pos hr]; exact hr1
  have hSum := Real.hasSum_pow_div_log_of_abs_lt_one hAbs
  have hPrefix :
      (Finset.range k).sum (fun j => r ^ (j + 1) / ((j + 1 : Nat) : Real)) <=
        -Real.log (1 - r) := by
    simp only [Nat.cast_add, Nat.cast_one]
    rw [<- hSum.tsum_eq]
    apply hSum.summable.sum_le_tsum
    intro j _
    exact div_nonneg (pow_nonneg hr.le _) (add_nonneg (Nat.cast_nonneg _) zero_le_one)
  have hLog := Real.one_sub_inv_le_log_of_pos hDen
  have hLoss : -(2 * r ^ (k + 1)) <= 1 - Inv.inv (1 - r ^ (k + 1)) := by
    let z := r ^ (k + 1)
    have hd : 0 < 1 - z := hDen
    have hMul : -(2 * z) * (1 - z) <= 1 - z - 1 := by
      nlinarith only [mul_nonneg hz (sub_nonneg.mpr hTrunc)]
    change -(2 * z) <= 1 - Inv.inv (1 - z)
    calc
      _ = (-(2 * z) * (1 - z)) / (1 - z) := by field_simp
      _ <= (1 - z - 1) / (1 - z) := div_le_div_of_nonneg_right hMul hd.le
      _ = _ := by rw [sub_div, div_self hd.ne', one_div]
  rw [Real.log_div hDen.ne' (sub_pos.mpr hr1).ne']
  linarith only [hPrefix, hLoss, hLog]

/-- A finite divisor Euler factor is bounded by the logarithmic prime-power
series through its exact exponent, for a reciprocal norm at most one half. -/
theorem logGeomFactor_le_primePowerLogSeries {r : Real} (hr : 0 < r)
    (hHalf : r <= 1 / 2) (k : Nat) :
    Real.log ((1 - r ^ (k + 1)) / (1 - r)) <=
      (Finset.range k).sum (fun j => r ^ (j + 1) / ((j + 1 : Nat) : Real)) := by
  have hr1 : r < 1 := hHalf.trans_lt (by norm_num)
  have hBase : 0 < 1 - r := sub_pos.mpr hr1
  by_cases hk0 : k = 0
  case pos =>
    subst k
    simp [hBase.ne']
  have hk : 1 <= k := Nat.pos_of_ne_zero hk0
  let f : Nat -> Real := fun j => r ^ (j + 1) / ((j : Real) + 1)
  let c : Real := r ^ (k + 1) / 2
  have hAbs : abs r < 1 := by rw [abs_of_pos hr]; exact hr1
  have hSum : HasSum f (-Real.log (1 - r)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one hAbs
  have hShift : Summable (fun j : Nat => f (j + k)) :=
    (summable_nat_add_iff k).mpr hSum.summable
  have hSplit :
      (Finset.range k).sum f + (tsum fun j : Nat => f (j + k)) =
        -Real.log (1 - r) :=
    (hSum.summable.sum_add_tsum_nat_add k).trans hSum.tsum_eq
  have hPoint (j : Nat) : f (j + k) <= c * r ^ j := by
    have hkR : (1 : Real) <= (k : Real) := by exact_mod_cast hk
    have hj : (2 : Real) <= (j : Real) + (k : Real) + 1 := by
      linarith only [hkR, (show (0 : Real) <= (j : Real) from Nat.cast_nonneg j)]
    unfold f
    rw [Nat.cast_add, Nat.add_assoc, pow_add]
    calc
      _ <= (r ^ j * r ^ (k + 1)) / 2 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (pow_nonneg hr.le _) (pow_nonneg hr.le _)) (by norm_num) hj
      _ = _ := by unfold c; ring
  have hTail : (tsum fun j : Nat => f (j + k)) <= r ^ (k + 1) := calc
    _ <= (tsum fun j : Nat => c * r ^ j) :=
      hShift.tsum_le_tsum hPoint ((summable_geometric_of_lt_one hr.le hr1).mul_left c)
    _ = c * Inv.inv (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr.le hr1]
    _ = r ^ (k + 1) / (2 * (1 - r)) := by
      unfold c
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    _ <= _ := by
      have h := div_le_div_of_nonneg_left (pow_nonneg hr.le (k + 1)) zero_lt_one
        (by linarith only [hHalf] : (1 : Real) <= 2 * (1 - r))
      simpa only [div_one] using h
  have hDen : 0 < 1 - r ^ (k + 1) := by
    have h := pow_succ_le_half hr hHalf k
    linarith only [h]
  have hLog : Real.log (1 - r ^ (k + 1)) <= -(r ^ (k + 1)) := by
    linarith only [Real.log_le_sub_one_of_pos hDen]
  rw [Real.log_div hDen.ne' hBase.ne']
  simp only [Nat.cast_add, Nat.cast_one]
  change _ <= (Finset.range k).sum f
  linarith only [hSplit, hTail, hLog]

/-- Group the finite prime-power support by prime and predecessor exponent. -/
theorem sum_primePowersUpTo_eq_sum_by_prime [DecidableEq P] {n : Nat} (hn : Not (n = 0))
    (w : PP -> Real) :
    (primePowersUpTo K n).sum w =
      (cutoffPrimeMultiplicities K n).toFinset.sum (fun p =>
        (Finset.range (Nat.log (dedekindPrimeNorm K p) n)).sum (fun j => w (p, j))) := by
  classical
  have hMaps (pn : PP) (hp : Membership.mem (primePowersUpTo K n) pn) :
      Membership.mem (cutoffPrimeMultiplicities K n).toFinset pn.1 := by
    rw [Multiset.mem_toFinset, cutoffPrimeMultiplicities]
    exact Multiset.mem_map.mpr (Exists.intro pn (And.intro hp rfl))
  rw [<- Finset.sum_fiberwise_of_maps_to hMaps w]
  apply Finset.sum_congr rfl
  intro p _
  refine Finset.sum_bij (fun pn _ => pn.2) ?membership ?injective ?surjective ?value
  case membership =>
    intro pn hpn
    have hp := Finset.mem_filter.mp hpn
    have hpow : dedekindPrimeNorm K p ^ (pn.2 + 1) <= n := by
      simpa only [dedekindPrimePowerNorm, hp.2] using (mem_primePowersUpTo K).mp hp.1
    exact Finset.mem_range.mpr (Nat.lt_of_succ_le
      ((Nat.le_log_iff_pow_le (one_lt_dedekindPrimeNorm K p) hn).mpr hpow))
  case injective =>
    intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
  case surjective =>
    intro j hj
    have hpow := (Nat.le_log_iff_pow_le (one_lt_dedekindPrimeNorm K p) hn).mp
      (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
    exact Exists.intro (p, j) (Exists.intro
      (Finset.mem_filter.mpr (And.intro ((mem_primePowersUpTo K).mpr hpow) rfl)) rfl)
  case value =>
    intro pn hpn
    have hp := (Finset.mem_filter.mp hpn).2
    exact congrArg w (Prod.ext hp rfl)

/-- The Mertens sum is bounded by the logarithm of the cutoff ideal's divisor
ratio plus the sum of the local losses from truncating the geometric factors. -/
theorem dedekindMertensPrimePowerSum_le_log_cutoffIdeal_add [DecidableEq P] {n : Nat}
    (hn : Not (n = 0)) :
    dedekindMertensPrimePowerSum K (n : Real) <=
      Real.log ((idealDivisorNormSum (primePowerCutoffIdeal K n)
        (primePowerCutoffIdeal_ne_zero K n) : Real) /
          (Ideal.absNorm (primePowerCutoffIdeal K n) : Real)) +
        (cutoffPrimeMultiplicities K n).toFinset.sum (fun p =>
          2 * (Inv.inv (dedekindPrimeNorm K p : Real)) ^ (Nat.log (dedekindPrimeNorm K p) n + 1)) := by
  classical
  let q (p : P) : Real := dedekindPrimeNorm K p
  let r (p : P) : Real := Inv.inv (q p)
  let k (p : P) : Nat := Nat.log (dedekindPrimeNorm K p) n
  let g (p : P) : Real := (1 - r p ^ (k p + 1)) / (1 - r p)
  have hq (p : P) : (2 : Real) <= q p := by
    change (2 : Real) <= (dedekindPrimeNorm K p : Real)
    exact_mod_cast Nat.succ_le_iff.mpr (one_lt_dedekindPrimeNorm K p)
  have hr (p : P) : 0 < r p := inv_pos.mpr ((by norm_num : (0 : Real) < 2).trans_le (hq p))
  have hrHalf (p : P) : r p <= 1 / 2 := by
    dsimp only [r]
    rw [<- one_div]
    exact one_div_le_one_div_of_le (by norm_num) (hq p)
  have hg (p : P) : 0 < g p := by
    exact div_pos (sub_pos.mpr ((pow_succ_le_half (hr p) (hrHalf p) (k p)).trans_lt (by norm_num)))
      (sub_pos.mpr ((hrHalf p).trans_lt (by norm_num)))
  rw [dedekindMertensPrimePowerSum_eq_sum_primePowersUpTo, Nat.floor_natCast,
    sum_primePowersUpTo_eq_sum_by_prime K hn, cutoffIdeal_divisorRatio_eq_product K hn]
  change _ <= Real.log ((cutoffPrimeMultiplicities K n).toFinset.prod g) +
    (cutoffPrimeMultiplicities K n).toFinset.sum (fun p => 2 * r p ^ (k p + 1))
  rw [Real.log_prod (fun p _ => (hg p).ne'), <- Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  have hTerms (j : Nat) :
      Inv.inv ((dedekindPrimePowerNorm K (p, j) : Real) * ((j + 1 : Nat) : Real)) =
        r p ^ (j + 1) / ((j + 1 : Nat) : Real) := by
    simp [r, q, dedekindPrimePowerNorm, Nat.cast_pow, inv_pow, div_eq_mul_inv, mul_comm]
  simp_rw [hTerms]
  exact primePowerLogSeries_le_logGeomFactor (hr p) (hrHalf p) (k p)

end Robin1984.GRH
