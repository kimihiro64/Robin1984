import Robin1984.GRH.DedekindCutoffMertens
import Robin1984.GRH.DedekindPrimeLossIntegral

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A three-range bound for the geometric error at a Dedekind prime-power cutoff.
- Formalization note: Use the first-power Chebyshev domination below the square root and the inverse-square kernel above it.
- PROVENANCE-END
-/

/-!
# Summed geometric losses in the corrected ideal Robin converse

A linear Chebyshev upper bound controls the sum of all geometric
truncation losses by a constant times the reciprocal square root and
logarithm of the real cutoff.
-/

open IsDedekindDomain NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)

/-- Bound the cutoff ideal's total Euler truncation loss at the scale
required for the Mertens tail converse. -/
theorem sum_cutoffIdealLoss_le [DecidableEq P] {A x : Real} (hA : 0 <= A) (hx : 1 < x)
    (hPsi : forall t : Real, 1 <= t -> dedekindChebyshev K t <= A * t) :
    (cutoffPrimeMultiplicities K (Nat.floor x)).toFinset.sum (fun p =>
      2 * (Inv.inv (dedekindPrimeNorm K p : Real)) ^
        (Nat.log (dedekindPrimeNorm K p) (Nat.floor x) + 1)) <=
      32 * A / (Real.sqrt x * Real.log x) := by
  classical
  let n := Nat.floor x
  let y := Real.sqrt x
  let z := Real.sqrt y
  let L := Real.log x
  let q (p : P) : Real := dedekindPrimeNorm K p
  let k (p : P) : Nat := Nat.log (dedekindPrimeNorm K p) n
  let loss (p : P) : Real := 2 * (Inv.inv (q p)) ^ (k p + 1)
  let B := (cutoffPrimeMultiplicities K n).toFinset
  let S := B.filter (fun p => q p <= z)
  let M := (B.filter (fun p => q p <= y)).filter (fun p => Not (q p <= z))
  let T := B.filter (fun p => Not (q p <= y))
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy : 1 <= y := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx.le
  have hz : 1 <= z := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hy
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hz0 : 0 < z := zero_lt_one.trans_le hz
  have hL0 : 0 < L := Real.log_pos hx
  have hxy : y * y = x := Real.mul_self_sqrt hx0.le
  have hyz : z * z = y := Real.mul_self_sqrt hy0.le
  have hzy : z <= y := by
    calc
      _ <= z * z := le_mul_of_one_le_right hz0.le hz
      _ = _ := hyz
  have hLogY : L = 2 * Real.log y := by
    change Real.log x = _
    rw [<- hxy, Real.log_mul hy0.ne' hy0.ne']
    ring
  have hLogZ : L = 4 * Real.log z := by
    rw [hLogY, <- hyz, Real.log_mul hz0.ne' hz0.ne']
    ring
  have hLogLim : L <= 4 * z := by
    rw [hLogZ]
    have h := Real.log_le_sub_one_of_pos hz0
    linarith only [h]
  have hn1 : 1 <= n := (Nat.le_floor_iff hx0.le).mpr (by simpa only [Nat.cast_one] using hx.le)
  have hn : Not (n = 0) := Nat.ne_of_gt hn1
  have hq2 (p : P) : 2 <= q p := by
    change (2 : Real) <= (dedekindPrimeNorm K p : Real)
    exact_mod_cast Nat.succ_le_iff.mpr (one_lt_dedekindPrimeNorm K p)
  have hq0 (p : P) : 0 < q p := (by norm_num : (0 : Real) < 2).trans_le (hq2 p)
  have hLogq (p : P) : 1 / 2 <= Real.log (q p) := by
    have hTwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    have hLog := Real.log_le_log (by norm_num : (0 : Real) < 2) (hq2 p)
    norm_num at hTwo
    exact hTwo.trans hLog
  have hX (p : P) : loss p <= 2 / x := by
    have hNat := Nat.lt_pow_succ_log_self (one_lt_dedekindPrimeNorm K p) n
    have hPower : x < q p ^ (k p + 1) := by
      have h := Nat.lt_of_floor_lt (a := x) hNat
      simpa only [Nat.cast_pow] using h
    change 2 * (Inv.inv (q p)) ^ (k p + 1) <= 2 / x
    rw [inv_pow, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [one_div] using one_div_le_one_div_of_le hx0 hPower.le
  have hSquare (p : P) (hp : Membership.mem B p) : loss p <= 2 / q p ^ (2 : Nat) := by
    have hnp : dedekindPrimeNorm K p <= n := (mem_cutoffPrimeMultiplicities_toFinset K hn p).mp hp
    have hk : 1 <= k p := Nat.log_pos (one_lt_dedekindPrimeNorm K p) hnp
    have hPows : Monotone (fun j : Nat => q p ^ j) := by
      apply monotone_nat_of_le_succ
      intro j
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg (hq0 p).le _)
        ((by norm_num : (1 : Real) <= 2).trans (hq2 p))
    have hPow : q p ^ (2 : Nat) <= q p ^ (k p + 1) := hPows (Nat.succ_le_succ hk)
    change 2 * (Inv.inv (q p)) ^ (k p + 1) <= 2 / q p ^ (2 : Nat)
    rw [inv_pow, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos (hq0 p) _) hPow
  have hSlog : S.sum (fun p => Real.log (q p)) <= A * z :=
    (sum_primeNormLog_le_dedekindChebyshev K S hz0.le
      (fun _ hp => (Finset.mem_filter.mp hp).2)).trans (hPsi z hz)
  have hMlog : M.sum (fun p => Real.log (q p)) <= A * y :=
    (sum_primeNormLog_le_dedekindChebyshev K M hy0.le
      (fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)).trans (hPsi y hy)
  have hTlog : T.sum (fun p => Real.log (q p) / q p ^ (2 : Nat)) <= 2 * A / y :=
    sum_primeNormLog_div_norm_sq_le K hy hPsi T
      (fun _ hp => (lt_of_not_ge (Finset.mem_filter.mp hp).2).le)
  have hSmall : S.sum loss <= 16 * A / (y * L) := by
    have hEach (p : P) : loss p <= (4 / x) * Real.log (q p) := calc
      _ <= 2 / x := hX p
      _ = (4 / x) * (1 / 2) := by ring
      _ <= _ := mul_le_mul_of_nonneg_left (hLogq p) (div_nonneg (by norm_num) hx0.le)
    have hProd : (4 * A * z) * L <= (16 * A) * y := calc
      _ <= (4 * A * z) * (4 * z) := mul_le_mul_of_nonneg_left hLogLim
        (mul_nonneg (mul_nonneg (by norm_num) hA) hz0.le)
      _ = _ := by rw [<- hyz]; ring
    calc
      _ <= S.sum (fun p => (4 / x) * Real.log (q p)) :=
        Finset.sum_le_sum (fun p _ => hEach p)
      _ = (4 / x) * S.sum (fun p => Real.log (q p)) := (Finset.mul_sum ..).symm
      _ <= (4 / x) * (A * z) := mul_le_mul_of_nonneg_left hSlog (div_nonneg (by norm_num) hx0.le)
      _ = ((4 * A * z) * L) / (x * L) := by field_simp [hx0.ne', hL0.ne']
      _ <= ((16 * A) * y) / (x * L) := div_le_div_of_nonneg_right hProd (mul_nonneg hx0.le hL0.le)
      _ = _ := by field_simp [hx0.ne', hy0.ne', hL0.ne']; rw [<- hxy]; ring
  have hMid : M.sum loss <= 8 * A / (y * L) := by
    have hEach (p : P) (hp : Membership.mem M p) :
        loss p <= (8 / (x * L)) * Real.log (q p) := by
      have hpz : z < q p := lt_of_not_ge (Finset.mem_filter.mp hp).2
      have hlog : L / 4 <= Real.log (q p) := by
        have h := Real.log_le_log hz0 hpz.le
        rw [hLogZ]
        linarith only [h]
      calc
        _ <= 2 / x := hX p
        _ = (8 / (x * L)) * (L / 4) := by field_simp [hx0.ne', hL0.ne']; ring
        _ <= _ := mul_le_mul_of_nonneg_left hlog
          (div_nonneg (by norm_num) (mul_nonneg hx0.le hL0.le))
    calc
      _ <= M.sum (fun p => (8 / (x * L)) * Real.log (q p)) := Finset.sum_le_sum hEach
      _ = (8 / (x * L)) * M.sum (fun p => Real.log (q p)) := (Finset.mul_sum ..).symm
      _ <= (8 / (x * L)) * (A * y) := mul_le_mul_of_nonneg_left hMlog
        (div_nonneg (by norm_num) (mul_nonneg hx0.le hL0.le))
      _ = _ := by field_simp [hx0.ne', hy0.ne', hL0.ne']; rw [<- hxy]; ring
  have hLarge : T.sum loss <= 8 * A / (y * L) := by
    have hEach (p : P) (hp : Membership.mem T p) :
        loss p <= (4 / L) * (Real.log (q p) / q p ^ (2 : Nat)) := by
      have hp' := Finset.mem_filter.mp hp
      have hyq : y < q p := lt_of_not_ge hp'.2
      have hlog : L / 2 <= Real.log (q p) := by
        have h := Real.log_le_log hy0 hyq.le
        rw [hLogY]
        linarith only [h]
      calc
        _ <= 2 / q p ^ (2 : Nat) := hSquare p hp'.1
        _ = (4 / L) * ((L / 2) / q p ^ (2 : Nat)) := by
          field_simp [hL0.ne', (hq0 p).ne']
          ring
        _ <= _ := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hlog (pow_nonneg (hq0 p).le _))
          (div_nonneg (by norm_num) hL0.le)
    calc
      _ <= T.sum (fun p => (4 / L) * (Real.log (q p) / q p ^ (2 : Nat))) :=
        Finset.sum_le_sum hEach
      _ = (4 / L) * T.sum (fun p => Real.log (q p) / q p ^ (2 : Nat)) :=
        (Finset.mul_sum ..).symm
      _ <= (4 / L) * (2 * A / y) := mul_le_mul_of_nonneg_left hTlog (div_nonneg (by norm_num) hL0.le)
      _ = _ := by field_simp [hL0.ne', hy0.ne']; ring
  have hSmallSet : (B.filter (fun p => q p <= y)).filter (fun p => q p <= z) = S := by
    ext p
    simp only [S, Finset.mem_filter]
    exact Iff.intro (fun h => And.intro h.1.1 h.2)
      (fun h => And.intro (And.intro h.1 (h.2.trans hzy)) h.2)
  have hSplit : B.sum loss = S.sum loss + M.sum loss + T.sum loss := by
    have h1 := Finset.sum_filter_add_sum_filter_not B (fun p => q p <= y) loss
    have h2 := Finset.sum_filter_add_sum_filter_not (B.filter (fun p => q p <= y))
      (fun p => q p <= z) loss
    rw [hSmallSet] at h2
    change S.sum loss + M.sum loss = _ at h2
    change _ + T.sum loss = B.sum loss at h1
    rw [<- h1, <- h2]
  change B.sum loss <= 32 * A / (y * L)
  rw [hSplit]
  calc
    _ <= 16 * A / (y * L) + 8 * A / (y * L) + 8 * A / (y * L) :=
      add_le_add (add_le_add hSmall hMid) hLarge
    _ = _ := by ring

end Robin1984.GRH
