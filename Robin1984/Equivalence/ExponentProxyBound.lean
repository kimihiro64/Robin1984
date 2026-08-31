import Mathlib.NumberTheory.PrimeCounting
import Robin1984.Analytic.PrimeReferenceSign

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Complete exponent budget, including absent primes

The scalar cases below are summed over a full finite prime universe. No
distribution estimate or CA support assumption is introduced.
-/

namespace Robin1984

noncomputable section

def robinExponentLogProxy (H p : Real) (a : Nat) : Real :=
  if a = 0 then 0 else
    1 / p - (a : Real) * Real.log p / (H * Real.log H) - (Inv.inv p)^(a + 1)

theorem robin_absent_prime_cost {H p : Real} (hH : 2 <= H) (hp : 2 <= p) (hpH : p <= H / 2) :
    (Inv.inv p)^2 <= 1 / p - Real.log p / (H * Real.log H) := by
  have hHPos : 0 < H := by linarith
  have hpPos : 0 < p := by linarith
  have hpOne : 1 < p := by linarith
  have hHOne : 1 < H := by linarith
  have hLogH := Real.log_pos hHOne
  have hLogP := Real.log_pos hpOne
  have hLog : Real.log p <= Real.log H := Real.log_le_log hpPos (by linarith)
  have hSmall : Real.log p / (H * Real.log H) <= 1 / H := by
    have h := div_le_div_of_nonneg_right hLog (mul_nonneg hHPos.le hLogH.le)
    have hEq : Real.log H / (H * Real.log H) = 1 / H := by field_simp
    exact h.trans_eq hEq
  have hInv : 1 / H <= 1 / (2 * p) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hLast : (Inv.inv p)^2 <= 1 / p - 1 / (2 * p) := by
    have hInvP : 0 < Inv.inv p := inv_pos.mpr hpPos
    have hInvLe : Inv.inv p <= (1 / 2 : Real) := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) hp
    have hEq : 1 / p - 1 / (2 * p) = (1 / 2 : Real) * Inv.inv p := by ring
    rw [hEq]
    nlinarith
  linarith

/-- The a=0 branch is essential: omitted primes pay from the benchmark. -/
theorem robin_exponent_proxy_plus_cost_le_benchmark
    {H p : Real} (hH : 2 <= H) (hp : 2 <= p) (a : Nat) :
    robinExponentLogProxy H p a +
        (if p <= H / 2 then min (Real.log p / (H * Real.log H)) ((Inv.inv p)^2) else 0) <=
      (if p <= H then 1 / p - Real.log p / (H * Real.log H) else 0) := by
  have hpOne : 1 < p := by linarith
  have hHOne : 1 < H := by linarith
  have hLogP := Real.log_pos hpOne
  have hLogH := Real.log_pos hHOne
  have hCost : 0 <= Real.log p / (H * Real.log H) := by positivity
  have hPow : 0 <= (Inv.inv p)^(a + 1) := by positivity
  have hSigns := robin_prime_reference_atom_sign hpOne hHOne
  by_cases ha : a = 0
  . subst a
    rw [robinExponentLogProxy, if_pos rfl, zero_add]
    by_cases hpHalf : p <= H / 2
    . have hpFull : p <= H := by linarith
      rw [if_pos hpHalf, if_pos hpFull]
      exact (min_le_right _ _).trans (robin_absent_prime_cost hH hp hpHalf)
    . rw [if_neg hpHalf]
      split_ifs with hpFull
      . exact hSigns.1 hpFull
      . exact le_rfl
  . have haOne : 1 <= a := by omega
    have haReal : (1 : Real) <= a := by exact_mod_cast haOne
    unfold robinExponentLogProxy
    rw [if_neg ha]
    have hMul : (a : Real) * Real.log p / (H * Real.log H) =
        (a : Real) * (Real.log p / (H * Real.log H)) := by ring
    rw [hMul]
    by_cases hpHalf : p <= H / 2
    . have hpFull : p <= H := by linarith
      rw [if_pos hpHalf, if_pos hpFull]
      by_cases haEq : a = 1
      . subst a
        norm_num
        linarith [min_le_right (Real.log p / (H * Real.log H)) (Inv.inv (p^2))]
      . have haTwo : (2 : Real) <= a := by exact_mod_cast (show 2 <= a by omega)
        have hMin := min_le_left (Real.log p / (H * Real.log H)) ((Inv.inv p)^2)
        nlinarith
    . rw [if_neg hpHalf, add_zero]
      by_cases hpFull : p <= H
      . rw [if_pos hpFull]
        nlinarith
      . rw [if_neg hpFull]
        have hNeg := hSigns.2 (le_of_lt (lt_of_not_ge hpFull))
        nlinarith

theorem robin_complete_exponent_proxy_bound
    {H : Real} (hH : 2 <= H) (a : Nat -> Nat) (S : Finset Nat)
    (hPrime : forall p, Membership.mem S p -> Nat.Prime p)
    (hContains : forall p, Membership.mem (Nat.primesLE (Nat.floor H)) p -> Membership.mem S p) :
    Finset.sum S (fun p => robinExponentLogProxy H p (a p)) +
        Finset.sum (Nat.primesLE (Nat.floor (H / 2)))
          (fun p => min (Real.log p / (H * Real.log H)) ((Inv.inv (p : Real))^2)) <=
      Finset.sum (Nat.primesLE (Nat.floor H))
        (fun p => 1 / (p : Real) - Real.log p / (H * Real.log H)) := by
  classical
  have hHNonneg : 0 <= H := by linarith
  have hHalfNonneg : 0 <= H / 2 := by linarith
  have hSubset : Nat.primesLE (Nat.floor H) <= S := hContains
  have hHalfSubset : Nat.primesLE (Nat.floor (H / 2)) <= S :=
    (Nat.primesLE_mono (Nat.floor_mono (by linarith : H / 2 <= H))).trans hSubset
  have hSum := Finset.sum_le_sum (s := S) (fun p hp =>
    robin_exponent_proxy_plus_cost_le_benchmark (p := (p : Real)) hH
      (by exact_mod_cast (hPrime p hp).two_le) (a p))
  rw [Finset.sum_add_distrib] at hSum
  have hFilter (y : Real) (hy : 0 <= y)
      (hSub : Nat.primesLE (Nat.floor y) <= S) :
      S.filter (fun p : Nat => (p : Real) <= y) = Nat.primesLE (Nat.floor y) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    . intro hp
      exact And.intro (Nat.le_floor hp.2) (hPrime p hp.1)
    . intro hp
      exact And.intro (hSub (Nat.mem_primesLE.mpr hp)) ((Nat.le_floor_iff hy).mp hp.1)
  rw [<- Finset.sum_filter, <- Finset.sum_filter,
    hFilter (H / 2) hHalfNonneg hHalfSubset, hFilter H hHNonneg hSubset] at hSum
  exact hSum

end

end Robin1984
