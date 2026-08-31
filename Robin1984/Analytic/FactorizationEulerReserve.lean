import Robin1984.ColossallyAbundant.CAProfile
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 analytic implication supplies the surrounding mathematical target.
- Formalization note: The exact coefficient normalization, explicit cutoff choices, and proof interfaces in this module are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Euler-factor saturation and reserve for integer factorizations

The saturated potential records the full Euler factor for every prime already
present in an actual factorization packet.  The tower reserve records the
unspent tail above each current exponent.  Their difference is exactly the
logarithm of the abundancy ratio.  These exact identities retain every
prime-power layer and are used when comparing `lcmUpto` with the Nicolas
oscillation function.
-/

namespace Robin1984

noncomputable section

/-- Full Euler-factor potential of the prime support of `n`. -/
def factorizationEulerSaturation (n : Nat) : Real :=
  n.factorization.sum (fun p _ => primeTowerTopCorrection p 0)

/-- Unspent Euler-factor tail above the current exponent of each prime in `n`. -/
def factorizationTowerReserve (n : Nat) : Real :=
  n.factorization.sum (fun p k => primeTowerTopCorrection p k)


/-- The saturated Euler potential splits exactly into current log-abundancy
and the remaining higher-layer tower reserve. -/
theorem factorizationEulerSaturation_eq_log_abundancy_add_reserve
    {n : Nat} (hn : n ≠ 0) :
    factorizationEulerSaturation n =
      Real.log (abundancy n) + factorizationTowerReserve n := by
  have hAbundancy :=
    factorization_primeTowerTopCorrection_sum_eq_log_abundancy (n := n) hn
  unfold factorizationEulerSaturation factorizationTowerReserve
  rw [← hAbundancy]
  rw [Finsupp.sum, Finsupp.sum, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Every prime tower has nonnegative unspent Euler reserve. -/
theorem primeTowerTopCorrection_nonneg
    {p k : Nat} (hpPrime : Nat.Prime p) :
    0 ≤ primeTowerTopCorrection p k := by
  have hpReal : 1 < (p : Real) := by
    exact_mod_cast hpPrime.one_lt
  have hArgPos :
      0 < 1 - (p : Real) ^ (-(k + 1 : Int)) :=
    one_sub_prime_zpow_neg_pos (p := p) hpReal
      (j := k + 1) (Nat.succ_pos k)
  have hPowNonneg :
      0 ≤ (p : Real) ^ (-(k + 1 : Int)) :=
    zpow_nonneg (by exact_mod_cast hpPrime.pos.le) _
  unfold primeTowerTopCorrection
  exact neg_nonneg.mpr
    (Real.log_nonpos (le_of_lt hArgPos) (sub_le_self 1 hPowNonneg))

/-- The total unspent tower reserve of a nonzero integer is nonnegative. -/
theorem factorizationTowerReserve_nonneg (n : Nat) :
    0 ≤ factorizationTowerReserve n := by
  unfold factorizationTowerReserve
  apply Finsupp.sum_nonneg
  intro p hp
  have hpPrime : Nat.Prime p :=
    Nat.prime_of_mem_primeFactors (by
      simpa [Nat.support_factorization] using hp)
  exact primeTowerTopCorrection_nonneg hpPrime


end

end Robin1984
