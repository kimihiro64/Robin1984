import Robin1984.ColossallyAbundant.CAProfile
import Robin1984.Equivalence.ExponentProxyBound
import Robin1984.NicolasLandau.MertensWeightedBound
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann (1984).
- Formalization note: The retained statement or source-level argument is Robin's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# The complete exponent budget for an integer factorization

Each prime-power contribution to `log (sigma(n) / n)` is bounded by a
Mertens term minus an exponent-dependent cost. Summing over the actual
factorization first yields an exact-support proxy; extending to the complete
prime universe produces the prime-cost inequality used at large height.
-/

namespace Robin1984

noncomputable section

theorem robin_mertens_summand_sum_lower (S : Finset Nat) :
    Mertens.M - Real.eulerMascheroniConstant <= Finset.sum S Mertens.M_eq_summand := by
  have h := Mertens.M_eq_summable.neg.sum_le_tsum S
    (fun p _ => neg_nonneg.mpr (robin_mertens_summand_nonpos p))
  simp only [Finset.sum_neg_distrib, tsum_neg, Mertens.tsum_M_eq_summand_eq,
    Mertens.gamma_eq_eulerMascheroni] at h
  linarith

theorem robin_prime_factor_gain_le {p : Nat} (hp : Nat.Prime p) (a : Nat) :
    primeTowerTopCorrection p 0 - primeTowerTopCorrection p a <=
      1 / (p : Real) - (Inv.inv (p : Real))^(a + 1) - Mertens.M_eq_summand p := by
  have hpOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hPow : (p : Real)^(-(a + 1 : Int)) = (Inv.inv (p : Real))^(a + 1) := by
    rw [zpow_neg, show (a : Int) + 1 = ((a + 1 : Nat) : Int) by omega,
      zpow_natCast, <- inv_pow]
  have hNext : 0 < 1 - (Inv.inv (p : Real))^(a + 1) := by
    rw [<- hPow]
    exact one_sub_prime_zpow_neg_pos hpOne (by omega : 0 < a + 1)
  have hLog := Real.log_le_sub_one_of_pos hNext
  have hTop : primeTowerTopCorrection p a = -Real.log (1 - (Inv.inv (p : Real))^(a + 1)) := by
    unfold primeTowerTopCorrection
    rw [hPow]
  have hZero : primeTowerTopCorrection p 0 = -Real.log (1 - 1 / (p : Real)) := by
    norm_num [primeTowerTopCorrection, one_div]
  rw [hZero, hTop]
  simp only [Mertens.M_eq_summand, if_pos hp]
  linarith

theorem robin_log_abundancy_le_actual_proxy {n : Nat} (hn : Not (n = 0)) (H : Real) :
    Real.log (abundancy n) <= Real.eulerMascheroniConstant - Mertens.M +
      Finset.sum n.factorization.support (fun p => robinExponentLogProxy H p (n.factorization p)) +
        Real.log (n : Real) / (H * Real.log H) := by
  classical
  have hPrime (p : Nat) (hp : Membership.mem n.factorization.support p) : Nat.Prime p :=
    Nat.prime_of_mem_primeFactors (by simpa only [Nat.support_factorization] using hp)
  have hGain := Finset.sum_le_sum (s := n.factorization.support)
    (fun p hp => robin_prime_factor_gain_le (hPrime p hp) (n.factorization p))
  have hGainEq := factorization_primeTowerTopCorrection_sum_eq_log_abundancy hn
  rw [Finsupp.sum] at hGainEq
  rw [hGainEq, Finset.sum_sub_distrib] at hGain
  have hM := robin_mertens_summand_sum_lower n.factorization.support
  have hHeight : Finset.sum n.factorization.support
      (fun p => (n.factorization p : Real) * Real.log p / (H * Real.log H)) =
        Real.log (n : Real) / (H * Real.log H) := by
    rw [<- Finset.sum_div, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have hProxy : Finset.sum n.factorization.support (fun p => robinExponentLogProxy H p (n.factorization p)) =
      Finset.sum n.factorization.support (fun p => 1 / (p : Real) - (Inv.inv (p : Real))^(n.factorization p + 1)) -
        Real.log (n : Real) / (H * Real.log H) := by
    rw [<- hHeight, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hNe : Not (n.factorization p = 0) := Finsupp.mem_support_iff.mp hp
    rw [robinExponentLogProxy, if_neg hNe]
    ring
  linarith

theorem robin_log_abundancy_le_complete_prime_cost
    (hRH : RiemannHypothesis) {n : Nat} (hn : Not (n = 0))
    (hH : 20000 <= Real.log (n : Real)) :
    Real.log (abundancy n) - Real.eulerMascheroniConstant -
        Real.log (Real.log (Real.log (n : Real))) <=
      robinMertensWeightedScalar (Real.log (n : Real)) -
        Finset.sum (Nat.primesLE (Nat.floor (Real.log (n : Real) / 2)))
          (fun p => min (Real.log p / (Real.log (n : Real) * Real.log (Real.log (n : Real))))
            ((Inv.inv (p : Real))^2)) := by
  classical
  let H : Real := Real.log (n : Real)
  let S : Finset Nat := Union.union n.factorization.support (Nat.primesLE (Nat.floor H))
  have hHTwo : 2 <= H := by dsimp [H]; linarith
  have hPrime (p : Nat) (hp : Membership.mem S p) : Nat.Prime p := by
    rcases Finset.mem_union.mp hp with hLeft | hRight
    . exact Nat.prime_of_mem_primeFactors (by simpa only [Nat.support_factorization] using hLeft)
    . exact Nat.prime_of_mem_primesLE hRight
  have hContains : forall p, Membership.mem (Nat.primesLE (Nat.floor H)) p -> Membership.mem S p :=
    fun p hp => Finset.mem_union_right _ hp
  have hProxy := robin_complete_exponent_proxy_bound hHTwo n.factorization S hPrime hContains
  have hSubset : n.factorization.support <= S := Finset.subset_union_left
  have hSumEq : Finset.sum n.factorization.support (fun p => robinExponentLogProxy H p (n.factorization p)) =
      Finset.sum S (fun p => robinExponentLogProxy H p (n.factorization p)) := by
    apply Finset.sum_subset hSubset
    intro p _ hp
    have hZero : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    rw [robinExponentLogProxy, hZero, if_pos rfl]
  rw [<- hSumEq] at hProxy
  have hArithmetic := robin_log_abundancy_le_actual_proxy hn H
  have hPrimeSum := nicolasPrimeReciprocalSum_eq hHTwo
  rw [robin_theta_tail_eq_psi_sub_prime_power hHTwo] at hPrimeSum
  unfold nicolasThetaError at hPrimeSum
  have hTail := robin_prime_power_sub_psi_tail_le_scalar hRH hH
  rw [Finset.sum_sub_distrib, <- Finset.sum_div, <- Chebyshev.theta_eq_sum_primesLE] at hProxy
  simp only [sub_div] at hPrimeSum
  change Real.log (abundancy n) - Real.eulerMascheroniConstant - Real.log (Real.log H) <=
    robinMertensWeightedScalar H -
      Finset.sum (Nat.primesLE (Nat.floor (H / 2)))
        (fun p => min (Real.log p / (H * Real.log H)) ((Inv.inv (p : Real))^2))
  change robinPrimePowerWeightedTail 1 H - robinPsiWeightedErrorIntegral 1 H <=
    robinMertensWeightedScalar H at hTail
  change Real.log (abundancy n) <= Real.eulerMascheroniConstant - Mertens.M +
    Finset.sum n.factorization.support (fun p => robinExponentLogProxy H p (n.factorization p)) +
      H / (H * Real.log H) at hArithmetic
  linarith

end

end Robin1984
