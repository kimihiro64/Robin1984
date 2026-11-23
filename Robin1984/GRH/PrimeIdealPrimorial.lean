import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Nat.Log
import Robin1984.GRH.IdealDivisorEuler
import Robin1984.GRH.PrimeIdealChebyshev

/-!
# The prime-power cutoff ideal

The product of prime ideals indexed by all prime powers below a cutoff
has logarithmic norm equal to the Dedekind Chebyshev function.
The multiplicity of a prime is the integer logarithm of the cutoff.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The number-field analogue of the least common multiple of the integers up to a cutoff.
- Formalization note: Project the exact finite prime-power support onto a multiset of prime ideals and count each fiber by an exponent interval.
- PROVENANCE-END
-/

open IsDedekindDomain NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)

/-- Prime ideals with repetitions indexed by the powers of bounded norm. -/
noncomputable def cutoffPrimeMultiplicities (n : Nat) : Multiset P :=
  (primePowersUpTo K n).val.map Prod.fst

/-- The product of all prime ideals with their cutoff multiplicities. -/
noncomputable def primePowerCutoffIdeal (n : Nat) : Ideal (RingOfIntegers K) :=
  (primeMultisetIdealEquiv (cutoffPrimeMultiplicities K n)).val

theorem primePowerCutoffIdeal_ne_zero (n : Nat) : Not (primePowerCutoffIdeal K n = 0) :=
  (primeMultisetIdealEquiv (cutoffPrimeMultiplicities K n)).property

/-- The logarithmic norm of the cutoff ideal is the actual Chebyshev sum
at the same cutoff. -/
theorem log_absNorm_primePowerCutoffIdeal (x : Real) :
    Real.log (Ideal.absNorm (primePowerCutoffIdeal K (Nat.floor x)) : Real) =
      dedekindChebyshev K x := by
  classical
  unfold primePowerCutoffIdeal cutoffPrimeMultiplicities dedekindChebyshev
  rw [primeMultisetIdealEquiv_apply_val, map_multiset_prod, Multiset.map_map, Multiset.map_map]
  change Real.log ((((primePowersUpTo K (Nat.floor x)).val.map
    (fun pn => dedekindPrimeNorm K pn.1)).prod : Nat) : Real) = _
  rw [Finset.prod_map_val, Nat.cast_prod]
  exact Real.log_prod (fun pn _ =>
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_one.trans (one_lt_dedekindPrimeNorm K pn.1))))

/-- A prime occurs once for each predecessor exponent below the integer
logarithm of the cutoff in that prime's norm. -/
theorem count_cutoffPrimeMultiplicities [DecidableEq P] {n : Nat} (hn : Not (n = 0)) (p : P) :
    (cutoffPrimeMultiplicities K n).count p = Nat.log (dedekindPrimeNorm K p) n := by
  classical
  unfold cutoffPrimeMultiplicities
  rw [Multiset.count_map]
  let powers := primePowersUpTo K n
  let fiber := powers.filter (fun pn => p = pn.1)
  change fiber.card = Nat.log (dedekindPrimeNorm K p) n
  rw [<- Finset.card_range (Nat.log (dedekindPrimeNorm K p) n)]
  refine Finset.card_bij (fun pn _ => pn.2) ?membership ?injective ?surjective
  case membership =>
    intro pn hpn
    have hp := Finset.mem_filter.mp hpn
    have hpow : dedekindPrimeNorm K p ^ (pn.2 + 1) <= n := by
      have hNorm := (mem_primePowersUpTo K).mp hp.1
      simpa only [dedekindPrimePowerNorm, hp.2] using hNorm
    exact Finset.mem_range.mpr
      (Nat.lt_of_succ_le ((Nat.le_log_iff_pow_le (one_lt_dedekindPrimeNorm K p) hn).mpr hpow))
  case injective =>
    intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2) hab
  case surjective =>
    intro j hj
    have hj' := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hpow := (Nat.le_log_iff_pow_le (one_lt_dedekindPrimeNorm K p) hn).mp hj'
    exact Exists.intro (p, j) (Exists.intro
      (Finset.mem_filter.mpr (And.intro ((mem_primePowersUpTo K).mpr hpow) rfl)) rfl)

/-- The prime support of the cutoff ideal is exactly the primes whose
own norm lies below the cutoff. -/
theorem mem_cutoffPrimeMultiplicities_toFinset [DecidableEq P] {n : Nat}
    (hn : Not (n = 0)) (p : P) :
    Iff (Membership.mem (cutoffPrimeMultiplicities K n).toFinset p)
      (dedekindPrimeNorm K p <= n) := by
  rw [Multiset.mem_toFinset, <- Multiset.count_pos, count_cutoffPrimeMultiplicities K hn]
  exact Iff.intro (fun h => (Nat.log_pos_iff.mp h).1)
    (Nat.log_pos (one_lt_dedekindPrimeNorm K p))

/-- The divisor ratio of the cutoff ideal, expressed by truncated
geometric factors with their exact exponents. -/
theorem cutoffIdeal_divisorRatio_eq_product [DecidableEq P] {n : Nat} (hn : Not (n = 0)) :
    (idealDivisorNormSum (primePowerCutoffIdeal K n) (primePowerCutoffIdeal_ne_zero K n) : Real) /
        (Ideal.absNorm (primePowerCutoffIdeal K n) : Real) =
      (cutoffPrimeMultiplicities K n).toFinset.prod (fun p =>
        (1 - (Inv.inv (dedekindPrimeNorm K p : Real)) ^ (Nat.log (dedekindPrimeNorm K p) n + 1)) /
          (1 - Inv.inv (dedekindPrimeNorm K p : Real))) := by
  classical
  unfold primePowerCutoffIdeal
  rw [idealDivisorNormSum_div_primeMultiset K]
  apply Finset.prod_congr rfl
  intro p _
  rw [count_cutoffPrimeMultiplicities K hn]
  have hq : (1 : Real) < dedekindPrimeNorm K p := by
    exact_mod_cast one_lt_dedekindPrimeNorm K p
  have hr : Inv.inv (dedekindPrimeNorm K p : Real) < 1 := by
    simpa only [one_div, inv_one] using one_div_lt_one_div_of_lt (zero_lt_one : (0 : Real) < 1) hq
  let r : Real := Inv.inv (dedekindPrimeNorm K p : Real)
  let m := Nat.log (dedekindPrimeNorm K p) n + 1
  change (Finset.range m).sum (fun k => r ^ k) = (1 - r ^ m) / (1 - r)
  calc
    _ = (r ^ m - 1) / (r - 1) := geom_sum_eq (ne_of_lt hr) m
    _ = (-(r ^ m - 1)) / (-(r - 1)) := (neg_div_neg_eq _ _).symm
    _ = _ := by rw [neg_sub, neg_sub]

end Robin1984.GRH
