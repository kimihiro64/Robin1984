import Robin1984.GRH.DedekindEulerProduct

/-!
# The prime-ideal Chebyshev function

Every bounded norm range contains finitely many prime powers. The
Chebyshev function sums the logarithm of the underlying prime-ideal
norm over these powers, counting prime ideals of the same norm separately.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Chebyshev function for prime ideals in the logarithmic derivative of Dedekind zeta.
- Formalization note: The finite range follows from bounded ideal norm and bounded exponent. A pointwise tsum formula permits integration of the step functions.
- PROVENANCE-END
-/

open IsDedekindDomain NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)

/-- The norm of the prime power indexed by a prime ideal and its
predecessor exponent. -/
noncomputable def dedekindPrimePowerNorm (pn : Prod P Nat) : Nat :=
  dedekindPrimeNorm K pn.1 ^ (pn.2 + 1)

private theorem succ_le_pow_succ (q : Nat) (hq : 1 < q) (n : Nat) :
    n + 1 <= q ^ (n + 1) := by
  induction n with
  | zero => simpa using hq.le
  | succ n ih =>
    have hPos : 1 <= q ^ (n + 1) :=
      Nat.succ_le_of_lt (pow_pos ((zero_lt_one : 0 < (1 : Nat)).trans hq) _)
    calc
      (n + 1) + 1 <= q ^ (n + 1) + q ^ (n + 1) := Nat.add_le_add ih hPos
      _ = q ^ (n + 1) * 2 := (mul_two _).symm
      _ <= q ^ (n + 1) * q := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hq)
      _ = q ^ ((n + 1) + 1) := (pow_succ _ _).symm

private theorem finite_primeNorm_le (n : Nat) :
    Set.Finite {p : P | dedekindPrimeNorm K p <= n} := by
  have h : Function.Injective (fun p : P => p.asIdeal) :=
    fun _ _ hEq => HeightOneSpectrum.ext hEq
  exact (Ideal.finite_setOfPred_absNorm_le n).preimage h.injOn

/-- The exact finite support of the prime powers with norm bounded by
an integer cutoff. -/
theorem finite_primePowerNorm_le (n : Nat) :
    Set.Finite {pn : Prod P Nat | dedekindPrimePowerNorm K pn <= n} := by
  have hExp : Set.Finite (Set.Iic n) := Set.finite_Iic n
  refine ((finite_primeNorm_le K n).prod hExp).subset ?_
  intro pn hpn
  change dedekindPrimeNorm K pn.1 ^ (pn.2 + 1) <= n at hpn
  have hq := one_lt_dedekindPrimeNorm K pn.1
  have hPow : dedekindPrimeNorm K pn.1 <= dedekindPrimeNorm K pn.1 ^ (pn.2 + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq.le (Nat.succ_pos pn.2)
  exact And.intro (hPow.trans hpn)
    ((Nat.le_succ pn.2).trans ((succ_le_pow_succ _ hq _).trans hpn))

/-- Prime powers whose norm is at most `n`. -/
noncomputable def primePowersUpTo (n : Nat) : Finset (Prod P Nat) :=
  (finite_primePowerNorm_le K n).toFinset

theorem mem_primePowersUpTo {n : Nat} {pn : Prod P Nat} :
    Iff (Membership.mem (primePowersUpTo K n) pn) (dedekindPrimePowerNorm K pn <= n) :=
  (finite_primePowerNorm_le K n).mem_toFinset

/-- The Dedekind Chebyshev function sums `log(N p)` over individual
prime ideal powers whose norm is at most the real argument. -/
noncomputable def dedekindChebyshev (x : Real) : Real :=
  (primePowersUpTo K (Nat.floor x)).sum (fun pn => Real.log (dedekindPrimeNorm K pn.1 : Real))

theorem dedekindChebyshev_eq_tsum {x : Real} (hx : 0 <= x) :
    dedekindChebyshev K x =
      tsum (fun pn : Prod P Nat => if (dedekindPrimePowerNorm K pn : Real) <= x then
        Real.log (dedekindPrimeNorm K pn.1 : Real) else 0) := by
  classical
  unfold dedekindChebyshev
  symm
  calc
    _ = (primePowersUpTo K (Nat.floor x)).sum
        (fun pn => if (dedekindPrimePowerNorm K pn : Real) <= x then
          Real.log (dedekindPrimeNorm K pn.1 : Real) else 0) := by
      apply tsum_eq_sum
      intro pn hpn
      have h : Not ((dedekindPrimePowerNorm K pn : Real) <= x) := by
        intro hNorm
        exact hpn ((mem_primePowersUpTo K).mpr ((Nat.le_floor_iff hx).mpr hNorm))
      rw [if_neg h]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pn hpn
      rw [if_pos ((Nat.le_floor_iff hx).mp ((mem_primePowersUpTo K).mp hpn))]

end Robin1984.GRH
