import Robin1984.Arithmetic.Definitions

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Sound factor certificates for finite Robin startup arithmetic

A row records a prime-power factorization.  Pairwise coprimality is checked
against the complete remaining product, so multiplicativity of `sigma` proves
the represented divisor sum with no divisor enumeration.
-/

namespace Robin1984

abbrev StartupPrimePower := Prod Nat Nat

def startupFactorProduct : List StartupPrimePower -> Nat
  | [] => 1
  | pa :: tail => pa.1 ^ pa.2 * startupFactorProduct tail

def startupFactorSigma : List StartupPrimePower -> Nat
  | [] => 1
  | pa :: tail =>
      (Finset.range (pa.2 + 1)).sum (fun exponent => pa.1 ^ exponent) *
        startupFactorSigma tail

def StartupFactorsValid : List StartupPrimePower -> Prop
  | [] => True
  | pa :: tail =>
      And pa.1.Prime
        (And (Nat.Coprime (pa.1 ^ pa.2) (startupFactorProduct tail))
          (StartupFactorsValid tail))

theorem sigmaOneNat_startupFactorProduct_eq_startupFactorSigma
    (factors : List StartupPrimePower)
    (hValid : StartupFactorsValid factors) :
    Robin1984.Core.sigmaOneNat (startupFactorProduct factors) =
      startupFactorSigma factors := by
  induction factors with
  | nil =>
      simp [startupFactorProduct, startupFactorSigma,
        Robin1984.Core.sigmaOneNat,
        ArithmeticFunction.sigma_one]
  | cons pa tail ih =>
      have hp : pa.1.Prime := hValid.1
      have hCoprime :
          Nat.Coprime (pa.1 ^ pa.2) (startupFactorProduct tail) :=
        hValid.2.1
      have hTailValid : StartupFactorsValid tail := hValid.2.2
      have hTail := ih hTailValid
      unfold startupFactorProduct startupFactorSigma
      unfold Robin1984.Core.sigmaOneNat at hTail
      unfold Robin1984.Core.sigmaOneNat
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        hCoprime]
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
      rw [hTail]

def StartupFactorRowsValid
    (first : Nat) : List (List StartupPrimePower) -> Prop
  | [] => True
  | factors :: rows =>
      And (StartupFactorsValid factors)
        (And (startupFactorProduct factors = first)
          (And (35 * startupFactorSigma factors <= 127 * first)
            (StartupFactorRowsValid (first + 1) rows)))

theorem sigmaOneNat_le_127_div_35_of_startupFactorRowsValid
    {first n : Nat} {rows : List (List StartupPrimePower)}
    (hRows : StartupFactorRowsValid first rows)
    (hLower : first <= n) (hUpper : n < first + rows.length) :
    35 * Robin1984.Core.sigmaOneNat n <= 127 * n := by
  induction rows generalizing first n with
  | nil => simp at hUpper; omega
  | cons factors tail ih =>
      by_cases hEq : n = first
      case pos =>
        subst n
        have hSigma :=
          sigmaOneNat_startupFactorProduct_eq_startupFactorSigma
            factors hRows.1
        rw [hRows.2.1] at hSigma
        rw [hSigma]
        exact hRows.2.2.1
      case neg =>
        apply ih hRows.2.2.2
        . omega
        . simp only [List.length_cons] at hUpper
          omega


end Robin1984
