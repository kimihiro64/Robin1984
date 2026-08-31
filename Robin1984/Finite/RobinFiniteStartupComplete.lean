import Robin1984.Finite.RobinFiniteStartupCATangent7560
import Robin1984.Finite.RobinFiniteStartupFactorCertificateLengths
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Complete finite Robin startup

The exact factor certificates cover `5041 <= n < 7560`.  The common CA
tangent covers `7560 <= n < 720720`.  Together they prove Robin's inequality
throughout the finite startup interval.
-/

namespace Robin1984

theorem sigmaOneNat_startup_5041_to_7560_le_127_div_35
    {n : Nat} (hLower : 5041 <= n) (hUpper : n < 7560) :
    35 * Robin1984.Core.sigmaOneNat n <= 127 * n := by
  by_cases hFirst : n < 5077
  . apply sigmaOneNat_le_127_div_35_of_startupFactorRowsValid
      startupFactorRows5041To5077_valid hLower
    rw [startupFactorRows5041To5077_length]
    omega
  by_cases hSecond : n < 6101
  . apply sigmaOneNat_le_127_div_35_of_startupFactorRowsValid
      startupFactorRows5077To6101_valid (by omega)
    rw [startupFactorRows5077To6101_length]
    omega
  by_cases hThird : n < 7125
  . apply sigmaOneNat_le_127_div_35_of_startupFactorRowsValid
      startupFactorRows6101To7125_valid (by omega)
    rw [startupFactorRows6101To7125_length]
    omega
  . apply sigmaOneNat_le_127_div_35_of_startupFactorRowsValid
      startupFactorRows7125To7560_valid (by omega)
    rw [startupFactorRows7125To7560_length]
    omega

/-- Every integer in the finite startup interval satisfies Robin's
inequality. -/
theorem nativeRobinInequality_finite_startup
    {n : Nat} (hLower : 5040 < n) (hUpper : n < 720720) :
    Robin1984.Core.NativeRobinInequality n := by
  by_cases hSplit : n < 7560
  . apply nativeRobinInequality_of_sigmaOneNat_le_127_div_35 (by omega)
    exact sigmaOneNat_startup_5041_to_7560_le_127_div_35
      (by omega) hSplit
  . exact nativeRobinInequality_startup_from_7560 (by omega) hUpper

end Robin1984
