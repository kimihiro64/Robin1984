import Robin1984.Analytic.PrimeProductBlocks

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Exact prime-product block 104

This retained block covers the integer interval `[70656, 70850)`. It stores
the products over primes in its interval of `p^2 - 1`, `p * (p - 1)`, and `p`.

The accompanying `decide +kernel` theorem checks its size and upper bound and
recomputes all three products using the bounded primality test. This is the
last block required by the final retained finite row.
-/

namespace Robin1984

def robinPrimeBlock104 : RobinPrimeProductBlock where
  start := 70656
  count := 194
  numerator := 31059378815049261166136252100015455884952016469660154276989567796329326188226926131802745178234205917614928739206165372256673435817724608512000000
  denominator := 31052794731237544418230390214562503941075441560042207030828871282179457543462546664654401622037826775506939716049837082858959974806694359665213440
  baseProduct := 5573094195159301989389050795209219452063699298248616131099583109157281969

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinPrimeBlock104_checks : RobinPrimeProductBlockChecks robinPrimeBlock104 := by
  decide +kernel

end Robin1984
