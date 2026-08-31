import Robin1984.Equivalence.ReducedProductChecks
import Robin1984.Finite.Certificates.PrimeBlocks00
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 04

This row covers the log-height interval
`[47544747 / 500000, 146801491 / 1000000]`. It uses 8 cutoff thresholds, beginning at
`120`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow04 : RobinFiniteRow where
  lo := (47544747 / 500000)
  hi := (146801491 / 1000000)
  lambda := (1724212981141 / 1000000000000000)
  gainUpper := (1700882877263 / 200000000000)
  heightMantissa := (24680549958221430113 / 18446744073709551616)
  logLoLower := (4554818489 / 1000000000)
  logHiLower := (4989081271 / 1000000000)
  heightExponent := 182
  cuts := [120, 14, 6, 4, 3, 2, 2, 2]

def robinFiniteRow04Blocks : List RobinPrimeProductBlock := [
  robinPrimeBlock000,
  robinPrimeBlock001,
  robinPrimeBlock002,
  robinPrimeBlock003,
  robinPrimeBlock004]

theorem robinFiniteRow04Blocks_checks :
    forall b, Membership.mem robinFiniteRow04Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow04Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb
  all_goals subst b
  . exact robinPrimeBlock000_checks
  . exact robinPrimeBlock001_checks
  . exact robinPrimeBlock002_checks
  . exact robinPrimeBlock003_checks
  . exact robinPrimeBlock004_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow04_products : RobinFiniteProductChecks robinFiniteRow04 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 120) (tail := [14, 6, 4, 3, 2, 2, 2]) (bs := robinFiniteRow04Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow04Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow04_checks : RobinFiniteRowChecks robinFiniteRow04 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow04_products
    . decide +kernel

end Robin1984
