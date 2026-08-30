import Robin1984.Analytic.PrimeProductBlocks
import Robin1984.Equivalence.ReducedProductChecks
import Robin1984.Finite.Certificates.PrimeBlocks00
import Robin1984.Finite.FiniteRowCertificate
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 05

This row covers the log-height interval
`[146801491 / 1000000, 111686563 / 500000]`. It uses 9 cutoff thresholds, beginning at
`184`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow05 : RobinFiniteRow where
  lo := (146801491 / 1000000)
  hi := (111686563 / 500000)
  lambda := (8278925801 / 8000000000000)
  gainUpper := (4630388083099 / 500000000000)
  heightMantissa := (12659228613027413269 / 9223372036854775808)
  logLoLower := (4989081271 / 1000000000)
  logHiLower := (2704421791 / 500000000)
  heightExponent := 277
  cuts := [184, 17, 7, 4, 3, 2, 2, 2, 2]

def robinFiniteRow05Blocks : List RobinPrimeProductBlock := [
  robinPrimeBlock000,
  robinPrimeBlock001,
  robinPrimeBlock002,
  robinPrimeBlock003,
  robinPrimeBlock004,
  robinPrimeBlock005]

theorem robinFiniteRow05Blocks_checks :
    forall b, Membership.mem robinFiniteRow05Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow05Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb
  all_goals subst b
  . exact robinPrimeBlock000_checks
  . exact robinPrimeBlock001_checks
  . exact robinPrimeBlock002_checks
  . exact robinPrimeBlock003_checks
  . exact robinPrimeBlock004_checks
  . exact robinPrimeBlock005_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow05_products : RobinFiniteProductChecks robinFiniteRow05 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 184) (tail := [17, 7, 4, 3, 2, 2, 2, 2]) (bs := robinFiniteRow05Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow05Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow05_checks : RobinFiniteRowChecks robinFiniteRow05 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow05_products
    . decide +kernel

end Robin1984
