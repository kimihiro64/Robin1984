import Robin1984.Analytic.PrimeProductBlocks
import Robin1984.Equivalence.ReducedProductChecks
import Robin1984.Finite.Certificates.PrimeBlocks00
import Robin1984.Finite.Certificates.PrimeBlocks01
import Robin1984.Finite.FiniteRowCertificate
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 08

This row covers the log-height interval
`[464815043 / 1000000, 130165559 / 200000]`. It uses 11 cutoff thresholds, beginning at
`557`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow08 : RobinFiniteRow where
  lo := (464815043 / 1000000)
  hi := (130165559 / 200000)
  lambda := (70868018799 / 250000000000000)
  gainUpper := (11213775422259 / 1000000000000)
  heightMantissa := (31050297113955205021 / 18446744073709551616)
  logLoLower := (383852473 / 62500000)
  logHiLower := (3239122541 / 500000000)
  heightExponent := 811
  cuts := [557, 31, 11, 6, 4, 3, 2, 2, 2, 2, 2]

def robinFiniteRow08Blocks : List RobinPrimeProductBlock := [
  robinPrimeBlock000,
  robinPrimeBlock001,
  robinPrimeBlock002,
  robinPrimeBlock003,
  robinPrimeBlock004,
  robinPrimeBlock005,
  robinPrimeBlock006,
  robinPrimeBlock007,
  robinPrimeBlock008]

theorem robinFiniteRow08Blocks_checks :
    forall b, Membership.mem robinFiniteRow08Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow08Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb
  all_goals subst b
  . exact robinPrimeBlock000_checks
  . exact robinPrimeBlock001_checks
  . exact robinPrimeBlock002_checks
  . exact robinPrimeBlock003_checks
  . exact robinPrimeBlock004_checks
  . exact robinPrimeBlock005_checks
  . exact robinPrimeBlock006_checks
  . exact robinPrimeBlock007_checks
  . exact robinPrimeBlock008_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow08_products : RobinFiniteProductChecks robinFiniteRow08 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 557) (tail := [31, 11, 6, 4, 3, 2, 2, 2, 2, 2]) (bs := robinFiniteRow08Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow08Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow08_checks : RobinFiniteRowChecks robinFiniteRow08 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow08_products
    . decide +kernel

end Robin1984
