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
# Finite Robin certificate row 13

This row covers the log-height interval
`[2035337871 / 1000000, 518900301 / 200000]`. It uses 13 cutoff thresholds, beginning at
`2314`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow13 : RobinFiniteRow where
  lo := (2035337871 / 1000000)
  hi := (518900301 / 200000)
  lambda := (11152011487 / 200000000000000)
  gainUpper := (13784169975911 / 1000000000000)
  heightMantissa := (29021999988660336459 / 18446744073709551616)
  logLoLower := (7618417113 / 1000000000)
  logHiLower := (7861149677 / 1000000000)
  heightExponent := 3373
  cuts := [2314, 65, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2]

def robinFiniteRow13Blocks : List RobinPrimeProductBlock := [
  robinPrimeBlock000,
  robinPrimeBlock001,
  robinPrimeBlock002,
  robinPrimeBlock003,
  robinPrimeBlock004,
  robinPrimeBlock005,
  robinPrimeBlock006,
  robinPrimeBlock007,
  robinPrimeBlock008,
  robinPrimeBlock009,
  robinPrimeBlock010,
  robinPrimeBlock011,
  robinPrimeBlock012,
  robinPrimeBlock013,
  robinPrimeBlock014,
  robinPrimeBlock015]

theorem robinFiniteRow13Blocks_checks :
    forall b, Membership.mem robinFiniteRow13Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow13Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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
  . exact robinPrimeBlock009_checks
  . exact robinPrimeBlock010_checks
  . exact robinPrimeBlock011_checks
  . exact robinPrimeBlock012_checks
  . exact robinPrimeBlock013_checks
  . exact robinPrimeBlock014_checks
  . exact robinPrimeBlock015_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow13_products : RobinFiniteProductChecks robinFiniteRow13 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 2314) (tail := [65, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2]) (bs := robinFiniteRow13Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow13Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow13_checks : RobinFiniteRowChecks robinFiniteRow13 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow13_products
    . decide +kernel

end Robin1984
