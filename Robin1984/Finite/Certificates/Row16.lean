import Robin1984.Analytic.PrimeProductBlocks
import Robin1984.Equivalence.ReducedProductChecks
import Robin1984.Finite.Certificates.PrimeBlocks00
import Robin1984.Finite.Certificates.PrimeBlocks01
import Robin1984.Finite.Certificates.PrimeBlocks02
import Robin1984.Finite.FiniteRowCertificate
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 16

This row covers the log-height interval
`[406392661 / 100000, 1248690297 / 250000]`. It uses 14 cutoff thresholds, beginning at
`4528`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow16 : RobinFiniteRow where
  lo := (406392661 / 100000)
  hi := (1248690297 / 250000)
  lambda := (2622639723 / 100000000000000)
  gainUpper := (7493566089191 / 500000000000)
  heightMantissa := (32862165079507178585 / 18446744073709551616)
  logLoLower := (8309904929 / 1000000000)
  logHiLower := (4258072439 / 500000000)
  heightExponent := 6593
  cuts := [4528, 91, 22, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2]

def robinFiniteRow16Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock015,
  robinPrimeBlock016,
  robinPrimeBlock017,
  robinPrimeBlock018,
  robinPrimeBlock019,
  robinPrimeBlock020]

theorem robinFiniteRow16Blocks_checks :
    forall b, Membership.mem robinFiniteRow16Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow16Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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
  . exact robinPrimeBlock016_checks
  . exact robinPrimeBlock017_checks
  . exact robinPrimeBlock018_checks
  . exact robinPrimeBlock019_checks
  . exact robinPrimeBlock020_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow16_products : RobinFiniteProductChecks robinFiniteRow16 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 4528) (tail := [91, 22, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2]) (bs := robinFiniteRow16Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow16Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow16_checks : RobinFiniteRowChecks robinFiniteRow16 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow16_products
    . decide +kernel

end Robin1984
