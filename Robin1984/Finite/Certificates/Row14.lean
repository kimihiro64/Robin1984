import Robin1984.Equivalence.ReducedProductChecks
import Robin1984.Finite.Certificates.PrimeBlocks00
import Robin1984.Finite.Certificates.PrimeBlocks01
import Robin1984.Finite.Certificates.PrimeBlocks02
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 14

This row covers the log-height interval
`[518900301 / 200000, 815385537 / 250000]`. It uses 14 cutoff thresholds, beginning at
`2927`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow14 : RobinFiniteRow where
  lo := (518900301 / 200000)
  hi := (815385537 / 250000)
  lambda := (42786768497 / 1000000000000000)
  gainUpper := (1421791828229 / 100000000000)
  heightMantissa := (12095416622684725185 / 9223372036854775808)
  logLoLower := (7861149677 / 1000000000)
  logHiLower := (8089955413 / 1000000000)
  heightExponent := 4294
  cuts := [2927, 73, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2]

def robinFiniteRow14Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock016]

theorem robinFiniteRow14Blocks_checks :
    forall b, Membership.mem robinFiniteRow14Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow14Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow14_products : RobinFiniteProductChecks robinFiniteRow14 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 2927) (tail := [73, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2]) (bs := robinFiniteRow14Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow14Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow14_checks : RobinFiniteRowChecks robinFiniteRow14 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow14_products
    . decide +kernel

end Robin1984
