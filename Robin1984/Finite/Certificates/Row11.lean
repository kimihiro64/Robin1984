import Robin1984.Equivalence.ReducedProductChecks
import Robin1984.Finite.Certificates.PrimeBlocks00
import Robin1984.Finite.Certificates.PrimeBlocks01
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 11

This row covers the log-height interval
`[240770673 / 200000, 63176719 / 40000]`. It uses 12 cutoff thresholds, beginning at
`1391`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow11 : RobinFiniteRow where
  lo := (240770673 / 200000)
  hi := (63176719 / 40000)
  lambda := (99275427189 / 1000000000000000)
  gainUpper := (6429631547689 / 500000000000)
  heightMantissa := (2443405932771137419 / 2305843009213693952)
  logLoLower := (7093282827 / 1000000000)
  logHiLower := (3682405843 / 500000000)
  heightExponent := 2017
  cuts := [1391, 50, 15, 8, 5, 4, 3, 2, 2, 2, 2, 2]

def robinFiniteRow11Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock012]

theorem robinFiniteRow11Blocks_checks :
    forall b, Membership.mem robinFiniteRow11Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow11Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow11_products : RobinFiniteProductChecks robinFiniteRow11 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 1391) (tail := [50, 15, 8, 5, 4, 3, 2, 2, 2, 2, 2]) (bs := robinFiniteRow11Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow11Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow11_checks : RobinFiniteRowChecks robinFiniteRow11 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow11_products
    . decide +kernel

end Robin1984
