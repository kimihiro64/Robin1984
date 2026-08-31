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
# Finite Robin certificate row 01

This row covers the log-height interval
`[22117363 / 1000000, 35788699 / 1000000]`. It uses 6 cutoff thresholds, beginning at
`28`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow01 : RobinFiniteRow where
  lo := (22117363 / 1000000)
  hi := (35788699 / 1000000)
  lambda := (2565510579241 / 250000000000000)
  gainUpper := (5692332166421 / 1000000000000)
  heightMantissa := (5019589575 / 4294967296)
  logLoLower := (619272591 / 200000000)
  logHiLower := (894408043 / 250000000)
  heightExponent := 38
  cuts := [28, 6, 3, 2, 2, 2]

def robinFiniteRow01Blocks : List RobinPrimeProductBlock := [
  robinPrimeBlock000,
  robinPrimeBlock001]

theorem robinFiniteRow01Blocks_checks :
    forall b, Membership.mem robinFiniteRow01Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow01Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb
  all_goals subst b
  . exact robinPrimeBlock000_checks
  . exact robinPrimeBlock001_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow01_products : RobinFiniteProductChecks robinFiniteRow01 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 28) (tail := [6, 3, 2, 2, 2]) (bs := robinFiniteRow01Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow01Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow01_checks : RobinFiniteRowChecks robinFiniteRow01 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow01_products
    . decide +kernel

end Robin1984
