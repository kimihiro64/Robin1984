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
# Finite Robin certificate row 06

This row covers the log-height interval
`[111686563 / 500000, 163594351 / 500000]`. It uses 10 cutoff thresholds, beginning at
`274`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow06 : RobinFiniteRow where
  lo := (111686563 / 500000)
  hi := (163594351 / 500000)
  lambda := (80829194299 / 125000000000000)
  gainUpper := (9985855626483 / 1000000000000)
  heightMantissa := (9719554276707939449 / 9223372036854775808)
  logLoLower := (2704421791 / 500000000)
  logHiLower := (5790537073 / 1000000000)
  heightExponent := 412
  cuts := [274, 21, 8, 5, 3, 3, 2, 2, 2, 2]

def robinFiniteRow06Blocks : List RobinPrimeProductBlock := [
  robinPrimeBlock000,
  robinPrimeBlock001,
  robinPrimeBlock002,
  robinPrimeBlock003,
  robinPrimeBlock004,
  robinPrimeBlock005,
  robinPrimeBlock006]

theorem robinFiniteRow06Blocks_checks :
    forall b, Membership.mem robinFiniteRow06Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow06Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb
  all_goals subst b
  . exact robinPrimeBlock000_checks
  . exact robinPrimeBlock001_checks
  . exact robinPrimeBlock002_checks
  . exact robinPrimeBlock003_checks
  . exact robinPrimeBlock004_checks
  . exact robinPrimeBlock005_checks
  . exact robinPrimeBlock006_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow06_products : RobinFiniteProductChecks robinFiniteRow06 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 274) (tail := [21, 8, 5, 3, 3, 2, 2, 2, 2]) (bs := robinFiniteRow06Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow06Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow06_checks : RobinFiniteRowChecks robinFiniteRow06 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow06_products
    . decide +kernel

end Robin1984
