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
# Finite Robin certificate row 02

This row covers the log-height interval
`[35788699 / 1000000, 29149999 / 500000]`. It uses 7 cutoff thresholds, beginning at
`46`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow02 : RobinFiniteRow where
  lo := (35788699 / 1000000)
  hi := (29149999 / 500000)
  lambda := (5519615043151 / 1000000000000000)
  gainUpper := (3371325800503 / 500000000000)
  heightMantissa := (6181604729214089175 / 4611686018427387904)
  logLoLower := (894408043 / 250000000)
  logHiLower := (2032801029 / 500000000)
  heightExponent := 69
  cuts := [46, 8, 4, 3, 2, 2, 2]

def robinFiniteRow02Blocks : List RobinPrimeProductBlock := [
  robinPrimeBlock000,
  robinPrimeBlock001,
  robinPrimeBlock002]

theorem robinFiniteRow02Blocks_checks :
    forall b, Membership.mem robinFiniteRow02Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow02Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb
  all_goals subst b
  . exact robinPrimeBlock000_checks
  . exact robinPrimeBlock001_checks
  . exact robinPrimeBlock002_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow02_products : RobinFiniteProductChecks robinFiniteRow02 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 46) (tail := [8, 4, 3, 2, 2, 2]) (bs := robinFiniteRow02Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow02Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow02_checks : RobinFiniteRowChecks robinFiniteRow02 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow02_products
    . decide +kernel

end Robin1984
