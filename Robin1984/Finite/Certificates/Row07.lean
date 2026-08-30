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
# Finite Robin certificate row 07

This row covers the log-height interval
`[163594351 / 500000, 464815043 / 1000000]`. It uses 10 cutoff thresholds, beginning at
`395`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow07 : RobinFiniteRow where
  lo := (163594351 / 500000)
  hi := (464815043 / 1000000)
  lambda := (422180858753 / 1000000000000000)
  gainUpper := (5297643593427 / 500000000000)
  heightMantissa := (30938683420670908437 / 18446744073709551616)
  logLoLower := (5790537073 / 1000000000)
  logHiLower := (383852473 / 62500000)
  heightExponent := 575
  cuts := [395, 26, 9, 5, 4, 3, 2, 2, 2, 2]

def robinFiniteRow07Blocks : List RobinPrimeProductBlock := [
  robinPrimeBlock000,
  robinPrimeBlock001,
  robinPrimeBlock002,
  robinPrimeBlock003,
  robinPrimeBlock004,
  robinPrimeBlock005,
  robinPrimeBlock006,
  robinPrimeBlock007]

theorem robinFiniteRow07Blocks_checks :
    forall b, Membership.mem robinFiniteRow07Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow07Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb
  all_goals subst b
  . exact robinPrimeBlock000_checks
  . exact robinPrimeBlock001_checks
  . exact robinPrimeBlock002_checks
  . exact robinPrimeBlock003_checks
  . exact robinPrimeBlock004_checks
  . exact robinPrimeBlock005_checks
  . exact robinPrimeBlock006_checks
  . exact robinPrimeBlock007_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow07_products : RobinFiniteProductChecks robinFiniteRow07 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 395) (tail := [26, 9, 5, 4, 3, 2, 2, 2, 2]) (bs := robinFiniteRow07Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow07Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow07_checks : RobinFiniteRowChecks robinFiniteRow07 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow07_products
    . decide +kernel

end Robin1984
