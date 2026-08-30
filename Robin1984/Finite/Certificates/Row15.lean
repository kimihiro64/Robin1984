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
# Finite Robin certificate row 15

This row covers the log-height interval
`[815385537 / 250000, 406392661 / 100000]`. It uses 14 cutoff thresholds, beginning at
`3662`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow15 : RobinFiniteRow where
  lo := (815385537 / 250000)
  hi := (406392661 / 100000)
  lambda := (6654185407 / 200000000000000)
  gainUpper := (91279065703 / 6250000000)
  heightMantissa := (97982466908525699 / 72057594037927936)
  logLoLower := (8089955413 / 1000000000)
  logHiLower := (8309904929 / 1000000000)
  heightExponent := 5329
  cuts := [3662, 82, 21, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2]

def robinFiniteRow15Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock018]

theorem robinFiniteRow15Blocks_checks :
    forall b, Membership.mem robinFiniteRow15Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow15Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow15_products : RobinFiniteProductChecks robinFiniteRow15 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 3662) (tail := [82, 21, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2]) (bs := robinFiniteRow15Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow15Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow15_checks : RobinFiniteRowChecks robinFiniteRow15 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow15_products
    . decide +kernel

end Robin1984
