import Robin1984.Analytic.PrimeProductBlocks
import Robin1984.Equivalence.ReducedProductChecks
import Robin1984.Finite.Certificates.PrimeBlocks00
import Robin1984.Finite.Certificates.PrimeBlocks01
import Robin1984.Finite.Certificates.PrimeBlocks02
import Robin1984.Finite.Certificates.PrimeBlocks03
import Robin1984.Finite.FiniteRowCertificate
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 19

This row covers the log-height interval
`[458996953 / 62500, 4387795691 / 500000]`. It uses 15 cutoff thresholds, beginning at
`8059`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow19 : RobinFiniteRow where
  lo := (458996953 / 62500)
  hi := (4387795691 / 500000)
  lambda := (13794103247 / 1000000000000000)
  gainUpper := (16008228581683 / 1000000000000)
  heightMantissa := (18714211614409075569 / 18446744073709551616)
  logLoLower := (2225408073 / 250000000)
  logHiLower := (9079729439 / 1000000000)
  heightExponent := 11659
  cuts := [8059, 122, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2]

def robinFiniteRow19Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock020,
  robinPrimeBlock021,
  robinPrimeBlock022,
  robinPrimeBlock023,
  robinPrimeBlock024,
  robinPrimeBlock025,
  robinPrimeBlock026]

theorem robinFiniteRow19Blocks_checks :
    forall b, Membership.mem robinFiniteRow19Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow19Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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
  . exact robinPrimeBlock021_checks
  . exact robinPrimeBlock022_checks
  . exact robinPrimeBlock023_checks
  . exact robinPrimeBlock024_checks
  . exact robinPrimeBlock025_checks
  . exact robinPrimeBlock026_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow19_products : RobinFiniteProductChecks robinFiniteRow19 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 8059) (tail := [122, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2]) (bs := robinFiniteRow19Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow19Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow19_checks : RobinFiniteRowChecks robinFiniteRow19 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow19_products
    . decide +kernel

end Robin1984
