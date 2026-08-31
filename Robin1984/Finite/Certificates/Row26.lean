import Robin1984.Equivalence.ReducedProductChecks
import Robin1984.Finite.Certificates.PrimeBlocks00
import Robin1984.Finite.Certificates.PrimeBlocks01
import Robin1984.Finite.Certificates.PrimeBlocks02
import Robin1984.Finite.Certificates.PrimeBlocks03
import Robin1984.Finite.Certificates.PrimeBlocks04
import Robin1984.Finite.Certificates.PrimeBlocks05
import Robin1984.Finite.Certificates.PrimeBlocks06
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 26

This row covers the log-height interval
`[22433188173 / 1000000, 1287242339 / 50000]`. It uses 17 cutoff thresholds, beginning at
`24088`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow26 : RobinFiniteRow where
  lo := (22433188173 / 1000000)
  hi := (1287242339 / 50000)
  lambda := (2057220229 / 500000000000000)
  gainUpper := (3594193175181 / 200000000000)
  heightMantissa := (30201260215318202501 / 18446744073709551616)
  logLoLower := (2003659351 / 200000000)
  logHiLower := (7934367 / 781250)
  heightExponent := 34958
  cuts := [24088, 212, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]

def robinFiniteRow26Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock026,
  robinPrimeBlock027,
  robinPrimeBlock028,
  robinPrimeBlock029,
  robinPrimeBlock030,
  robinPrimeBlock031,
  robinPrimeBlock032,
  robinPrimeBlock033,
  robinPrimeBlock034,
  robinPrimeBlock035,
  robinPrimeBlock036,
  robinPrimeBlock037,
  robinPrimeBlock038,
  robinPrimeBlock039,
  robinPrimeBlock040,
  robinPrimeBlock041,
  robinPrimeBlock042,
  robinPrimeBlock043,
  robinPrimeBlock044,
  robinPrimeBlock045,
  robinPrimeBlock046,
  robinPrimeBlock047,
  robinPrimeBlock048,
  robinPrimeBlock049]

theorem robinFiniteRow26Blocks_checks :
    forall b, Membership.mem robinFiniteRow26Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow26Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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
  . exact robinPrimeBlock027_checks
  . exact robinPrimeBlock028_checks
  . exact robinPrimeBlock029_checks
  . exact robinPrimeBlock030_checks
  . exact robinPrimeBlock031_checks
  . exact robinPrimeBlock032_checks
  . exact robinPrimeBlock033_checks
  . exact robinPrimeBlock034_checks
  . exact robinPrimeBlock035_checks
  . exact robinPrimeBlock036_checks
  . exact robinPrimeBlock037_checks
  . exact robinPrimeBlock038_checks
  . exact robinPrimeBlock039_checks
  . exact robinPrimeBlock040_checks
  . exact robinPrimeBlock041_checks
  . exact robinPrimeBlock042_checks
  . exact robinPrimeBlock043_checks
  . exact robinPrimeBlock044_checks
  . exact robinPrimeBlock045_checks
  . exact robinPrimeBlock046_checks
  . exact robinPrimeBlock047_checks
  . exact robinPrimeBlock048_checks
  . exact robinPrimeBlock049_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow26_products : RobinFiniteProductChecks robinFiniteRow26 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 24088) (tail := [212, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]) (bs := robinFiniteRow26Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow26Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow26_checks : RobinFiniteRowChecks robinFiniteRow26 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow26_products
    . decide +kernel

end Robin1984
