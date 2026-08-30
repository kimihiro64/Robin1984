import Robin1984.Analytic.PrimeProductBlocks
import Robin1984.Equivalence.ReducedProductChecks
import Robin1984.Finite.Certificates.PrimeBlocks00
import Robin1984.Finite.Certificates.PrimeBlocks01
import Robin1984.Finite.Certificates.PrimeBlocks02
import Robin1984.Finite.Certificates.PrimeBlocks03
import Robin1984.Finite.Certificates.PrimeBlocks04
import Robin1984.Finite.Certificates.PrimeBlocks05
import Robin1984.Finite.FiniteRowCertificate
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 25

This row covers the log-height interval
`[9718846411 / 500000, 22433188173 / 1000000]`. It uses 17 cutoff thresholds, beginning at
`20934`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow25 : RobinFiniteRow where
  lo := (9718846411 / 500000)
  hi := (22433188173 / 1000000)
  lambda := (1200244709 / 250000000000000)
  gainUpper := (354242307219 / 20000000000)
  heightMantissa := (31629297847177716087 / 18446744073709551616)
  logLoLower := (9874969387 / 1000000000)
  logHiLower := (2003659351 / 200000000)
  heightExponent := 30244
  cuts := [20934, 197, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]

def robinFiniteRow25Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock045]

theorem robinFiniteRow25Blocks_checks :
    forall b, Membership.mem robinFiniteRow25Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow25Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow25_products : RobinFiniteProductChecks robinFiniteRow25 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 20934) (tail := [197, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]) (bs := robinFiniteRow25Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow25Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow25_checks : RobinFiniteRowChecks robinFiniteRow25 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow25_products
    . decide +kernel

end Robin1984
