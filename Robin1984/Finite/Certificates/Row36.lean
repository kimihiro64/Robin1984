import Robin1984.Analytic.PrimeProductBlocks
import Robin1984.Equivalence.ReducedProductChecks
import Robin1984.Finite.Certificates.PrimeBlocks00
import Robin1984.Finite.Certificates.PrimeBlocks01
import Robin1984.Finite.Certificates.PrimeBlocks02
import Robin1984.Finite.Certificates.PrimeBlocks03
import Robin1984.Finite.Certificates.PrimeBlocks04
import Robin1984.Finite.Certificates.PrimeBlocks05
import Robin1984.Finite.Certificates.PrimeBlocks06
import Robin1984.Finite.Certificates.PrimeBlocks07
import Robin1984.Finite.Certificates.PrimeBlocks08
import Robin1984.Finite.Certificates.PrimeBlocks09
import Robin1984.Finite.Certificates.PrimeBlocks10
import Robin1984.Finite.Certificates.PrimeBlocks11
import Robin1984.Finite.Certificates.PrimeBlocks12
import Robin1984.Finite.Certificates.PrimeBlocks13
import Robin1984.Finite.Certificates.PrimeBlocks14
import Robin1984.Finite.FiniteRowCertificate
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 36

This row covers the log-height interval
`[37283397387 / 500000, 41321869833 / 500000]`. It uses 19 cutoff thresholds, beginning at
`78604`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow36 : RobinFiniteRow where
  lo := (37283397387 / 500000)
  hi := (41321869833 / 500000)
  lambda := (564299807 / 500000000000000)
  gainUpper := (4014804438909 / 200000000000)
  heightMantissa := (15559495979352395835 / 9223372036854775808)
  logLoLower := (448778023 / 40000000)
  logHiLower := (5661147177 / 500000000)
  heightExponent := 113577
  cuts := [78604, 385, 59, 22, 12, 8, 6, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2]

def robinFiniteRow36Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock049,
  robinPrimeBlock050,
  robinPrimeBlock051,
  robinPrimeBlock052,
  robinPrimeBlock053,
  robinPrimeBlock054,
  robinPrimeBlock055,
  robinPrimeBlock056,
  robinPrimeBlock057,
  robinPrimeBlock058,
  robinPrimeBlock059,
  robinPrimeBlock060,
  robinPrimeBlock061,
  robinPrimeBlock062,
  robinPrimeBlock063,
  robinPrimeBlock064,
  robinPrimeBlock065,
  robinPrimeBlock066,
  robinPrimeBlock067,
  robinPrimeBlock068,
  robinPrimeBlock069,
  robinPrimeBlock070,
  robinPrimeBlock071,
  robinPrimeBlock072,
  robinPrimeBlock073,
  robinPrimeBlock074,
  robinPrimeBlock075,
  robinPrimeBlock076,
  robinPrimeBlock077,
  robinPrimeBlock078,
  robinPrimeBlock079,
  robinPrimeBlock080,
  robinPrimeBlock081,
  robinPrimeBlock082,
  robinPrimeBlock083,
  robinPrimeBlock084,
  robinPrimeBlock085,
  robinPrimeBlock086,
  robinPrimeBlock087,
  robinPrimeBlock088,
  robinPrimeBlock089,
  robinPrimeBlock090,
  robinPrimeBlock091,
  robinPrimeBlock092,
  robinPrimeBlock093,
  robinPrimeBlock094,
  robinPrimeBlock095,
  robinPrimeBlock096,
  robinPrimeBlock097,
  robinPrimeBlock098,
  robinPrimeBlock099,
  robinPrimeBlock100,
  robinPrimeBlock101,
  robinPrimeBlock102,
  robinPrimeBlock103,
  robinPrimeBlock104,
  robinPrimeBlock105,
  robinPrimeBlock106,
  robinPrimeBlock107,
  robinPrimeBlock108,
  robinPrimeBlock109,
  robinPrimeBlock110,
  robinPrimeBlock111,
  robinPrimeBlock112]

theorem robinFiniteRow36Blocks_checks :
    forall b, Membership.mem robinFiniteRow36Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow36Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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
  . exact robinPrimeBlock050_checks
  . exact robinPrimeBlock051_checks
  . exact robinPrimeBlock052_checks
  . exact robinPrimeBlock053_checks
  . exact robinPrimeBlock054_checks
  . exact robinPrimeBlock055_checks
  . exact robinPrimeBlock056_checks
  . exact robinPrimeBlock057_checks
  . exact robinPrimeBlock058_checks
  . exact robinPrimeBlock059_checks
  . exact robinPrimeBlock060_checks
  . exact robinPrimeBlock061_checks
  . exact robinPrimeBlock062_checks
  . exact robinPrimeBlock063_checks
  . exact robinPrimeBlock064_checks
  . exact robinPrimeBlock065_checks
  . exact robinPrimeBlock066_checks
  . exact robinPrimeBlock067_checks
  . exact robinPrimeBlock068_checks
  . exact robinPrimeBlock069_checks
  . exact robinPrimeBlock070_checks
  . exact robinPrimeBlock071_checks
  . exact robinPrimeBlock072_checks
  . exact robinPrimeBlock073_checks
  . exact robinPrimeBlock074_checks
  . exact robinPrimeBlock075_checks
  . exact robinPrimeBlock076_checks
  . exact robinPrimeBlock077_checks
  . exact robinPrimeBlock078_checks
  . exact robinPrimeBlock079_checks
  . exact robinPrimeBlock080_checks
  . exact robinPrimeBlock081_checks
  . exact robinPrimeBlock082_checks
  . exact robinPrimeBlock083_checks
  . exact robinPrimeBlock084_checks
  . exact robinPrimeBlock085_checks
  . exact robinPrimeBlock086_checks
  . exact robinPrimeBlock087_checks
  . exact robinPrimeBlock088_checks
  . exact robinPrimeBlock089_checks
  . exact robinPrimeBlock090_checks
  . exact robinPrimeBlock091_checks
  . exact robinPrimeBlock092_checks
  . exact robinPrimeBlock093_checks
  . exact robinPrimeBlock094_checks
  . exact robinPrimeBlock095_checks
  . exact robinPrimeBlock096_checks
  . exact robinPrimeBlock097_checks
  . exact robinPrimeBlock098_checks
  . exact robinPrimeBlock099_checks
  . exact robinPrimeBlock100_checks
  . exact robinPrimeBlock101_checks
  . exact robinPrimeBlock102_checks
  . exact robinPrimeBlock103_checks
  . exact robinPrimeBlock104_checks
  . exact robinPrimeBlock105_checks
  . exact robinPrimeBlock106_checks
  . exact robinPrimeBlock107_checks
  . exact robinPrimeBlock108_checks
  . exact robinPrimeBlock109_checks
  . exact robinPrimeBlock110_checks
  . exact robinPrimeBlock111_checks
  . exact robinPrimeBlock112_checks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow36_products : RobinFiniteProductChecks robinFiniteRow36 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 78604) (tail := [385, 59, 22, 12, 8, 6, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2]) (bs := robinFiniteRow36Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow36Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow36_checks : RobinFiniteRowChecks robinFiniteRow36 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow36_products
    . decide +kernel

end Robin1984
