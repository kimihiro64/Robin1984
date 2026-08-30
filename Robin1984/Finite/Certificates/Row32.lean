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
import Robin1984.Finite.FiniteRowCertificate
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 32

This row covers the log-height interval
`[48110318623 / 1000000, 10789326747 / 200000]`. It uses 18 cutoff thresholds, beginning at
`51028`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow32 : RobinFiniteRow where
  lo := (48110318623 / 1000000)
  hi := (10789326747 / 200000)
  lambda := (1807809003 / 1000000000000000)
  gainUpper := (9651034107219 / 500000000000)
  heightMantissa := (14266740078647197633 / 9223372036854775808)
  logLoLower := (2695312989 / 250000000)
  logHiLower := (10895750571 / 1000000000)
  heightExponent := 73685
  cuts := [51028, 310, 51, 20, 11, 7, 5, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]

def robinFiniteRow32Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock081]

theorem robinFiniteRow32Blocks_checks :
    forall b, Membership.mem robinFiniteRow32Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow32Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow32_products : RobinFiniteProductChecks robinFiniteRow32 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 51028) (tail := [310, 51, 20, 11, 7, 5, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]) (bs := robinFiniteRow32Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow32Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow32_checks : RobinFiniteRowChecks robinFiniteRow32 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow32_products
    . decide +kernel

end Robin1984
