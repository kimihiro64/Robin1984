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
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 30

This row covers the log-height interval
`[9481137173 / 250000, 1070418171 / 25000]`. It uses 18 cutoff thresholds, beginning at
`40370`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow30 : RobinFiniteRow where
  lo := (9481137173 / 250000)
  hi := (1070418171 / 25000)
  lambda := (2335546837 / 1000000000000000)
  gainUpper := (9442891043759 / 500000000000)
  heightMantissa := (25881087461094799483 / 18446744073709551616)
  logLoLower := (10543353903 / 1000000000)
  logHiLower := (5332342059 / 500000000)
  heightExponent := 58355
  cuts := [40370, 275, 47, 19, 11, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2]

def robinFiniteRow30Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock069]

theorem robinFiniteRow30Blocks_checks :
    forall b, Membership.mem robinFiniteRow30Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow30Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow30_products : RobinFiniteProductChecks robinFiniteRow30 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 40370) (tail := [275, 47, 19, 11, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2]) (bs := robinFiniteRow30Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow30Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow30_checks : RobinFiniteRowChecks robinFiniteRow30 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow30_products
    . decide +kernel

end Robin1984
