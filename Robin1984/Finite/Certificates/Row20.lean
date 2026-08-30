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
# Finite Robin certificate row 20

This row covers the log-height interval
`[4387795691 / 500000, 10433152137 / 1000000]`. It uses 15 cutoff thresholds, beginning at
`9603`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow20 : RobinFiniteRow where
  lo := (4387795691 / 500000)
  hi := (10433152137 / 1000000)
  lambda := (11354367573 / 1000000000000000)
  gainUpper := (4081742288033 / 250000000000)
  heightMantissa := (35268474367176998613 / 18446744073709551616)
  logLoLower := (9079729439 / 1000000000)
  logHiLower := (9252743719 / 1000000000)
  heightExponent := 13935
  cuts := [9603, 133, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2]

def robinFiniteRow20Blocks : List RobinPrimeProductBlock := [
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
  robinPrimeBlock029]

theorem robinFiniteRow20Blocks_checks :
    forall b, Membership.mem robinFiniteRow20Blocks b -> RobinPrimeProductBlockChecks b := by
  intro b hb
  simp only [robinFiniteRow20Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow20_products : RobinFiniteProductChecks robinFiniteRow20 := by
  apply RobinFiniteProductChecks.of_first_layer_blocks
    (c := 9603) (tail := [133, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2]) (bs := robinFiniteRow20Blocks) rfl
  . decide +kernel
  . exact robinFiniteRow20Blocks_checks
  . decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow20_checks : RobinFiniteRowChecks robinFiniteRow20 := by
  apply And.intro
  . decide +kernel
  . apply And.intro
    . exact robinFiniteRow20_products
    . decide +kernel

end Robin1984
