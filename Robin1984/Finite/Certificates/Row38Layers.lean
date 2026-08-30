import Robin1984.Finite.FiniteLayerChecks
import Robin1984.Finite.FiniteRowCertificate

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Final finite row: layer and endpoint checks

This module defines row 38 on the log-height interval
`[285455918 / 3125, 100000]`. Its 19 cutoff thresholds begin at `95672`. The
two kernel-checked theorems verify all included/excluded layer signs and both
rational endpoint tangent inequalities.

The much larger first-layer prime products are assembled in `Row38`, which
combines them with these results to obtain the complete row certificate.
-/

namespace Robin1984

def robinFiniteRow38 : RobinFiniteRow where
  lo := (285455918 / 3125)
  hi := 100000
  lambda := (227843693 / 250000000000000)
  gainUpper := (20426439746163 / 1000000000000)
  heightMantissa := (32545606599505639473 / 18446744073709551616)
  logLoLower := (11422408609 / 1000000000)
  logHiLower := (11512925463 / 1000000000)
  heightExponent := 138388
  cuts := [95672, 425, 63, 23, 13, 8, 6, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow38_layers : RobinLayerChecks robinFiniteRow38.cuts robinFiniteRow38.lambda := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow38_endpoints :
    And (RobinFiniteEndpointCheck robinFiniteRow38.lo robinFiniteRow38.logLoLower robinFiniteRow38.lambda (robinFiniteRowObjectiveUpper robinFiniteRow38))
      (RobinFiniteEndpointCheck robinFiniteRow38.hi robinFiniteRow38.logHiLower robinFiniteRow38.lambda (robinFiniteRowObjectiveUpper robinFiniteRow38)) := by
  decide +kernel

end Robin1984
