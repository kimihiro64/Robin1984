import Robin1984.Finite.FiniteRowCertificate

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 finite-range obligation supplies the target; the certificate data have no external source attribution.
- Formalization note: The block or row representation, generated exact data, and kernel-checked verification are original to this formalization.
- PROVENANCE-END
-/

/-!
# Finite Robin certificate row 00

This row covers the log-height interval
`[336 / 25, 22117363 / 1000000]`. It uses 5 cutoff thresholds, beginning at
`17`. Its stored rational slope, gain bound, height bound, and endpoint
logarithm bounds define one instance of `RobinFiniteRow`.

The row theorem verifies the layer-sign, prime-product, and endpoint tangent
conditions required by `RobinFiniteRowChecks`, using kernel decisions for the
generated exact arithmetic. The resulting soundness theorem proves Robin's
inequality whenever `log n` lies in this interval.
-/

namespace Robin1984

def robinFiniteRow00 : RobinFiniteRow where
  lo := (336 / 25)
  hi := (22117363 / 1000000)
  lambda := (9771914406623 / 500000000000000)
  gainUpper := (5141587823941 / 1000000000000)
  heightMantissa := (11486475 / 8388608)
  logLoLower := (1299117667 / 500000000)
  logHiLower := (619272591 / 200000000)
  heightExponent := 28
  cuts := [17, 5, 3, 2, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem robinFiniteRow00_checks : RobinFiniteRowChecks robinFiniteRow00 := by
  decide +kernel

end Robin1984
