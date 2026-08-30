import Robin1984.Finite.RobinFiniteStartupFactorCertificateCore

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Startup factor certificates for [5041, 5077)

This table contains one prime-power factorization for each integer from 5041
through 5076. The validity theorem checks the primality and coprimality data,
reconstructs each integer, and proves the exact integer inequality
`35 * sigma(n) <= 127 * n` throughout this half-open range.
-/

namespace Robin1984

def startupFactorRows5041To5077 :
    List (List StartupPrimePower) := [
    [(71, 2)],
    [(2, 1), (2521, 1)],
    [(3, 1), (41, 2)],
    [(2, 2), (13, 1), (97, 1)],
    [(5, 1), (1009, 1)],
    [(2, 1), (3, 1), (29, 2)],
    [(7, 2), (103, 1)],
    [(2, 3), (631, 1)],
    [(3, 3), (11, 1), (17, 1)],
    [(2, 1), (5, 2), (101, 1)],
    [(5051, 1)],
    [(2, 2), (3, 1), (421, 1)],
    [(31, 1), (163, 1)],
    [(2, 1), (7, 1), (19, 2)],
    [(3, 1), (5, 1), (337, 1)],
    [(2, 6), (79, 1)],
    [(13, 1), (389, 1)],
    [(2, 1), (3, 2), (281, 1)],
    [(5059, 1)],
    [(2, 2), (5, 1), (11, 1), (23, 1)],
    [(3, 1), (7, 1), (241, 1)],
    [(2, 1), (2531, 1)],
    [(61, 1), (83, 1)],
    [(2, 3), (3, 1), (211, 1)],
    [(5, 1), (1013, 1)],
    [(2, 1), (17, 1), (149, 1)],
    [(3, 2), (563, 1)],
    [(2, 2), (7, 1), (181, 1)],
    [(37, 1), (137, 1)],
    [(2, 1), (3, 1), (5, 1), (13, 2)],
    [(11, 1), (461, 1)],
    [(2, 4), (317, 1)],
    [(3, 1), (19, 1), (89, 1)],
    [(2, 1), (43, 1), (59, 1)],
    [(5, 2), (7, 1), (29, 1)],
    [(2, 2), (3, 3), (47, 1)],
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem startupFactorRows5041To5077_valid :
    StartupFactorRowsValid 5041 startupFactorRows5041To5077 := by
  norm_num [startupFactorRows5041To5077, StartupFactorRowsValid, StartupFactorsValid,
    startupFactorProduct, startupFactorSigma]

end Robin1984
