import Robin1984.Equivalence.Theorem
import Robin1984.GRH.DirichletMultiplicity
import Robin1984.GRH.DirichletMultiplicityArithmetic
import Robin1984.GRH.HeckeTateMellin
import Robin1984.GRH.HeckeTateQuotientIntegration
import Robin1984.GRH.HeckeTateZetaUnfolding
import Robin1984.GRH.MultiplicityArithmetic
import Robin1984.GRH.MultiplicityDivisor
import Robin1984.GRH.MultiplicityExpansion
import Robin1984.GRH.MultiplicityFourierSeries
import Robin1984.GRH.MultiplicityGaussian
import Robin1984.GRH.RiemannMultiplicity
import Robin1984.GRH.RiemannMultiplicityArithmetic
import Robin1984.Lagarias.Theorem
import Robin1984.Mathlib
import Robin1984.Public

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Public Robin 1984 library facade

Importing this module exposes the Robin and Lagarias equivalence theorems, the small public
API intended for downstream users, and the project-independent Mathlib
candidate layer. The mathematical development remains organized in the
narrower modules imported by these facades.
-/
