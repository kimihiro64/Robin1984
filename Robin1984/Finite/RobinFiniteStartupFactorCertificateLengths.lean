import Robin1984.Finite.RobinFiniteStartupFactorCertificate5041To5077
import Robin1984.Finite.RobinFiniteStartupFactorCertificate6101To7125
import Robin1984.Finite.RobinFiniteStartupFactorCertificate7125To7560
import Robin1984.Finite.RobinFiniteStartupFactorCertificate5077To6101
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Coverage lengths for the startup factor tables

These definitional equalities record the exact number of rows in each startup
factor table: 36, 1024, 1024, and 435. Together with their starting values,
the lengths show that the four tables meet without gaps and cover precisely
the integer interval `[5041, 7560)`.
-/

namespace Robin1984

set_option maxRecDepth 300000 in
theorem startupFactorRows5041To5077_length :
    startupFactorRows5041To5077.length = 36 := by
  rfl

set_option maxRecDepth 300000 in
theorem startupFactorRows5077To6101_length :
    startupFactorRows5077To6101.length = 1024 := by
  rfl

set_option maxRecDepth 300000 in
theorem startupFactorRows6101To7125_length :
    startupFactorRows6101To7125.length = 1024 := by
  rfl

set_option maxRecDepth 300000 in
theorem startupFactorRows7125To7560_length :
    startupFactorRows7125To7560.length = 435 := by
  rfl

end Robin1984
