import Robin1984.Equivalence.Theorem
import Robin1984.GRH.DedekindMultiplicity
import Robin1984.GRH.DirichletMultiplicity
import Robin1984.GRH.DirichletMultiplicityArithmetic
import Robin1984.GRH.GodementJacquetAdelicMatrixBounds
import Robin1984.GRH.GodementJacquetCoordinates
import Robin1984.GRH.GodementJacquetFiniteMatrixDenominator
import Robin1984.GRH.GodementJacquetFiniteMatrixVolume
import Robin1984.GRH.GodementJacquetFiniteRectangleDilation
import Robin1984.GRH.GodementJacquetFiniteRectangleFourier
import Robin1984.GRH.GodementJacquetFourier
import Robin1984.GRH.GodementJacquetFullThetaGrowth
import Robin1984.GRH.GodementJacquetFundamentalDomain
import Robin1984.GRH.GodementJacquetHaarNormalization
import Robin1984.GRH.GodementJacquetHaarUnimodularity
import Robin1984.GRH.GodementJacquetHaarVolume
import Robin1984.GRH.GodementJacquetMatrixMeasure
import Robin1984.GRH.GodementJacquetMatrixPoisson
import Robin1984.GRH.GodementJacquetMellinAbsolute
import Robin1984.GRH.GodementJacquetMellinGrowth
import Robin1984.GRH.GodementJacquetMellinIdentification
import Robin1984.GRH.GodementJacquetProductLattice
import Robin1984.GRH.GodementJacquetReductionContinuation
import Robin1984.GRH.GodementJacquetReductionWeights
import Robin1984.GRH.GodementJacquetSchwartzDilation
import Robin1984.GRH.GodementJacquetSingularOrbits
import Robin1984.GRH.GodementJacquetThetaAnalyticContinuation
import Robin1984.GRH.GodementJacquetThetaDecay
import Robin1984.GRH.GodementJacquetThetaDualDecay
import Robin1984.GRH.GodementJacquetThetaKernel
import Robin1984.GRH.GodementJacquetThetaL2Decay
import Robin1984.GRH.GodementJacquetThetaLatticeDecay
import Robin1984.GRH.GodementJacquetThetaMellin
import Robin1984.GRH.GodementJacquetThetaWeightedCancellation
import Robin1984.GRH.GodementJacquetUnfolding
import Robin1984.GRH.GodementJacquetUnramifiedMeasure
import Robin1984.GRH.GodementJacquetUnramifiedSpherical
import Robin1984.GRH.GodementJacquetVectorPoisson
import Robin1984.GRH.HeckeTateAdelicEuler
import Robin1984.GRH.HeckeTateClassPoisson
import Robin1984.GRH.HeckeTateContinuation
import Robin1984.GRH.HeckeTateFiniteFourier
import Robin1984.GRH.HeckeTateFunctionalEquation
import Robin1984.GRH.HeckeTateInfiniteFourier
import Robin1984.GRH.HeckeTateMellin
import Robin1984.GRH.HeckeTateMellinReflection
import Robin1984.GRH.HeckeTateQuotientIntegration
import Robin1984.GRH.LocalIwasawaMeasure
import Robin1984.GRH.MultiplicityArithmetic
import Robin1984.GRH.MultiplicityDivisor
import Robin1984.GRH.MultiplicityExceptions
import Robin1984.GRH.MultiplicityExpansion
import Robin1984.GRH.MultiplicityFourierSeries
import Robin1984.GRH.MultiplicityGaussian
import Robin1984.GRH.RiemannMultiplicity
import Robin1984.GRH.RiemannMultiplicityArithmetic
import Robin1984.GRH.StandardAutomorphicMultiplicity
import Robin1984.GRH.StandardEulerSummability
import Robin1984.GRH.TriangularContinuation
import Robin1984.GRH.UniversalRH
import Robin1984.GRH.UniversalRHDisk
import Robin1984.GRH.ValuationIwasawa
import Robin1984.GRH.ValuationIwasawaCoordinates
import Robin1984.GRH.ValuationIwasawaSubgroups
import Robin1984.GRH.ValuationUnitriangularMeasure
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
