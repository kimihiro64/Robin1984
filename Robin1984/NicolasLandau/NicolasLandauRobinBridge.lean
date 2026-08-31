import Robin1984.NicolasLandau.LcmTransfer
import Robin1984.NicolasLandau.NicolasLandauRightmostRay
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# Nicolas-Landau negative oscillation to the native Robin inequality

This bridge composes the proved negative Nicolas-Landau excursion with the
finite-product and `lcmUpto` transfer.  It introduces no additional analytic
or arithmetic assumption.
-/

namespace Robin1984

noncomputable section

/-- Failure of mathlib's Riemann hypothesis forces failure of Robin's
inequality for some integer above `5040`. -/
theorem not_nativeRobinInequalityAll_of_not_riemannHypothesis
    (hNotRH : Not RiemannHypothesis) :
    Not Robin1984.Core.NativeRobinInequalityAll := by
  choose b _hbPos hbHalf hJ using
    exists_nicolasJ_omegaMinus_of_not_riemannHypothesis hNotRH
  have hbOne : b < 1 := lt_trans hbHalf (by norm_num)
  exact not_nativeRobinInequalityAll_of_nicolasOmegaMinus hbHalf
    (nicolasLogMertensOscillation_omegaMinus_of_J_proved_upper hbOne hJ)

/-- Robin's inequality for every integer above `5040` implies mathlib's
Riemann hypothesis. -/
theorem riemannHypothesis_of_nativeRobinInequalityAll
    (hRobin : Robin1984.Core.NativeRobinInequalityAll) :
    RiemannHypothesis := by
  by_contra hNotRH
  exact not_nativeRobinInequalityAll_of_not_riemannHypothesis hNotRH hRobin


end

end Robin1984
