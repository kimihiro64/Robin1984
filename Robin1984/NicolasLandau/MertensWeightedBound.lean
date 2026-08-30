import Robin1984.Equivalence.RobinLemmaTwo
import Robin1984.Equivalence.WeightedKernelBounds
import Robin1984.Equivalence.PrimePowerFirstWeightBounds
import Robin1984.NicolasLandau.NicolasOscillation
import Robin1984.NicolasLandau.WeightedEndpointArithmetic
import Robin1984.NicolasLandau.WeightedPrimePowerTail
import Robin1984.NicolasLandau.WeightedPsiError
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Jean-Louis Nicolas (1983), Landau's oscillation principle, and Guy Robin's use of that argument (1984).
- Formalization note: The retained mathematical step reconstructs the cited Nicolas--Landau argument; module boundaries and Lean proof engineering are original to this formalization.
- PROVENANCE-END
-/

/-!
# The RH Mertens bound with its endpoint defect retained

The omitted logarithmic prime-power series has the favorable sign. The
complete theta tail is then replaced by the proved psi and prime-power bounds.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

theorem robin_mertens_summand_nonpos (p : Nat) : Mertens.M_eq_summand p <= 0 := by
  classical
  unfold Mertens.M_eq_summand
  split_ifs with hp
  . have hpOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
    have hpPos : (0 : Real) < p := by linarith
    have hFrac : (1 : Real) / p < 1 := (div_lt_one hpPos).mpr hpOne
    have hLog := Real.log_le_sub_one_of_pos (by linarith : (0 : Real) < 1 - 1 / p)
    linarith
  . exact le_rfl


theorem robin_theta_tail_eq_psi_sub_prime_power {x : Real} (hx : 2 <= x) :
    nicolasK x = robinPsiWeightedErrorIntegral 1 x - robinPrimePowerWeightedTail 1 x := by
  have hPsi := integrableOn_robinPsiWeightedError_one hx
  have hPowers := integrableOn_robinPrimePowerWeightedTail (n := 1) (by omega)
    (by linarith : 1 < x)
  unfold nicolasK robinPsiWeightedErrorIntegral robinPrimePowerWeightedTail
  rw [<- integral_sub hPsi hPowers]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have htX : x < t := ht
  rw [robinRealWeight_one_eq_nicolasTailKernel (by linarith : 1 < t)]
  unfold nicolasThetaError
  ring


/-- Every term is in the original x-normalization; no theta endpoint estimate
is assumed here. -/
def robinMertensWeightedScalar (x : Real) : Real :=
  (2 + (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) *
      x^(-(1 / 2 : Real)) * Inv.inv (Real.log x) +
    ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) - 2) *
      x^(-(1 / 2 : Real)) * Inv.inv ((Real.log x)^2) +
    (8 + 4 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) *
      x^(-(1 / 2 : Real)) * Inv.inv ((Real.log x)^3) +
    2 * x^(-(2 / 3 : Real)) * Inv.inv (Real.log x) +
    Real.log (2 * Real.pi) * x^(-(1 : Real)) * Inv.inv (Real.log x)

theorem robin_prime_power_sub_psi_tail_le_scalar
    (hRH : RiemannHypothesis) {x : Real} (hx : 20000 <= x) :
    robinPrimePowerWeightedTail 1 x - robinPsiWeightedErrorIntegral 1 x <=
      robinMertensWeightedScalar x := by
  have hxOne : 1 < x := by linarith
  have hPower := robinPrimePowerWeightedTail_one_upper hRH hx
  have hHalf := robinZeroKernel_half_one_upper hxOne
  have hThird := robinZeroKernel_third_one_upper hxOne
  have hPsi := (robinPsiWeightedErrorIntegral_bounds_all hRH (n := 1) (by omega)
    (by linarith : 2 <= x)).1
  have hScalar : robinPsiWeightedErrorScalar 1 x =
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        x^(-(1 / 2 : Real)) *
          (Inv.inv (Real.log x) + Inv.inv ((Real.log x)^2) +
            4 * Inv.inv ((Real.log x)^3)) := by
    unfold robinPsiWeightedErrorScalar
    norm_num
    field_simp [(Real.log_pos hxOne).ne']
  rw [hScalar] at hPsi
  norm_num at hPsi
  unfold robinMertensWeightedScalar
  linarith


end

end Robin1984
