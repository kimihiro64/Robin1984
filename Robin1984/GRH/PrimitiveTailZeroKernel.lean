import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The divided difference of a genus-one logarithmic derivative at the Dedekind pole normalization.
- Formalization note: Subtract the value at one before summing the Hadamard terms. Each term then has the exact primitive-tail weight and Mellin denominator.
- PROVENANCE-END
-/

/-!
# The zero kernel of the signed primitive tail

The divided difference at one turns each regularized logarithmic
derivative term into a simple-pole Mellin transform with coefficient
one over the zero times one minus the zero.
-/

namespace Robin1984.GRH

/-- The genus-one logarithmic derivative divided by its argument, after
subtracting the value at one and dividing by one minus the argument.
The two elementary summands come from the zero at zero and the constant
logarithmic derivative of the exponential factor. -/
theorem primitiveTailKernel_eq_hadamardZeroSeries {I : Type*}
    (rho : I -> Complex) (a m s : Complex) (hs0 : Not (s = 0)) (hs1 : Not (s = 1))
    (hr0 : forall i, Not (rho i = 0)) (hr1 : forall i, Not (rho i = 1))
    (hrs : forall i, Not (s = rho i))
    (hAtS : Summable (fun i => 1 / (rho i * (s - rho i))))
    (hAtOne : Summable (fun i => 1 / (rho i * (1 - rho i)))) :
    ((m / s ^ (2 : Nat) + a / s + tsum (fun i => 1 / (rho i * (s - rho i)))) -
      (m + a + tsum (fun i => 1 / (rho i * (1 - rho i))))) / (1 - s) =
      (a + m) / s + m / s ^ (2 : Nat) +
        tsum (fun i => 1 / (rho i * (1 - rho i) * (s - rho i))) := by
  have hd : Not (1 - s = 0) := sub_ne_zero.mpr (fun h => hs1 h.symm)
  have hTerm (i : I) :
      (1 / (rho i * (s - rho i)) - 1 / (rho i * (1 - rho i))) / (1 - s) =
        1 / (rho i * (1 - rho i) * (s - rho i)) := by
    have hdOne : Not (1 - rho i = 0) := sub_ne_zero.mpr (fun h => hr1 i h.symm)
    field_simp [hd, hr0 i, hdOne, sub_ne_zero.mpr (hrs i)]
    ring
  have hSeries := (hAtS.hasSum.sub hAtOne.hasSum).div_const (1 - s)
  change HasSum (fun i =>
    (1 / (rho i * (s - rho i)) - 1 / (rho i * (1 - rho i))) / (1 - s))
    ((tsum (fun i => 1 / (rho i * (s - rho i))) -
      tsum (fun i => 1 / (rho i * (1 - rho i)))) / (1 - s)) at hSeries
  simp_rw [hTerm] at hSeries
  rw [hSeries.tsum_eq]
  field_simp [hs0, hd]
  ring

end Robin1984.GRH
