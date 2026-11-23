import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Robin1984.GRH.DedekindThetaDilation
import Robin1984.GRH.DualIdealRepresentative

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The trace-dual fractional ideal and the different of a number field.
- Formalization note: The norm of an integral representative of the trace-dual ideal.
- PROVENANCE-END
-/

/-!
# The norm of an integral representative of the trace-dual ideal

The ideal norm accounts for the archimedean dilation when the completed
Dedekind zeta functional equation exchanges dual ideal classes.
-/

open DedekindZeta.ConeRadialReduction NumberField

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

local notation "R" => RingOfIntegers K
local notation "F" => FractionalIdeal (nonZeroDivisors R) K

private theorem idealDifferentProduct_ne_zero (a : Ideal R) (ha : Not (a = 0)) :
    Not ((a : F) * Theta.differentFractionalIdeal K = 0) := by
  have hA : Not (a = (Bot.bot : Ideal R)) := by simpa only [Ideal.zero_eq_bot] using ha
  have hD : Not (differentIdeal Int R = (Bot.bot : Ideal R)) := differentIdeal_ne_bot
  have neFrac (I : Ideal R) := FractionalIdeal.coeIdeal_ne_zero'
    (P := K) (S := nonZeroDivisors R) (I := I) le_rfl
  exact mul_ne_zero ((neFrac a).mpr hA) ((neFrac (differentIdeal Int R)).mpr hD)

/-- Multiplying an integral representative of the trace-dual by
the original ideal and the different gives the clearing principal ideal. -/
theorem integral_dual_representative_mul (a b : Ideal R) (ha : Not (a = 0)) (m : Nat)
    (hb : (b : F) = FractionalIdeal.spanSingleton (nonZeroDivisors R) (m : K) *
      Theta.dualIdeal K a) :
    b * (a * differentIdeal Int R) = Ideal.span {(m : R)} := by
  let D : Ideal R := differentIdeal Int R
  let A : F := (a : F) * (D : F)
  have hA : Not (A = 0) := idealDifferentProduct_ne_zero K a ha
  have hInv : Inv.inv A * A = 1 := by rw [mul_comm, <- div_eq_mul_inv, div_self hA]
  have hFrac : (b : F) * A = FractionalIdeal.spanSingleton (nonZeroDivisors R) (m : K) := by
    rw [hb]
    change (FractionalIdeal.spanSingleton (nonZeroDivisors R) (m : K) * Inv.inv A) * A = _
    rw [mul_assoc, hInv, mul_one]
  apply FractionalIdeal.coeIdeal_injective' (S := nonZeroDivisors R) (P := K) le_rfl
  change ((b * (a * D) : Ideal R) : F) = ((Ideal.span {(m : R)} : Ideal R) : F)
  rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_span_singleton, map_natCast]
  exact hFrac

/-- The norm identity for the integral representative of the trace-dual. -/
theorem norm_integral_dual_representative (a b : Ideal R) (ha : Not (a = 0)) (m : Nat)
    (hb : (b : F) = FractionalIdeal.spanSingleton (nonZeroDivisors R) (m : K) *
      Theta.dualIdeal K a) :
    Ideal.absNorm b * (Ideal.absNorm a * (discr K).natAbs) = m ^ Module.finrank Rat K := by
  let D : Ideal R := differentIdeal Int R
  have hIdeal : b * (a * D) = Ideal.span {(m : R)} :=
    integral_dual_representative_mul K a b ha m hb
  calc
    _ = Ideal.absNorm (b * (a * D)) := by
      rw [map_mul, map_mul, show Ideal.absNorm D = (discr K).natAbs from absNorm_differentIdeal K R]
    _ = _ := by
      rw [hIdeal, Ideal.absNorm_span_natCast, IsFractionRing.finrank_eq Int Rat R K]

/-- Choose an integral representative of the trace-dual ideal, with the
arithmetic normalization and all positive-radius theta identities. -/
theorem exists_scaled_integral_dual_representative (a : Ideal R) (ha : Not (a = 0)) :
    exists m : Nat, And (0 < m) (exists b : Ideal R, And (Not (b = 0))
      (And (Ideal.absNorm b * (Ideal.absNorm a * (discr K).natAbs) = m ^ Module.finrank Rat K)
        (forall r : Real, 0 < r -> radialThetaDual K a r =
          radialTheta K b (r / (m : Real) ^ Module.finrank Rat K)))) := by
  have hDual : Not (Theta.dualIdeal K a = 0) :=
    inv_ne_zero (idealDifferentProduct_ne_zero K a ha)
  choose m hm b hb hScaled using exists_integral_natural_multiple K (Theta.dualIdeal K a) hDual
  exact Exists.intro m (And.intro hm (Exists.intro b (And.intro hb
    (And.intro (norm_integral_dual_representative K a b ha m hScaled)
      (fun r hr => radialThetaDual_eq_radialTheta_natural_rescale K a b hm hScaled hr)))))

end DedekindZeta
