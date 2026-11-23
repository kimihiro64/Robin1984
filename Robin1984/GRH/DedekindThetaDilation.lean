import DedekindZeta.ConeRadialReduction

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The scaling law for the ideal theta kernel.
- Formalization note: Scaling the fractional-ideal theta kernel.
- PROVENANCE-END
-/

/-!
# Scaling the fractional-ideal theta kernel

Multiplying a fractional ideal by a rational integer dilates the
radial coordinate by the corresponding field norm.
-/

open DedekindZeta.ConeRadialReduction MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

local notation "R" => RingOfIntegers K
local notation "F" => FractionalIdeal (nonZeroDivisors R) K

private abbrev nonzeroElement (I : F) :=
  {a : K // And (Membership.mem I a) (Not (a = 0))}

private noncomputable def scaleFractionalIdealElements (I : F) {c : K} (hc : Not (c = 0)) :
    Equiv (nonzeroElement K I)
      (nonzeroElement K (FractionalIdeal.spanSingleton (nonZeroDivisors R) c * I)) := by
  let J : F := FractionalIdeal.spanSingleton (nonZeroDivisors R) c * I
  have hIJ : And
      (forall z, Membership.mem J z -> exists a, And (Membership.mem I a) (c * a = z))
      (forall a, Membership.mem I a -> Membership.mem J (c * a)) :=
    FractionalIdeal.eq_spanSingleton_mul.mp (rfl : J = _)
  let e : nonzeroElement K I -> nonzeroElement K J := fun a =>
    Subtype.mk (c * a.val) (And.intro (hIJ.2 a.val a.property.1) (mul_ne_zero hc a.property.2))
  refine Equiv.ofBijective e (And.intro ?hInjective ?hSurjective)
  case hInjective =>
    intro a b h
    have hMul := congrArg (fun z : nonzeroElement K J => Inv.inv c * z.val) h
    change Inv.inv c * (c * a.val) = Inv.inv c * (c * b.val) at hMul
    apply Subtype.ext
    simpa [<- mul_assoc, hc] using hMul
  case hSurjective =>
    intro b
    choose a ha using hIJ.1 b.val b.property.1
    have hNonzero : Not (a = 0) := by
      intro h
      apply b.property.2
      simpa [h] using ha.2.symm
    exact Exists.intro (Subtype.mk a (And.intro ha.1 hNonzero)) (Subtype.ext ha.2)

/-- A principal fractional factor can be moved from the ideal into
the point at which the theta kernel is evaluated. -/
theorem mixedThetaKernel_spanSingleton_mul (I : F) {c : K} (hc : Not (c = 0))
    (x : mixedSpace K) :
    Theta.mixedThetaKernel K (FractionalIdeal.spanSingleton (nonZeroDivisors R) c * I) x =
      Theta.mixedThetaKernel K I (x * mixedEmbedding K c) := by
  let e := scaleFractionalIdealElements K I hc
  let J := FractionalIdeal.spanSingleton (nonZeroDivisors R) c * I
  let G (y : mixedSpace K) (a : K) : Complex := Theta.mixedGaussian K (y * mixedEmbedding K a)
  change (tsum (fun b : nonzeroElement K J => G x b.val)) =
    tsum (fun a : nonzeroElement K I => G (x * mixedEmbedding K c) a.val)
  calc
    _ = tsum (fun a : nonzeroElement K I => G x (e a).val) :=
      (e.tsum_eq (fun b : nonzeroElement K J => G x b.val)).symm
    _ = _ := by
      apply tsum_congr
      intro a
      change G x (c * a.val) = G (x * mixedEmbedding K c) a.val
      dsimp [G]
      rw [map_mul, mul_assoc]

private theorem radialMap_mul_mixedEmbedding_nat {m : Nat} (hm : 0 < m)
    {r : Real} (hr : 0 < r) (x : mixedSpace K) :
    radialMap K (r / (m : Real) ^ Module.finrank Rat K) x * mixedEmbedding K (m : K) =
      radialMap K r x := by
  have hmR : (0 : Real) < (m : Real) := Nat.cast_pos.mpr hm
  have hd : Not ((Module.finrank Rat K : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (Module.finrank_pos : 0 < Module.finrank Rat K))
  have hNat : (m : mixedSpace K) = algebraMap Real (mixedSpace K) (m : Real) := by rw [map_natCast]
  rw [map_natCast, hNat, mul_comm, <- Algebra.smul_def]
  simp only [radialMap, smul_smul]
  congr 1
  rw [Real.div_rpow hr.le (pow_nonneg hmR.le _) _, <- Real.rpow_natCast,
    <- Real.rpow_mul hmR.le, show (Module.finrank Rat K : Real) *
        Inv.inv (Module.finrank Rat K : Real) = 1 by field_simp, Real.rpow_one]
  field_simp

/-- If scaling a trace-dual ideal by the positive integer `m` produces
the integral ideal `b`, the two radial theta functions differ by the
dilation of their norm coordinate. -/
theorem radialThetaDual_eq_radialTheta_natural_rescale (a b : Ideal R)
    {m : Nat} (hm : 0 < m)
    (hb : (b : F) = FractionalIdeal.spanSingleton (nonZeroDivisors R) (m : K) *
      Theta.dualIdeal K a) {r : Real} (hr : 0 < r) :
    radialThetaDual K a r = radialTheta K b (r / (m : Real) ^ Module.finrank Rat K) := by
  unfold radialThetaDual radialTheta orbitThetaFrac orbitTheta
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun x => ?_)
  change Theta.mixedThetaKernel K (Theta.dualIdeal K a) (radialMap K r x) =
    Theta.idealThetaKernel K b (radialMap K (r / (m : Real) ^ Module.finrank Rat K) x)
  rw [Theta.idealThetaKernel_eq_mixed, hb, mixedThetaKernel_spanSingleton_mul K _
    (Nat.cast_ne_zero.mpr hm.ne'), radialMap_mul_mixedEmbedding_nat K hm hr]

end DedekindZeta
