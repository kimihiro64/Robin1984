import DedekindZeta.ConeMellinBridge
import Robin1984.GRH.DedekindDualNorm
import Robin1984.GRH.DedekindFunctionalEquation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The ideal norm scaling in the classwise theta-Mellin functional equation.
- Formalization note: Reflection of the normalized Mellin transform for an ideal and its dual.
- PROVENANCE-END
-/

/-!
# Reflection of the normalized Mellin transform for an ideal and its dual

The product of the lattice covolumes is the norm of the rational
denominator used to clear the dual ideal. This cancels the factor from
Mellin dilation.
-/

open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple NumberField
open scoped Real

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

local notation "R" => RingOfIntegers K
local notation "F" => FractionalIdeal (nonZeroDivisors R) K

private theorem covolume_pos (a : Ideal R) (ha : Not (a = 0)) : 0 < Theta.covolume K a := by
  have hN : (0 : Real) < (Ideal.absNorm a : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => ha (Ideal.absNorm_eq_zero_iff.mp h))
  have hD : (0 : Real) < |(discr K : Real)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  rw [Theta.covolume]
  exact mul_pos hN (Real.sqrt_pos_of_pos hD)

private theorem covolume_mul_eq_denominatorNorm (a b : Ideal R) (m : Nat)
    (hN : Ideal.absNorm b * (Ideal.absNorm a * (discr K).natAbs) = m ^ Module.finrank Rat K) :
    Theta.covolume K a * Theta.covolume K b = (m : Real) ^ Module.finrank Rat K := by
  have hNReal : (Ideal.absNorm b : Real) * ((Ideal.absNorm a : Real) *
      ((discr K).natAbs : Real)) = (m : Real) ^ Module.finrank Rat K := by
    exact_mod_cast hN
  have hSq : Real.sqrt |(discr K : Real)| * Real.sqrt |(discr K : Real)| =
      ((discr K).natAbs : Real) := by
    rw [<- pow_two, Real.sq_sqrt (abs_nonneg _), Nat.cast_natAbs, Int.cast_abs]
  calc
    _ = (Ideal.absNorm b : Real) * ((Ideal.absNorm a : Real) *
        (Real.sqrt |(discr K : Real)| * Real.sqrt |(discr K : Real)|)) := by
      simp only [Theta.covolume]
      ring
    _ = _ := by rw [hSq, hNReal]

private theorem posCpow_eq_exp_log (x : Real) (hx : 0 < x) (s : Complex) :
    (x : Complex) ^ s = Complex.exp ((Real.log x : Complex) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    <- Complex.ofReal_log hx.le]

private theorem normalizeCovolumeDilation (A B q : Real) (hA : 0 < A) (hB : 0 < B)
    (hq : A * B = q) (s : Complex) :
    (A : Complex) ^ s * (Inv.inv (A : Complex) * ((Inv.inv q : Real) : Complex) ^ (-(1 - s))) =
      (B : Complex) ^ (1 - s) := by
  have hQ : 0 < q := by
    rw [<- hq]
    exact mul_pos hA hB
  have hInv : Inv.inv (A : Complex) = Complex.exp (-(Real.log A : Complex)) := by
    rw [Complex.exp_neg, <- Complex.ofReal_exp, Real.exp_log hA]
  have hLog : Real.log (Inv.inv q) = -(Real.log A + Real.log B) := by
    rw [Real.log_inv, <- hq, Real.log_mul hA.ne' hB.ne']
  rw [posCpow_eq_exp_log A hA, hInv, posCpow_eq_exp_log _ (inv_pos.mpr hQ),
    posCpow_eq_exp_log B hB, hLog, Complex.ofReal_neg, Complex.ofReal_add,
    <- Complex.exp_add, <- Complex.exp_add]
  congr 1
  ring

/-- The meromorphic radial Mellin transform normalized by the ideal's
covolume. The normalization includes the finite torsion-unit factor. -/
noncomputable def completedIdealContinuation (a : Ideal R) (s : Complex) : Complex :=
  (1 / (Units.torsionOrder K : Complex)) * (Theta.covolume K a : Complex) ^ s *
    mellinContinuation (radialTheta K a) (radialThetaDual K a)
      (surfaceVolume K) (surfaceVolume K) (Inv.inv (Theta.covolume K a : Complex)) 1 s

/-- For a nonzero ideal and an integral representative of its trace-dual,
the normalized Mellin transforms agree under `s -> 1 - s`. -/
theorem completedIdealContinuation_eq_dual (a b : Ideal R) (ha : Not (a = 0))
    (hb : Not (b = 0)) {m : Nat} (hm : 0 < m)
    (hScaled : (b : F) = FractionalIdeal.spanSingleton (nonZeroDivisors R) (m : K) * Theta.dualIdeal K a)
    {s : Complex} (hs0 : Not (s = 0)) (hs1 : Not (s = 1)) :
    completedIdealContinuation K a s = completedIdealContinuation K b (1 - s) := by
  choose c alpha hPa using exists_isMellinPair_radialTheta (K := K) a ha
  choose c' alpha' hPb using exists_isMellinPair_radialTheta (K := K) b hb
  let q : Real := (m : Real) ^ Module.finrank Rat K
  have hQ : 0 < q := pow_pos (show (0 : Real) < (m : Real) from Nat.cast_pos.mpr hm) _
  have hScale (y : Real) (hy : 0 < y) : radialThetaDual K a y = radialTheta K b (y * Inv.inv q) := by
    rw [<- div_eq_mul_inv]
    exact radialThetaDual_eq_radialTheta_natural_rescale K a b hm hScaled hy
  have hRefl := mellinContinuation_eq_mul_swap (radialTheta K a) (radialThetaDual K a)
    (surfaceVolume K) (surfaceVolume K) (Inv.inv (Theta.covolume K a : Complex)) 1 s
    hPa.hC hs0 (by simpa using hs1)
  have h1s0 : Not ((1 : Complex) - s = 0) := sub_ne_zero.mpr (Ne.symm hs1)
  have h1s1 : Not ((1 : Complex) - s - 1 = 0) := by
    rw [show (1 : Complex) - s - 1 = -s by ring]
    exact neg_ne_zero.mpr hs0
  have hDilate := mellinContinuation_dilation hPa.swap hPb (inv_pos.mpr hQ) hScale h1s0 h1s1
  have hProduct : Theta.covolume K a * Theta.covolume K b = q :=
    covolume_mul_eq_denominatorNorm K a b m (norm_integral_dual_representative K a b ha m hScaled)
  have hCoef := normalizeCovolumeDilation _ _ _ (covolume_pos K a ha) (covolume_pos K b hb) hProduct s
  unfold completedIdealContinuation
  rw [hRefl, Complex.ofReal_one, hDilate]
  rw [<- hCoef]
  ring

private theorem covolume_cpow_eq_norm_discriminant (a : Ideal R) (s : Complex) :
    (Theta.covolume K a : Complex) ^ s =
      (Ideal.absNorm a : Complex) ^ s * (((|discr K| : Int) : Complex) ^ (s / 2)) := by
  let d : Real := |(discr K : Real)|
  have hd : 0 < d := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hCast : (d : Complex) = ((|discr K| : Int) : Complex) := by
    dsimp [d]
    rw [<- Int.cast_abs, Complex.ofReal_intCast]
  have hsqrt : ((Real.sqrt d : Real) : Complex) ^ s = (d : Complex) ^ (s / 2) := by
    rw [posCpow_eq_exp_log _ (Real.sqrt_pos_of_pos hd), posCpow_eq_exp_log d hd, Real.log_sqrt hd.le]
    congr 1
    push_cast <;> ring
  rw [Theta.covolume]
  change (((Ideal.absNorm a : Real) * Real.sqrt d : Real) : Complex) ^ s = _
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _),
    Complex.ofReal_natCast, hsqrt, hCast]

/-- The normalized continuation is the original completed partial zeta
throughout its half-plane of absolute convergence. -/
theorem completedIdealContinuation_eq_completedPartialZeta (a : Ideal R) (ha : Not (a = 0))
    {s : Complex} (hs : 1 < s.re) :
    completedIdealContinuation K a s = completedPartialZeta K a s := by
  rw [completedIdealContinuation, ConeMellinBridge.completedPartialZeta_eq_mellinContinuation a ha hs,
    covolume_cpow_eq_norm_discriminant]
  ring

/-- The normalized completed partial zeta with both candidate poles
cleared. Its value at each pole is obtained from the entire expression. -/
noncomputable def completedIdealPoleCleared (a : Ideal R) (s : Complex) : Complex :=
  (1 / (Units.torsionOrder K : Complex)) * (Theta.covolume K a : Complex) ^ s *
    poleClearedMellin (radialTheta K a) (radialThetaDual K a)
      (surfaceVolume K) (Inv.inv (Theta.covolume K a : Complex)) s

/-- The pole-cleared completed partial zeta of a nonzero ideal is entire. -/
theorem analyticAt_completedIdealPoleCleared (a : Ideal R) (ha : Not (a = 0)) (s : Complex) :
    AnalyticAt Complex (completedIdealPoleCleared K a) s := by
  let u := Theta.covolume K a
  have hComp : AnalyticAt Complex (fun w : Complex =>
      Complex.exp ((Real.log u : Complex) * w)) s :=
    analyticAt_cexp.comp (f := fun w : Complex => (Real.log u : Complex) * w)
      (analyticAt_const.mul analyticAt_id)
  have hPower : AnalyticAt Complex (fun w : Complex => (u : Complex) ^ w) s :=
    hComp.congr (Filter.Eventually.of_forall (fun w =>
      (posCpow_eq_exp_log u (covolume_pos K a ha) w).symm))
  choose c alpha hPair using exists_isMellinPair_radialTheta (K := K) a ha
  exact (analyticAt_const.mul hPower).mul (analyticAt_poleClearedMellin hPair s)

theorem completedIdealPoleCleared_eq (a : Ideal R) {s : Complex}
    (hs0 : Not (s = 0)) (hs1 : Not (s = 1)) :
    completedIdealPoleCleared K a s = s * (s - 1) * completedIdealContinuation K a s := by
  simp only [completedIdealPoleCleared, completedIdealContinuation,
    poleClearedMellin_eq hs0 (sub_ne_zero.mpr hs1)]
  ring

end DedekindZeta
