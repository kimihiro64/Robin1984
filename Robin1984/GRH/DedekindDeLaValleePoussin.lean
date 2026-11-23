import Mathlib.Tactic.Ring
import Robin1984.GRH.DedekindLogDerivative

/-!
# Dedekind logarithmic derivative positivity

The classical trigonometric polynomial with coefficients 3, 4, and 1
gives a positivity inequality for the negative logarithmic derivative
on three vertical translates in the initial half-plane.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The de la Vallee Poussin trigonometric argument for zeta nonvanishing on the line of absolute convergence.
- Formalization note: Take the real part termwise in the proven Dedekind prime-power Dirichlet series and use the exact square identity.
- PROVENANCE-END
-/

open IsDedekindDomain NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)

private theorem re_dedekindPrimePowerTerm (p : P) (n : Nat) (sigma t : Real) :
    (dedekindPrimePowerTerm K p n (Complex.mk sigma t)).re =
      Real.log (dedekindPrimeNorm K p : Real) *
        (Real.exp (Real.log ((dedekindPrimeNorm K p ^ (n + 1) : Nat) : Real) * (-sigma)) *
          Real.cos (Real.log ((dedekindPrimeNorm K p ^ (n + 1) : Nat) : Real) * t)) := by
  let q := dedekindPrimeNorm K p
  let r := q ^ (n + 1)
  have hq : 0 < q := Nat.zero_lt_one.trans (one_lt_dedekindPrimeNorm K p)
  have hr : 0 < r := pow_pos hq _
  have hqReal : 0 <= (q : Real) := Nat.cast_nonneg _
  have hrReal : 0 <= (r : Real) := Nat.cast_nonneg _
  have hrComplex : Not ((r : Complex) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  have hLogQ : Complex.log (q : Complex) = (Real.log (q : Real) : Complex) := by
    rw [Complex.ofReal_log hqReal, Complex.ofReal_natCast]
  have hLogR : Complex.log (r : Complex) = (Real.log (r : Real) : Complex) := by
    rw [Complex.ofReal_log hrReal, Complex.ofReal_natCast]
  let z : Complex := (Real.log (r : Real) : Complex) * (-Complex.mk sigma t)
  have hre : z.re = Real.log (r : Real) * (-sigma) := by
    simp only [z, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im, zero_mul, sub_zero]
  have him : z.im = -(Real.log (r : Real) * t) := by
    simp only [z, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im,
      zero_mul, add_zero, mul_neg]
  change (Complex.log (q : Complex) * (r : Complex) ^ (-Complex.mk sigma t)).re = _
  rw [hLogQ, Complex.cpow_def_of_ne_zero hrComplex, hLogR]
  change ((Real.log (q : Real) : Complex) * Complex.exp z).re = _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, hre, him, Real.cos_neg]

private theorem primePowerTerm_trigonometric_nonneg (pn : Prod P Nat) (sigma t : Real) :
    0 <= 3 * (dedekindPrimePowerTerm K pn.1 pn.2 (Complex.mk sigma 0)).re +
      4 * (dedekindPrimePowerTerm K pn.1 pn.2 (Complex.mk sigma t)).re +
      (dedekindPrimePowerTerm K pn.1 pn.2 (Complex.mk sigma (2 * t))).re := by
  simp only [re_dedekindPrimePowerTerm, mul_zero, Real.cos_zero, mul_one]
  let v := Real.log ((dedekindPrimeNorm K pn.1 ^ (pn.2 + 1) : Nat) : Real)
  let w := Real.log (dedekindPrimeNorm K pn.1 : Real)
  change 0 <= 3 * (w * Real.exp (v * (-sigma))) +
      4 * (w * (Real.exp (v * (-sigma)) * Real.cos (v * t))) +
      w * (Real.exp (v * (-sigma)) * Real.cos (v * (2 * t)))
  rw [show v * (2 * t) = 2 * (v * t) by ring, Real.cos_two_mul]
  have hq : (1 : Real) <= dedekindPrimeNorm K pn.1 := by
    exact_mod_cast (one_lt_dedekindPrimeNorm K pn.1).le
  have hw : 0 <= w := Real.log_nonneg hq
  calc
    0 <= w * Real.exp (v * (-sigma)) * (2 * (1 + Real.cos (v * t)) ^ 2) :=
      mul_nonneg (mul_nonneg hw (Real.exp_pos _).le)
        (mul_nonneg (by norm_num) (sq_nonneg _))
    _ = _ := by ring

/-- The real parts of the negative logarithmic derivative satisfy the
three-point inequality for every point on the line of real part greater
than one. -/
theorem dedekindLogDerivative_trigonometric_nonneg {sigma : Real} (hs : 1 < sigma) (t : Real) :
    0 <= 3 * (-deriv (dedekindZeta K) (Complex.mk sigma 0) /
        dedekindZeta K (Complex.mk sigma 0)).re +
      4 * (-deriv (dedekindZeta K) (Complex.mk sigma t) /
        dedekindZeta K (Complex.mk sigma t)).re +
      (-deriv (dedekindZeta K) (Complex.mk sigma (2 * t)) /
        dedekindZeta K (Complex.mk sigma (2 * t))).re := by
  have hSum (y : Real) :
      HasSum (fun pn : Prod P Nat => (dedekindPrimePowerTerm K pn.1 pn.2 (Complex.mk sigma y)).re)
        (-deriv (dedekindZeta K) (Complex.mk sigma y) / dedekindZeta K (Complex.mk sigma y)).re :=
    Complex.reCLM.hasSum (hasSum_dedekindPrimePowerTerm K hs)
  have h := (((hSum 0).mul_left (3 : Real)).add ((hSum t).mul_left (4 : Real))).add (hSum (2 * t))
  rw [<- h.tsum_eq]
  exact tsum_nonneg (fun pn => primePowerTerm_trigonometric_nonneg K pn sigma t)

end Robin1984.GRH
