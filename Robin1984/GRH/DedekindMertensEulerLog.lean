import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Robin1984.GRH.DedekindNormCoefficients

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The real logarithm power series and the Euler product for Dedekind zeta.
- Formalization note: Group the absolutely summable prime-power logarithm series by the natural norm.
- PROVENANCE-END
-/

/-!
# The Dedekind Mertens coefficients and the logarithm of zeta

Expand each real Euler factor, then group the absolutely convergent
prime-power sum by the natural norm. The local logarithm and the
norm-indexed logarithmic denominator agree exactly.
-/

open IsDedekindDomain NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "PP" => Prod P Nat

private theorem primeNorm_pos (p : P) : (0 : Real) < dedekindPrimeNorm K p := by
  exact_mod_cast zero_lt_one.trans (one_lt_dedekindPrimeNorm K p)

private theorem primeNorm_ge_two (p : P) : (2 : Real) <= dedekindPrimeNorm K p := by
  exact_mod_cast Nat.succ_le_of_lt (one_lt_dedekindPrimeNorm K p)

private theorem primePower_rpow_eq (pn : PP) (s : Real) :
    Real.rpow (dedekindPrimePowerNorm K pn : Real) (-s) =
      (Real.rpow (dedekindPrimeNorm K pn.1 : Real) (-s)) ^ (pn.2 + 1) := by
  have h := (primeNorm_pos K pn.1).le
  change (dedekindPrimePowerNorm K pn : Real) ^ (-s) =
    ((dedekindPrimeNorm K pn.1 : Real) ^ (-s)) ^ (pn.2 + 1)
  unfold dedekindPrimePowerNorm
  rw [Nat.cast_pow]
  calc
    _ = ((dedekindPrimeNorm K pn.1 : Real) ^ ((pn.2 + 1 : Nat) : Real)) ^ (-s) := by
      rw [Real.rpow_natCast]
    _ = (dedekindPrimeNorm K pn.1 : Real) ^ (((pn.2 + 1 : Nat) : Real) * (-s)) :=
      (Real.rpow_mul h _ _).symm
    _ = _ := by rw [mul_comm _ (-s), Real.rpow_mul h, Real.rpow_natCast]

private theorem log_primePower_norm (pn : PP) :
    Real.log (dedekindPrimePowerNorm K pn : Real) =
      ((pn.2 + 1 : Nat) : Real) * Real.log (dedekindPrimeNorm K pn.1 : Real) := by
  rw [dedekindPrimePowerNorm, Nat.cast_pow, Real.log_pow]

private theorem ofReal_primeNorm_rpow (p : P) (s : Real) :
    (Real.rpow (dedekindPrimeNorm K p : Real) (-s) : Complex) =
      (dedekindPrimeNorm K p : Complex) ^ (-(s : Complex)) := by
  change (((dedekindPrimeNorm K p : Real) ^ (-s) : Real) : Complex) = _
  rw [Complex.ofReal_cpow (primeNorm_pos K p).le, Complex.ofReal_natCast, Complex.ofReal_neg]

private theorem ofReal_primePowerNorm_rpow (pn : PP) (s : Real) :
    (Real.rpow (dedekindPrimePowerNorm K pn : Real) (-s) : Complex) =
      (dedekindPrimePowerNorm K pn : Complex) ^ (-(s : Complex)) := by
  change (((dedekindPrimePowerNorm K pn : Real) ^ (-s) : Real) : Complex) = _
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, Complex.ofReal_neg]

private theorem primePowerTerm_ofReal (pn : PP) (s : Real) :
    dedekindPrimePowerTerm K pn.1 pn.2 (s : Complex) =
      (Real.log (dedekindPrimeNorm K pn.1 : Real) *
        Real.rpow (dedekindPrimePowerNorm K pn : Real) (-s) : Real) := by
  have hLog := Complex.ofReal_log (primeNorm_pos K pn.1).le
  rw [Complex.ofReal_natCast] at hLog
  unfold dedekindPrimePowerTerm
  rw [Complex.ofReal_mul, hLog, ofReal_primePowerNorm_rpow]
  rfl

/-- On the real initial half-line, the Dirichlet coefficients obtained by
dividing the norm coefficients by log norm sum to the logarithm of the
Dedekind zeta function. -/
theorem hasSum_dedekindMertensLogCoeff {s : Real} (hs : 1 < s) :
    LSeriesHasSum (fun n : Nat => (dedekindNormCoeff K n : Complex) / (Real.log (n : Real) : Complex))
      (s : Complex) (Real.log (dedekindZeta K (s : Complex)).re : Complex) := by
  classical
  let r := fun p : P => Real.rpow (dedekindPrimeNorm K p : Real) (-s)
  let U := fun pn : PP => r pn.1 ^ (pn.2 + 1) / ((pn.2 + 1 : Nat) : Real)
  let B := tsum U
  have hOne : forall p : P, 1 < (dedekindPrimeNorm K p : Real) :=
    fun p => (show (1 : Real) < 2 by norm_num).trans_le (primeNorm_ge_two K p)
  have hRPos : forall p : P, 0 < r p := fun p => Real.rpow_pos_of_pos (primeNorm_pos K p) _
  have hRLess : forall p : P, r p < 1 := fun p =>
    Real.rpow_lt_one_of_one_lt_of_neg (hOne p) (neg_lt_zero.mpr (zero_lt_one.trans hs))
  have hS : 1 < (s : Complex).re := by simpa only [Complex.ofReal_re] using hs
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDom (pn : PP) : U pn <= Inv.inv (Real.log 2) *
      norm (dedekindPrimePowerTerm K pn.1 pn.2 (s : Complex)) := by
    have hPow : 0 <= r pn.1 ^ (pn.2 + 1) := pow_nonneg (hRPos pn.1).le _
    have hExp : (1 : Real) <= ((pn.2 + 1 : Nat) : Real) := by exact_mod_cast Nat.succ_pos pn.2
    have hLog := Real.log_le_log (by norm_num : (0 : Real) < 2) (primeNorm_ge_two K pn.1)
    have hNorm : norm (dedekindPrimePowerTerm K pn.1 pn.2 (s : Complex)) =
        Real.log (dedekindPrimeNorm K pn.1 : Real) * r pn.1 ^ (pn.2 + 1) := by
      rw [primePowerTerm_ofReal, Complex.norm_real, Real.norm_eq_abs, primePower_rpow_eq]
      exact abs_of_nonneg (mul_nonneg (Real.log_nonneg (hOne pn.1).le) hPow)
    calc
      U pn <= r pn.1 ^ (pn.2 + 1) := div_le_self hPow hExp
      _ = Inv.inv (Real.log 2) * (Real.log 2 * r pn.1 ^ (pn.2 + 1)) := by
        field_simp [hLog2.ne']
      _ <= _ := by
        rw [hNorm]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLog hPow)
          (inv_nonneg.mpr hLog2.le)
  have hSum : Summable U := Summable.of_nonneg_of_le
    (fun pn => div_nonneg (pow_nonneg (hRPos pn.1).le _)
      (Nat.cast_nonneg (pn.2 + 1))) hDom
    ((summable_norm_dedekindPrimePowerTerm K hS).mul_left _)
  have hLogSum : HasSum (fun p : P => -Real.log (1 - r p)) B := by
    have hFiber := hSum.hasSum.tsum_fiberwise (fun pn : PP => pn.1)
    have hEq : (fun p : P => tsum (fun pn : {q : PP // q.1 = p} => U pn.val)) =
        fun p : P => -Real.log (1 - r p) := by
      funext p
      let index : Equiv {pn : PP // pn.1 = p} Nat :=
        Equiv.mk (fun pn => pn.val.2) (fun k => Subtype.mk (p, k) rfl)
          (fun pn => Subtype.ext (Prod.ext pn.property.symm rfl)) (fun _ => rfl)
      have hLog : HasSum (fun k : Nat => U (p, k)) (-Real.log (1 - r p)) := by
        simpa only [U, Nat.cast_add, Nat.cast_one] using
          Real.hasSum_pow_div_log_of_abs_lt_one ((abs_of_pos (hRPos p)).trans_lt (hRLess p))
      rw [<- hLog.tsum_eq]
      calc
        _ = tsum (fun pn : {q : PP // q.1 = p} => U (p, index pn)) := by
          apply tsum_congr
          intro pn
          exact congrArg U (Prod.ext pn.property rfl)
        _ = _ := index.tsum_eq (fun k => U (p, k))
    rw [<- hEq]
    exact hFiber
  have hZeta : dedekindZeta K (s : Complex) = (Real.exp B : Complex) := by
    rw [dedekindZeta_eq_exp_tsum_log_eulerFactors K hS, Complex.ofReal_exp]
    congr 1
    rw [<- hLogSum.tsum_eq, Complex.ofReal_tsum]
    congr 1
    funext p
    have h := Complex.ofReal_log (sub_nonneg.mpr (hRLess p).le)
    rw [Complex.ofReal_sub, Complex.ofReal_one, ofReal_primeNorm_rpow] at h
    rw [Complex.ofReal_neg, h]
  have hLogZeta : Real.log (dedekindZeta K (s : Complex)).re = B := by
    rw [hZeta, Complex.ofReal_re, Real.log_exp]
  have hCoeff (pn : PP) :
      (U pn : Complex) = (Real.log (dedekindPrimeNorm K pn.1 : Real) : Complex) *
        ((dedekindPrimePowerNorm K pn : Complex) ^ (-(s : Complex)) /
          (Real.log (dedekindPrimePowerNorm K pn : Real) : Complex)) := by
    have hReal : U pn = Real.log (dedekindPrimeNorm K pn.1 : Real) *
        (Real.rpow (dedekindPrimePowerNorm K pn : Real) (-s) /
          Real.log (dedekindPrimePowerNorm K pn : Real)) := by
      rw [primePower_rpow_eq, log_primePower_norm]
      have hk : Not (((pn.2 + 1 : Nat) : Real) = 0) := by
        exact_mod_cast Nat.succ_ne_zero pn.2
      unfold U r
      field_simp [hk, (Real.log_pos (hOne pn.1)).ne']
    rw [hReal, Complex.ofReal_mul, Complex.ofReal_div, ofReal_primePowerNorm_rpow]
  have hComplex : HasSum (fun pn : PP => (U pn : Complex)) (B : Complex) :=
    Complex.ofRealCLM.hasSum hSum.hasSum
  have hGrouped := hasSum_dedekindNormCoeff_mul K
    (v := fun n => (n : Complex) ^ (-(s : Complex)) / (Real.log (n : Real) : Complex))
    hComplex hCoeff
  have hsNZ : Not ((s : Complex) = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hS)
  change HasSum (LSeries.term
    (fun n : Nat => (dedekindNormCoeff K n : Complex) / (Real.log (n : Real) : Complex))
    (s : Complex)) (Real.log (dedekindZeta K (s : Complex)).re : Complex)
  have hTerms : LSeries.term
      (fun n : Nat => (dedekindNormCoeff K n : Complex) / (Real.log (n : Real) : Complex))
      (s : Complex) =
      fun n : Nat => (dedekindNormCoeff K n : Complex) *
        ((n : Complex) ^ (-(s : Complex)) / (Real.log (n : Real) : Complex)) := by
    funext n
    simp only [LSeries.term_of_ne_zero' hsNZ, Complex.cpow_neg, div_eq_mul_inv]
    ring
  rw [hLogZeta, hTerms]
  exact hGrouped

end Robin1984.GRH
