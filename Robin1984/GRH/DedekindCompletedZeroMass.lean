import Robin1984.GRH.DedekindCompletedHadamard

/-!
# The mass of the completed Dedekind zeros

Subtract the Hadamard logarithmic derivatives at 2 and -1. The functional equation relates their values, and each zero on the critical line contributes a nonnegative term that controls the inverse squared norm.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The explicit logarithmic derivative bound for the Dedekind zero sum under ERH.
- Formalization note: Subtract the convergent Hadamard sums at reflected points and compare the resulting terms.
- Content basis: The completed functional equation and the critical-line location of its zeros.
- Dependency status: Optional GRH extension and PrimeNumberTheoremAnd.
-/

open DedekindZeta NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

private theorem logDeriv_completed_reflect_two :
    logDeriv (completedDedekindPoleCleared K) (-1) =
      -logDeriv (completedDedekindPoleCleared K) 2 := by
  let F := completedDedekindPoleCleared K
  let r : Complex -> Complex := fun z => 1 - z
  have hF : F = F.comp r := funext (completedDedekindPoleCleared_functionalEquation K)
  have hR : HasDerivAt r (-1) 2 := by
    change HasDerivAt ((fun _ : Complex => 1) - id) (-1) 2
    have h := (hasDerivAt_const (x := (2 : Complex)) (1 : Complex)).sub
      (hasDerivAt_id (2 : Complex))
    rw [zero_sub] at h
    exact h
  have hD : DifferentiableAt Complex F (r 2) :=
    (analyticAt_completedDedekindPoleCleared K (r 2)).differentiableAt
  have h := congrArg (fun f : Complex -> Complex => logDeriv f 2) hF
  change logDeriv F 2 = logDeriv (F.comp r) 2 at h
  rw [logDeriv_comp hD hR.differentiableAt, hR.deriv, mul_neg_one] at h
  have hr2 : r 2 = -1 := by norm_num [r]
  rw [hr2] at h
  change logDeriv F (-1) = -logDeriv F 2
  rw [h, neg_neg]

private theorem zeroTerm_difference_re {z : Complex} (hz : z.re = 1 / 2) :
    ((1 / (2 - z) + 1 / z) - (1 / (-1 - z) + 1 / z)).re =
      3 / (9 / 4 + z.im ^ 2) := by
  have hPos : (2 - z).normSq = 9 / 4 + z.im ^ 2 := by
    norm_num [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz]
    ring
  have hNeg : (-1 - z).normSq = 9 / 4 + z.im ^ 2 := by
    norm_num [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz]
    ring
  rw [add_sub_add_right_eq_sub]
  simp only [Complex.sub_re, one_div, Complex.inv_re, hPos, hNeg, Complex.neg_re,
    Complex.one_re, hz]
  have hTwo : (2 : Complex).re = 2 := by norm_num
  rw [hTwo]
  ring

private theorem zeroWeight_le_difference_re {z : Complex} (hz : z.re = 1 / 2) :
    (Inv.inv (norm z)) ^ (2 : Nat) <=
      3 * ((1 / (2 - z) + 1 / z) - (1 / (-1 - z) + 1 / z)).re := by
  rw [zeroTerm_difference_re hz, inv_pow, Complex.sq_norm]
  have hSq : z.normSq = 1 / 4 + z.im ^ 2 := by
    simp only [Complex.normSq_apply, hz]
    ring
  rw [hSq]
  have hPos : 0 < 1 / 4 + z.im ^ 2 := by positivity
  have hPos' : 0 < 9 / 4 + z.im ^ 2 := by positivity
  field_simp
  nlinarith [sq_nonneg z.im]

/-- Under Dedekind RH the inverse-square zero mass is at most six times the
real part of the logarithmic derivative of the entire completion at two. -/
theorem completedDedekindZeroMass_le_six_logDeriv (hRH : DedekindRH K) :
    tsum (fun i : DedekindCompletedZeroIndex K =>
      (Inv.inv (norm (completedDedekindZero K i))) ^ (2 : Nat)) <=
      6 * (logDeriv (completedDedekindPoleCleared K) 2).re := by
  let F := completedDedekindPoleCleared K
  let Z := completedDedekindZero K
  let T (s : Complex) (i : DedekindCompletedZeroIndex K) := 1 / (s - Z i) + 1 / Z i
  have hTwo : Not (F 2 = 0) :=
    completedDedekindPoleCleared_ne_zero_of_one_le_re K (by norm_num)
  have hNegOne : Not (F (-1) = 0) := by
    change Not (completedDedekindPoleCleared K (-1) = 0)
    rw [completedDedekindPoleCleared_functionalEquation K (-1)]
    rw [show (1 : Complex) - (-1) = 2 by norm_num]
    exact hTwo
  have hT2 : Summable (T 2) := summable_completedDedekindZero_logDerivTerm K hTwo
  have hTn : Summable (T (-1)) := summable_completedDedekindZero_logDerivTerm K hNegOne
  have hDiff := hT2.sub hTn
  have hMass := summable_completedDedekindZero_inv_sq K
  have hre : Summable (fun i : DedekindCompletedZeroIndex K => (T 2 i - T (-1) i).re) :=
    Complex.reCLM.summable hDiff
  have hle := hMass.tsum_le_tsum (g := fun i => 3 * (T 2 i - T (-1) i).re)
    (fun i => zeroWeight_le_difference_re
      (completedDedekindPoleCleared_zero_re_of_dedekindRH K hRH
        (completedDedekindZero_is_zero K i))) (hre.mul_left 3)
  rw [tsum_mul_left, <- Complex.re_tsum hDiff, hT2.tsum_sub hTn] at hle
  choose b hb using completedDedekindPoleCleared_logDeriv_eq_zeroSum K
  have hEq : ((tsum (T 2)) - tsum (T (-1))).re = 2 * (logDeriv F 2).re := by
    have h2 : logDeriv F 2 = b + tsum (T 2) := hb 2 hTwo
    have hn : logDeriv F (-1) = b + tsum (T (-1)) := hb (-1) hNegOne
    calc
      _ = ((b + tsum (T 2)) - (b + tsum (T (-1)))).re := by
        rw [add_sub_add_left_eq_sub]
      _ = (logDeriv F 2 - logDeriv F (-1)).re := by rw [<- h2, <- hn]
      _ = _ := by
        change (logDeriv F 2 - logDeriv (completedDedekindPoleCleared K) (-1)).re = _
        rw [logDeriv_completed_reflect_two K, sub_neg_eq_add, Complex.add_re]
        change (logDeriv F 2).re + (logDeriv F 2).re = _
        ring
  rw [hEq] at hle
  linarith

end Robin1984.GRH
