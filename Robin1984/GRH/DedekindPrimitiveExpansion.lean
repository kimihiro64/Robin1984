import Mathlib.Analysis.PSeries
import Robin1984.GRH.DedekindArchimedeanLogDerivative
import Robin1984.GRH.DedekindCompletedZeroMass
import Robin1984.GRH.PrimitiveTailZeroKernel

/-!
# The Dedekind logarithmic derivative divided by its argument

The Hadamard terms of the completed function and the gamma terms of the
completion each give a convergent simple-pole series. The series and
the separate zero at the origin determine the primitive-tail transform.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The partial-fraction expansion of the Dedekind logarithmic derivative.
- Formalization note: Divide the logarithmic derivative by its argument and express the gamma contributions as negative lattices.
- Content basis: Canonical Hadamard product, archimedean logarithmic derivative, and convergent zero weights.
- Dependency status: Optional GRH extension and PrimeNumberTheoremAnd.
-/

open DedekindZeta NumberField NumberField.InfinitePlace Set

namespace Robin1984.GRH

/-- The power coefficient contributed by a nonzero zero in the primitive tail. -/
noncomputable def primitiveZeroWeight (rho : Complex) : Complex := 1 / (rho * (1 - rho))

variable (K : Type*) [Field K] [NumberField K]

/-- Under Dedekind RH the zero mass is at most 9 plus three times the logarithm of the absolute discriminant. -/
theorem completedDedekindZeroMass_le (hRH : DedekindRH K) :
    tsum (fun i : DedekindCompletedZeroIndex K =>
      (Inv.inv (norm (completedDedekindZero K i))) ^ (2 : Nat)) <=
      9 + 3 * Real.log ((discr K).natAbs : Real) := by
  have h1 := completedDedekindZeroMass_le_six_logDeriv K hRH
  have h2 := completedDedekind_logDeriv_two_le K
  linarith

private theorem dedekindCompletedZero_ne_zero (i : DedekindCompletedZeroIndex K) :
    Not (completedDedekindZero K i = 0) := i.property

/-- Summability of strictly positive masses makes the zero index countable. -/
theorem countable_dedekindCompletedZeroIndex : Countable (DedekindCompletedZeroIndex K) := by
  let z := completedDedekindZero K
  let v (i : DedekindCompletedZeroIndex K) : NNReal :=
    Real.toNNReal ((Inv.inv (norm (z i))) ^ (2 : Nat))
  have hv : Summable v := by
    apply NNReal.summable_coe.mp
    refine (summable_completedDedekindZero_inv_sq K).congr ?_
    intro i
    exact (Real.coe_toNNReal _ (sq_nonneg _)).symm
  have hS : Function.support v = univ := by
    refine Set.eq_univ_of_forall ?_
    intro i
    have h := norm_pos_iff.mpr (dedekindCompletedZero_ne_zero K i)
    have hV : 0 < (Inv.inv (norm (z i))) ^ (2 : Nat) := by positivity
    exact ne_of_gt (Real.toNNReal_pos.mpr hV)
  have h := Summable.countable_support_nnreal v hv
  rw [hS] at h
  exact Set.countable_univ_iff.mp h

theorem norm_primitiveZeroWeight_of_re_eq_half {rho : Complex} (hr : rho.re = 1 / 2) :
    norm (primitiveZeroWeight rho) = (Inv.inv (norm rho)) ^ (2 : Nat) := by
  have hSq : norm (1 - rho) ^ (2 : Nat) = norm rho ^ (2 : Nat) := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, zero_sub, hr]
    ring
  have he : norm (1 - rho) = norm rho := by
    have h : Not (rho = 0) := Complex.ne_zero_of_re_pos (by rw [hr]; norm_num)
    nlinarith [norm_pos_iff.mpr h, norm_nonneg (1 - rho)]
  rw [primitiveZeroWeight, norm_div, norm_one, norm_mul, he, <- pow_two, one_div, inv_pow]

theorem summable_norm_primitiveZeroWeight (hRH : DedekindRH K) :
    Summable (fun i : DedekindCompletedZeroIndex K => norm (primitiveZeroWeight (completedDedekindZero K i))) :=
  (summable_completedDedekindZero_inv_sq K).congr (fun i =>
    (norm_primitiveZeroWeight_of_re_eq_half
      (completedDedekindPoleCleared_zero_re_of_dedekindRH K hRH (completedDedekindZero_is_zero K i))).symm)

private theorem norm_gammaZeroWeight_le {q : Real} (hq : 1 <= q) (n : Nat) :
    norm (primitiveZeroWeight (gammaZero q n)) <= Inv.inv (((n + 1 : Nat) : Real) ^ (2 : Nat)) := by
  let a : Real := (n : Real) + 1
  let b : Real := q * a
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a <= b := by dsimp [b]; nlinarith
  have hb := ha.trans_le hab
  have h1b : 0 <= (1 + b) := by positivity
  have he : gammaZero q n = -((b : Real) : Complex) := rfl
  have hNorm : norm (1 - gammaZero q n) = 1 + b := by
    rw [he, sub_neg_eq_add, <- Complex.ofReal_one, <- Complex.ofReal_add,
      Complex.norm_real, Real.norm_of_nonneg h1b]
  rw [primitiveZeroWeight, norm_div, norm_one, norm_mul, hNorm, he, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg hb.le, Nat.cast_add, Nat.cast_one, <- one_div]
  change 1 / (b * (1 + b)) <= 1 / a ^ (2 : Nat)
  exact one_div_le_one_div_of_le (by positivity)
    (by rw [pow_two]; exact mul_le_mul hab (by linarith) ha.le hb.le)

theorem summable_norm_gammaZeroWeight {q : Real} (hq : 1 <= q) :
    Summable (fun n => norm (primitiveZeroWeight (gammaZero q n))) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_gammaZeroWeight_le hq) ?_
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : Nat)))

private theorem hasSum_completed_zeroLogDeriv_div (b : Complex)
    (hb : forall s : Complex, Not (completedDedekindPoleCleared K s = 0) ->
      logDeriv (completedDedekindPoleCleared K) s =
        b + tsum (fun i : DedekindCompletedZeroIndex K =>
          1 / (s - completedDedekindZero K i) + 1 / completedDedekindZero K i))
    {s : Complex} (hs0 : Not (s = 0)) (hn : Not (completedDedekindPoleCleared K s = 0)) :
    HasSum (fun i : DedekindCompletedZeroIndex K =>
      1 / (completedDedekindZero K i * (s - completedDedekindZero K i)))
      ((logDeriv (completedDedekindPoleCleared K) s - b) / s) := by
  let z := completedDedekindZero K
  have h := (summable_completedDedekindZero_logDerivTerm K hn).hasSum.div_const s
  have hTerm (i : DedekindCompletedZeroIndex K) :
      (1 / (s - z i) + 1 / z i) / s = 1 / (z i * (s - z i)) := by
    have hzi : Not (z i = 0) := dedekindCompletedZero_ne_zero K i
    have hN : Not (s - z i = 0) := sub_ne_zero.mpr (fun e => by
      apply hn
      rw [e]
      exact completedDedekindZero_is_zero K i)
    field_simp [hs0, hzi, hN]
    ring
  change HasSum (fun i : DedekindCompletedZeroIndex K => (1 / (s - z i) + 1 / z i) / s) _ at h
  simp_rw [hTerm] at h
  rw [hb s hn, add_sub_cancel_left]
  exact h

/-- The regularized logarithmic derivative splits into the completed zeros, the two gamma lattices, and the origin term. -/
theorem exists_dedekind_primitiveLogDeriv_expansion :
    exists a : Complex, forall s : Complex, 0 < s.re ->
      Not (completedDedekindPoleCleared K s = 0) ->
      (logDeriv (entirePoleFreeDedekindZeta K) s + 1) / s =
        ((nrRealPlaces K : Complex) + (nrComplexPlaces K : Complex) - 1) / s ^ (2 : Nat) +
        a / s +
        tsum (fun i : DedekindCompletedZeroIndex K =>
          1 / (completedDedekindZero K i * (s - completedDedekindZero K i))) +
        (nrRealPlaces K : Complex) * tsum (fun n => 1 / (gammaZero 2 n * (s - gammaZero 2 n))) +
        (nrComplexPlaces K : Complex) * tsum (fun n => 1 / (gammaZero 1 n * (s - gammaZero 1 n))) := by
  choose b hb using completedDedekindPoleCleared_logDeriv_eq_zeroSum K
  let r := (nrRealPlaces K : Complex)
  let c := (nrComplexPlaces K : Complex)
  refine Exists.intro (b + 1 - Complex.log ((discr K).natAbs : Complex) / 2 +
    r * ((Real.eulerMascheroniConstant : Complex) + Complex.log (Real.pi : Complex)) / 2 +
    c * ((Real.eulerMascheroniConstant : Complex) + Complex.log (2 * (Real.pi : Complex)))) ?_
  intro s hs hn
  have hs0 := Complex.ne_zero_of_re_pos hs
  have hZ := hasSum_completed_zeroLogDeriv_div K b hb hs0 hn
  have hR := hasSum_gammaZeroLogDeriv_div (q := 2) (by norm_num) hs
  have hC := hasSum_gammaZeroLogDeriv_div (q := 1) (by norm_num) hs
  rw [logDeriv_entirePoleFreeDedekindZeta K hs hn, logDeriv_dedekindArchimedean K hs,
    hZ.tsum_eq, hR.tsum_eq, hC.tsum_eq]
  simp only [Complex.ofReal_ofNat, Complex.ofReal_one, div_one]
  dsimp only [r, c]
  field_simp [hs0]
  ring

end Robin1984.GRH
