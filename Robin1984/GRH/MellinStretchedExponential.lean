import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Growth of a Mellin tail with stretched exponential decay

A complex Mellin tail of a function bounded by a stretched exponential
has growth at most the exponential of a constant times
`(1 + R) * log (2 + R)`, uniformly where its real exponent is at most `R`.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The logarithmic tangent bound for a stretched exponential moment.
- Formalization note: Adapt the envelope argument from AxiomMath/DedekindZetaZeroFree at 09afbb4ce6570c1615d58509dc197fc9f0956b7d.
- Content basis: PowerStretchedExponentialEnvelope and MellinTailBounds in that Apache-2.0 source.
- Dependency status: Mathlib only.
-/

open MeasureTheory Set

namespace Robin1984.GRH

private theorem stretchedExpMoment_envelope {a p R t : Real}
    (ha : 0 < a) (hp : 0 < p) (hR : 0 <= R) (ht : 1 <= t) :
    let c := 1 + 2 / (a * p)
    let K := (1 + Real.log c / Real.log 2) / p
    t ^ R * Real.exp (-a * t ^ p) <=
      Real.exp (K * (1 + R) * Real.log (2 + R)) *
        Real.exp (-(a / 2) * t ^ p) := by
  let c := 1 + 2 / (a * p)
  let K := (1 + Real.log c / Real.log 2) / p
  let q := R / p
  let L := c * (2 + R)
  let y := t ^ p
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hy : 0 < y := Real.rpow_pos_of_pos ht0 p
  have hq : 0 <= q := div_nonneg hR hp.le
  have h2 : (0 : Real) < 2 := by norm_num
  have h2R : 0 < 2 + R := add_pos_of_pos_of_nonneg h2 hR
  have hcTerm : 0 < 2 / (a * p) := div_pos h2 (mul_pos ha hp)
  have hc : 1 < c := lt_add_of_pos_right _ hcTerm
  have hL : 0 < L := mul_pos (zero_lt_one.trans hc) h2R
  have hLcomp : 2 * R / (a * p) <= L := by
    rw [show 2 * R / (a * p) = (2 / (a * p)) * R from by ring]
    unfold L c
    nlinarith only [hR, hcTerm]
  have hqcomp : q <= (a / 2) * L := by
    rw [show q = (a / 2) * (2 * R / (a * p)) from by
      unfold q
      field_simp [ha.ne', hp.ne'] <;> ring]
    exact mul_le_mul_of_nonneg_left hLcomp (half_pos ha).le
  have hqdiv : q / L <= a / 2 := by
    have h := div_le_div_of_nonneg_right hqcomp hL.le
    rwa [show (a / 2) * L / L = a / 2 from by field_simp [hL.ne']] at h
  have hprod : q * (y / L) <= (a / 2) * y := by
    rw [show q * (y / L) = (q / L) * y from by ring]
    exact mul_le_mul_of_nonneg_right hqdiv hy.le
  have hlogLine := Real.log_le_sub_one_of_pos (div_pos hy hL)
  rw [Real.log_div hy.ne' hL.ne'] at hlogLine
  have hlogMul := mul_le_mul_of_nonneg_left hlogLine hq
  have he : q * Real.log y - (a / 2) * y <= q * Real.log L := by
    nlinarith only [hlogMul, hprod, hq]
  have hqy : q * Real.log y = Real.log t * R := by
    change R / p * Real.log (t ^ p) = _
    rw [Real.log_rpow ht0 p]
    field_simp [hp.ne'] <;> ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2R : Real.log 2 <= Real.log (2 + R) := Real.log_le_log h2 (le_add_of_nonneg_right hR)
  have hLc : Real.log c <= (Real.log c / Real.log 2) * Real.log (2 + R) := by
    have h := mul_le_mul_of_nonneg_left hlog2R
      (div_nonneg (Real.log_pos hc).le hlog2.le)
    rwa [show Real.log c / Real.log 2 * Real.log 2 = Real.log c from
      by field_simp [hlog2.ne']] at h
  have hLogL : Real.log L <= (1 + Real.log c / Real.log 2) * Real.log (2 + R) := by
    unfold L
    rw [Real.log_mul (zero_lt_one.trans hc).ne' h2R.ne']
    linarith only [hLc]
  have hK : 0 <= K := div_nonneg
    (add_nonneg zero_le_one (div_nonneg (Real.log_pos hc).le hlog2.le)) hp.le
  have hExponent : q * Real.log L <= K * (1 + R) * Real.log (2 + R) := calc
    _ <= q * ((1 + Real.log c / Real.log 2) * Real.log (2 + R)) :=
      mul_le_mul_of_nonneg_left hLogL hq
    _ = K * R * Real.log (2 + R) := by unfold q K; ring
    _ <= _ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hK)
        (hlog2.le.trans hlog2R)
  change t ^ R * Real.exp (-a * y) <=
    Real.exp (K * (1 + R) * Real.log (2 + R)) * Real.exp (-(a / 2) * y)
  rw [Real.rpow_def_of_pos ht0, <- Real.exp_add, <- Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hqy] at he
  linarith only [he, hExponent]

/-- Uniform logarithmic growth of a Mellin moment on `(1, infinity)`. -/
theorem norm_mellinMoment_le_logarithmicGrowth
    (f : Real -> Complex) {A a p : Real}
    (hA : 0 <= A) (ha : 0 < a) (hp : 0 < p)
    (hDecay : forall t : Real, 1 <= t -> norm (f t) <= A * Real.exp (-a * t ^ p))
    (hInt : forall s : Complex, IntegrableOn
      (fun t : Real => f t * (t : Complex) ^ (s - 1)) (Ioi (1 : Real))) :
    exists C K : Real, And (0 <= C) (And (0 <= K)
      (forall (s : Complex) (R : Real), 0 <= R -> s.re - 1 <= R ->
        norm (integral (volume.restrict (Ioi (1 : Real)))
          (fun t : Real => f t * (t : Complex) ^ (s - 1))) <=
          C * Real.exp (K * (1 + R) * Real.log (2 + R)))) := by
  let c := 1 + 2 / (a * p)
  let K := (1 + Real.log c / Real.log 2) / p
  let g (t : Real) := Real.exp (-(a / 2) * t ^ p)
  let mu := volume.restrict (Ioi (1 : Real))
  let J := integral mu g
  have hg : Integrable g mu := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (b := a / 2)
      (by norm_num) hp (half_pos ha)
    simp only [Real.rpow_zero, one_mul] at h
    apply h.mono_set
    intro t ht
    exact mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp ht))
  have hJ : 0 <= J := integral_nonneg (fun t => (Real.exp_pos _).le)
  have hc : 1 < c := lt_add_of_pos_right _ (div_pos (by norm_num) (mul_pos ha hp))
  have hK : 0 <= K := div_nonneg
    (add_nonneg zero_le_one (div_nonneg (Real.log_pos hc).le (Real.log_nonneg (by norm_num)))) hp.le
  refine Exists.intro (A * J) (Exists.intro K (And.intro (mul_nonneg hA hJ) (And.intro hK ?_)))
  intro s R hR hs
  let F (t : Real) := f t * (t : Complex) ^ (s - 1)
  let E := Real.exp (K * (1 + R) * Real.log (2 + R))
  have hDom : Integrable (fun t => (A * E) * g t) mu := hg.const_mul _
  have hPoint {t : Real} (ht : 1 <= t) : norm (F t) <= (A * E) * g t := by
    have ht0 := zero_lt_one.trans_le ht
    unfold F
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
    calc
      _ <= (A * Real.exp (-a * t ^ p)) * t ^ R :=
        mul_le_mul (hDecay t ht) (Real.rpow_le_rpow_of_exponent_le ht hs)
          (Real.rpow_nonneg ht0.le _) (mul_nonneg hA (Real.exp_pos _).le)
      _ = A * (t ^ R * Real.exp (-a * t ^ p)) := by ring
      _ <= A * (E * g t) := mul_le_mul_of_nonneg_left
        (stretchedExpMoment_envelope ha hp hR ht) hA
      _ = _ := by ring
  calc
    _ <= integral mu (fun t => norm (F t)) := norm_integral_le_integral_norm _
    _ <= integral mu (fun t => (A * E) * g t) := by
      apply integral_mono_ae (hInt s).norm hDom
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hPoint (le_of_lt ht)
    _ = _ := by rw [integral_const_mul]; change (A * E) * J = (A * J) * E; ring

end Robin1984.GRH
