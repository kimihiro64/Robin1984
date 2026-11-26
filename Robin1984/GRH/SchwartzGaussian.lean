import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Schwartz decay of an exponential with temperate exponent and a negative quadratic upper bound.
- Formalization note: Shared proof for the archimedean Tate and Godement-Jacquet Gaussian tests.
- PROVENANCE-END
-/

/-!
# Schwartz functions from a negative quadratic bound

A smooth temperate exponent bounded above by a negative quadratic has a
Schwartz exponential. The Tate and spherical Godement-Jacquet tests use
this construction.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

section QuadraticExponent

open Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

private theorem temperateGrowth_fderiv {f : E -> F} (h : f.HasTemperateGrowth) :
    (fderiv Real f).HasTemperateGrowth := by
  refine And.intro (h.1.fderiv_right (by simp)) ?_
  intro n
  choose k C hC using h.2 (n + 1)
  exact Exists.intro k (Exists.intro C (fun x => by
    rw [norm_iteratedFDeriv_fderiv]
    exact hC x))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
private theorem iteratedFDeriv_exp_factor {q : E -> Real}
    (hq : q.HasTemperateGrowth) (n : Nat) :
    exists g : E -> ContinuousMultilinearMap Real (fun _ : Fin n => E) Real,
      And g.HasTemperateGrowth
        (forall x, iteratedFDeriv Real n (fun y => Real.exp (q y)) x = HSMul.hSMul (Real.exp (q x)) (g x)) := by
  let f (x : E) := Real.exp (q x)
  have hF (x : E) : HasFDerivAt f (HSMul.hSMul (f x) (fderiv Real q x)) x := by
    have hqd : DifferentiableAt Real q x := hq.1.differentiable (by simp) x
    exact hqd.hasFDerivAt.exp
  induction n with
  | zero =>
    let L := (continuousMultilinearCurryFin0 Real E Real).symm
    refine Exists.intro (fun _ => L 1) (And.intro (HasTemperateGrowth.const _) ?_)
    intro x
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    change L (f x) = HSMul.hSMul (f x) (L 1)
    have h := map_smul L (f x) (1 : Real)
    simpa only [smul_eq_mul, mul_one] using h
  | succ n hPrev =>
    choose g hg using hPrev
    let L := (continuousMultilinearCurryLeftEquiv Real (fun _ : Fin (n + 1) => E) Real).symm
    let B := ContinuousLinearMap.smulRightL Real E
      (ContinuousMultilinearMap Real (fun _ : Fin n => E) Real)
    let A (x : E) := fderiv Real g x + B (fderiv Real q x) (g x)
    have hD : (fderiv Real q).HasTemperateGrowth := temperateGrowth_fderiv hq
    have hB := @ContinuousLinearMap.bilinear_hasTemperateGrowth Real E
      (ContinuousLinearMap (RingHom.id Real) E Real)
      (ContinuousMultilinearMap Real (fun _ : Fin n => E) Real)
      (ContinuousLinearMap (RingHom.id Real) E (ContinuousMultilinearMap Real (fun _ : Fin n => E) Real))
      _ _ _ _ _ _ _ _ _ _ _ _ _ B (fderiv Real q) g hD hg.1
    have hA : A.HasTemperateGrowth := (temperateGrowth_fderiv hg.1).add hB
    have hLC := @ContinuousLinearMap.hasTemperateGrowth
      (ContinuousLinearMap (RingHom.id Real) E (ContinuousMultilinearMap Real (fun _ : Fin n => E) Real))
      (ContinuousMultilinearMap Real (fun _ : Fin (n + 1) => E) Real)
      _ _ _ _ L.toContinuousLinearEquiv.toContinuousLinearMap
    have hLA := hLC.comp hA
    refine Exists.intro (fun x => L (A x)) (And.intro hLA ?_)
    intro x
    have hgEq : iteratedFDeriv Real n f = fun y => HSMul.hSMul (f y) (g y) := funext hg.2
    have hgd : DifferentiableAt Real g x := hg.1.1.differentiable (by simp) x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    change L (fderiv Real (iteratedFDeriv Real n f) x) = HSMul.hSMul (f x) (L (A x))
    have hL : L (HSMul.hSMul (f x) (A x)) = HSMul.hSMul (f x) (L (A x)) :=
      map_smul L (f x) (A x)
    rw [hgEq, fderiv_fun_smul (hF x).differentiableAt hgd, (hF x).fderiv, <- hL]
    congr 1
    ext y
    simp only [A, B, _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRightL_apply_apply,
      smul_add, smul_smul, smul_eq_mul]

private theorem pow_mul_exp_neg_quadratic_le (a : Real) (ha : 0 < a)
    (r : Real) (hr : 0 <= r) (n : Nat) :
    (1 + r) ^ n * Real.exp (-a * r ^ 2) <=
      Real.exp a * (2 / a) ^ n * (n.factorial : Real) := by
  let t := a * (1 + r ^ 2)
  have ht : 0 <= t := mul_nonneg ha.le (by positivity)
  have hBase : 1 + r <= (2 / a) * t := by
    have he : (2 / a) * t = 2 * (1 + r ^ 2) := by
      dsimp only [t]
      field_simp [ha.ne']
    rw [he]
    nlinarith [sq_nonneg (r - 1)]
  have hn : 0 < (n.factorial : Real) := by exact_mod_cast Nat.factorial_pos n
  have hExp : t ^ n <= Real.exp t * (n.factorial : Real) := by
    have h := mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp t ht n) hn.le
    have hEq : t ^ n / (n.factorial : Real) * (n.factorial : Real) = t ^ n := by
      field_simp [hn.ne']
    rwa [hEq] at h
  have hT : t ^ n * Real.exp (-t) <= (n.factorial : Real) := by
    calc
      _ <= (Real.exp t * (n.factorial : Real)) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right hExp (Real.exp_nonneg _)
      _ = _ := by
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
  calc
    _ <= ((2 / a) * t) ^ n * Real.exp (-a * r ^ 2) := by
      gcongr
    _ = (Real.exp a * (2 / a) ^ n) * (t ^ n * Real.exp (-t)) := by
      rw [show -a * r ^ 2 = a + -t by dsimp [t]; ring, Real.exp_add, mul_pow]
      ring
    _ <= _ := mul_le_mul_of_nonneg_left hT (by positivity)

/-- A smooth temperate exponent bounded above by a negative quadratic gives
a Schwartz function after exponentiation. -/
def schwartzExp_of_negativeQuadratic {q : E -> Real}
    (hq : q.HasTemperateGrowth) {a : Real} (ha : 0 < a)
    (hNeg : forall x, q x <= -a * norm x ^ 2) :
    SchwartzMap E Real where
  toFun x := Real.exp (q x)
  smooth' := Real.contDiff_exp.comp hq.1
  decay' k n := by
    choose g hg using iteratedFDeriv_exp_factor hq n
    choose d C hC using hg.1.2 0
    have hNorm (x : E) : norm (g x) <= (max C 0) * (1 + norm x) ^ d := by
      have h := hC x
      rw [norm_iteratedFDeriv_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    refine Exists.intro
      ((max C 0) * (Real.exp a * (2 / a) ^ (k + d) * ((k + d).factorial : Real))) ?_
    intro x
    have hS : norm (HSMul.hSMul (Real.exp (q x)) (g x)) = Real.exp (q x) * norm (g x) := by
      have h := norm_smul (Real.exp (q x)) (g x)
      simpa only [Real.norm_of_nonneg (Real.exp_nonneg _)] using h
    rw [hg.2 x, hS]
    calc
      _ <= (1 + norm x) ^ k * (Real.exp (-a * norm x ^ 2) * ((max C 0) * (1 + norm x) ^ d)) := by
        gcongr
        . exact le_add_of_nonneg_left (by norm_num)
        . exact hNeg x
        . exact hNorm x
      _ = (max C 0) * ((1 + norm x) ^ (k + d) * Real.exp (-a * norm x ^ 2)) := by
        rw [pow_add]
        ring
      _ <= _ := mul_le_mul_of_nonneg_left (pow_mul_exp_neg_quadratic_le a ha _ (norm_nonneg _) _)
        (le_max_right _ _)



end QuadraticExponent

end Robin1984.GRH
