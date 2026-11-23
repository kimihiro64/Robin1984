import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The derivative of the Gamma function at one.
- Formalization note: Evaluate and rescale the exponential logarithmic moment by a positive change of variables.
- PROVENANCE-END
-/

/-!
# Euler's constant in the logarithmic Laplace average

The normalizing constant in Mertens' theorem is the negative of the
first derivative of the Gamma function at one.
-/

open Filter MeasureTheory Set Topology

namespace Robin1984.GRH

/-- The logarithmic first moment of the exponential measure. -/
theorem integral_log_mul_exp_neg_eq_neg_eulerMascheroni :
    integral (volume.restrict (Ioi (0 : Real))) (fun t => Real.log t * Real.exp (-t)) =
      -Real.eulerMascheroniConstant := by
  have hOne : 0 < (1 : Complex).re := by rw [Complex.one_re]; exact zero_lt_one
  have hNear : Filter.Eventually (fun s : Complex => 0 < s.re) (nhds 1) :=
    (Complex.continuous_re.continuousAt.tendsto).eventually (Ioi_mem_nhds hOne)
  have hEq : Filter.EventuallyEq (nhds (1 : Complex)) Complex.Gamma Complex.GammaIntegral :=
    hNear.mono (fun _ hs => Complex.Gamma_eq_integral hs)
  have hD := (Complex.hasDerivAt_GammaIntegral hOne).congr_of_eventuallyEq hEq
  have h := hD.deriv.symm.trans Complex.hasDerivAt_Gamma_one.deriv
  have hCast : integral (volume.restrict (Ioi (0 : Real)))
      (fun t => ((Real.log t * Real.exp (-t) : Real) : Complex)) =
        -(Real.eulerMascheroniConstant : Complex) := by
    simpa only [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul] using h
  rw [integral_complex_ofReal, <- Complex.ofReal_neg] at hCast
  exact Complex.ofReal_injective hCast

theorem integrableOn_log_mul_exp_neg :
    IntegrableOn (fun t => Real.log t * Real.exp (-t)) (Ioi (0 : Real)) := by
  by_contra hNot
  have hZero := integral_undef hNot
  rw [integral_log_mul_exp_neg_eq_neg_eulerMascheroni] at hZero
  have hPos : 0 < Real.eulerMascheroniConstant :=
    (show (0 : Real) < 1 / 2 by norm_num).trans Real.one_half_lt_eulerMascheroniConstant
  exact (neg_ne_zero.mpr hPos.ne') hZero

/-- The scaled exponential average of the logarithm has the exact
constant and logarithmic dependence on the positive scale. -/
theorem mul_integral_log_mul_exp_neg_scale {u : Real} (hu : 0 < u) :
    u * integral (volume.restrict (Ioi (0 : Real)))
        (fun t => Real.log t * Real.exp (-(u * t))) =
      -Real.eulerMascheroniConstant - Real.log u := by
  let F := fun v : Real => (Real.log v - Real.log u) * Real.exp (-v)
  have hImage : (fun t : Real => u * t) '' Ioi (0 : Real) = Ioi 0 := by
    ext y
    constructor
    case mp =>
      intro h
      obtain t := Classical.choose h
      have ht := Classical.choose_spec h
      change 0 < y
      rw [<- ht.2]
      exact mul_pos hu ht.1
    case mpr =>
      intro hy
      exact Exists.intro (y / u) (And.intro (div_pos hy hu) (by
        change u * (y / u) = y
        field_simp [hu.ne']))
  have hDerivative (t : Real) : HasDerivAt (fun v : Real => u * v) u t := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id t).const_mul u
  have hInj : InjOn (fun t : Real => u * t) (Ioi (0 : Real)) :=
    (show StrictMono (fun t : Real => u * t) from
      fun _ _ h => mul_lt_mul_of_pos_left h hu).injective.injOn
  have hJac := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (hDerivative t).hasDerivWithinAt) hInj F
  rw [hImage] at hJac
  change integral (volume.restrict (Ioi (0 : Real))) F =
    integral (volume.restrict (Ioi (0 : Real))) (fun t => abs u * F (u * t)) at hJac
  rw [abs_of_pos hu, integral_const_mul] at hJac
  have hChart : integral (volume.restrict (Ioi (0 : Real)))
        (fun t => Real.log t * Real.exp (-(u * t))) =
      integral (volume.restrict (Ioi (0 : Real))) (fun t => F (u * t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change Real.log t * Real.exp (-(u * t)) =
      (Real.log (u * t) - Real.log u) * Real.exp (-(u * t))
    rw [Real.log_mul hu.ne' (show 0 < t from ht).ne']
    ring
  have hExpInt : IntegrableOn (fun t => Real.exp (-t)) (Ioi (0 : Real)) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0
  have hExpMass : integral (volume.restrict (Ioi (0 : Real))) (fun t => Real.exp (-t)) = 1 := by
    simpa using integral_exp_mul_Ioi (a := -1) (by norm_num) (0 : Real)
  have hF : F = fun t => Real.log t * Real.exp (-t) - Real.log u * Real.exp (-t) := by
    funext t
    exact sub_mul _ _ _
  rw [hChart, <- hJac, hF, integral_sub integrableOn_log_mul_exp_neg (hExpInt.const_mul _),
    integral_const_mul, integral_log_mul_exp_neg_eq_neg_eulerMascheroni, hExpMass, mul_one]

end Robin1984.GRH
