import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Mellin kernel for the triangularly smoothed prime-power sum.
- Formalization note: The integral is evaluated at an arbitrary positive prime-power norm with the full complex convergence condition.
- PROVENANCE-END
-/

/-!
# The triangular Mellin kernel

The weight at a positive norm starts at that norm and gives the denominator
`s * (s + 1)` in the transform used for the automorphic criterion.
-/

open MeasureTheory Set

namespace Robin1984.GRH

/-- The Mellin transform of one triangular weight above its norm. -/
theorem triangularMellin (a : Real) (s : Complex) (ha : 0 < a) (hs : 0 < s.re) :
    MeasureTheory.integral (volume.restrict (Ioi a))
      (fun t : Real => (1 - (a : Complex) / (t : Complex)) * (t : Complex) ^ (-s - 1)) =
        (a : Complex) ^ (-s) / (s * (s + 1)) := by
  have hFirst : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith only [hs]
  have hSecond : (-s - 2).re < -1 := by
    have hTwo : (2 : Complex).re = 2 := calc
      (2 : Complex).re = (1 + 1 : Complex).re := congrArg Complex.re (by ring)
      _ = (1 : Complex).re + (1 : Complex).re := Complex.add_re _ _
      _ = 2 := by simp only [Complex.one_re, one_add_one_eq_two]
    rw [Complex.sub_re, Complex.neg_re, hTwo]
    linarith only [hs]
  have hSplit : Set.EqOn
      (fun t : Real => (1 - (a : Complex) / (t : Complex)) * (t : Complex) ^ (-s - 1))
      (fun t : Real => (t : Complex) ^ (-s - 1) - (a : Complex) * (t : Complex) ^ (-s - 2))
      (Ioi a) := by
    intro t ht
    have htn : Not ((t : Complex) = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt (ha.trans ht))
    have hPower : (t : Complex) ^ (-s - 1) / (t : Complex) = (t : Complex) ^ (-s - 2) := by
      rw [div_eq_mul_inv, <- Complex.cpow_neg_one, <- Complex.cpow_add _ _ htn]
      congr 1
      ring
    calc
      _ = (t : Complex) ^ (-s - 1) -
          (a : Complex) * ((t : Complex) ^ (-s - 1) / (t : Complex)) := by
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by rw [hPower]
  have hFirstInt : Integrable (fun t : Real => (t : Complex) ^ (-s - 1))
      (volume.restrict (Ioi a)) := integrableOn_Ioi_cpow_of_lt hFirst ha
  have hSecondInt : Integrable (fun t : Real => (t : Complex) ^ (-s - 2))
      (volume.restrict (Ioi a)) := integrableOn_Ioi_cpow_of_lt hSecond ha
  rw [setIntegral_congr_fun measurableSet_Ioi hSplit,
    integral_sub hFirstInt (hSecondInt.const_mul (a : Complex)), integral_const_mul,
    integral_Ioi_cpow_of_lt hFirst ha, integral_Ioi_cpow_of_lt hSecond ha]
  have hAn : Not ((a : Complex) = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  have hPower : (a : Complex) * (a : Complex) ^ (-s - 1) = (a : Complex) ^ (-s) := by
    calc
      _ = (a : Complex) ^ (1 : Complex) * (a : Complex) ^ (-s - 1) := by
        rw [Complex.cpow_one]
      _ = (a : Complex) ^ (1 + (-s - 1)) := (Complex.cpow_add _ _ hAn).symm
      _ = _ := by congr 1; ring
  have hSimplifyFirst : -s - 1 + 1 = -s := by ring
  have hSimplifySecond : -s - 2 + 1 = -s - 1 := by ring
  rw [hSimplifyFirst, hSimplifySecond, <- mul_div_assoc, mul_neg, hPower]
  have hS : Not (s = 0) := Complex.ne_zero_of_re_pos hs
  have hSOne : Not (s + 1 = 0) := Complex.ne_zero_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hs])
  have hNeg : Not (-s - 1 = 0) := by
    rw [neg_sub_left, add_comm (1 : Complex) s]
    exact neg_ne_zero.mpr hSOne
  field_simp [hS, hSOne, hNeg]
  <;> ring

end Robin1984.GRH
