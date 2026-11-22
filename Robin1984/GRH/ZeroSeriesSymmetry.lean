import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Robin1984.GRH.TriangularZeroTerms

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Pairing conjugate zeros in the canonical explicit formula.
- Formalization note: Reality is proved by reindexing the entire multiplicity-aware zero sum, while the Mellin uniqueness argument uses its measurable real part.
- PROVENANCE-END
-/

/-!
# Reality of the canonical zero expansion

Conjugation of each zero and a bijection of the zero indices give a real
sum on the positive tail. The summands are globally measurable.
-/

open MeasureTheory Set

namespace Robin1984.GRH

private theorem measurable_realBase_cpow (s : Complex) :
    Measurable (fun x : Real => (x : Complex) ^ s) := by
  classical
  have hBreak : (fun x : Real => (x : Complex) ^ s) =
      fun x : Real => if x = 0 then (0 : Complex) ^ s
        else Complex.exp (Complex.log (x : Complex) * s) := by
    funext x
    by_cases hx : x = 0
    case pos => simp only [hx, Complex.ofReal_zero, if_pos]
    case neg => rw [if_neg hx, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx)]
  rw [hBreak]
  exact Measurable.ite (measurableSet_singleton (0 : Real)) measurable_const
    (Complex.continuous_exp.measurable.comp
      ((Complex.measurable_log.comp Complex.continuous_ofReal.measurable).mul measurable_const))

/-- The real part of the triangular zero sum is measurable. -/
theorem measurable_re_triangularZeroSum {iota : Type*} [Countable iota] (rho : iota -> Complex) :
    Measurable (fun x : Real => (tsum (fun i => triangularZeroTerm (rho i) x)).re) :=
  Complex.continuous_re.measurable.comp (Measurable.tsum (fun i =>
    ((measurable_realBase_cpow (rho i)).sub (measurable_realBase_cpow (-1))).div measurable_const))

private theorem conj_triangularZeroTerm (rho : Complex) {x : Real} (hx : 0 < x) :
    (starRingEnd Complex) (triangularZeroTerm rho x) =
      triangularZeroTerm ((starRingEnd Complex) rho) x := by
  have hArg : Not ((x : Complex).arg = Real.pi) := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  have hPower (s : Complex) :
      (starRingEnd Complex) ((x : Complex) ^ s) =
        (x : Complex) ^ ((starRingEnd Complex) s) := by
    simpa only [Complex.conj_ofReal] using (Complex.cpow_conj (x : Complex) s hArg).symm
  simp only [triangularZeroTerm, div_eq_mul_inv, map_mul, Complex.conj_inv, map_sub,
    map_add, map_one, hPower, map_neg]

/-- A conjugation bijection of the zero indices makes the sum real for
every positive real argument. -/
theorem im_triangularZeroSum_eq_zero {iota : Type*} (rho : iota -> Complex) (e : Equiv iota iota)
    (hConj : forall i, rho (e i) = (starRingEnd Complex) (rho i)) {x : Real} (hx : 0 < x) :
    (tsum (fun i => triangularZeroTerm (rho i) x)).im = 0 := by
  have hSymmetry : (starRingEnd Complex) (tsum (fun i => triangularZeroTerm (rho i) x)) =
      tsum (fun i => triangularZeroTerm (rho i) x) := by
    calc
      _ = tsum (fun i => (starRingEnd Complex) (triangularZeroTerm (rho i) x)) :=
        Complex.conjCLE.map_tsum
      _ = tsum (fun i => triangularZeroTerm (rho (e i)) x) := by
        apply tsum_congr
        intro i
        rw [conj_triangularZeroTerm (rho i) hx, <- hConj i]
      _ = _ := e.tsum_eq (fun i => triangularZeroTerm (rho i) x)
  have him := congrArg Complex.im hSymmetry
  simp only [Complex.conj_im] at him
  linarith only [him]

end Robin1984.GRH
