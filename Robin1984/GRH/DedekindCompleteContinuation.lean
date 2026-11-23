import Robin1984.GRH.DedekindClassFunctionalEquation
import Robin1984.GRH.DedekindContinuation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The classical completed and pole-removed Dedekind zeta functions.
- Formalization note: The functional equation for the actual Dedekind zeta continuation.
- PROVENANCE-END
-/

/-!
# The functional equation for the actual Dedekind zeta continuation

The independently continued zeta function agrees, after completion, with
the ideal-class Mellin construction. In the open critical strip the
archimedean factors are nonzero, so reflection preserves its zeros.
-/

open Filter NumberField Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

local notation "R" => RingOfIntegers K

private theorem idealClassRep_ne_zero' (c : ClassGroup R) : Not (idealClassRep K c = 0) := by
  let I : (nonZeroDivisors (Ideal R)) := Function.surjInv ClassGroup.mk0_surjective c
  exact mem_nonZeroDivisors_iff_ne_zero.mp I.property

/-- The entire completed zeta function with the factors `s(s-1)`
clearing the two possible poles. -/
noncomputable def completedDedekindPoleCleared (s : Complex) : Complex :=
  Finset.sum Finset.univ (fun c : ClassGroup R => completedIdealPoleCleared K (idealClassRep K c) s)

theorem analyticAt_completedDedekindPoleCleared (s : Complex) :
    AnalyticAt Complex (completedDedekindPoleCleared K) s := by
  apply Finset.analyticAt_fun_sum
  intro c _
  exact analyticAt_completedIdealPoleCleared K _ (idealClassRep_ne_zero' K c) s

theorem completedDedekindPoleCleared_eq {s : Complex}
    (hs0 : Not (s = 0)) (hs1 : Not (s = 1)) :
    completedDedekindPoleCleared K s = s * (s - 1) * completedDedekindContinuation K s := by
  unfold completedDedekindPoleCleared completedDedekindContinuation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact completedIdealPoleCleared_eq K (idealClassRep K c) hs0 hs1

/-- The completed entire function factors on the positive half-plane,
including at the removed pole. -/
theorem completedDedekindPoleCleared_eq_archimedean {s : Complex} (hs : 0 < s.re) :
    completedDedekindPoleCleared K s = s * ZInfty K s * entirePoleFreeDedekindZeta K s := by
  let H : Set Complex := {w | 0 < w.re}
  let G : Complex -> Complex := fun w => w * ZInfty K w * entirePoleFreeDedekindZeta K w
  have hL : AnalyticOnNhd Complex (completedDedekindPoleCleared K) H :=
    fun w _ => analyticAt_completedDedekindPoleCleared K w
  have hG : AnalyticOnNhd Complex G H := by
    intro w hw
    exact (analyticAt_id.mul (analyticAt_ZInfty_of_re_pos K (show 0 < w.re from hw))).mul
      (analyticAt_entirePoleFreeDedekindZeta K w)
  have hConn : IsPreconnected H :=
    (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear (0 : Real)).isPreconnected
  have hLarge : IsOpen {w : Complex | 1 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hTwo : Membership.mem {w : Complex | 1 < w.re} (2 : Complex) := by
    change 1 < (2 : Complex).re
    norm_num
  have hNear : Filter.EventuallyEq (nhds (2 : Complex)) (completedDedekindPoleCleared K) G := by
    filter_upwards [hLarge.mem_nhds hTwo] with w hw
    change 1 < w.re at hw
    have hw0 : Not (w = 0) := by
      intro h
      rw [h, Complex.zero_re] at hw
      exact (not_lt_of_ge zero_le_one) hw
    have hw1 : Not (w = 1) := by
      intro h
      rw [h, Complex.one_re] at hw
      exact (lt_irrefl (1 : Real)) hw
    dsimp [G]
    rw [completedDedekindPoleCleared_eq K hw0 hw1,
      completedDedekindContinuation_eq_initial K hw,
      entirePoleFreeDedekindZeta_eq_poleFree K (zero_lt_one.trans hw), poleFreeDedekindZeta_eq K hw]
    ring
  have hTwoH : Membership.mem H (2 : Complex) := by
    change 0 < (2 : Complex).re
    exact zero_lt_one.trans (show 1 < (2 : Complex).re from hTwo)
  have hA := hL.eqOn_of_preconnected_of_eventuallyEq hG hConn hTwoH hNear
  exact hA (show Membership.mem H s from hs)

/-- Completion is the gamma factor times the actual meromorphic zeta
continuation at every point of positive real part away from the pole. -/
theorem completedDedekindContinuation_eq_archimedean_mul {s : Complex}
    (hs : 0 < s.re) (hs1 : Not (s = 1)) :
    completedDedekindContinuation K s = ZInfty K s * dedekindZetaContinuation K s := by
  have hs0 : Not (s = 0) := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact (lt_irrefl (0 : Real)) hs
  have hFactor : Not (s - 1 = 0) := sub_ne_zero.mpr hs1
  have hZ : (s - 1) * dedekindZetaContinuation K s = entirePoleFreeDedekindZeta K s := by
    unfold dedekindZetaContinuation
    field_simp
  have hEq := completedDedekindPoleCleared_eq_archimedean K hs
  rw [completedDedekindPoleCleared_eq K hs0 hs1, <- hZ] at hEq
  have hRight : s * ZInfty K s * ((s - 1) * dedekindZetaContinuation K s) =
      s * (s - 1) * (ZInfty K s * dedekindZetaContinuation K s) := by ring
  rw [hRight] at hEq
  have hDiff : s * (s - 1) * (completedDedekindContinuation K s -
      ZInfty K s * dedekindZetaContinuation K s) = 0 := by
    rw [mul_sub, hEq, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hDiff).resolve_left (mul_ne_zero hs0 hFactor))

/-- The zeros of the actual Dedekind zeta continuation in the open
critical strip are invariant under `s -> 1 - s`. -/
theorem dedekindZetaContinuation_zero_iff_reflect {s : Complex}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Iff (dedekindZetaContinuation K s = 0) (dedekindZetaContinuation K (1 - s) = 0) := by
  have hsN0 : Not (s = 0) := by
    intro h
    rw [h, Complex.zero_re] at hs0
    exact (lt_irrefl (0 : Real)) hs0
  have hsN1 : Not (s = 1) := by
    intro h
    rw [h, Complex.one_re] at hs1
    exact (lt_irrefl (1 : Real)) hs1
  have ht0 : 0 < ((1 : Complex) - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    exact sub_pos.mpr hs1
  have htN1 : Not ((1 : Complex) - s = 1) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hRe
    linarith only [hRe, hs0]
  have heq := completedDedekindContinuation_functionalEquation K hsN0 hsN1
  rw [completedDedekindContinuation_eq_archimedean_mul K hs0 hsN1,
    completedDedekindContinuation_eq_archimedean_mul K ht0 htN1] at heq
  constructor
  case mp =>
    intro hz
    rw [hz, mul_zero] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left (ZInfty_ne_zero_of_re_pos K ht0)
  case mpr =>
    intro hz
    rw [hz, mul_zero] at heq
    exact (mul_eq_zero.mp heq).resolve_left (ZInfty_ne_zero_of_re_pos K hs0)

end DedekindZeta
