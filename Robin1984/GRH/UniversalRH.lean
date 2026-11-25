import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The condition that the full zero set of a complex function is contained in a vertical line.
- Formalization note: Defines the line condition for all functions from Complex to Complex and proves the uniqueness of a critical line as the midpoint of the zero strip.
- PROVENANCE-END
-/

/-!
# The Universal Riemann Hypothesis

These predicates describe the full zero set of any complex function. An
entire or completed function can be supplied whenever a particular
application requires it.
-/

set_option autoImplicit false

namespace Robin1984.GRH

/-- The complex function has infinitely many distinct zero locations. -/
def HasInfiniteZeros (F : Complex -> Complex) : Prop :=
  Set.Infinite {z : Complex | F z = 0}

/-- All zeros of the complex function lie on the specified vertical line. -/
def ZerosOnLine (F : Complex -> Complex) (c : Real) : Prop :=
  forall z : Complex, F z = 0 -> z.re = c

/-- The Universal Riemann Hypothesis at `c` says that the function has
infinitely many distinct zeros and every zero has real part `c`. -/
def UniversalRiemannHypothesisAt (F : Complex -> Complex) (c : Real) : Prop :=
  HasInfiniteZeros F /\ ZerosOnLine F c

/-- A complex function satisfies the Universal Riemann Hypothesis if
its infinite zero set lies on a vertical line. -/
def UniversalRiemannHypothesis (F : Complex -> Complex) : Prop :=
  exists c : Real, UniversalRiemannHypothesisAt F c

/-- The Universal Riemann Hypothesis is equivalent to infinitely many
zeros with equal real parts for every pair. -/
theorem universalRiemannHypothesis_iff_zero_realParts_eq (F : Complex -> Complex) :
    UniversalRiemannHypothesis F <->
      HasInfiniteZeros F /\
        (forall z w : Complex, F z = 0 -> F w = 0 -> z.re = w.re) := by
  constructor
  next =>
    intro h
    choose c hc using h
    exact And.intro hc.1 (fun z w hz hw => (hc.2 z hz).trans (hc.2 w hw).symm)
  next =>
    intro h
    choose z hz using Set.Infinite.nonempty h.1
    exact Exists.intro z.re (And.intro h.1 (fun y hy => h.2 y z hy hz))

/-- The vertical line of a function satisfying URH is unique. -/
theorem universalRiemannHypothesisAt_line_unique
    {F : Complex -> Complex} {c d : Real}
    (hc : UniversalRiemannHypothesisAt F c) (hd : UniversalRiemannHypothesisAt F d) :
    c = d := by
  choose z hz using Set.Infinite.nonempty hc.1
  exact (hc.2 z hz).symm.trans (hd.2 z hz)

/-- A function with finitely many distinct zero locations cannot satisfy URH. -/
theorem not_universalRiemannHypothesis_of_finiteZeros
    {F : Complex -> Complex} (h : Set.Finite {z : Complex | F z = 0}) :
    Not (UniversalRiemannHypothesis F) := by
  intro hURH
  choose c hc using hURH
  exact hc.1 h

/-- Real parts of all zeros of a complex function. -/
def complexZeroRealParts (F : Complex -> Complex) : Set Real :=
  {r : Real | exists z : Complex, F z = 0 /\ z.re = r}

/-- A critical line is a vertical reflection axis for an infinite zero set
whose real parts are bounded. This predicate uses zero
locations, so it is defined even for a function without analyticity. -/
def HasCriticalLineAt (F : Complex -> Complex) (c : Real) : Prop :=
  HasInfiniteZeros F /\
    (exists w : Real, 0 <= w /\
      forall z : Complex, F z = 0 -> abs (z.re - c) <= w) /\
    (forall z : Complex, F z = 0 -> F (Complex.mk (2 * c - z.re) z.im) = 0)

/-- A critical line is the midpoint of the smallest closed vertical strip
containing the zeros. -/
theorem HasCriticalLineAt.eq_midpoint {F : Complex -> Complex} {c : Real}
    (h : HasCriticalLineAt F c) :
    c = (sInf (complexZeroRealParts F) + sSup (complexZeroRealParts F)) / 2 := by
  let S := complexZeroRealParts F
  choose z0 hz using Set.Infinite.nonempty h.1
  choose w hw using h.2.1
  have hN : S.Nonempty :=
    Exists.intro z0.re (Exists.intro z0 (And.intro hz rfl))
  have hA : BddAbove S := by
    refine Exists.intro (c + w) ?_
    intro r hr
    change (exists z : Complex, F z = 0 /\ z.re = r) at hr
    choose z hz using hr
    linarith [(abs_le.mp (hw.2 z hz.1)).2, hz.2]
  have hB : BddBelow S := by
    refine Exists.intro (c - w) ?_
    intro r hr
    change (exists z : Complex, F z = 0 /\ z.re = r) at hr
    choose z hz using hr
    linarith [(abs_le.mp (hw.2 z hz.1)).1, hz.2]
  have hReflect (r : Real) (hr : Membership.mem S r) :
      Membership.mem S (2 * c - r) := by
    change (exists z : Complex, F z = 0 /\ z.re = r) at hr
    choose z hz using hr
    refine Exists.intro (Complex.mk (2 * c - z.re) z.im) (And.intro (h.2.2 z hz.1) ?_)
    change 2 * c - z.re = 2 * c - r
    rw [hz.2]
  have hRight : sSup S <= 2 * c - sInf S := by
    apply csSup_le hN
    intro r hr
    linarith [csInf_le hB (hReflect r hr)]
  have hLeft : 2 * c - sSup S <= sInf S := by
    apply le_csInf hN
    intro r hr
    linarith [le_csSup hA (hReflect r hr)]
  change c = (sInf S + sSup S) / 2
  linarith

/-- An infinite zero set with bounded real parts has at most one critical line. -/
theorem HasCriticalLineAt.unique {F : Complex -> Complex} {c d : Real}
    (hc : HasCriticalLineAt F c) (hd : HasCriticalLineAt F d) :
    c = d :=
  hc.eq_midpoint.trans hd.eq_midpoint.symm

/-- The line containing all zeros of a URH function is a critical line. -/
theorem UniversalRiemannHypothesisAt.hasCriticalLineAt
    {F : Complex -> Complex} {c : Real}
    (h : UniversalRiemannHypothesisAt F c) : HasCriticalLineAt F c := by
  refine And.intro h.1 (And.intro ?_ ?_)
  next =>
    refine Exists.intro 0 (And.intro le_rfl ?_)
    intro z hz
    rw [h.2 z hz, sub_self, abs_zero]
  next =>
    intro z hz
    have hFix : Complex.mk (2 * c - z.re) z.im = z := by
      apply Complex.ext
      next =>
        change 2 * c - z.re = z.re
        linarith [h.2 z hz]
      next =>
        rfl
    rw [hFix]
    exact hz

/-- The two shifted Mellin poles lie to the right of the proposed strip. -/
noncomputable def triangularZeroWeight (c w : Real) (z : Complex) : Complex :=
  Inv.inv ((z - ((c + w + 1 : Real) : Complex)) * (z - ((c + w + 2 : Real) : Complex)))

/-- The finite triangular zero bound uses every finite set of zero locations
and both directions of logarithmic scale. It requires no regularity of the
function whose zeros are tested. -/
def FiniteTriangularZeroBound (F : Complex -> Complex) (c w : Real) : Prop :=
  Not (F ((c + w + 1 : Real) : Complex) = 0) /\
    Not (F ((c + w + 2 : Real) : Complex) = 0) /\
    (forall E : Finset Complex, (forall z, Membership.mem E z -> F z = 0) ->
      forall t : Real,
        norm (E.sum (fun z => triangularZeroWeight c w z *
          Complex.exp ((t : Complex) * (z - (c : Complex))))) <=
            Real.exp (w * abs t) * E.sum (fun z => norm (triangularZeroWeight c w z)))

private theorem norm_centeredExp (t c : Real) (z : Complex) :
    norm (Complex.exp ((t : Complex) * (z - (c : Complex)))) =
      Real.exp (t * (z.re - c)) := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.sub_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- The finite triangular zero bound characterizes containment in the
closed vertical strip of center `c` and half-width `w`. -/
theorem finiteTriangularZeroBound_iff (F : Complex -> Complex) (c w : Real) :
    FiniteTriangularZeroBound F c w <->
      forall z : Complex, F z = 0 -> abs (z.re - c) <= w := by
  classical
  symm
  constructor
  next =>
    intro h
    have hAnchor (d : Real) (hd : 0 < d) :
        Not (F ((c + w + d : Real) : Complex) = 0) := by
      intro hz
      have he := (abs_le.mp (h _ hz)).2
      rw [Complex.ofReal_re] at he
      linarith
    refine And.intro (hAnchor 1 zero_lt_one) (And.intro (hAnchor 2 zero_lt_two) ?_)
    intro E hE t
    calc
      _ <= E.sum (fun z => norm (triangularZeroWeight c w z *
          Complex.exp ((t : Complex) * (z - (c : Complex))))) :=
        norm_sum_le E _
      _ <= E.sum (fun z => Real.exp (w * abs t) * norm (triangularZeroWeight c w z)) := by
        apply Finset.sum_le_sum
        intro z hz
        have ht : t * (z.re - c) <= w * abs t := by
          calc
            _ <= abs (t * (z.re - c)) := le_abs_self _
            _ = abs t * abs (z.re - c) := abs_mul _ _
            _ <= abs t * w := mul_le_mul_of_nonneg_left (h z (hE z hz)) (abs_nonneg t)
            _ = w * abs t := mul_comm _ _
        rw [Complex.norm_mul, norm_centeredExp, mul_comm (norm (triangularZeroWeight c w z))]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht) (norm_nonneg _)
      _ = _ := (Finset.mul_sum E _ _).symm
  next =>
    intro h z hz
    have hA : Not (z - ((c + w + 1 : Real) : Complex) = 0) := by
      intro he
      apply h.1
      rw [<- sub_eq_zero.mp he]
      exact hz
    have hB : Not (z - ((c + w + 2 : Real) : Complex) = 0) := by
      intro he
      apply h.2.1
      rw [<- sub_eq_zero.mp he]
      exact hz
    have hPos : 0 < norm (triangularZeroWeight c w z) :=
      norm_pos_iff.mpr (inv_ne_zero (mul_ne_zero hA hB))
    have hRe (t : Real) : t * (z.re - c) <= w * abs t := by
      have he := h.2.2 ({z} : Finset Complex) (by
        intro y hy
        rw [Finset.mem_singleton.mp hy]
        exact hz) t
      simp only [Finset.sum_singleton, Complex.norm_mul, norm_centeredExp] at he
      rw [mul_comm (Real.exp (w * abs t))] at he
      exact Real.exp_le_exp.mp (le_of_mul_le_mul_left he hPos)
    have hPosScale := hRe 1
    have hNegScale := hRe (-1)
    rw [abs_of_nonneg zero_le_one] at hPosScale
    rw [abs_neg, abs_of_nonneg zero_le_one] at hNegScale
    exact abs_le.mpr (And.intro (by linarith) (by linarith))

/-- The Universal Riemann Hypothesis is the width-zero triangular bound
together with the existence of infinitely many distinct zero locations. -/
theorem universalRiemannHypothesisAt_iff_finiteTriangularZeroBound
    (F : Complex -> Complex) (c : Real) :
    UniversalRiemannHypothesisAt F c <->
      HasInfiniteZeros F /\ FiniteTriangularZeroBound F c 0 := by
  rw [finiteTriangularZeroBound_iff F c 0]
  constructor
  next =>
    intro h
    refine And.intro h.1 ?_
    intro z hz
    rw [h.2 z hz, sub_self, abs_zero]
  next =>
    intro h
    refine And.intro h.1 ?_
    intro z hz
    have hc := abs_le.mp (h.2 z hz)
    linarith [hc.1, hc.2]

end Robin1984.GRH
