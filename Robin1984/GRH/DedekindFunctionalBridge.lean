import Robin1984.GRH
import Robin1984.GRH.DedekindCompleteContinuation

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The Dedekind functional equation and the project definition of the critical-line condition.
- Formalization note: The actual Dedekind continuation in the Robin1984 predicate.
- PROVENANCE-END
-/

/-!
# The actual Dedekind continuation in the Robin1984 predicate

The unconditional reflection theorem reduces the Dedekind RH predicate
to absence of zeros in the right half of its open critical strip.
-/

open NumberField Robin1984.GRH

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

theorem isDedekindZetaContinuation_actual :
    IsDedekindZetaContinuation K (dedekindZetaContinuation K) := by
  refine And.intro ?_ (fun _ hs => dedekindZetaContinuation_eq_series K hs)
  intro s hs
  exact (analyticAt_dedekindZetaContinuation K hs).differentiableAt.differentiableWithinAt

/-- Right-half-strip nonvanishing is sufficient and necessary for
Dedekind RH in the repository's continuation-independent predicate. -/
theorem dedekindRH_iff_noZero_rightHalfStrip :
    Iff (DedekindRH K)
      (forall s : Complex, 1 / 2 < s.re -> s.re < 1 -> Not (dedekindZetaContinuation K s = 0)) := by
  rw [dedekindRH_iff_zeros_of_continuation (isDedekindZetaContinuation_actual K)]
  constructor
  case mp =>
    intro h s hsL hsR hz
    have hs0 : 0 < s.re := by linarith only [hsL]
    have hEq := h s hs0 hsR hz
    exact (ne_of_gt hsL) hEq
  case mpr =>
    intro h s hs0 hs1 hz
    rcases lt_trichotomy s.re (1 / 2) with hsL | hEq | hsR
    case inl =>
      have htL : 1 / 2 < ((1 : Complex) - s).re := by
        rw [Complex.sub_re, Complex.one_re]
        linarith only [hsL]
      have htR : ((1 : Complex) - s).re < 1 := by
        rw [Complex.sub_re, Complex.one_re]
        linarith only [hs0]
      have hZ := (dedekindZetaContinuation_zero_iff_reflect K hs0 hs1).mp hz
      exact False.elim (h (1 - s) htL htR hZ)
    case inr.inl => exact hEq
    case inr.inr => exact False.elim (h s hsR hs1 hz)

theorem entirePoleFreeDedekindZeta_ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) :
    Not (entirePoleFreeDedekindZeta K s = 0) := by
  rw [entirePoleFreeDedekindZeta_eq_poleFree K (zero_lt_one.trans hs), poleFreeDedekindZeta_eq K hs]
  have hs1 : Not (s - 1 = 0) := by
    intro h
    have hS := sub_eq_zero.mp h
    rw [hS, Complex.one_re] at hs
    exact (lt_irrefl (1 : Real)) hs
  exact mul_ne_zero hs1 (dedekindZeta_ne_zero_of_one_lt_re K hs)

/-- The pole-free function has no zero at any real argument at least one. -/
theorem entirePoleFreeDedekindZeta_ne_zero_of_real_one_le {b : Real} (hb : 1 <= b) :
    Not (entirePoleFreeDedekindZeta K (b : Complex) = 0) := by
  by_cases h : b = 1
  case pos =>
    subst b
    rw [Complex.ofReal_one, entirePoleFreeDedekindZeta_eq_poleFree K (by simp),
      poleFreeDedekindZeta_one K]
    exact Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_pos K).ne'
  case neg =>
    apply entirePoleFreeDedekindZeta_ne_zero_of_one_lt_re K
    simpa only [Complex.ofReal_re] using lt_of_le_of_ne hb (Ne.symm h)

end DedekindZeta
