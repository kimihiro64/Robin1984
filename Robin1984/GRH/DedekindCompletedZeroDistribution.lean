import Robin1984.GRH.DedekindLineBridge

/-!
# The zeros of the pole-cleared completed Dedekind zeta function

The functional equation extends across the two removed poles. The completed
entire function is nonzero outside the open critical strip, where its zeros
agree with those of the actual zeta continuation.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Dedekind functional equation and the Euler-product nonvanishing region.
- Formalization note: Continue the functional equation of the pole-cleared function through both endpoints.
- Content basis: Analytic continuation, nonvanishing on the line one, and nonvanishing of gamma factors.
- Dependency status: Optional GRH extension and the pinned Dedekind-zeta theta modules.
-/

open Filter NumberField Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

/-- The pole-cleared entire completion satisfies reflection at every complex point. -/
theorem completedDedekindPoleCleared_functionalEquation (s : Complex) :
    completedDedekindPoleCleared K s = completedDedekindPoleCleared K (1 - s) := by
  let f := completedDedekindPoleCleared K
  let g := fun z : Complex => f (1 - z)
  have hf : AnalyticOnNhd Complex f univ :=
    fun z _ => analyticAt_completedDedekindPoleCleared K z
  have hg : AnalyticOnNhd Complex g univ := by
    intro z _
    exact (analyticAt_completedDedekindPoleCleared K (1 - z)).comp
      (analyticAt_const.sub analyticAt_id)
  have hOpen : IsOpen {z : Complex | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hMem : Membership.mem {z : Complex | 1 < z.re} (2 : Complex) := by
    change 1 < (2 : Complex).re
    norm_num
  have hNear : Filter.EventuallyEq (nhds (2 : Complex)) f g := by
    filter_upwards [hOpen.mem_nhds hMem] with z hz
    change 1 < z.re at hz
    have h0 : Not (z = 0) := by
      intro h
      rw [h, Complex.zero_re] at hz
      linarith only [hz]
    have h1 : Not (z = 1) := by
      intro h
      rw [h, Complex.one_re] at hz
      exact (lt_irrefl (1 : Real)) hz
    have hR0 : Not (1 - z = 0) := sub_ne_zero.mpr (Ne.symm h1)
    have hR1 : Not (1 - z = 1) := by
      intro h
      have hRe := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re] at hRe
      linarith only [hRe, hz]
    change completedDedekindPoleCleared K z = completedDedekindPoleCleared K (1 - z)
    rw [completedDedekindPoleCleared_eq K h0 h1,
      completedDedekindPoleCleared_eq K hR0 hR1,
      completedDedekindContinuation_functionalEquation K h0 h1]
    ring
  exact (hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ _) hNear)
    (mem_univ s)

/-- The entire completion is nonvanishing on the closed half-plane to the right. -/
theorem completedDedekindPoleCleared_ne_zero_of_one_le_re {s : Complex}
    (hs : 1 <= s.re) : Not (completedDedekindPoleCleared K s = 0) := by
  have hsPos := zero_lt_one.trans_le hs
  have hs0 : Not (s = 0) := by
    intro h
    rw [h, Complex.zero_re] at hsPos
    exact (lt_irrefl _) hsPos
  rw [completedDedekindPoleCleared_eq_archimedean K hsPos]
  exact mul_ne_zero (mul_ne_zero hs0 (ZInfty_ne_zero_of_re_pos K hsPos))
    (entirePoleFreeDedekindZeta_ne_zero_of_one_le_re K hs)

/-- Every zero of the entire completion lies in the open critical strip. -/
theorem completedDedekindPoleCleared_zero_in_strip {s : Complex}
    (hz : completedDedekindPoleCleared K s = 0) : And (0 < s.re) (s.re < 1) := by
  have hR : s.re < 1 := lt_of_not_ge
    (fun h => completedDedekindPoleCleared_ne_zero_of_one_le_re K h hz)
  have hL : 0 < s.re := by
    apply lt_of_not_ge
    intro h
    have hRe : 1 <= ((1 : Complex) - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith only [h]
    have hZero := (completedDedekindPoleCleared_functionalEquation K s).symm.trans hz
    exact completedDedekindPoleCleared_ne_zero_of_one_le_re K hRe hZero
  exact And.intro hL hR

/-- Dedekind RH places every zero of the actual entire completion
on real part one half. -/
theorem completedDedekindPoleCleared_zero_re_of_dedekindRH
    (h : Robin1984.GRH.DedekindRH K) {s : Complex}
    (hz : completedDedekindPoleCleared K s = 0) : s.re = 1 / 2 := by
  have hs := completedDedekindPoleCleared_zero_in_strip K hz
  have hs0 : Not (s = 0) := by
    intro heq
    have hPos := hs.1
    rw [heq, Complex.zero_re] at hPos
    exact (lt_irrefl _) hPos
  rw [completedDedekindPoleCleared_eq_archimedean K hs.1] at hz
  have hF := (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero hs0 (ZInfty_ne_zero_of_re_pos K hs.1))
  have hZ : dedekindZetaContinuation K s = 0 := by
    unfold dedekindZetaContinuation
    rw [hF, zero_div]
  exact (Robin1984.GRH.dedekindRH_iff_zeros_of_continuation
    (isDedekindZetaContinuation_actual K)).mp h s hs.1 hs.2 hZ

end DedekindZeta
