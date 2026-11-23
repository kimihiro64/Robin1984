import Robin1984.GRH.DedekindFunctionalBridge

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The classical Euler-product nonvanishing argument on the line of convergence.
- Formalization note: The Dedekind continuation on the boundary.
- PROVENANCE-END
-/

/-!
# The Dedekind continuation on the boundary

Apply the three-point inequality to the pole-cleared continuation
constructed from the number-field theta kernel.
-/

open NumberField Robin1984.GRH

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

theorem entirePoleFreeDedekindZeta_ne_zero_of_one_le_re {s : Complex} (hs : 1 <= s.re) :
    Not (entirePoleFreeDedekindZeta K s = 0) := by
  by_cases h : 1 < s.re
  case pos =>
    exact entirePoleFreeDedekindZeta_ne_zero_of_one_lt_re K h
  case neg =>
    apply dedekindPoleCleared_ne_zero_re_eq_one K (fun z => analyticAt_entirePoleFreeDedekindZeta K z)
    case hMatch =>
      intro z hz
      rw [entirePoleFreeDedekindZeta_eq_poleFree K (zero_lt_one.trans hz), poleFreeDedekindZeta_eq K hz]
    case hOne =>
      simpa only [Complex.ofReal_one] using
        entirePoleFreeDedekindZeta_ne_zero_of_real_one_le K (b := 1) (le_refl 1)
    case hs =>
      exact le_antisymm (le_of_not_gt h) hs

/-- The regularized Chebyshev transform is analytic on the closed
half-plane needed for Tauberian application. -/
theorem analyticAt_regularizedDedekindChebyshev {s : Complex} (hs : 1 <= s.re) :
    AnalyticAt Complex
      (fun z => -logDeriv (entirePoleFreeDedekindZeta K) z / z - 1 / z) s := by
  have hf := analyticAt_entirePoleFreeDedekindZeta K s
  have hNZ := entirePoleFreeDedekindZeta_ne_zero_of_one_le_re K hs
  have hS : Not (s = 0) := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact (not_le_of_gt zero_lt_one) hs
  have hLog : AnalyticAt Complex (logDeriv (entirePoleFreeDedekindZeta K)) s := by
    change AnalyticAt Complex (fun z => logDeriv (entirePoleFreeDedekindZeta K) z) s
    simp only [logDeriv_apply]
    exact hf.deriv.div hf hNZ
  exact (hLog.neg.div analyticAt_id hS).sub (analyticAt_const.div analyticAt_id hS)

end DedekindZeta
