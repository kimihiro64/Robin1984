import Robin1984.GRH.DedekindLaplaceProfile
import Robin1984.GRH.DedekindPrimeIdealTheorem

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Boundedness of the logarithmic Chebyshev profile from the Dedekind prime ideal theorem.
- Formalization note: Boundedness in the Dedekind logarithmic chart.
- PROVENANCE-END
-/

/-!
# Boundedness in the Dedekind logarithmic chart

The prime ideal theorem bounds the Chebyshev error profile on the positive
axis. Monotonicity supplies the bound on the initial compact interval.
-/

open Filter MeasureTheory NumberField Robin1984.GRH Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

private theorem norm_logErrorProfile (t : Real) :
    norm (dedekindLogErrorProfile K t) =
      abs (dedekindChebyshev K (Real.exp t) / Real.exp t - 1) := by
  rw [dedekindLogErrorProfile, <- Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  congr 1
  rw [dedekindChebyshevErrorRatio]
  field_simp [(Real.exp_pos t).ne']

/-- The actual logarithmic Chebyshev profile is bounded on the full
nonnegative real axis. -/
theorem exists_bound_dedekindLogErrorProfile :
    Exists (fun M : Real => forall t : Real, 0 <= t -> norm (dedekindLogErrorProfile K t) <= M) := by
  have hEventually : Filter.Eventually (fun x : Real => dedekindChebyshev K x / x < 2) atTop :=
    (dedekindChebyshev_div_tendsto_one K).eventually (gt_mem_nhds (show (1 : Real) < 2 by norm_num))
  let R := Classical.choose (eventually_atTop.mp hEventually)
  have hR := Classical.choose_spec (eventually_atTop.mp hEventually)
  refine Exists.intro (1 + max 2 (dedekindChebyshev K R)) ?_
  intro t ht
  let x := Real.exp t
  have hx : 1 <= x := by
    change 1 <= Real.exp t
    rw [<- Real.exp_zero]
    exact Real.exp_le_exp.mpr ht
  have hNonnegativePsi : 0 <= dedekindChebyshev K x := dedekindChebyshev_nonneg K x
  have hNonnegative : 0 <= dedekindChebyshev K x / x :=
    div_nonneg hNonnegativePsi (zero_le_one.trans hx)
  have hBound : dedekindChebyshev K x / x <= max 2 (dedekindChebyshev K R) := by
    by_cases h : R <= x
    case pos => exact (hR x h).le.trans (le_max_left _ _)
    case neg =>
      have hPsi := (monotone_dedekindChebyshev K) (le_of_not_ge h)
      exact (div_le_self hNonnegativePsi hx).trans (hPsi.trans (le_max_right _ _))
  rw [norm_logErrorProfile]
  change abs (dedekindChebyshev K x / x - 1) <= 1 + max 2 (dedekindChebyshev K R)
  have hMax : (2 : Real) <= max 2 (dedekindChebyshev K R) := le_max_left _ _
  exact abs_le.mpr (And.intro (by linarith) (by linarith))

end DedekindZeta
