import Robin1984.GRH.DedekindProfileBound
import TauCeti.NumberTheory.LSeries.Newman.Tauberian

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Newman's Tauberian theorem applied to the actual Dedekind Chebyshev profile.
- Formalization note: Convergence of the actual Dedekind Chebyshev primitive.
- PROVENANCE-END
-/

/-!
# Convergence of the actual Dedekind Chebyshev primitive

Analyticity of the regularized logarithmic derivative on the boundary,
and boundedness of its logarithmic error profile, identify the improper
primitive and its exact value.
-/

open Filter MeasureTheory NumberField Robin1984.GRH Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

/-- The actual Dedekind Chebyshev primitive converges at infinity, with
value equal to the negative regularized logarithmic derivative at one. -/
theorem exists_dedekindChebyshevPrimitiveLimit :
    Exists (fun a : Real =>
      And (Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds a))
        ((a : Complex) = -(logDeriv (entirePoleFreeDedekindZeta K) 1 + 1))) := by
  let B := dedekindLogErrorProfile K
  let P := realPrimitiveFromOne (dedekindChebyshevErrorRatio K)
  let f := entirePoleFreeDedekindZeta K
  let G : Complex -> Complex := fun z => -logDeriv f (z + 1) / (z + 1) - 1 / (z + 1)
  have hMeas : AEStronglyMeasurable B (volume.restrict (Ici (0 : Real))) :=
    (measurable_dedekindLogErrorProfile K).aestronglyMeasurable
  have hAllBound := exists_bound_dedekindLogErrorProfile K
  let M := Classical.choose hAllBound
  have hBound : forall t : Real, Membership.mem (Ici (0 : Real)) t -> norm (B t) <= M :=
    Classical.choose_spec hAllBound
  have hAnalytic (z : Complex) (hz : z.re = 0) : AnalyticAt Complex G z := by
    have hs : 1 <= (z + 1).re := by rw [Complex.add_re, Complex.one_re, hz, zero_add]
    have hShift : AnalyticAt Complex (fun w : Complex => w + 1) z :=
      analyticAt_id.add analyticAt_const
    exact (analyticAt_regularizedDedekindChebyshev K hs).comp_of_eq hShift rfl
  have hLaplace (z : Complex) (hz : 0 < z.re) :
      G z = integral (volume.restrict (Ici (0 : Real)))
        (fun t : Real => B t * Complex.exp (-z * (t : Complex))) := by
    have h := dedekindLogErrorProfile_laplace K hz
    calc
      G z = -(logDeriv f (z + 1) + 1) / (z + 1) := by dsimp [G]; ring
      _ = _ := h
  have hTransform :=
    TauCeti.LSeries.newmanLaplace_tendsto_integral_of_analyticAt hMeas hBound hAnalytic hLaplace
  have hProfile : Filter.EventuallyEq atTop
      (fun T : Real => intervalIntegral B 0 T volume)
      (fun T : Real => (P (Real.exp T) : Complex)) :=
    eventually_atTop.mpr (Exists.intro 0
      (fun _ hT => intervalIntegral_dedekindLogErrorProfile K hT))
  have hAtExp := hTransform.congr' hProfile
  have hReal : Tendsto (fun T : Real => P (Real.exp T)) atTop (nhds ((G 0).re)) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      (Complex.continuous_re.continuousAt.tendsto.comp hAtExp)
  have hImag : Tendsto (fun _ : Real => (0 : Real)) atTop (nhds ((G 0).im)) := by
    simpa only [Function.comp_def, Complex.ofReal_im] using
      (Complex.continuous_im.continuousAt.tendsto.comp hAtExp)
  have hIm : (G 0).im = 0 := tendsto_nhds_unique hImag tendsto_const_nhds
  have hLog := hReal.comp Real.tendsto_log_atTop
  have hChart : Filter.EventuallyEq atTop (fun x : Real => P (Real.exp (Real.log x))) P :=
    eventually_atTop.mpr (Exists.intro 1 (fun x hx => by
      change P (Real.exp (Real.log x)) = P x
      rw [Real.exp_log (zero_lt_one.trans_le hx)]))
  have hValue : G 0 = -(logDeriv f 1 + 1) := by
    simp only [G, zero_add, div_one]
    ring
  refine Exists.intro ((G 0).re) (And.intro (hLog.congr' hChart) ?_)
  change ((G 0).re : Complex) = -(logDeriv f 1 + 1)
  rw [<- hValue]
  exact Complex.ext rfl (by simpa only [Complex.ofReal_im, hIm])

end DedekindZeta
