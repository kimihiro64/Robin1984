import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Mathlib's analytic class number formula for Dedekind zeta.
- Formalization note: Compose the real one-sided residue limit with a unit translation, real part, and logarithm.
- PROVENANCE-END
-/

/-!
# The slope-one logarithmic residue limit

The real class number formula gives the logarithmic limit required to
identify the Dedekind Mertens constant.
-/

open Filter NumberField Set Topology

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

/-- The sum of the logarithmic pole term and the logarithm of zeta tends
to the logarithm of the positive Dedekind residue. -/
theorem tendsto_log_dedekindZeta_add_log_scale :
    Tendsto (fun u : Real => Real.log (dedekindZeta K ((1 + u : Real) : Complex)).re + Real.log u)
      (nhdsWithin 0 (Ioi (0 : Real))) (nhds (Real.log (dedekindZeta_residue K))) := by
  have hShift : Tendsto (fun u : Real => 1 + u) (nhdsWithin 0 (Ioi (0 : Real)))
      (nhdsWithin 1 (Ioi (1 : Real))) := by
    have hc : ContinuousAt (fun u : Real => 1 + u) 0 := continuousAt_const.add continuousAt_id
    have hTop : Tendsto (fun u : Real => 1 + u) (nhdsWithin 0 (Ioi (0 : Real))) (nhds 1) := by
      simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hTop ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    change 1 < 1 + u
    exact lt_add_of_pos_right 1 (show 0 < u from hu)
  have hMul := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).comp hShift
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp hMul
  have hMass : Tendsto (fun u : Real => u * (dedekindZeta K ((1 + u : Real) : Complex)).re)
      (nhdsWithin 0 (Ioi (0 : Real))) (nhds (dedekindZeta_residue K)) := by
    simpa only [Function.comp_def, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      add_sub_cancel_left, zero_sub, neg_zero, zero_mul, sub_zero] using hRe
  have hLog := (Real.continuousAt_log (dedekindZeta_residue_ne_zero K)).tendsto.comp hMass
  have hPos : Filter.Eventually
      (fun u : Real => 0 < u * (dedekindZeta K ((1 + u : Real) : Complex)).re)
      (nhdsWithin 0 (Ioi (0 : Real))) :=
    hMass.eventually (Ioi_mem_nhds (dedekindZeta_residue_pos K))
  refine hLog.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hPos] with u hu hProduct
  change Real.log (u * (dedekindZeta K ((1 + u : Real) : Complex)).re) =
    Real.log (dedekindZeta K ((1 + u : Real) : Complex)).re + Real.log u
  have hZeta : Not ((dedekindZeta K ((1 + u : Real) : Complex)).re = 0) := by
    intro h
    rw [h, mul_zero] at hProduct
    exact (lt_irrefl 0) hProduct
  rw [Real.log_mul (show 0 < u from hu).ne' hZeta, add_comm]

end Robin1984.GRH
