import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Factorization of an analytic function at an isolated zero and the residue of its logarithmic derivative.
- Formalization note: The punctured complex limit yields the positive multiplicity used to compute the real residues of the comparison transforms.
- PROVENANCE-END
-/

/-!
# The logarithmic derivative at a zero

Scaling by the distance from an isolated zero extracts its positive
multiplicity from the logarithmic derivative.
-/

open Filter Set

namespace Robin1984.GRH

/-- At a zero of a nonzero analytic germ, the scaled logarithmic derivative
converges to a positive integer. -/
theorem tendsto_scaled_logDeriv_at_zero {f : Complex -> Complex} {z : Complex}
    (hf : AnalyticAt Complex f z) (hZero : f z = 0)
    (hNonzeroGerm : Not (Filter.Eventually (fun w => f w = 0) (nhds z))) :
    exists n : Nat, And (0 < n)
      (Tendsto (fun w => (w - z) * logDeriv f w)
        (nhdsWithin z {w : Complex | Not (w = z)}) (nhds (n : Complex))) := by
  choose n g facts using (hf.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hNonzeroGerm
  have hg : AnalyticAt Complex g z := facts.1
  have hg0 : Not (g z = 0) := facts.2.1
  have hFactor : Filter.EventuallyEq (nhds z) f (fun w => (w - z) ^ n * g w) :=
    facts.2.2.mono (fun _ h => by simpa only [smul_eq_mul] using h)
  have hPos : 0 < n := Nat.pos_of_ne_zero (fun hn => by
    have hAt := hFactor.self_of_nhds
    simp only [hZero, hn, pow_zero, one_mul] at hAt
    exact hg0 hAt.symm)
  let punctured : Set Complex := {w : Complex | Not (w = z)}
  have hPunctured : Filter.Eventually (fun w => Not (w = z)) (nhdsWithin z punctured) :=
    self_mem_nhdsWithin
  have hNonzeroOpen : IsOpen {w : Complex | Not (w = 0)} :=
    isOpen_ne
  have hNearNonzero : Filter.Eventually (fun w => Not (g w = 0)) (nhds z) :=
    hg.continuousAt.tendsto.eventually (hNonzeroOpen.mem_nhds hg0)
  have hExpression : Filter.EventuallyEq (nhdsWithin z punctured)
      (fun w => (w - z) * logDeriv f w)
      (fun w => (n : Complex) + (w - z) * logDeriv g w) := by
    filter_upwards [hPunctured, (logDeriv_congr_nhds hFactor).filter_mono nhdsWithin_le_nhds,
      hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      hNearNonzero.filter_mono nhdsWithin_le_nhds] with w hw hfw hgw hgn
    have hSub : Not (w - z = 0) := sub_ne_zero.mpr hw
    have hId : HasDerivAt (fun v : Complex => v - z) 1 w :=
      (hasDerivAt_id w).sub_const z
    have hSimple : logDeriv (fun v => v - z) w = 1 / (w - z) := by
      rw [logDeriv_apply, hId.deriv]
    rw [hfw, logDeriv_mul (f := fun v => (v - z) ^ n) w (pow_ne_zero n hSub)
      hgn (hId.differentiableAt.pow n)
      hgw.differentiableAt, logDeriv_fun_pow hId.differentiableAt n, hSimple]
    field_simp [hSub]
  have hLogRegular : ContinuousAt (logDeriv g) z :=
    hg.deriv.continuousAt.div hg.continuousAt hg0
  have hRegular : ContinuousAt
      (fun w => (n : Complex) + (w - z) * logDeriv g w) z :=
    continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul hLogRegular)
  have hLimit : Tendsto (fun w => (n : Complex) + (w - z) * logDeriv g w)
      (nhdsWithin z punctured) (nhds (n : Complex)) := by
    simpa only [sub_self, zero_mul, add_zero] using
      hRegular.tendsto.mono_left nhdsWithin_le_nhds
  exact Exists.intro n (And.intro hPos (hLimit.congr' hExpression.symm))

end Robin1984.GRH
