import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic.FieldSimp
import Robin1984.GRH.MellinComparison

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Landau's theorem applied to the once-integrated prime-ideal error.
- Formalization note: The real recovery uses a divided difference at one. A real zero below one contributes its multiplicity divided by the negative factor beta times beta minus one.
- PROVENANCE-END
-/

/-!
# Landau's argument for the Dedekind tail comparison

The integrated error has a different kernel from the triangular explicit
formula. The apparent pole at one is removable, and the comparison
transform has a negative residue at any real zero between one half and one.
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace Robin1984.GRH

private theorem analyticAt_dslope_complex {g : Complex -> Complex} {s : Complex}
    (hg : AnalyticAt Complex g s) : AnalyticAt Complex (dslope g 1) s := by
  by_cases h : s = 1
  case pos =>
    subst s
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _
      (continuousAt_dslope_same.mpr hg.differentiableAt)
    let puncture : Set Complex := {w | Not (w = 1)}
    change Filter.Eventually (fun w => DifferentiableAt Complex (dslope g 1) w)
      (nhdsWithin 1 puncture)
    have hNe : Filter.Eventually (fun w : Complex => Not (w = 1))
        (nhdsWithin 1 puncture) := self_mem_nhdsWithin
    have hNear := hg.eventually_analyticAt.filter_mono
      (nhdsWithin_le_nhds : nhdsWithin (1 : Complex) puncture <= nhds 1)
    exact (hNe.and hNear).mono (fun w hw =>
      (differentiableAt_dslope_of_ne hw.1).mpr hw.2.differentiableAt)
  case neg =>
    have hQuotient : AnalyticAt Complex (fun w : Complex => (g w - g 1) / (w - 1)) s :=
      (hg.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr h)
    refine hQuotient.congr ?_
    have hNear : Filter.Eventually (fun w : Complex => Not (w = 1)) (nhds s) :=
      isOpen_ne.mem_nhds h
    exact hNear.mono (fun w hw => by rw [dslope_of_ne g hw, slope_def_field])

private theorem complex_sub_half_ne {w : Complex} (hw : (1 / 2 : Real) < w.re) :
    Not (w - (1 / 2 : Complex) = 0) := by
  intro h
  have hRe := congrArg Complex.re (sub_eq_zero.mp h)
  norm_num at hRe
  linarith only [hw, hRe]

private theorem complex_ne_zero_of_half_lt_re {w : Complex} (hw : (1 / 2 : Real) < w.re) :
    Not (w = 0) := by
  intro h
  rw [h, Complex.zero_re] at hw
  norm_num at hw

private theorem negative_residue_of_tailKernel
    {f Q : Complex -> Complex} {beta : Real} (hb : 0 < beta) (hb1 : beta < 1)
    (hf : AnalyticAt Complex f (beta : Complex)) (hZero : f (beta : Complex) = 0)
    (hGerm : Not (Filter.Eventually (fun w => f w = 0) (nhds (beta : Complex))))
    (hQ : ContinuousAt Q (beta : Complex)) :
    exists r : Real, And (r < 0)
      (Tendsto (fun s : Real => (s - beta) *
        (Q (s : Complex) + logDeriv f (s : Complex) /
          ((s : Complex) * ((s : Complex) - 1))).re)
        (nhdsWithin beta (Ioi beta)) (nhds r)) := by
  choose n hn using tendsto_scaled_logDeriv_at_zero hf hZero hGerm
  have hDenNeg : beta * (beta - 1) < 0 := mul_neg_of_pos_of_neg hb (sub_neg.mpr hb1)
  have hDen : Not ((beta : Complex) * ((beta : Complex) - 1) = 0) := by
    exact_mod_cast hDenNeg.ne
  have hIncl : Tendsto (fun s : Real => (s : Complex)) (nhdsWithin beta (Ioi beta))
      (nhdsWithin (beta : Complex) {w : Complex | Not (w = (beta : Complex))}) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine And.intro (Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) ?_
    have hRight : Filter.Eventually (fun s : Real => beta < s) (nhdsWithin beta (Ioi beta)) :=
      self_mem_nhdsWithin
    exact hRight.mono (fun s hs h => hs.ne (Complex.ofReal_injective h).symm)
  have hReg : Tendsto (fun w : Complex => (w - (beta : Complex)) * Q w)
      (nhds (beta : Complex)) (nhds 0) := by
    have hCont : ContinuousAt (fun w : Complex => (w - (beta : Complex)) * Q w)
        (beta : Complex) := (continuousAt_id.sub continuousAt_const).mul hQ
    simpa only [sub_self, zero_mul] using hCont.tendsto
  have hDenLim : Tendsto (fun w : Complex => w * (w - 1)) (nhds (beta : Complex))
      (nhds ((beta : Complex) * ((beta : Complex) - 1))) :=
    (continuousAt_id.mul (continuousAt_id.sub continuousAt_const)).tendsto
  have hLimit : Tendsto
      (fun w : Complex => (w - (beta : Complex)) *
        (Q w + logDeriv f w / (w * (w - 1))))
      (nhdsWithin (beta : Complex) {w : Complex | Not (w = (beta : Complex))})
      (nhds (0 + (n : Complex) / ((beta : Complex) * ((beta : Complex) - 1)))) := by
    refine ((hReg.mono_left nhdsWithin_le_nhds).add
      (hn.2.div (hDenLim.mono_left nhdsWithin_le_nhds) hDen)).congr' ?_
    exact Filter.Eventually.of_forall (fun w => by
      change (w - (beta : Complex)) * Q w + (w - (beta : Complex)) * logDeriv f w / (w * (w - 1))
        = (w - (beta : Complex)) * (Q w + logDeriv f w / (w * (w - 1)))
      rw [mul_add, mul_div_assoc])
  have hReal := Complex.continuous_re.continuousAt.tendsto.comp (hLimit.comp hIncl)
  have hNum : 0 < (n : Real) := by exact_mod_cast hn.1
  refine Exists.intro ((n : Real) / (beta * (beta - 1)))
    (And.intro (div_neg_of_pos_of_neg hNum hDenNeg) ?_)
  have hValue : (0 + (n : Complex) / ((beta : Complex) * ((beta : Complex) - 1))).re =
      (n : Real) / (beta * (beta - 1)) := by
    rw [zero_add]
    norm_cast
  change Tendsto (fun s : Real => (((s : Complex) - (beta : Complex)) *
    (Q (s : Complex) + logDeriv f (s : Complex) / ((s : Complex) * ((s : Complex) - 1)))).re)
      (nhdsWithin beta (Ioi beta)) _ at hReal
  simpa only [hValue, <- Complex.ofReal_sub, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hReal

/-- The differential identity from the Dedekind tail comparison excludes
zeros to the right of one half. At one the numerator of the divided
difference vanishes by the stated value of the error transform. -/
theorem ne_zero_of_dedekindTailComparison
    {Omega : Type*} [MeasurableSpace Omega] {X : Omega -> Real} {mu : Measure Omega}
    (hMeas : Measurable X)
    (hSupport : Filter.Eventually (fun x => 0 <= X x) (ae mu))
    {f : Complex -> Complex} {C Fone : Complex}
    (hf : AnalyticOnNhd Complex f {w : Complex | (1 / 2 : Real) < w.re})
    (hNoRealHigh : forall b : Real, 1 <= b -> Not (f (b : Complex) = 0))
    (hAtOne : logDeriv f 1 + 1 + Fone = 0)
    (hBaseExp : Membership.mem (interior (integrableExpSet X mu)) (-(2 : Complex)).re)
    (hInitial : Filter.EventuallyEq (nhds (2 : Complex)) (deriv f)
      (f * fun w => -1 - w * Fone - w * (w - 1) * (C / (w - 1 / 2)) +
        w * (w - 1) * complexMGF X mu (-w)))
    {z : Complex} (hz : (1 / 2 : Real) < z.re) :
    Not (f z = 0) := by
  let half : Set Complex := {w | (1 / 2 : Real) < w.re}
  let U : Complex -> Complex := fun w => C / (w - 1 / 2)
  let B : Complex -> Complex := fun w => w * (w - 1)
  let A : Complex -> Complex := fun w => -1 - w * Fone - B w * U w
  let P : Complex -> Complex := fun w => (logDeriv f w + 1) / w + Fone
  let J : Complex -> Complex := fun w => U w + dslope P 1 w
  let Q : Complex -> Complex := fun w => U w + (1 / w + Fone) / (w - 1)
  let H : Real -> Real := fun t => (J (-(t : Complex))).re
  have hU w (hw : Membership.mem half w) : AnalyticAt Complex U w :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (complex_sub_half_ne hw)
  have hB w : AnalyticAt Complex B w := analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
  have hA w (hw : Membership.mem half w) : AnalyticAt Complex A w :=
    (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).sub ((hB w).mul (hU w hw))
  have hPone : P 1 = 0 := by simpa only [P, div_one] using hAtOne
  have hJOff (w : Complex) (hW : Not (w = 1)) : J w = Q w + logDeriv f w / B w := by
    change U w + dslope P 1 w = Q w + logDeriv f w / B w
    rw [dslope_of_ne P hW, slope_def_field, hPone, sub_zero]
    simp only [P, Q, B, add_div, div_div, add_assoc, add_comm, add_left_comm]
  have hJAnalytic (w : Complex) (hw : Membership.mem half w) (hNonzero : Not (f w = 0)) :
      AnalyticAt Complex J w := by
    have hF := hf w hw
    have hLog : AnalyticAt Complex (logDeriv f) w := hF.deriv.div hF hNonzero
    have hP : AnalyticAt Complex P w := ((hLog.add analyticAt_const).div analyticAt_id
      (complex_ne_zero_of_half_lt_re hw)).add analyticAt_const
    exact (hU w hw).add (analyticAt_dslope_complex hP)
  have hCReal (b : Real) (hb : Membership.mem half (-(b : Complex)))
      (hNonzero : Not (f (-(b : Complex)) = 0)) : AnalyticAt Real H b := by
    have hFrom : AnalyticAt Real (fun t : Real => -(t : Complex)) b :=
      (Complex.ofRealCLM.analyticAt b).neg
    have hCompose := ((hJAnalytic (-(b : Complex)) hb hNonzero).restrictScalars : AnalyticAt Real J (-(b : Complex))).comp (x := b) hFrom
    exact (Complex.reCLM.analyticAt _).comp hCompose
  have hHalf (t : Real) (ht : t < -(1 / 2 : Real)) :
      Membership.mem half (-(t : Complex)) := by
    change (1 / 2 : Real) < (-(t : Complex)).re
    rw [Complex.neg_re, Complex.ofReal_re]
    exact lt_neg_of_lt_neg ht
  have hBase : Membership.mem half (2 : Complex) := by norm_num [half]
  have hBaseNonzero : Not (f (2 : Complex) = 0) := by
    simpa only [Complex.ofReal_ofNat] using hNoRealHigh 2 (by norm_num)
  refine ne_zero_of_mgf_comparison (A := A) (B := B) (H := H) (exceptional := -1)
    hMeas hSupport hf hA (fun w _ => hB w) hBase hBaseExp hBaseNonzero hInitial
    ?hRecover ?hExceptional ?hBoundary hz
  case hRecover =>
    intro t ht ht1 _ m hm
    let w : Complex := -(t : Complex)
    have hw : Membership.mem half w := hHalf t ht
    have hw1 : Not (w = 1) := by
      intro h
      have hRe := congrArg Complex.re h
      simp only [w, Complex.neg_re, Complex.ofReal_re, Complex.one_re] at hRe
      exact ht1 (by linarith only [hRe])
    have hw0 := complex_ne_zero_of_half_lt_re hw
    have hDen := sub_ne_zero.mpr hw1
    change logDeriv f w = A w + B w * m at hm
    change m.re = (J w).re
    suffices m = J w from congrArg Complex.re this
    rw [hJOff w hw1, hm]
    simp only [A, B, Q]
    field_simp [hw0, hDen]
    ring
  case hExceptional =>
    exact fun he hn => (hCReal (-1) (hHalf (-1) he) hn).continuousAt
  case hBoundary =>
    intro b hb
    let beta := -b
    have hHalfB := hHalf b hb
    by_cases hZero : f (-(b : Complex)) = 0
    case neg => exact Or.inl (hCReal b hHalfB hZero)
    case pos =>
      have hBetaHalf : (1 / 2 : Real) < beta := lt_neg_of_lt_neg hb
      have hBetaPos : 0 < beta := by linarith only [hBetaHalf]
      have hBeta1 : beta < 1 := by
        by_contra h
        exact hNoRealHigh beta (le_of_not_gt h) (by simpa only [beta, Complex.ofReal_neg] using hZero)
      have hHalfBeta : Membership.mem half (beta : Complex) := by
        simpa only [beta, Complex.ofReal_neg] using hHalfB
      have hZeroBeta : f (beta : Complex) = 0 := by
        simpa only [beta, Complex.ofReal_neg] using hZero
      have hGerm : Not (Filter.Eventually (fun w => f w = 0) (nhds (beta : Complex))) := by
        intro hLocal
        have hHalfConvex : Convex Real half := (convex_Ioi (1 / 2 : Real)).linear_preimage Complex.reLm
        have hConst : AnalyticOnNhd Complex (fun _ : Complex => (0 : Complex)) half :=
          fun _ _ => analyticAt_const
        exact hBaseNonzero
          (hf.eqOn_of_preconnected_of_eventuallyEq hConst
            hHalfConvex.isPreconnected hHalfBeta hLocal hBase)
      have hBeta0 := complex_ne_zero_of_half_lt_re hHalfBeta
      have hBetaSub : Not ((beta : Complex) - 1 = 0) := by
        exact_mod_cast (sub_neg.mpr hBeta1).ne
      have hQ : AnalyticAt Complex Q (beta : Complex) :=
        (hU _ hHalfBeta).add (((analyticAt_const.div analyticAt_id hBeta0).add
          analyticAt_const).div (analyticAt_id.sub analyticAt_const) hBetaSub)
      choose residue hResidue using negative_residue_of_tailKernel hBetaPos hBeta1
        (hf _ hHalfBeta) hZeroBeta hGerm hQ.continuousAt
      have hNearby : Filter.Eventually (fun s : Real => s < 1) (nhdsWithin beta (Ioi beta)) :=
        (show nhdsWithin beta (Ioi beta) <= nhds beta from nhdsWithin_le_nhds) (Iio_mem_nhds hBeta1)
      have hJResidue : Tendsto (fun s : Real => (s - beta) * (J (s : Complex)).re)
          (nhdsWithin beta (Ioi beta)) (nhds residue) := by
        refine hResidue.2.congr' (hNearby.mono (fun s hs => ?_))
        have hs1 : Not ((s : Complex) = 1) := by exact_mod_cast hs.ne
        simp only [hJOff (s : Complex) hs1, B]
      have hNeg : Tendsto (fun t : Real => -t) (nhdsWithin b (Iio b))
          (nhdsWithin beta (Ioi beta)) := by
        refine tendsto_nhdsWithin_iff.mpr (And.intro
          (continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_)
        have hLeft : Filter.Eventually (fun t : Real => t < b) (nhdsWithin b (Iio b)) :=
          self_mem_nhdsWithin
        exact hLeft.mono (fun _ ht => neg_lt_neg ht)
      exact Or.inr (Exists.intro residue (And.intro hResidue.1 (by
        simpa only [Function.comp_def, beta, neg_sub_neg, Complex.ofReal_neg, H]
          using hJResidue.comp hNeg)))

end Robin1984.GRH
