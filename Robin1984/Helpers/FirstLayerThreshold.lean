import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Robin1984.Helpers.Event

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# First-layer event thresholds

This module treats the first-layer gain and threshold as real functions of the
prime scale, proves their derivative formulas, and establishes the threshold's
monotonic decrease.
-/

namespace Robin1984


/-- Continuous first-layer gain `log(1 + 1/t)`. -/
noncomputable def firstLayerContinuousGain (t : ℝ) : ℝ :=
  Real.log (1 + t⁻¹)


/-- First-layer threshold as a continuous function of the prime scale. -/
noncomputable def firstLayerThreshold (t : ℝ) : ℝ :=
  firstLayerContinuousGain t / Real.log t


lemma hasDerivAt_firstLayerContinuousGain
    {t : ℝ}
    (ht : t ≠ 0)
    (harg : 1 + 1 / t ≠ 0) :
    HasDerivAt firstLayerContinuousGain (-(1 / (t^2)) / (1 + 1 / t)) t := by
  unfold firstLayerContinuousGain
  have hdiv : HasDerivAt (fun u : ℝ => 1 / u) ((0 * t - 1 * 1) / t ^ 2) t := by
    exact (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht
  have hslope : (0 * t - 1 * 1) / t ^ 2 = -(1 / t^2) := by
    field_simp [ht]
    ring
  have hinner : HasDerivAt (fun u : ℝ => 1 + 1 / u) (-(1 / t^2)) t := by
    exact (hdiv.const_add (1 : Real)).congr_deriv hslope
  simpa [one_div] using hinner.log harg


lemma firstLayerThreshold_derivativeNumerator_neg
    {t : ℝ}
    (ht : 1 < t) :
    (-(1 / (t^2)) / (1 + 1 / t)) * Real.log t -
        firstLayerContinuousGain t * (1 / t) < 0 := by
  have htpos : 0 < t := by linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hgainpos : 0 < firstLayerContinuousGain t := by
    unfold firstLayerContinuousGain
    apply Real.log_pos
    have hinvpos : 0 < t⁻¹ := inv_pos.mpr htpos
    linarith
  have hdenpos : 0 < 1 + 1 / t := by
    have hinvpos : 0 < 1 / t := by positivity
    linarith
  have hleftneg : (-(1 / (t^2)) / (1 + 1 / t)) * Real.log t < 0 := by
    have hslopeNeg : (-(1 / (t^2)) / (1 + 1 / t)) < 0 := by
      have ht2pos : 0 < t^2 := sq_pos_of_ne_zero htne
      have hinv2pos : 0 < 1 / (t^2) := by positivity
      have hnumneg : -(1 / (t^2)) < 0 := by linarith
      exact div_neg_of_neg_of_pos hnumneg hdenpos
    exact mul_neg_of_neg_of_pos hslopeNeg hlogpos
  have hrightpos : 0 < firstLayerContinuousGain t * (1 / t) := by
    have hinvpos : 0 < 1 / t := by positivity
    exact mul_pos hgainpos hinvpos
  nlinarith

lemma hasDerivAt_firstLayerThreshold
    {t : ℝ}
    (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => firstLayerThreshold u)
      (((-(1 / (t^2)) / (1 + 1 / t)) * Real.log t -
          firstLayerContinuousGain t * (1 / t)) / (Real.log t)^2) t := by
  unfold firstLayerThreshold
  have htpos : 0 < t := by linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have harg : 1 + 1 / t ≠ 0 := by
    have hinvpos : 0 < 1 / t := by positivity
    positivity
  have hg := hasDerivAt_firstLayerContinuousGain (t := t) htne harg
  have hlogd : HasDerivAt (fun u : ℝ => Real.log u) (1 / t) t := by
    simpa [one_div] using Real.hasDerivAt_log htne
  have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  exact hg.div hlogd hlogne

lemma firstLayerThreshold_derivative_neg
    {t : ℝ}
    (ht : 1 < t) :
    ((-(1 / (t^2)) / (1 + 1 / t)) * Real.log t -
        firstLayerContinuousGain t * (1 / t)) / (Real.log t)^2 < 0 := by
  have hnum := firstLayerThreshold_derivativeNumerator_neg ht
  have hdenpos : 0 < (Real.log t)^2 := sq_pos_of_ne_zero (ne_of_gt (Real.log_pos ht))
  exact div_neg_of_neg_of_pos hnum hdenpos

lemma strictAntiOn_firstLayerThreshold :
    StrictAntiOn firstLayerThreshold (Set.Ioi (1 : ℝ)) := by
  exact strictAntiOn_of_deriv_neg (convex_Ioi (1 : ℝ))
    (by
      intro x hx
      exact (hasDerivAt_firstLayerThreshold (t := x) hx).continuousAt.continuousWithinAt)
    (by
      intro x hx
      rw [interior_Ioi] at hx
      have hder := hasDerivAt_firstLayerThreshold (t := x) hx
      rw [hder.deriv]
      exact firstLayerThreshold_derivative_neg hx)

lemma firstLayerThreshold_antitone_on_gt_one
    {a b : ℝ}
    (ha : 1 < a)
    (hab : a ≤ b) :
    firstLayerThreshold b ≤ firstLayerThreshold a := by
  by_cases heq : a = b
  · subst b
    exact le_rfl
  · have hlt : a < b := lt_of_le_of_ne hab heq
    have hb : b ∈ Set.Ioi (1 : ℝ) := by
      exact lt_trans ha hlt
    have ha' : a ∈ Set.Ioi (1 : ℝ) := ha
    exact (strictAntiOn_firstLayerThreshold ha' hb hlt).le

lemma firstLayerThreshold_nat_antitone
    {p q : ℕ}
    (hp : 1 < p)
    (hpq : p ≤ q) :
    firstLayerThreshold (q : ℝ) ≤ firstLayerThreshold (p : ℝ) := by
  have hpReal : 1 < (p : ℝ) := by exact_mod_cast hp
  have hpqReal : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
  exact firstLayerThreshold_antitone_on_gt_one hpReal hpqReal


lemma firstLayerEvent_threshold_antitone
    {e f : Event}
    (hej : e.j = 1)
    (hfj : f.j = 1)
    (hpf : e.p ≤ f.p) :
    f.threshold ≤ e.threshold := by
  rw [Event.threshold_eq_firstLayer_of_j_eq_one hej,
    Event.threshold_eq_firstLayer_of_j_eq_one hfj]
  exact firstLayerThreshold_nat_antitone e.hp.one_lt hpf


end Robin1984
