import Mathlib

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Exact colossally abundant marginal events

An event raises one prime exponent by one.  Its logarithmic gain and threshold
give an exact finite representation of the fixed-parameter colossally
abundant objective.
-/

namespace Robin1984
/-- A marginal event `(p, j)` raises the exponent of `p` from `j - 1` to `j`. -/
structure Event where
  p : ℕ
  j : ℕ
  hp : Nat.Prime p
  hj : 0 < j
deriving Repr, DecidableEq

namespace Event

/-- The exact logarithmic gain in `σ(n)/n` from a marginal event. -/
noncomputable def gain (e : Event) : ℝ :=
  Real.log ((1 - (e.p : ℝ) ^ (-(e.j + 1 : ℤ))) /
    (1 - (e.p : ℝ) ^ (-(e.j : ℤ))))

/-- The event threshold, used to order CA marginal events. -/
noncomputable def threshold (e : Event) : ℝ :=
  e.gain / Real.log e.p


lemma prime_pos (e : Event) : 0 < (e.p : ℝ) := by
  exact_mod_cast Nat.Prime.pos e.hp

lemma log_prime_pos (e : Event) : 0 < Real.log (e.p : ℝ) := by
  exact Real.log_pos (by exact_mod_cast e.hp.one_lt)

lemma threshold_mul_log (e : Event) :
    e.threshold * Real.log e.p = e.gain := by
  unfold threshold
  field_simp [ne_of_gt e.log_prime_pos]

lemma gain_eq_firstLayerContinuousGain_of_j_eq_one
    {e : Event}
    (hj : e.j = 1) :
    e.gain = Real.log (1 + (e.p : ℝ)⁻¹) := by
  unfold gain
  rw [hj]
  have hpne : (e.p : ℝ) ≠ 0 := ne_of_gt e.prime_pos
  have hpone : (e.p : ℝ) ≠ 1 := by
    have hpgt : (1 : ℝ) < e.p := by exact_mod_cast e.hp.one_lt
    exact ne_of_gt hpgt
  have hden : 1 - (e.p : ℝ) ^ (-(1 : ℤ)) ≠ 0 := by
    have hpgt : (1 : ℝ) < e.p := by exact_mod_cast e.hp.one_lt
    have hinvlt : (e.p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpgt
    rw [zpow_neg, zpow_one]
    linarith
  have hratio :
      (1 - ((e.p : ℝ) ^ 2)⁻¹) / (1 - ((e.p : ℝ))⁻¹) =
        1 + 1 / (e.p : ℝ) := by
    have hden' : -1 + (e.p : ℝ) ≠ 0 := by
      intro h
      apply hpone
      linarith
    field_simp [hpne, hden']
    ring
  norm_num
  exact (congrArg Real.log hratio).trans (by simp [one_div])

lemma threshold_eq_firstLayer_of_j_eq_one
    {e : Event}
    (hj : e.j = 1) :
    e.threshold = Real.log (1 + (e.p : ℝ)⁻¹) / Real.log (e.p : ℝ) := by
  unfold threshold
  rw [gain_eq_firstLayerContinuousGain_of_j_eq_one hj]

end Event

end Robin1984
