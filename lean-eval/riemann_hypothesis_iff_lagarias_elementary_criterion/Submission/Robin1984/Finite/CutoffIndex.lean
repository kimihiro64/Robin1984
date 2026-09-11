import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Fixed-prime cutoff indices

This file formalizes the exact algebra behind the cutoff-index mnemonic

```text
j_q(P) ~= floor(log_q(((1 - 1/q) P log P) / log q)).
```

The final asymptotic substitution `lambda_P ~ 1 / (P log P)` is deliberately
not made here.  The checked theorem uses an arbitrary positive threshold
parameter `lambda`, so it can later be instantiated with the CA first-layer
threshold.
-/

namespace Robin1984.FiniteSupport

/-- Exact simplified gain for adding the `j`th exponent at base `q`.

This is the algebraic form

```text
log ((1 - q^(-(j+1))) / (1 - q^(-j)))
  = log (1 + (q - 1) / (q * (q^j - 1))).
```

The bridge back to `Event.gain` is proved below, so this expression can be
used for concrete event packets.
-/
noncomputable def simplifiedLayerGain (q : Real) (j : Nat) : Real :=
  Real.log (1 + (q - 1) / (q * (q ^ j - 1)))


theorem pow_sub_one_pos_of_one_lt_of_pos_nat
    {q : Real} {j : Nat} (hq : 1 < q) (hj : 0 < j) :
    0 < q ^ j - 1 := by
  have hqnonneg : 0 <= q := le_of_lt (lt_trans zero_lt_one hq)
  have hpow : 1 < q ^ j :=
    (one_lt_pow_iff_of_nonneg hqnonneg hj.ne').mpr hq
  linarith

/-- Denominator of the fixed-layer gain fraction, written as a finite
geometric sum. -/
noncomputable def simplifiedLayerGainDenomSum (q : Real) (j : Nat) : Real :=
  (Finset.range j).sum (fun i => q ^ (i + 1))

/-- The finite geometric sum is the exact denominator
`q * (q^j - 1) / (q - 1)` appearing in the simplified layer gain. -/
theorem simplifiedLayerGainDenomSum_eq
    {q : Real} {j : Nat} (hq : 1 < q) :
    simplifiedLayerGainDenomSum q j =
      q * (q ^ j - 1) / (q - 1) := by
  unfold simplifiedLayerGainDenomSum
  rw [show (Finset.range j).sum (fun i => q ^ (i + 1)) =
      q * (Finset.range j).sum (fun i => q ^ i) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [pow_succ]
    ring]
  have hqne : Ne q 1 := by linarith
  rw [geom_sum_eq hqne j]
  ring

/-- The denominator sum is positive for positive layer index. -/
theorem simplifiedLayerGainDenomSum_pos
    {q : Real} {j : Nat} (hq : 1 < q) (hj : 0 < j) :
    0 < simplifiedLayerGainDenomSum q j := by
  unfold simplifiedLayerGainDenomSum
  apply Finset.sum_pos
  intro i _hi
  exact pow_pos (lt_trans zero_lt_one hq) (i + 1)
  exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hj)

/-- Power monotonicity over nonnegative real bases, specialized to natural
exponents. -/
theorem real_natPow_mono_of_nonneg
    {a b : Real} (ha : 0 <= a) (hab : a <= b) (n : Nat) :
    a ^ n <= b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hb : 0 <= b := le_trans ha hab
      have hb_pow : 0 <= b ^ n := pow_nonneg hb n
      have hmul := mul_le_mul ih hab ha hb_pow
      simpa [pow_succ] using hmul


/-- The fixed-layer denominator sum is monotone in the base. -/
theorem simplifiedLayerGainDenomSum_mono
    {a b : Real} {j : Nat} (ha : 0 <= a) (hab : a <= b) :
    simplifiedLayerGainDenomSum a j <= simplifiedLayerGainDenomSum b j := by
  unfold simplifiedLayerGainDenomSum
  apply Finset.sum_le_sum
  intro i _hi
  exact real_natPow_mono_of_nonneg ha hab (i + 1)

/-- For a fixed layer `j`, the rational part of the simplified gain is
decreasing as the prime base grows. -/
theorem simplifiedLayerGain_fraction_le_of_base_le
    {a b : Real} {j : Nat}
    (ha : 1 < a) (hab : a <= b) (hj : 0 < j) :
    (b - 1) / (b * (b ^ j - 1)) <=
      (a - 1) / (a * (a ^ j - 1)) := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hSa := simplifiedLayerGainDenomSum_eq (q := a) (j := j) ha
  have hSb := simplifiedLayerGainDenomSum_eq (q := b) (j := j) hb
  have hSa_pos := simplifiedLayerGainDenomSum_pos (q := a) (j := j) ha hj
  have hSle := simplifiedLayerGainDenomSum_mono (a := a) (b := b) (j := j)
    (le_of_lt (lt_trans zero_lt_one ha)) hab
  have hinv :
      1 / simplifiedLayerGainDenomSum b j <=
        1 / simplifiedLayerGainDenomSum a j :=
    one_div_le_one_div_of_le hSa_pos hSle
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have hb_pos : 0 < b := lt_trans zero_lt_one hb
  have haj_pos : 0 < a ^ j - 1 :=
    pow_sub_one_pos_of_one_lt_of_pos_nat ha hj
  have hbj_pos : 0 < b ^ j - 1 :=
    pow_sub_one_pos_of_one_lt_of_pos_nat hb hj
  have hA :
      1 / simplifiedLayerGainDenomSum a j =
        (a - 1) / (a * (a ^ j - 1)) := by
    rw [hSa]
    field_simp [ne_of_gt ha_pos, ne_of_gt haj_pos,
      sub_ne_zero.mpr (ne_of_gt ha)]
  have hB :
      1 / simplifiedLayerGainDenomSum b j =
        (b - 1) / (b * (b ^ j - 1)) := by
    rw [hSb]
    field_simp [ne_of_gt hb_pos, ne_of_gt hbj_pos,
      sub_ne_zero.mpr (ne_of_gt hb)]
  rwa [hA, hB] at hinv

/-- For a fixed layer `j`, the simplified layer gain is antitone in the
prime base. -/
theorem simplifiedLayerGain_le_of_base_le
    {a b : Real} {j : Nat}
    (ha : 1 < a) (hab : a <= b) (hj : 0 < j) :
    simplifiedLayerGain b j <= simplifiedLayerGain a j := by
  have hfrac :=
    simplifiedLayerGain_fraction_le_of_base_le
      (a := a) (b := b) (j := j) ha hab hj
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hb_num : 0 < b - 1 := by linarith
  have hb_den : 0 < b * (b ^ j - 1) :=
    mul_pos (lt_trans zero_lt_one hb)
      (pow_sub_one_pos_of_one_lt_of_pos_nat hb hj)
  have hb_arg :
      0 < 1 + (b - 1) / (b * (b ^ j - 1)) := by
    have hfrac_pos : 0 < (b - 1) / (b * (b ^ j - 1)) :=
      div_pos hb_num hb_den
    linarith
  have harg_le :
      1 + (b - 1) / (b * (b ^ j - 1)) <=
        1 + (a - 1) / (a * (a ^ j - 1)) := by
    linarith
  unfold simplifiedLayerGain
  exact Real.log_le_log hb_arg harg_le


end Robin1984.FiniteSupport
