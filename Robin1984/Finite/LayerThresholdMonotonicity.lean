import Robin1984.Finite.CutoffIndex

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Active-set/KKT algebra for CA threshold profiles

The CA threshold prefix is the finite active set for the reduced-weight
objective

```text
  sum_e (gain(e) - lambda * cost(e)).
```

This file keeps that variational interpretation definitional and proves the
finite optimizer/complementary-slackness facts without adding any analytic
assumption.
-/

namespace Robin1984.FiniteSupport

noncomputable section


/-- Positivity of the fixed-layer gain. -/
theorem simplifiedLayerGain_pos
    {q : Real} {j : Nat} (hq : 1 < q) (hj : 0 < j) :
    0 < simplifiedLayerGain q j := by
  unfold simplifiedLayerGain
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hnum : 0 < q - 1 := by linarith
  have hpow : 0 < q ^ j - 1 :=
    pow_sub_one_pos_of_one_lt_of_pos_nat hq hj
  have hden : 0 < q * (q ^ j - 1) := mul_pos hqpos hpow
  have hfrac : 0 < (q - 1) / (q * (q ^ j - 1)) := div_pos hnum hden
  exact Real.log_pos (by linarith)

/-- For a fixed layer index, the gain-per-log-cost threshold is antitone in
the base.  This is the formal reason each layer is a prime prefix once a
frontier base is known. -/
theorem simplifiedLayerThreshold_le_of_base_le
    {a b : Real} {j : Nat}
    (ha : 1 < a) (hab : a <= b) (hj : 0 < j) :
    simplifiedLayerGain b j / Real.log b <=
      simplifiedLayerGain a j / Real.log a := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hgain_le := simplifiedLayerGain_le_of_base_le
    (a := a) (b := b) (j := j) ha hab hj
  have hgain_b_nonneg : 0 <= simplifiedLayerGain b j :=
    le_of_lt (simplifiedLayerGain_pos hb hj)
  have hlog_a_pos : 0 < Real.log a := Real.log_pos ha
  have hlog_le : Real.log a <= Real.log b :=
    Real.log_le_log (lt_trans zero_lt_one ha) hab
  calc
    simplifiedLayerGain b j / Real.log b <=
        simplifiedLayerGain b j / Real.log a := by
          exact div_le_div_of_nonneg_left hgain_b_nonneg hlog_a_pos hlog_le
    _ <= simplifiedLayerGain a j / Real.log a := by
          exact div_le_div_of_nonneg_right hgain_le (le_of_lt hlog_a_pos)


end

end Robin1984.FiniteSupport
