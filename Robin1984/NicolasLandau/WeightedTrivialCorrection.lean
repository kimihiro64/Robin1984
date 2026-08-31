import Robin1984.NicolasLandau.WeightedPsiIntegral

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# The negative-even-zero correction in Robin's explicit formula

Each negative-even atom is shown integrable and the family is summable in
integrated norm. The module then interchanges the series and integral,
evaluates the kernel sum logarithmically, and identifies the exact elementary
correction term appearing in the weighted explicit formula.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set

def robinNegativeEvenAtom (n k : Nat) (t : Real) : Real :=
  robinRealWeight n t * (1 / t^2)^(k + 1) / (2 * ((k : Real) + 1))

theorem robinNegativeEvenAtom_bounds
    (n k : Nat) {t : Real} (ht : 2 <= t) :
    And (0 <= robinNegativeEvenAtom n k t)
      (robinNegativeEvenAtom n k t <= (1 / 4 : Real)^(k + 1) * robinRealWeight n t) := by
  have hWeight : 0 <= robinRealWeight n t := robinRealWeight_nonneg (by linarith)
  have hSquare : (4 : Real) <= t^2 := by nlinarith
  have hRatio : 1 / t^2 <= (1 / 4 : Real) :=
    one_div_le_one_div_of_le (by norm_num) hSquare
  have hRatioNonneg : 0 <= 1 / t^2 := by positivity
  have hk : 0 <= (k : Real) := Nat.cast_nonneg k
  have hDen : 1 <= 2 * ((k : Real) + 1) := by linarith
  have hPower : (1 / t^2)^(k + 1) <= (1 / 4 : Real)^(k + 1) := by
    gcongr
  refine And.intro ?_ ?_
  . unfold robinNegativeEvenAtom
    positivity
  . have hDiv : (1 / t^2)^(k + 1) / (2 * ((k : Real) + 1)) <= (1 / t^2)^(k + 1) := by
      have h := div_le_div_of_nonneg_left (pow_nonneg hRatioNonneg (k + 1))
        (by norm_num : (0 : Real) < 1) hDen
      simpa only [div_one] using h
    unfold robinNegativeEvenAtom
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left (hDiv.trans hPower) hWeight).trans_eq (mul_comm _ _)

theorem integrableOn_robinNegativeEvenAtom
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) (k : Nat) :
    IntegrableOn (robinNegativeEvenAtom n k) (Ioi x) := by
  have hxOne : 1 < x := by linarith
  have hMeas : Measurable (robinNegativeEvenAtom n k) := by
    unfold robinNegativeEvenAtom robinRealWeight
    fun_prop
  apply ((integrableOn_robinRealWeight hn hxOne).const_mul ((1 / 4 : Real)^(k + 1))).mono'
    hMeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hBounds := robinNegativeEvenAtom_bounds n k (le_trans hx (le_of_lt ht))
  rw [Real.norm_eq_abs, abs_of_nonneg hBounds.1]
  exact hBounds.2

theorem summable_integral_norm_robinNegativeEvenAtoms
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    Summable (fun k : Nat => integral (volume.restrict (Ioi x))
      (fun t : Real => norm (robinNegativeEvenAtom n k t : Complex))) := by
  have hxOne : 1 < x := by linarith
  have hWeight := integrableOn_robinRealWeight hn hxOne
  have hGeom : Summable (fun k : Nat => (1 / 4 : Real)^(k + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_norm_lt_one (by norm_num : norm (1 / 4 : Real) < 1)).mul_right (1 / 4)
  have hBound : forall k : Nat, integral (volume.restrict (Ioi x))
      (fun t : Real => norm (robinNegativeEvenAtom n k t : Complex)) <=
      (1 / 4 : Real)^(k + 1) * integral (volume.restrict (Ioi x)) (robinRealWeight n) := by
    intro k
    have hF : IntegrableOn (fun t : Real => (robinNegativeEvenAtom n k t : Complex)) (Ioi x) :=
      (integrableOn_robinNegativeEvenAtom hn hx k).ofReal
    calc
      integral (volume.restrict (Ioi x)) (fun t : Real => norm (robinNegativeEvenAtom n k t : Complex)) <=
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            (1 / 4 : Real)^(k + 1) * robinRealWeight n t) := by
        apply integral_mono_ae hF.norm (hWeight.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hBounds := robinNegativeEvenAtom_bounds n k (le_trans hx (le_of_lt ht))
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hBounds.1]
        exact hBounds.2
      _ = _ := integral_const_mul _ _
  exact Summable.of_nonneg_of_le
    (fun k => integral_nonneg (fun t => norm_nonneg (robinNegativeEvenAtom n k t : Complex)))
    hBound (hGeom.mul_right _)

theorem tsum_robinNegativeEvenAtoms
    (n : Nat) {t : Real} (ht : 2 <= t) :
    tsum (fun k : Nat => robinNegativeEvenAtom n k t) =
      -(robinRealWeight n t / 2) * Real.log (1 - 1 / t^2) := by
  have hSquare : (4 : Real) <= t^2 := by nlinarith
  have hRatio : 1 / t^2 <= (1 / 4 : Real) :=
    one_div_le_one_div_of_le (by norm_num) hSquare
  have hAbs : abs (1 / t^2) < (1 : Real) := by
    rw [abs_of_nonneg (by positivity : (0 : Real) <= 1 / t^2)]
    linarith
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hAbs).mul_left (robinRealWeight n t / 2)
  have hFunction : (fun k : Nat =>
      (robinRealWeight n t / 2) * ((1 / t^2)^(k + 1) / ((k : Real) + 1))) =
      (fun k : Nat => robinNegativeEvenAtom n k t) := by
    funext k
    unfold robinNegativeEvenAtom
    field_simp [ne_of_gt (show 0 < t by linarith)] <;> ring
  rw [hFunction] at h
  rw [h.tsum_eq]
  ring

theorem robinNegativeEvenAtom_eq_kernel_integrand
    (n k : Nat) {t : Real} (ht : 1 < t) :
    ((t : Complex) ^ (-(2 * ((k : Complex) + 1)) - (n : Complex) - 1) *
        (((n : Real) * Real.log t + 1) / (Real.log t)^2 : Real)) /
          (2 * ((k : Complex) + 1)) =
      (robinNegativeEvenAtom n k t : Complex) := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have hPower : t ^ (-(2 * ((k : Real) + 1)) - (n : Real) - 1) =
      t ^ (-(n : Real) - 1) * (1 / t^2)^(k + 1) := by
    rw [show -(2 * ((k : Real) + 1)) - (n : Real) - 1 =
        (-(n : Real) - 1) + (-2) * ((k : Real) + 1) by ring,
      Real.rpow_add htPos, Real.rpow_mul htPos.le]
    rw [show (k : Real) + 1 = ((k + 1 : Nat) : Real) by simp,
      Real.rpow_natCast, Real.rpow_neg htPos.le, Real.rpow_two]
    simp only [one_div]
  have hExponent : -(2 * ((k : Complex) + 1)) - (n : Complex) - 1 =
      ((-(2 * ((k : Real) + 1)) - (n : Real) - 1 : Real) : Complex) := by
    push_cast
    ring
  rw [hExponent, <- Complex.ofReal_cpow htPos.le, hPower]
  unfold robinNegativeEvenAtom robinRealWeight
  push_cast
  ring

theorem robinNegativeEvenKernel_eq_integral
    (n k : Nat) {x : Real} (hx : 1 < x) :
    robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1)) =
      integral (volume.restrict (Ioi x))
        (fun t : Real => (robinNegativeEvenAtom n k t : Complex)) := by
  unfold robinZeroKernel
  rw [<- integral_div]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  exact robinNegativeEvenAtom_eq_kernel_integrand n k (lt_trans hx ht)

theorem tsum_robinNegativeEvenKernels_eq_log_integral
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    tsum (fun k : Nat =>
        robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1))) =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        ((-(robinRealWeight n t / 2) * Real.log (1 - 1 / t^2) : Real) : Complex)) := by
  have hxOne : 1 < x := by linarith
  have hF : forall k : Nat, IntegrableOn
      (fun t : Real => (robinNegativeEvenAtom n k t : Complex)) (Ioi x) := by
    intro k
    exact (integrableOn_robinNegativeEvenAtom hn hx k).ofReal
  calc
    tsum (fun k : Nat =>
        robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1))) =
      tsum (fun k : Nat => integral (volume.restrict (Ioi x))
        (fun t : Real => (robinNegativeEvenAtom n k t : Complex))) := by
      apply tsum_congr
      intro k
      exact robinNegativeEvenKernel_eq_integral n k hxOne
    _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
        tsum (fun k : Nat => (robinNegativeEvenAtom n k t : Complex))) :=
      integral_tsum_of_summable_integral_norm hF (summable_integral_norm_robinNegativeEvenAtoms hn hx)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [<- Complex.ofReal_tsum, tsum_robinNegativeEvenAtoms n (le_trans hx (le_of_lt ht))]

/-- The constant and complete negative-even series are precisely the
correction already bounded in Robin's Lemma 2. -/
theorem robin_explicit_correction_eq
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    -(Real.log (2 * Real.pi) : Complex) * robinCutoffMellinTest n x 1 +
        tsum (fun k : Nat =>
          robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1))) =
      -(robinTrivialZeroCorrection n x : Complex) := by
  have hxOne : 1 < x := by linarith
  have hWeight := integrableOn_robinRealWeight hn hxOne
  have hCorr := integrableOn_robinTrivialZeroCorrection_integrand hn hx
  have hOne : robinCutoffMellinTest n x 1 =
      ((integral (volume.restrict (Ioi x)) (robinRealWeight n) : Real) : Complex) := by
    simp only [robinCutoffMellinTest, if_pos hxOne.le]
    exact (complex_integral_robinRealWeight hn hxOne).symm
  have hFunction : (fun t : Real =>
      -(robinRealWeight n t / 2) * Real.log (1 - 1 / t^2)) =
      (fun t : Real => Real.log (2 * Real.pi) * robinRealWeight n t -
        robinRealWeight n t * robinTrivialZeroCorrectionFactor t) := by
    funext t
    unfold robinTrivialZeroCorrectionFactor
    ring
  rw [tsum_robinNegativeEvenKernels_eq_log_integral hn hx,
    integral_complex_ofReal, hFunction]
  have hSub := integral_sub (hWeight.const_mul (Real.log (2 * Real.pi))) hCorr
  rw [hSub, integral_const_mul, hOne]
  change -(Real.log (2 * Real.pi) : Complex) *
      ((integral (volume.restrict (Ioi x)) (robinRealWeight n) : Real) : Complex) +
      ((Real.log (2 * Real.pi) * integral (volume.restrict (Ioi x)) (robinRealWeight n) -
        robinTrivialZeroCorrection n x : Real) : Complex) = _
  push_cast
  ring

end

end Robin1984
