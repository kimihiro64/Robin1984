import Robin1984.Arithmetic.Definitions
import Robin1984.Arithmetic.RobinBounds
import Robin1984.Helpers.Event
import Robin1984.Helpers.Lyapunov
/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: Leonidas Alaoglu and Paul Erdos (1944), with Guy Robin's 1984 use of colossally abundant numbers.
- Formalization note: The CA objective and threshold characterization are published mathematics; the event representation and Lean interfaces are specific to this formalization.
- PROVENANCE-END
-/

/-!
# Colossally abundant threshold profiles

A colossally abundant factorization packet satisfies complementary slackness
for the marginal-event objective.  The resulting event packet is exactly the
canonical threshold prefix, and its logarithmic mass and gain recover
`log n` and `log (sigma(n) / n)`.
-/

namespace Robin1984
/-- Reduced marginal weight for the CA Lagrangian at cutoff `lambda`. -/
noncomputable def eventReducedWeight (lambda : Real) (e : Event) : Real :=
  e.gain - lambda * Real.log (e.p : Real)

/-- Reduced weight is threshold gap times prime log. -/
theorem eventReducedWeight_eq_threshold_sub_mul
    (lambda : Real) (e : Event) :
    eventReducedWeight lambda e =
      (e.threshold - lambda) * Real.log (e.p : Real) := by
  unfold eventReducedWeight
  rw [← e.threshold_mul_log]
  ring

/-- Nonnegative reduced weight is the same as lying above the threshold. -/
theorem eventReducedWeight_nonneg_iff_threshold
    (lambda : Real) (e : Event) :
    0 <= eventReducedWeight lambda e <-> lambda <= e.threshold := by
  unfold eventReducedWeight
  constructor
  · intro h
    have hmul : lambda * Real.log (e.p : Real) <=
        e.threshold * Real.log (e.p : Real) := by
      rw [e.threshold_mul_log]
      linarith
    have hmulLeft :
        Real.log (e.p : Real) * lambda <=
          Real.log (e.p : Real) * e.threshold := by
      simpa [mul_comm] using hmul
    exact (mul_le_mul_iff_right₀ e.log_prime_pos).mp hmulLeft
  · intro h
    have hmulLeft :
        Real.log (e.p : Real) * lambda <=
          Real.log (e.p : Real) * e.threshold :=
      (mul_le_mul_iff_right₀ e.log_prime_pos).mpr h
    have hmul : lambda * Real.log (e.p : Real) <=
        e.threshold * Real.log (e.p : Real) := by
      simpa [mul_comm] using hmulLeft
    rw [e.threshold_mul_log] at hmul
    linarith


/-- Nonpositive reduced weight is the same as lying at or below the cutoff. -/
theorem eventReducedWeight_nonpos_iff_threshold
    (lambda : Real) (e : Event) :
    eventReducedWeight lambda e <= 0 <-> e.threshold <= lambda := by
  rw [eventReducedWeight_eq_threshold_sub_mul]
  constructor
  · intro h
    have hgap :
        e.threshold - lambda <= 0 := by
      have hmul :
          (e.threshold - lambda) * Real.log (e.p : Real) <=
            0 * Real.log (e.p : Real) := by
        simpa using h
      exact (mul_le_mul_iff_right₀ e.log_prime_pos).mp
        (by simpa [mul_comm] using hmul)
    linarith
  · intro h
    have hgap : e.threshold - lambda <= 0 := by linarith
    have hmul :
        (e.threshold - lambda) * Real.log (e.p : Real) <=
          0 * Real.log (e.p : Real) :=
      by
        simpa [mul_comm] using
          ((mul_le_mul_iff_right₀ e.log_prime_pos).mpr hgap)
    simpa using hmul


/-- A zero-threshold tie has zero reduced weight. -/
theorem eventReducedWeight_eq_zero_of_threshold_eq
    {lambda : Real} {e : Event} (hTie : e.threshold = lambda) :
    eventReducedWeight lambda e = 0 := by
  rw [eventReducedWeight_eq_threshold_sub_mul, hTie]
  ring


/-- Total reduced Lagrange weight of a finite event packet. -/
noncomputable def eventPacketReducedWeight
    (lambda : Real) (events : Finset Event) : Real :=
  ∑ e ∈ events, eventReducedWeight lambda e

/-- Packet reduced weight is total gain minus the cutoff times total
logarithmic prime mass. -/
theorem eventPacketReducedWeight_eq_eventGainSum_sub
    (lambda : Real) (events : Finset Event) :
    eventPacketReducedWeight lambda events =
      eventGainSum events - lambda * eventLogMass events := by
  unfold eventPacketReducedWeight eventReducedWeight eventGainSum eventLogMass
  rw [Finset.sum_sub_distrib]
  rw [Finset.mul_sum]


/-- The multiplicative gain ratio for a single prime-power layer. -/
noncomputable def eventGainRatio (q : Real) (j : Nat) : Real :=
  (1 - q ^ (j + 1)) / (1 - q ^ j)

/-- The gain ratio is positive for `0 < q < 1` and positive layers. -/
theorem eventGainRatio_pos
    {q : Real} (hq0 : 0 < q) (hq1 : q < 1)
    {j : Nat} (hj : 0 < j) :
    0 < eventGainRatio q j := by
  unfold eventGainRatio
  have hq0le : 0 <= q := le_of_lt hq0
  have hjne : j ≠ 0 := Nat.ne_of_gt hj
  have hj1ne : j + 1 ≠ 0 := Nat.succ_ne_zero j
  have hpowj_lt : q ^ j < 1 :=
    (pow_lt_one_iff_of_nonneg hq0le hjne).mpr hq1
  have hpowj1_lt : q ^ (j + 1) < 1 :=
    (pow_lt_one_iff_of_nonneg hq0le hj1ne).mpr hq1
  exact div_pos (by linarith) (by linarith)


/-- One-step decrease of the prime-power gain ratio. -/
theorem eventGainRatio_step_le
    {q : Real} (hq0 : 0 < q) (hq1 : q < 1)
    {j : Nat} (hj : 0 < j) :
    eventGainRatio q (j + 1) <= eventGainRatio q j := by
  unfold eventGainRatio
  have hq0le : 0 <= q := le_of_lt hq0
  have hjne : j ≠ 0 := Nat.ne_of_gt hj
  have hj1ne : j + 1 ≠ 0 := Nat.succ_ne_zero j
  have hpowj_lt : q ^ j < 1 :=
    (pow_lt_one_iff_of_nonneg hq0le hjne).mpr hq1
  have hpowj1_lt : q ^ (j + 1) < 1 :=
    (pow_lt_one_iff_of_nonneg hq0le hj1ne).mpr hq1
  have hdenj : 0 < 1 - q ^ j := by linarith
  have hdenj1 : 0 < 1 - q ^ (j + 1) := by linarith
  have hsq : 0 <= q ^ j * (1 - q) ^ 2 :=
    mul_nonneg (pow_nonneg hq0le j) (sq_nonneg (1 - q))
  field_simp [hdenj.ne', hdenj1.ne']
  ring_nf
  nlinarith [hsq]

/-- The prime-power gain ratio decreases along same-prime layers. -/
theorem eventGainRatio_le_of_le
    {q : Real} (hq0 : 0 < q) (hq1 : q < 1)
    {j k : Nat} (hj : 0 < j) (hjk : j <= k) :
    eventGainRatio q k <= eventGainRatio q j := by
  induction hjk with
  | refl => exact le_rfl
  | step hm ih =>
      have hmpos : 0 < _ := lt_of_lt_of_le hj hm
      exact le_trans (eventGainRatio_step_le hq0 hq1 hmpos) ih

/-- Event gain is the logarithm of its prime-power gain ratio. -/
theorem event_gain_eq_log_eventGainRatio (e : Event) :
    e.gain = Real.log (eventGainRatio ((e.p : Real)⁻¹) e.j) := by
  unfold Event.gain eventGainRatio
  have hExp1 :
      -((e.j : Int) + 1) = -(((e.j + 1 : Nat) : Int)) := by
    omega
  have hExp0 : -((e.j : Int)) = -(((e.j : Nat) : Int)) := rfl
  rw [hExp1, hExp0]
  rw [zpow_neg, zpow_natCast, inv_pow]
  rw [zpow_neg, zpow_natCast, inv_pow]


/-- For a fixed prime, event gains decrease as the exponent layer increases. -/
theorem event_gain_antitone_same_prime
    {e f : Event} (hSame : e.p = f.p) (hLayer : e.j <= f.j) :
    f.gain <= e.gain := by
  let q : Real := (e.p : Real)⁻¹
  have hq0 : 0 < q := by
    dsimp [q]
    exact inv_pos.mpr e.prime_pos
  have hpgt : (1 : Real) < (e.p : Real) := by
    exact_mod_cast e.hp.one_lt
  have hq1 : q < 1 := by
    dsimp [q]
    exact inv_lt_one_of_one_lt₀ hpgt
  have hle : eventGainRatio q f.j <= eventGainRatio q e.j :=
    eventGainRatio_le_of_le hq0 hq1 e.hj hLayer
  have hpos : 0 < eventGainRatio q f.j :=
    eventGainRatio_pos hq0 hq1 f.hj
  rw [event_gain_eq_log_eventGainRatio e,
    event_gain_eq_log_eventGainRatio f]
  change
    Real.log (eventGainRatio ((f.p : Real)⁻¹) f.j) <=
      Real.log (eventGainRatio q e.j)
  rw [← hSame]
  exact Real.log_le_log hpos hle

/-- For a fixed prime, event thresholds decrease as the exponent layer
increases. -/
theorem event_threshold_antitone_same_prime
    {e f : Event} (hSame : e.p = f.p) (hLayer : e.j <= f.j) :
    f.threshold <= e.threshold := by
  unfold Event.threshold
  have hgain := event_gain_antitone_same_prime hSame hLayer
  have hlogpos : 0 < Real.log (e.p : Real) := e.log_prime_pos
  have hlogeq : Real.log (f.p : Real) = Real.log (e.p : Real) := by
    rw [← hSame]
  rw [hlogeq]
  exact (div_le_div_iff_of_pos_right hlogpos).mpr hgain


end Robin1984
namespace Robin1984

/-- Textbook colossally-abundant objective at parameter `eps`. -/
noncomputable def caObjective (eps : Real) (n : Nat) : Real :=
  (Robin1984.Core.sigmaOneNat n : Real) /
    ((n : Real) ^ (1 + eps))

/-- Logarithmic form of the fixed-parameter CA objective. -/
noncomputable def caLogObjective (eps : Real) (n : Nat) : Real :=
  Real.log (caObjective eps n)

/--
Classical colossally-abundant condition with a fixed parameter `eps`:
`n` maximizes `sigma(k) / k^(1+eps)` among integers above `1`.
-/
noncomputable def IsColossallyAbundantWith (n : Nat) (eps : Real) : Prop :=
  0 < eps ∧ 1 < n ∧
    ∀ k : Nat, 1 < k -> caObjective eps k <= caObjective eps n

theorem IsColossallyAbundantWith.eps_pos
    {n : Nat} {eps : Real} (h : IsColossallyAbundantWith n eps) :
    0 < eps := h.1

theorem IsColossallyAbundantWith.one_lt
    {n : Nat} {eps : Real} (h : IsColossallyAbundantWith n eps) :
    1 < n := h.2.1

theorem IsColossallyAbundantWith.objective_max
    {n : Nat} {eps : Real} (h : IsColossallyAbundantWith n eps)
    {k : Nat} (hk : 1 < k) :
    caObjective eps k <= caObjective eps n := h.2.2 k hk

/-- A concrete tail bound below the value at `2` produces a textbook
colossally-abundant maximizer at parameter `eps`.  This is the finite-maximum
extraction step behind CA existence; the analytic work is exactly the tail
bound hypothesis. -/
theorem exists_colossallyAbundantWith_of_tail_le_two
    {eps : Real} (heps : 0 < eps) {B : Nat} (hB : 2 <= B)
    (hTail :
      ∀ k : Nat, B < k -> caObjective eps k <= caObjective eps 2) :
    ∃ m : Nat, IsColossallyAbundantWith m eps := by
  classical
  let candidates : Finset Nat :=
    (Finset.range (B + 1)).filter (fun k => 1 < k)
  have h2Candidates : 2 ∈ candidates := by
    unfold candidates
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hB), by norm_num⟩
  have hCandidatesNonempty : candidates.Nonempty := ⟨2, h2Candidates⟩
  rcases Finset.exists_max_image candidates (fun k => caObjective eps k)
      hCandidatesNonempty with
    ⟨m, hmCandidates, hmMax⟩
  have hmOne : 1 < m := (Finset.mem_filter.mp hmCandidates).2
  refine ⟨m, heps, hmOne, ?_⟩
  intro k hk
  by_cases hkB : k <= B
  · have hkCandidates : k ∈ candidates := by
      unfold candidates
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hkB), hk⟩
    exact hmMax k hkCandidates
  · have hTailK : caObjective eps k <= caObjective eps 2 :=
      hTail k (Nat.lt_of_not_ge hkB)
    have hTwoLeM : caObjective eps 2 <= caObjective eps m :=
      hmMax 2 h2Candidates
    exact le_trans hTailK hTwoLeM

/-- An eventual tail bound below the value at `2` is enough to produce a
textbook CA maximizer. -/
theorem exists_colossallyAbundantWith_of_eventual_tail_le_two
    {eps : Real} (heps : 0 < eps)
    (hTail :
      ∃ B : Nat, ∀ k : Nat, B < k -> caObjective eps k <= caObjective eps 2) :
    ∃ m : Nat, IsColossallyAbundantWith m eps := by
  rcases hTail with ⟨B, hTailB⟩
  exact exists_colossallyAbundantWith_of_tail_le_two heps
    (B := max 2 B) (le_max_left 2 B)
    (fun k hk => hTailB k (lt_of_le_of_lt (le_max_right 2 B) hk))

/-- The fixed-parameter CA objective is positive on positive integers. -/
theorem caObjective_pos {eps : Real} {n : Nat} (hn : 0 < n) :
    0 < caObjective eps n := by
  unfold caObjective
  exact div_pos
    (by exact_mod_cast sigmaOneNat_pos hn)
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) (1 + eps))

/-- If the fixed-parameter CA objective tends to zero, then a textbook CA
maximizer exists.  Thus the remaining analytic existence input can be stated
as ordinary tail decay of `sigma(k) / k^(1+eps)`. -/
theorem exists_colossallyAbundantWith_of_tendsto_caObjective_zero
    {eps : Real} (heps : 0 < eps)
    (hTendsto :
      Filter.Tendsto (fun k : Nat => caObjective eps k) Filter.atTop
        (nhds 0)) :
    ∃ m : Nat, IsColossallyAbundantWith m eps := by
  have hTwoPos : 0 < caObjective eps 2 :=
    caObjective_pos (eps := eps) (n := 2) (by norm_num)
  have hEventuallyLt :
      ∀ᶠ k : Nat in Filter.atTop, caObjective eps k < caObjective eps 2 :=
    hTendsto.eventually (eventually_lt_nhds hTwoPos)
  rcases Filter.eventually_atTop.mp hEventuallyLt with ⟨B, hB⟩
  exact exists_colossallyAbundantWith_of_eventual_tail_le_two heps
    ⟨B, fun k hk => le_of_lt (hB k (le_of_lt hk))⟩

/-- The CA objective is the abundancy ratio with the Lagrange denominator
separated. -/
theorem caObjective_eq_abundancy_div_rpow
    {eps : Real} {n : Nat} (hn : 0 < n) :
    caObjective eps n = abundancy n / ((n : Real) ^ eps) := by
  unfold caObjective abundancy
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hpow : 0 < (n : Real) ^ eps := Real.rpow_pos_of_pos hnR eps
  rw [show (1 + eps) = (1 : Real) + eps by ring]
  rw [Real.rpow_add hnR, Real.rpow_one]
  field_simp [hnR.ne', hpow.ne']


/-- Logarithmic CA objective split into abundancy and size terms. -/
theorem caLogObjective_eq_log_abundancy_sub
    {eps : Real} {n : Nat} (hn : 0 < n) :
    caLogObjective eps n =
      Real.log (abundancy n) - eps * Real.log (n : Real) := by
  unfold caLogObjective
  rw [caObjective_eq_abundancy_div_rpow (eps := eps) hn]
  have hab : 0 < abundancy n := abundancy_pos hn
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hpow : 0 < (n : Real) ^ eps := Real.rpow_pos_of_pos hnR eps
  rw [Real.log_div hab.ne' hpow.ne']
  rw [Real.log_rpow hnR]


/-- The abundancy ratio is bounded by the harmonic sum over `1, ..., n`:
`sigma(n) / n = sum_{d|n} 1/d <= H_n`. -/
theorem abundancy_le_harmonic {n : Nat} (hn : 0 < n) :
    abundancy n <= (harmonic n : Real) := by
  unfold abundancy Robin1984.Core.sigmaOneNat
  rw [ArithmeticFunction.sigma_eq_sum_div]
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  calc
    ((∑ d ∈ n.divisors, (n / d) ^ 1 : Nat) : Real) / (n : Real)
        = (∑ d ∈ n.divisors, ((n / d : Nat) : Real)) / (n : Real) := by
      simp
    _ = ∑ d ∈ n.divisors, (((n / d : Nat) : Real) / (n : Real)) := by
      rw [Finset.sum_div]
    _ = ∑ d ∈ n.divisors, ((d : Real)⁻¹) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hdR : (d : Real) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
      have hmulNat : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      have hmulReal :
          (d : Real) * ((n / d : Nat) : Real) = (n : Real) := by
        exact_mod_cast hmulNat
      field_simp [hdR, ne_of_gt hnR]
      nlinarith
    _ ≤ ∑ d ∈ Finset.Icc 1 n, ((d : Real)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr
          ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
      · intro d _hdIcc _hdNot
        exact inv_nonneg.mpr (by positivity)
    _ = (harmonic n : Real) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- Elementary Robin-side growth bound: `sigma(n)/n <= 1 + log n`. -/
theorem abundancy_le_one_add_log {n : Nat} (hn : 0 < n) :
    abundancy n <= 1 + Real.log (n : Real) :=
  (abundancy_le_harmonic hn).trans (harmonic_le_one_add_log n)

/-- The constant part of `(1 + log n) / n^eps` tends to zero. -/
theorem tendsto_nat_one_div_rpow_atTop_zero
    {eps : Real} (heps : 0 < eps) :
    Filter.Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) ^ eps))
      Filter.atTop (nhds 0) := by
  have hpow :
      Filter.Tendsto (fun x : Real => x ^ (-eps))
        Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop heps
  have hnat :
      Filter.Tendsto (fun n : Nat => (n : Real) ^ (-eps))
        Filter.atTop (nhds 0) :=
    hpow.comp tendsto_natCast_atTop_atTop
  refine hnat.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : Nat)] with n hn
  have hnR : 0 <= (n : Real) := by positivity
  rw [Real.rpow_neg hnR eps]
  simp [one_div]

/-- The logarithmic part of `(1 + log n) / n^eps` tends to zero. -/
theorem tendsto_nat_log_div_rpow_atTop_zero
    {eps : Real} (heps : 0 < eps) :
    Filter.Tendsto
      (fun n : Nat => Real.log (n : Real) / ((n : Real) ^ eps))
      Filter.atTop (nhds 0) := by
  exact ((isLittleO_log_rpow_atTop heps).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop

/-- The elementary divisor-sum majorant decays after division by `n^eps`. -/
theorem tendsto_nat_one_add_log_div_rpow_atTop_zero
    {eps : Real} (heps : 0 < eps) :
    Filter.Tendsto
      (fun n : Nat =>
        (1 + Real.log (n : Real)) / ((n : Real) ^ eps))
      Filter.atTop (nhds 0) := by
  have hone := tendsto_nat_one_div_rpow_atTop_zero (eps := eps) heps
  have hlog := tendsto_nat_log_div_rpow_atTop_zero (eps := eps) heps
  have hsum := hone.add hlog
  have hsum0 :
      Filter.Tendsto
        (fun n : Nat =>
          (1 : Real) / ((n : Real) ^ eps) +
            Real.log (n : Real) / ((n : Real) ^ eps))
        Filter.atTop (nhds 0) := by
    simpa using hsum
  refine hsum0.congr' ?_
  filter_upwards with n
  ring

/-- Pointwise CA-objective upper bound by the elementary harmonic majorant. -/
theorem caObjective_le_one_add_log_div_rpow
    {eps : Real} {n : Nat} (hn : 0 < n) :
    caObjective eps n <=
      (1 + Real.log (n : Real)) / ((n : Real) ^ eps) := by
  rw [caObjective_eq_abundancy_div_rpow (eps := eps) hn]
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hden : 0 <= (((n : Real) ^ eps)⁻¹) :=
    inv_nonneg.mpr (le_of_lt (Real.rpow_pos_of_pos hnR eps))
  simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right (abundancy_le_one_add_log hn) hden

/-- For every positive CA parameter, the textbook objective tends to zero. -/
theorem tendsto_caObjective_zero
    {eps : Real} (heps : 0 < eps) :
    Filter.Tendsto (fun n : Nat => caObjective eps n)
      Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (tendsto_nat_one_add_log_div_rpow_atTop_zero (eps := eps) heps)
    ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (0 : Nat)] with n hn
    exact le_of_lt (caObjective_pos (eps := eps) hn)
  · filter_upwards [Filter.eventually_gt_atTop (0 : Nat)] with n hn
    exact caObjective_le_one_add_log_div_rpow (eps := eps) hn

/-- Textbook colossally-abundant maximizers exist for every positive
parameter, using only the elementary divisor-sum tail bound. -/
theorem exists_colossallyAbundantWith
    {eps : Real} (heps : 0 < eps) :
    ∃ m : Nat, IsColossallyAbundantWith m eps :=
  exists_colossallyAbundantWith_of_tendsto_caObjective_zero heps
    (tendsto_caObjective_zero heps)

/-- Closed form for the divisor sum of a prime power, as a real identity. -/
theorem sigma_one_prime_pow_real_closed {p a : Nat} (hp : Nat.Prime p) :
    ((Robin1984.Core.sigmaOneNat (p ^ a) : Nat) : Real) =
      (((p : Real) ^ (a + 1) - 1) / ((p : Real) - 1)) := by
  unfold Robin1984.Core.sigmaOneNat
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  norm_num
  have hpne : (p : Real) ≠ 1 := by exact_mod_cast hp.ne_one
  rw [geom_sum_eq (x := (p : Real)) hpne (a + 1)]

/-- Event gain ratio after replacing the event parameter by the prime itself. -/
theorem eventGainRatio_inv_eq {p : Real} (hp0 : p ≠ 0)
    {k : Nat} (hden : p ^ (k + 1) - 1 ≠ 0) :
    Robin1984.eventGainRatio p⁻¹ (k + 1) =
      (p ^ (k + 2) - 1) / (p * (p ^ (k + 1) - 1)) := by
  unfold Robin1984.eventGainRatio
  rw [inv_pow, inv_pow]
  field_simp [hp0, hden]
  ring

/-- Adjacent prime-power abundancy ratios are exactly event gain ratios. -/
theorem primePowAbundancyRatio_succ_eq_eventGainRatio {p k : Nat}
    (hp : Nat.Prime p) :
    (((Robin1984.Core.sigmaOneNat (p ^ (k + 1)) : Real) /
          ((p : Real) ^ (k + 1))) /
        ((Robin1984.Core.sigmaOneNat (p ^ k) : Real) /
          ((p : Real) ^ k))) =
      Robin1984.eventGainRatio ((p : Real)⁻¹) (k + 1) := by
  have hpRpos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpRone : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hpRne0 : (p : Real) ≠ 0 := ne_of_gt hpRpos
  have hpRne1 : (p : Real) ≠ 1 := by exact_mod_cast hp.ne_one
  have hdenSig : (p : Real) ^ (k + 1) - 1 ≠ 0 := by
    have hpowgt : 1 < (p : Real) ^ (k + 1) := by
      induction k with
      | zero =>
          simpa using hpRone
      | succ k ih =>
          rw [pow_succ]
          have hpowpos : 0 < (p : Real) ^ (k + 1) :=
            pow_pos hpRpos (k + 1)
          nlinarith [ih, hpRone, hpowpos]
    exact ne_of_gt (by linarith)
  have hsig1 := sigma_one_prime_pow_real_closed (p := p) (a := k + 1) hp
  have hsig0 := sigma_one_prime_pow_real_closed (p := p) (a := k) hp
  rw [eventGainRatio_inv_eq hpRne0 hdenSig]
  rw [hsig1, hsig0]
  field_simp [hpRne0, hpRne1, hdenSig]
  ring

/-- The divisor sum factors across a prime-power part and its p-adic
complement. -/
theorem sigmaOneNat_mul_primePow_ordCompl {n p : Nat}
    (hp : Nat.Prime p) (hn : n ≠ 0) :
    Robin1984.Core.sigmaOneNat n =
      Robin1984.Core.sigmaOneNat (p ^ n.factorization p) *
        Robin1984.Core.sigmaOneNat
          (n / p ^ n.factorization p) := by
  have hcop :
      (p ^ n.factorization p).Coprime
        (n / p ^ n.factorization p) :=
    Nat.Coprime.pow_left (n.factorization p) (Nat.coprime_ordCompl hp hn)
  have hmul :=
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
      hcop
  unfold Robin1984.Core.sigmaOneNat
  conv_lhs =>
    rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  exact hmul

/-- The abundancy ratio factors across a prime-power part and its p-adic
complement. -/
theorem abundancy_eq_primePow_mul_ordCompl {n p : Nat}
    (hp : Nat.Prime p) (hn : n ≠ 0) :
    abundancy n =
      ((Robin1984.Core.sigmaOneNat (p ^ n.factorization p) : Real) /
        ((p : Real) ^ n.factorization p)) *
      abundancy (n / p ^ n.factorization p) := by
  have hcompPosNat : 0 < n / p ^ n.factorization p := Nat.ordCompl_pos p hn
  have hpRpos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpPowRealPos : 0 < (p : Real) ^ n.factorization p :=
    pow_pos hpRpos _
  have hcompPos : (0 : Real) <
      (n / p ^ n.factorization p : Nat) := by
    exact_mod_cast hcompPosNat
  have hsig := sigmaOneNat_mul_primePow_ordCompl hp hn
  have hnCast :
      (n : Real) =
        ((p ^ n.factorization p : Nat) : Real) *
          ((n / p ^ n.factorization p : Nat) : Real) := by
    exact_mod_cast (Eq.symm (Nat.ordProj_mul_ordCompl_eq_self n p))
  unfold abundancy
  rw [hsig, hnCast]
  norm_num
  field_simp [hpPowRealPos.ne', hcompPos.ne']

/-- Multiplying by a prime increments that prime's factorization exponent. -/
theorem factorization_mul_prime_self {n p : Nat}
    (hp : Nat.Prime p) (hn : n ≠ 0) :
    (n * p).factorization p = n.factorization p + 1 := by
  have hmul := Nat.factorization_mul hn hp.ne_zero
  have happly := congrArg (fun f => f p) hmul
  simpa [Finsupp.add_apply, hp.factorization_self] using happly


/-- The p-adic complement is unchanged when multiplying by one more `p`. -/
theorem ordCompl_mul_prime_eq {n p : Nat}
    (hp : Nat.Prime p) (hn : n ≠ 0) :
    (n * p) / p ^ ((n * p).factorization p) =
      n / p ^ n.factorization p := by
  let a := n.factorization p
  let m := n / p ^ a
  have hfac : (n * p).factorization p = a + 1 := by
    simpa [a] using factorization_mul_prime_self hp hn
  have hrepr : p ^ a * m = n := by
    simpa [a, m] using Nat.ordProj_mul_ordCompl_eq_self n p
  have hnum : n * p = p ^ (a + 1) * m := by
    rw [← hrepr]
    rw [pow_succ]
    ring
  rw [hfac, hnum]
  exact Nat.mul_div_right m (Nat.pow_pos (a := p) (n := a + 1) hp.pos)


/-- Multiplying by one more `p` changes abundancy by the first missing event
gain ratio. -/
theorem abundancy_mul_prime_ratio_eq_eventGainRatio {n p : Nat}
    (hp : Nat.Prime p) (hn : n ≠ 0) :
    abundancy (n * p) / abundancy n =
      Robin1984.eventGainRatio ((p : Real)⁻¹) (n.factorization p + 1) := by
  have hmul :=
    abundancy_eq_primePow_mul_ordCompl hp (Nat.mul_ne_zero hn hp.ne_zero)
  have hbase := abundancy_eq_primePow_mul_ordCompl hp hn
  have hfac := factorization_mul_prime_self hp hn
  have hcompl := ordCompl_mul_prime_eq hp hn
  rw [hmul, hbase, hcompl, hfac]
  have hCpos : 0 < abundancy (n / p ^ n.factorization p) :=
    abundancy_pos (Nat.ordCompl_pos p hn)
  have hApos : 0 <
      ((Robin1984.Core.sigmaOneNat (p ^ n.factorization p) : Real) /
        ((p : Real) ^ n.factorization p)) := by
    exact div_pos
      (by
        exact_mod_cast
          sigmaOneNat_pos
            (Nat.pow_pos (a := p) (n := n.factorization p) hp.pos))
      (pow_pos (by exact_mod_cast hp.pos : (0 : Real) < p) _)
  have hratio :=
    primePowAbundancyRatio_succ_eq_eventGainRatio
      (p := p) (k := n.factorization p) hp
  rw [← hratio]
  field_simp [hCpos.ne', hApos.ne']


/-- Log variation for adding the first missing exponent of a prime. -/
theorem eventReducedWeight_add_first_eq_logVariation
    {n : Nat} {eps : Real} {first : Robin1984.Event}
    (hn : 0 < n)
    (hfirst : first.j = n.factorization first.p + 1) :
    Robin1984.eventReducedWeight eps first =
      caLogObjective eps (n * first.p) - caLogObjective eps n := by
  have hnNe : n ≠ 0 := Nat.ne_of_gt hn
  have hpRpos : (0 : Real) < first.p := first.prime_pos
  have hnRpos : (0 : Real) < n := by exact_mod_cast hn
  have hnpPos : 0 < n * first.p := Nat.mul_pos hn first.hp.pos
  have hratio :=
    abundancy_mul_prime_ratio_eq_eventGainRatio first.hp hnNe
  have hlogAb :
      Real.log (abundancy (n * first.p)) - Real.log (abundancy n) =
        Real.log
          (Robin1984.eventGainRatio ((first.p : Real)⁻¹)
            (n.factorization first.p + 1)) := by
    have hdiv :=
      Real.log_div
        (ne_of_gt (abundancy_pos hnpPos))
        (ne_of_gt (abundancy_pos hn))
    rw [hratio] at hdiv
    linarith
  have hlogN :
      Real.log ((n * first.p : Nat) : Real) - Real.log (n : Real) =
        Real.log (first.p : Real) := by
    have hmul : Real.log ((n * first.p : Nat) : Real) =
        Real.log (n : Real) + Real.log (first.p : Real) := by
      rw [Nat.cast_mul]
      exact Real.log_mul (ne_of_gt hnRpos) (ne_of_gt hpRpos)
    linarith
  rw [caLogObjective_eq_log_abundancy_sub (eps := eps) hnpPos,
    caLogObjective_eq_log_abundancy_sub (eps := eps) hn]
  unfold Robin1984.eventReducedWeight
  rw [Robin1984.event_gain_eq_log_eventGainRatio first, hfirst]
  rw [show
      Real.log (abundancy (n * first.p)) -
          eps * Real.log ((n * first.p : Nat) : Real) -
        (Real.log (abundancy n) - eps * Real.log (n : Real)) =
        (Real.log (abundancy (n * first.p)) - Real.log (abundancy n)) -
          eps *
            (Real.log ((n * first.p : Nat) : Real) -
              Real.log (n : Real)) by
    ring]
  rw [hlogAb, hlogN]


/-- Textbook CA maximality transferred to the logarithmic objective. -/
theorem IsColossallyAbundantWith.logObjective_max
    {n : Nat} {eps : Real} (h : IsColossallyAbundantWith n eps)
    {k : Nat} (hk : 1 < k) :
    caLogObjective eps k <= caLogObjective eps n := by
  unfold caLogObjective
  exact Real.log_le_log
    (caObjective_pos (Nat.zero_lt_of_lt hk))
    (h.objective_max hk)

/-- The marginal prime-power events present in the factorization of `n`. -/
noncomputable def actualExponentEvents (n : Nat) : Finset Event := by
  classical
  exact (primesUpToSet n).attach.biUnion fun p =>
    ((Finset.range (n.factorization p.val + 1)).filter (fun j => 0 < j)).attach.image
      (fun j => {
        p := p.val
        j := j.val
        hp := (Finset.mem_filter.mp p.property).2
        hj := (Finset.mem_filter.mp j.property).2
      })

/-- The event state associated with the prime factorization of `n`. -/
noncomputable def actualExponentState (n : Nat) : CAState :=
  applyPacket zeroCAState (actualExponentEvents n)


/-- Membership in the actual exponent packet is exactly bounded by the
factorization exponent of the event's prime base. -/
theorem mem_actualExponentEvents_iff
    {n : Nat} (hn : n ≠ 0) {e : Robin1984.Event} :
    e ∈ actualExponentEvents n ↔ e.j <= n.factorization e.p := by
  classical
  constructor
  · intro he
    unfold actualExponentEvents at he
    rcases Finset.mem_biUnion.mp he with ⟨p, _hpMem, heImage⟩
    rcases Finset.mem_image.mp heImage with ⟨j, _hjMem, hje⟩
    rw [← hje]
    exact Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp j.property).1)
  · intro hle
    unfold actualExponentEvents
    have hfacpos : n.factorization e.p ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le e.hj hle)
    have hpdvd : e.p ∣ n := Nat.dvd_of_factorization_pos hfacpos
    have hp_le_n : e.p <= n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpdvd
    have hpMem : e.p ∈ Robin1984.primesUpToSet n := by
      unfold Robin1984.primesUpToSet
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hp_le_n), e.hp⟩
    refine
      Finset.mem_biUnion.mpr
        ⟨⟨e.p, hpMem⟩, Finset.mem_attach _ _, ?_⟩
    apply Finset.mem_image.mpr
    have hjMem :
        e.j ∈ (Finset.range (n.factorization e.p + 1)).filter
          (fun j => 0 < j) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle), e.hj⟩
    refine ⟨⟨e.j, hjMem⟩, Finset.mem_attach _ _, ?_⟩
    cases e
    rfl

/-- The actual tower events for one prime in the support of `n.factorization`. -/
noncomputable def actualFactorizationTowerEventsForPrime
    (n : Nat) (p : {p : Nat // p ∈ n.factorization.support}) :
    Finset Robin1984.Event := by
  classical
  exact (Finset.Icc 1 (n.factorization p.val)).attach.image
    (fun j => {
      p := p.val
      j := j.val
      hp := by
        have hpPrimeFactors : p.val ∈ n.primeFactors := by
          exact p.property
        exact Nat.prime_of_mem_primeFactors hpPrimeFactors
      hj := (Finset.mem_Icc.mp j.property).1
    })

/-- The same actual exponent packet, indexed directly by the support of
`n.factorization`. -/
noncomputable def actualFactorizationTowerEvents (n : Nat) :
    Finset Robin1984.Event :=
  n.factorization.support.attach.biUnion
    (actualFactorizationTowerEventsForPrime n)

/-- Membership in the support-indexed factorization tower is exactly bounded by
the factorization exponent of the event's prime base. -/
theorem mem_actualFactorizationTowerEvents_iff
    {n : Nat} {e : Robin1984.Event} :
    e ∈ actualFactorizationTowerEvents n ↔
      e.j <= n.factorization e.p := by
  classical
  constructor
  · intro he
    unfold actualFactorizationTowerEvents at he
    rcases Finset.mem_biUnion.mp he with ⟨p, _hpMem, heImage⟩
    rcases Finset.mem_image.mp heImage with ⟨j, _hjMem, hje⟩
    rw [← hje]
    exact (Finset.mem_Icc.mp j.property).2
  · intro hle
    unfold actualFactorizationTowerEvents
    have hfacpos : n.factorization e.p ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le e.hj hle)
    have hpSupport : e.p ∈ n.factorization.support :=
      Finsupp.mem_support_iff.mpr hfacpos
    refine
      Finset.mem_biUnion.mpr
        ⟨⟨e.p, hpSupport⟩, Finset.mem_attach _ _, ?_⟩
    apply Finset.mem_image.mpr
    have hjMem : e.j ∈ Finset.Icc 1 (n.factorization e.p) :=
      Finset.mem_Icc.mpr ⟨e.hj, hle⟩
    refine ⟨⟨e.j, hjMem⟩, Finset.mem_attach _ _, ?_⟩
    cases e
    rfl

/-- The range-based actual packet agrees with the direct factorization-tower
packet for nonzero `n`. -/
theorem actualExponentEvents_eq_actualFactorizationTowerEvents
    {n : Nat} (hn : n ≠ 0) :
    actualExponentEvents n = actualFactorizationTowerEvents n := by
  classical
  ext e
  rw [mem_actualExponentEvents_iff (n := n) hn,
    mem_actualFactorizationTowerEvents_iff]

/-- Distinct prime-base tower packets are disjoint. -/
theorem pairwiseDisjoint_actualFactorizationTowerEventsForPrime
    (n : Nat) :
    Set.PairwiseDisjoint (↑(n.factorization.support.attach))
      (actualFactorizationTowerEventsForPrime n) := by
  rw [Set.PairwiseDisjoint]
  intro p _hp q _hq hpq
  change Disjoint (actualFactorizationTowerEventsForPrime n p)
    (actualFactorizationTowerEventsForPrime n q)
  rw [Finset.disjoint_left]
  intro e hep heq
  unfold actualFactorizationTowerEventsForPrime at hep heq
  rcases Finset.mem_image.mp hep with ⟨j, _hj, hje⟩
  rcases Finset.mem_image.mp heq with ⟨k, _hk, hke⟩
  have hpvalq : p.val = q.val := by
    have hbase := congrArg Robin1984.Event.p (hje.trans hke.symm)
    simpa using hbase
  exact hpq (Subtype.ext hpvalq)

/-- The support-indexed factorization tower has logarithmic mass equal to the
finite factorization log sum. -/
theorem actualFactorizationTowerEvents_sum_log_eq_factorization_log
    (n : Nat) :
    (actualFactorizationTowerEvents n).sum
        (fun e => Real.log (e.p : Real)) =
      n.factorization.sum
        (fun p t => (t : Real) * Real.log (p : Real)) := by
  classical
  unfold actualFactorizationTowerEvents
  rw [Finset.sum_biUnion
    (pairwiseDisjoint_actualFactorizationTowerEventsForPrime n)]
  rw [Finsupp.sum]
  conv_rhs =>
    rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro p hp
  unfold actualFactorizationTowerEventsForPrime
  rw [Finset.sum_image]
  · simp [Finset.sum_const, Nat.card_Icc, mul_comm]
  · intro a _ha b _hb h
    exact Subtype.ext (congrArg Robin1984.Event.j h)

/-- Native actual-packet log-mass identity: summing `log p` over all
factorization events gives `log n`. -/
theorem actualExponentEvents_eventLogMass_eq_log
    {n : Nat} (hn : n ≠ 0) :
    Robin1984.eventLogMass (actualExponentEvents n) = Real.log (n : Real) := by
  rw [actualExponentEvents_eq_actualFactorizationTowerEvents hn]
  unfold Robin1984.eventLogMass
  rw [actualFactorizationTowerEvents_sum_log_eq_factorization_log]
  rw [← Real.log_nat_eq_sum_factorization n]

/-- The actual exponent-event packet has logarithmic height `log n`. -/
theorem actualExponentState_logN_eq_log
    {n : Nat} (hn : n ≠ 0) :
    (actualExponentState n).logN = Real.log (n : Real) := by
  unfold actualExponentState Robin1984.applyPacket
  simpa [Robin1984.zeroCAState, Robin1984.eventLogMass] using
    actualExponentEvents_eventLogMass_eq_log (n := n) hn

/-- Finite Euler-factor correction attached to the top exponent of one prime. -/
noncomputable def primeTowerTopCorrection (p j : Nat) : Real :=
  - Real.log (1 - (p : Real) ^ (-(j + 1 : Int)))

/-- For a base above `1`, the Euler-factor term at a positive layer has a
strictly positive logarithm argument. -/
theorem one_sub_prime_zpow_neg_pos
    {p : Nat} (hp : 1 < (p : Real)) {j : Nat} (hj : 0 < j) :
    0 < 1 - (p : Real) ^ (-(j : Int)) := by
  have hp_nonneg : 0 <= (p : Real) := le_of_lt (lt_trans zero_lt_one hp)
  have hpow_gt_one : 1 < (p : Real) ^ j := by
    exact (one_lt_pow_iff_of_nonneg hp_nonneg hj.ne').mpr hp
  have hinv_lt_one : ((p : Real) ^ j)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hpow_gt_one
  rw [zpow_neg, zpow_natCast]
  exact sub_pos.mpr hinv_lt_one

/-- One event gain is the drop in the finite Euler-factor correction from the
previous layer to the new top layer. -/
theorem primeTowerEventGain_succ_eq_topCorrection_sub
    {p d : Nat} (hpPrime : Nat.Prime p) :
    ({ p := p, j := d + 1, hp := hpPrime, hj := Nat.succ_pos d } :
        Robin1984.Event).gain =
      primeTowerTopCorrection p d - primeTowerTopCorrection p (d + 1) := by
  have hpReal : 1 < (p : Real) := by exact_mod_cast hpPrime.one_lt
  have hA : 0 < 1 - (p : Real) ^ (-(d + 2 : Int)) := by
    simpa using one_sub_prime_zpow_neg_pos (p := p) hpReal
      (j := d + 2) (by omega)
  have hB : 0 < 1 - (p : Real) ^ (-(d + 1 : Int)) := by
    simpa using one_sub_prime_zpow_neg_pos (p := p) hpReal
      (j := d + 1) (Nat.succ_pos d)
  change
    Real.log
        ((1 - (p : Real) ^ (-(d + 2 : Int))) /
          (1 - (p : Real) ^ (-(d + 1 : Int)))) =
      -Real.log (1 - (p : Real) ^ (-(d + 1 : Int))) -
        -Real.log (1 - (p : Real) ^ (-(d + 2 : Int)))
  rw [Real.log_div (ne_of_gt hA) (ne_of_gt hB)]
  ring

/-- Full-tower telescope for one prime base. -/
theorem primeTowerEventGains_sum_eq_topCorrection_sub
    {p d : Nat} (hpPrime : Nat.Prime p) :
    (Finset.Icc 1 d).sum
        (fun j =>
          if hj : 0 < j then
            ({ p := p, j := j, hp := hpPrime, hj := hj } : Robin1984.Event).gain
          else 0) =
      primeTowerTopCorrection p 0 - primeTowerTopCorrection p d := by
  induction d with
  | zero =>
      simp [primeTowerTopCorrection]
  | succ d ih =>
      have hIcc :
          Finset.Icc 1 (d + 1) =
            insert (d + 1) (Finset.Icc 1 d) := by
        ext j
        simp
        omega
      have hnotmem : d + 1 ∉ Finset.Icc 1 d := by
        simp
      have hgain :
          (if hj : 0 < d + 1 then
              ({ p := p, j := d + 1, hp := hpPrime, hj := hj } :
                Robin1984.Event).gain
            else 0) =
            primeTowerTopCorrection p d -
              primeTowerTopCorrection p (d + 1) := by
        split
        · simpa using
            primeTowerEventGain_succ_eq_topCorrection_sub
              (p := p) (d := d) hpPrime
        · omega
      rw [hIcc, Finset.sum_insert hnotmem, ih, hgain]
      ring

/-- Attached-index version of the one-prime tower telescope, matching
`actualFactorizationTowerEventsForPrime`. -/
theorem primeTowerEventGains_attach_sum_eq_topCorrection_sub
    {p d : Nat} (hpPrime : Nat.Prime p) :
    (Finset.Icc 1 d).attach.sum
        (fun j =>
          ({ p := p, j := j.val, hp := hpPrime,
              hj := (Finset.mem_Icc.mp j.property).1 } : Robin1984.Event).gain) =
      primeTowerTopCorrection p 0 - primeTowerTopCorrection p d := by
  have hattach :
      (Finset.Icc 1 d).attach.sum
          (fun j =>
            ({ p := p, j := j.val, hp := hpPrime,
                hj := (Finset.mem_Icc.mp j.property).1 } : Robin1984.Event).gain) =
        (Finset.Icc 1 d).sum
          (fun j =>
            if hj : 0 < j then
              ({ p := p, j := j, hp := hpPrime, hj := hj } :
                Robin1984.Event).gain
            else 0) := by
    rw [← Finset.sum_attach (s := Finset.Icc 1 d)
      (f := fun j =>
        if hj : 0 < j then
          ({ p := p, j := j, hp := hpPrime, hj := hj } : Robin1984.Event).gain
        else 0)]
    apply Finset.sum_congr rfl
    intro j _hj
    have hpos : 0 < (j : Nat) := (Finset.mem_Icc.mp j.property).1
    simp [hpos]
  rw [hattach]
  exact primeTowerEventGains_sum_eq_topCorrection_sub
    (p := p) (d := d) hpPrime

/-- The endpoint correction drop is the local prime-power abundancy factor. -/
theorem primeTowerTopCorrection_zero_sub_eq_log_geom_div_pow
    {p k : Nat} (hp : 1 < (p : Real)) :
    primeTowerTopCorrection p 0 - primeTowerTopCorrection p k =
      Real.log
        (((Finset.range (k + 1)).sum (fun i => (p : Real) ^ i)) /
          ((p : Real) ^ k)) := by
  have hA : 0 < 1 - (p : Real) ^ (-(k + 1 : Int)) := by
    simpa using
      one_sub_prime_zpow_neg_pos (p := p) hp (j := k + 1)
        (Nat.succ_pos k)
  have hB : 0 < 1 - (p : Real) ^ (-(1 : Int)) := by
    simpa using
      one_sub_prime_zpow_neg_pos (p := p) hp (j := 1)
        (by norm_num : 0 < 1)
  have hlog :
      primeTowerTopCorrection p 0 - primeTowerTopCorrection p k =
        Real.log
          (((1 - (p : Real) ^ (-(k + 1 : Int))) /
            (1 - (p : Real) ^ (-(1 : Int))))) := by
    dsimp [primeTowerTopCorrection]
    rw [Real.log_div (ne_of_gt hA) (ne_of_gt hB)]
    ring
  rw [hlog]
  apply congrArg Real.log
  have hp_pos : 0 < (p : Real) := lt_trans zero_lt_one hp
  have hp0 : (p : Real) ≠ 0 := ne_of_gt hp_pos
  have hp1 : (p : Real) ≠ 1 := ne_of_gt hp
  have hz : (p : Real) ^ ((k : Int) + 1) = (p : Real) ^ (k + 1) := by
    simpa using zpow_natCast (p : Real) (k + 1)
  rw [geom_sum_eq hp1]
  rw [zpow_neg, zpow_neg, hz]
  norm_num
  field_simp [hp0, hp1]
  ring

/-- The support-indexed factorization tower gain sum telescopes prime by prime
to finite Euler-factor endpoint corrections. -/
theorem actualFactorizationTowerEvents_sum_gain_eq_factorization_topCorrection
    (n : Nat) :
    (actualFactorizationTowerEvents n).sum (fun e => e.gain) =
      n.factorization.sum
        (fun p k =>
          primeTowerTopCorrection p 0 - primeTowerTopCorrection p k) := by
  classical
  unfold actualFactorizationTowerEvents
  rw [Finset.sum_biUnion
    (pairwiseDisjoint_actualFactorizationTowerEventsForPrime n)]
  rw [Finsupp.sum]
  conv_rhs =>
    rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro p hp
  unfold actualFactorizationTowerEventsForPrime
  rw [Finset.sum_image]
  · have hpPrime : Nat.Prime p.val := by
      have hpPrimeFactors : p.val ∈ n.primeFactors := by
        exact p.property
      exact Nat.prime_of_mem_primeFactors hpPrimeFactors
    simpa using
      primeTowerEventGains_attach_sum_eq_topCorrection_sub
        (p := p.val) (d := n.factorization p.val) hpPrime
  · intro a _ha b _hb h
    exact Subtype.ext (congrArg Robin1984.Event.j h)

/-- The factorization endpoint-correction product is exactly
`log (sigma(n) / n)`. -/
theorem factorization_primeTowerTopCorrection_sum_eq_log_abundancy
    {n : Nat} (hn : n ≠ 0) :
    n.factorization.sum
        (fun p k =>
          primeTowerTopCorrection p 0 - primeTowerTopCorrection p k) =
      Real.log (abundancy n) := by
  classical
  let localGain : Nat → Real := fun p =>
    ((Finset.range (n.factorization p + 1)).sum
        (fun i => (p : Real) ^ i)) /
      ((p : Real) ^ n.factorization p)
  have hsum :
      n.factorization.sum
          (fun p k =>
            primeTowerTopCorrection p 0 - primeTowerTopCorrection p k) =
        ∑ p ∈ n.factorization.support, Real.log (localGain p) := by
    rw [Finsupp.sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : Nat.Prime p :=
      Nat.prime_of_mem_primeFactors (by
        simpa [Nat.support_factorization] using hp)
    have hpReal : 1 < (p : Real) := by exact_mod_cast hpPrime.one_lt
    simp [localGain,
      primeTowerTopCorrection_zero_sub_eq_log_geom_div_pow
        (p := p) (k := n.factorization p) hpReal]
  have hlocal_ne :
      ∀ p ∈ n.factorization.support, localGain p ≠ 0 := by
    intro p hp
    have hpPrime : Nat.Prime p :=
      Nat.prime_of_mem_primeFactors (by
        simpa [Nat.support_factorization] using hp)
    have hp_pos : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have hden : (p : Real) ^ n.factorization p ≠ 0 :=
      pow_ne_zero _ (ne_of_gt hp_pos)
    have hnum_pos :
        0 <
          (Finset.range (n.factorization p + 1)).sum
            (fun i => (p : Real) ^ i) := by
      refine Finset.sum_pos (fun i _hi => pow_pos hp_pos i) ?_
      exact ⟨0, by simp⟩
    dsimp [localGain]
    exact div_ne_zero (ne_of_gt hnum_pos) hden
  have hprod_log :
      (∑ p ∈ n.factorization.support, Real.log (localGain p)) =
        Real.log (∏ p ∈ n.factorization.support, localGain p) :=
    (Real.log_prod hlocal_ne).symm
  rw [hsum, hprod_log]
  apply congrArg Real.log
  unfold abundancy
  have hsigma :
      (Robin1984.Core.sigmaOneNat n : Real) =
        ∏ p ∈ n.factorization.support,
          (Finset.range (n.factorization p + 1)).sum
            (fun i => (p : Real) ^ i) := by
    have h :=
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) (n := n) hn
    unfold Robin1984.Core.sigmaOneNat
    rw [h]
    simp [Nat.support_factorization]
  have hnprod :
      (n : Real) =
        ∏ p ∈ n.factorization.support,
          (p : Real) ^ n.factorization p := by
    have hNat :
        (∏ p ∈ n.factorization.support, p ^ n.factorization p) = n := by
      simpa [Finsupp.prod] using Nat.prod_factorization_pow_eq_self hn
    exact_mod_cast hNat.symm
  rw [hsigma, hnprod]
  dsimp [localGain]
  rw [Finset.prod_div_distrib]

/-- Native actual-packet gain identity: summing event gains over the concrete
factorization packet gives `log (sigma(n) / n)`. -/
theorem actualExponentEvents_eventGainSum_eq_log_abundancy
    {n : Nat} (hn : n ≠ 0) :
    Robin1984.eventGainSum (actualExponentEvents n) = Real.log (abundancy n) := by
  rw [actualExponentEvents_eq_actualFactorizationTowerEvents hn]
  unfold Robin1984.eventGainSum
  rw [actualFactorizationTowerEvents_sum_gain_eq_factorization_topCorrection]
  exact factorization_primeTowerTopCorrection_sum_eq_log_abundancy (n := n) hn


/-- The CA log-objective of an integer is exactly the reduced weight of its
actual factorization event packet at the same cutoff. -/
theorem caLogObjective_eq_actualExponentEvents_eventPacketReducedWeight
    {eps : Real} {n : Nat} (hn : n ≠ 0) :
    caLogObjective eps n =
      Robin1984.eventPacketReducedWeight eps (actualExponentEvents n) := by
  rw [caLogObjective_eq_log_abundancy_sub (eps := eps)
    (n := n) (Nat.pos_of_ne_zero hn)]
  rw [Robin1984.eventPacketReducedWeight_eq_eventGainSum_sub]
  rw [actualExponentEvents_eventGainSum_eq_log_abundancy (n := n) hn,
    actualExponentEvents_eventLogMass_eq_log (n := n) hn]

/-- The actual exponent-event packet has sigma coordinate
`log (sigma(n) / n)`. -/
theorem actualExponentState_logSigmaOverN_eq_log_abundancy
    {n : Nat} (hn : n ≠ 0) :
    (actualExponentState n).logSigmaOverN = Real.log (abundancy n) := by
  unfold actualExponentState Robin1984.applyPacket
  simpa [Robin1984.zeroCAState, Robin1984.eventGainSum] using
    actualExponentEvents_eventGainSum_eq_log_abundancy (n := n) hn


/-- The same tangent bound for every `U > 1`, not only for points to the
right of `L`.  This is the form needed to move from a Robin counterexample to
a CA/log-objective maximizer at the tangent cutoff. -/
theorem log_log_sub_le_frontier_tangent_global
    {L U : Real} (hL : 1 < L) (hU : 1 < U) :
    Real.log (Real.log U) - Real.log (Real.log L) <=
      (L * Real.log L)⁻¹ * (U - L) := by
  have hLpos : 0 < L := lt_trans zero_lt_one hL
  have hUpos : 0 < U := lt_trans zero_lt_one hU
  have hLogLpos : 0 < Real.log L := Real.log_pos hL
  have hLogUpos : 0 < Real.log U := Real.log_pos hU
  have hLogRatioPos : 0 < Real.log U / Real.log L :=
    div_pos hLogUpos hLogLpos
  have hLogRatio := Real.log_le_sub_one_of_pos hLogRatioPos
  have hLogDivLogs :
      Real.log (Real.log U / Real.log L) =
        Real.log (Real.log U) - Real.log (Real.log L) :=
    Real.log_div (ne_of_gt hLogUpos) (ne_of_gt hLogLpos)
  have hStep1 :
      Real.log (Real.log U) - Real.log (Real.log L) <=
        Real.log U / Real.log L - 1 := by
    rw [← hLogDivLogs]
    exact hLogRatio
  have hURatioPos : 0 < U / L := div_pos hUpos hLpos
  have hLogURatio := Real.log_le_sub_one_of_pos hURatioPos
  have hLogDivUL : Real.log (U / L) = Real.log U - Real.log L :=
    Real.log_div (ne_of_gt hUpos) (ne_of_gt hLpos)
  have hLogDiff_le : Real.log U - Real.log L <= U / L - 1 := by
    rw [← hLogDivUL]
    exact hLogURatio
  have hUL_sub : U / L - 1 = (U - L) / L := by
    field_simp [ne_of_gt hLpos]
  have hLogDiff_le' : Real.log U - Real.log L <= (U - L) / L := by
    simpa [hUL_sub] using hLogDiff_le
  have hStep2 :
      Real.log U / Real.log L - 1 <=
        ((U - L) / L) / Real.log L := by
    have hEq :
        Real.log U / Real.log L - 1 =
          (Real.log U - Real.log L) / Real.log L := by
      field_simp [ne_of_gt hLogLpos]
    rw [hEq]
    exact div_le_div_of_nonneg_right hLogDiff_le' (le_of_lt hLogLpos)
  have hStep3 :
      ((U - L) / L) / Real.log L =
        (L * Real.log L)⁻¹ * (U - L) := by
    field_simp [ne_of_gt hLpos, ne_of_gt hLogLpos]
  exact hStep1.trans (hStep2.trans (le_of_eq hStep3))


end Robin1984
