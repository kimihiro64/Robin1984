import Mathlib.Tactic.NormNum.Prime
import Robin1984.ColossallyAbundant.CAProfile
import Robin1984.Helpers.FirstLayerThreshold
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Constructive startup for the Robin tangent-CA coverage

This module isolates the finite `5040 -> 55440` transition used by the exact
Robin-equivalent coverage theorem.
-/

namespace Robin1984

noncomputable section

private theorem startup_mul_div_cancel_left_pos
    (x y : Real) (hx : 0 < x) :
    x * y / x = y := by
  field_simp [ne_of_gt hx]

private theorem startup_div_div_cancel_left_pos
    (x y : Real) (hx : 0 < x) (hy : 0 < y) :
    (x / y) / x = 1 / y := by
  field_simp [ne_of_gt hx, ne_of_gt hy]

/-- The shared CA transition parameter of `5040` and `55440`. -/
def ca5040To55440Cutoff : Real :=
  Robin1984.firstLayerThreshold (11 : Real)

/-- Every prime divisor of `5040` is one of its four prime bases. -/
theorem prime_dvd_5040_cases
    {p : Nat} (hp : Nat.Prime p) (hd : Dvd.dvd p 5040) :
    Or (p = 2) (Or (p = 3) (Or (p = 5) (p = 7))) := by
  have hfac : 5040 = (((2 ^ 4) * (3 ^ 2)) * 5) * 7 := by
    norm_num
  rw [hfac] at hd
  exact Or.elim (hp.dvd_mul.mp hd)
    (fun h235 =>
      Or.elim (hp.dvd_mul.mp h235)
        (fun h23 =>
          Or.elim (hp.dvd_mul.mp h23)
            (fun h2 => Or.inl
              ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
                (hp.dvd_of_dvd_pow h2)))
            (fun h3 => Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
                (hp.dvd_of_dvd_pow h3)))))
        (fun h5 => Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5)))))
    (fun h7 => Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7))))

/-- A rational power certificate puts an event threshold above `1 / N`. -/
theorem one_div_nat_lt_event_threshold_of_prime_lt_gainRatio_pow
    {e : Robin1984.Event} {N : Nat} (hN : 0 < N)
    (hPow :
      (e.p : Real) <
        (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) ^ N) :
    1 / (N : Real) < e.threshold := by
  have hNReal : (0 : Real) < (N : Real) := by
    exact_mod_cast hN
  have hRatioPos :
      0 < Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j := by
    apply Robin1984.eventGainRatio_pos
    rw [zpow_neg_one]
    exact inv_pos.mpr e.prime_pos
    rw [zpow_neg_one]
    have hpOne : (1 : Real) < (e.p : Real) := by
      exact_mod_cast e.hp.one_lt
    have hInv :=
      (div_lt_div_iff_of_pos_left (a := (1 : Real))
        (by norm_num : (0 : Real) < 1) e.prime_pos
        (by norm_num : (0 : Real) < 1)).2 hpOne
    simpa [one_div] using hInv
    exact e.hj
  have hLogPow :
      Real.log (e.p : Real) <
        (N : Real) *
          Real.log
            (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) := by
    have hLog := Real.log_lt_log e.prime_pos hPow
    simpa [Real.log_pow] using hLog
  have hDiv :
      Real.log (e.p : Real) / (N : Real) <
        Real.log
          (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) := by
    have hScaled :=
      (div_lt_div_iff_of_pos_right hNReal).2 hLogPow
    calc
      Real.log (e.p : Real) / (N : Real) <
          ((N : Real) *
              Real.log
                (Robin1984.eventGainRatio
                  ((e.p : Real) ^ (-1 : Int)) e.j)) / (N : Real) := hScaled
      _ = Real.log
          (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) := by
        exact startup_mul_div_cancel_left_pos _ _ hNReal
  have hFinal :=
    (div_lt_div_iff_of_pos_right e.log_prime_pos).2 hDiv
  have hBound :
      1 / (N : Real) <
        Real.log
            (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) /
          Real.log (e.p : Real) := by
    calc
      1 / (N : Real) =
          (Real.log (e.p : Real) / (N : Real)) /
            Real.log (e.p : Real) := by
        exact
          (startup_div_div_cancel_left_pos _ _ e.log_prime_pos hNReal).symm
      _ < Real.log
            (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) /
          Real.log (e.p : Real) := hFinal
  rw [Robin1984.Event.threshold, Robin1984.event_gain_eq_log_eventGainRatio]
  simpa [zpow_neg_one] using hBound

/-- A rational power certificate puts an event threshold below `1 / N`. -/
theorem event_threshold_lt_one_div_nat_of_gainRatio_pow_lt_prime
    {e : Robin1984.Event} {N : Nat} (hN : 0 < N)
    (hPow :
      (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) ^ N <
        (e.p : Real)) :
    e.threshold < 1 / (N : Real) := by
  have hNReal : (0 : Real) < (N : Real) := by
    exact_mod_cast hN
  have hRatioPos :
      0 < Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j := by
    apply Robin1984.eventGainRatio_pos
    rw [zpow_neg_one]
    exact inv_pos.mpr e.prime_pos
    rw [zpow_neg_one]
    have hpOne : (1 : Real) < (e.p : Real) := by
      exact_mod_cast e.hp.one_lt
    have hInv :=
      (div_lt_div_iff_of_pos_left (a := (1 : Real))
        (by norm_num : (0 : Real) < 1) e.prime_pos
        (by norm_num : (0 : Real) < 1)).2 hpOne
    simpa [one_div] using hInv
    exact e.hj
  have hLogPow :
      (N : Real) *
          Real.log
            (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) <
        Real.log (e.p : Real) := by
    have hLog := Real.log_lt_log (pow_pos hRatioPos N) hPow
    simpa [Real.log_pow] using hLog
  have hDiv :
      Real.log
          (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) <
        Real.log (e.p : Real) / (N : Real) := by
    have hScaled :=
      (div_lt_div_iff_of_pos_right hNReal).2 hLogPow
    calc
      Real.log
          (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) =
          ((N : Real) *
              Real.log
                (Robin1984.eventGainRatio
                  ((e.p : Real) ^ (-1 : Int)) e.j)) / (N : Real) := by
        exact (startup_mul_div_cancel_left_pos _ _ hNReal).symm
      _ < Real.log (e.p : Real) / (N : Real) := hScaled
  have hFinal :=
    (div_lt_div_iff_of_pos_right e.log_prime_pos).2 hDiv
  have hBound :
      Real.log
            (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) /
          Real.log (e.p : Real) <
        1 / (N : Real) := by
    calc
      Real.log
            (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) /
          Real.log (e.p : Real) <
          (Real.log (e.p : Real) / (N : Real)) /
            Real.log (e.p : Real) := hFinal
      _ = 1 / (N : Real) := by
        exact startup_div_div_cancel_left_pos _ _ e.log_prime_pos hNReal
  rw [Robin1984.Event.threshold, Robin1984.event_gain_eq_log_eventGainRatio]
  simpa [zpow_neg_one] using hBound

theorem prime_11 : Nat.Prime 11 := by norm_num

theorem one_pos_nat : 0 < (1 : Nat) := by norm_num

/-- The event whose admission changes `5040` into `55440`. -/
def ca5040To55440Event : Robin1984.Event :=
  Robin1984.layerEventOfPrime 11 1 prime_11 one_pos_nat

theorem ca5040To55440Event_threshold_eq_cutoff :
    ca5040To55440Event.threshold = ca5040To55440Cutoff := by
  rw [Robin1984.Event.threshold_eq_firstLayer_of_j_eq_one
    (e := ca5040To55440Event) (by rfl)]
  rfl

/-- Exact rational enclosure used to separate all non-tie startup events. -/
theorem ca5040To55440Cutoff_lower :
    (1 : Real) / 34 < ca5040To55440Cutoff := by
  rw [<- ca5040To55440Event_threshold_eq_cutoff]
  apply one_div_nat_lt_event_threshold_of_prime_lt_gainRatio_pow
    (e := ca5040To55440Event) (N := 34) (by norm_num)
  norm_num [ca5040To55440Event, Robin1984.layerEventOfPrime,
    Robin1984.eventGainRatio]

theorem ca5040To55440Cutoff_upper :
    ca5040To55440Cutoff < (1 : Real) / 22 := by
  rw [<- ca5040To55440Event_threshold_eq_cutoff]
  apply event_threshold_lt_one_div_nat_of_gainRatio_pow_lt_prime
    (e := ca5040To55440Event) (N := 22) (by norm_num)
  norm_num [ca5040To55440Event, Robin1984.layerEventOfPrime,
    Robin1984.eventGainRatio]

theorem factorization_5040_at_11 :
    Nat.factorization 5040 11 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  norm_num

theorem ca5040To55440Event_is_first_missing :
    ca5040To55440Event.j =
      Nat.factorization 5040 ca5040To55440Event.p + 1 := by
  simp [ca5040To55440Event, Robin1984.layerEventOfPrime,
    factorization_5040_at_11]

/-- The two startup integers have exactly the same tangent objective. -/
theorem caLogObjective_55440_eq_5040_at_cutoff :
    caLogObjective ca5040To55440Cutoff 55440 =
      caLogObjective ca5040To55440Cutoff 5040 := by
  have hWeightZero :
      Robin1984.eventReducedWeight ca5040To55440Cutoff
          ca5040To55440Event = 0 :=
    Robin1984.eventReducedWeight_eq_zero_of_threshold_eq
      ca5040To55440Event_threshold_eq_cutoff
  have hVariation :=
    eventReducedWeight_add_first_eq_logVariation
      (n := 5040) (eps := ca5040To55440Cutoff)
      (first := ca5040To55440Event)
      (by norm_num) ca5040To55440Event_is_first_missing
  rw [hVariation] at hWeightZero
  norm_num [ca5040To55440Event, Robin1984.layerEventOfPrime] at hWeightZero
  linarith

/-- One startup CA certificate suffices: the exact tie promotes it to `55440`. -/
theorem colossallyAbundantWith_55440_of_5040
    (h5040 : IsColossallyAbundantWith 5040 ca5040To55440Cutoff) :
    IsColossallyAbundantWith 55440 ca5040To55440Cutoff := by
  have hLogEq := caLogObjective_55440_eq_5040_at_cutoff
  unfold caLogObjective at hLogEq
  have h55440Pos : 0 < caObjective ca5040To55440Cutoff 55440 :=
    caObjective_pos (by norm_num)
  have h5040Pos : 0 < caObjective ca5040To55440Cutoff 5040 :=
    caObjective_pos (by norm_num)
  have hObjEq :
      caObjective ca5040To55440Cutoff 55440 =
        caObjective ca5040To55440Cutoff 5040 :=
    le_antisymm
      ((Real.log_le_log_iff h55440Pos h5040Pos).mp (le_of_eq hLogEq))
      ((Real.log_le_log_iff h5040Pos h55440Pos).mp (le_of_eq hLogEq.symm))
  exact And.intro h5040.eps_pos
    (And.intro (by norm_num)
      (by
        intro k hk
        rw [hObjEq]
        exact h5040.objective_max hk))

/-- A complete sign classification makes `base` maximize reduced packet
weight among every finite competitor packet. -/
theorem eventPacketReducedWeight_le_of_complete_signs
    {lambda : Real} {base events : Finset Robin1984.Event}
    (hBase : forall e : Robin1984.Event,
      Membership.mem base e -> 0 <= Robin1984.eventReducedWeight lambda e)
    (hOutside : forall e : Robin1984.Event,
      Membership.mem events e -> Not (Membership.mem base e) ->
        Robin1984.eventReducedWeight lambda e <= 0) :
    Robin1984.eventPacketReducedWeight lambda events <=
      Robin1984.eventPacketReducedWeight lambda base := by
  classical
  let common : Finset Robin1984.Event :=
    events.filter (fun e => Membership.mem base e)
  have hCommonEvent : common <= events := by
    exact Finset.filter_subset _ _
  have hCommonBase : common <= base := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hEventSplit :=
    Finset.sum_sdiff hCommonEvent
      (f := fun e => Robin1984.eventReducedWeight lambda e)
  have hBaseSplit :=
    Finset.sum_sdiff hCommonBase
      (f := fun e => Robin1984.eventReducedWeight lambda e)
  have hEventRemainder :
      Finset.sum (events \ common)
          (fun e => Robin1984.eventReducedWeight lambda e) <= 0 := by
    calc
      Finset.sum (events \ common)
          (fun e => Robin1984.eventReducedWeight lambda e) <=
          Finset.sum (events \ common) (fun _ => 0) := by
        apply Finset.sum_le_sum
        intro e he
        have heParts := Finset.mem_sdiff.mp he
        have hNotBase : Not (Membership.mem base e) := by
          intro heBase
          exact heParts.2
            (Finset.mem_filter.mpr (And.intro heParts.1 heBase))
        exact hOutside e heParts.1 hNotBase
      _ = 0 := by simp
  have hBaseRemainder :
      0 <= Finset.sum (base \ common)
        (fun e => Robin1984.eventReducedWeight lambda e) := by
    apply Finset.sum_nonneg
    intro e he
    exact hBase e (Finset.mem_sdiff.mp he).1
  unfold Robin1984.eventPacketReducedWeight
  linarith

theorem factorization_5040_at_2 : Nat.factorization 5040 2 = 4 := by
  have hMul := congrArg (fun f => f 2)
    (Nat.factorization_mul (a := 16) (b := 315)
      (by norm_num) (by norm_num))
  have hLeft : Nat.factorization 16 2 = 4 := by
    simpa using Nat.factorization_pow_self (p := 2) (n := 4) Nat.prime_two
  have hRight : Nat.factorization 315 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  calc
    Nat.factorization 5040 2 =
        Nat.factorization 16 2 + Nat.factorization 315 2 := by
      simpa using hMul
    _ = 4 := by rw [hLeft, hRight]

theorem factorization_5040_at_3 : Nat.factorization 5040 3 = 2 := by
  have hp : Nat.Prime 3 := by norm_num
  have hMul := congrArg (fun f => f 3)
    (Nat.factorization_mul (a := 9) (b := 560)
      (by norm_num) (by norm_num))
  have hLeft : Nat.factorization 9 3 = 2 := by
    simpa using Nat.factorization_pow_self (p := 3) (n := 2) hp
  have hRight : Nat.factorization 560 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  calc
    Nat.factorization 5040 3 =
        Nat.factorization 9 3 + Nat.factorization 560 3 := by
      simpa using hMul
    _ = 2 := by rw [hLeft, hRight]

theorem factorization_5040_at_5 : Nat.factorization 5040 5 = 1 := by
  have hp : Nat.Prime 5 := by norm_num
  have hMul := congrArg (fun f => f 5)
    (Nat.factorization_mul (a := 5) (b := 1008)
      (by norm_num) (by norm_num))
  have hLeft : Nat.factorization 5 5 = 1 := hp.factorization_self
  have hRight : Nat.factorization 1008 5 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  calc
    Nat.factorization 5040 5 =
        Nat.factorization 5 5 + Nat.factorization 1008 5 := by
      simpa using hMul
    _ = 1 := by rw [hLeft, hRight]

theorem factorization_5040_at_7 : Nat.factorization 5040 7 = 1 := by
  have hp : Nat.Prime 7 := by norm_num
  have hMul := congrArg (fun f => f 7)
    (Nat.factorization_mul (a := 7) (b := 720)
      (by norm_num) (by norm_num))
  have hLeft : Nat.factorization 7 7 = 1 := hp.factorization_self
  have hRight : Nat.factorization 720 7 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  calc
    Nat.factorization 5040 7 =
        Nat.factorization 7 7 + Nat.factorization 720 7 := by
      simpa using hMul
    _ = 1 := by rw [hLeft, hRight]

theorem cutoff_lt_event_threshold_of_pow22_certificate
    (e : Robin1984.Event)
    (hPow :
      (e.p : Real) <
        (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) ^ 22) :
    ca5040To55440Cutoff < e.threshold :=
  lt_trans ca5040To55440Cutoff_upper
    (one_div_nat_lt_event_threshold_of_prime_lt_gainRatio_pow
      (e := e) (N := 22) (by norm_num) hPow)

theorem event_threshold_lt_cutoff_of_pow34_certificate
    (e : Robin1984.Event)
    (hPow :
      (Robin1984.eventGainRatio ((e.p : Real) ^ (-1 : Int)) e.j) ^ 34 <
        (e.p : Real)) :
    e.threshold < ca5040To55440Cutoff :=
  lt_trans
    (event_threshold_lt_one_div_nat_of_gainRatio_pow_lt_prime
      (e := e) (N := 34) (by norm_num) hPow)
    ca5040To55440Cutoff_lower

def ca5040Top2 : Robin1984.Event :=
  Robin1984.layerEventOfPrime 2 4 Nat.prime_two (by norm_num)

def ca5040Top3 : Robin1984.Event :=
  Robin1984.layerEventOfPrime 3 2 (by norm_num) (by norm_num)

def ca5040Top5 : Robin1984.Event :=
  Robin1984.layerEventOfPrime 5 1 (by norm_num) one_pos_nat

def ca5040Top7 : Robin1984.Event :=
  Robin1984.layerEventOfPrime 7 1 (by norm_num) one_pos_nat

def ca5040FirstMissing2 : Robin1984.Event :=
  Robin1984.layerEventOfPrime 2 5 Nat.prime_two (by norm_num)

def ca5040FirstMissing3 : Robin1984.Event :=
  Robin1984.layerEventOfPrime 3 3 (by norm_num) (by norm_num)

def ca5040FirstMissing5 : Robin1984.Event :=
  Robin1984.layerEventOfPrime 5 2 (by norm_num) (by norm_num)

def ca5040FirstMissing7 : Robin1984.Event :=
  Robin1984.layerEventOfPrime 7 2 (by norm_num) (by norm_num)

theorem cutoff_lt_ca5040Top2_threshold :
    ca5040To55440Cutoff < ca5040Top2.threshold := by
  apply cutoff_lt_event_threshold_of_pow22_certificate
  change (2 : Real) <
    (Robin1984.eventGainRatio ((2 : Real) ^ (-1 : Int)) 4) ^ 22
  have hRatio :
      Robin1984.eventGainRatio ((2 : Real) ^ (-1 : Int)) 4 =
        (31 : Real) / 30 := by
    norm_num [Robin1984.eventGainRatio]
  rw [hRatio]
  norm_num

theorem cutoff_lt_ca5040Top3_threshold :
    ca5040To55440Cutoff < ca5040Top3.threshold := by
  apply cutoff_lt_event_threshold_of_pow22_certificate
  change (3 : Real) <
    (Robin1984.eventGainRatio ((3 : Real) ^ (-1 : Int)) 2) ^ 22
  have hRatio :
      Robin1984.eventGainRatio ((3 : Real) ^ (-1 : Int)) 2 =
        (13 : Real) / 12 := by
    norm_num [Robin1984.eventGainRatio]
  rw [hRatio]
  norm_num

theorem cutoff_lt_ca5040Top5_threshold :
    ca5040To55440Cutoff < ca5040Top5.threshold := by
  apply cutoff_lt_event_threshold_of_pow22_certificate
  change (5 : Real) <
    (Robin1984.eventGainRatio ((5 : Real) ^ (-1 : Int)) 1) ^ 22
  have hRatio :
      Robin1984.eventGainRatio ((5 : Real) ^ (-1 : Int)) 1 =
        (6 : Real) / 5 := by
    norm_num [Robin1984.eventGainRatio]
  rw [hRatio]
  norm_num

theorem cutoff_lt_ca5040Top7_threshold :
    ca5040To55440Cutoff < ca5040Top7.threshold := by
  apply cutoff_lt_event_threshold_of_pow22_certificate
  change (7 : Real) <
    (Robin1984.eventGainRatio ((7 : Real) ^ (-1 : Int)) 1) ^ 22
  have hRatio :
      Robin1984.eventGainRatio ((7 : Real) ^ (-1 : Int)) 1 =
        (8 : Real) / 7 := by
    norm_num [Robin1984.eventGainRatio]
  rw [hRatio]
  norm_num

theorem ca5040FirstMissing2_threshold_lt_cutoff :
    ca5040FirstMissing2.threshold < ca5040To55440Cutoff := by
  apply event_threshold_lt_cutoff_of_pow34_certificate
  change (Robin1984.eventGainRatio ((2 : Real) ^ (-1 : Int)) 5) ^ 34 <
    (2 : Real)
  have hRatio :
      Robin1984.eventGainRatio ((2 : Real) ^ (-1 : Int)) 5 =
        (63 : Real) / 62 := by
    norm_num [Robin1984.eventGainRatio]
  rw [hRatio]
  norm_num

theorem ca5040FirstMissing3_threshold_lt_cutoff :
    ca5040FirstMissing3.threshold < ca5040To55440Cutoff := by
  apply event_threshold_lt_cutoff_of_pow34_certificate
  change (Robin1984.eventGainRatio ((3 : Real) ^ (-1 : Int)) 3) ^ 34 <
    (3 : Real)
  have hRatio :
      Robin1984.eventGainRatio ((3 : Real) ^ (-1 : Int)) 3 =
        (40 : Real) / 39 := by
    norm_num [Robin1984.eventGainRatio]
  rw [hRatio]
  norm_num

theorem ca5040FirstMissing5_threshold_lt_cutoff :
    ca5040FirstMissing5.threshold < ca5040To55440Cutoff := by
  apply event_threshold_lt_cutoff_of_pow34_certificate
  change (Robin1984.eventGainRatio ((5 : Real) ^ (-1 : Int)) 2) ^ 34 <
    (5 : Real)
  have hRatio :
      Robin1984.eventGainRatio ((5 : Real) ^ (-1 : Int)) 2 =
        (31 : Real) / 30 := by
    norm_num [Robin1984.eventGainRatio]
  rw [hRatio]
  norm_num

theorem ca5040FirstMissing7_threshold_lt_cutoff :
    ca5040FirstMissing7.threshold < ca5040To55440Cutoff := by
  apply event_threshold_lt_cutoff_of_pow34_certificate
  change (Robin1984.eventGainRatio ((7 : Real) ^ (-1 : Int)) 2) ^ 34 <
    (7 : Real)
  have hRatio :
      Robin1984.eventGainRatio ((7 : Real) ^ (-1 : Int)) 2 =
        (57 : Real) / 56 := by
    norm_num [Robin1984.eventGainRatio]
  rw [hRatio]
  norm_num

end

end Robin1984
