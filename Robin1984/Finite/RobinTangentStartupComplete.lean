import Robin1984.Equivalence.RobinTangentTransfer
import Robin1984.Finite.RobinTangentStartup
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Complete constructive startup certificate for Robin tangent coverage

This module propagates the eight certified boundary signs across the complete
prime-power event packet and proves the classical CA startup pair.
-/

namespace Robin1984

noncomputable section

structure CA5040EventsPackage where
  events : Finset Robin1984.Event
  eq_actual : events = actualExponentEvents 5040

opaque ca5040EventsPackage : CA5040EventsPackage :=
  { events := actualExponentEvents 5040
    eq_actual := rfl }

/-- Opaque name for the concrete startup packet.  Keeping the generated
finset behind this projection prevents elaboration from evaluating all rows. -/
def ca5040Events : Finset Robin1984.Event := ca5040EventsPackage.events

theorem ca5040Events_eq_actualExponentEvents :
    ca5040Events = actualExponentEvents 5040 := by
  exact ca5040EventsPackage.eq_actual

theorem mem_ca5040Events_iff (e : Robin1984.Event) :
    Membership.mem ca5040Events e <->
      e.j <= Nat.factorization 5040 e.p := by
  rw [ca5040Events_eq_actualExponentEvents]
  exact mem_actualExponentEvents_iff (n := 5040) (e := e)
    (by norm_num : Not (5040 = 0))

theorem eventReducedWeight_nonneg_of_actual_5040_top
    (e top : Robin1984.Event)
    (he : Membership.mem ca5040Events e)
    (hSame : e.p = top.p)
    (hFactor : Nat.factorization 5040 e.p = top.j)
    (hTop : ca5040To55440Cutoff < top.threshold) :
    0 <= Robin1984.eventReducedWeight ca5040To55440Cutoff e := by
  have hLayer : e.j <= top.j := by
    rw [<- hFactor]
    exact
      (mem_ca5040Events_iff e).mp he
  have hThreshold : top.threshold <= e.threshold :=
    Robin1984.event_threshold_antitone_same_prime hSame hLayer
  exact
    (Robin1984.eventReducedWeight_nonneg_iff_threshold
      ca5040To55440Cutoff e).mpr
        (le_trans hTop.le hThreshold)

theorem eventReducedWeight_nonpos_of_not_actual_5040_firstMissing
    (e first : Robin1984.Event)
    (heNot : Not (Membership.mem ca5040Events e))
    (hSame : first.p = e.p)
    (hFactor : first.j = Nat.factorization 5040 e.p + 1)
    (hFirst : first.threshold < ca5040To55440Cutoff) :
    Robin1984.eventReducedWeight ca5040To55440Cutoff e <= 0 := by
  have hNotLayer : Not (e.j <= Nat.factorization 5040 e.p) := by
    intro hLayer
    exact heNot
      ((mem_ca5040Events_iff e).mpr hLayer)
  have hLayer : first.j <= e.j := by
    rw [hFactor]
    omega
  have hThreshold : e.threshold <= first.threshold :=
    Robin1984.event_threshold_antitone_same_prime hSame hLayer
  exact
    (Robin1984.eventReducedWeight_nonpos_iff_threshold
      ca5040To55440Cutoff e).mpr
        (le_trans hThreshold hFirst.le)

theorem eleven_le_prime_of_not_two_three_five_seven
    {p : Nat} (hp : Nat.Prime p)
    (h2 : Not (p = 2)) (h3 : Not (p = 3))
    (h5 : Not (p = 5)) (h7 : Not (p = 7)) :
    11 <= p := by
  by_contra hNot
  have hpLt : p < 11 := Nat.lt_of_not_ge hNot
  have hpTwo : 2 <= p := hp.two_le
  interval_cases p
  all_goals norm_num at hp
  all_goals omega

/-- The actual `5040` packet has the globally correct signs: every included
event is nonnegative and every excluded event, at every prime and layer, is
nonpositive. -/
theorem actualExponentEvents_5040_complete_signs :
    And
      (forall e : Robin1984.Event,
        Membership.mem ca5040Events e ->
          0 <= Robin1984.eventReducedWeight ca5040To55440Cutoff e)
      (forall e : Robin1984.Event,
        Not (Membership.mem ca5040Events e) ->
          Robin1984.eventReducedWeight ca5040To55440Cutoff e <= 0) := by
  constructor
  case left =>
    intro e he
    have hLayer :=
      (mem_ca5040Events_iff e).mp he
    have hFactorPos : Not (Nat.factorization 5040 e.p = 0) := by
      intro hZero
      rw [hZero] at hLayer
      have hj := e.hj
      omega
    have hDvd : Dvd.dvd e.p 5040 :=
      Nat.dvd_of_factorization_pos hFactorPos
    have hCases := prime_dvd_5040_cases e.hp hDvd
    exact Or.elim hCases
      (fun hpEq =>
        eventReducedWeight_nonneg_of_actual_5040_top e ca5040Top2 he
          (by simpa [ca5040Top2, Robin1984.layerEventOfPrime] using hpEq)
          (by
            rw [hpEq]
            simpa [ca5040Top2, Robin1984.layerEventOfPrime] using
              factorization_5040_at_2)
          cutoff_lt_ca5040Top2_threshold)
      (fun hRest3 => Or.elim hRest3
        (fun hpEq =>
          eventReducedWeight_nonneg_of_actual_5040_top e ca5040Top3 he
            (by simpa [ca5040Top3, Robin1984.layerEventOfPrime] using hpEq)
            (by
              rw [hpEq]
              simpa [ca5040Top3, Robin1984.layerEventOfPrime] using
                factorization_5040_at_3)
            cutoff_lt_ca5040Top3_threshold)
        (fun hRest5 => Or.elim hRest5
          (fun hpEq =>
            eventReducedWeight_nonneg_of_actual_5040_top e ca5040Top5 he
              (by simpa [ca5040Top5, Robin1984.layerEventOfPrime] using hpEq)
              (by
                rw [hpEq]
                simpa [ca5040Top5, Robin1984.layerEventOfPrime] using
                  factorization_5040_at_5)
              cutoff_lt_ca5040Top5_threshold)
          (fun hpEq =>
            eventReducedWeight_nonneg_of_actual_5040_top e ca5040Top7 he
              (by simpa [ca5040Top7, Robin1984.layerEventOfPrime] using hpEq)
              (by
                rw [hpEq]
                simpa [ca5040Top7, Robin1984.layerEventOfPrime] using
                  factorization_5040_at_7)
              cutoff_lt_ca5040Top7_threshold)))
  case right =>
    intro e heNot
    by_cases hCases :
        Or (e.p = 2) (Or (e.p = 3) (Or (e.p = 5) (e.p = 7)))
    case pos =>
      exact Or.elim hCases
        (fun hpEq =>
          eventReducedWeight_nonpos_of_not_actual_5040_firstMissing
            e ca5040FirstMissing2 heNot
            (by simpa [ca5040FirstMissing2, Robin1984.layerEventOfPrime] using
              hpEq.symm)
            (by
              rw [hpEq, factorization_5040_at_2]
              norm_num [ca5040FirstMissing2, Robin1984.layerEventOfPrime])
            ca5040FirstMissing2_threshold_lt_cutoff)
        (fun hRest3 => Or.elim hRest3
          (fun hpEq =>
            eventReducedWeight_nonpos_of_not_actual_5040_firstMissing
              e ca5040FirstMissing3 heNot
              (by simpa [ca5040FirstMissing3, Robin1984.layerEventOfPrime] using
                hpEq.symm)
              (by
                rw [hpEq, factorization_5040_at_3]
                norm_num [ca5040FirstMissing3, Robin1984.layerEventOfPrime])
              ca5040FirstMissing3_threshold_lt_cutoff)
          (fun hRest5 => Or.elim hRest5
            (fun hpEq =>
              eventReducedWeight_nonpos_of_not_actual_5040_firstMissing
                e ca5040FirstMissing5 heNot
                (by simpa [ca5040FirstMissing5, Robin1984.layerEventOfPrime] using
                  hpEq.symm)
                (by
                  rw [hpEq, factorization_5040_at_5]
                  norm_num [ca5040FirstMissing5, Robin1984.layerEventOfPrime])
                ca5040FirstMissing5_threshold_lt_cutoff)
            (fun hpEq =>
              eventReducedWeight_nonpos_of_not_actual_5040_firstMissing
                e ca5040FirstMissing7 heNot
                (by simpa [ca5040FirstMissing7, Robin1984.layerEventOfPrime] using
                  hpEq.symm)
                (by
                  rw [hpEq, factorization_5040_at_7]
                  norm_num [ca5040FirstMissing7, Robin1984.layerEventOfPrime])
                ca5040FirstMissing7_threshold_lt_cutoff)))
    case neg =>
      have h2 : Not (e.p = 2) := fun hpEq => hCases (Or.inl hpEq)
      have h3 : Not (e.p = 3) :=
        fun hpEq => hCases (Or.inr (Or.inl hpEq))
      have h5 : Not (e.p = 5) :=
        fun hpEq => hCases (Or.inr (Or.inr (Or.inl hpEq)))
      have h7 : Not (e.p = 7) :=
        fun hpEq => hCases (Or.inr (Or.inr (Or.inr hpEq)))
      have hpGe : 11 <= e.p :=
        eleven_le_prime_of_not_two_three_five_seven e.hp h2 h3 h5 h7
      let first : Robin1984.Event :=
        Robin1984.layerEventOfPrime e.p 1 e.hp one_pos_nat
      have hSamePrime : first.p = e.p := by rfl
      have hLayer : first.j <= e.j := by
        exact Nat.succ_le_of_lt e.hj
      have hSamePrimeThreshold : e.threshold <= first.threshold :=
        Robin1984.event_threshold_antitone_same_prime hSamePrime hLayer
      have hFirstThreshold : first.threshold <= ca5040To55440Event.threshold :=
        Robin1984.firstLayerEvent_threshold_antitone
          (e := ca5040To55440Event) (f := first)
          (by rfl) (by rfl) hpGe
      have hFirstCutoff : first.threshold <= ca5040To55440Cutoff := by
        rw [<- ca5040To55440Event_threshold_eq_cutoff]
        exact hFirstThreshold
      exact
        (Robin1984.eventReducedWeight_nonpos_iff_threshold
          ca5040To55440Cutoff e).mpr
            (le_trans hSamePrimeThreshold hFirstCutoff)

/-- The explicit startup packet proves that `5040` is a textbook CA maximizer
at the exact `5040 -> 55440` tangent parameter. -/
theorem colossallyAbundantWith_5040_at_cutoff :
    IsColossallyAbundantWith 5040 ca5040To55440Cutoff := by
  have hSigns := actualExponentEvents_5040_complete_signs
  have hEpsPos : 0 < ca5040To55440Cutoff :=
    lt_trans (by norm_num : (0 : Real) < 1 / 34)
      ca5040To55440Cutoff_lower
  exact And.intro hEpsPos
    (And.intro (by norm_num)
      (by
        intro k hk
        have hkPos : 0 < k := Nat.zero_lt_of_lt hk
        have hPacket :
            Robin1984.eventPacketReducedWeight ca5040To55440Cutoff
                (actualExponentEvents k) <=
              Robin1984.eventPacketReducedWeight ca5040To55440Cutoff
                ca5040Events :=
          eventPacketReducedWeight_le_of_complete_signs
            (lambda := ca5040To55440Cutoff)
            (base := ca5040Events)
            (events := actualExponentEvents k)
            (fun e he => hSigns.1 e he)
            (fun e _he heNot => hSigns.2 e heNot)
        have hLog :
            caLogObjective ca5040To55440Cutoff k <=
              caLogObjective ca5040To55440Cutoff 5040 := by
          rw [caLogObjective_eq_actualExponentEvents_eventPacketReducedWeight
              (eps := ca5040To55440Cutoff) (n := k)
              (Nat.ne_of_gt hkPos),
            caLogObjective_eq_actualExponentEvents_eventPacketReducedWeight
              (eps := ca5040To55440Cutoff) (n := 5040)
              (by norm_num : Not (5040 = 0))]
          simpa only [ca5040Events_eq_actualExponentEvents] using hPacket
        unfold caLogObjective at hLog
        exact
          (Real.log_le_log_iff
            (caObjective_pos hkPos)
            (caObjective_pos (by norm_num : 0 < 5040))).mp hLog))

theorem colossallyAbundantWith_55440_at_cutoff :
    IsColossallyAbundantWith 55440 ca5040To55440Cutoff :=
  colossallyAbundantWith_55440_of_5040
    colossallyAbundantWith_5040_at_cutoff

theorem tangentCAMaximizer_above_5040_at_startup_cutoff
    {n q : Nat}
    (hnCut : 5040 < n)
    (hEps : robinFrontierCutoff n < ca5040To55440Cutoff)
    (hqCA : IsColossallyAbundantWith q (robinFrontierCutoff n)) :
    5040 < q :=
  tangentCAMaximizer_above_5040_of_shared_5040_55440
    hnCut hEps colossallyAbundantWith_5040_at_cutoff
      colossallyAbundantWith_55440_at_cutoff hqCA

end

end Robin1984
