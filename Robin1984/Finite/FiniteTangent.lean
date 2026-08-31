import Mathlib.NumberTheory.PrimeCounting
import Robin1984.ColossallyAbundant.CAProfile
import Robin1984.ColossallyAbundant.EventGainFormula
import Robin1984.Finite.LayerThresholdMonotonicity
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Complete finite prime-power tangents

A finite list of layer cutoffs describes every positive event at a fixed
slope. Two boundary signs per layer, and one final-layer sign, control all
primes and all exponents. The conclusion bounds the objective of every
integer, not merely the integers used to select the slope.
-/

namespace Robin1984

noncomputable section

private theorem robin_div_le_iff_pos {a b c : Real} (hc : 0 < c) :
    a / c <= b <-> a <= b * c := by
  constructor
  . intro h
    calc
      a = (a / c) * c := by field_simp
      _ <= b * c := mul_le_mul_of_nonneg_right h hc.le
  . intro h
    calc
      a / c <= (b * c) / c := div_le_div_of_nonneg_right h hc.le
      _ = b := by field_simp

private theorem robin_le_div_iff_pos {a b c : Real} (hc : 0 < c) :
    a <= b / c <-> a * c <= b := by
  constructor
  . intro h
    calc
      a * c <= (b / c) * c := mul_le_mul_of_nonneg_right h hc.le
      _ = b := by field_simp
  . intro h
    calc
      a = (a * c) / c := by field_simp
      _ <= b / c := div_le_div_of_nonneg_right h hc.le

def robinRawEventWeight (lambda : Real) (v : Prod Nat Nat) : Real :=
  Robin1984.FiniteSupport.simplifiedLayerGain (v.1 : Real) v.2 - lambda * Real.log v.1

def robinLayerBox (cuts : List Nat) : Finset (Prod Nat Nat) :=
  (Finset.range cuts.length).biUnion (fun i =>
    (Nat.primesLE cuts[i]!).image (fun p => (p, i + 1)))

theorem robinLayerBox_mem {cuts : List Nat} {p j : Nat} :
    Membership.mem (robinLayerBox cuts) (p, j) <->
      And (0 < j) (And (j <= cuts.length)
        (And (Nat.Prime p) (p <= cuts[j - 1]!))) := by
  classical
  unfold robinLayerBox
  constructor
  . intro h
    choose i hi using Finset.mem_biUnion.mp h
    choose q hq using Finset.mem_image.mp hi.2
    have hEq : And (q = p) (i + 1 = j) := Prod.mk.inj hq.2
    have hp := Nat.mem_primesLE.mp hq.1
    have hiLt := Finset.mem_range.mp hi.1
    have hiEq : i = j - 1 := by omega
    have hqEq := hEq.1
    subst q
    subst i
    exact And.intro (by omega) (And.intro (by omega) (And.intro hp.2 hp.1))
  . intro h
    apply Finset.mem_biUnion.mpr
    refine Exists.intro (j - 1) (And.intro (Finset.mem_range.mpr (by omega)) ?_)
    apply Finset.mem_image.mpr
    exact Exists.intro p (And.intro (Nat.mem_primesLE.mpr (And.intro h.2.2.2 h.2.2.1))
      (by congr 1; omega))

theorem robinRawEventWeight_event (lambda : Real) (e : Robin1984.Event) :
    robinRawEventWeight lambda (e.p, e.j) = Robin1984.eventReducedWeight lambda e := by
  unfold robinRawEventWeight Robin1984.eventReducedWeight
  rw [event_gain_eq_caSimplifiedLayerGain]

theorem robinLayerBox_complete_signs {cuts : List Nat} {lambda : Real}
    (hTop : forall i : Nat, i < cuts.length ->
      2 <= cuts[i]! ->
      lambda * Real.log (cuts[i]! : Real) <=
        Robin1984.FiniteSupport.simplifiedLayerGain (cuts[i]! : Real) (i + 1))
    (hNext : forall i : Nat, i < cuts.length ->
      Robin1984.FiniteSupport.simplifiedLayerGain (max 2 (cuts[i]! + 1) : Nat) (i + 1) <=
        lambda * Real.log (max 2 (cuts[i]! + 1) : Nat))
    (hLast : Robin1984.FiniteSupport.simplifiedLayerGain 2 (cuts.length + 1) <=
      lambda * Real.log 2) :
    And
      (forall v, Membership.mem (robinLayerBox cuts) v -> 0 <= robinRawEventWeight lambda v)
      (forall e : Robin1984.Event, Not (Membership.mem (robinLayerBox cuts) (e.p, e.j)) ->
        Robin1984.eventReducedWeight lambda e <= 0) := by
  constructor
  . intro v hv
    have hm := robinLayerBox_mem.mp hv
    have hpOne : (1 : Real) < v.1 := by exact_mod_cast hm.2.2.1.one_lt
    have hcTwo : 2 <= cuts[v.2 - 1]! := hm.2.2.1.two_le.trans hm.2.2.2
    have hcOne : (1 : Real) < cuts[v.2 - 1]! := by exact_mod_cast (by omega : 1 < cuts[v.2 - 1]!)
    have hMono := Robin1984.FiniteSupport.simplifiedLayerThreshold_le_of_base_le
      (b := (cuts[v.2 - 1]! : Real))
      hpOne (by exact_mod_cast hm.2.2.2) hm.1
    have hTopI := hTop (v.2 - 1) (by omega) hcTwo
    have hJ : v.2 - 1 + 1 = v.2 := by omega
    rw [hJ] at hTopI
    have hLower : lambda <= Robin1984.FiniteSupport.simplifiedLayerGain (cuts[v.2 - 1]! : Real) v.2 /
        Real.log (cuts[v.2 - 1]! : Real) :=
      (robin_le_div_iff_pos (Real.log_pos hcOne)).mpr hTopI
    have h := (robin_le_div_iff_pos (Real.log_pos hpOne)).mp (hLower.trans hMono)
    unfold robinRawEventWeight
    linarith
  . intro e he
    have hjPos := e.hj
    have hpOne : (1 : Real) < e.p := by exact_mod_cast e.hp.one_lt
    have hBound : e.threshold <= lambda := by
      by_cases hj : e.j <= cuts.length
      . have hpCut : cuts[e.j - 1]! < e.p := by
          by_contra h
          apply he
          exact robinLayerBox_mem.mpr
            (And.intro e.hj (And.intro hj (And.intro e.hp (le_of_not_gt h))))
        have hBase : max 2 (cuts[e.j - 1]! + 1) <= e.p :=
          max_le e.hp.two_le (by omega)
        have hBaseOne : (1 : Real) < (max 2 (cuts[e.j - 1]! + 1) : Nat) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (le_max_left _ _))
        have hNextI := hNext (e.j - 1) (by omega)
        have hJ : e.j - 1 + 1 = e.j := by omega
        rw [hJ] at hNextI
        have hUpper := (robin_div_le_iff_pos (Real.log_pos hBaseOne)).mpr hNextI
        have hMono := Robin1984.FiniteSupport.simplifiedLayerThreshold_le_of_base_le
          (b := (e.p : Real))
          hBaseOne (by exact_mod_cast hBase) e.hj
        unfold Robin1984.Event.threshold
        rw [event_gain_eq_caSimplifiedLayerGain]
        exact hMono.trans hUpper
      . let f : Robin1984.Event := { p := e.p, j := cuts.length + 1, hp := e.hp, hj := Nat.succ_pos _ }
        have hLayer : e.threshold <= f.threshold :=
          Robin1984.event_threshold_antitone_same_prime (by rfl) (by dsimp [f]; omega)
        have hMono := Robin1984.FiniteSupport.simplifiedLayerThreshold_le_of_base_le
          (b := (e.p : Real))
          (by norm_num : (1 : Real) < 2) (by exact_mod_cast e.hp.two_le) (Nat.succ_pos cuts.length)
        have hUpper := (robin_div_le_iff_pos (Real.log_pos (by norm_num : (1 : Real) < 2))).mpr hLast
        have hf : f.threshold <= lambda := by
          unfold Robin1984.Event.threshold
          rw [event_gain_eq_caSimplifiedLayerGain]
          exact hMono.trans hUpper
        exact hLayer.trans hf
    exact (Robin1984.eventReducedWeight_nonpos_iff_threshold lambda e).mpr hBound

theorem robin_objective_le_finite_box {cuts : List Nat} {lambda : Real}
    (hSigns : And
      (forall v, Membership.mem (robinLayerBox cuts) v -> 0 <= robinRawEventWeight lambda v)
      (forall e : Robin1984.Event, Not (Membership.mem (robinLayerBox cuts) (e.p, e.j)) ->
        Robin1984.eventReducedWeight lambda e <= 0))
    {n : Nat} (hn : 0 < n) :
    Real.log (abundancy n) - lambda * Real.log (n : Real) <=
      Finset.sum (robinLayerBox cuts) (robinRawEventWeight lambda) := by
  classical
  let f : Robin1984.Event -> Prod Nat Nat := fun e => (e.p, e.j)
  have hInj : Function.Injective f := by
    intro e d h
    have hp : e.p = d.p := congrArg Prod.fst h
    have hj : e.j = d.j := congrArg Prod.snd h
    cases e
    cases d
    cases hp
    cases hj
    rfl
  let actual := (actualExponentEvents n).image f
  let base := robinLayerBox cuts
  let common := actual.filter (fun v => Membership.mem base v)
  have hCommonA : common <= actual := Finset.filter_subset _ _
  have hCommonB : common <= base := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hSplit := Finset.sum_sdiff hCommonA (f := robinRawEventWeight lambda)
  have hOutside : Finset.sum (SDiff.sdiff actual common) (robinRawEventWeight lambda) <= 0 := by
    apply Finset.sum_nonpos
    intro v hv
    have ha := Finset.mem_sdiff.mp hv
    choose e he using Finset.mem_image.mp ha.1
    have hNot : Not (Membership.mem base v) := by
      intro h
      exact ha.2 (Finset.mem_filter.mpr (And.intro ha.1 h))
    rw [<- he.2] at hNot
    rw [<- he.2]
    change robinRawEventWeight lambda (e.p, e.j) <= 0
    rw [robinRawEventWeight_event]
    exact hSigns.2 e hNot
  have hCommon : Finset.sum common (robinRawEventWeight lambda) <=
      Finset.sum base (robinRawEventWeight lambda) :=
    Finset.sum_le_sum_of_subset_of_nonneg hCommonB (fun v hv _ => hSigns.1 v hv)
  have hActual : Finset.sum actual (robinRawEventWeight lambda) =
      Real.log (abundancy n) - lambda * Real.log (n : Real) := by
    dsimp only [actual]
    rw [Finset.sum_image (fun _ _ _ _ h => hInj h)]
    simp only [f, robinRawEventWeight_event]
    change Robin1984.eventPacketReducedWeight lambda (actualExponentEvents n) = _
    rw [<- caLogObjective_eq_actualExponentEvents_eventPacketReducedWeight hn.ne',
      caLogObjective_eq_log_abundancy_sub hn]
  linarith

end

end Robin1984
