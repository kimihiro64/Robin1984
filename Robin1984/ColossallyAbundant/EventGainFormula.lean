import Robin1984.Finite.CutoffIndex
import Robin1984.Helpers.Event
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Fixed-layer formula for a marginal event gain

The logarithmic gain stored by `Event` agrees exactly with the simplified
fixed-layer expression used by the finite threshold certificates.
-/

namespace Robin1984

noncomputable section

/-- Native event gains agree with the simplified fixed-layer expression used
by the exact cutoff/KKT library. -/
theorem event_gain_eq_caSimplifiedLayerGain
    (e : Robin1984.Event) :
    e.gain = Robin1984.FiniteSupport.simplifiedLayerGain (e.p : Real) e.j := by
  unfold Robin1984.Event.gain Robin1984.FiniteSupport.simplifiedLayerGain
  have hExp1 :
      -((e.j : Int) + 1) = -(((e.j + 1 : Nat) : Int)) := by
    omega
  have hExp0 : -((e.j : Int)) = -(((e.j : Nat) : Int)) := rfl
  rw [hExp1, hExp0]
  rw [zpow_neg, zpow_natCast]
  rw [zpow_neg, zpow_natCast]
  have hp : 1 < (e.p : Real) := by
    exact_mod_cast e.hp.one_lt
  have hp0 : Ne (e.p : Real) 0 :=
    ne_of_gt (lt_trans zero_lt_one hp)
  have hpowj_gt : 1 < (e.p : Real) ^ e.j := by
    have hp_nonneg : 0 <= (e.p : Real) :=
      le_of_lt (lt_trans zero_lt_one hp)
    exact (one_lt_pow_iff_of_nonneg hp_nonneg e.hj.ne').mpr hp
  have hpowj_pos : 0 < (e.p : Real) ^ e.j :=
    lt_trans zero_lt_one hpowj_gt
  have hpowj_ne : Ne ((e.p : Real) ^ e.j - 1) 0 :=
    ne_of_gt (by linarith)
  have hden_left :
      Ne (1 - Inv.inv ((e.p : Real) ^ e.j)) 0 := by
    intro hzero
    have hmul :=
      congrArg (fun x : Real => x * ((e.p : Real) ^ e.j)) hzero
    field_simp [ne_of_gt hpowj_pos] at hmul
    linarith
  have hratio :
      (1 - Inv.inv ((e.p : Real) ^ (e.j + 1))) /
          (1 - Inv.inv ((e.p : Real) ^ e.j)) =
        1 + ((e.p : Real) - 1) /
          ((e.p : Real) * ((e.p : Real) ^ e.j - 1)) := by
    field_simp [hp0, hpowj_ne, hden_left]
    ring
  exact congrArg Real.log hratio


end

end Robin1984
