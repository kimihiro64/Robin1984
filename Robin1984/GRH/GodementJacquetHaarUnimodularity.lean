import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.ModularCharacter

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Haar measure, the modular character, and finite-covolume quotients of locally compact groups.
- Formalization note: Proves right invariance of left Haar measure from a measurable left fundamental domain of positive finite mass.
- PROVENANCE-END
-/

/-!
# Right Haar invariance from finite covolume

Right translating a measurable fundamental domain preserves its exact
left-orbit representative property. Its Haar mass is therefore unchanged.
A positive finite mass forces the modular character to be one.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open MeasureTheory

/-- A measurable left-quotient fundamental domain of positive finite Haar
mass forces the Haar measure to be right invariant. -/
theorem isMulRightInvariant_of_measurableFundamentalRepresentatives_finiteMass
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [mu.IsHaarMeasure] [Measure.InnerRegular mu]
    (H : Subgroup G) [Countable H]
    (D : Set G) (hD : MeasurableSet D)
    (hUnique : forall x : G, ExistsUnique (fun h : H => Membership.mem D (h.val * x)))
    (hPos : 0 < mu D) (hFin : mu D < Top.top) :
    mu.IsMulRightInvariant := by
  let hFD : IsFundamentalDomain H D mu :=
    IsFundamentalDomain.mk' hD.nullMeasurableSet hUnique
  constructor
  intro g
  let R (x : G) := x * g
  let S := Set.preimage R D
  have hR : Measurable R := (continuous_mul_const g).measurable
  have hS : MeasurableSet S := hR hD
  have hUS (x : G) : ExistsUnique (fun h : H => Membership.mem S (h.val * x)) := by
    change ExistsUnique (fun h : H => Membership.mem D ((h.val * x) * g))
    simpa only [mul_assoc] using hUnique (x * g)
  let hFS : IsFundamentalDomain H S mu := IsFundamentalDomain.mk' hS.nullMeasurableSet hUS
  have he : Measure.map R mu D = mu D := by
    rw [Measure.map_apply hR hD]
    exact hFS.measure_eq hFD
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul] at he
  change (Measure.modularCharacterFun g : ENNReal) * mu D = mu D at he
  have hm : Measure.modularCharacterFun g = 1 := by
    apply ENNReal.coe_injective
    simpa only [ENNReal.coe_one] using (ENNReal.mul_eq_right hPos.ne' hFin.ne).mp he
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul, hm, one_smul]

end Robin1984.GRH
