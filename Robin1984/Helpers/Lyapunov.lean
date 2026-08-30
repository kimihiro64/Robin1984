import Mathlib
import Robin1984.Helpers.Event

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# State and potential for colossally abundant event packets

`CAState` records the accumulated logarithmic size, logarithmic abundancy gain,
and event support of a prime-power packet. This module defines the zero state,
packet application, total event mass and gain, and the Lyapunov potential used
to compare successive colossally abundant states.
-/

namespace Robin1984
/-- A finite CA-state summary, using logarithms to avoid huge integer products. -/
structure CAState where
  logN : ℝ
  logSigmaOverN : ℝ

/-- Empty CA-state before applying any event prefix. -/
def zeroCAState : CAState where
  logN := 0
  logSigmaOverN := 0


/-- Robin Lyapunov value `L = -log R = γ + log(log(log N)) - log(σ(N)/N)`. -/
noncomputable def lyapunov (s : CAState) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log s.logN) - s.logSigmaOverN


/-- Apply a finite event packet to the logarithmic CA-state summary. -/
noncomputable def applyPacket (s : CAState) (events : Finset Event) : CAState where
  logN := s.logN + (∑ e ∈ events, Real.log (e.p : ℝ))
  logSigmaOverN := s.logSigmaOverN + (∑ e ∈ events, e.gain)

/-- Total logarithmic prime mass of a finite event set. -/
noncomputable def eventLogMass (events : Finset Event) : ℝ :=
  ∑ e ∈ events, Real.log (e.p : ℝ)


/-- Prime numbers up to a bound `P`, represented as a finite filtered range. -/
def primesUpToSet (P : ℕ) : Finset ℕ :=
  (Finset.range (P + 1)).filter Nat.Prime


/-- The canonical layer-`j` event attached to a prime `p`. -/
def layerEventOfPrime (p j : ℕ) (hp : Nat.Prime p) (hj : 0 < j) : Event where
  p := p
  j := j
  hp := hp
  hj := hj


/-- Total logarithmic gain in `sigma(n)/n` from a finite event set. -/
noncomputable def eventGainSum (events : Finset Event) : ℝ :=
  ∑ e ∈ events, e.gain


end Robin1984
