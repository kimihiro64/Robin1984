import Robin1984.Mathlib.Analysis.Asymptotics.Omega

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# Omega-scale transfer in Robin's converse implication

Compatibility declarations for the project-independent one-sided Omega API
maintained in the Mathlib candidate layer.
-/

namespace Robin1984

open Asymptotics Filter

noncomputable section

/-- Compatibility alias for positive at-top Omega excursions. -/
abbrev AtTopOmegaPlus : (Real -> Real) -> (Real -> Real) -> Prop :=
  Asymptotics.AtTopOmegaPlus

/-- Compatibility alias for negative at-top Omega excursions. -/
abbrev AtTopOmegaMinus : (Real -> Real) -> (Real -> Real) -> Prop :=
  Asymptotics.AtTopOmegaMinus

/-- Compatibility theorem for stability of positive Omega excursions. -/
theorem AtTopOmegaPlus.add_isLittleO
    {g e h : Real -> Real}
    (hg : AtTopOmegaPlus g h)
    (hPos : Filter.Eventually (fun x => 0 < h x) Filter.atTop)
    (he : Asymptotics.IsLittleO Filter.atTop e h) :
    AtTopOmegaPlus (fun x => g x + e x) h :=
  Asymptotics.AtTopOmegaPlus.add_isLittleO hg hPos he

/-- Compatibility theorem for stability of negative Omega excursions. -/
theorem AtTopOmegaMinus.add_isLittleO
    {g e h : Real -> Real}
    (hg : AtTopOmegaMinus g h)
    (hPos : Filter.Eventually (fun x => 0 < h x) Filter.atTop)
    (he : Asymptotics.IsLittleO Filter.atTop e h) :
    AtTopOmegaMinus (fun x => g x + e x) h :=
  Asymptotics.AtTopOmegaMinus.add_isLittleO hg hPos he

/-- Compatibility theorem for the square-root/Nicolas scale comparison. -/
theorem rpow_neg_oneHalf_isLittleO_rpow_neg
    {b : Real} (hb : b < 1 / 2) :
    Asymptotics.IsLittleO Filter.atTop
      (fun x : Real => x ^ (-(1 / 2 : Real)))
      (fun x : Real => x ^ (-b)) :=
  Asymptotics.rpow_neg_oneHalf_isLittleO_rpow_neg hb

end

end Robin1984
