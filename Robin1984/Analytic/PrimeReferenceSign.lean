import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: A conventional algebraic, analytic, order-theoretic, or finite-sum fact with no single author claimed.
- Formalization note: The fact is standard; its exact statement, chosen constants, and Lean proof are formalization work.
- PROVENANCE-END
-/

/-!
# A complete prime-sum bound at a freely chosen reference height

The finite prime sum is maximized at its sign threshold. This compares two
entire prime sums and retains the exact theta endpoint at the original cutoff.
-/

namespace Robin1984

noncomputable section

theorem robin_prime_reference_atom_sign {u v : Real} (hu : 1 < u) (hv : 1 < v) :
    And (u <= v -> 0 <= 1 / u - Real.log u / (v * Real.log v))
      (v <= u -> 1 / u - Real.log u / (v * Real.log v) <= 0) := by
  have huPos : 0 < u := by linarith
  have hvPos : 0 < v := by linarith
  have hLogU := Real.log_pos hu
  have hLogV := Real.log_pos hv
  have hFactor : 0 < u * (v * Real.log v) := by positivity
  have hEq : (1 / u - Real.log u / (v * Real.log v)) *
      (u * (v * Real.log v)) = v * Real.log v - u * Real.log u := by
    field_simp
  constructor
  . intro h
    have hLog := Real.log_le_log huPos h
    have hMul : u * Real.log u <= v * Real.log v := by gcongr
    nlinarith
  . intro h
    have hLog := Real.log_le_log hvPos h
    have hMul : v * Real.log v <= u * Real.log u := by gcongr
    nlinarith


end

end Robin1984
