import Robin1984.ColossallyAbundant.CAProfile
import Robin1984.Finite.CutoffIndex
import Robin1984.Finite.FiniteLogCertificate
import Robin1984.Finite.FiniteLogScale
import Robin1984.Finite.FiniteTangent
import Robin1984.Helpers.Event
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Exact certificates for the layer signs

For a row cutoff `c` and layer `j`, `robinLayerGainRatioRat` is the exact
rational gain ratio whose logarithm controls the next prime-power event.
`RobinLayerTopCheck` certifies that an included boundary event has
nonnegative reduced weight, while `RobinLayerNextCheck` certifies that the
first excluded event has nonpositive reduced weight.

The two soundness theorems turn the rational logarithm comparisons into the
corresponding real inequalities. `RobinLayerChecks` packages these checks for
all cutoffs in a row, and its soundness theorem proves the complete sign
conditions needed by the finite-box reduction.
-/

namespace Robin1984

def robinLayerGainRatioRat (c j : Nat) : Rat :=
  1 + ((c : Rat) - 1) / ((c : Rat) * ((c : Rat)^j - 1))

theorem robinLayerGainRatioRat_ge_one {c j : Nat} (hc : 2 <= c) (hj : 0 < j) :
    (1 : Rat) <= robinLayerGainRatioRat c j := by
  have hpow : (1 : Rat) < (c : Rat)^j := by
    exact_mod_cast (Nat.one_lt_pow hj.ne' (by omega : 1 < c))
  have hcR : (2 : Rat) <= c := by exact_mod_cast hc
  unfold robinLayerGainRatioRat
  have h : (0 : Rat) <= ((c : Rat) - 1) / ((c : Rat) * ((c : Rat)^j - 1)) :=
    div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  linarith

theorem robinLayerGainRatioRat_cast (c j : Nat) :
    (robinLayerGainRatioRat c j : Real) =
      1 + ((c : Real) - 1) / ((c : Real) * ((c : Real)^j - 1)) := by
  unfold robinLayerGainRatioRat
  push_cast
  rfl

def RobinLayerTopCheck (lambda : Rat) (c j k : Nat) : Prop :=
  And (2 <= c) (And (0 < j) (And (2^k <= c)
    (lambda * robinLogScaledUpper c k 20 <= robinLogLower (robinLayerGainRatioRat c j) 20)))

def RobinLayerNextCheck (lambda : Rat) (c j k : Nat) : Prop :=
  And (2 <= c) (And (0 < j) (And (2^k <= c)
    (robinLogUpper (robinLayerGainRatioRat c j) 20 <= lambda * robinLogScaledLower c k 20)))

instance (lambda : Rat) (c j k : Nat) : Decidable (RobinLayerTopCheck lambda c j k) :=
  inferInstanceAs (Decidable (And _ (And _ (And _ _))))

instance (lambda : Rat) (c j k : Nat) : Decidable (RobinLayerNextCheck lambda c j k) :=
  inferInstanceAs (Decidable (And _ (And _ (And _ _))))

theorem RobinLayerTopCheck.sound {lambda : Rat} {c j k : Nat}
    (hlambda : 0 <= lambda) (h : RobinLayerTopCheck lambda c j k) :
    (lambda : Real) * Real.log c <= Robin1984.FiniteSupport.simplifiedLayerGain c j := by
  have hLog := (robin_log_scaled_bounds (q := (c : Rat)) k 20 (by exact_mod_cast h.2.2.1)).2
  have hGain := robinLogLower_le_log (robinLayerGainRatioRat_ge_one h.1 h.2.1) 20
  have hLam : (0 : Real) <= lambda := by exact_mod_cast hlambda
  have hMul := mul_le_mul_of_nonneg_left hLog hLam
  have hCheck : (lambda : Real) * (robinLogScaledUpper c k 20 : Real) <=
      (robinLogLower (robinLayerGainRatioRat c j) 20 : Real) := by
    exact_mod_cast h.2.2.2
  rw [robinLayerGainRatioRat_cast] at hGain
  exact hMul.trans (hCheck.trans hGain)

theorem RobinLayerNextCheck.sound {lambda : Rat} {c j k : Nat}
    (hlambda : 0 <= lambda) (h : RobinLayerNextCheck lambda c j k) :
    Robin1984.FiniteSupport.simplifiedLayerGain c j <= (lambda : Real) * Real.log c := by
  have hLog := (robin_log_scaled_bounds (q := (c : Rat)) k 20 (by exact_mod_cast h.2.2.1)).1
  have hGain := log_le_robinLogUpper (robinLayerGainRatioRat_ge_one h.1 h.2.1) 20
  have hLam : (0 : Real) <= lambda := by exact_mod_cast hlambda
  have hMul := mul_le_mul_of_nonneg_left hLog hLam
  have hCheck : (robinLogUpper (robinLayerGainRatioRat c j) 20 : Real) <=
      (lambda : Real) * (robinLogScaledLower c k 20 : Real) := by
    exact_mod_cast h.2.2.2
  rw [robinLayerGainRatioRat_cast] at hGain
  exact hGain.trans (hCheck.trans hMul)

def RobinLayerChecks (cuts : List Nat) (lambda : Rat) : Prop :=
  And (0 <= lambda)
    (And (forall i : Fin cuts.length,
      RobinLayerTopCheck lambda cuts[i.val]! (i.val + 1) (Nat.log2 cuts[i.val]!))
    (And (forall i : Fin cuts.length,
      RobinLayerNextCheck lambda (cuts[i.val]! + 1) (i.val + 1) (Nat.log2 (cuts[i.val]! + 1)))
      (RobinLayerNextCheck lambda 2 (cuts.length + 1) 1)))

instance (cuts : List Nat) (lambda : Rat) : Decidable (RobinLayerChecks cuts lambda) :=
  inferInstanceAs (Decidable (And _ (And _ (And _ _))))


theorem RobinLayerChecks.sound {cuts : List Nat} {lambda : Rat}
    (h : RobinLayerChecks cuts lambda) :
    And
      (forall v, Membership.mem (robinLayerBox cuts) v -> 0 <= robinRawEventWeight lambda v)
      (forall e : Robin1984.Event, Not (Membership.mem (robinLayerBox cuts) (e.p, e.j)) ->
        Robin1984.eventReducedWeight lambda e <= 0) := by
  apply robinLayerBox_complete_signs
  . intro i hi _
    exact (h.2.1 (Fin.mk i hi)).sound h.1
  . intro i hi
    have hc : 2 <= cuts[i]! := (h.2.1 (Fin.mk i hi)).1
    rw [max_eq_right (by omega : 2 <= cuts[i]! + 1)]
    exact (h.2.2.1 (Fin.mk i hi)).sound h.1
  . exact h.2.2.2.sound h.1

end Robin1984
