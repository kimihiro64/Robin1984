import Robin1984.GRH.SmoothedCriterion
import Robin1984.GRH.SmoothedForward

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The signed triangular prime-power equivalent of the critical-line property for analytic L-function data.
- Formalization note: Combines the canonical Mellin forward theorem and the Landau converse using the zero reflection of the pair.
- PROVENANCE-END
-/

/-!
# The grand RH criterion for analytic L-function data

The forward implication uses a canonical Mellin identity for the paired
zero expansion. The converse obtains right-hand nonvanishing from the
signed coefficient bound and reflects it across the critical line.
-/

set_option autoImplicit false

universe u

namespace Robin1984.GRH

/-- Grand RH: every nontrivial zero of every standard automorphic L-function
has real part one half. The index ranges over all fields, ranks, and
normalized unitary cuspidal representations when applied to grand RH. -/
def GrandRH {index : Type u} (automorphicL : index -> Complex -> Complex) : Prop :=
  forall (pi : index) (s : Complex),
    0 < s.re -> s.re < 1 -> automorphicL pi s = 0 -> s.re = 1 / 2

/-- Euler coefficients, pole-removed function, and indexed zeros for a paired standard L-function.
The constraining analytic identities are stated in `GrandRobinAdmissible`. -/
structure GrandRobinDatum (coefficients zeros : Type u) where
  primePower : coefficients -> Nat
  coefficient : coefficients -> Real
  poleOrder : Nat
  poleRemoved : Complex -> Complex
  zero : zeros -> Complex
  conjugateIndex : Equiv zeros zeros
  error : Real -> Real

/-- The one-sided triangular prime-power remainder of the analytic datum. -/
noncomputable def triangularPrimePowerRemainder {coefficients zeros : Type u}
    (d : GrandRobinDatum coefficients zeros) (x : Real) : Real :=
  (d.poleOrder : Real) / 2 * x -
    tsum (fun i => (Set.Ioi (d.primePower i : Real)).indicator
      (fun y => d.coefficient i * (1 - (d.primePower i : Real) / y)) x)

/-- The Mellin integrand of a real remainder in the triangular criterion. -/
noncomputable def grandMellinIntegrand (r : Real -> Real) (s : Complex) (x : Real) : Complex :=
  (r x : Complex) * (x : Complex) ^ (-s - 1)

/-- The analytic hypotheses for the grand RH criterion.
They require the paired L-function's log-derivative and zero transform. -/
structure GrandRobinAdmissible {coefficients zeros : Type u}
    (d : GrandRobinDatum coefficients zeros) : Prop where
  primePower_pos : forall i, 1 <= d.primePower i
  primePowers_locallyFinite : forall t : Real,
    Set.Finite {i : coefficients | (d.primePower i : Real) < t}
  dirichlet_summable : forall r : Real, 1 < r ->
    Summable (fun i => norm (d.coefficient i) * (d.primePower i : Real) ^ (-r))
  analytic : AnalyticOnNhd Complex d.poleRemoved {s : Complex | (1 / 2 : Real) < s.re}
  nonzero_at_two : Not (d.poleRemoved (2 : Complex) = 0)
  logDeriv_eq : forall s : Complex, 1 < s.re ->
    logDeriv d.poleRemoved s = (d.poleOrder : Complex) / (s - 1) -
      tsum (fun i => (d.coefficient i : Complex) * (d.primePower i : Complex) ^ (-s))
  zero_in_strip : forall i, And (0 < (d.zero i).re) ((d.zero i).re < 1)
  is_zero : forall i, d.poleRemoved (d.zero i) = 0
  conjugation : forall i, d.zero (d.conjugateIndex i) = (starRingEnd Complex) (d.zero i)
  reflection : forall s : Complex, 0 < s.re -> s.re < 1 ->
    d.poleRemoved s = 0 -> d.poleRemoved (1 - s) = 0
  zero_series_summable :
    Summable (fun i => (norm (d.zero i * (d.zero i + 1))) ^ (-1 : Int))
  remainder_continuous : ContinuousOn (triangularPrimePowerRemainder d) (Set.Ioi 1)
  remainder_measurable : Measurable (triangularPrimePowerRemainder d)
  error_measurable : Measurable d.error
  remainder_integrable : forall s : Complex, 1 < s.re ->
    MeasureTheory.Integrable (grandMellinIntegrand (triangularPrimePowerRemainder d) s)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
  error_integrable : forall s : Complex, 1 < s.re ->
    MeasureTheory.Integrable (grandMellinIntegrand d.error s)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
  mellin_identity : forall s : Complex, 1 < s.re ->
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
        (grandMellinIntegrand (triangularPrimePowerRemainder d) s) =
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
        (grandMellinIntegrand d.error s) +
        tsum (fun i => 1 / (s - d.zero i) + 1 / d.zero i) / (s * (s + 1))
  error_bound : exists c : Real, forall x : Real, 1 < x -> d.error x <= c * Real.sqrt x

/-- The datum uses the analytic properties of the paired L-function.
Pairing and removing a pure imaginary norm twist preserve the set of
real parts of zeros in the open strip. -/
structure GrandRobinRealization {coefficients zeros : Type u}
    (L : Complex -> Complex) (d : GrandRobinDatum coefficients zeros) : Prop where
  admissible : GrandRobinAdmissible d
  zeroRealParts : forall r : Real, 0 < r -> r < 1 ->
    ((exists s : Complex, And (s.re = r) (L s = 0)) <->
      (exists s : Complex, And (s.re = r) (d.poleRemoved s = 0)))

/-- Every zero of the paired L-function in the open strip is on the critical line. -/
private def GrandRobinRH {coefficients zeros : Type u} (d : GrandRobinDatum coefficients zeros) : Prop :=
  forall s : Complex, 0 < s.re -> s.re < 1 -> d.poleRemoved s = 0 -> s.re = 1 / 2

/-- The signed triangular prime-power remainder satisfies an eventual square-root bound. -/
def GrandRobinBound {coefficients zeros : Type u}
    (d : GrandRobinDatum coefficients zeros) : Prop :=
  exists cutoff c : Real, 1 <= cutoff /\
    forall x : Real, cutoff <= x -> triangularPrimePowerRemainder d x <= c * Real.sqrt x

private theorem grandRobinRH_iff_grandRobinBound {coefficients zeros : Type u}
    [Countable coefficients] [Countable zeros] {d : GrandRobinDatum coefficients zeros}
    (h : GrandRobinAdmissible d) : GrandRobinRH d <-> GrandRobinBound d := by
  constructor
  case mp =>
    intro hRH
    have hLine (i : zeros) : (d.zero i).re = 1 / 2 :=
      hRH (d.zero i) (h.zero_in_strip i).1 (h.zero_in_strip i).2 (h.is_zero i)
    have hZero (i : zeros) : Not (d.zero i = 0) := Complex.ne_zero_of_re_pos (h.zero_in_strip i).1
    have hZeroAdd (i : zeros) : Not (d.zero i + 1 = 0) := by
      apply Complex.ne_zero_of_re_pos
      rw [Complex.add_re, Complex.one_re]
      exact add_pos (h.zero_in_strip i).1 zero_lt_one
    have hMeas : Measurable (triangularPrimePowerRemainder d) := h.remainder_measurable
    choose c hc using h.error_bound
    refine Exists.intro 2 (Exists.intro (c + 2 * tsum (fun i =>
      (norm (d.zero i * (d.zero i + 1))) ^ (-1 : Int))) (And.intro (by norm_num) ?_))
    intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx
    exact triangularSquareRootBound_of_canonicalMellin d.zero d.conjugateIndex
      h.conjugation hMeas h.error_measurable h.remainder_continuous
      (fun i => le_of_eq (hLine i)) hZero hZeroAdd h.zero_series_summable
      h.remainder_integrable h.error_integrable h.mellin_identity hc hx1
  case mpr =>
    intro hBound s hs0 hs1 hs
    choose cutoff c hCutoff using hBound
    have ha (i : coefficients) : 1 <= (d.primePower i : Real) := by
      exact_mod_cast h.primePower_pos i
    have hDirichlet (t : Complex) (ht : 1 < t.re) :
        logDeriv d.poleRemoved t = ((d.poleOrder : Real) : Complex) / (t - 1) -
          tsum (fun i => (d.coefficient i : Complex) *
            ((d.primePower i : Real) : Complex) ^ (-t)) := by
      simpa only [Complex.ofReal_natCast] using h.logDeriv_eq t ht
    have hRight (t : Complex) (ht : (1 / 2 : Real) < t.re) : Not (d.poleRemoved t = 0) :=
      ne_zero_of_eventual_triangularSquareRootBound (fun i => (d.primePower i : Real))
        d.coefficient (d.poleOrder : Real) ha h.primePowers_locallyFinite h.dirichlet_summable
        h.analytic h.nonzero_at_two hDirichlet hCutoff.1 hCutoff.2 ht
    by_contra hLine
    cases lt_or_gt_of_ne hLine with
    | inl hLeft =>
      have hReflected : (1 / 2 : Real) < (1 - s).re := by
        rw [Complex.sub_re, Complex.one_re]
        linarith only [hLeft]
      exact hRight (1 - s) hReflected (h.reflection s hs0 hs1 hs)
    | inr hGreater => exact hRight s hGreater hs

/-- The criterion for the family of original L-functions represented by the analytic data. -/
theorem grandRobinFamilyCriterion {index coefficients zeros : Type u}
    [Countable coefficients] [Countable zeros]
    (automorphicL : index -> Complex -> Complex)
    (family : index -> GrandRobinDatum coefficients zeros)
    (realizes : forall pi, GrandRobinRealization (automorphicL pi) (family pi)) :
    GrandRH automorphicL <-> (forall pi, GrandRobinBound (family pi)) := by
  have hTransfer : GrandRH automorphicL <-> (forall pi, GrandRobinRH (family pi)) := by
    constructor
    case mp =>
      intro hRH pi s hs0 hs1 hs
      have hExists := (realizes pi).zeroRealParts s.re hs0 hs1 |>.mpr
        (Exists.intro s (And.intro rfl hs))
      choose t ht using hExists
      have ht0 : 0 < t.re := by simpa only [ht.1] using hs0
      have ht1 : t.re < 1 := by simpa only [ht.1] using hs1
      exact ht.1.symm.trans (hRH pi t ht0 ht1 ht.2)
    case mpr =>
      intro hRH pi s hs0 hs1 hs
      have hExists := (realizes pi).zeroRealParts s.re hs0 hs1 |>.mp
        (Exists.intro s (And.intro rfl hs))
      choose t ht using hExists
      have ht0 : 0 < t.re := by simpa only [ht.1] using hs0
      have ht1 : t.re < 1 := by simpa only [ht.1] using hs1
      exact ht.1.symm.trans (hRH pi t ht0 ht1 ht.2)
  exact hTransfer.trans (forall_congr' (fun pi =>
    grandRobinRH_iff_grandRobinBound (realizes pi).admissible))

end Robin1984.GRH
