import Robin1984.GRH.TriangularHadamard

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

/-- Grand RH says that every nontrivial zero of every automorphic
L-function has real part one half. The index enumerates the L-functions
in the family. For the full hypothesis it ranges over all automorphic
L-functions in the usual normalization. -/
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

/-- The completed formulation of Grand RH: every automorphic L-function
has all of its nontrivial zeros on the critical line. The full hypothesis
uses an index ranging over every automorphic L-function. Here the completed
functions represent the nontrivial zeros after normalization and pole removal. -/
def CompletedFamilyRH {Representation : Type*}
    (completedL : Representation -> Complex -> Complex) : Prop :=
  forall pi s, completedL pi s = 0 -> s.re = (1 : Real) / 2

/-- A nonvanishing completion factor on the right and the completed
functional equation identify the full zero condition with right-half-plane
nonvanishing of the functions used in the Euler-product criterion. -/
theorem completedFamilyRH_iff_right_nonvanishing {Representation : Type*}
    (completedL poleRemoved completionFactor : Representation -> Complex -> Complex)
    (dual : Representation -> Representation)
    (functionalEquationFactor : Representation -> Complex -> Complex)
    (completion : forall pi s, (1 : Real) / 2 < s.re ->
      completedL pi s = completionFactor pi s * poleRemoved pi s)
    (completion_ne_zero : forall pi s, (1 : Real) / 2 < s.re ->
      Not (completionFactor pi s = 0))
    (functionalEquation : forall pi s,
      completedL (dual pi) (1 - s) = functionalEquationFactor pi s * completedL pi s) :
    CompletedFamilyRH completedL <->
      forall pi s, (1 : Real) / 2 < s.re -> Not (poleRemoved pi s = 0) := by
  constructor
  case mp =>
    intro rh pi s hs hzero
    have hcompleted : completedL pi s = 0 := by rw [completion pi s hs, hzero, mul_zero]
    have hline := rh pi s hcompleted
    linarith
  case mpr =>
    intro hnonzero
    have completed_ne_zero : forall pi s, (1 : Real) / 2 < s.re ->
        Not (completedL pi s = 0) := by
      intro pi s hs
      rw [completion pi s hs]
      exact mul_ne_zero (completion_ne_zero pi s hs) (hnonzero pi s hs)
    intro pi s hzero
    have hr : s.re <= (1 : Real) / 2 :=
      le_of_not_gt (fun hs => completed_ne_zero pi s hs hzero)
    have hl : (1 : Real) / 2 <= s.re := by
      apply le_of_not_gt
      intro hs
      have hreflect : (1 : Real) / 2 < (1 - s : Complex).re := by
        rw [Complex.sub_re, Complex.one_re]
        linarith
      have hreflect_zero : completedL (dual pi) (1 - s) = 0 := by
        rw [functionalEquation pi s, hzero, mul_zero]
      exact completed_ne_zero (dual pi) (1 - s) hreflect hreflect_zero
    exact le_antisymm hr hl

/-- The prime-power coefficients and pole removal for a standard L-function
paired with its contragredient. -/
structure GrandRobinEulerData (powers : Type*) where
  normPower : powers -> Real
  coefficient : powers -> Real
  poleOrder : Real
  poleRemoved : Complex -> Complex

/-- The signed triangular prime-power sum is bounded above by a constant
times the square root of the cutoff, for all sufficiently large cutoffs. -/
def GrandRobinTriangularBound {powers : Type*}
    (d : GrandRobinEulerData powers) : Prop :=
  exists cutoff C : Real, 1 <= cutoff /\
    forall x : Real, cutoff <= x ->
      triangularRemainder d.normPower d.coefficient d.poleOrder x <= C * Real.sqrt x

/-- Analytic input about the Euler product and zeros of the
pole-cleared uncompleted function. The zero list omits zero and minus one,
whose multiplicities appear separately in the logarithmic derivative. -/
structure GrandRobinEulerAnalytic {powers zeros : Type*} (d : GrandRobinEulerData powers)
    (rho : zeros -> Complex) : Prop where
  normPower_ge_one : forall i, 1 <= d.normPower i
  locallyFinite : forall T : Real, Set.Finite {i : powers | d.normPower i < T}
  summableEuler : forall r : Real, 1 < r ->
    Summable (fun i => norm (d.coefficient i) * (d.normPower i) ^ (-r))
  analytic : AnalyticOnNhd Complex d.poleRemoved {s : Complex | (1 / 2 : Real) < s.re}
  nonzero_at_two : Not (d.poleRemoved (2 : Complex) = 0)
  euler_logDeriv : forall s : Complex, 1 < s.re ->
    logDeriv d.poleRemoved s = (d.poleOrder : Complex) / (s - 1) -
      tsum (fun i => (d.coefficient i : Complex) * (d.normPower i : Complex) ^ (-s))
  zero_is_zero : forall i, d.poleRemoved (rho i) = 0
  zero_ne_zero : forall i, Not (rho i = 0)
  zero_ne_neg_one : forall i, Not (rho i + 1 = 0)
  summableZeros : Summable (fun i => (norm (rho i * (rho i + 1))) ^ (-1 : Int))
  hadamard_logDeriv : exists (beta : Complex) (m0 mNeg : Real),
    forall s : Complex, 1 < s.re -> logDeriv d.poleRemoved s =
      beta + (m0 : Complex) / s + (mNeg : Complex) * (1 / (s + 1) - 1) +
        tsum (fun i => 1 / (s - rho i) + 1 / rho i)

/-- For paired analytic Euler data, the triangular inequality is equivalent
to nonvanishing on the right of the critical line. -/
theorem grandRobinTriangularBound_iff_right_nonvanishing
    {powers zeros : Type*} [Countable powers] [Countable zeros]
    {d : GrandRobinEulerData powers} {rho : zeros -> Complex}
    (h : GrandRobinEulerAnalytic d rho) :
    GrandRobinTriangularBound d <->
      forall s : Complex, (1 / 2 : Real) < s.re -> Not (d.poleRemoved s = 0) := by
  constructor
  case mp =>
    intro hB s hs
    choose T C hCut using hB
    exact ne_zero_of_eventual_triangularSquareRootBound
      d.normPower d.coefficient d.poleOrder h.normPower_ge_one h.locallyFinite
      h.summableEuler h.analytic h.nonzero_at_two h.euler_logDeriv hCut.1 hCut.2 hs
  case mpr =>
    intro hRight
    have hRho (i : zeros) : (rho i).re <= 1 / 2 :=
      le_of_not_gt (fun hr => hRight (rho i) hr (h.zero_is_zero i))
    choose beta m0 mNeg hHadamard using h.hadamard_logDeriv
    have hCont :=
      continuousOn_triangularRemainder d.normPower d.coefficient d.poleOrder h.locallyFinite
    choose C hC using
      triangularSquareRootBound_of_hadamard d.normPower d.coefficient d.poleOrder d.poleRemoved
        rho beta m0 mNeg h.normPower_ge_one h.summableEuler h.euler_logDeriv
        hRho h.zero_ne_zero h.zero_ne_neg_one h.summableZeros hHadamard hCont
    exact Exists.intro 2 (Exists.intro C
      (And.intro (by norm_num) (fun x hx => hC x (lt_of_lt_of_le (by norm_num) hx))))

/-- The all-members zero condition for completed L-functions is equivalent
to the triangular criterion for their paired Euler data when the completed
functional equation and nonvanishing completion factors are supplied. -/
theorem grandRobinCompletedCriterion
    {Representation : Type*} {powers zeros : Representation -> Type*}
    [forall pi, Countable (powers pi)] [forall pi, Countable (zeros pi)]
    (completedL completionFactor equationFactor : Representation -> Complex -> Complex)
    (dual : Representation -> Representation)
    (data : forall pi, GrandRobinEulerData (powers pi))
    (rho : forall pi, zeros pi -> Complex)
    (hData : forall pi, GrandRobinEulerAnalytic (data pi) (rho pi))
    (hCompletion : forall pi s, (1 / 2 : Real) < s.re ->
      completedL pi s * completedL (dual pi) s =
        completionFactor pi s * (data pi).poleRemoved s)
    (hFactor : forall pi s, (1 / 2 : Real) < s.re -> Not (completionFactor pi s = 0))
    (hEquation : forall pi s, completedL (dual pi) (1 - s) =
      equationFactor pi s * completedL pi s) :
    CompletedFamilyRH completedL <-> forall pi, GrandRobinTriangularBound (data pi) := by
  have hCompleted := completedFamilyRH_iff_right_nonvanishing
    completedL completedL (fun _ _ => 1) dual equationFactor
    (fun _ _ _ => (one_mul _).symm) (fun _ _ _ => one_ne_zero) hEquation
  rw [hCompleted]
  constructor
  case mp =>
    intro hRH pi
    apply (grandRobinTriangularBound_iff_right_nonvanishing (hData pi)).mpr
    intro s hs hn
    have hProduct := hCompletion pi s hs
    rw [hn, mul_zero] at hProduct
    exact mul_ne_zero (hRH pi s hs) (hRH (dual pi) s hs) hProduct
  case mpr =>
    intro hBounds pi s hs hZero
    have hProduct := hCompletion pi s hs
    rw [hZero, zero_mul] at hProduct
    have hPair := (grandRobinTriangularBound_iff_right_nonvanishing (hData pi)).mp (hBounds pi) s hs
    exact mul_ne_zero (hFactor pi s hs) hPair hProduct.symm

/-- The entire order-one bound supplies the Hadamard expansion and its
zero weights for the completed-family triangular criterion. -/
theorem grandRobinCompletedCriterion_of_entireOrder
    {Representation : Type*} {powers : Representation -> Type*}
    [forall pi, Countable (powers pi)]
    (completedL completionFactor equationFactor : Representation -> Complex -> Complex)
    (dual : Representation -> Representation)
    (data : forall pi, GrandRobinEulerData (powers pi))
    (hNorm : forall pi i, 1 <= (data pi).normPower i)
    (hFinite : forall pi T, Set.Finite {i : powers pi | (data pi).normPower i < T})
    (hSummable : forall pi (r : Real), 1 < r ->
      Summable (fun i => norm ((data pi).coefficient i) * ((data pi).normPower i) ^ (-r)))
    (hOrder : forall pi, Complex.Hadamard.EntireOfOrderAtMost 1 (data pi).poleRemoved)
    (hNonzero : forall pi s, 1 < s.re -> Not ((data pi).poleRemoved s = 0))
    (hEuler : forall pi s, 1 < s.re ->
      logDeriv (data pi).poleRemoved s = ((data pi).poleOrder : Complex) / (s - 1) -
        tsum (fun i => ((data pi).coefficient i : Complex) *
          ((data pi).normPower i : Complex) ^ (-s)))
    (hCompletion : forall pi s, (1 / 2 : Real) < s.re ->
      completedL pi s * completedL (dual pi) s =
        completionFactor pi s * (data pi).poleRemoved s)
    (hFactor : forall pi s, (1 / 2 : Real) < s.re -> Not (completionFactor pi s = 0))
    (hEquation : forall pi s, completedL (dual pi) (1 - s) =
      equationFactor pi s * completedL pi s) :
    CompletedFamilyRH completedL <-> forall pi, GrandRobinTriangularBound (data pi) := by
  have hNonzeroTwo (pi : Representation) : Not ((data pi).poleRemoved (2 : Complex) = 0) :=
    hNonzero pi 2 (by norm_num)
  have hNT (pi : Representation) : exists z, Not ((data pi).poleRemoved z = 0) :=
    Exists.intro 2 (hNonzeroTwo pi)
  let zs : Representation -> Type := fun pi => regularHadamardZeroIndex (data pi).poleRemoved
  let rho (pi : Representation) : zs pi -> Complex := regularHadamardZero
  let hCount : forall pi, Countable (zs pi) := fun pi => by
    have hc : Countable (entireNonzeroZeroIndex (data pi).poleRemoved) :=
      countable_entireNonzeroZeroIndex (hOrder pi) (hNT pi)
    change Countable (regularHadamardZeroIndex (data pi).poleRemoved)
    infer_instance
  have hData (pi : Representation) : GrandRobinEulerAnalytic (data pi) (rho pi) := by
    refine {
      normPower_ge_one := hNorm pi
      locallyFinite := hFinite pi
      summableEuler := hSummable pi
      analytic := fun z _ => (hOrder pi).differentiable.analyticAt z
      nonzero_at_two := hNonzeroTwo pi
      euler_logDeriv := hEuler pi
      zero_is_zero := fun i => entireNonzeroZero_is_zero (hOrder pi).differentiable i.val
      zero_ne_zero := fun i => i.val.property
      zero_ne_neg_one := fun i => i.property
      summableZeros := summable_regularHadamardZeroWeight (hOrder pi) (hNT pi)
      hadamard_logDeriv := ?_ }
    choose beta m0 mNeg hm using entireOfOrderAtMost_one_logDeriv_regular (hOrder pi) (hNT pi)
    refine Exists.intro beta (Exists.intro (m0 : Real) (Exists.intro (mNeg : Real) ?_))
    intro s hs
    have hS : Not (s = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
    simpa only [Complex.ofReal_natCast] using hm s hS (hNonzero pi s hs)
  exact grandRobinCompletedCriterion completedL completionFactor equationFactor
    dual data rho hData hCompletion hFactor hEquation

end Robin1984.GRH
