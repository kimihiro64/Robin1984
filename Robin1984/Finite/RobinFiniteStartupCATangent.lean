import Robin1984.Arithmetic.Definitions
import Robin1984.Arithmetic.RobinBounds
import Robin1984.ColossallyAbundant.CAProfile
import Robin1984.Finite.RobinTangentStartup
import Robin1984.Finite.RobinTangentStartupComplete
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Common CA tangent on the finite Robin startup interval

The common `5040`/`55440` CA parameter gives one logarithmic abundancy
tangent.  After the substitution `y = log n`, the gap between the Robin bound
and that tangent is concave, so its minimum on a closed interval occurs at an
endpoint.
-/

namespace Robin1984

open Set

noncomputable section

/-- For a nonnegative slope, `log (log y) - eps * y` is concave on `y > 1`.
This is the exact transformed gap between the logarithmic Robin bound and a
fixed CA tangent, up to an additive constant. -/
theorem concaveOn_log_log_sub_mul
    {eps : Real} (hEps : 0 <= eps) :
    ConcaveOn Real (Set.Ioi (1 : Real)) (fun y : Real =>
      Real.log (Real.log y) - eps * y) := by
  have hImage :
      Real.log '' Set.Ioi (1 : Real) = Set.Ioi (0 : Real) := by
    ext z
    constructor
    case mp =>
      intro hz
      choose y hy hyEq using hz
      rw [<- hyEq]
      exact Real.log_pos hy
    case mpr =>
      intro hz
      apply Exists.intro (Real.exp z)
      have hExpMem : Membership.mem (Set.Ioi (1 : Real)) (Real.exp z) := by
        change 1 < Real.exp z
        simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hz
      exact And.intro hExpMem (Real.log_exp z)
  have hInner :
      ConcaveOn Real (Set.Ioi (1 : Real)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn.subset
      (Set.Ioi_subset_Ioi (by norm_num : (0 : Real) <= 1))
      (convex_Ioi 1)
  have hOuter :
      ConcaveOn Real (Real.log '' Set.Ioi (1 : Real)) Real.log := by
    rw [hImage]
    exact strictConcaveOn_log_Ioi.concaveOn
  have hOuterMono :
      MonotoneOn Real.log (Real.log '' Set.Ioi (1 : Real)) := by
    rw [hImage]
    exact Real.strictMonoOn_log.monotoneOn
  have hComposed :
      ConcaveOn Real (Set.Ioi (1 : Real)) (fun y : Real =>
        Real.log (Real.log y)) := by
    have hRaw := hOuter.comp hInner hOuterMono
    change ConcaveOn Real (Set.Ioi (1 : Real))
      (fun y : Real => Real.log (Real.log y)) at hRaw
    exact hRaw
  have hLinear :
      ConvexOn Real (Set.Ioi (1 : Real)) (fun y : Real => eps * y) := by
    simpa only [id_eq, smul_eq_mul] using
      (convexOn_id (convex_Ioi (1 : Real))).smul hEps
  exact hComposed.sub hLinear

/-- The transformed CA-tangent gap is bounded below by the smaller endpoint
value on every closed subinterval of `y > 1`. -/
theorem min_logLogCATangentEndpoint_le
    {eps a b y : Real} (hEps : 0 <= eps)
    (ha : 1 < a) (hab : a <= b)
    (hy : Membership.mem (Set.Icc a b) y) :
    min (Real.log (Real.log a) - eps * a)
          (Real.log (Real.log b) - eps * b) <=
      Real.log (Real.log y) - eps * y := by
  have hConcave := concaveOn_log_log_sub_mul hEps
  exact hConcave.min_le_of_mem_Icc ha (ha.trans_le hab) hy

/-- Exact logarithmic gap between Robin's bound and the common `5040` CA
tangent, written in the variable `y = log n`. -/
def ca5040RobinLogTangentGapAtLog (y : Real) : Real :=
  Real.eulerMascheroniConstant + Real.log (Real.log y) -
    Real.log (abundancy 5040) -
      ca5040To55440Cutoff * (y - Real.log (5040 : Real))

/-- The certified CA maximizer places every positive integer below the common
`5040` logarithmic tangent. -/
theorem log_abundancy_sub_commonStartupCutoff_log_le_5040
    {n : Nat} (hn : 1 < n) :
    Real.log (abundancy n) -
          ca5040To55440Cutoff * Real.log (n : Real) <=
      Real.log (abundancy 5040) -
        ca5040To55440Cutoff * Real.log (5040 : Real) := by
  have hMax :=
    colossallyAbundantWith_5040_at_cutoff.logObjective_max hn
  rw [caLogObjective_eq_log_abundancy_sub
      (eps := ca5040To55440Cutoff) (n := n) (by omega),
    caLogObjective_eq_log_abundancy_sub
      (eps := ca5040To55440Cutoff) (n := 5040) (by norm_num)] at hMax
  exact hMax

/-- Positivity of the two transformed endpoint gaps proves Robin throughout
the intervening integer interval.  The only arithmetic input is the already
proved common `5040` CA maximizer. -/
theorem nativeRobinInequality_of_commonStartupTangentEndpoints
    {L U n : Nat}
    (hLCut : 5040 < L) (hLU : L <= U)
    (hLn : L <= n) (hnU : n <= U)
    (hLeft :
      0 < ca5040RobinLogTangentGapAtLog (Real.log (L : Real)))
    (hRight :
      0 < ca5040RobinLogTangentGapAtLog (Real.log (U : Real))) :
    Robin1984.Core.NativeRobinInequality n := by
  let eps : Real := ca5040To55440Cutoff
  let a : Real := Real.log (L : Real)
  let b : Real := Real.log (U : Real)
  let y : Real := Real.log (n : Real)
  let c : Real :=
    Real.eulerMascheroniConstant - Real.log (abundancy 5040) +
      eps * Real.log (5040 : Real)
  have hNcut : 5040 < n := lt_of_lt_of_le hLCut hLn
  have hNOne : 1 < n := by omega
  have hEps : 0 <= eps :=
    (colossallyAbundantWith_5040_at_cutoff.eps_pos).le
  have hLPos : (0 : Real) < (L : Real) := by positivity
  have hNPos : (0 : Real) < (n : Real) := by positivity
  have ha : 1 < a := by
    dsimp only [a]
    rw [Real.lt_log_iff_exp_lt hLPos]
    exact Real.exp_one_lt_three.trans
      (by exact_mod_cast (lt_trans (by norm_num : 3 < 5040) hLCut))
  have hab : a <= b := by
    dsimp only [a, b]
    exact Real.log_le_log hLPos (by exact_mod_cast hLU)
  have hy : Membership.mem (Set.Icc a b) y := by
    apply And.intro
    case left =>
      dsimp only [a, y]
      exact Real.log_le_log hLPos (by exact_mod_cast hLn)
    case right =>
      dsimp only [b, y]
      exact Real.log_le_log hNPos (by exact_mod_cast hnU)
  have hEndpoint := min_logLogCATangentEndpoint_le hEps ha hab hy
  have hLeftExpanded :
      0 < c + (Real.log (Real.log a) - eps * a) := by
    dsimp only [c, a, eps]
    unfold ca5040RobinLogTangentGapAtLog at hLeft
    linarith
  have hRightExpanded :
      0 < c + (Real.log (Real.log b) - eps * b) := by
    dsimp only [c, b, eps]
    unfold ca5040RobinLogTangentGapAtLog at hRight
    linarith
  have hMinPositive :
      0 < c + min
        (Real.log (Real.log a) - eps * a)
        (Real.log (Real.log b) - eps * b) := by
    rcases le_total
        (Real.log (Real.log a) - eps * a)
        (Real.log (Real.log b) - eps * b) with hAB | hBA
    case inl =>
      rw [min_eq_left hAB]
      exact hLeftExpanded
    case inr =>
      rw [min_eq_right hBA]
      exact hRightExpanded
  have hGapPositive :
      0 < c + (Real.log (Real.log y) - eps * y) := by
    linarith
  have hCATangent :=
    log_abundancy_sub_commonStartupCutoff_log_le_5040 hNOne
  have hLogRobin :
      Real.log (abundancy n) <
        Real.eulerMascheroniConstant +
          Real.log (Real.log (Real.log (n : Real))) := by
    dsimp only [c, y, eps] at hGapPositive
    linarith
  have hRobinLog := log_robinBoundRatio_eq_of_cutoff hNcut
  have hLogComparison :
      Real.log (abundancy n) < Real.log (robinBoundRatio n) := by
    rw [hRobinLog]
    exact hLogRobin
  have hAbPos : 0 < abundancy n := abundancy_pos (by omega)
  have hBoundPos : 0 < robinBoundRatio n :=
    robinBoundRatio_pos_of_cutoff hNcut
  have hRatio : abundancy n < robinBoundRatio n := by
    have hExp := Real.exp_lt_exp.mpr hLogComparison
    rw [Real.exp_log hAbPos, Real.exp_log hBoundPos] at hExp
    exact hExp
  exact
    (nativeRobinInequality_iff_abundancy_lt_bound (by omega)).mpr hRatio

end

end Robin1984
