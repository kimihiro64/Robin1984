import Robin1984.Finite.RobinTangentStartupComplete
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Constructive tangent-CA coverage equivalence for Robin

Using the certified startup packet, this module proves that Robin on a
finite startup interval plus Robin on every later tangent CA support is exactly
Robin on all integers above `5040`.
-/

namespace Robin1984

noncomputable section


/-- Exact finite-startup plus tangent-support condition at an eventual
cutoff endpoint `N`. -/
def RobinFiniteTangentCACoverage (N : Nat) : Prop :=
  And
    (forall n : Nat, 5040 < n -> n < N ->
      Robin1984.Core.NativeRobinInequality n)
    (forall n q : Nat, 5040 < n -> N <= n ->
      IsColossallyAbundantWith q (robinFrontierCutoff n) ->
        Robin1984.Core.NativeRobinInequality q)

/-- For any certified eventual endpoint, finite startup plus all later tangent
CA supports is equivalent to Robin's inequality for every integer. -/
theorem nativeRobinInequalityAll_iff_finiteTangentCACoverage
    {N : Nat}
    (hN : forall n : Nat, N <= n ->
      robinFrontierCutoff n < ca5040To55440Cutoff) :
    Robin1984.Core.NativeRobinInequalityAll <->
      RobinFiniteTangentCACoverage N := by
  constructor
  case mp =>
    intro hRobin
    exact And.intro
      (fun n hn _hnN => hRobin n hn)
      (fun n q hn hnN hqCA =>
        hRobin q
          (tangentCAMaximizer_above_5040_at_startup_cutoff
            hn (hN n hnN) hqCA))
  case mpr =>
    intro hCoverage n hn
    by_cases hnN : n < N
    case pos =>
      exact hCoverage.1 n hn hnN
    case neg =>
      have hNn : N <= n := Nat.le_of_not_gt hnN
      have hLambdaPos : 0 < robinFrontierCutoff n :=
        robinFrontierCutoff_pos_of_cutoff hn
      choose q hqCA using exists_colossallyAbundantWith hLambdaPos
      have hqCut : 5040 < q :=
        tangentCAMaximizer_above_5040_at_startup_cutoff
          hn (hN n hNn) hqCA
      have hqRobin : Robin1984.Core.NativeRobinInequality q :=
        hCoverage.2 n q hn hNn hqCA
      exact nativeRobinInequality_of_tangent_colossallyAbundant
        hn hqCut hqCA hqRobin


end

end Robin1984
