import ChallengeDeps
import Submission.Helpers

open LeanEval.NumberTheory
open scoped ArithmeticFunction.sigma

namespace Submission

theorem riemann_hypothesis_iff_lagarias_elementary_criterion :
    RiemannHypothesis <-> LagariasElementaryCriterion := by
  change RiemannHypothesis <-> Robin1984.LagariasElementaryCriterion
  exact Robin1984.riemannHypothesis_iff_lagariasElementaryCriterion

end Submission
