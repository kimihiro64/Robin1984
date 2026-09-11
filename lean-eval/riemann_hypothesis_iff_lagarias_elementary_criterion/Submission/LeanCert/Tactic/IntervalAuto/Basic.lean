/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Submission.LeanCert.Tactic.IntervalAuto.Types
import Submission.LeanCert.Tactic.IntervalAuto.Norm
import Submission.LeanCert.Tactic.IntervalAuto.Extract
import Submission.LeanCert.Tactic.IntervalAuto.Parse
import Submission.LeanCert.Tactic.IntervalAuto.Diagnostic
import Submission.LeanCert.Tactic.IntervalAuto.ProveCommon

/-!
# Interval Arithmetic Tactics - Infrastructure

This module provides infrastructure for the interval arithmetic tactics:
- `Types`: Core data structures
- `Norm`: Goal normalization
- `Extract`: Rational extraction
- `Parse`: Goal parsing
- `Diagnostic`: Error reporting
- `ProveCommon`: Shared utilities

The main tactics are in `LeanCert.Tactic.IntervalAuto`.
-/
