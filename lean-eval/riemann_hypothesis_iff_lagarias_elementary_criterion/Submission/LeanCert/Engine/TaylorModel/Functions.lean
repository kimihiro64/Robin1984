/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Submission.LeanCert.Engine.TaylorModel.Trig
import Submission.LeanCert.Engine.TaylorModel.ExpLog
import Submission.LeanCert.Engine.TaylorModel.Hyperbolic
import Submission.LeanCert.Engine.TaylorModel.Special

/-!
# Taylor Models - Function-Specific Definitions

This file re-exports all function-specific Taylor model definitions.
The implementation is split into:

* `TaylorModel/Trig.lean` - Sin, Cos, Sinc (and future Tan)
* `TaylorModel/ExpLog.lean` - Exp, Log
* `TaylorModel/Hyperbolic.lean` - Sinh, Cosh, Tanh, Atan, Atanh, Asinh
* `TaylorModel/Special.lean` - Erf (and future Sqrt)

## Main definitions (re-exported)

### Trig
* `sinTaylorPoly`, `cosTaylorPoly`, `sincTaylorPoly`
* `tmSin`, `tmCos`, `tmSinc`
* `tmSin_correct`, `tmCos_correct`

### ExpLog
* `expTaylorPoly`, `logTaylorPolyAtCenter`
* `tmExp`, `tmLog`
* `tmExp_correct`, `tmLog_correct`

### Hyperbolic
* `sinhTaylorPoly`, `coshTaylorPoly`, `atanTaylorPoly`, `atanhTaylorPoly`, `asinhTaylorPoly`
* `tmSinh`, `tmCosh`, `tmTanh`, `tmAtan`, `tmAtanh`, `tmAsinh`
* `tmSinh_correct`, `tmCosh_correct`, `tmAtanh_correct`

### Special
* `erfTaylorPoly`
* `tmErf`
-/
