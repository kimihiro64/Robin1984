import Robin1984.Finite.Certificates.AllRows
import Robin1984.Finite.RobinFiniteStartupComplete
import Robin1984.Finite.RobinTangentExplicitCutoff
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# The complete finite range below the analytic Robin cutoff

Every integer is covered: the startup proof handles 5040 < n < 720720,
and the certified tangent intervals handle 720720 <= n with log n < 74500.
-/

namespace Robin1984

theorem nativeRobinInequality_finite_log {n : Nat} (hn : 5040 < n)
    (hUpper : Real.log (n : Real) < 74500) :
    Robin1984.Core.NativeRobinInequality n := by
  by_cases hSmall : n < 720720
  . exact nativeRobinInequality_finite_startup hn hSmall
  have hLower : 720720 <= n := le_of_not_gt hSmall
  have hLog : Real.log (720720 : Real) <= Real.log (n : Real) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hLower)
  have hLo : (336 : Real) / 25 <= Real.log (n : Real) :=
    rational_336_div_25_lt_log_720720.le.trans hLog
  have hHi : Real.log (n : Real) < (37283397387 : Real) / 500000 := by
    calc
      Real.log (n : Real) < 74500 := hUpper
      _ < (37283397387 : Real) / 500000 := by norm_num
  apply nativeRobinInequality_of_finite_cover robinFiniteRows_cover robinFiniteRows_checks hn
  . convert hLo using 1 <;> norm_num
  . simpa using hHi

end Robin1984
