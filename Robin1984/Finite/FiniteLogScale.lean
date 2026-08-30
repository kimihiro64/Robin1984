import Robin1984.Finite.FiniteLogCertificate

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Dyadically scaled rational logarithm bounds

Direct rational logarithm certificates are most efficient when their input
is close to one. These definitions write `q` as `2^k * (q / 2^k)`, combine
certified lower and upper bounds for `log 2` with the bounds for the scaled
argument, and keep the result in exact rational arithmetic.

`robin_log_scaled_bounds` proves that the two computed rationals enclose the
real value `Real.log q` whenever `2^k <= q`.
-/

namespace Robin1984

def robinLogScaledLower (q : Rat) (k N : Nat) : Rat :=
  (k : Rat) * (693147180559945309 / 1000000000000000000) +
    robinLogLower (q / 2^k) N

def robinLogScaledUpper (q : Rat) (k N : Nat) : Rat :=
  (k : Rat) * (693147180559945310 / 1000000000000000000) +
    robinLogUpper (q / 2^k) N

theorem robin_log_scaled_bounds {q : Rat} (k N : Nat) (hq : (2 : Rat)^k <= q) :
    And ((robinLogScaledLower q k N : Real) <= Real.log (q : Real))
      (Real.log (q : Real) <= (robinLogScaledUpper q k N : Real)) := by
  have hp : (0 : Rat) < (2 : Rat)^k := pow_pos (by norm_num) k
  have hz : (1 : Rat) <= q / 2^k := by
    have h := div_le_div_of_nonneg_right hq hp.le
    simpa only [div_self hp.ne'] using h
  have hEq : (2 : Real)^k * ((q / 2^k : Rat) : Real) = (q : Real) := by
    push_cast
    field_simp
  have h := robin_log_bounds_of_dyadic_bracket
    (q := q / 2^k) (r := q / 2^k) k N hz hz hEq.le hEq.ge
  simpa only [robinLogScaledLower, robinLogScaledUpper, Rat.cast_add, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] using h

end Robin1984
