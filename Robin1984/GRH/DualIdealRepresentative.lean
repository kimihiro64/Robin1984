import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Clearing denominators in fractional ideals of a number field.
- Formalization note: Clearing a fractional ideal by a rational integer.
- PROVENANCE-END
-/

/-!
# Clearing a fractional ideal by a rational integer

The norm of a principal denominator ideal is an integer in that ideal.
Using this integer as the denominator scales uniformly at all
archimedean places.
-/

open NumberField

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

local notation "R" => RingOfIntegers K
local notation "F" => FractionalIdeal (nonZeroDivisors R) K

/-- A nonzero fractional ideal is made integral by a positive natural
number, viewed inside the number field. -/
theorem exists_integral_natural_multiple (I : F) (hI : Not (I = 0)) :
    exists m : Nat, And (0 < m)
      (exists B : Ideal R, And (Not (B = 0))
        ((B : F) = FractionalIdeal.spanSingleton (nonZeroDivisors R) (m : K) * I)) := by
  let d : R := I.den.val
  let J : Ideal R := Ideal.span {d}
  have hd : Not (d = 0) := mem_nonZeroDivisors_iff_ne_zero.mp I.den.property
  have hJ : Not (J = 0) := by
    intro h
    have hMem : Membership.mem J d := Ideal.subset_span (Set.mem_singleton d)
    rw [h] at hMem
    change Membership.mem (Bot.bot : Ideal R) d at hMem
    exact hd (Ideal.mem_bot.mp hMem)
  let m := Ideal.absNorm J
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h))
  have hMem : Membership.mem J (m : R) := Ideal.absNorm_mem J
  choose c hc using Ideal.mem_span_singleton.mp hMem
  let B : Ideal R := Ideal.span {c} * I.num
  have hCleared : (B : F) = FractionalIdeal.spanSingleton (nonZeroDivisors R) (m : K) * I := by
    unfold B
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
    have hNum : (I.num : F) =
        FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K d) * I :=
      (FractionalIdeal.den_mul_self_eq_num' (nonZeroDivisors R) K I).symm
    rw [hNum, <- mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, <- map_mul]
    have hDom : c * d = (m : R) := (mul_comm c d).trans hc.symm
    rw [hDom, map_natCast]
  have hM0 : Not ((m : K) = 0) := by exact_mod_cast hm.ne'
  have hProd : Not (FractionalIdeal.spanSingleton (nonZeroDivisors R) (m : K) * I = 0) :=
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hM0) hI
  have hB : Not (B = 0) := by
    intro h
    exact hProd (by simpa [h] using hCleared.symm)
  exact Exists.intro m (And.intro hm (Exists.intro B (And.intro hB hCleared)))

end DedekindZeta
