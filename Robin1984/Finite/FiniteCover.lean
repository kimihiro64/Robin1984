import Robin1984.Finite.FiniteRowCertificate
/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin (1984) supplies the exceptional cutoff and finite proof obligation.
- Formalization note: The rational certificate formats, interval partition, tangent argument, and exact startup verification are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Chaining the finite log-height intervals

`RobinFiniteCover lo hi rows` states that the rows form a gap-free chain from
`lo` to `hi`, with every row ordered from its lower to its upper endpoint.
The recursive definition is decidable, so a generated list can be checked by
the Lean kernel.

`RobinFiniteCover.exists_row` locates the certificate row containing a real
log-height. `nativeRobinInequality_of_finite_cover` then applies that row's
soundness theorem to prove Robin's inequality for any `n > 5040` whose
`log n` lies in the covered range.
-/

namespace Robin1984

def RobinFiniteCover (lo hi : Rat) : List RobinFiniteRow -> Prop
  | [] => lo = hi
  | r :: rs => And (lo = r.lo) (And (r.lo <= r.hi) (RobinFiniteCover r.hi hi rs))

instance robinFiniteCoverDecidable (lo hi : Rat) (rs : List RobinFiniteRow) :
    Decidable (RobinFiniteCover lo hi rs) :=
  match rs with
  | [] => inferInstanceAs (Decidable (lo = hi))
  | r :: tail => by
    letI := robinFiniteCoverDecidable r.hi hi tail
    exact inferInstanceAs (Decidable (And _ (And _ _)))


theorem RobinFiniteCover.exists_row {lo hi : Rat} {rs : List RobinFiniteRow}
    (h : RobinFiniteCover lo hi rs) {H : Real} (hLo : (lo : Real) <= H) (hHi : H < (hi : Real)) :
    Exists fun r : RobinFiniteRow =>
      And (Membership.mem rs r) (And ((r.lo : Real) <= H) (H <= (r.hi : Real))) := by
  induction rs generalizing lo with
  | nil =>
    change lo = hi at h
    subst lo
    exact False.elim (not_lt_of_ge hLo hHi)
  | cons r tail ih =>
    change And (lo = r.lo) (And (r.lo <= r.hi) (RobinFiniteCover r.hi hi tail)) at h
    by_cases hSplit : H <= (r.hi : Real)
    . refine Exists.intro r (And.intro (by simp) (And.intro ?_ hSplit))
      rw [<- h.1]
      exact hLo
    . choose s hs using ih h.2.2 (le_of_lt (lt_of_not_ge hSplit))
      exact Exists.intro s (And.intro (List.mem_cons_of_mem r hs.1) hs.2)

theorem nativeRobinInequality_of_finite_cover {lo hi : Rat} {rs : List RobinFiniteRow}
    (hCover : RobinFiniteCover lo hi rs)
    (hRows : forall r, Membership.mem rs r -> RobinFiniteRowChecks r)
    {n : Nat} (hn : 5040 < n)
    (hLo : (lo : Real) <= Real.log (n : Real))
    (hHi : Real.log (n : Real) < (hi : Real)) :
    Robin1984.Core.NativeRobinInequality n := by
  choose r hr using hCover.exists_row hLo hHi
  exact (hRows r hr.1).sound hn hr.2.1 hr.2.2

end Robin1984
