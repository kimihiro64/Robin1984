import Robin1984.Finite.FinitePacketProducts

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Robin's 1984 analytic implication supplies the surrounding mathematical target.
- Formalization note: The exact coefficient normalization, explicit cutoff choices, and proof interfaces in this module are primarily project-authored.
- PROVENANCE-END
-/

/-!
# Bounded exact prime-product certificates

Each numeric block contains at most 1024 integers. The symbolic concatenation
lemma carries the complete prime product to the endpoint without re-running
one monolithic primality computation over the entire prefix.
-/

namespace Robin1984

def robinPrimeBlockProduct (start count : Nat) (f : Nat -> Nat) : Nat :=
  (Finset.range count).prod (fun i => if Nat.Prime (start + i) then f (start + i) else 1)

theorem robinPrimeBlockProduct_add (start a b : Nat) (f : Nat -> Nat) :
    robinPrimeBlockProduct start (a + b) f =
      robinPrimeBlockProduct start a f * robinPrimeBlockProduct (start + a) b f := by
  unfold robinPrimeBlockProduct
  rw [Finset.prod_range_add]
  simp only [Nat.add_assoc]

theorem robinPrimeBlockProduct_eq_primesLE (c : Nat) (f : Nat -> Nat) :
    robinPrimeBlockProduct 0 (c + 1) f = (Nat.primesLE c).prod f := by
  simp only [robinPrimeBlockProduct, Nat.primesLE_eq_filter_range, Finset.prod_filter,
    Nat.zero_add]

structure RobinPrimeProductBlock where
  start : Nat
  count : Nat
  numerator : Nat
  denominator : Nat
  baseProduct : Nat

def RobinPrimeTrial (n : Nat) : Prop :=
  And (2 <= n) (forall d : Fin 318,
    2 <= d.val -> d.val * d.val <= n -> Not (Dvd.dvd d.val n))

instance (n : Nat) : Decidable (RobinPrimeTrial n) :=
  inferInstanceAs (Decidable (And _ _))

theorem robinPrimeTrial_iff {n : Nat} (hn : n <= 100000) :
    RobinPrimeTrial n <-> Nat.Prime n := by
  constructor
  . intro h
    apply Nat.prime_def_le_sqrt.mpr
    refine And.intro h.1 ?_
    intro d hd hds
    have hs : Nat.sqrt n < 318 := Nat.sqrt_lt.mpr (by omega)
    exact h.2 (Fin.mk d (lt_of_le_of_lt hds hs)) hd (Nat.le_sqrt.mp hds)
  . intro h
    refine And.intro h.two_le ?_
    intro d hd hsq
    exact (Nat.prime_def_le_sqrt.mp h).2 d.val hd (Nat.le_sqrt.mpr hsq)

def robinPrimeBlockProductFast (start count : Nat) (f : Nat -> Nat) : Nat :=
  (Finset.range count).prod (fun i => if RobinPrimeTrial (start + i) then f (start + i) else 1)

theorem robinPrimeBlockProductFast_eq {start count : Nat}
    (h : start + count <= 100000) (f : Nat -> Nat) :
    robinPrimeBlockProductFast start count f = robinPrimeBlockProduct start count f := by
  unfold robinPrimeBlockProductFast robinPrimeBlockProduct
  apply Finset.prod_congr rfl
  intro i hi
  have hiLt := Finset.mem_range.mp hi
  simp only [robinPrimeTrial_iff (by omega : start + i <= 100000)]

def RobinPrimeProductBlockChecks (b : RobinPrimeProductBlock) : Prop :=
  And (b.count <= 1024)
    (And (b.start + b.count <= 100000)
    (And (robinPrimeBlockProductFast b.start b.count (fun p => p^2 - 1) = b.numerator)
    (And (robinPrimeBlockProductFast b.start b.count (fun p => p * (p - 1)) = b.denominator)
      (robinPrimeBlockProductFast b.start b.count (fun p => p) = b.baseProduct))))

instance (b : RobinPrimeProductBlock) : Decidable (RobinPrimeProductBlockChecks b) :=
  inferInstanceAs (Decidable (And _ (And _ (And _ (And _ _)))))

theorem RobinPrimeProductBlockChecks.numerator_eq {b : RobinPrimeProductBlock}
    (h : RobinPrimeProductBlockChecks b) :
    robinPrimeBlockProduct b.start b.count (fun p => p^2 - 1) = b.numerator :=
  (robinPrimeBlockProductFast_eq h.2.1 _).symm.trans h.2.2.1

theorem RobinPrimeProductBlockChecks.denominator_eq {b : RobinPrimeProductBlock}
    (h : RobinPrimeProductBlockChecks b) :
    robinPrimeBlockProduct b.start b.count (fun p => p * (p - 1)) = b.denominator :=
  (robinPrimeBlockProductFast_eq h.2.1 _).symm.trans h.2.2.2.1

theorem RobinPrimeProductBlockChecks.baseProduct_eq {b : RobinPrimeProductBlock}
    (h : RobinPrimeProductBlockChecks b) :
    robinPrimeBlockProduct b.start b.count (fun p => p) = b.baseProduct :=
  (robinPrimeBlockProductFast_eq h.2.1 _).symm.trans h.2.2.2.2

def RobinPrimeBlocksCover (lo hi : Nat) : List RobinPrimeProductBlock -> Prop
  | [] => lo = hi
  | b :: bs => And (lo = b.start) (RobinPrimeBlocksCover (b.start + b.count) hi bs)

instance robinPrimeBlocksCoverDecidable (lo hi : Nat) (bs : List RobinPrimeProductBlock) :
    Decidable (RobinPrimeBlocksCover lo hi bs) :=
  match bs with
  | [] => inferInstanceAs (Decidable (lo = hi))
  | b :: tail => by
    letI := robinPrimeBlocksCoverDecidable (b.start + b.count) hi tail
    exact inferInstanceAs (Decidable (And _ _))

theorem RobinPrimeBlocksCover.product {lo hi : Nat} {bs : List RobinPrimeProductBlock}
    (hCover : RobinPrimeBlocksCover lo hi bs)
    (f : Nat -> Nat) (v : RobinPrimeProductBlock -> Nat)
    (hValues : forall b, Membership.mem bs b -> robinPrimeBlockProduct b.start b.count f = v b) :
    robinPrimeBlockProduct 0 hi f = robinPrimeBlockProduct 0 lo f * (bs.map v).prod := by
  induction bs generalizing lo with
  | nil =>
    change lo = hi at hCover
    subst lo
    simp
  | cons b tail ih =>
    change And (lo = b.start) (RobinPrimeBlocksCover (b.start + b.count) hi tail) at hCover
    have hTail := ih hCover.2 (fun c hc => hValues c (List.mem_cons_of_mem b hc))
    have hFirst := hValues b (by simp)
    rw [hTail, robinPrimeBlockProduct_add, Nat.zero_add, hFirst]
    rw [hCover.1]
    simp only [List.map_cons, List.prod_cons]
    exact mul_assoc _ _ _

theorem RobinPrimeBlocksCover.prime_prefix {c : Nat} {bs : List RobinPrimeProductBlock}
    (hCover : RobinPrimeBlocksCover 0 (c + 1) bs)
    (f : Nat -> Nat) (v : RobinPrimeProductBlock -> Nat)
    (hValues : forall b, Membership.mem bs b -> robinPrimeBlockProduct b.start b.count f = v b) :
    (Nat.primesLE c).prod f = (bs.map v).prod := by
  have h := hCover.product f v hValues
  rw [robinPrimeBlockProduct_eq_primesLE] at h
  simpa only [robinPrimeBlockProduct, Finset.range_zero, Finset.prod_empty, one_mul] using h

theorem robinBoxProduct_cons (c : Nat) (cuts : List Nat) (f : Prod Nat Nat -> Nat) :
    robinBoxProduct (c :: cuts) f = (Nat.primesLE c).prod (fun p => f (p, 1)) *
      robinBoxProduct cuts (fun v => f (v.1, v.2 + 1)) := by
  simp [robinBoxProduct, Finset.prod_range_succ', Nat.add_assoc, mul_comm]

end Robin1984
