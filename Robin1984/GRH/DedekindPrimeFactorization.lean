import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Unique factorization of nonzero ideals in a Dedekind domain.
- Formalization note: The equivalence stores a multiset of nonzero prime ideals, so both finite Euler expansions and ideal divisor sums can use the same factorization.
- PROVENANCE-END
-/

/-!
# Nonzero ideals and multisets of prime ideals

The product map from prime-ideal multisets to nonzero ideals has an
inverse given by normalized factors. Every multiplicity is retained.
-/

open IsDedekindDomain UniqueFactorizationMonoid

namespace Robin1984.GRH

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

private theorem primeMultisetProduct_ne_zero (m : Multiset (HeightOneSpectrum R)) :
    Not ((m.map HeightOneSpectrum.asIdeal).prod = 0) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons p rest hRest =>
    simpa only [Multiset.map_cons, Multiset.prod_cons] using mul_ne_zero p.prime.ne_zero hRest

private theorem normalizedFactors_primeMultisetProduct (m : Multiset (HeightOneSpectrum R)) :
    normalizedFactors (m.map HeightOneSpectrum.asIdeal).prod =
      m.map HeightOneSpectrum.asIdeal := by
  induction m using Multiset.induction_on with
  | empty => simp only [Multiset.map_zero, Multiset.prod_zero, normalizedFactors_one]
  | cons p rest hRest =>
    rw [Multiset.map_cons, Multiset.prod_cons,
      normalizedFactors_mul p.prime.ne_zero (primeMultisetProduct_ne_zero rest),
      normalizedFactors_irreducible p.irreducible, normalize_eq, hRest]
    simp only [Multiset.singleton_add]

/-- Multiply the listed prime ideals, with their multiplicities. -/
noncomputable def primeMultisetIdeal (m : Multiset (HeightOneSpectrum R)) :
    {a : Ideal R // Not (a = 0)} :=
  Subtype.mk (m.map HeightOneSpectrum.asIdeal).prod (primeMultisetProduct_ne_zero m)

private theorem primeMultisetIdeal_injective :
    Function.Injective (primeMultisetIdeal (R := R)) := by
  intro m n h
  have hFactors := congrArg (fun a : {a : Ideal R // Not (a = 0)} =>
    normalizedFactors a.val) h
  change normalizedFactors (m.map HeightOneSpectrum.asIdeal).prod =
    normalizedFactors (n.map HeightOneSpectrum.asIdeal).prod at hFactors
  rw [normalizedFactors_primeMultisetProduct, normalizedFactors_primeMultisetProduct] at hFactors
  exact Multiset.map_injective HeightOneSpectrum.asIdeal_injective hFactors

private theorem primeMultisetIdeal_surjective :
    Function.Surjective (primeMultisetIdeal (R := R)) := by
  intro a
  let factors := normalizedFactors a.val
  let locate : {p : Ideal R // Membership.mem factors p} -> HeightOneSpectrum R :=
    fun p => HeightOneSpectrum.ofPrime
      (irreducible_iff_prime.mp (irreducible_of_normalized_factor p.val p.property))
  let primes := factors.attach.map locate
  refine Exists.intro primes (Subtype.ext ?_)
  change (primes.map HeightOneSpectrum.asIdeal).prod = a.val
  have hFactors : primes.map HeightOneSpectrum.asIdeal = factors := by
    unfold primes
    rw [Multiset.map_map]
    exact Multiset.attach_map_val factors
  rw [hFactors]
  exact Ideal.prod_normalizedFactors_eq_self a.property

/-- Unique factorization identifies prime-ideal multisets with nonzero ideals. -/
noncomputable def primeMultisetIdealEquiv :
    Equiv (Multiset (HeightOneSpectrum R)) {a : Ideal R // Not (a = 0)} :=
  Equiv.ofBijective primeMultisetIdeal
    (And.intro primeMultisetIdeal_injective primeMultisetIdeal_surjective)

/-- The equivalence is given by the product of the corresponding ideals. -/
theorem primeMultisetIdealEquiv_apply_val (m : Multiset (HeightOneSpectrum R)) :
    (primeMultisetIdealEquiv m).val = (m.map HeightOneSpectrum.asIdeal).prod := rfl

end Robin1984.GRH
