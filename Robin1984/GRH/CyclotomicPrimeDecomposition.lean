import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Local prime decomposition in a rational cyclotomic field

The inertia degree at a rational prime is its multiplicative order modulo
the part of the conductor coprime to that prime. The number of primes above
it times that degree is the totient of that part.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Cyclotomic ramification and the fundamental identity for a Galois extension.
- Formalization note: Combine the ramified and unramified cases in one coefficient calculation.
- Content basis: Mathlib inertia degree, ramification index, and norm formulas.
- Dependency status: Mathlib only.
-/

open Ideal NumberField IsCyclotomicExtension.Rat

namespace Robin1984.GRH

/-- The rational prime `p` has the stated norm and number of primes above it
when the cyclotomic level is `p ^ k * d` with `p` prime to `d`. -/
theorem cyclotomic_primesOver_norm_and_count {m d p k : Nat} [NeZero m] [NeZero d]
    (hp : Nat.Prime p) (hm : m = p ^ k * d) (hpd : Not (Dvd.dvd p d)) :
    let q : Ideal Int := Ideal.span ({(p : Int)} : Set Int)
    let R := RingOfIntegers (CyclotomicField m Rat)
    let f := orderOf (p : ZMod d)
    And ((q.primesOver R).ncard * f = d.totient)
      (forall P : Ideal R, Membership.mem (q.primesOver R) P ->
        Ideal.absNorm P = p ^ f) := by
  let F := CyclotomicField m Rat
  let R := RingOfIntegers F
  let q : Ideal Int := Ideal.span ({(p : Int)} : Set Int)
  let f := orderOf (p : ZMod d)
  let e := (p ^ k).totient
  letI : Fact (Nat.Prime p) := Fact.mk hp
  have hpZ : Prime (p : Int) := Nat.prime_iff_prime_int.mp hp
  letI : q.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  letI : NeZero (m : Rat) := NeZero.mk (by exact_mod_cast NeZero.ne m)
  letI : IsCyclotomicExtension ({m} : Set Nat) Rat F :=
    CyclotomicField.isCyclotomicExtension m Rat
  letI : IsGalois Rat F := IsCyclotomicExtension.isGalois ({m} : Set Nat) Rat F
  have hSplit : And (q.inertiaDegIn R = f) (q.ramificationIdxIn R = e) := by
    dsimp only [q, R, f, e]
    cases k with
    | zero =>
      have hd : m = d := by simpa only [pow_zero, one_mul] using hm
      subst d
      apply And.intro
      case left => exact inertiaDegIn_eq_of_not_dvd p F hpd
      case right =>
        simpa only [pow_zero, Nat.totient_one] using ramificationIdxIn_eq_of_not_dvd p F hpd
    | succ k =>
      apply And.intro
      case left => exact inertiaDegIn_eq m F hm hpd
      case right =>
        rw [Nat.totient_prime_pow_succ hp]
        exact ramificationIdxIn_eq m F hm hpd
  have hTot : e * d.totient = m.totient := by
    unfold e
    rw [<- Nat.totient_mul (Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).mpr hpd))]
    exact congrArg Nat.totient hm.symm
  have hGaloisDegree : Nat.card (AlgEquiv Rat F F) = m.totient := by
    rw [IsGalois.card_aut_eq_finrank]
    exact IsCyclotomicExtension.Rat.finrank m F
  have hCount := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    q R (AlgEquiv Rat F F)
  rw [hSplit.1, hSplit.2, hGaloisDegree] at hCount
  have he : 0 < e := Nat.totient_pos.mpr (pow_pos hp.pos k)
  apply And.intro
  case left =>
    change (q.primesOver R).ncard * f = d.totient
    apply Nat.eq_of_mul_eq_mul_left he
    calc
      _ = (q.primesOver R).ncard * (e * f) := by ac_rfl
      _ = m.totient := hCount
      _ = _ := hTot.symm
  case right =>
    intro P hP
    letI : P.IsPrime := hP.1
    letI : P.LiesOver q := hP.2
    have hDegree := inertiaDegIn_eq_inertiaDeg q P (AlgEquiv Rat F F)
    have hLocal := hSplit.1
    rw [hDegree] at hLocal
    rw [<- Ideal.natAbs_pow_inertiaDeg (p : Int) P, Int.natAbs_natCast, hLocal]

end Robin1984.GRH
