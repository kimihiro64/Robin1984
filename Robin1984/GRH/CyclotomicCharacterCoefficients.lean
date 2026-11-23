import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Cyclotomic character sums at prime powers

For the primitive characters associated with all characters of a level, the
local coefficient at a positive power of a rational prime can be computed by
character orthogonality at the part of the level prime to that prime.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Dirichlet character orthogonality and conductor descent.
- Formalization note: Reindex the active primitive characters by change of level.
- Content basis: Terms with noncoprime conductor vanish at positive powers.
- Dependency status: Optional GRH extension and existing Mathlib APIs.
-/

namespace Robin1984.GRH

open DirichletCharacter

/-- The summed primitive Euler coefficient at a positive power of a prime
depends on its multiplicative order modulo the prime-to-prime part of the level. -/
theorem sum_primitiveCharacter_primePower
    (m p k : Nat) [NeZero m] (hp : Nat.Prime p) (hk : 0 < k) :
    (Finset.univ.sum fun chi : DirichletCharacter Complex m =>
      (chi.primitiveCharacter (p : Int)) ^ k) =
      let d := m / p ^ m.factorization p
      if Dvd.dvd (orderOf (p : ZMod d)) k then (d.totient : Complex) else 0 := by
  classical
  let d := m / p ^ m.factorization p
  letI : NeZero d := NeZero.mk (Nat.ordCompl_pos p (NeZero.ne m)).ne'
  have hd : Dvd.dvd d m := Nat.ordCompl_dvd m p
  have hpd : p.Coprime d := Nat.coprime_ordCompl hp (NeZero.ne m)
  let lift : DirichletCharacter Complex d -> DirichletCharacter Complex m :=
    changeLevel hd
  have hInj : Function.Injective lift := changeLevel_injective hd
  have hmem (chi : DirichletCharacter Complex m) (h : p.Coprime chi.conductor) :
      Membership.mem (Finset.univ.image lift) chi := by
    have hcd : Dvd.dvd chi.conductor d :=
      Nat.dvd_ordCompl_of_dvd_not_dvd chi.conductor_dvd_level
        ((hp.coprime_iff_not_dvd).mp h)
    have hFactor := chi.factorsThrough_conductor.mono chi hcd hd
    cases hFactor.2 with
    | intro psi hpsi =>
      exact Finset.mem_image.mpr (Exists.intro psi (And.intro (Finset.mem_univ _) hpsi.symm))
  change _ = if Dvd.dvd (orderOf (p : ZMod d)) k then (d.totient : Complex) else 0
  calc
    _ = (Finset.univ.image lift).sum
        (fun chi => (chi.primitiveCharacter (p : Int)) ^ k) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro chi _ hNotMem
      have hnc : Not (p.Coprime chi.conductor) := fun h => hNotMem (hmem chi h)
      have hz : chi.primitiveCharacter (p : Int) = 0 :=
        (chi.primitiveCharacter.apply_eq_zero_iff (p : Int)).mpr
          (fun h => hnc (Nat.isCoprime_iff_coprime.mp h))
      rw [hz, zero_pow hk.ne']
    _ = Finset.univ.sum (fun chi : DirichletCharacter Complex d =>
        chi ((p : ZMod d) ^ k)) := by
      rw [Finset.sum_image hInj.injOn]
      apply Finset.sum_congr rfl
      intro chi _
      rw [show lift chi = changeLevel hd chi from rfl,
        primitiveCharacter_changeLevel_apply,
        primitiveCharacter_apply_of_isCoprime chi (Nat.isCoprime_iff_coprime.mpr hpd),
        Int.cast_natCast, map_pow]
    _ = _ := by
      rw [sum_characters_eq]
      simp only [orderOf_dvd_iff_pow_eq_one]

end Robin1984.GRH
