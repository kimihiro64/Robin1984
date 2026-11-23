import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.Tactic.FieldSimp
import Robin1984.GRH.DedekindPrimeFactorization

/-!
# Ideal divisors and their prime multiplicities

Dividing a nonzero ideal is equivalent to respecting each prime
multiplicity. The complementary multiplicities multiply back to
the original ideal.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Unique factorization of nonzero integral ideals and the divisor complement.
- Formalization note: The divisibility relation is transported through the checked multiset equivalence, with the complementary ideal constructed by multiset subtraction.
- PROVENANCE-END
-/

open IsDedekindDomain

namespace Robin1984.GRH

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

local notation "M" => Multiset (HeightOneSpectrum R)
local notation "J" => {a : Ideal R // Not (a = 0)}

/-- Adding multiplicities multiplies the corresponding nonzero ideals. -/
theorem primeMultisetIdealEquiv_add_val (m n : M) :
    (primeMultisetIdealEquiv (m + n)).val =
      (primeMultisetIdealEquiv m).val * (primeMultisetIdealEquiv n).val := by
  simp only [primeMultisetIdealEquiv_apply_val, Multiset.map_add, Multiset.prod_add]

/-- The divisor relation is transported to the multiset order. -/
theorem primeMultisetIdealEquiv_dvd_iff (m n : M) :
    Iff (Dvd.dvd (primeMultisetIdealEquiv m).val (primeMultisetIdealEquiv n).val) (m <= n) := by
  constructor
  case mp =>
    intro h
    choose a ha using h
    have ha0 : Not (a = 0) := by
      intro h0
      rw [h0, mul_zero] at ha
      exact (primeMultisetIdealEquiv n).property ha
    let A : J := Subtype.mk a ha0
    let k := primeMultisetIdealEquiv.symm A
    have hk : (primeMultisetIdealEquiv k).val = a :=
      congrArg (fun x : J => x.val) (primeMultisetIdealEquiv.apply_symm_apply A)
    apply Multiset.le_iff_exists_add.mpr
    refine Exists.intro k (primeMultisetIdealEquiv.injective (Subtype.ext ?_))
    rw [primeMultisetIdealEquiv_add_val, hk]
    exact ha
  case mpr =>
    intro h
    choose k hk using Multiset.le_iff_exists_add.mp h
    refine Exists.intro (primeMultisetIdealEquiv k).val ?_
    rw [hk, primeMultisetIdealEquiv_add_val]

omit [IsDedekindDomain R] in
private theorem ideal_divisor_ne_zero {a d : Ideal R} (ha : Not (a = 0)) (hd : Dvd.dvd d a) :
    Not (d = 0) := by
  intro h
  rw [h] at hd
  exact ha (zero_dvd_iff.mp hd)

/-- A divisor of an integral ideal is uniquely indexed by its multiset of
prime ideals, bounded by the multiset of the original ideal. -/
noncomputable def idealDivisorMultiplicityEquiv (a : J) :
    Equiv {d : Ideal R // Dvd.dvd d a.val} {m : M // m <= primeMultisetIdealEquiv.symm a} where
  toFun d := by
    let D : J := Subtype.mk d.val (ideal_divisor_ne_zero a.property d.property)
    refine Subtype.mk (primeMultisetIdealEquiv.symm D) ((primeMultisetIdealEquiv_dvd_iff _ _).mp ?_)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact d.property
  invFun m := by
    refine Subtype.mk (primeMultisetIdealEquiv m.val).val ?_
    have h := (primeMultisetIdealEquiv_dvd_iff _ _).mpr m.property
    rwa [Equiv.apply_symm_apply] at h
  left_inv d := by
    apply Subtype.ext
    exact congrArg (fun x : J => x.val) (primeMultisetIdealEquiv.apply_symm_apply
      (Subtype.mk d.val (ideal_divisor_ne_zero a.property d.property)))
  right_inv m := by
    apply Subtype.ext
    exact primeMultisetIdealEquiv.symm_apply_apply m.val

/-- Adding the complementary multiplicities gives back the original
ideal, including when one of the factors is the unit ideal. -/
theorem primeMultisetIdealEquiv_mul_complement (m n : M) (h : m <= n) :
    let _ : DecidableEq (HeightOneSpectrum R) := Classical.decEq _
    (primeMultisetIdealEquiv m).val * (primeMultisetIdealEquiv (n - m)).val =
      (primeMultisetIdealEquiv n).val := by
  classical
  intro _
  rw [<- primeMultisetIdealEquiv_add_val, add_comm, Multiset.sub_add_cancel h]

private noncomputable def multisetComplementEquiv (m : M) :
    Equiv {n : M // n <= m} {n : M // n <= m} := by
  classical
  let f : {n : M // n <= m} -> {n : M // n <= m} := fun n =>
    Subtype.mk (m - n.val) (Multiset.sub_le_self _ _)
  have hf (n : {n : M // n <= m}) : f (f n) = n := by
    apply Subtype.ext
    change m - (m - n.val) = n.val
    apply add_right_cancel (b := m - n.val)
    rw [Multiset.sub_add_cancel (Multiset.sub_le_self _ _), add_comm n.val,
      Multiset.sub_add_cancel n.property]
  exact Equiv.mk f f hf hf

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The sum of the absolute norms of the divisors of a nonzero integral ideal. -/
noncomputable def idealDivisorNormSum (a : Ideal (NumberField.RingOfIntegers K)) (ha : Not (a = 0)) : Nat := by
  classical
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
  exact Finset.univ.sum (fun d : {d // Dvd.dvd d a} => Ideal.absNorm d.val)

private theorem absNorm_cast_ne_zero {a : Ideal (RingOfIntegers K)} (ha : Not (a = 0)) :
    Not ((Ideal.absNorm a : Real) = 0) :=
  Nat.cast_ne_zero.mpr (fun h => ha (Ideal.absNorm_eq_zero_iff.mp h))

/-- The original Robin divisor ratio is the finite sum of reciprocal
norms over the same divisor set. -/
theorem idealDivisorNormSum_div_eq_sum_invNorm (a : Ideal (RingOfIntegers K)) (ha : Not (a = 0)) :
    let _ : Fintype {d : Ideal (RingOfIntegers K) // Dvd.dvd d a} :=
      UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
    (idealDivisorNormSum a ha : Real) / (Ideal.absNorm a : Real) =
      Finset.univ.sum (fun d : {d : Ideal (RingOfIntegers K) // Dvd.dvd d a} =>
        Inv.inv (Ideal.absNorm d.val : Real)) := by
  classical
  intro _
  let A : {d : Ideal (RingOfIntegers K) // Not (d = 0)} := Subtype.mk a ha
  let m := primeMultisetIdealEquiv.symm A
  let e := idealDivisorMultiplicityEquiv A
  let B := e.trans ((multisetComplementEquiv m).trans e.symm)
  have hComplement (d : {d : Ideal (RingOfIntegers K) // Dvd.dvd d a}) :
      d.val * (B d).val = a := by
    let k := (e d).val
    let E : {i : Ideal (RingOfIntegers K) // Not (i = 0)} :=
      Subtype.mk d.val (ideal_divisor_ne_zero ha d.property)
    have hk : k <= m := (e d).property
    have hd : (primeMultisetIdealEquiv k).val = d.val :=
      congrArg (fun x : {i : Ideal (RingOfIntegers K) // Not (i = 0)} => x.val)
        (primeMultisetIdealEquiv.apply_symm_apply E)
    have hA : (primeMultisetIdealEquiv m).val = a :=
      congrArg (fun x : {i : Ideal (RingOfIntegers K) // Not (i = 0)} => x.val)
        (primeMultisetIdealEquiv.apply_symm_apply A)
    change d.val * (primeMultisetIdealEquiv (m - k)).val = a
    rw [<- hd, primeMultisetIdealEquiv_mul_complement k m hk, hA]
  have hEach (d : {d : Ideal (RingOfIntegers K) // Dvd.dvd d a}) :
      (Ideal.absNorm d.val : Real) / (Ideal.absNorm a : Real) =
        Inv.inv (Ideal.absNorm (B d).val : Real) := by
    have hProduct : (Ideal.absNorm a : Real) =
        (Ideal.absNorm d.val : Real) * (Ideal.absNorm (B d).val : Real) := by
      calc
        (Ideal.absNorm a : Real) =
            (Ideal.absNorm (d.val * (B d).val) : Real) :=
          congrArg (fun i : Ideal (RingOfIntegers K) => (Ideal.absNorm i : Real))
            (hComplement d).symm
        _ = _ := by rw [map_mul Ideal.absNorm, Nat.cast_mul]
    have hd := absNorm_cast_ne_zero (ideal_divisor_ne_zero ha d.property)
    have hOther := absNorm_cast_ne_zero (ideal_divisor_ne_zero ha (B d).property)
    rw [hProduct]
    field_simp [hd, hOther]
  unfold idealDivisorNormSum
  rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  simp only [<- div_eq_mul_inv]
  simp_rw [hEach]
  exact Equiv.sum_comp B
    (fun d : {d : Ideal (RingOfIntegers K) // Dvd.dvd d a} => Inv.inv (Ideal.absNorm d.val : Real))

end Robin1984.GRH
