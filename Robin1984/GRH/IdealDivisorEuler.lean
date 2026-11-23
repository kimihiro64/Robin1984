import Mathlib.Algebra.BigOperators.Ring.Finset
import Robin1984.GRH.DedekindEulerProduct
import Robin1984.GRH.IdealDivisorMultiplicities

/-!
# The finite Euler product for the ideal divisor ratio

Each divisor chooses one exponent between zero and the corresponding
prime multiplicity. The sum of reciprocal norms therefore factors into
finite geometric sums.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The finite Euler factors of the divisor-sum function in a Dedekind domain.
- Formalization note: The divisor equivalence is composed with the dependent finite product of exponent intervals, then the sum is factored exactly.
- PROVENANCE-END
-/

open IsDedekindDomain NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "M" => Multiset P

private abbrev exponentBox [DecidableEq P] (m : M) :=
  forall p : m.toFinset, Fin (m.count p.val + 1)

private noncomputable def submultiplicityBoxEquiv [DecidableEq P] (m : M) :
    Equiv {n : M // n <= m} (exponentBox K m) := by
  let f : {n : M // n <= m} -> exponentBox K m := fun n p =>
    Fin.mk (n.val.count p.val) (Nat.lt_succ_iff.mpr ((Multiset.le_iff_count.mp n.property) p.val))
  let value (e : exponentBox K m) (p : P) : Nat :=
    if hp : Membership.mem m.toFinset p then (e (Subtype.mk p hp)).val else 0
  let finitelySupported (e : exponentBox K m) : Finsupp P Nat :=
    Finsupp.onFinset m.toFinset (value e) (fun p hv => by
      by_contra h
      exact hv (dif_neg h))
  let g : exponentBox K m -> {n : M // n <= m} := fun e => by
    refine Subtype.mk (finitelySupported e).toMultiset (Multiset.le_iff_count.mpr (fun p => ?_))
    rw [Finsupp.count_toMultiset, Finsupp.onFinset_apply]
    by_cases hp : Membership.mem m.toFinset p
    case pos =>
      rw [show value e p = (e (Subtype.mk p hp)).val from dif_pos hp]
      exact Nat.lt_succ_iff.mp (e (Subtype.mk p hp)).isLt
    case neg =>
      rw [show value e p = 0 from dif_neg hp]
      exact Nat.zero_le _
  refine Equiv.mk f g ?left ?right
  case left =>
    intro n
    apply Subtype.ext
    apply Multiset.ext.mpr
    intro p
    change (finitelySupported (f n)).toMultiset.count p = n.val.count p
    rw [Finsupp.count_toMultiset, Finsupp.onFinset_apply]
    by_cases hp : Membership.mem m.toFinset p
    case pos =>
      exact dif_pos hp
    case neg =>
      have hn : Not (Membership.mem n.val p) := fun h =>
        hp (Multiset.mem_toFinset.mpr (Multiset.mem_of_le n.property h))
      rw [show value (f n) p = 0 from dif_neg hp, Multiset.count_eq_zero.mpr hn]
  case right =>
    intro e
    funext p
    apply Fin.ext
    change (finitelySupported e).toMultiset.count p.val = (e p).val
    rw [Finsupp.count_toMultiset, Finsupp.onFinset_apply]
    exact dif_pos p.property

private theorem absNorm_primeMultiset_eq_prod_count [DecidableEq P] (n : M) (S : Finset P)
    (hn : n.toFinset <= S) :
    Ideal.absNorm (primeMultisetIdealEquiv n).val =
      S.prod (fun p => dedekindPrimeNorm K p ^ n.count p) := by
  let e := Multiset.toFinsupp n
  have hNorm : Ideal.absNorm (primeMultisetIdealEquiv n).val = (n.map (dedekindPrimeNorm K)).prod := by
    rw [primeMultisetIdealEquiv_apply_val, map_multiset_prod, Multiset.map_map]
    rfl
  have hProd : (n.map (dedekindPrimeNorm K)).prod =
      e.prod (fun p k => dedekindPrimeNorm K p ^ k) := by
    calc
      _ = (e.toMultiset.map (dedekindPrimeNorm K)).prod := by
        rw [Multiset.toFinsupp_toMultiset]
      _ = _ := by
        rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index pow_zero pow_add]
  have hSupport : e.support <= S := by
    change (Multiset.toFinsupp n).support <= S
    rw [Multiset.toFinsupp_support]
    exact hn
  rw [hNorm, hProd]
  rw [Finsupp.prod_of_support_subset _ hSupport _ (fun _ _ => pow_zero _)]
  simp only [e, Multiset.toFinsupp_apply]

private noncomputable def idealPrimeMultiplicities (a : Ideal (RingOfIntegers K)) (ha : Not (a = 0)) : M :=
  primeMultisetIdealEquiv.symm (Subtype.mk a ha)

/-- The product of the finite geometric factors carried by the prime
multiplicities of an ideal. -/
noncomputable def idealDivisorGeometricProduct [DecidableEq P] (a : Ideal (RingOfIntegers K))
    (ha : Not (a = 0)) :
    Real := by
  classical
  let m := idealPrimeMultiplicities K a ha
  exact Finset.univ.prod (fun p : m.toFinset =>
    Finset.univ.sum (fun j : Fin (m.count p.val + 1) =>
      (Inv.inv (dedekindPrimeNorm K p.val : Real)) ^ j.val))

/-- The norm-normalized ideal divisor sum factors exactly over the
finite geometric Euler factors. -/
theorem idealDivisorNormSum_div_eq_geometricProduct [DecidableEq P] (a : Ideal (RingOfIntegers K))
    (ha : Not (a = 0)) :
    (idealDivisorNormSum a ha : Real) / (Ideal.absNorm a : Real) = idealDivisorGeometricProduct K a ha := by
  classical
  let A : {d : Ideal (RingOfIntegers K) // Not (d = 0)} := Subtype.mk a ha
  let m := idealPrimeMultiplicities K a ha
  let e := idealDivisorMultiplicityEquiv A
  let j := e.trans (submultiplicityBoxEquiv K m)
  let w (p : m.toFinset) (k : Fin (m.count p.val + 1)) : Real :=
    (Inv.inv (dedekindPrimeNorm K p.val : Real)) ^ k.val
  let W (exponents : exponentBox K m) : Real := Finset.univ.prod (fun p => w p (exponents p))
  let _ := UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
  have hWeight (d : {d : Ideal (RingOfIntegers K) // Dvd.dvd d a}) :
      Inv.inv (Ideal.absNorm d.val : Real) = W (j d) := by
    let n := (e d).val
    have hn : n.toFinset <= m.toFinset := by
      intro p hp
      exact Multiset.mem_toFinset.mpr
        (Multiset.mem_of_le (e d).property (Multiset.mem_toFinset.mp hp))
    have hdNorm : Ideal.absNorm d.val = m.toFinset.prod
        (fun p => dedekindPrimeNorm K p ^ n.count p) := by
      have hd : (primeMultisetIdealEquiv n).val = d.val :=
        congrArg (fun d : {d : Ideal (RingOfIntegers K) // Dvd.dvd d a} => d.val)
          (e.symm_apply_apply d)
      rw [<- hd, absNorm_primeMultiset_eq_prod_count K n m.toFinset hn]
    calc
      Inv.inv (Ideal.absNorm d.val : Real) =
          m.toFinset.prod (fun p => (Inv.inv (dedekindPrimeNorm K p : Real)) ^ n.count p) := by
        rw [hdNorm, Nat.cast_prod, <- Finset.prod_inv_distrib]
        simp only [Nat.cast_pow, inv_pow]
      _ = Finset.univ.prod (fun p : m.toFinset =>
          (Inv.inv (dedekindPrimeNorm K p.val : Real)) ^ n.count p.val) := by
        exact (Finset.prod_coe_sort m.toFinset
          (fun p => (Inv.inv (dedekindPrimeNorm K p : Real)) ^ n.count p)).symm
      _ = W (j d) := by
        unfold W
        apply Finset.prod_congr rfl
        intro p _
        congr 1
  rw [idealDivisorNormSum_div_eq_sum_invNorm]
  calc
    _ = Finset.univ.sum (fun d => W (j d)) := Finset.sum_congr rfl (fun d _ => hWeight d)
    _ = Finset.univ.sum W := Equiv.sum_comp j W
    _ = _ := (Fintype.prod_sum w).symm

/-- The divisor ratio of an ideal given by its prime multiset, with
local sums in ordinary finite exponent ranges. -/
theorem idealDivisorNormSum_div_primeMultiset [DecidableEq P] (m : M) :
    (idealDivisorNormSum (primeMultisetIdealEquiv m).val (primeMultisetIdealEquiv m).property : Real) /
        (Ideal.absNorm (primeMultisetIdealEquiv m).val : Real) =
      m.toFinset.prod (fun p => (Finset.range (m.count p + 1)).sum
        (fun k => (Inv.inv (dedekindPrimeNorm K p : Real)) ^ k)) := by
  classical
  rw [idealDivisorNormSum_div_eq_geometricProduct K]
  let g (n : M) : Real := n.toFinset.prod (fun p => (Finset.range (n.count p + 1)).sum
    (fun k => (Inv.inv (dedekindPrimeNorm K p : Real)) ^ k))
  have hGeo (n : M) :
      (Finset.univ.prod (fun p : n.toFinset => Finset.univ.sum
        (fun k : Fin (n.count p.val + 1) => (Inv.inv (dedekindPrimeNorm K p.val : Real)) ^ k.val))) =
        g n := by
    simp only [Fin.sum_univ_eq_sum_range, g]
    exact Finset.prod_coe_sort n.toFinset (fun p => (Finset.range (n.count p + 1)).sum
      (fun k => (Inv.inv (dedekindPrimeNorm K p : Real)) ^ k))
  unfold idealDivisorGeometricProduct idealPrimeMultiplicities
  exact (hGeo (primeMultisetIdealEquiv.symm (primeMultisetIdealEquiv m))).trans
    (congrArg g (primeMultisetIdealEquiv.symm_apply_apply m))

end Robin1984.GRH
