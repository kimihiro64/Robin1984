import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Robin1984.GRH.EulerProductSupport
import Robin1984.GRH.FiniteEulerFactors

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Euler product expansion for a free commutative monoid.
- Formalization note: The finite subseries is reindexed by the exact exponent assignments on its finite prime set, then the support limit recovers the full product.
- PROVENANCE-END
-/

/-!
# Euler products indexed by finitely supported exponents

Each finite product expands over exponent assignments supported on its
finite set, and the absolutely summable full series determines the product.
-/

open Set

namespace Robin1984.GRH

variable {P : Type*} [DecidableEq P]

private noncomputable def supportedExponentEquiv (S : Finset P) :
    Equiv {e : Finsupp P Nat // e.support <= S}
      ({p : P // Membership.mem S p} -> Nat) where
  toFun := fun e p => e.val p.val
  invFun f :=
    let e := Finsupp.onFinset S
      (fun p => if h : Membership.mem S p then f (Subtype.mk p h) else 0)
      (fun p hp => Classical.byContradiction (fun hn => hp (dif_neg hn)))
    Subtype.mk e Finsupp.support_onFinset_subset
  left_inv e := by
    apply Subtype.ext
    ext p
    simp only [Finsupp.onFinset_apply]
    by_cases hp : Membership.mem S p
    case pos => exact dif_pos hp
    case neg =>
      rw [dif_neg hp]
      exact (Finsupp.notMem_support_iff.mp (fun hm => hp (e.property hm))).symm
  right_inv f := by
    funext p
    simp only [Finsupp.onFinset_apply, dif_pos p.property]

/-- The Dirichlet weight of one finitely supported exponent assignment. -/
noncomputable def exponentWeight (a : P -> Complex) (e : Finsupp P Nat) : Complex :=
  e.prod (fun p n => a p ^ n)

private theorem finite_euler_of_exponentWeight (a : P -> Complex)
    (ha : forall p, norm (a p) < 1) (S : Finset P) :
    S.prod (fun p => Inv.inv (1 - a p)) =
      tsum (fun e : Finsupp P Nat => if e.support <= S then exponentWeight a e else 0) := by
  classical
  let Q := {p : P // Membership.mem S p}
  let T := {e : Finsupp P Nat // e.support <= S}
  let ix : Equiv T (Q -> Nat) := supportedExponentEquiv S
  let V := fun f : Q -> Nat => Finset.univ.prod (fun p : Q => a p.val ^ f p)
  let E : Set (Finsupp P Nat) := {e | e.support <= S}
  have hGeom := (finiteGeometricSeries (fun p : Q => a p.val) (fun p => ha p.val)).2
  have hTerm (e : T) : exponentWeight a e.val = V (ix e) := by
    unfold exponentWeight
    rw [Finsupp.prod_of_support_subset _ e.property _ (fun p _ => pow_zero (a p))]
    change S.prod (fun p => a p ^ e.val p) =
      Finset.univ.prod (fun p : Q => a p.val ^ e.val p.val)
    exact (Finset.prod_coe_sort S (fun p => a p ^ e.val p)).symm
  have hMask : (fun e : Finsupp P Nat => if e.support <= S then exponentWeight a e else 0) =
      E.indicator (exponentWeight a) := by
    funext e
    by_cases h : e.support <= S
    case pos => rw [if_pos h, indicator_of_mem (show Membership.mem E e from h)]
    case neg => rw [if_neg h, indicator_of_notMem (show Not (Membership.mem E e) from h)]
  calc
    _ = Finset.univ.prod (fun p : Q => Inv.inv (1 - a p.val)) :=
      (Finset.prod_coe_sort S (fun p => Inv.inv (1 - a p))).symm
    _ = tsum V := hGeom.symm
    _ = tsum (fun e : T => V (ix e)) := (ix.tsum_eq V).symm
    _ = tsum (fun e : T => exponentWeight a e.val) := tsum_congr (fun e => (hTerm e).symm)
    _ = _ := by
      rw [hMask]
      exact tsum_subtype E (exponentWeight a)

/-- Absolute convergence of the finitely supported exponent series
identifies its sum with the full unordered Euler product. -/
theorem hasProd_eulerFactors_of_exponentWeight (a : P -> Complex)
    (ha : forall p, norm (a p) < 1)
    (hSum : Summable (fun e : Finsupp P Nat => norm (exponentWeight a e))) :
    HasProd (fun p => Inv.inv (1 - a p)) (tsum (exponentWeight a)) :=
  hasProd_of_finsetSupportExpansion _ Finsupp.support (exponentWeight a) hSum
    (finite_euler_of_exponentWeight a ha)

end Robin1984.GRH
