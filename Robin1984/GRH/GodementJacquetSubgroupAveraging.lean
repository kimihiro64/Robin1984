import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Compact-open averaging and the positive torus in Casselman's notes on representations of p-adic groups, Section 4, and the Cayley-Hamilton theorem.
- Formalization note: Proves a finite recurrence for matrix coefficients from double-coset multiplication and a subgroup average.
- PROVENANCE-END
-/

/-!
# Averaged operators and matrix coefficient recurrences

A finite-dimensional space of subgroup-fixed vectors carries the
compressed action of elements satisfying the double-coset condition.
Its characteristic polynomial gives a recurrence for the original
matrix coefficient along the powers of such an element.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

variable {G V : Type*} [Group G] [AddCommGroup V] [Module Complex V]
variable {rho : MonoidHom G (Module.End Complex V)} {K : Subgroup G}

/-- A linear average whose evaluation on each vector is a finite average
over the subgroup, with subgroup-fixed output. -/
structure HeckeLocalSubgroupAverage (rho : MonoidHom G (Module.End Complex V)) (K : Subgroup G) where
  proj : Module.End Complex V
  left_invariant : forall (k : K) (v : V), proj (rho k.val v) = proj v
  fixed : forall (k : K) (v : V), rho k.val (proj v) = proj v
  finite_sum : forall v : V, exists (n : Nat) (k : Fin n -> K) (w : Fin n -> Complex),
    And (Finset.univ.sum w = 1)
      (proj v = Finset.univ.sum (fun i => HSMul.hSMul (w i) (rho (k i).val v)))

namespace HeckeLocalSubgroupAverage

variable (P : HeckeLocalSubgroupAverage rho K)

/-- A subgroup-fixed vector belongs to the range of averaging. -/
theorem proj_eq_of_fixed (v : V) (hv : forall k : K, rho k.val v = v) : P.proj v = v := by
  choose n k w h using P.finite_sum v
  rw [h.2]
  simp only [hv]
  rw [<- Finset.sum_smul, h.1, one_smul]

/-- An invariant linear functional has the same value after averaging. -/
theorem pairing_proj
    (ell : LinearMap (RingHom.id Complex) V Complex)
    (hEll : forall (k : K) (v : V), ell (rho k.val v) = ell v) (v : V) :
    ell (P.proj v) = ell v := by
  choose n k w h using P.finite_sum v
  rw [h.2, map_sum]
  simp only [map_smul, hEll]
  rw [<- Finset.sum_smul, h.1, one_smul]

/-- The action of a group element followed by averaging, restricted to
the range of the average. -/
def operator (a : G) : Module.End Complex (LinearMap.range P.proj) where
  toFun v := Subtype.mk (P.proj (rho a v.val)) (Exists.intro (rho a v.val) rfl)
  map_add' := by
    intro x y
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
  map_smul' := by
    intro r x
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply, map_smul]

/-- The compressed product agrees with compression of the product when
every element inserted between the two factors is absorbed by the outside
subgroup actions. -/
theorem operator_mul (a b : G)
    (hDouble : forall k : K, exists l r : K, a * k.val * b = l.val * (a * b) * r.val) :
    P.operator a * P.operator b = P.operator (a * b) := by
  ext v
  change P.proj (rho a (P.proj (rho b v.val))) = P.proj (rho (a * b) v.val)
  have hv (r : K) : rho r.val v.val = v.val := by
    choose u hu using v.property
    rw [<- hu]
    exact P.fixed r u
  choose n k w h using P.finite_sum (rho b v.val)
  have hConst (i : Fin n) :
      P.proj (rho a (rho (k i).val (rho b v.val))) = P.proj (rho (a * b) v.val) := by
    choose l r hEq using hDouble (k i)
    calc
      _ = P.proj (rho (a * (k i).val * b) v.val) := by
        simp only [map_mul, Module.End.mul_apply]
      _ = P.proj (rho l.val (rho (a * b) (rho r.val v.val))) := by
        rw [hEq]
        simp only [map_mul, Module.End.mul_apply]
      _ = _ := by rw [hv, P.left_invariant]
  rw [h.2, map_sum, map_sum]
  simp only [map_smul, hConst]
  rw [<- Finset.sum_smul, h.1, one_smul]

/-- Compression of powers is computed by powers of a single averaged
operator on the subgroup-fixed range. -/
theorem operator_pow (a : G)
    (hDouble : forall (n : Nat) (k : K),
      exists l r : K, a * k.val * a ^ n = l.val * (a * a ^ n) * r.val) (n : Nat) :
    P.operator a ^ n = P.operator (a ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    ext v
    change v.val = P.proj (rho 1 v.val)
    rw [map_one]
    change v.val = P.proj v.val
    apply Eq.symm
    refine P.proj_eq_of_fixed v.val (fun k => ?_)
    choose u hu using v.property
    rw [<- hu]
    exact P.fixed k u
  | succ n ih =>
    rw [pow_succ', ih, P.operator_mul a (a ^ n) (hDouble n), pow_succ']

/-- Finite-dimensionality of the averaged range gives a monic linear
recurrence for the original invariant matrix coefficient. -/
theorem matrixCoefficient_recurrence
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (a : G)
    (hDouble : forall (n : Nat) (k : K),
      exists l r : K, a * k.val * a ^ n = l.val * (a * a ^ n) * r.val)
    (ell : LinearMap (RingHom.id Complex) V Complex)
    (hEll : forall (k : K) (v : V), ell (rho k.val v) = ell v)
    (v : V) (hv : forall k : K, rho k.val v = v) :
    let d := Module.finrank Complex (LinearMap.range P.proj)
    exists coeff : Nat -> Complex, And (coeff d = 1)
      (forall n : Nat, (Finset.range (d + 1)).sum
        (fun j => coeff j * ell (rho (a ^ (n + j)) v)) = 0) := by
  intro d
  let t := P.operator a
  let q := t.charpoly
  have hDeg : q.natDegree = d := LinearMap.charpoly_natDegree t
  have hLead : q.coeff d = 1 := by
    rw [<- hDeg]
    exact LinearMap.charpoly_monic t
  refine Exists.intro q.coeff (And.intro hLead (fun n => ?_))
  let w : LinearMap.range P.proj := Subtype.mk v (Exists.intro v (P.proj_eq_of_fixed v hv))
  let ellW := ell.comp (LinearMap.range P.proj).subtype
  have hSum : (Finset.range (d + 1)).sum (fun j => HSMul.hSMul (q.coeff j) (t ^ j)) = 0 := by
    rw [<- hDeg, <- Polynomial.aeval_eq_sum_range (p := q) t]
    exact LinearMap.aeval_self_charpoly t
  have hZero := congrArg (fun op : Module.End Complex (LinearMap.range P.proj) =>
    ellW (op ((t ^ n) w))) hSum
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, map_sum,
    map_smul, smul_eq_mul, map_zero] at hZero
  have hTerm (j : Nat) :
      ellW ((t ^ j) ((t ^ n) w)) = ell (rho (a ^ (n + j)) v) := by
    have hPow : t ^ (n + j) = P.operator (a ^ (n + j)) := P.operator_pow a hDouble _
    change ellW ((t ^ j * t ^ n) w) = _
    rw [<- pow_add, Nat.add_comm j n, hPow]
    exact P.pairing_proj ell hEll _
  simpa only [hTerm] using hZero

end HeckeLocalSubgroupAverage

/-- A subgroup decomposition and two conjugation directions give the
double-coset identity for all nonnegative powers of the same element. -/
theorem exists_doubleCoset_factor_pow_of_decomposition
    (U M L : Subgroup G) (hL : L <= K) (a : G)
    (hDecomp : forall k : K, exists u : U, exists m : M, exists l : L,
      k.val = u.val * m.val * l.val)
    (hUpper : forall u : U, Membership.mem K (a * u.val * Inv.inv a))
    (hDiagonal : forall m : M, Membership.mem K (a * m.val * Inv.inv a))
    (hLower : forall l : L, Membership.mem L (Inv.inv a * l.val * a))
    (n : Nat) (k : K) :
    exists l r : K, a * k.val * a ^ n = l.val * (a * a ^ n) * r.val := by
  have hStable (l : L) (j : Nat) :
      Membership.mem L (Inv.inv (a ^ j) * l.val * a ^ j) := by
    induction j with
    | zero => simpa only [pow_zero, inv_one, one_mul, mul_one] using l.property
    | succ j ih =>
      have hStep := hLower (Subtype.mk (Inv.inv (a ^ j) * l.val * a ^ j) ih)
      simpa only [pow_succ, mul_inv_rev, mul_assoc] using hStep
  choose u m l hk using hDecomp k
  let up : K := Subtype.mk (a * u.val * Inv.inv a) (hUpper u)
  let mid : K := Subtype.mk (a * m.val * Inv.inv a) (hDiagonal m)
  let low : K := Subtype.mk (Inv.inv (a ^ n) * l.val * a ^ n) (hL (hStable l n))
  refine Exists.intro (up * mid) (Exists.intro low ?_)
  change a * k.val * a ^ n =
    ((a * u.val * Inv.inv a) * (a * m.val * Inv.inv a)) *
      (a * a ^ n) * (Inv.inv (a ^ n) * l.val * a ^ n)
  simp [hk, mul_assoc]

end Robin1984.GRH
