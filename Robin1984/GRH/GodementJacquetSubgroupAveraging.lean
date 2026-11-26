import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Compact-open averaging and the positive torus in Casselman's notes on representations of p-adic groups, Section 4, and the Cayley-Hamilton theorem.
- Formalization note: Constructs averaging for smooth representations on compact subgroups and proves a matrix coefficient recurrence using double-coset multiplication.
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

namespace Robin1984.GRH

private theorem finiteQuotientAverage_surjective
    {G H V : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    [AddCommGroup V] [Module Complex V]
    (pi : MonoidHom G H) (hpi : Function.Surjective pi) (f : H -> V) :
    HSMul.hSMul (Inv.inv (Fintype.card G : Complex)) (Finset.univ.sum (fun g => f (pi g))) =
      HSMul.hSMul (Inv.inv (Fintype.card H : Complex)) (Finset.univ.sum f) := by
  classical
  let fiberEquiv (h : H) : Equiv {g : G // pi g = h} pi.ker := by
    choose a ha using hpi h
    exact
      { toFun := fun g => Subtype.mk (Inv.inv a * g.val) (by
          change pi (Inv.inv a * g.val) = 1
          rw [map_mul, map_inv, ha, g.property, inv_mul_cancel])
        invFun := fun k => Subtype.mk (a * k.val) (by
          have hk : pi k.val = 1 := k.property
          rw [map_mul, ha, hk, mul_one])
        left_inv := fun g => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
  have hSize (h : H) : Fintype.card {g : G // pi g = h} = Fintype.card pi.ker :=
    Fintype.card_congr (fiberEquiv h)
  have hCard : Fintype.card G = Fintype.card H * Fintype.card pi.ker := by
    simpa only [Finset.sum_const, Finset.card_univ, hSize, nsmul_eq_mul, Nat.cast_id, mul_one] using
      (Fintype.sum_fiberwise' pi (fun _ => (1 : Nat))).symm
  have hSum : (Finset.univ.sum (fun g => f (pi g))) =
      HSMul.hSMul (Fintype.card pi.ker) (Finset.univ.sum f) := by
    calc
      _ = Finset.univ.sum (fun h : H =>
          Finset.univ.sum (fun _ : {g : G // pi g = h} => f h)) :=
        (Fintype.sum_fiberwise' pi f).symm
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hSize, Finset.smul_sum]
  have hN : Not ((Fintype.card pi.ker : Complex) = 0) :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hSum, <- Nat.cast_smul_eq_nsmul Complex, smul_smul]
  congr 1
  rw [hCard, Nat.cast_mul, mul_comm (Fintype.card H : Complex), mul_inv_rev, mul_assoc]
  have hCancel : Inv.inv (Fintype.card pi.ker : Complex) * (Fintype.card pi.ker : Complex) = 1 := by
    have hFiber : Not ((Fintype.card {x : G // pi x = 1} : Complex) = 0) := by
      rw [hSize (1 : H)]
      exact hN
    simp [hFiber]
  rw [hCancel, mul_one]

section QuotientAverages

variable {H V : Type*} [Group H] [AddCommGroup V] [Module Complex V]

private abbrev SubgroupCosets (N : Subgroup H) := HasQuotient.Quotient H N

private def subgroupQuotientOrbit (rho : MonoidHom H (Module.End Complex V))
    (N : Subgroup H) (v : V) (hv : forall n : N, rho n.val v = v) :
    SubgroupCosets N -> V :=
  Quotient.lift (fun h : H => rho h v) (fun a b h => by
    have hn : Membership.mem N (Inv.inv a * b) := QuotientGroup.leftRel_apply.mp h
    have hab : a * (Inv.inv a * b) = b := by simp
    have hAction : rho (a * (Inv.inv a * b)) v = rho a (rho (Inv.inv a * b) v) := by
      simp only [map_mul, Module.End.mul_apply]
    rw [hab, hv (Subtype.mk (Inv.inv a * b) hn)] at hAction
    exact hAction.symm)

private theorem subgroupQuotientOrbit_mk (rho : MonoidHom H (Module.End Complex V))
    (N : Subgroup H) [N.Normal] (v : V) (hv : forall n : N, rho n.val v = v) (a : H) :
    subgroupQuotientOrbit rho N v hv (QuotientGroup.mk' N a) = rho a v := rfl

private def subgroupQuotientAverage (rho : MonoidHom H (Module.End Complex V))
    (N : Subgroup H) [N.FiniteIndex] (v : V) (hv : forall n : N, rho n.val v = v) : V :=
  let : Fintype (SubgroupCosets N) := Fintype.ofFinite _
  HSMul.hSMul (Inv.inv (Fintype.card (SubgroupCosets N) : Complex))
    (Finset.univ.sum (fun x => subgroupQuotientOrbit rho N v hv x))

private theorem subgroupQuotientAverage_eq_of_le (rho : MonoidHom H (Module.End Complex V))
    {N M : Subgroup H} [N.Normal] [M.Normal] [N.FiniteIndex] [M.FiniteIndex] (hNM : N <= M)
    (v : V) (hn : forall n : N, rho n.val v = v) (hm : forall m : M, rho m.val v = v) :
    subgroupQuotientAverage rho N v hn = subgroupQuotientAverage rho M v hm := by
  let : Fintype (SubgroupCosets N) := Fintype.ofFinite _
  let : Fintype (SubgroupCosets M) := Fintype.ofFinite _
  let q := QuotientGroup.map N M (MonoidHom.id H) hNM
  have hMap (a : H) : q (QuotientGroup.mk' N a) = QuotientGroup.mk' M a := by
    rfl
  have hSurj : Function.Surjective q := by
    intro y
    choose a ha using QuotientGroup.mk'_surjective M y
    exact Exists.intro (QuotientGroup.mk' N a) ((hMap a).trans ha)
  have hOrbit (x : SubgroupCosets N) :
      subgroupQuotientOrbit rho N v hn x = subgroupQuotientOrbit rho M v hm (q x) := by
    choose a ha using QuotientGroup.mk'_surjective N x
    rw [<- ha, hMap, subgroupQuotientOrbit_mk, subgroupQuotientOrbit_mk]
  simpa only [subgroupQuotientAverage, hOrbit] using
    (finiteQuotientAverage_surjective q hSurj (subgroupQuotientOrbit rho M v hm))

private theorem subgroupQuotientAverage_add (rho : MonoidHom H (Module.End Complex V))
    (N : Subgroup H) [N.Normal] [N.FiniteIndex]
    (v w : V) (hv : forall n : N, rho n.val v = v) (hw : forall n : N, rho n.val w = w)
    (hs : forall n : N, rho n.val (v + w) = v + w) :
    subgroupQuotientAverage rho N (v + w) hs =
      subgroupQuotientAverage rho N v hv + subgroupQuotientAverage rho N w hw := by
  have hOrbit (q : SubgroupCosets N) :
      subgroupQuotientOrbit rho N (v + w) hs q =
        subgroupQuotientOrbit rho N v hv q + subgroupQuotientOrbit rho N w hw q := by
    choose a ha using QuotientGroup.mk'_surjective N q
    rw [<- ha, subgroupQuotientOrbit_mk, subgroupQuotientOrbit_mk, subgroupQuotientOrbit_mk]
    exact map_add (rho a) v w
  simp only [subgroupQuotientAverage, hOrbit, Finset.sum_add_distrib, smul_add]

private theorem subgroupQuotientAverage_smul (rho : MonoidHom H (Module.End Complex V))
    (N : Subgroup H) [N.Normal] [N.FiniteIndex]
    (r : Complex) (v : V) (hv : forall n : N, rho n.val v = v)
    (hs : forall n : N, rho n.val (HSMul.hSMul r v) = HSMul.hSMul r v) :
    subgroupQuotientAverage rho N (HSMul.hSMul r v) hs =
      HSMul.hSMul r (subgroupQuotientAverage rho N v hv) := by
  have hOrbit (q : SubgroupCosets N) :
      subgroupQuotientOrbit rho N (HSMul.hSMul r v) hs q =
        HSMul.hSMul r (subgroupQuotientOrbit rho N v hv q) := by
    choose a ha using QuotientGroup.mk'_surjective N q
    rw [<- ha, subgroupQuotientOrbit_mk, subgroupQuotientOrbit_mk]
    exact map_smul (rho a) r v
  simp only [subgroupQuotientAverage, hOrbit, <- Finset.smul_sum]
  exact smul_comm _ _ _

private theorem subgroupQuotientAverage_fixed (rho : MonoidHom H (Module.End Complex V))
    (N : Subgroup H) [N.Normal] [N.FiniteIndex]
    (v : V) (hv : forall n : N, rho n.val v = v) (k : H) :
    rho k (subgroupQuotientAverage rho N v hv) = subgroupQuotientAverage rho N v hv := by
  let : Fintype (SubgroupCosets N) := Fintype.ofFinite _
  have hOrbit (q : SubgroupCosets N) :
      rho k (subgroupQuotientOrbit rho N v hv q) =
        subgroupQuotientOrbit rho N v hv ((QuotientGroup.mk' N k) * q) := by
    choose a ha using QuotientGroup.mk'_surjective N q
    rw [<- ha, <- map_mul, subgroupQuotientOrbit_mk, subgroupQuotientOrbit_mk,
      map_mul, Module.End.mul_apply]
  simp only [subgroupQuotientAverage, map_smul, map_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk' N k)) _ _ hOrbit

private theorem subgroupQuotientAverage_translate (rho : MonoidHom H (Module.End Complex V))
    (N : Subgroup H) [N.Normal] [N.FiniteIndex]
    (v : V) (hv : forall n : N, rho n.val v = v) (k : H)
    (hk : forall n : N, rho n.val (rho k v) = rho k v) :
    subgroupQuotientAverage rho N (rho k v) hk = subgroupQuotientAverage rho N v hv := by
  let : Fintype (SubgroupCosets N) := Fintype.ofFinite _
  have hOrbit (q : SubgroupCosets N) :
      subgroupQuotientOrbit rho N (rho k v) hk q =
        subgroupQuotientOrbit rho N v hv (q * (QuotientGroup.mk' N k)) := by
    choose a ha using QuotientGroup.mk'_surjective N q
    rw [<- ha, <- map_mul, subgroupQuotientOrbit_mk, subgroupQuotientOrbit_mk,
      map_mul, Module.End.mul_apply]
  simp only [subgroupQuotientAverage]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk' N k)) _ _ hOrbit

private theorem subgroupQuotientAverage_finite_sum (rho : MonoidHom H (Module.End Complex V))
    (N : Subgroup H) [N.Normal] [N.FiniteIndex]
    (v : V) (hv : forall n : N, rho n.val v = v) :
    exists (m : Nat) (rep : Fin m -> H) (w : Fin m -> Complex),
      And (Finset.univ.sum w = 1)
        (subgroupQuotientAverage rho N v hv =
          Finset.univ.sum (fun i => HSMul.hSMul (w i) (rho (rep i) v))) := by
  let : Fintype (SubgroupCosets N) := Fintype.ofFinite _
  let m := Fintype.card (SubgroupCosets N)
  let e : Equiv (Fin m) (SubgroupCosets N) := (Fintype.equivFin _).symm
  choose rep hRep using (fun i : Fin m => QuotientGroup.mk'_surjective N (e i))
  have hm : Not ((m : Complex) = 0) := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine Exists.intro m (Exists.intro rep (Exists.intro (fun _ => Inv.inv (m : Complex))
    (And.intro ?_ ?_)))
  . simp [nsmul_eq_mul, hm]
  . simp only [subgroupQuotientAverage, <- Finset.smul_sum]
    congr 1
    symm
    refine Fintype.sum_equiv e _ _ (fun i => ?_)
    rw [<- hRep i, subgroupQuotientOrbit_mk]

end QuotientAverages

/-- Each vector can be averaged on its own finite quotient. Common refinements
give a single linear subgroup average with fixed output. -/
def HeckeLocalSubgroupAverage.ofFiniteIndexNormalFixers
    {G V : Type*} [Group G] [AddCommGroup V] [Module Complex V]
    (rho : MonoidHom G (Module.End Complex V)) (K : Subgroup G)
    (hFinite : forall v : V, exists N : Subgroup K,
      And N.Normal (And N.FiniteIndex (forall n : N, rho n.val.val v = v))) :
    HeckeLocalSubgroupAverage rho K := by
  classical
  let r := rho.comp K.subtype
  choose N hN using hFinite
  let : forall v : V, (N v).Normal := fun v => (hN v).1
  let : forall v : V, (N v).FiniteIndex := fun v => (hN v).2.1
  let average (v : V) := subgroupQuotientAverage r (N v) v (hN v).2.2
  have compare (v : V) (M : Subgroup K) [M.Normal] [M.FiniteIndex]
      (hm : forall m : M, r m.val v = v) :
      average v = subgroupQuotientAverage r M v hm := by
    let S := min (N v) M
    let : S.Normal := by dsimp [S]; infer_instance
    let : S.FiniteIndex := by dsimp [S]; infer_instance
    have hSN : S <= N v := inf_le_left
    have hSM : S <= M := inf_le_right
    have hv (s : S) : r s.val v = v := hm (Subtype.mk s.val (hSM s.property))
    exact (subgroupQuotientAverage_eq_of_le r hSN v hv (hN v).2.2).symm.trans
      (subgroupQuotientAverage_eq_of_le r hSM v hv hm)
  refine {
    proj := {
      toFun := average
      map_add' := ?_
      map_smul' := ?_ }
    left_invariant := ?_
    fixed := ?_
    finite_sum := ?_ }
  . intro v w
    let S := min (N v) (N w)
    let : S.Normal := by dsimp [S]; infer_instance
    let : S.FiniteIndex := by dsimp [S]; infer_instance
    have hSv : S <= N v := inf_le_left
    have hSw : S <= N w := inf_le_right
    have hv (s : S) : r s.val v = v := (hN v).2.2 (Subtype.mk s.val (hSv s.property))
    have hw (s : S) : r s.val w = w := (hN w).2.2 (Subtype.mk s.val (hSw s.property))
    have hs (s : S) : r s.val (v + w) = v + w := by rw [map_add, hv, hw]
    rw [compare (v + w) S hs, compare v S hv, compare w S hw]
    exact subgroupQuotientAverage_add r S v w hv hw hs
  . intro c v
    have hs (n : N v) : r n.val (HSMul.hSMul c v) = HSMul.hSMul c v := by
      rw [map_smul, show r n.val v = v from (hN v).2.2 n]
    change average (HSMul.hSMul c v) = HSMul.hSMul c (average v)
    rw [compare _ (N v) hs]
    exact subgroupQuotientAverage_smul r (N v) c v (hN v).2.2 hs
  . intro k v
    change average (r k v) = average v
    let S := min (N v) (N (r k v))
    let : S.Normal := by dsimp [S]; infer_instance
    let : S.FiniteIndex := by dsimp [S]; infer_instance
    have hSv : S <= N v := inf_le_left
    have hSk : S <= N (r k v) := inf_le_right
    have hv (s : S) : r s.val v = v := (hN v).2.2 (Subtype.mk s.val (hSv s.property))
    have hk (s : S) : r s.val (r k v) = r k v :=
      (hN (r k v)).2.2 (Subtype.mk s.val (hSk s.property))
    rw [compare _ S hk, compare _ S hv]
    exact subgroupQuotientAverage_translate r S v hv k hk
  . intro k v
    exact subgroupQuotientAverage_fixed r (N v) v (hN v).2.2 k
  . intro v
    exact subgroupQuotientAverage_finite_sum r (N v) v (hN v).2.2

/-- A finite-index stabilizer suffices because its normal core still has finite index. -/
def HeckeLocalSubgroupAverage.ofFiniteIndexFixers
    {G V : Type*} [Group G] [AddCommGroup V] [Module Complex V]
    (rho : MonoidHom G (Module.End Complex V)) (K : Subgroup G)
    (hFinite : forall v : V, exists N : Subgroup K,
      And N.FiniteIndex (forall n : N, rho n.val.val v = v)) :
    HeckeLocalSubgroupAverage rho K := by
  apply HeckeLocalSubgroupAverage.ofFiniteIndexNormalFixers rho K
  intro v
  choose N hN using hFinite v
  let : N.FiniteIndex := hN.1
  refine Exists.intro N.normalCore (And.intro inferInstance (And.intro inferInstance ?_))
  intro n
  exact hN.2 (Subtype.mk n.val (Subgroup.normalCore_le N n.property))

/-- A smooth representation admits averaging over every compact subgroup. -/
def HeckeLocalSubgroupAverage.ofCompactSmooth
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module Complex V]
    (rho : MonoidHom G (Module.End Complex V)) (K : Subgroup G)
    (hK : IsCompact (K : Set G))
    (hSmooth : forall v : V, Filter.Eventually (fun g : G => rho g v = v) (nhds 1)) :
    HeckeLocalSubgroupAverage rho K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let r := rho.comp K.subtype
  apply HeckeLocalSubgroupAverage.ofFiniteIndexFixers rho K
  intro v
  let N : Subgroup K :=
    { carrier := {k | r k v = v}
      one_mem' := by
        change r 1 v = v
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        change r a v = v at ha
        change r b v = v at hb
        change r (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        change r a v = v at ha
        change r (Inv.inv a) v = v
        have h := congrArg (fun w => r (Inv.inv a) w) ha
        rw [<- Module.End.mul_apply, <- map_mul, inv_mul_cancel, map_one] at h
        exact h.symm }
  have hAt : Filter.Eventually (fun k : K => Membership.mem N k) (nhds (1 : K)) := by
    exact (continuous_subtype_val.tendsto (1 : K)).eventually (hSmooth v)
  have hOpen : IsOpen (N : Set K) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hCont : Continuous (fun y : K => Inv.inv x * y) := continuous_const.mul continuous_id
    have hMove : Filter.Tendsto (fun y : K => Inv.inv x * y) (nhds x) (nhds 1) := by
      simpa only [inv_mul_cancel] using hCont.tendsto x
    exact (hMove.eventually hAt).mono (fun y hy => by
      have hEq : x * (Inv.inv x * y) = y := by simp
      change Membership.mem N y
      rw [<- hEq]
      exact N.mul_mem hx hy)
  let : Finite (SubgroupCosets N) := Subgroup.quotient_finite_of_isOpen N hOpen
  refine Exists.intro N (And.intro Subgroup.finiteIndex_of_finite_quotient ?_)
  intro n
  exact n.property

end Robin1984.GRH
