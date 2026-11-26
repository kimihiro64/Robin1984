import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Minkowski's convex body theorem, Gram-Schmidt orthogonalization, and restriction of scalars.
- Formalization note: Selects short field-independent rows with integral preimages and bounds their length product by the real lattice covolume.
- PROVENANCE-END
-/

/-! # Short independent lattice rows over a finite field extension -/

set_option autoImplicit false

open MeasureTheory

namespace Robin1984.GRH

section FieldRowSelection

variable (F K V : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [AddCommGroup V] [Module F V] [Module K V] [IsScalarTower F K V]

/-- A rationally independent prefix of length d * i + 1 contains a row
outside the K-span of any i given rows, where d is the extension degree. -/
theorem exists_prefixRow_outside_extensionSpan
    {m i : Nat} (p : Fin m -> V) (hp : LinearIndependent F p)
    (v : Fin i -> V) (hLen : Module.finrank F K * i < m) :
    exists j : Fin m, And (j.val <= Module.finrank F K * i)
      (Not (Membership.mem (Submodule.span K (Set.range v)) (p j))) := by
  let W := Submodule.span K (Set.range v)
  let _ : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range v)
  let _ : FiniteDimensional F W := FiniteDimensional.trans F K W
  have hW : Module.finrank K W <= i := by
    change Set.finrank K (Set.range v) <= i
    simpa only [Fintype.card_fin] using (finrank_range_le_card (R := K) v)
  have hDim : Module.finrank F W <= Module.finrank F K * i := by
    rw [<- Module.finrank_mul_finrank F K W]
    exact Nat.mul_le_mul_left _ hW
  let P : Fin (Module.finrank F K * i + 1) -> Fin m := Fin.castLE (Nat.succ_le_of_lt hLen)
  have hP : Function.Injective P :=
    fun a b h => Fin.ext (congrArg (fun j : Fin m => j.val) h)
  by_contra h
  have hInside (j : Fin (Module.finrank F K * i + 1)) : Membership.mem W (p (P j)) :=
    Classical.byContradiction (fun hj =>
      h (Exists.intro (P j) (And.intro (Nat.le_of_lt_succ j.isLt) hj)))
  let w (j : Fin (Module.finrank F K * i + 1)) : W := Subtype.mk (p (P j)) (hInside j)
  have hInd : LinearIndependent F w :=
    LinearIndependent.of_comp (W.subtype.restrictScalars F) (hp.comp P hP)
  have hCard := hInd.fintype_card_le_finrank
  rw [Fintype.card_fin] at hCard
  exact (Nat.not_succ_le_self _) (hCard.trans hDim)

/-- From an F-linearly independent list ordered by length, the j-th
K-independent row can be chosen at index at most d * j, with zero-based
indices. The conclusion is stated on indices and applies to any row norm. -/
theorem exists_extensionIndependent_rows_from_prefixes
    {m : Nat} (p : Fin m -> V) (hp : LinearIndependent F p)
    (n : Nat) (hLen : forall i : Fin n, Module.finrank F K * i.val < m) :
    exists q : Fin n -> Fin m,
      And (LinearIndependent K (Function.comp p q))
        (forall i : Fin n, (q i).val <= Module.finrank F K * i.val) := by
  induction n with
  | zero =>
    exact Exists.intro Fin.elim0 (And.intro (linearIndependent_empty_type) (fun i => Fin.elim0 i))
  | succ n ih =>
    have hShort (i : Fin n) : Module.finrank F K * i.val < m := hLen i.castSucc
    choose q hq using ih hShort
    choose j hj using exists_prefixRow_outside_extensionSpan F K V p hp (Function.comp p q)
      (hLen (Fin.last n))
    let r := @Fin.snoc n (fun _ => Fin m) q j
    have heq : Function.comp p r = @Fin.snoc n (fun _ => V) (Function.comp p q) (p j) := by
      funext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      . simp [r, Function.comp_def]
      . simp [r, Function.comp_def]
    refine Exists.intro r (And.intro ?_ ?_)
    . rw [heq]
      exact linearIndependent_finSnoc.mpr (And.intro hq.1 hj.2)
    . intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      . simpa [r] using hj.1
      . simpa [r] using hq.2 k


/-- Over an extension of degree d, an increasing list of n * d
nonnegative row lengths contains an extension-independent selection whose
product to the d-th power is bounded by the full list's product. -/
theorem exists_extensionIndependent_rows_with_product_le
    (n : Nat) (p : Fin (n * Module.finrank F K) -> V) (hp : LinearIndependent F p)
    (z : Fin (n * Module.finrank F K) -> Real) (hz : Monotone z) (h0 : forall i, 0 <= z i) :
    exists q : Fin n -> Fin (n * Module.finrank F K),
      And (LinearIndependent K (Function.comp p q))
        (Finset.univ.prod (fun i => z (q i) ^ Module.finrank F K) <= Finset.univ.prod z) := by
  let d := Module.finrank F K
  have hd : 0 < d := Module.finrank_pos
  have hLen (i : Fin n) : d * i.val < n * d := by
    rw [Nat.mul_comm d i.val]
    exact Nat.mul_lt_mul_of_pos_right i.isLt hd
  choose q hq using exists_extensionIndependent_rows_from_prefixes F K V p hp n hLen
  refine Exists.intro q (And.intro hq.1 ?_)
  let E : Equiv (Prod (Fin n) (Fin d)) (Fin (n * d)) := finProdFinEquiv
  have hIdx (i : Fin n) (j : Fin d) : q i <= E (Prod.mk i j) := by
    change (q i).val <= (finProdFinEquiv (Prod.mk i j)).val
    rw [finProdFinEquiv_apply_val]
    exact (hq.2 i).trans (Nat.le_add_left _ _)
  calc
    Finset.univ.prod (fun i => z (q i) ^ Module.finrank F K) =
        Finset.univ.prod (fun i : Fin n => Finset.univ.prod (fun _ : Fin d => z (q i))) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, d]
    _ <= Finset.univ.prod (fun i : Fin n => Finset.univ.prod
        (fun j : Fin d => z (E (Prod.mk i j)))) := by
      apply Finset.prod_le_prod
      . intro i hi
        exact Finset.prod_nonneg (fun _ _ => h0 _)
      . intro i hi
        exact Finset.prod_le_prod (fun _ _ => h0 _) (fun j _ => hz (hIdx i j))
    _ = Finset.univ.prod (fun p : Prod (Fin n) (Fin d) => z (E p)) :=
      (Fintype.prod_prod_type (fun p : Prod (Fin n) (Fin d) => z (E p))).symm
    _ = Finset.univ.prod z := E.prod_comp z

end FieldRowSelection

section SuccessiveRows

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [ProperSpace E]

/-- A discrete lattice has a shortest vector outside any subspace it
is not contained in. The comparison holds over the entire lattice. -/
theorem exists_shortest_latticeVector_outside_subspace
    (L : Submodule Int E) [DiscreteTopology L] (W : Submodule Real E)
    (h : exists w : L, Not (Membership.mem W w.val)) :
    exists v : L, And (Not (Membership.mem W v.val))
      (forall w : L, Not (Membership.mem W w.val) -> norm v.val <= norm w.val) := by
  classical
  choose w hw using h
  let A := Set.preimage (Subtype.val : L -> E) (Metric.closedBall 0 (norm w.val))
  let B : Set L := {u | And (A.Mem u) (Not (Membership.mem W u.val))}
  have hClosed : IsClosed (L : Set E) := AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  have hA : A.Finite :=
    (hClosed.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_closedBall _ _)).finite_of_discrete
  have hB : B.Finite := hA.subset (fun _ hu => hu.1)
  have hIn (u : L) : A.Mem u <-> norm u.val <= norm w.val := by
    change dist u.val 0 <= norm w.val <-> _
    rw [dist_zero_right]
  have hwB : B.Mem w := And.intro ((hIn w).mpr le_rfl) hw
  have hb : hB.toFinset.Nonempty := Exists.intro w (hB.mem_toFinset.mpr hwB)
  choose v hv using Finset.exists_min_image hB.toFinset (fun u : L => norm u.val) hb
  have hvB := hB.mem_toFinset.mp hv.1
  refine Exists.intro v (And.intro hvB.2 ?_)
  intro u hu
  by_cases hle : norm u.val <= norm w.val
  . exact hv.2 u (hB.mem_toFinset.mpr (And.intro ((hIn u).mpr hle) hu))
  . exact (hv.2 w (hB.mem_toFinset.mpr hwB)).trans (le_of_lt (lt_of_not_ge hle))


private theorem finSnoc_image_Iio_castSucc {X : Type*} {n : Nat}
    (v : Fin n -> X) (w : X) (i : Fin n) :
    Set.image (@Fin.snoc n (fun _ => X) v w) (Set.Iio i.castSucc) = Set.image v (Set.Iio i) := by
  ext x
  constructor
  . intro h
    choose j hj using h
    have hjlt : j.val < i.val := hj.1
    let k := j.castLT (lt_trans hjlt i.isLt)
    have hk : k.castSucc = j := Fin.ext rfl
    exact Exists.intro k (And.intro hjlt (by simpa only [<- hk, Fin.snoc_castSucc] using hj.2))
  . intro h
    choose j hj using h
    exact Exists.intro j.castSucc (And.intro hj.1 (by simpa only [Fin.snoc_castSucc] using hj.2))

private theorem finSnoc_image_Iio_last {X : Type*} {n : Nat}
    (v : Fin n -> X) (w : X) :
    Set.image (@Fin.snoc n (fun _ => X) v w) (Set.Iio (Fin.last n)) = Set.range v := by
  ext x
  constructor
  . intro h
    choose j hj using h
    have hjlt : j.val < n := hj.1
    let k := j.castLT hjlt
    have hk : k.castSucc = j := Fin.ext rfl
    exact Exists.intro k (by simpa only [<- hk, Fin.snoc_castSucc] using hj.2)
  . intro h
    choose j hj using h
    exact Exists.intro j.castSucc (And.intro j.isLt (by simpa only [Fin.snoc_castSucc] using hj))

/-- The row at i minimizes the norm among all lattice vectors outside
the real span of the rows with strictly smaller index. -/
def IsSuccessiveShortestLatticeRows (L : Submodule Int E) {m : Nat} (v : Fin m -> L) : Prop :=
  forall i : Fin m,
    let W := Submodule.span Real (Set.image (Function.comp Subtype.val v) (Set.Iio i))
    And (Not (Membership.mem W (v i).val))
      (forall w : L, Not (Membership.mem W w.val) -> norm (v i).val <= norm w.val)

/-- Successively minimizing the norm outside the current real span
produces a linearly independent sequence up to the real dimension. -/
theorem exists_successive_shortest_latticeRows
    (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L]
    (m : Nat) (hm : m <= Module.finrank Real E) :
    exists v : Fin m -> L,
      And (LinearIndependent Real (Function.comp Subtype.val v)) (IsSuccessiveShortestLatticeRows L v) := by
  induction m with
  | zero => exact Exists.intro Fin.elim0 (And.intro linearIndependent_empty_type (fun i => Fin.elim0 i))
  | succ m ih =>
    choose v hv using ih (Nat.le_of_succ_le hm)
    let P := Function.comp (@Subtype.val E (fun x => Membership.mem L x)) v
    let W := Submodule.span Real (Set.range P)
    have hDim : Module.finrank Real W <= m := by
      change Set.finrank Real (Set.range P) <= m
      simpa only [Fintype.card_fin] using (finrank_range_le_card (R := Real) P)
    have hTop : W < Top.top :=
      Submodule.lt_top_of_finrank_lt_finrank (hDim.trans_lt (Nat.lt_of_succ_le hm))
    have hOut : exists x : L, Not (Membership.mem W x.val) := by
      by_contra h
      have hLe : Submodule.span Real (L : Set E) <= W := by
        apply Submodule.span_le.mpr
        intro x hx
        exact Classical.byContradiction (fun hW => h (Exists.intro (Subtype.mk x hx) hW))
      rw [IsZLattice.span_top (K := Real)] at hLe
      exact (not_le_of_gt hTop) hLe
    choose w hw using exists_shortest_latticeVector_outside_subspace L W hOut
    let r := @Fin.snoc m (fun _ => L) v w
    have hr : Function.comp Subtype.val r = @Fin.snoc m (fun _ => E) P w.val := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      . simp only [r, Function.comp_apply, Fin.snoc_last]
      . simp only [r, P, Function.comp_apply, Fin.snoc_castSucc]
    refine Exists.intro r (And.intro ?_ ?_)
    . rw [hr]
      exact linearIndependent_finSnoc.mpr (And.intro hv.1 hw.1)
    . intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      . simp only [hr, finSnoc_image_Iio_last, r, Fin.snoc_last]
        exact hw
      . simp only [hr, finSnoc_image_Iio_castSucc, r, Fin.snoc_castSucc]
        exact hv.2 j

end SuccessiveRows

/-- Decreasing the denominator at every nonzero coordinate before
the last support index can only increase the squared Euclidean norm. -/
theorem one_le_sum_scaled_squares_of_last_support
    {m : Nat} (a w : Fin m -> Real) (hw : forall i, 0 < w i) (hm : Monotone w)
    (j : Fin m) (hLast : forall i, j < i -> a i = 0)
    (hNorm : w j ^ 2 <= Finset.univ.sum (fun i => a i ^ 2)) :
    1 <= Finset.univ.sum (fun i => (a i / w i) ^ 2) := by
  have hPoint (i : Fin m) : a i ^ 2 / w j ^ 2 <= (a i / w i) ^ 2 := by
    rw [div_pow]
    by_cases h : i <= j
    . have hsq : w i ^ 2 <= w j ^ 2 := by
        simpa only [pow_two] using mul_le_mul (hm h) (hm h) (hw i).le (hw j).le
      exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos (hw i) _) hsq
    . simp only [hLast i (lt_of_not_ge h), zero_pow (by decide : Not (2 = 0)), zero_div, le_refl]
  calc
    (1 : Real) = w j ^ 2 / w j ^ 2 := (div_self (pow_ne_zero _ (hw j).ne')).symm
    _ <= Finset.univ.sum (fun i => a i ^ 2) / w j ^ 2 :=
      div_le_div_of_nonneg_right hNorm (sq_nonneg _)
    _ = Finset.univ.sum (fun i => a i ^ 2 / w j ^ 2) := Finset.sum_div _ _ _
    _ <= Finset.univ.sum (fun i => (a i / w i) ^ 2) := Finset.sum_le_sum (fun i _ => hPoint i)

/-- An invertible linear map under which every nonzero lattice vector has
norm at least one bounds the volume of the corresponding open ellipsoid
by the covolume times two to the real dimension. -/
theorem inv_det_mul_unitBall_volume_le_covolume_mul_two_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (L : AddSubgroup E) [Countable L] (D : Set E) (hD : IsAddFundamentalDomain L D mu)
    (A : LinearMap (RingHom.id Real) E E) (hDet : Not (LinearMap.det A = 0))
    (hEmpty : forall x : L, Not (x = 0) -> 1 <= norm (A x.val)) :
    ENNReal.ofReal (abs (Inv.inv (LinearMap.det A))) * mu (Metric.ball 0 1) <=
      mu D * 2 ^ Module.finrank Real E := by
  let U : Set E := Metric.ball 0 1
  let S := Set.preimage A U
  have hSym (x : E) (hx : S.Mem x) : S.Mem (-x) := by
    change dist (A (-x)) 0 < 1
    change dist (A x) 0 < 1 at hx
    simpa only [map_neg, dist_zero_right, norm_neg] using hx
  have hConv : Convex Real S := (convex_ball (0 : E) (1 : Real)).linear_preimage A
  have hVol : mu S <= mu D * 2 ^ Module.finrank Real E := by
    apply le_of_not_gt
    intro hBig
    choose x hx using exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hD hSym hConv hBig
    have hBall : dist (A x.val) 0 < 1 := hx.2
    rw [dist_zero_right] at hBall
    exact (not_lt_of_ge (hEmpty x hx.1)) hBall
  have hChange : mu S = ENNReal.ofReal (abs (Inv.inv (LinearMap.det A))) * mu U :=
    Measure.addHaar_preimage_linearMap mu hDet U
  rw [hChange] at hVol
  exact hVol

section ShortRowsVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [ProperSpace E] [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 900000 in
/-- A real lattice has a full independent sequence of lattice vectors
whose increasing lengths have product bounded by the covolume times
two to the dimension divided by the volume of the open unit ball. -/
theorem exists_shortest_latticeRows_normProduct_mul_unitBall_le
    (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L] [Countable L]
    (mu : Measure E) [mu.IsAddHaarMeasure] (D : Set E)
    (hD : IsAddFundamentalDomain L.toAddSubgroup D mu) :
    exists v : Fin (Module.finrank Real E) -> L,
      And (LinearIndependent Real (Function.comp Subtype.val v))
        (And (Monotone (fun i => norm (v i).val))
          (ENNReal.ofReal (Finset.univ.prod (fun i => norm (v i).val)) *
            mu (Metric.ball 0 1) <= mu D * 2 ^ Module.finrank Real E)) := by
  classical
  let n := Module.finrank Real E
  choose v hv using exists_successive_shortest_latticeRows L n le_rfl
  let P := Function.comp (@Subtype.val E (fun x => Membership.mem L x)) v
  let W (i : Fin n) := Submodule.span Real (Set.image P (Set.Iio i))
  let w (i : Fin n) := norm (v i).val
  have hPos (i : Fin n) : 0 < w i := by
    apply norm_pos_iff.mpr
    intro h
    apply (hv.2 i).1
    change Membership.mem (W i) (v i).val
    rw [h]
    exact Submodule.zero_mem _
  have hMono : Monotone w := by
    intro i j hij
    have hSub : W i <= W j := Submodule.span_mono
      (Set.image_mono (Set.Iio_subset_Iio hij))
    exact (hv.2 i).2 (v j) (fun h => (hv.2 j).1 (hSub h))
  have hn : Module.finrank Real E = Fintype.card (Fin n) := (Fintype.card_fin n).symm
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hn P
  let e := b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 Real (Fin n -> Real))
  have hTri {i j : Fin n} (h : i < j) : e (P i) j = 0 :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular' hn P h
  have hSq (x : E) : norm x ^ 2 = Finset.univ.sum (fun i => e x i ^ 2) := by
    rw [<- b.repr.norm_map x]
    exact EuclideanSpace.real_norm_sq_eq (b.repr x)
  let M := Matrix.diagonal (fun i : Fin n => Inv.inv (w i))
  let A := e.symm.conj (Matrix.toLin' M)
  have hCoord (x : E) (i : Fin n) : e (A x) i = e x i / w i := by
    have hEq : e (A x) = Matrix.toLin' M (e x) := e.apply_symm_apply _
    rw [hEq, Matrix.toLin'_apply, show M = Matrix.diagonal (fun j => Inv.inv (w j)) from rfl,
      Matrix.mulVec_diagonal, div_eq_mul_inv, mul_comm]
  have hEmpty (x : L.toAddSubgroup) (hx : Not (x = 0)) : 1 <= norm (A x.val) := by
    let support := Finset.univ.filter (fun i : Fin n => Not (e x.val i = 0))
    have hSupport : support.Nonempty := by
      by_contra h
      apply hx
      apply Subtype.ext
      change x.val = (0 : E)
      apply e.injective
      rw [map_zero]
      funext i
      apply Classical.byContradiction
      intro hi
      exact h (Exists.intro i (Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) hi)))
    let j := support.max' hSupport
    have hj : Not (e x.val j = 0) := (Finset.mem_filter.mp (Finset.max'_mem support hSupport)).2
    have hLast (i : Fin n) (hi : j < i) : e x.val i = 0 := by
      apply Classical.byContradiction
      intro hb
      have hm : Membership.mem support i := Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) hb)
      exact (not_le_of_gt hi) (Finset.le_max' support i hm)
    let ell : LinearMap (RingHom.id Real) E Real := (LinearMap.proj j).comp e.toLinearMap
    have hSpan : W j <= ell.ker := by
      apply Submodule.span_le.mpr
      intro y hy
      choose i hi using hy
      rw [<- hi.2]
      exact LinearMap.mem_ker.mpr (hTri hi.1)
    have hout : Not (Membership.mem (W j) x.val) :=
      fun h => hj (LinearMap.mem_ker.mp (hSpan h))
    have hLen : w j <= norm x.val := (hv.2 j).2 x hout
    have hNorm : w j ^ 2 <= Finset.univ.sum (fun i => e x.val i ^ 2) := by
      rw [<- hSq]
      simpa only [pow_two] using mul_le_mul hLen hLen (norm_nonneg _) (norm_nonneg _)
    have hs := one_le_sum_scaled_squares_of_last_support (e x.val) w hPos hMono j hLast hNorm
    have hSqA := hSq (A x.val)
    simp_rw [hCoord] at hSqA
    rw [<- hSqA] at hs
    by_contra h
    have hl : norm (A x.val) < 1 := lt_of_not_ge h
    have hsq : norm (A x.val) ^ 2 < (1 : Real) := by
      calc
        norm (A x.val) ^ 2 <= norm (A x.val) * 1 := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left hl.le (norm_nonneg _)
        _ < 1 := by simpa only [mul_one] using hl
    exact (not_lt_of_ge hs) hsq
  have hProd : 0 < Finset.univ.prod w := Finset.prod_pos (fun i _ => hPos i)
  have hDet : LinearMap.det A = Inv.inv (Finset.univ.prod w) := by
    calc
      LinearMap.det A = LinearMap.det (Matrix.toLin' M) :=
        LinearMap.det_conj (Matrix.toLin' M) e.symm
      _ = _ := by
        rw [LinearMap.det_toLin', show M = Matrix.diagonal (fun j => Inv.inv (w j)) from rfl,
          Matrix.det_diagonal, Finset.prod_inv_distrib]
  have hDetNe : Not (LinearMap.det A = 0) := by rw [hDet]; exact inv_ne_zero hProd.ne'
  have hCov := inv_det_mul_unitBall_volume_le_covolume_mul_two_pow
    mu L.toAddSubgroup D hD A hDetNe hEmpty
  rw [hDet, inv_inv, abs_of_pos hProd] at hCov
  exact Exists.intro v (And.intro hv.1 (And.intro hMono hCov))

end ShortRowsVolume


section NumberFieldRows

variable {E K V : Type*} [Field K] [Algebra Rat K] [FiniteDimensional Rat K]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [ProperSpace E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
  [Module Rat E] [IsScalarTower Rat Real E]
  [AddCommGroup V] [Module Rat V] [Module K V] [IsScalarTower Rat K V]

/-- Lifting real lattice vectors through a rational-linear map gives
short independent rows in the source vector space over the number field.
The preimages stay in S, which is the integral row set in applications. -/
theorem exists_fieldIndependent_shortRows_of_latticeImage
    (n : Nat) (hDim : Module.finrank Real E = n * Module.finrank Rat K)
    (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L] [Countable L]
    (mu : Measure E) [mu.IsAddHaarMeasure] (D : Set E)
    (hD : IsAddFundamentalDomain L.toAddSubgroup D mu)
    (phi : LinearMap (RingHom.id Rat) V E) (S : Set V)
    (hLift : forall b : L, exists x : V, And (S.Mem x) (phi x = b.val)) :
    exists w : Fin n -> V,
      And (forall i, S.Mem (w i))
        (And (LinearIndependent K w)
          (ENNReal.ofReal (Finset.univ.prod (fun i => norm (phi (w i)) ^ Module.finrank Rat K)) *
            mu (Metric.ball 0 1) <= mu D * 2 ^ Module.finrank Real E)) := by
  choose v hv using exists_shortest_latticeRows_normProduct_mul_unitBall_le L mu D hD
  let d := Module.finrank Rat K
  let c : Equiv (Fin (n * d)) (Fin (Module.finrank Real E)) := finCongr hDim.symm
  have hLiftAll (i : Fin (n * d)) : exists x : V, And (S.Mem x) (phi x = (v (c i)).val) :=
    hLift (v (c i))
  choose p hp using hLiftAll
  let z (i : Fin (n * d)) := norm (phi (p i))
  have hz (i : Fin (n * d)) : z i = norm (v (c i)).val := congrArg norm (hp i).2
  have hQ : LinearIndependent Rat (Function.comp Subtype.val v) :=
    LinearIndependent.restrict_scalars' Rat hv.1
  have hpQ : LinearIndependent Rat p := by
    apply LinearIndependent.of_comp phi
    have hEq : Function.comp phi p = Function.comp (Function.comp Subtype.val v) c :=
      funext (fun i => (hp i).2)
    rw [hEq]
    exact hQ.comp c c.injective
  have hm : Monotone z := by
    intro i j hij
    change z i <= z j
    rw [hz, hz]
    exact hv.2.1 (show c i <= c j from hij)
  choose q hq using exists_extensionIndependent_rows_with_product_le Rat K V n p hpQ z hm
    (fun i => norm_nonneg (phi (p i)))
  let w := Function.comp p q
  refine Exists.intro w (And.intro (fun i => (hp (q i)).1) (And.intro hq.1 ?_))
  have hProd : Finset.univ.prod z = Finset.univ.prod (fun j => norm (v j).val) := by
    calc
      _ = Finset.univ.prod (fun i => norm (v (c i)).val) :=
        Finset.prod_congr rfl (fun i _ => hz i)
      _ = _ := c.prod_comp (fun j => norm (v j).val)
  have hLe : Finset.univ.prod (fun i => norm (phi (w i)) ^ d) <=
      Finset.univ.prod (fun j => norm (v j).val) := hq.2.trans_eq hProd
  exact (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hLe) zero_le).trans hv.2.2

end NumberFieldRows

end Robin1984.GRH
