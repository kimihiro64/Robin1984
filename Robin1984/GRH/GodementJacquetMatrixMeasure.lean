import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.LocalRing.Basic

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and the determinant change of variables for additive Haar measure on adelic matrices.
- Formalization note: Derives matrix Haar dilation from the rank-one multiplier by constructing unit pivots and proving measure preservation of adelic block shears.
- PROVENANCE-END
-/

/-!
# Additive Haar measure and invertible adelic matrices

An invertible matrix over the adeles admits a unit pivot after elementary
row operations. The coefficients for these operations are integral at
almost every finite place. Upper and lower block shears preserve the
product measure by translation invariance in the affected coordinates.

Induction on the matrix size transfers the one-dimensional Haar scaling
law to all finite adelic vectors. The factor is the rank-one multiplier
evaluated at the determinant.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain Filter

private theorem localRing_unitPivot {R : Type*} [CommRing R] [IsLocalRing R]
    (a b c d : R) (h : c * a + d * b = 1) :
    exists t : R, (t = 0 \/ t = 1) /\ IsUnit (a + t * b) := by
  by_cases ha : IsUnit a
  . exact Exists.intro 0 (And.intro (Or.inl rfl) (by simpa using ha))
  . have hc : Not (IsUnit (c * a)) := fun hca => ha (isUnit_of_mul_isUnit_right hca)
    have hb : IsUnit b :=
      isUnit_of_mul_isUnit_right ((IsLocalRing.isUnit_or_isUnit_of_add_one h).resolve_left hc)
    have he : (a + b) + (-a) = b := by
      rw [add_assoc, add_comm b, <- add_assoc, add_neg_cancel, zero_add]
    have hab : IsUnit (a + b) := by
      have hb' : IsUnit ((a + b) + (-a)) := by
        rw [he]
        exact hb
      exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hb').resolve_right
        (fun hn => ha (by simpa only [neg_neg] using hn.neg))
    exact Exists.intro 1 (And.intro (Or.inr rfl) (by simpa using hab))

variable (K : Type*) [Field K] [NumberField K]

private abbrev FinitePart := FiniteAdeleRing (RingOfIntegers K) K
private abbrev Place := HeightOneSpectrum (RingOfIntegers K)

private theorem exists_finiteAdele_unitPivot (a b c d : FinitePart K) (h : c * a + d * b = 1) :
    exists t : FinitePart K, IsUnit (a + t * b) := by
  classical
  let O (p : Place K) := p.adicCompletionIntegers K
  let good (p : Place K) :=
    Membership.mem (O p) (a p) /\ Membership.mem (O p) (b p) /\
      Membership.mem (O p) (c p) /\ Membership.mem (O p) (d p)
  have hgood : Filter.Eventually good cofinite :=
    a.property.and (b.property.and (c.property.and d.property))
  have hlocal (p : Place K) : c p * a p + d p * b p = 1 :=
    congrArg (fun x : FinitePart K => x p) h
  have hpivot (p : Place K) :
      exists t : p.adicCompletion K,
        (t = 0 \/ t = 1) /\ IsUnit (a p + t * b p) /\
          (good p -> exists hs : Membership.mem (O p) (a p + t * b p),
            IsUnit (Subtype.mk (a p + t * b p) hs : O p)) := by
    by_cases hp : good p
    . let A : O p := Subtype.mk (a p) hp.1
      let B : O p := Subtype.mk (b p) hp.2.1
      let C : O p := Subtype.mk (c p) hp.2.2.1
      let D : O p := Subtype.mk (d p) hp.2.2.2
      have hO : C * A + D * B = 1 := Subtype.ext (hlocal p)
      choose x hx using localRing_unitPivot A B C D hO
      refine Exists.intro x.val (And.intro ?_ (And.intro ?_ ?_))
      . exact hx.1.elim (fun h0 => Or.inl (congrArg Subtype.val h0))
          (fun h1 => Or.inr (congrArg Subtype.val h1))
      . exact hx.2.map (O p).toSubring.subtype
      . intro _
        exact Exists.intro (A + x * B).property hx.2
    . choose x hx using localRing_unitPivot (a p) (b p) (c p) (d p) (hlocal p)
      exact Exists.intro x (And.intro hx.1 (And.intro hx.2 (fun H => (hp H).elim)))
  choose t ht using hpivot
  let T : FinitePart K := Subtype.mk t (Filter.Eventually.of_forall (fun p =>
    (ht p).1.elim (fun h0 => by rw [h0]; exact (O p).zero_mem)
      (fun h1 => by rw [h1]; exact (O p).one_mem)))
  refine Exists.intro T ?_
  apply RestrictedProduct.isUnit_of_eventually_isUnit
  . intro p
    exact (ht p).2.1
  . exact hgood.mono (fun p hp => (ht p).2.2 hp)

omit [NumberField K] in
private theorem exists_infiniteAdele_unitPivot (a b c d : InfiniteAdeleRing K)
    (h : c * a + d * b = 1) :
    exists t : InfiniteAdeleRing K, IsUnit (a + t * b) := by
  have hlocal (p : InfinitePlace K) : c p * a p + d p * b p = 1 :=
    congrArg (fun x : InfiniteAdeleRing K => x p) h
  choose t ht using fun p => localRing_unitPivot (a p) (b p) (c p) (d p) (hlocal p)
  let u (p : InfinitePlace K) := (ht p).2.unit
  let T : InfiniteAdeleRing K := t
  let U : Units (InfiniteAdeleRing K) :=
    { val := fun p => (u p).val
      inv := fun p => (u p).inv
      val_inv := funext (fun p => (u p).val_inv)
      inv_val := funext (fun p => (u p).inv_val) }
  exact Exists.intro T (Exists.intro U (funext (fun p => (ht p).2.unit_spec)))

private theorem exists_adele_unitPivot (a b c d : AdeleRing (RingOfIntegers K) K)
    (h : c * a + d * b = 1) :
    exists t : AdeleRing (RingOfIntegers K) K, IsUnit (a + t * b) := by
  have hInf : c.1 * a.1 + d.1 * b.1 = 1 := congrArg Prod.fst h
  have hFin : c.2 * a.2 + d.2 * b.2 = 1 := congrArg Prod.snd h
  choose ti hi using exists_infiniteAdele_unitPivot K a.1 b.1 c.1 d.1 hInf
  choose tf hf using exists_finiteAdele_unitPivot K a.2 b.2 c.2 d.2 hFin
  let T : AdeleRing (RingOfIntegers K) K := Prod.mk ti tf
  let U : Units (AdeleRing (RingOfIntegers K) K) :=
    MulEquiv.prodUnits.symm (Prod.mk hi.unit hf.unit)
  refine Exists.intro T (Exists.intro U ?_)
  exact Prod.ext hi.unit_spec hf.unit_spec


private theorem transvection_product_one_row {R : Type*} [CommRing R]
    {I : Type*} [Fintype I] [DecidableEq I] (r : I) (M : Matrix I I R)
    (L : List (Matrix.TransvectionStruct I R)) (hL : forall t, List.Mem t L -> t.i = r) :
    (forall a b, Not (a = r) -> ((L.map Matrix.TransvectionStruct.toMatrix).prod * M) a b =
      M a b) /\
    (forall b, ((L.map Matrix.TransvectionStruct.toMatrix).prod * M) r b =
      M r b + (L.map (fun t => t.c * M t.j b)).sum) := by
  induction L with
  | nil => simp
  | cons t L ih =>
      have htr := hL t (List.mem_cons_self)
      have hrest := ih (fun u hu => hL u (List.mem_cons_of_mem t hu))
      have htj : Not (t.j = r) := fun h => t.hij (htr.trans h.symm)
      simp only [List.map_cons, List.prod_cons, Matrix.mul_assoc, List.sum_cons]
      constructor
      . intro a b ha
        rw [Matrix.TransvectionStruct.toMatrix, Matrix.transvection_mul_apply_of_ne
          _ _ _ _ (fun h => ha (h.trans htr)), hrest.1 _ _ ha]
      . intro b
        calc
          _ = ((L.map Matrix.TransvectionStruct.toMatrix).prod * M) r b +
                t.c * ((L.map Matrix.TransvectionStruct.toMatrix).prod * M) t.j b := by
                  rw [<- htr]
                  exact Matrix.transvection_mul_apply_same t.i t.j b t.c _
          _ = _ := by
            rw [hrest.1 _ _ htj, hrest.2 b, add_assoc, add_comm _ (t.c * M t.j b)]

private theorem exists_adeleMatrix_unitPivot (r : Nat)
    (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) (AdeleRing (RingOfIntegers K) K))
    (hM : IsUnit M) :
    exists L : List (Matrix.TransvectionStruct (Sum (Fin r) Unit)
        (AdeleRing (RingOfIntegers K) K)),
      IsUnit (((L.map Matrix.TransvectionStruct.toMatrix).prod * M) (Sum.inr ()) (Sum.inr ())) := by
  classical
  let j : Sum (Fin r) Unit := Sum.inr ()
  let N := hM.unit.inv
  have hNM : N * M = 1 := by
    rw [<- hM.unit_spec]
    exact hM.unit.inv_val
  let B := Finset.univ.sum (fun i : Fin r => N j (Sum.inl i) * M (Sum.inl i) j)
  have he : N j j * M j j + (1 : AdeleRing (RingOfIntegers K) K) * B = 1 := by
    have heval := congrArg (fun Q : Matrix _ _ _ => Q j j) hNM
    change (N * M) j j = (1 : Matrix _ _ _) j j at heval
    rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply_eq] at heval
    simpa [B, j, add_comm] using heval
  choose x hx using exists_adele_unitPivot K (M j j) B (N j j) 1 he
  let op (i : Fin r) : Matrix.TransvectionStruct (Sum (Fin r) Unit)
      (AdeleRing (RingOfIntegers K) K) :=
    { i := j, j := Sum.inl i, hij := by simp [j], c := x * N j (Sum.inl i) }
  let L := List.ofFn op
  have hL (t : Matrix.TransvectionStruct (Sum (Fin r) Unit)
      (AdeleRing (RingOfIntegers K) K)) (ht : List.Mem t L) : t.i = j := by
    obtain h := List.mem_ofFn.mp ht
    choose i hi using h
    rw [<- hi]
  have hrow := (transvection_product_one_row j M L hL).2 j
  refine Exists.intro L ?_
  rw [hrow]
  have hsum : (L.map (fun t => t.c * M t.j j)).sum = x * B := by
    change ((List.ofFn op).map (fun t => t.c * M t.j j)).sum =
      x * Finset.univ.sum (fun i : Fin r => N j (Sum.inl i) * M (Sum.inl i) j)
    rw [List.map_ofFn, Fin.sum_ofFn, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
  rwa [hsum]

private theorem unitPivot_block_elimination {I R : Type*}
    [Fintype I] [DecidableEq I] [CommRing R]
    (A : Matrix I I R) (B : Matrix I Unit R) (C : Matrix Unit I R) (u : Units R) :
    let D := Matrix.diagonal (fun _ : Unit => u.val)
    let V := Matrix.diagonal (fun _ : Unit => u.inv)
    let S := A - B * V * C
    let L := Matrix.fromBlocks 1 (-(B * V)) 0 1
    let Q := Matrix.fromBlocks 1 0 (-(V * C)) 1
    L * Matrix.fromBlocks A B C D * Q = Matrix.fromBlocks S 0 0 D /\
      Matrix.det (Matrix.fromBlocks A B C D) = Matrix.det S * u.val := by
  dsimp only
  let D := Matrix.diagonal (fun _ : Unit => u.val)
  let V := Matrix.diagonal (fun _ : Unit => u.inv)
  let S := A - B * V * C
  let L : Matrix (Sum I Unit) (Sum I Unit) R := Matrix.fromBlocks 1 (-(B * V)) 0 1
  let Q : Matrix (Sum I Unit) (Sum I Unit) R := Matrix.fromBlocks 1 0 (-(V * C)) 1
  have hVD : V * D = 1 := by
    change Matrix.diagonal _ * Matrix.diagonal _ = _
    simp [Matrix.diagonal_mul_diagonal]
  have hDV : D * V = 1 := by
    change Matrix.diagonal _ * Matrix.diagonal _ = _
    simp [Matrix.diagonal_mul_diagonal]
  have hB : -(B * V) * D = -B := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hVD, Matrix.mul_one]
  have hC : D * -(V * C) = -C := by
    rw [Matrix.mul_neg, <- Matrix.mul_assoc, hDV, Matrix.one_mul]
  have hL : L * Matrix.fromBlocks A B C D = Matrix.fromBlocks S 0 C D := by
    change Matrix.fromBlocks 1 (-(B * V)) 0 1 * Matrix.fromBlocks A B C D = _
    rw [Matrix.fromBlocks_multiply]
    simp [S, hB, Matrix.neg_mul, sub_eq_add_neg]
  have he : L * Matrix.fromBlocks A B C D * Q = Matrix.fromBlocks S 0 0 D := by
    rw [hL]
    change Matrix.fromBlocks S 0 C D * Matrix.fromBlocks 1 0 (-(V * C)) 1 = _
    rw [Matrix.fromBlocks_multiply]
    simp [hC]
  refine And.intro he ?_
  have hdetL : Matrix.det L = 1 := by simp [L]
  have hdetQ : Matrix.det Q = 1 := by simp [Q]
  have hdet := congrArg Matrix.det he
  change Matrix.det (Matrix.fromBlocks A B C D) = Matrix.det S * u.val
  simpa [Matrix.det_mul, hdetL, hdetQ, D] using hdet

open MeasureTheory

private theorem measurePreserving_dependentAdd {X A : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [AddGroup A]
    (nu : Measure X) (mu : Measure A) [SFinite nu] [SFinite mu] [mu.IsAddLeftInvariant]
    (hadd : Measurable (fun p : Prod A A => p.1 + p.2))
    (f : X -> A) (hf : Measurable f) :
    MeasurePreserving (fun p : Prod X A => Prod.mk p.1 (f p.1 + p.2))
      (nu.prod mu) (nu.prod mu) := by
  exact (MeasurePreserving.id nu).skew_product (g := fun x a => f x + a)
    (hadd.comp ((hf.comp measurable_fst).prodMk measurable_snd))
    (Filter.Eventually.of_forall (fun x => map_add_left_eq_self mu (f x)))

private theorem measurePreserving_update_add_other {I A : Type*}
    [Fintype I] [DecidableEq I] [MeasurableSpace A] [AddGroup A]
    (mu : Measure A) [SigmaFinite mu] [mu.IsAddLeftInvariant]
    (hadd : Measurable (fun p : Prod A A => p.1 + p.2))
    (i j : I) (hji : Not (j = i)) (f : A -> A) (hf : Measurable f) :
    MeasurePreserving
      (fun x : I -> A => fun k => if k = i then f (x j) + x k else x k)
      (Measure.pi (fun _ : I => mu)) (Measure.pi (fun _ : I => mu)) := by
  classical
  let p : I -> Prop := fun k => Not (k = i)
  let S := Subtype p
  let T := Subtype (fun k => Not (p k))
  let q : T := Subtype.mk i (fun h => h rfl)
  let k : S := Subtype.mk j hji
  let : Unique T := {
    default := q
    uniq := fun a => Subtype.ext (Classical.byContradiction a.property)
  }
  let nu : Measure (S -> A) := Measure.pi (fun _ : S => mu)
  let e0 := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => A) p
  let e1 := (MeasurableEquiv.refl (S -> A)).prodCongr
    (MeasurableEquiv.piUnique (fun _ : T => A))
  let e := e0.trans e1
  have he0 : MeasurePreserving e0 (Measure.pi (fun _ : I => mu))
      (nu.prod (Measure.pi (fun _ : T => mu))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : I => mu) p
  have he1 : MeasurePreserving e1 (nu.prod (Measure.pi (fun _ : T => mu)))
      (nu.prod mu) :=
    (MeasurePreserving.id nu).prod (measurePreserving_piUnique (fun _ : T => mu))
  have he := he1.comp he0
  have hh := measurePreserving_dependentAdd nu mu hadd
    (fun y : S -> A => f (y k)) (hf.comp (measurable_pi_apply k))
  have h := (MeasurePreserving.symm e he).comp (hh.comp he)
  convert h using 1
  funext x
  apply e.injective
  change e (fun a => if a = i then f (x j) + x a else x a) =
    e (e.symm (Prod.mk (e x).1 (f ((e x).1 k) + (e x).2)))
  rw [e.apply_symm_apply]
  apply Prod.ext
  . funext a
    change (if (a : I) = i then f (x j) + x a else x a) = x a
    exact if_neg a.property
  . change (if i = i then f (x j) + x i else x i) = f (x j) + x i
    exact if_pos rfl

private theorem measurePreserving_transvection_mulVec {I R : Type*}
    [Fintype I] [DecidableEq I] [MeasurableSpace R] [CommRing R]
    (mu : Measure R) [SigmaFinite mu] [mu.IsAddLeftInvariant]
    (hadd : Measurable (fun p : Prod R R => p.1 + p.2))
    (i j : I) (hij : Not (i = j)) (c : R)
    (hc : Measurable (fun x : R => c * x)) :
    MeasurePreserving (Matrix.mulVec (Matrix.transvection i j c))
      (Measure.pi (fun _ : I => mu)) (Measure.pi (fun _ : I => mu)) := by
  convert measurePreserving_update_add_other mu hadd i j (Ne.symm hij) (fun x => c * x) hc using 1
  funext x k
  let X : Matrix I Unit R := fun a _ => x a
  change (Matrix.transvection i j c * X) k () = if k = i then c * x j + x k else x k
  by_cases hi : k = i
  . subst k
    rw [if_pos rfl, Matrix.transvection_mul_apply_same]
    exact add_comm _ _
  . rw [if_neg hi, Matrix.transvection_mul_apply_of_ne _ _ _ _ hi]

private theorem measurePreserving_transvectionList_mulVec {I R : Type*}
    [Fintype I] [DecidableEq I] [MeasurableSpace R] [CommRing R]
    (mu : Measure R) [SigmaFinite mu] [mu.IsAddLeftInvariant]
    (hadd : Measurable (fun p : Prod R R => p.1 + p.2))
    (hmul : forall c : R, Measurable (fun x : R => c * x))
    (L : List (Matrix.TransvectionStruct I R)) :
    MeasurePreserving (Matrix.mulVec (L.map Matrix.TransvectionStruct.toMatrix).prod)
      (Measure.pi (fun _ : I => mu)) (Measure.pi (fun _ : I => mu)) := by
  induction L with
  | nil =>
      have h0 : Matrix.mulVec (1 : Matrix I I R) = id :=
        funext (fun x => Matrix.one_mulVec x)
      rw [List.map_nil, List.prod_nil, h0]
      exact MeasurePreserving.id _
  | cons t L ih =>
      have ht := measurePreserving_transvection_mulVec mu hadd t.i t.j t.hij t.c (hmul t.c)
      simpa only [Function.comp_def, List.map_cons, List.prod_cons,
        Matrix.TransvectionStruct.toMatrix, Matrix.mulVec_mulVec] using ht.comp ih

section Blocks

variable {I J R : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [MeasurableSpace R] [CommRing R]

omit [DecidableEq I] [DecidableEq J] in
private theorem split_fromBlocks_mulVec
    (A : Matrix I I R) (B : Matrix I J R) (C : Matrix J I R) (D : Matrix J J R)
    (x : Sum I J -> R) :
    let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Sum I J => R)
    e ((Matrix.fromBlocks A B C D).mulVec x) =
      Prod.mk (A.mulVec (e x).1 + B.mulVec (e x).2)
        (C.mulVec (e x).1 + D.mulVec (e x).2) := by
  dsimp only
  apply Prod.ext
  . funext k
    change (Matrix.fromBlocks A B C D).mulVec x (Sum.inl k) =
      A.mulVec (Function.comp x Sum.inl) k + B.mulVec (Function.comp x Sum.inr) k
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  . funext k
    change (Matrix.fromBlocks A B C D).mulVec x (Sum.inr k) =
      C.mulVec (Function.comp x Sum.inl) k + D.mulVec (Function.comp x Sum.inr) k
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private theorem measurePreserving_fromBlocks_upper_mulVec [MeasurableAdd R]
    (mu : Measure R) [SigmaFinite mu] [mu.IsAddLeftInvariant]
    (hadd : Measurable (fun p : Prod (I -> R) (I -> R) => p.1 + p.2))
    (B : Matrix I J R) (hB : Measurable B.mulVec) :
    MeasurePreserving (Matrix.fromBlocks 1 B 0 1).mulVec
      (Measure.pi (fun _ : Sum I J => mu)) (Measure.pi (fun _ : Sum I J => mu)) := by
  let nuI := Measure.pi (fun _ : I => mu)
  let nuJ := Measure.pi (fun _ : J => mu)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Sum I J => R)
  have he : MeasurePreserving e (Measure.pi (fun _ : Sum I J => mu)) (nuI.prod nuJ) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Sum I J => mu)
  let : nuI.IsAddLeftInvariant := by
    dsimp [nuI]
    infer_instance
  have hh := measurePreserving_dependentAdd nuJ nuI hadd B.mulVec hB
  have hIJ : MeasurePreserving (fun x : Prod (I -> R) (J -> R) => Prod.mk
      (B.mulVec x.2 + x.1) x.2) (nuI.prod nuJ) (nuI.prod nuJ) :=
    Measure.measurePreserving_swap.comp (hh.comp Measure.measurePreserving_swap)
  convert (MeasurePreserving.symm e he).comp (hIJ.comp he) using 1
  funext x
  apply e.injective
  change e ((Matrix.fromBlocks 1 B 0 1).mulVec x) =
    e (e.symm (Prod.mk (B.mulVec (e x).2 + (e x).1) (e x).2))
  rw [e.apply_symm_apply]
  exact (split_fromBlocks_mulVec 1 B 0 1 x).trans (by simp [e, add_comm])

private theorem measurePreserving_fromBlocks_lower_mulVec [MeasurableAdd R]
    (mu : Measure R) [SigmaFinite mu] [mu.IsAddLeftInvariant]
    (hadd : Measurable (fun p : Prod (J -> R) (J -> R) => p.1 + p.2))
    (C : Matrix J I R) (hC : Measurable C.mulVec) :
    MeasurePreserving (Matrix.fromBlocks 1 0 C 1).mulVec
      (Measure.pi (fun _ : Sum I J => mu)) (Measure.pi (fun _ : Sum I J => mu)) := by
  let nuI := Measure.pi (fun _ : I => mu)
  let nuJ := Measure.pi (fun _ : J => mu)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Sum I J => R)
  have he : MeasurePreserving e (Measure.pi (fun _ : Sum I J => mu)) (nuI.prod nuJ) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Sum I J => mu)
  let : nuJ.IsAddLeftInvariant := by
    dsimp [nuJ]
    infer_instance
  have hh := measurePreserving_dependentAdd nuI nuJ hadd C.mulVec hC
  convert (MeasurePreserving.symm e he).comp (hh.comp he) using 1
  funext x
  apply e.injective
  change e ((Matrix.fromBlocks 1 0 C 1).mulVec x) =
    e (e.symm (Prod.mk (e x).1 (C.mulVec (e x).1 + (e x).2)))
  rw [e.apply_symm_apply]
  exact (split_fromBlocks_mulVec 1 0 C 1 x).trans (by simp [e])

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
private theorem measurable_matrix_mulVec
    (hadd : Measurable (fun p : Prod R R => p.1 + p.2))
    (hmul : forall c : R, Measurable (fun x : R => c * x)) (M : Matrix I J R) :
    Measurable M.mulVec := by
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  have hsum (s : Finset J) : Measurable (fun x : J -> R => s.sum (fun j => M i j * x j)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
        simpa only [Finset.sum_insert hj, Function.comp_def] using
          hadd.comp (((hmul (M i j)).comp (measurable_pi_apply j)).prodMk ih)
  exact hsum Finset.univ

omit [DecidableEq I] [DecidableEq J] in
private theorem map_fromBlocks_diagonal_mulVec
    (mu : Measure R) [SigmaFinite mu] (A : Matrix I I R) (D : Matrix J J R)
    (hA : Measurable A.mulVec) (hD : Measurable D.mulVec) (c d : NNReal)
    (hAscale : Measure.map A.mulVec (Measure.pi (fun _ : I => mu)) =
      HSMul.hSMul c (Measure.pi (fun _ : I => mu)))
    (hDscale : Measure.map D.mulVec (Measure.pi (fun _ : J => mu)) =
      HSMul.hSMul d (Measure.pi (fun _ : J => mu))) :
    Measure.map (Matrix.fromBlocks A 0 0 D).mulVec (Measure.pi (fun _ : Sum I J => mu)) =
      HSMul.hSMul (c * d) (Measure.pi (fun _ : Sum I J => mu)) := by
  let nu := Measure.pi (fun _ : Sum I J => mu)
  let nuI := Measure.pi (fun _ : I => mu)
  let nuJ := Measure.pi (fun _ : J => mu)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Sum I J => R)
  let f := Prod.map A.mulVec D.mulVec
  have he : MeasurePreserving e nu (nuI.prod nuJ) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Sum I J => mu)
  have hf : Measurable f := hA.prodMap hD
  have hsplit : Function.comp e.symm (Function.comp f e) = (Matrix.fromBlocks A 0 0 D).mulVec := by
    funext x
    apply e.injective
    change e (e.symm (f (e x))) = e ((Matrix.fromBlocks A 0 0 D).mulVec x)
    rw [e.apply_symm_apply]
    simpa [e, f, Prod.map] using (split_fromBlocks_mulVec A 0 0 D x).symm
  have hprod : Measure.map f (nuI.prod nuJ) = HSMul.hSMul (c * d) (nuI.prod nuJ) := by
    rw [<- Measure.map_prod_map nuI nuJ hA hD, hAscale, hDscale,
      Measure.prod_smul_left c, Measure.prod_smul_right d, smul_smul]
  change Measure.map _ nu = HSMul.hSMul (c * d) nu
  calc
    Measure.map (Matrix.fromBlocks A 0 0 D).mulVec nu =
        Measure.map e.symm (Measure.map f (Measure.map e nu)) := by
          rw [Measure.map_map hf e.measurable, Measure.map_map e.symm.measurable
            (hf.comp e.measurable), hsplit]
    _ = HSMul.hSMul (c * d) nu := by
      rw [he.map_eq, hprod, Measure.map_smul (c * d), (MeasurePreserving.symm e he).map_eq]

private theorem map_unit_diagonal_mulVec
    (mu : Measure R) [SigmaFinite mu] (a : R) (c : NNReal)
    (ha : Measurable (fun x : R => a * x))
    (hscale : Measure.map (fun x : R => a * x) mu = HSMul.hSMul c mu) :
    Measure.map (Matrix.diagonal (fun _ : Unit => a)).mulVec
        (Measure.pi (fun _ : Unit => mu)) =
      HSMul.hSMul c (Measure.pi (fun _ : Unit => mu)) := by
  let nu := Measure.pi (fun _ : Unit => mu)
  let e := MeasurableEquiv.piUnique (fun _ : Unit => R)
  have he : MeasurePreserving e nu mu := measurePreserving_piUnique (fun _ : Unit => mu)
  let f := fun x : R => a * x
  have h : Function.comp e.symm (Function.comp f e) =
      (Matrix.diagonal (fun _ : Unit => a)).mulVec := by
    funext x k
    cases k
    change a * x () = _
    simp
  change Measure.map _ nu = HSMul.hSMul c nu
  rw [<- h, <- Measure.map_map e.symm.measurable (ha.comp e.measurable),
    <- Measure.map_map ha e.measurable, he.map_eq, hscale, Measure.map_smul c,
    (MeasurePreserving.symm e he).map_eq]

omit [DecidableEq I] in
private theorem map_matrix_mulVec_mul
    (nu : Measure (I -> R)) (L M : Matrix I I R)
    (hL : Measurable L.mulVec) (hM : Measurable M.mulVec) :
    Measure.map (L * M).mulVec nu = Measure.map L.mulVec (Measure.map M.mulVec nu) := by
  rw [Measure.map_map hL hM]
  exact congrArg (fun f => Measure.map f nu) (funext (fun x => (Matrix.mulVec_mulVec x L M).symm))

private theorem map_mulVec_smul_iff_of_two_shears
    (nu : Measure (I -> R)) (L M Q : Matrix I I R) (hL : IsUnit L)
    (hm : forall P : Matrix I I R, Measurable P.mulVec)
    (hLp : MeasurePreserving L.mulVec nu nu) (hQp : MeasurePreserving Q.mulVec nu nu)
    (c : NNReal) :
    (Measure.map (L * M * Q).mulVec nu = HSMul.hSMul c nu) <->
      (Measure.map M.mulVec nu = HSMul.hSMul c nu) := by
  let N := hL.unit.inv
  have hNL : N * L = 1 := by
    rw [<- hL.unit_spec]
    exact hL.unit.inv_val
  have hinv (rho : Measure (I -> R)) :
      Measure.map N.mulVec (Measure.map L.mulVec rho) = rho := by
    rw [<- map_matrix_mulVec_mul rho N L (hm N) (hm L), hNL]
    have hId : Matrix.mulVec (1 : Matrix I I R) = id := funext Matrix.one_mulVec
    rw [hId, Measure.map_id]
  have hN : Measure.map N.mulVec nu = nu := by
    simpa only [hLp.map_eq] using hinv nu
  have hcomp : Measure.map (L * M * Q).mulVec nu =
      Measure.map L.mulVec (Measure.map M.mulVec nu) := by
    rw [map_matrix_mulVec_mul nu (L * M) Q (hm _) (hm _), hQp.map_eq,
      map_matrix_mulVec_mul nu L M (hm _) (hm _)]
  rw [hcomp]
  constructor
  . intro h
    calc
      Measure.map M.mulVec nu = Measure.map N.mulVec
          (Measure.map L.mulVec (Measure.map M.mulVec nu)) := (hinv _).symm
      _ = HSMul.hSMul c nu := by rw [h, Measure.map_smul c, hN]
  . intro h
    rw [h, Measure.map_smul c, hLp.map_eq]

end Blocks

private theorem map_mulVec_from_reindex {I J R : Type*}
    [Fintype I] [Fintype J] [MeasurableSpace R] [CommRing R]
    (mu : Measure R) [SigmaFinite mu]
    (hadd : Measurable (fun p : Prod R R => p.1 + p.2))
    (hmul : forall a : R, Measurable (fun x : R => a * x))
    (e : Equiv J I) (M : Matrix I I R) (c : NNReal)
    (h : Measure.map (M.submatrix e e).mulVec (Measure.pi (fun _ : J => mu)) =
      HSMul.hSMul c (Measure.pi (fun _ : J => mu))) :
    Measure.map M.mulVec (Measure.pi (fun _ : I => mu)) =
      HSMul.hSMul c (Measure.pi (fun _ : I => mu)) := by
  let M' := M.submatrix e e
  let nuI := Measure.pi (fun _ : I => mu)
  let nuJ := Measure.pi (fun _ : J => mu)
  let E := MeasurableEquiv.piCongrLeft (fun _ : I => R) e
  have he : MeasurePreserving E nuJ nuI := measurePreserving_piCongrLeft (fun _ : I => mu) e
  have hM : Measurable M.mulVec := measurable_matrix_mulVec hadd hmul M
  have hM' : Measurable M'.mulVec := measurable_matrix_mulVec hadd hmul M'
  have hc : Function.comp E M'.mulVec = Function.comp M.mulVec E := by
    funext v i
    choose k hk using e.surjective i
    subst i
    have hE (y : J -> R) (j : J) : E y (e j) = y j :=
      @MeasurableEquiv.piCongrLeft_apply_apply J I e (fun _ : I => R)
        (fun _ => inferInstance) y j
    simp only [Function.comp_apply, hE]
    change Finset.univ.sum (fun j : J => M (e k) (e j) * v j) =
      Finset.univ.sum (fun j : I => M (e k) j * E v j)
    simpa only [hE] using e.sum_comp (fun j : I => M (e k) j * E v j)
  change Measure.map M.mulVec nuI = HSMul.hSMul c nuI
  calc
    _ = Measure.map M.mulVec (Measure.map E nuJ) := by rw [he.map_eq]
    _ = Measure.map E (Measure.map M'.mulVec nuJ) := by
      rw [Measure.map_map hM E.measurable, Measure.map_map E.measurable hM', hc]
    _ = _ := by rw [h, Measure.map_smul c, he.map_eq]

section AdelecMeasure

variable {F : Type*} [Field F] [NumberField F]

private abbrev Adeles := AdeleRing (RingOfIntegers F) F

variable [MeasurableSpace (Adeles (F := F))] [MeasurableAdd (Adeles (F := F))]

private theorem map_adeleMatrix_mulVec_det_fin
    (mu : Measure (Adeles (F := F))) [SigmaFinite mu] [mu.IsAddLeftInvariant]
    (delta : MonoidHom (Adeles (F := F)) NNReal)
    (hadd : Measurable (fun p : Prod (Adeles (F := F)) (Adeles (F := F)) => p.1 + p.2))
    (hmul : forall a : Adeles (F := F), Measurable (fun x : Adeles (F := F) => a * x))
    (hscale : forall u : Units (Adeles (F := F)),
      Measure.map (fun x : Adeles (F := F) => u.val * x) mu = HSMul.hSMul (delta u.val) mu)
    (n : Nat) (M : Matrix (Fin n) (Fin n) (Adeles (F := F))) (hM : IsUnit M) :
    Measure.map M.mulVec (Measure.pi (fun _ : Fin n => mu)) =
      HSMul.hSMul (delta M.det) (Measure.pi (fun _ : Fin n => mu)) := by
  induction n with
  | zero =>
      have h : M.mulVec = id := funext (fun _ => funext (fun i => Fin.elim0 i))
      rw [h, Measure.map_id, Matrix.det_isEmpty, map_one, one_smul]
  | succ n ih =>
      let un : Equiv Unit (Fin 1) :=
        { toFun := fun _ => 0
          invFun := fun _ => ()
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _ }
      let J := Sum (Fin n) Unit
      let e : Equiv J (Fin (n + 1)) :=
        (Equiv.sumCongr (Equiv.refl (Fin n)) un).trans finSumFinEquiv
      let M' := M.submatrix e e
      let nu := Measure.pi (fun _ : J => mu)
      have hdetM' : M'.det = M.det := Matrix.det_submatrix_equiv_self e M
      have hMd := (Matrix.isUnit_iff_isUnit_det M).mp hM
      have hM' : IsUnit M' := (Matrix.isUnit_iff_isUnit_det M').mpr (by rwa [hdetM'])
      apply map_mulVec_from_reindex mu hadd hmul e M
      change Measure.map M'.mulVec nu = HSMul.hSMul (delta M.det) nu
      rw [<- hdetM']
      choose ops hpivot using exists_adeleMatrix_unitPivot F n M' hM'
      let P := (ops.map Matrix.TransvectionStruct.toMatrix).prod
      let N := P * M'
      let A := N.submatrix Sum.inl Sum.inl
      let B := N.submatrix Sum.inl Sum.inr
      let C := N.submatrix Sum.inr Sum.inl
      let u := hpivot.unit
      let D := Matrix.diagonal (fun _ : Unit => u.val)
      let V := Matrix.diagonal (fun _ : Unit => u.inv)
      let S := A - B * V * C
      let L : Matrix J J (Adeles (F := F)) := Matrix.fromBlocks 1 (-(B * V)) 0 1
      let Q : Matrix J J (Adeles (F := F)) := Matrix.fromBlocks 1 0 (-(V * C)) 1
      have hN : N = Matrix.fromBlocks A B C D := by
        ext i j
        cases i with
        | inl i => cases j <;> rfl
        | inr i =>
            cases i
            cases j with
            | inl j => rfl
            | inr j =>
                cases j
                change N (Sum.inr ()) (Sum.inr ()) = D () ()
                rw [show D () () = u.val by simp [D]]
                exact hpivot.unit_spec.symm
      have he : L * N * Q = Matrix.fromBlocks S 0 0 D /\ N.det = S.det * u.val := by
        rw [hN]
        exact unitPivot_block_elimination A B C u
      have hPdet : P.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod ops
      have hNdet : N.det = M'.det := by simp [N, Matrix.det_mul, hPdet]
      have hDet : M'.det = S.det * u.val := hNdet.symm.trans he.2
      have hSd : IsUnit S.det := isUnit_of_mul_isUnit_left
        (by rw [<- hDet]; exact (Matrix.isUnit_iff_isUnit_det M').mp hM')
      have hS := (Matrix.isUnit_iff_isUnit_det S).mpr hSd
      have hD := map_unit_diagonal_mulVec mu u.val (delta u.val) (hmul u.val) (hscale u)
      have hSplit : Measure.map (L * N * Q).mulVec nu =
          HSMul.hSMul (delta M'.det) nu := by
        rw [he.1, hDet, map_mul]
        exact map_fromBlocks_diagonal_mulVec mu S D (measurable_matrix_mulVec hadd hmul S)
          (measurable_matrix_mulVec hadd hmul D) _ _ (ih S hS) hD
      have hAddVec (T : Type) :
          Measurable (fun p : Prod (T -> Adeles (F := F)) (T -> Adeles (F := F)) =>
            p.1 + p.2) := by
        refine measurable_pi_lambda _ (fun i => ?_)
        change Measurable (fun p : Prod (T -> Adeles (F := F)) (T -> Adeles (F := F)) =>
          p.1 i + p.2 i)
        have hp : Measurable (fun y : T -> Adeles (F := F) => y i) := measurable_pi_apply i
        have hfst : Measurable (fun p : Prod (T -> Adeles (F := F)) (T -> Adeles (F := F)) =>
            p.1 i) := hp.comp measurable_fst
        have hsnd : Measurable (fun p : Prod (T -> Adeles (F := F)) (T -> Adeles (F := F)) =>
            p.2 i) := hp.comp measurable_snd
        exact hadd.comp (hfst.prodMk hsnd)
      have hLp : MeasurePreserving L.mulVec nu nu :=
        measurePreserving_fromBlocks_upper_mulVec mu (hAddVec (Fin n)) _
          (measurable_matrix_mulVec hadd hmul _)
      have hQp : MeasurePreserving Q.mulVec nu nu :=
        measurePreserving_fromBlocks_lower_mulVec mu (hAddVec Unit) _
          (measurable_matrix_mulVec hadd hmul _)
      have hm (P : Matrix J J (Adeles (F := F))) : Measurable P.mulVec :=
        measurable_matrix_mulVec hadd hmul P
      have hLdet : L.det = 1 := by
        change (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) (Adeles (F := F)))
          (-(B * V)) 0 (1 : Matrix Unit Unit (Adeles (F := F)))).det = 1
        simp
      have hL : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (by rw [hLdet]; exact isUnit_one)
      have hMapN := (map_mulVec_smul_iff_of_two_shears nu L N Q hL hm hLp hQp _).mp hSplit
      have hPp : MeasurePreserving P.mulVec nu nu :=
        measurePreserving_transvectionList_mulVec mu hadd hmul ops
      have hP : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr (by rw [hPdet]; exact isUnit_one)
      have hid : Matrix.mulVec (1 : Matrix J J (Adeles (F := F))) = id :=
        funext Matrix.one_mulVec
      have h1 : MeasurePreserving (Matrix.mulVec (1 : Matrix J J (Adeles (F := F)))) nu nu := by
        rw [hid]
        exact MeasurePreserving.id nu
      apply (map_mulVec_smul_iff_of_two_shears nu P M' 1 hP hm hPp h1 _).mp
      simpa only [Matrix.mul_one] using hMapN

/-- On a finite vector space over the adeles, the pushforward along an
invertible matrix is the product additive measure scaled by the rank-one
multiplier evaluated at its determinant. -/
theorem map_adeleMatrix_mulVec_det
    (mu : Measure (Adeles (F := F))) [SigmaFinite mu] [mu.IsAddLeftInvariant]
    (delta : MonoidHom (Adeles (F := F)) NNReal)
    (hadd : Measurable (fun p : Prod (Adeles (F := F)) (Adeles (F := F)) => p.1 + p.2))
    (hmul : forall a : Adeles (F := F), Measurable (fun x : Adeles (F := F) => a * x))
    (hscale : forall u : Units (Adeles (F := F)),
      Measure.map (fun x : Adeles (F := F) => u.val * x) mu = HSMul.hSMul (delta u.val) mu)
    {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I (Adeles (F := F))) (hM : IsUnit M) :
    Measure.map M.mulVec (Measure.pi (fun _ : I => mu)) =
      HSMul.hSMul (delta M.det) (Measure.pi (fun _ : I => mu)) := by
  let e := (Fintype.equivFin I).symm
  let N := M.submatrix e e
  have hdet : N.det = M.det := Matrix.det_submatrix_equiv_self e M
  have hN : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr (by
    rw [hdet]
    exact (Matrix.isUnit_iff_isUnit_det M).mp hM)
  apply map_mulVec_from_reindex mu hadd hmul e M
  rw [<- hdet]
  exact map_adeleMatrix_mulVec_det_fin mu delta hadd hmul hscale _ N hN

end AdelecMeasure

end Robin1984.GRH
