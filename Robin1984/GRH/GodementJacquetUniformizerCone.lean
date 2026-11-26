import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Robin1984.GRH.GodementJacquetOrderedDiagonalSeries

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Ordered diagonal exponent gaps and determinant multiplicativity.
- Formalization note: Identifies ordered exponents with uniformizer prefix directions and proves the corresponding rational matrix-coefficient series with the complex determinant weight.
- PROVENANCE-END
-/

/-!
# Uniformizer cones and complex determinant weights

Ordered valuations have unique nonnegative gap lengths. Each prefix direction
contributes its length times its number of diagonal coordinates to the
determinant exponent. The weighted generating series uses the resulting
powers of the norm of the uniformizer.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

/-- Nonnegative gaps give the decreasing sequence of their successive tail sums. -/
def orderedValuationConeExponents : (n : Nat) -> (Fin n -> Nat) -> (Fin n -> Nat)
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, gaps => Fin.cons (Finset.univ.sum gaps)
      (orderedValuationConeExponents n (fun i => gaps i.succ))

private theorem orderedValuationConeExponents_zero (n : Nat) (gaps : Fin (n + 1) -> Nat) :
    orderedValuationConeExponents (n + 1) gaps 0 = Finset.univ.sum gaps := by
  rw [orderedValuationConeExponents, Fin.cons_zero]

private theorem orderedValuationConeExponents_succ (n : Nat) (gaps : Fin (n + 1) -> Nat)
    (i : Fin n) : orderedValuationConeExponents (n + 1) gaps i.succ =
      orderedValuationConeExponents n (fun j => gaps j.succ) i := by
  rw [orderedValuationConeExponents, Fin.cons_succ]

/-- The exponent of each coordinate is the sum of the lengths of all
prefix directions that contain that coordinate. -/
theorem orderedValuationConeExponents_eq_sum (n : Nat) (gaps : Fin n -> Nat) (i : Fin n) :
    orderedValuationConeExponents n gaps i =
      Finset.univ.sum (fun j => if i <= j then gaps j else 0) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    next =>
      rw [orderedValuationConeExponents_zero]
      simp
    next =>
      rw [orderedValuationConeExponents_succ, Fin.sum_univ_succ, ih]
      simp [Fin.succ_le_succ_iff]

theorem antitone_orderedValuationConeExponents (n : Nat) (gaps : Fin n -> Nat) :
    Antitone (orderedValuationConeExponents n gaps) := by
  intro i j hij
  rw [orderedValuationConeExponents_eq_sum, orderedValuationConeExponents_eq_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hjk : j <= k
  next => simp [hjk, hij.trans hjk]
  next => simp [hjk]

/-- Every decreasing family of nonnegative valuations has a unique gap
vector. This includes zero rank and repeated valuations. -/
theorem existsUnique_orderedValuationConeExponents
    (n : Nat) (e : Fin n -> Nat) (he : Antitone e) :
    ExistsUnique (fun gaps : Fin n -> Nat => orderedValuationConeExponents n gaps = e) := by
  induction n with
  | zero =>
    refine Exists.intro (fun _ => 0) (And.intro ?_ ?_)
    next => exact Subsingleton.elim _ _
    next => intro _ _; exact Subsingleton.elim _ _
  | succ n ih =>
    have hTail : Antitone (fun i : Fin n => e i.succ) :=
      fun i j h => he (Fin.succ_le_succ_iff.mpr h)
    choose t ht using ih (fun i : Fin n => e i.succ) hTail
    have hPeak : Finset.univ.sum t <= e 0 := by
      cases n with
      | zero => simp
      | succ n =>
        rw [<- orderedValuationConeExponents_zero n t, ht.1]
        exact he (Fin.zero_le ((0 : Fin (n + 1)).succ))
    let gaps : Fin (n + 1) -> Nat := Fin.cons (e 0 - Finset.univ.sum t) t
    have hGaps : orderedValuationConeExponents (n + 1) gaps = e := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      next =>
        rw [orderedValuationConeExponents_zero, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact Nat.sub_add_cancel hPeak
      next =>
        rw [orderedValuationConeExponents_succ]
        exact congrFun ht.1 i
    refine Exists.intro gaps (And.intro hGaps ?_)
    intro other hOther
    have hTailEq : orderedValuationConeExponents n (fun i => other i.succ) =
        fun i => e i.succ := by
      funext i
      rw [<- orderedValuationConeExponents_succ]
      exact congrFun hOther i.succ
    have hEq : (fun i : Fin n => other i.succ) = t := ht.2 _ hTailEq
    have hHead := congrFun hOther 0
    rw [orderedValuationConeExponents_zero, Fin.sum_univ_succ, hEq] at hHead
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    next =>
      change other 0 = e 0 - Finset.univ.sum t
      omega
    next => exact congrFun hEq i

/-- The determinant exponent is the weighted sum of the gap lengths.
The direction indexed by i scales exactly i.val + 1 coordinates. -/
theorem sum_orderedValuationConeExponents (n : Nat) (gaps : Fin n -> Nat) :
    Finset.univ.sum (orderedValuationConeExponents n gaps) =
      Finset.univ.sum (fun i => (i.val + 1) * gaps i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = (Finset.univ.sum gaps) +
          Finset.univ.sum (fun i : Fin n => (i.val + 1) * gaps i.succ) := by
        rw [Fin.sum_univ_succ (f := orderedValuationConeExponents (n + 1) gaps),
          orderedValuationConeExponents_zero]
        simp only [orderedValuationConeExponents_succ, ih]
      _ = gaps 0 + Finset.univ.sum (fun i : Fin n => (i.succ.val + 1) * gaps i.succ) := by
        rw [Fin.sum_univ_succ (f := gaps), Nat.add_assoc, <- Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        have he : i.succ.val + 1 = 1 + (i.val + 1) := by
          simp only [Fin.val_succ]
          omega
        rw [he, Nat.add_mul 1 (i.val + 1) (gaps i.succ), one_mul]
      _ = _ := by
        rw [Fin.sum_univ_succ]
        simp

/-- The i-th direction multiplies the first i.val + 1 diagonal coordinates
by the uniformizer. -/
def valuationConePrefixUniformizer {F : Type*} [Field F]
    (n : Nat) (uniformizer : Units F) (i : Fin n) : Units (Fin n -> F) where
  val := fun j => if j <= i then uniformizer.val else 1
  inv := fun j => if j <= i then uniformizer.inv else 1
  val_inv := by
    funext j
    change (if j <= i then uniformizer.val else 1) *
      (if j <= i then uniformizer.inv else 1) = 1
    by_cases h : j <= i
    next => simpa only [if_pos h] using uniformizer.val_inv
    next => simp only [if_neg h, one_mul]
  inv_val := by
    funext j
    change (if j <= i then uniformizer.inv else 1) *
      (if j <= i then uniformizer.val else 1) = 1
    by_cases h : j <= i
    next => simpa only [if_pos h] using uniformizer.inv_val
    next => simp only [if_neg h, one_mul]

/-- Each positive-length direction stays in the ordered diagonal monoid
when the uniformizer valuation is at most one. -/
theorem monotone_valuationConePrefixUniformizer
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (uniformizer : Units F)
    (hu : v uniformizer.val <= 1) (k : Fin n) :
    Monotone (fun i => v ((valuationConePrefixUniformizer n uniformizer k).val i)) := by
  intro i j hij
  change v (if i <= k then uniformizer.val else 1) <=
    v (if j <= k then uniformizer.val else 1)
  by_cases hj : j <= k
  next => simp [hj, hij.trans hj]
  next =>
    by_cases hi : i <= k
    next => simpa only [if_pos hi, if_neg hj, v.map_one] using hu
    next => simp [hi, hj]

/-- The i-th diagonal entry of the product of prefix uniformizer
directions has the i-th ordered cone exponent. -/
theorem valuationConePrefixUniformizer_prod_apply
    {F : Type*} [Field F] (n : Nat) (uniformizer : Units F)
    (gaps : Fin n -> Nat) (i : Fin n) :
    (Finset.univ.prod (fun j => (valuationConePrefixUniformizer n uniformizer j) ^ gaps j)).val i =
      uniformizer.val ^ orderedValuationConeExponents n gaps i := by
  let ev : MonoidHom (Units (Fin n -> F)) F :=
    { toFun := fun a => a.val i
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  change ev (Finset.univ.prod _) = _
  rw [map_prod, orderedValuationConeExponents_eq_sum, <- Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_pow]
  change (if i <= j then uniformizer.val else 1) ^ gaps j =
    uniformizer.val ^ (if i <= j then gaps j else 0)
  by_cases h : i <= j <;> simp [h]

/-- The determinant of a translated product of prefix directions has the
weighted cone exponent used by the local matrix-coefficient series. -/
theorem det_valuationDiagonalSection_uniformizerCone
    {F : Type*} [Field F] (n : Nat) (uniformizer : Units F)
    (base : Units (Fin n -> F)) (gaps : Fin n -> Nat) :
    let dirs := Finset.univ.prod (fun j => (valuationConePrefixUniformizer n uniformizer j) ^ gaps j)
    ((valuationDiagonalSection F n (base * dirs)).val.val).det =
      ((valuationDiagonalSection F n base).val.val).det *
        uniformizer.val ^ Finset.univ.sum (fun j => (j.val + 1) * gaps j) := by
  intro dirs
  change (Matrix.diagonal (base.val * dirs.val)).det =
    (Matrix.diagonal base.val).det * _
  rw [show Matrix.diagonal (base.val * dirs.val) =
      Matrix.diagonal base.val * Matrix.diagonal dirs.val from
    map_mul (Matrix.diagonalRingHom (Fin n) F) base.val dirs.val, Matrix.det_mul]
  simp only [Matrix.det_diagonal]
  congr 1
  have hProd : Finset.univ.prod dirs.val =
      Finset.univ.prod (fun i => uniformizer.val ^ orderedValuationConeExponents n gaps i) := by
    apply Finset.prod_congr rfl
    intro i _
    exact valuationConePrefixUniformizer_prod_apply n uniformizer gaps i
  rw [hProd, Finset.prod_pow_eq_pow_sum, sum_orderedValuationConeExponents]

/-- A uniformizer prefix power is an ordered direction, with the
determinant gap weight recorded by its index. -/
def valuationUniformizerConeDirections
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (vf : Valuation F W) (n : Nat) (uniformizer : Units F) (hu : vf uniformizer.val <= 1)
    (i : Fin n) : valuationOrderedDiagonalSubmonoid vf n :=
  Subtype.mk (valuationConePrefixUniformizer n uniformizer i)
    (fun _ _ h => monotone_valuationConePrefixUniformizer vf n uniformizer hu i h)

/-- The weighted diagonal-cone expansion with the actual complex determinant
weight. The base determinant gives the prefactor. The reversed operator
polynomials, dilated by the determinant weights, give the denominator. -/
theorem valuationPrincipalCongruence_uniformizerCone_detSeries
    {F W V : Type*} [NormedField F] [LinearOrderedCommGroupWithZero W]
    [AddCommGroup V] [Module Complex V]
    (vf : Valuation F W) (n : Nat) (r : W) (hr : r < 1)
    (rho : MonoidHom (Units (Matrix (Fin n) (Fin n) F)) (Module.End Complex V))
    (P : HeckeLocalSubgroupAverage rho (valuationPrincipalCongruenceSubgroup vf n r))
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (uniformizer : Units F) (hu : vf uniformizer.val <= 1) :
    let directions := valuationUniformizerConeDirections vf n uniformizer hu
    let op := P.orderedDiagonalOperators vf n r hr rho
    let d := Module.finrank Complex (LinearMap.range P.proj)
    let denominator : Polynomial Complex := Finset.univ.prod (fun i =>
      (Finset.range (d + 1)).sum (fun j =>
        Polynomial.C ((op (directions i)).charpoly.coeff j) *
          Polynomial.X ^ ((i.val + 1) * (d - j))))
    forall (base : valuationOrderedDiagonalSubmonoid vf n)
      (ell : LinearMap (RingHom.id Complex) V Complex),
      (forall (k : valuationPrincipalCongruenceSubgroup vf n r) (u : V),
        ell (rho k.val u) = ell u) ->
      forall (u : V),
      (forall k : valuationPrincipalCongruenceSubgroup vf n r, rho k.val u = u) ->
      let matr (e : Fin n -> Nat) := (valuationDiagonalSection F n
        (base * Finset.univ.prod (fun i => directions i ^ e i)).val).val
      let baseMatrix := (valuationDiagonalSection F n base.val).val
      let weighted (s : Complex) (e : Fin n -> Nat) :=
        (norm (matr e).val.det : Complex) ^ s * ell (rho (matr e) u)
      exists numerator : Polynomial Complex,
        And (denominator.eval 0 = 1)
          (forall s : Complex, Summable (weighted s) ->
            let z := (norm uniformizer.val : Complex) ^ s
            denominator.eval z * tsum (weighted s) =
              (norm baseMatrix.val.det : Complex) ^ s * numerator.eval z) := by
  intro directions op d denominator base ell hEll u hU matr baseMatrix weighted
  have h := valuationPrincipalCongruence_diagonalCone_series
    vf n r hr rho P n directions (fun i => i.val + 1) (fun i => Nat.succ_pos i.val)
    base ell hEll u hU
  choose numerator hn using h
  refine Exists.intro numerator (And.intro hn.1 ?_)
  intro s hSum z
  let C := (norm baseMatrix.val.det : Complex) ^ s
  let E (e : Fin n -> Nat) := Finset.univ.sum (fun i => (i.val + 1) * e i)
  let aseq (e : Fin n -> Nat) := ell (rho (matr e) u)
  let seq (e : Fin n -> Nat) := aseq e * z ^ E e
  have hBase : Not (baseMatrix.val.det = 0) := by
    have hInv := congrArg (fun A : Matrix (Fin n) (Fin n) F => A.det) baseMatrix.val_inv
    change (baseMatrix.val * baseMatrix.inv).det = (1 : Matrix (Fin n) (Fin n) F).det at hInv
    rw [Matrix.det_mul, Matrix.det_one] at hInv
    intro h0
    rw [h0, zero_mul] at hInv
    exact zero_ne_one hInv
  have hC : Not (C = 0) := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hBase)))
  have hDirect (e : Fin n -> Nat) :
      (Finset.univ.prod (fun i => directions i ^ e i)).val =
        Finset.univ.prod (fun i => valuationConePrefixUniformizer n uniformizer i ^ e i) := by
    exact map_prod (valuationOrderedDiagonalSubmonoid vf n).subtype (fun i => directions i ^ e i) _
  have hDet (e : Fin n -> Nat) :
      (matr e).val.det = baseMatrix.val.det * uniformizer.val ^ E e := by
    change ((valuationDiagonalSection F n
      (base.val * (Finset.univ.prod (fun i => directions i ^ e i)).val)).val.val).det = _
    rw [hDirect]
    exact det_valuationDiagonalSection_uniformizerCone n uniformizer base.val e
  have hNormPow (k : Nat) :
      (((norm uniformizer.val) ^ k : Real) : Complex) ^ s = z ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ (norm uniformizer.val), Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _), ih]
      exact (pow_succ z k).symm
  have hTerm (e : Fin n -> Nat) : weighted s e = C * seq e := by
    change ((norm (matr e).val.det : Complex) ^ s) * aseq e = _
    rw [hDet, norm_mul, norm_pow, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _), hNormPow]
    change (C * z ^ E e) * aseq e = C * (aseq e * z ^ E e)
    ac_rfl
  have hSeq : Summable seq := by
    refine ((hSum.congr hTerm).mul_left (Inv.inv C)).congr ?_
    intro e
    change Inv.inv C * (C * seq e) = seq e
    rw [<- mul_assoc]
    simp [hC]
  have hTsum : tsum (weighted s) = C * tsum seq :=
    (tsum_congr hTerm).trans (hSeq.tsum_mul_left C)
  have hRatio : denominator.eval z * tsum seq = numerator.eval z := hn.2 z hSeq
  rw [hTsum, mul_left_comm, hRatio]

end Robin1984.GRH
