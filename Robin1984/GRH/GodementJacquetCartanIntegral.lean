import Robin1984.GRH.GodementJacquetCartanDoubleCosets
import Robin1984.GRH.HeckeEulerProduct

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Cartan double cosets of a general linear group over a nonarchimedean local field and countable additivity of the Bochner integral.
- Formalization note: Specializes the integral matrix partition to finite places and decomposes a determinant-weighted integral into its uniformizer gap coefficient series.
- PROVENANCE-END
-/

/-!
# Finite-place Cartan integrals

The integral matrix double cosets are compact and open. At a finite place,
the valuation gives a disjoint partition by uniformizer exponent gaps.
The determinant norm is constant on each coset, so the weighted integral
is a sum with one coefficient integral for each gap vector.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open IsDedekindDomain MeasureTheory NumberField

private theorem finiteUniformizerValue_lt_one_cartan : finiteUniformizerValue < 1 := by
  change ((Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) : WithZero (Multiplicative Int)) <
    ((1 : Multiplicative Int) : WithZero (Multiplicative Int))
  exact (@WithZero.coe_lt_coe (Multiplicative Int)
    (@instLTMultiplicative Int Int.instLTInt) (Multiplicative.ofAdd (-1 : Int)) 1).mpr
      (show (-1 : Int) < 0 by decide)

private theorem toAdd_uniformizer_pow_cartan (n : Nat) :
    Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : Int)) ^ n) = -(n : Int) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    change Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : Int)) ^ k) + (-1 : Int) =
      -(Nat.succ k : Int)
    rw [ih, Nat.cast_succ]
    ring

/-- Every nonzero valuation at most one is a nonnegative uniformizer power
for a valuation with values in integers with zero adjoined. -/
theorem exists_integral_valuation_eq_finiteUniformizerValue_pow
    {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative Int)))
    (x : Units F) (hx : v x.val <= 1) :
    exists e : Nat, v x.val = finiteUniformizerValue ^ e := by
  let xu := Units.map v.toMonoidHom x
  let z : Multiplicative Int := WithZero.unitsWithZeroEquiv xu
  have hz : (z : WithZero (Multiplicative Int)) = v x.val :=
    WithZero.coe_unitsWithZeroEquiv_eq_units_val xu
  have hLe : (z : WithZero (Multiplicative Int)) <=
      ((1 : Multiplicative Int) : WithZero (Multiplicative Int)) := hz.le.trans hx
  have hAdd : Multiplicative.toAdd z <= 0 :=
    (@WithZero.coe_le_coe (Multiplicative Int) (@instLEMultiplicative Int Int.instLEInt) z 1).mp hLe
  let e := Int.toNat (-Multiplicative.toAdd z)
  have he : (e : Int) = -Multiplicative.toAdd z := Int.toNat_of_nonneg (neg_nonneg.mpr hAdd)
  have heZ : z = (Multiplicative.ofAdd (-1 : Int)) ^ e := by
    have hEq : Multiplicative.toAdd z =
        Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : Int)) ^ e) := by
      rw [toAdd_uniformizer_pow_cartan, he, neg_neg]
    exact congrArg Multiplicative.ofAdd hEq
  refine Exists.intro e ?_
  rw [<- hz, heZ]
  exact WithZero.coe_pow _ _

/-- For a finite place the integral matrix locus is partitioned by the
uniformizer gap double cosets. -/
theorem iUnion_heckeLocal_valuationUniformizerGapDoubleCosets
    {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    (pi : Units (p.adicCompletion K))
    (hPi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue) :
    Set.iUnion (fun gaps : Fin n -> Nat =>
      valuationIntegralDiagonalDoubleCoset
        (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
        n (valuationUniformizerGapDiagonal n pi gaps)) =
      Set.ofPred (fun g : Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)) =>
        forall i j, Valued.v (g.val i j) <= (1 : WithZero (Multiplicative Int))) := by
  let v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
  have hPiLt : v pi.val < 1 := hPi.trans_lt finiteUniformizerValue_lt_one_cartan
  refine iUnion_valuationUniformizerGapDoubleCosets v n pi hPiLt ?_
  intro x hx
  have hVal : v pi.val = finiteUniformizerValue := hPi
  rw [hVal]
  exact exists_integral_valuation_eq_finiteUniformizerValue_pow v x hx


/-- An integral diagonal double coset is open when the valuation ring is
open. -/
theorem isOpen_valuationIntegralDiagonalDoubleCoset
    {F W : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LinearOrderedCommGroupWithZero W] (v : Valuation F W) (n : Nat)
    (a : Units (Fin n -> F)) (hInteger : IsOpen (v.integer : Set F)) :
    IsOpen (valuationIntegralDiagonalDoubleCoset v n a) := by
  let G := Units (Matrix (Fin n) (Fin n) F)
  let K := valuationIntegralMatrixSubgroup v n
  let d := (valuationDiagonalSection F n a).val
  let T (l : K) : G -> G := fun g => Inv.inv (l.val * d) * g
  have hOpen : IsOpen (K : Set G) := isOpen_valuationIntegralMatrixSubgroup v n hInteger
  have hSet : valuationIntegralDiagonalDoubleCoset v n a =
      Set.iUnion (fun l : K => Set.preimage (T l) (K : Set G)) := by
    ext g
    constructor
    . intro hg
      change (exists l r : K, g = l.val * d * r.val) at hg
      choose l r h using hg
      apply Set.mem_iUnion.mpr
      refine Exists.intro l ?_
      change Membership.mem K (Inv.inv (l.val * d) * g)
      rw [h, <- mul_assoc]
      simp [r.property]
    . intro hg
      choose l hl using Set.mem_iUnion.mp hg
      change Membership.mem K (T l g) at hl
      let r : K := Subtype.mk (T l g) hl
      change exists l r : K, g = l.val * d * r.val
      refine Exists.intro l (Exists.intro r ?_)
      change g = (l.val * d) * (Inv.inv (l.val * d) * g)
      rw [<- mul_assoc]
      simp
  rw [hSet]
  exact isOpen_iUnion (fun l => hOpen.preimage (continuous_const.mul continuous_id))

/-- An integral diagonal double coset is compact when the valuation ring
is compact. -/
theorem isCompact_valuationIntegralDiagonalDoubleCoset
    {F W : Type*} [Field F] [TopologicalSpace F] [T2Space F] [IsTopologicalRing F]
    [LinearOrderedCommGroupWithZero W] (v : Valuation F W) (n : Nat)
    (a : Units (Fin n -> F)) (hInteger : IsCompact (v.integer : Set F)) :
    IsCompact (valuationIntegralDiagonalDoubleCoset v n a) := by
  let G := Units (Matrix (Fin n) (Fin n) F)
  let K := valuationIntegralMatrixSubgroup v n
  let d := (valuationDiagonalSection F n a).val
  let M : Prod G G -> G := fun lr => lr.1 * d * lr.2
  have hK : IsCompact (K : Set G) :=
    isCompact_valuationIntegralMatrixSubgroup v n hInteger
  have hSet : valuationIntegralDiagonalDoubleCoset v n a =
      Set.image M (Set.prod (K : Set G) (K : Set G)) := by
    ext g
    constructor
    . intro hg
      change (exists l r : K, g = l.val * d * r.val) at hg
      choose l r h using hg
      exact Exists.intro (Prod.mk l.val r.val)
        (And.intro (And.intro l.property r.property) h.symm)
    . intro hg
      choose q hq using hg
      have hmem : And (Membership.mem K q.1) (Membership.mem K q.2) := hq.1
      change exists l r : K, g = l.val * d * r.val
      exact Exists.intro (Subtype.mk q.1 hmem.1)
        (Exists.intro (Subtype.mk q.2 hmem.2) hq.2.symm)
  rw [hSet]
  exact (hK.prod hK).image ((continuous_fst.mul continuous_const).mul continuous_snd)

/-- The finite-place matrix integral on the entrywise integral locus is the
sum of its integrals over the disjoint uniformizer gap double cosets. -/
theorem hasSum_heckeLocal_integral_valuationUniformizerGapDoubleCosets
    {K E : Type*} [Field K] [NumberField K]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (pi : Units (p.adicCompletion K))
    (hPi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue)
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    (f : Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)) -> E)
    (hInt : IntegrableOn f (Set.ofPred (fun g => forall i j,
      Valued.v (g.val i j : p.adicCompletion K) <= (1 : WithZero (Multiplicative Int)))) mu) :
    HasSum
      (fun gaps : Fin n -> Nat => integral (mu.restrict
        (valuationIntegralDiagonalDoubleCoset
          (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
          n (valuationUniformizerGapDiagonal n pi gaps))) f)
      (integral (mu.restrict (Set.ofPred (fun g => forall i j,
        Valued.v (g.val i j : p.adicCompletion K) <= (1 : WithZero (Multiplicative Int))))) f) := by
  let L := p.adicCompletion K
  let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
  let D (gaps : Fin n -> Nat) :=
    valuationIntegralDiagonalDoubleCoset v n (valuationUniformizerGapDiagonal n pi gaps)
  have hOpen : IsOpen (v.integer : Set L) := Valued.isOpen_valuationSubring L
  have hMeas (gaps : Fin n -> Nat) : MeasurableSet (D gaps) :=
    (isOpen_valuationIntegralDiagonalDoubleCoset v n _ hOpen).measurableSet
  have hPiLt : v pi.val < 1 := hPi.trans_lt finiteUniformizerValue_lt_one_cartan
  have hDisj := pairwiseDisjoint_valuationUniformizerGapDoubleCosets v n pi hPiLt
  have hUnion := iUnion_heckeLocal_valuationUniformizerGapDoubleCosets p n pi hPi
  change HasSum (fun gaps => integral (mu.restrict (D gaps)) f) _
  rw [<- hUnion]
  rw [<- hUnion] at hInt
  exact hasSum_integral_iUnion hMeas hDisj hInt

/-- The determinant has constant valuation on each integral diagonal double
coset. -/
theorem valuation_det_of_mem_valuationIntegralDiagonalDoubleCoset
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (v : Valuation F W) (n : Nat) (a : Units (Fin n -> F))
    (g : Units (Matrix (Fin n) (Fin n) F))
    (hg : Membership.mem (valuationIntegralDiagonalDoubleCoset v n a) g) :
    v g.val.det = v ((valuationDiagonalSection F n a).val.val).det := by
  change (exists left right : valuationIntegralMatrixSubgroup v n,
    g = left.val * (valuationDiagonalSection F n a).val * right.val) at hg
  choose left right hEq using hg
  have hL := valuation_det_integralMatrixUnit v n left.val left.property
  have hR := valuation_det_integralMatrixUnit v n right.val right.property
  rw [hEq]
  simp only [Units.val_mul, Matrix.det_mul, v.map_mul, hL, hR, one_mul, mul_one]

/-- The norm of a determinant on a finite-place uniformizer coset is
the corresponding power of the uniformizer norm. -/
theorem norm_det_of_mem_heckeLocal_valuationUniformizerGapDoubleCoset
    {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    (pi : Units (p.adicCompletion K)) (gaps : Fin n -> Nat)
    (g : Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))
    (hg : Membership.mem (valuationIntegralDiagonalDoubleCoset
      (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
        n (valuationUniformizerGapDiagonal n pi gaps)) g) :
    norm g.val.det = norm pi.val ^ Finset.univ.sum (fun j => (j.val + 1) * gaps j) := by
  let L := p.adicCompletion K
  let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
  let e : Nat := Finset.univ.sum (fun j => (j.val + 1) * gaps j)
  let a := valuationUniformizerGapDiagonal n pi gaps
  have hDiag : ((valuationDiagonalSection L n a).val.val).det = pi.val ^ e := by
    simpa [a, e, valuationUniformizerGapDiagonal] using
      (det_valuationDiagonalSection_uniformizerCone n pi (1 : Units (Fin n -> L)) gaps)
  have hv := valuation_det_of_mem_valuationIntegralDiagonalDoubleCoset v n a g hg
  rw [hDiag] at hv
  calc
    norm g.val.det = norm (pi.val ^ e) := by
      rw [FinitePlace.norm_def, FinitePlace.norm_def]
      rw [show Valued.v g.val.det = Valued.v (pi.val ^ e) from hv]
    _ = _ := norm_pow _ _

/-- The determinant-weighted local integral has one coefficient integral
per gap vector, multiplied by the determinant weight of its diagonal
representative. -/
theorem hasSum_heckeLocal_detWeightedIntegral_valuationUniformizerGapDoubleCosets
    {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (pi : Units (p.adicCompletion K))
    (hPi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue)
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    (f : Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)) -> Complex)
    (z : Complex) :
    let G := Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))
    let v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
    let A := Set.ofPred (fun g : G => forall i j, v (g.val i j) <= 1)
    let D (gaps : Fin n -> Nat) :=
      valuationIntegralDiagonalDoubleCoset v n (valuationUniformizerGapDiagonal n pi gaps)
    let F (g : G) := (norm g.val.det : Complex) ^ z * f g
    IntegrableOn F A mu ->
      HasSum
        (fun gaps : Fin n -> Nat =>
          ((norm pi.val : Complex) ^ z) ^ Finset.univ.sum (fun j => (j.val + 1) * gaps j) *
            integral (mu.restrict (D gaps)) f)
        (integral (mu.restrict A) F) := by
  intro G v A D F hInt
  have hOpen : IsOpen (v.integer : Set (p.adicCompletion K)) :=
    Valued.isOpen_valuationSubring (p.adicCompletion K)
  have hMeas (gaps : Fin n -> Nat) : MeasurableSet (D gaps) :=
    (isOpen_valuationIntegralDiagonalDoubleCoset v n _ hOpen).measurableSet
  let b := (norm pi.val : Complex) ^ z
  have hPow (k : Nat) : ((norm pi.val ^ k : Real) : Complex) ^ z = b ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ (norm pi.val), Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _), ih]
      exact (pow_succ b k).symm
  let w (gaps : Fin n -> Nat) := b ^ Finset.univ.sum (fun j => (j.val + 1) * gaps j)
  have hCoeffs (gaps : Fin n -> Nat) :
      integral (mu.restrict (D gaps)) F =
        w gaps * integral (mu.restrict (D gaps)) f := by
    have hEq : Filter.EventuallyEq (ae (mu.restrict (D gaps))) F
        (fun g => w gaps * f g) := by
      refine (ae_restrict_mem (hMeas gaps)).mono ?_
      intro g hg
      change (norm g.val.det : Complex) ^ z * f g = w gaps * f g
      rw [norm_det_of_mem_heckeLocal_valuationUniformizerGapDoubleCoset p n pi gaps g hg, hPow]
    rw [integral_congr_ae hEq, integral_const_mul]
  have hSum := hasSum_heckeLocal_integral_valuationUniformizerGapDoubleCosets p n pi hPi mu F hInt
  change HasSum (fun gaps => integral (mu.restrict (D gaps)) F) (integral (mu.restrict A) F) at hSum
  simpa only [hCoeffs, w, b] using hSum

end Robin1984.GRH
