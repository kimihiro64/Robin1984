import Mathlib.Algebra.Group.Pi.Units
import Mathlib.MeasureTheory.Integral.Pi
import Robin1984.GRH.GodementJacquetUnramifiedSpherical

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The diagonal integration in the unramified Godement-Jacquet local calculation, Goldfeld and Jacquet, Automorphic Representations and L-functions for GL(n), Section 2.4.
- Formalization note: Combines the unipotent fibre integral with multiplicative unit shells and finite product integration in diagonal coordinates.
- PROVENANCE-END
-/

/-!
# Diagonal factors of the unramified spherical integral

After integrating the upper unitriangular coordinates, the integral
diagonal cone decomposes into products of normalized multiplicative
shells. Each coordinate contributes one geometric Euler factor.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

open IsDedekindDomain NumberField

section

variable {K : Type*} [Field K] [NumberField K]

/-- The normalized finite-place norm is at most one exactly on the
valuation ring. -/
theorem heckeLocal_mem_integers_iff_norm_le_one
    (p : HeightOneSpectrum (RingOfIntegers K)) (x : p.adicCompletion K) :
    Membership.mem (p.adicCompletionIntegers K) x <-> norm x <= 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FinitePlace.norm_def]
  exact (WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal p)).symm

end

section

variable {L : Type*} [NormedField L]

/-- The complex unramified norm weight times a diagonal character. -/
def unramifiedLocalWeightedCharacter
    (chi : MonoidHom (Units L) Complex) (s : Complex) : MonoidHom (Units L) Complex where
  toFun x := (norm x.val : Complex) ^ s * chi x
  map_one' := by simp
  map_mul' x y := by
    change (norm (x.val * y.val) : Complex) ^ s * chi (x * y) =
      ((norm x.val : Complex) ^ s * chi x) * ((norm y.val : Complex) ^ s * chi y)
    rw [norm_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg x.val) (norm_nonneg y.val),
      map_mul]
    ring

/-- On any unit shell of norm one and trivial character, the weighted
character equals one. -/
theorem unramifiedLocalWeightedCharacter_eq_one
    (chi : MonoidHom (Units L) Complex) (s : Complex) (x : Units L)
    (hx : norm x.val = 1) (hchi : chi x = 1) :
    unramifiedLocalWeightedCharacter chi s x = 1 := by
  change (norm x.val : Complex) ^ s * chi x = 1
  simp [hx, hchi]

end

open MeasureTheory MeasureTheory.Measure Set

section ScalarShell

variable {K : Type*} [Field K] [NumberField K]
variable (p : HeightOneSpectrum (RingOfIntegers K))

local notation "L" => p.adicCompletion K
local notation "G1" => Units L

/-- The integral multiplicative cone is the set of nonzero integral local
elements, expressed as elements of the multiplicative group. -/
theorem heckeLocalIntegralUnits_iff (x : G1) :
    Membership.mem (heckeLocalIntegralUnits p) x <->
      Membership.mem (p.adicCompletionIntegers K) x.val := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, <- coe_heckeLocalValueIndex]
  change (heckeLocalValueIndex p x : Multiplicative Int) <= 1 <->
    (heckeLocalValueIndex p x : WithZero (Multiplicative Int)) <=
      ((1 : Multiplicative Int) : WithZero (Multiplicative Int))
  exact WithZero.coe_le_coe.symm

variable [MeasurableSpace (Units (p.adicCompletion K))]
variable [BorelSpace (Units (p.adicCompletion K))]

/-- On the integral multiplicative cone, an unramified weighted character
is absolutely integrable as soon as its uniformizer value has norm below one. -/
theorem integrableAndIntegral_unramifiedLocalWeightedCharacter
    (a : G1) (ha : Valued.v a.val = finiteUniformizerValue)
    (chi : MonoidHom G1 Complex)
    (hChi : forall x : G1, Membership.mem (heckeLocalUnitShell p) x -> chi x = 1)
    (s : Complex) (hNorm : norm (unramifiedLocalWeightedCharacter chi s a) < 1) :
    let f := (heckeLocalIntegralUnits p).indicator (unramifiedLocalWeightedCharacter chi s)
    And (Integrable f (heckeLocalHaar p))
      (integral (heckeLocalHaar p) f = Inv.inv (1 - unramifiedLocalWeightedCharacter chi s a)) := by
  let _ : MeasurableMul G1 :=
    { measurable_const_mul := fun x => (continuous_const_mul x).measurable
      measurable_mul_const := fun x => (continuous_mul_const x).measurable }
  have hUnit (x : G1) (hx : Membership.mem (heckeLocalUnitShell p) x) :
      unramifiedLocalWeightedCharacter chi s x = 1 := by
    have hv : Valued.v x.val = 1 := hx
    apply unramifiedLocalWeightedCharacter_eq_one chi s x _ (hChi x hx)
    rw [FinitePlace.norm_def, hv]
    simp
  dsimp only
  rw [<- heckeLocalUniformizerShells_eq_integralUnits p a ha]
  exact integrableAndIntegral_unramified_uniformizerShells (heckeLocalHaar p)
    (heckeLocalUnitShell p) (isOpen_heckeLocalUnitShell p).measurableSet
    (heckeLocalHaar_unitShell p) a (unramifiedLocalWeightedCharacter chi s)
    hUnit (heckeLocalUniformizerShells_pairwiseDisjoint p a ha) hNorm

/-- An arbitrary unramified local multiplicative weight integrates to
its Euler factor on the integral cone with normalized Haar measure. -/
theorem integral_unramifiedLocalWeightedCharacter
    (a : G1) (ha : Valued.v a.val = finiteUniformizerValue)
    (chi : MonoidHom G1 Complex)
    (hChi : forall x : G1, Membership.mem (heckeLocalUnitShell p) x -> chi x = 1)
    (s : Complex) (hNorm : norm (unramifiedLocalWeightedCharacter chi s a) < 1) :
    integral (heckeLocalHaar p) ((heckeLocalIntegralUnits p).indicator
      (unramifiedLocalWeightedCharacter chi s)) =
      Inv.inv (1 - unramifiedLocalWeightedCharacter chi s a) :=
  (integrableAndIntegral_unramifiedLocalWeightedCharacter p a ha chi hChi s hNorm).2

end ScalarShell

section DiagonalCharacters

variable {L : Type*} [Monoid L]

/-- The normalized induction uses a product of one character per diagonal
coordinate. -/
def productDiagonalCharacter (n : Nat) (chi : Fin n -> MonoidHom (Units L) Complex) :
    MonoidHom (Units (Fin n -> L)) Complex where
  toFun a := Finset.univ.prod (fun i : Fin n => chi i (MulEquiv.piUnits a i))
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, Pi.mul_apply, Finset.prod_mul_distrib]

end DiagonalCharacters

section ActualDiagonal

variable {K : Type*} [Field K] [NumberField K]
variable (p : HeightOneSpectrum (RingOfIntegers K))
variable [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
variable [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]

local notation "L" => p.adicCompletion K
local notation "GU" => Units L

variable [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
variable [MeasurableSpace (Units (p.adicCompletion K))]
variable [BorelSpace (Units (p.adicCompletion K))]

local notation "v" => (Valued.v : Valuation L (WithZero (Multiplicative Int)))

/-- Integration of the finite-place spherical kernel over unipotent
and diagonal coordinates gives the product of the scalar Euler factors. -/
theorem integral_heckeUnramifiedSpherical_diagonal
    [SigmaFinite (heckeLocalHaar p)]
    (n : Nat) (u0 : GU) (hu0 : Valued.v u0.val = finiteUniformizerValue)
    (chi : Fin n -> MonoidHom GU Complex)
    (hUnit : forall i x, Membership.mem (heckeLocalUnitShell p) x -> chi i x = 1)
    (hInducing : forall b : valuationUpperTriangularSubgroup L n,
      Membership.mem (valuationIntegralMatrixSubgroup v n) b.val ->
        valuationNormalizedInducingCharacter L n (productDiagonalCharacter n chi) b = 1)
    (s : Complex)
    (hNorm : forall i, norm (unramifiedLocalWeightedCharacter (chi i) s u0) < 1) :
    integral (Measure.pi (fun _ : Fin n => heckeLocalHaar p))
      (fun a : Fin n -> GU =>
        integral (valuationUnitriangularProductMeasure L (heckeLocalAdditiveMeasure p) n)
          (fun u : valuationUpperUnitriangularSubgroup L n =>
            valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi) s
              (valuationDiagonalSection L n (MulEquiv.piUnits.symm a) * u.val).val)) =
      Finset.univ.prod
        (fun i : Fin n => Inv.inv (1 - unramifiedLocalWeightedCharacter (chi i) s u0)) := by
  classical
  let D (a : Fin n -> GU) : Units (Fin n -> L) := MulEquiv.piUnits.symm a
  let w (i : Fin n) : GU -> Complex :=
    (heckeLocalIntegralUnits p).indicator (unramifiedLocalWeightedCharacter (chi i) s)
  let muU := valuationUnitriangularProductMeasure L (heckeLocalAdditiveMeasure p) n
  have hPoint (a : Fin n -> GU) :
      integral muU (fun u : valuationUpperUnitriangularSubgroup L n =>
        valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi) s
          (valuationDiagonalSection L n (D a) * u.val).val) =
      Finset.univ.prod (fun i : Fin n => w i (a i)) := by
    by_cases hAll : forall i : Fin n, Membership.mem (heckeLocalIntegralUnits p) (a i)
    next =>
      have hDiag (i : Fin n) : Membership.mem (p.adicCompletionIntegers K) ((D a).val i) :=
        (heckeLocalIntegralUnits_iff p (a i)).mp (hAll i)
      change integral
          (valuationUnitriangularProductMeasure L (heckeLocalAdditiveMeasure p) n)
          (fun u : valuationUpperUnitriangularSubgroup L n =>
            valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi)
              s (valuationDiagonalSection L n (D a) * u.val).val) = _
      rw [integral_heckeUnramifiedSpherical_fibre p n (D a) hDiag
        (productDiagonalCharacter n chi) hInducing s]
      have hChi : productDiagonalCharacter n chi (D a) =
          Finset.univ.prod (fun i : Fin n => chi i (a i)) := by
        change Finset.univ.prod (fun i : Fin n => chi i (MulEquiv.piUnits (D a) i)) = _
        rw [show MulEquiv.piUnits (D a) = a from MulEquiv.apply_symm_apply _ _]
      rw [hChi, <- Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [show w i (a i) = unramifiedLocalWeightedCharacter (chi i) s (a i)
        from Set.indicator_of_mem (hAll i) _]
      rfl
    next =>
      have hDiag : Not (forall i : Fin n, Membership.mem (v).integer ((D a).val i)) := by
        intro h
        apply hAll
        intro i
        exact (heckeLocalIntegralUnits_iff p (a i)).mpr (h i)
      have hZero (u : valuationUpperUnitriangularSubgroup L n) :
          valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi) s
            (valuationDiagonalSection L n (D a) * u.val).val = 0 :=
        valuationUnramifiedSphericalIntegrand_of_nonintegral L v n (D a) u hDiag _ s
      choose i hi using not_forall.mp hAll
      simp only [hZero, integral_zero]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact Set.indicator_of_notMem hi _
  change integral (Measure.pi (fun _ : Fin n => heckeLocalHaar p))
    (fun a : Fin n -> GU => integral muU (fun u : valuationUpperUnitriangularSubgroup L n =>
      valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi) s
        (valuationDiagonalSection L n (D a) * u.val).val)) = _
  simp only [hPoint]
  rw [integral_fintype_prod_eq_prod w]
  exact Finset.prod_congr rfl (fun i _ =>
    integral_unramifiedLocalWeightedCharacter p u0 hu0 (chi i) (hUnit i) s (hNorm i))

end ActualDiagonal

end Robin1984.GRH
