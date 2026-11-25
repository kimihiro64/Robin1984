import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Separation.Profinite
import Robin1984.GRH.GodementJacquetFiniteMatrixVolume
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

/-- The unramified spherical kernel is absolutely integrable in the
multiplicative diagonal and additive unipotent coordinates. Its product
integral and its iterated integral give the same Euler factor. -/
theorem integrableAndIntegral_heckeUnramifiedSpherical_product
    [SigmaFinite (heckeLocalHaar p)]
    (n : Nat) (u0 : GU) (hu0 : Valued.v u0.val = finiteUniformizerValue)
    (chi : Fin n -> MonoidHom GU Complex)
    (hUnit : forall i x, Membership.mem (heckeLocalUnitShell p) x -> chi i x = 1)
    (hInducing : forall b : valuationUpperTriangularSubgroup L n,
      Membership.mem (valuationIntegralMatrixSubgroup v n) b.val ->
        valuationNormalizedInducingCharacter L n (productDiagonalCharacter n chi) b = 1)
    (s : Complex)
    (hNorm : forall i, norm (unramifiedLocalWeightedCharacter (chi i) s u0) < 1) :
    letI : MeasurableSpace (valuationUpperUnitriangularSubgroup L n) := borel _
    let muA := Measure.pi (fun _ : Fin n => heckeLocalHaar p)
    let muU := valuationUnitriangularProductMeasure L (heckeLocalAdditiveMeasure p) n
    let f := fun x : Prod (Fin n -> GU) (valuationUpperUnitriangularSubgroup L n) =>
      valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi) s
        (valuationDiagonalSection L n (MulEquiv.piUnits.symm x.1) * x.2.val).val
    let P := Finset.univ.prod
      (fun i : Fin n => Inv.inv (1 - unramifiedLocalWeightedCharacter (chi i) s u0))
    And (Integrable f (muA.prod muU))
      (And (integral (muA.prod muU) f = P)
        (integral muA (fun a => integral muU (fun u => f (a, u))) = P)) := by
  classical
  let A := Fin n -> GU
  let U := valuationUpperUnitriangularSubgroup L n
  let D (a : A) : Units (Fin n -> L) := MulEquiv.piUnits.symm a
  let w (i : Fin n) : GU -> Complex :=
    (heckeLocalIntegralUnits p).indicator (unramifiedLocalWeightedCharacter (chi i) s)
  let _ : MeasurableSpace U := borel U
  let _ : BorelSpace U := BorelSpace.mk rfl
  let _ : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let e : Homeomorph L (MulOpposite L) := MulOpposite.opHomeomorph
  let _ : SecondCountableTopology (MulOpposite L) := e.symm.isEmbedding.secondCountableTopology
  let hUnits : Topology.IsEmbedding (Units.embedProduct L) := Units.isEmbedding_embedProduct
  let _ : SecondCountableTopology GU := hUnits.secondCountableTopology
  let _ : SecondCountableTopology A := inferInstanceAs (SecondCountableTopology (Fin n -> GU))
  let _ : SigmaFinite (heckeLocalAdditiveMeasure p) := sigmaFinite_heckeLocalAdditiveMeasure p
  let muA := Measure.pi (fun _ : Fin n => heckeLocalHaar p)
  let muU := valuationUnitriangularProductMeasure L (heckeLocalAdditiveMeasure p) n
  let _ : SigmaFinite muU := sigmaFinite_valuationUnitriangularProductMeasure L
    (heckeLocalAdditiveMeasure p) n
  let f (x : Prod A U) : Complex :=
    valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi) s
      (valuationDiagonalSection L n (D x.1) * x.2.val).val
  have hFibre (a : A) :
      And (Integrable (fun u => f (a, u)) muU)
        (And (integral muU (fun u => norm (f (a, u))) = norm (integral muU (fun u => f (a, u))))
          (integral muU (fun u => f (a, u)) = Finset.univ.prod (fun i : Fin n => w i (a i)))) := by
    by_cases hAll : forall i : Fin n, Membership.mem (heckeLocalIntegralUnits p) (a i)
    next =>
      have hDiag (i : Fin n) : Membership.mem (p.adicCompletionIntegers K) ((D a).val i) :=
        (heckeLocalIntegralUnits_iff p (a i)).mp (hAll i)
      have h := integrableAndIntegral_heckeUnramifiedSpherical_fibre p n (D a) hDiag
        (productDiagonalCharacter n chi) hInducing s
      refine And.intro h.1 (And.intro h.2.1 ?_)
      change integral
          (valuationUnitriangularProductMeasure L (heckeLocalAdditiveMeasure p) n)
          (fun u : U => valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi)
            s (valuationDiagonalSection L n (D a) * u.val).val) = _
      rw [h.2.2]
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
      have hZero (u : U) : f (a, u) = 0 :=
        valuationUnramifiedSphericalIntegrand_of_nonintegral L v n (D a) u hDiag _ s
      choose i hi using not_forall.mp hAll
      have hProd : Finset.univ.prod (fun j : Fin n => w j (a j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
      simp [hZero, hProd]
  have hPoint (a : A) : integral muU (fun u => f (a, u)) =
      Finset.univ.prod (fun i : Fin n => w i (a i)) := (hFibre a).2.2
  have hNormPoint (a : A) : integral muU (fun u => norm (f (a, u))) =
      Finset.univ.prod (fun i : Fin n => norm (w i (a i))) := by
    rw [(hFibre a).2.1, hPoint, norm_prod]
  have hOuter : Integrable (fun a : A => integral muU (fun u => norm (f (a, u)))) muA := by
    simp only [hNormPoint]
    exact Integrable.fintype_prod (fun i =>
      (integrableAndIntegral_unramifiedLocalWeightedCharacter p u0 hu0 (chi i) (hUnit i) s (hNorm i)).1.norm)
  have hD : Continuous D :=
    (ContinuousMulEquiv.piUnits (M := fun _ : Fin n => L)).symm.continuous
  have hDiagonal : Continuous (fun x : Prod A U => valuationDiagonalSection L n (D x.1)) :=
    (continuous_valuationDiagonalSection L n).comp (hD.comp continuous_fst)
  have hUnipotent : Continuous (fun x : Prod A U => x.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hMatrix : Continuous (fun x : Prod A U =>
      (valuationDiagonalSection L n (D x.1) * x.2.val).val) :=
    continuous_subtype_val.comp (hDiagonal.mul hUnipotent)
  have hMeas : AEStronglyMeasurable f (muA.prod muU) :=
    ((continuous_valuationUnramifiedSphericalIntegrand L v n
      (Valued.isOpen_valuationSubring L) (productDiagonalCharacter n chi) hInducing s).comp
        hMatrix).measurable.aestronglyMeasurable
  have hInt : Integrable f (muA.prod muU) :=
    (integrable_prod_iff hMeas).mpr
      (And.intro (Filter.Eventually.of_forall (fun a => (hFibre a).1)) hOuter)
  have hIterated : integral muA (fun a => integral muU (fun u => f (a, u))) =
      Finset.univ.prod
        (fun i : Fin n => Inv.inv (1 - unramifiedLocalWeightedCharacter (chi i) s u0)) := by
    simp only [hPoint]
    rw [integral_fintype_prod_eq_prod w]
    exact Finset.prod_congr rfl (fun i _ =>
      integral_unramifiedLocalWeightedCharacter p u0 hu0 (chi i) (hUnit i) s (hNorm i))
  exact And.intro hInt (And.intro ((integral_prod f hInt).trans hIterated) hIterated)

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
        (fun i : Fin n => Inv.inv (1 - unramifiedLocalWeightedCharacter (chi i) s u0)) :=
  (integrableAndIntegral_heckeUnramifiedSpherical_product p n u0 hu0 chi hUnit hInducing s hNorm).2.2

end ActualDiagonal

section ActualHaar

variable {K : Type*} [Field K] [NumberField K]
variable (p : HeightOneSpectrum (RingOfIntegers K))

local notation "L" => p.adicCompletion K
local notation "GU" => Units L
local notation "v" => (Valued.v : Valuation L (WithZero (Multiplicative Int)))

/-- In diagonal coordinates, the integral matrix subgroup consists of
a local unit in every coordinate. -/
private theorem mem_heckeDiagonalIntegral_iff_localUnitShell
    (n : Nat) (a : Units (Fin n -> L)) :
    Membership.mem (valuationDiagonalIntegralSubgroup L n v) a <->
      forall i : Fin n, Membership.mem (heckeLocalUnitShell p) (MulEquiv.piUnits a i) := by
  have hProd (i : Fin n) : (v) (a.val i) * (v) (a.inv i) = 1 := by
    rw [<- map_mul]
    change (v) ((a.val * a.inv) i) = 1
    rw [a.val_inv]
    exact map_one v
  have hEntries (b : Fin n -> L)
      (hb : forall i : Fin n, Membership.mem (v).integer (b i)) :
      forall i j : Fin n, Membership.mem (v).integer (Matrix.diagonal b i j) := by
    intro i j
    by_cases hij : i = j
    next =>
      subst j
      rw [Matrix.diagonal_apply_eq]
      exact hb i
    next =>
      rw [Matrix.diagonal_apply_ne _ hij]
      exact (v).integer.zero_mem
  change Membership.mem (valuationIntegralMatrixSubgroup v n)
    (valuationDiagonalSection L n a).val <-> _
  rw [mem_valuationIntegralMatrixSubgroup_iff]
  constructor
  next =>
    intro h i
    have hv := h.1 i i
    have hu := h.2 i i
    change Membership.mem (v).integer (Matrix.diagonal a.val i i) at hv
    change Membership.mem (v).integer (Matrix.diagonal a.inv i i) at hu
    rw [Matrix.diagonal_apply_eq] at hv hu
    change (v) (a.val i) = 1
    have huLe : (v) (a.inv i) <= 1 := hu
    exact le_antisymm hv ((hProd i).symm.le.trans (mul_le_of_le_one_right' huLe))
  next =>
    intro h
    have hUnit (i : Fin n) : (v) (a.val i) = 1 := h i
    have hVal (i : Fin n) : Membership.mem (v).integer (a.val i) :=
      (hUnit i).le
    have hInv (i : Fin n) : Membership.mem (v).integer (a.inv i) := by
      have hP := hProd i
      rw [hUnit i, one_mul] at hP
      exact hP.le
    exact And.intro (hEntries a.val hVal) (hEntries a.inv hInv)

/-- Integral matrix units have determinant of local norm one. -/
private theorem norm_det_heckeIntegralMatrixUnit (n : Nat)
    (k : Units (Matrix (Fin n) (Fin n) L))
    (hk : Membership.mem (valuationIntegralMatrixSubgroup v n) k) :
    norm k.val.det = 1 := by
  let R := (v).integer
  have hDetMem (A : Matrix (Fin n) (Fin n) L)
      (hA : forall i j, Membership.mem R (A i j)) : Membership.mem R A.det := by
    let A0 : Matrix (Fin n) (Fin n) R := Matrix.of (fun i j => Subtype.mk (A i j) (hA i j))
    have hMap : R.subtype.mapMatrix A0 = A := by ext i j; rfl
    rw [<- hMap, <- RingHom.map_det]
    exact A0.det.property
  have hkEntries := (mem_valuationIntegralMatrixSubgroup_iff v n k).mp hk
  have hNorm (x : L) : Membership.mem R x <-> norm x <= 1 :=
    heckeLocal_mem_integers_iff_norm_le_one p x
  have hLeft := (hNorm k.val.det).mp (hDetMem k.val hkEntries.1)
  have hRight := (hNorm k.inv.det).mp (hDetMem k.inv hkEntries.2)
  have hDetProd : norm k.val.det * norm k.inv.det = 1 := by
    rw [<- norm_mul, <- Matrix.det_mul, k.val_inv, Matrix.det_one, norm_one]
  exact le_antisymm hLeft (hDetProd.symm.le.trans (mul_le_of_le_one_right (norm_nonneg _) hRight))

/-- The shifted determinant weight with the integral matrix test. -/
def heckeUnramifiedLocalMatrixWeight (n : Nat) (s : Complex) :
    Units (Matrix (Fin n) (Fin n) L) -> Complex :=
  Set.indicator
    {g : Units (Matrix (Fin n) (Fin n) L) |
      forall i j : Fin n, Membership.mem (v).integer (g.val i j)}
    (fun g => (norm g.val.det : Complex) ^ (s + (((n : Real) - 1) / 2 : Real)))

private theorem heckeUnramifiedLocalMatrixWeight_left (n : Nat) (s : Complex)
    (g k : Units (Matrix (Fin n) (Fin n) L))
    (hk : Membership.mem (valuationIntegralMatrixSubgroup v n) k) :
    heckeUnramifiedLocalMatrixWeight p n s (k * g) =
      heckeUnramifiedLocalMatrixWeight p n s g := by
  let G := Units (Matrix (Fin n) (Fin n) L)
  let R := (v).integer
  let S : Set G := {x : G | forall i j : Fin n, Membership.mem R (x.val i j)}
  have hKeep (x y : G) (hx : Membership.mem (valuationIntegralMatrixSubgroup v n) x)
      (hy : Membership.mem S y) : Membership.mem S (x * y) := by
    change Membership.mem R.matrix (x.val * y.val)
    exact R.matrix.mul_mem ((mem_valuationIntegralMatrixSubgroup_iff v n x).mp hx).1 hy
  have hMem : Membership.mem S (k * g) <-> Membership.mem S g := by
    refine Iff.intro ?_ (hKeep k g hk)
    intro h
    have h' := hKeep (Inv.inv k) (k * g) ((valuationIntegralMatrixSubgroup v n).inv_mem hk) h
    rwa [inv_mul_cancel_left] at h'
  unfold heckeUnramifiedLocalMatrixWeight
  by_cases hg : Membership.mem S g
  next =>
    rw [Set.indicator_of_mem (hMem.mpr hg), Set.indicator_of_mem hg]
    rw [show (k * g).val.det = k.val.det * g.val.det from Matrix.det_mul _ _,
      norm_mul, norm_det_heckeIntegralMatrixUnit p n k hk, one_mul]
  next =>
    rw [Set.indicator_of_notMem (fun h => hg (hMem.mp h)), Set.indicator_of_notMem hg]

private theorem heckeUnramifiedSphericalIntegrand_eq_weight_mul (n : Nat)
    (chi : MonoidHom (Units (Fin n -> L)) Complex) (s : Complex)
    (g : Units (Matrix (Fin n) (Fin n) L)) :
    valuationUnramifiedSphericalIntegrand L v n chi s g =
      heckeUnramifiedLocalMatrixWeight p n s g *
        valuationSphericalSection v n (valuationNormalizedInducingCharacter L n chi) g := by
  unfold valuationUnramifiedSphericalIntegrand heckeUnramifiedLocalMatrixWeight
  exact Set.indicator_mul_left _ _ _

/-- The spherical kernel is invariant under right multiplication by
an integral matrix unit. -/
private theorem heckeUnramifiedSphericalIntegrand_rightInvariant
    (n : Nat) (chi : MonoidHom (Units (Fin n -> L)) Complex)
    (hChi : forall b : valuationUpperTriangularSubgroup L n,
      Membership.mem (valuationIntegralMatrixSubgroup v n) b.val ->
        valuationNormalizedInducingCharacter L n chi b = 1)
    (s : Complex) (g k : Units (Matrix (Fin n) (Fin n) L))
    (hk : Membership.mem (valuationIntegralMatrixSubgroup v n) k) :
    valuationUnramifiedSphericalIntegrand L v n chi s (g * k) =
      valuationUnramifiedSphericalIntegrand L v n chi s g := by
  let G := Units (Matrix (Fin n) (Fin n) L)
  let R := (v).integer
  let S : Set G := {x : G | forall i j : Fin n, Membership.mem R (x.val i j)}
  have hKeep (x y : G) (hy : Membership.mem (valuationIntegralMatrixSubgroup v n) y)
      (hx : Membership.mem S x) : Membership.mem S (x * y) := by
    change Membership.mem R.matrix (x.val * y.val)
    exact R.matrix.mul_mem hx ((mem_valuationIntegralMatrixSubgroup_iff v n y).mp hy).1
  have hMem : Membership.mem S (g * k) <-> Membership.mem S g := by
    refine Iff.intro ?_ (hKeep g k hk)
    intro h
    have h' := hKeep (g * k) (Inv.inv k) ((valuationIntegralMatrixSubgroup v n).inv_mem hk) h
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h'
  have hDet := norm_det_heckeIntegralMatrixUnit p n k hk
  let w := valuationNormalizedInducingCharacter L n chi
  change S.indicator (fun x : G => (norm x.val.det : Complex) ^
      (s + (((n : Real) - 1) / 2 : Real)) * valuationSphericalSection v n w x) (g * k) =
    S.indicator (fun x : G => (norm x.val.det : Complex) ^
      (s + (((n : Real) - 1) / 2 : Real)) * valuationSphericalSection v n w x) g
  by_cases h : Membership.mem S g
  next =>
    rw [Set.indicator_of_mem (hMem.mpr h), Set.indicator_of_mem h]
    rw [show (g * k).val.det = g.val.det * k.val.det from Matrix.det_mul _ _,
      norm_mul, hDet, mul_one, valuationSphericalSection_mul_integral v n w hChi g k hk]
  next =>
    rw [Set.indicator_of_notMem (fun hh => h (hMem.mp hh)), Set.indicator_of_notMem h]

private theorem heckeNormalizedInducingCharacter_eq_one_of_integral
    (n : Nat) (chi : Fin n -> MonoidHom GU Complex)
    (hUnit : forall i x, Membership.mem (heckeLocalUnitShell p) x -> chi i x = 1)
    (b : valuationUpperTriangularSubgroup L n)
    (hb : Membership.mem (valuationIntegralMatrixSubgroup v n) b.val) :
    valuationNormalizedInducingCharacter L n (productDiagonalCharacter n chi) b = 1 := by
  have hChiDiag (a : Units (Fin n -> L))
      (ha : Membership.mem (valuationDiagonalIntegralSubgroup L n v) a) :
      productDiagonalCharacter n chi a = 1 := by
    have hLocal := (mem_heckeDiagonalIntegral_iff_localUnitShell p n a).mp ha
    change Finset.univ.prod (fun i : Fin n => chi i (MulEquiv.piUnits a i)) = 1
    have h1 (i : Fin n) : chi i (MulEquiv.piUnits a i) = 1 := hUnit i _ (hLocal i)
    simp only [h1, Finset.prod_const_one]
  exact valuationNormalizedInducingCharacter_eq_one L v (heckeLocal_mem_integers_iff_norm_le_one p)
    n _ hChiDiag b hb

private theorem measurableMul_of_continuousBorel (H : Type*) [Mul H] [TopologicalSpace H]
    [ContinuousMul H] [MeasurableSpace H] [BorelSpace H] : MeasurableMul H :=
  { measurable_const_mul := fun x => (continuous_const_mul x).measurable
    measurable_mul_const := fun x => (continuous_mul_const x).measurable }

variable [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
variable [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
variable [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
variable [MeasurableSpace (Units (p.adicCompletion K))]
variable [BorelSpace (Units (p.adicCompletion K))]

/-- The full local Godement-Jacquet spherical integral converges absolutely
and gives the Euler factor for the normalized Haar measure on the matrix
group. Each diagonal character is trivial on the local unit shell. -/
theorem integrableAndIntegral_heckeUnramifiedSpherical_haar
    [SigmaFinite (heckeLocalHaar p)]
    (n : Nat) (u0 : GU) (hu0 : Valued.v u0.val = finiteUniformizerValue)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    (muG : Measure (Units (Matrix (Fin n) (Fin n) L))) [muG.IsMulLeftInvariant]
    (hMassG : muG (valuationIntegralMatrixSubgroup v n : Set (Units (Matrix (Fin n) (Fin n) L))) = 1)
    (chi : Fin n -> MonoidHom GU Complex)
    (hUnit : forall i x, Membership.mem (heckeLocalUnitShell p) x -> chi i x = 1)
    (s : Complex)
    (hNorm : forall i, norm (unramifiedLocalWeightedCharacter (chi i) s u0) < 1) :
    let f := valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi) s
    And (Integrable f muG) (integral muG f = Finset.univ.prod
      (fun i : Fin n => Inv.inv (1 - unramifiedLocalWeightedCharacter (chi i) s u0))) := by
  classical
  let G := Units (Matrix (Fin n) (Fin n) L)
  let A := Units (Fin n -> L)
  let T := Fin n -> GU
  let B := valuationUpperTriangularSubgroup L n
  let U := valuationUpperUnitriangularSubgroup L n
  let _ : MeasurableSpace A := borel A
  let _ : BorelSpace A := BorelSpace.mk rfl
  let _ : MeasurableSpace B := borel B
  let _ : BorelSpace B := BorelSpace.mk rfl
  let _ : MeasurableSpace U := borel U
  let _ : BorelSpace U := BorelSpace.mk rfl
  let _ : MeasurableMul A := measurableMul_of_continuousBorel A
  let _ : MeasurableMul B := measurableMul_of_continuousBorel B
  let _ : MeasurableMul U := measurableMul_of_continuousBorel U
  let _ : MeasurableMul G := measurableMul_of_continuousBorel G
  let _ : MeasurableMul GU := measurableMul_of_continuousBorel GU
  let _ : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let op : Homeomorph L (MulOpposite L) := MulOpposite.opHomeomorph
  let _ : SecondCountableTopology (MulOpposite L) := op.symm.isEmbedding.secondCountableTopology
  have hUnits : Topology.IsEmbedding (Units.embedProduct L) := Units.isEmbedding_embedProduct
  let _ : SecondCountableTopology GU := hUnits.secondCountableTopology
  let _ : SecondCountableTopology T := inferInstanceAs (SecondCountableTopology (Fin n -> GU))
  let D : ContinuousMulEquiv A T := ContinuousMulEquiv.piUnits
  let _ : SecondCountableTopology A := D.toHomeomorph.isEmbedding.secondCountableTopology
  let nu := heckeLocalHaar p
  let muT := Measure.pi (fun _ : Fin n => nu)
  let muA := Measure.map D.symm muT
  let muU := valuationUnitriangularProductMeasure L (heckeLocalAdditiveMeasure p) n
  let _ : SigmaFinite (heckeLocalAdditiveMeasure p) := sigmaFinite_heckeLocalAdditiveMeasure p
  let _ : (heckeLocalAdditiveMeasure p).IsAddLeftInvariant := isAddLeftInvariant_heckeLocalAdditiveMeasure p
  let _ : SigmaFinite muU :=
    sigmaFinite_valuationUnitriangularProductMeasure L (heckeLocalAdditiveMeasure p) n
  let _ : muU.IsMulLeftInvariant :=
    isMulLeftInvariant_valuationUnitriangularProductMeasure L (heckeLocalAdditiveMeasure p) n
  have hMuT : muT.IsMulLeftInvariant := by
    constructor
    intro t
    exact (measurePreserving_pi (fun _ : Fin n => nu) (fun _ : Fin n => nu)
      (fun i => measurePreserving_mul_left nu (t i))).map_eq
  let _ := hMuT
  have hD : Measurable (D.symm : T -> A) := D.symm.continuous.measurable
  let _ : muA.IsMulLeftInvariant :=
    isMulLeftInvariant_map D.symm.toMulEquiv.toMulHom hD D.symm.surjective
  let _ : SigmaFinite muA := D.symm.toHomeomorph.measurableEmbedding.sigmaFinite_map
  have hOpen := Valued.isOpen_valuationSubring L
  have hDiagMeas : MeasurableSet (valuationDiagonalIntegralSubgroup L n v : Set A) :=
    ((isOpen_valuationIntegralMatrixSubgroup v n hOpen).preimage
      (continuous_subtype_val.comp (continuous_valuationDiagonalSection L n))).measurableSet
  have hRect : Set.preimage D.symm (valuationDiagonalIntegralSubgroup L n v : Set A) =
      Set.pi Set.univ (fun _ : Fin n => heckeLocalUnitShell p) := by
    ext t
    change Membership.mem (valuationDiagonalIntegralSubgroup L n v) (D.symm t) <-> _
    rw [mem_heckeDiagonalIntegral_iff_localUnitShell]
    have hDT : MulEquiv.piUnits (D.symm t) = t := D.apply_symm_apply t
    rw [hDT]
    exact Iff.intro (fun h i _ => h i) (fun h i => h i (Set.mem_univ i))
  have hMassA : muA (valuationDiagonalIntegralSubgroup L n v : Set A) = 1 := by
    change Measure.map D.symm muT _ = _
    rw [Measure.map_apply hD hDiagMeas, hRect]
    change Measure.pi (fun _ : Fin n => nu) _ = _
    rw [Measure.pi_pi]
    simp only [nu, heckeLocalHaar_unitShell, Finset.prod_const_one]
  have hMassU : muU (valuationUnitriangularIntegralSubgroup L n v : Set U) = 1 :=
    measure_valuationUnitriangularProduct_integral L v (heckeLocalAdditiveMeasure p)
      (heckeLocalAdditiveMeasure_integral p) n
  have hInducing (b : B) (hb : Membership.mem (valuationIntegralMatrixSubgroup v n) b.val) :
      valuationNormalizedInducingCharacter L n (productDiagonalCharacter n chi) b = 1 :=
    heckeNormalizedInducingCharacter_eq_one_of_integral p n chi hUnit b hb
  let f := valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi) s
  have hF : Continuous f :=
    continuous_valuationUnramifiedSphericalIntegrand L v n hOpen _ hInducing s
  let E := valuationTriangularHomeomorph L n
  let fA (z : Prod A U) := f (E.symm z).val
  have hFA : Measurable fA :=
    (hF.comp (continuous_subtype_val.comp E.symm.continuous)).measurable
  let phi : Prod T U -> Prod A U := Prod.map D.symm id
  have hPhi : Measurable phi := hD.prodMap measurable_id
  have hMap : Measure.map phi (muT.prod muU) = muA.prod muU := by
    change Measure.map (Prod.map D.symm id) (muT.prod muU) =
      (Measure.map D.symm muT).prod muU
    rw [<- Measure.map_prod_map muT muU hD measurable_id, Measure.map_id]
  have hProduct := integrableAndIntegral_heckeUnramifiedSpherical_product p n u0 hu0 chi
    hUnit hInducing s hNorm
  have hIntA : Integrable fA (muA.prod muU) := by
    rw [<- hMap]
    exact (integrable_map_measure hFA.aestronglyMeasurable hPhi.aemeasurable).mpr hProduct.1
  have hIA : integral (muA.prod muU) fA = Finset.univ.prod
      (fun i : Fin n => Inv.inv (1 - unramifiedLocalWeightedCharacter (chi i) s u0)) := by
    rw [<- hMap, integral_map hPhi.aemeasurable hFA.aestronglyMeasurable]
    exact hProduct.2.1
  have hCompare := integrable_iff_and_integral_valuationIwasawa_in_product_coordinates L n v hOpen
    muG muA muU hMassG hMassA hMassU f hF.measurable
    (heckeUnramifiedSphericalIntegrand_rightInvariant p n _ hInducing s)
  exact And.intro (hCompare.1.mpr hIntA) (hCompare.2.trans hIA)

/-- The spherical coefficient is the compact average of the normalized
section in the unramified induced model. -/
def heckeUnramifiedSphericalCoefficient (n : Nat)
    [MeasurableSpace (valuationIntegralMatrixSubgroup v n)]
    (nu : Measure (valuationIntegralMatrixSubgroup v n))
    (chi : MonoidHom (Units (Fin n -> L)) Complex) (g : Units (Matrix (Fin n) (Fin n) L)) :
    Complex :=
  integral nu (fun k : valuationIntegralMatrixSubgroup v n =>
    valuationSphericalSection v n (valuationNormalizedInducingCharacter L n chi) (k.val * g))

/-- The standard unramified finite-place zeta integrand. Its determinant
weight includes the characteristic function of the integral matrices. -/
def heckeUnramifiedLocalZetaIntegrand (n : Nat)
    [MeasurableSpace (valuationIntegralMatrixSubgroup v n)]
    (nu : Measure (valuationIntegralMatrixSubgroup v n))
    (chi : Fin n -> MonoidHom GU Complex) (s : Complex)
    (g : Units (Matrix (Fin n) (Fin n) L)) : Complex :=
  heckeUnramifiedLocalMatrixWeight p n s g *
    heckeUnramifiedSphericalCoefficient p n nu (productDiagonalCharacter n chi) g

omit [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
  [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
  [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
  [MeasurableSpace (Units (p.adicCompletion K))] [BorelSpace (Units (p.adicCompletion K))] in
/-- The unramified zeta integrand is one on the integral matrix subgroup. -/
theorem heckeUnramifiedLocalZetaIntegrand_eq_one_of_mem_integral
    (n : Nat)
    [MeasurableSpace (valuationIntegralMatrixSubgroup v n)]
    (nu : Measure (valuationIntegralMatrixSubgroup v n)) [IsProbabilityMeasure nu]
    (chi : Fin n -> MonoidHom GU Complex)
    (hUnit : forall i x, Membership.mem (heckeLocalUnitShell p) x -> chi i x = 1)
    (s : Complex) (g : Units (Matrix (Fin n) (Fin n) L))
    (hg : Membership.mem (valuationIntegralMatrixSubgroup v n) g) :
    heckeUnramifiedLocalZetaIntegrand p n nu chi s g = 1 := by
  let C := valuationIntegralMatrixSubgroup v n
  let B := valuationUpperTriangularSubgroup L n
  let w := valuationNormalizedInducingCharacter L n (productDiagonalCharacter n chi)
  have hW (b : B) (hb : Membership.mem C b.val) : w b = 1 :=
    heckeNormalizedInducingCharacter_eq_one_of_integral p n chi hUnit b hb
  have hDet : heckeUnramifiedLocalMatrixWeight p n s g = 1 := by
    unfold heckeUnramifiedLocalMatrixWeight
    have hEntries : Membership.mem {x : Units (Matrix (Fin n) (Fin n) L) |
        forall i j : Fin n, Membership.mem (v).integer (x.val i j)} g :=
      ((mem_valuationIntegralMatrixSubgroup_iff v n g).mp hg).1
    rw [Set.indicator_of_mem hEntries, norm_det_heckeIntegralMatrixUnit p n g hg]
    simp
  have hPoint (k : C) : valuationSphericalSection v n w (k.val * g) = 1 := by
    have hk : Membership.mem C (Inv.inv ((1 : B).val) * (k.val * g)) := by
      simpa only [Subgroup.coe_one, inv_one, one_mul] using C.mul_mem k.property hg
    rw [valuationSphericalSection_eq v n w hW hk, map_one]
  have hCoeff :
      heckeUnramifiedSphericalCoefficient p n nu (productDiagonalCharacter n chi) g = 1 := by
    unfold heckeUnramifiedSphericalCoefficient
    change integral nu (fun k : C => valuationSphericalSection v n w (k.val * g)) = 1
    rw [show (fun k : C => valuationSphericalSection v n w (k.val * g)) =
      (fun _ : C => (1 : Complex)) from funext hPoint, integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  simp only [heckeUnramifiedLocalZetaIntegrand, hDet, hCoeff, mul_one]

/-- Compact averaging preserves absolute convergence and the Euler factor
in the normalized full-group local Godement-Jacquet zeta integral. -/
theorem integrableAndIntegral_heckeUnramifiedSphericalCoefficient_haar
    [SigmaFinite (heckeLocalHaar p)]
    (n : Nat) (u0 : GU) (hu0 : Valued.v u0.val = finiteUniformizerValue)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    [MeasurableSpace (valuationIntegralMatrixSubgroup v n)]
    [BorelSpace (valuationIntegralMatrixSubgroup v n)]
    (muG : Measure (Units (Matrix (Fin n) (Fin n) L))) [muG.IsMulLeftInvariant] [SFinite muG]
    (hMass : muG (valuationIntegralMatrixSubgroup v n : Set (Units (Matrix (Fin n) (Fin n) L))) = 1)
    (nu : Measure (valuationIntegralMatrixSubgroup v n)) [IsProbabilityMeasure nu]
    (chi : Fin n -> MonoidHom GU Complex)
    (hUnit : forall i x, Membership.mem (heckeLocalUnitShell p) x -> chi i x = 1)
    (s : Complex)
    (hNorm : forall i, norm (unramifiedLocalWeightedCharacter (chi i) s u0) < 1) :
    let c := heckeUnramifiedSphericalCoefficient p n nu (productDiagonalCharacter n chi)
    let f := fun g => heckeUnramifiedLocalMatrixWeight p n s g * c g
    And (Integrable f muG) (integral muG f = Finset.univ.prod
      (fun i : Fin n => Inv.inv (1 - unramifiedLocalWeightedCharacter (chi i) s u0))) := by
  let M := Matrix (Fin n) (Fin n) L
  let G := Units M
  let C := valuationIntegralMatrixSubgroup v n
  let _ : MeasurableMul G := measurableMul_of_continuousBorel G
  let _ : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  let _ : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> L))
  let op : Homeomorph M (MulOpposite M) := MulOpposite.opHomeomorph
  let _ : SecondCountableTopology (MulOpposite M) := op.symm.isEmbedding.secondCountableTopology
  let hUnits : Topology.IsEmbedding (Units.embedProduct M) := Units.isEmbedding_embedProduct
  let _ : SecondCountableTopology G := hUnits.secondCountableTopology
  let g0 := valuationUnramifiedSphericalIntegrand L v n (productDiagonalCharacter n chi) s
  let T (x : Prod C G) : G := x.1.val * x.2
  have hT : Measurable T :=
    ((continuous_subtype_val.comp continuous_fst).mul continuous_snd).measurable
  have hSkew : MeasurePreserving (fun x : Prod C G => (x.1, T x))
      (nu.prod muG) (nu.prod muG) :=
    (MeasurePreserving.id nu).skew_product hT
      (Filter.Eventually.of_forall (fun k => map_mul_left_eq_self muG k.val))
  have hProj : MeasurePreserving (Prod.snd : Prod C G -> G) (nu.prod muG) muG :=
    measurePreserving_snd
  have hPres : MeasurePreserving T (nu.prod muG) muG := hProj.comp hSkew
  have hZ := integrableAndIntegral_heckeUnramifiedSpherical_haar p n u0 hu0
    muG hMass chi hUnit s hNorm
  let G0 : Prod C G -> Complex := Function.comp g0 T
  have hInt : Integrable G0 (nu.prod muG) := hPres.integrable_comp_of_integrable hZ.1
  have hAvg : (fun g : G => integral nu (fun k : C => G0 (k, g))) = fun g : G =>
      heckeUnramifiedLocalMatrixWeight p n s g *
        heckeUnramifiedSphericalCoefficient p n nu (productDiagonalCharacter n chi) g := by
    funext g
    have hVal (k : C) : G0 (k, g) = heckeUnramifiedLocalMatrixWeight p n s g *
        valuationSphericalSection v n
          (valuationNormalizedInducingCharacter L n (productDiagonalCharacter n chi)) (k.val * g) := by
      change g0 (k.val * g) = _
      dsimp only [g0]
      rw [heckeUnramifiedSphericalIntegrand_eq_weight_mul,
        heckeUnramifiedLocalMatrixWeight_left p n s g k.val k.property]
    simp only [hVal, heckeUnramifiedSphericalCoefficient]
    exact integral_const_mul _ _
  have hAvgInt := hInt.integral_prod_right
  have hI : integral muG (fun g : G => integral nu (fun k : C => G0 (k, g))) =
      integral muG g0 := by
    have hStrong : AEStronglyMeasurable g0 (Measure.map T (nu.prod muG)) := by
      rw [hPres.map_eq]
      exact hZ.1.aestronglyMeasurable
    have hMap := integral_map hPres.aemeasurable hStrong
    rw [hPres.map_eq] at hMap
    exact (integral_prod_symm G0 hInt).symm.trans hMap.symm
  rw [hAvg] at hAvgInt hI
  exact And.intro hAvgInt (hI.trans hZ.2)

private theorem weightedCharacter_uniformizer_primeNorm
    (chi : MonoidHom GU Complex) (s : Complex) (u0 : GU)
    (hu0 : Valued.v u0.val = finiteUniformizerValue) :
    unramifiedLocalWeightedCharacter chi s u0 =
      chi u0 * (dedekindPrimeNorm K p : Complex) ^ (-s) := by
  have hNorm := norm_eq_inv_of_valuation_finiteUniformizer p u0.val hu0
  have hArg : Not (((dedekindPrimeNorm K p : Real) : Complex).arg = Real.pi) := by
    rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
    exact (ne_of_gt Real.pi_pos).symm
  change (norm u0.val : Complex) ^ s * chi u0 = _
  rw [hNorm, Complex.ofReal_inv, Complex.inv_cpow _ _ hArg,
    <- Complex.cpow_neg, Complex.ofReal_natCast, mul_comm]

/-- The spherical coefficient integral gives the unramified Euler factor
with the normalized prime norm and the diagonal characters evaluated at a
uniformizer. The same hypotheses give absolute convergence. -/
theorem integrableAndIntegral_heckeUnramifiedSphericalCoefficient_primeNorm
    [SigmaFinite (heckeLocalHaar p)]
    (n : Nat) (u0 : GU) (hu0 : Valued.v u0.val = finiteUniformizerValue)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    [MeasurableSpace (valuationIntegralMatrixSubgroup v n)]
    [BorelSpace (valuationIntegralMatrixSubgroup v n)]
    (muG : Measure (Units (Matrix (Fin n) (Fin n) L))) [muG.IsMulLeftInvariant] [SFinite muG]
    (hMass : muG (valuationIntegralMatrixSubgroup v n : Set (Units (Matrix (Fin n) (Fin n) L))) = 1)
    (nu : Measure (valuationIntegralMatrixSubgroup v n)) [IsProbabilityMeasure nu]
    (chi : Fin n -> MonoidHom GU Complex)
    (hUnit : forall i x, Membership.mem (heckeLocalUnitShell p) x -> chi i x = 1)
    (s : Complex)
    (hNorm : forall i, norm (chi i u0 * (dedekindPrimeNorm K p : Complex) ^ (-s)) < 1) :
    let c := heckeUnramifiedSphericalCoefficient p n nu (productDiagonalCharacter n chi)
    let f := fun g => heckeUnramifiedLocalMatrixWeight p n s g * c g
    And (Integrable f muG) (integral muG f = Finset.univ.prod
      (fun i : Fin n => Inv.inv (1 - chi i u0 * (dedekindPrimeNorm K p : Complex) ^ (-s)))) := by
  have hWeighted : forall i, norm (unramifiedLocalWeightedCharacter (chi i) s u0) < 1 := by
    intro i
    rw [weightedCharacter_uniformizer_primeNorm p (chi i) s u0 hu0]
    exact hNorm i
  simpa only [weightedCharacter_uniformizer_primeNorm p _ s u0 hu0] using
    integrableAndIntegral_heckeUnramifiedSphericalCoefficient_haar p n u0 hu0
      muG hMass nu chi hUnit s hWeighted

end ActualHaar

section AbsoluteEulerMajorant

section

variable (L : Type*) [NormedField L]

private def localAbsoluteMajorantCharacter (n : Nat) (i : Fin n) :
    MonoidHom (Units L) Complex where
  toFun x := (norm x.val ^ ((i.val : Real) - ((n : Real) - 1) / 2) : Real)
  map_one' := by simp
  map_mul' x y := by
    change ((norm (x.val * y.val) ^
        ((i.val : Real) - ((n : Real) - 1) / 2) : Real) : Complex) = _
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul]

private theorem localAbsoluteMajorant_normalizedInducingCharacter (n : Nat)
    (b : valuationUpperTriangularSubgroup L n) :
    valuationNormalizedInducingCharacter L n
      (productDiagonalCharacter n (localAbsoluteMajorantCharacter L n)) b = 1 := by
  let a := valuationTriangularDiagonalHom L n b
  let e := fun i : Fin n => ((n : Real) - 1) / 2 - (i.val : Real)
  have hPositive (i : Fin n) : 0 < norm (a.val i) := by
    exact norm_pos_iff.mpr (MulEquiv.piUnits a i).ne_zero
  have hProduct : (Finset.univ.prod (fun i : Fin n => norm (a.val i) ^ e i)) *
      (Finset.univ.prod (fun i : Fin n =>
        norm (a.val i) ^ ((i.val : Real) - ((n : Real) - 1) / 2))) = 1 := by
    rw [<- Finset.prod_mul_distrib]
    calc
      _ = Finset.univ.prod (fun _ : Fin n => (1 : Real)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [<- Real.rpow_add (hPositive i)]
        have hCancel : e i + ((i.val : Real) - ((n : Real) - 1) / 2) = 0 := by
          dsimp [e]
          ring
        rw [hCancel, Real.rpow_zero]
      _ = 1 := Finset.prod_const_one
  change ((Finset.univ.prod (fun i : Fin n => norm (a.val i) ^ e i) : Real) : Complex) *
    (Finset.univ.prod (fun i : Fin n =>
      ((norm (a.val i) ^ ((i.val : Real) - ((n : Real) - 1) / 2) : Real) : Complex))) = 1
  rw [<- Complex.ofReal_prod, <- Complex.ofReal_mul, hProduct, Complex.ofReal_one]

end

variable {K : Type*} [Field K] [NumberField K]

/-- The integral of the positive determinant weight at an unramified prime. -/
def unramifiedLocalAbsoluteEulerFactor (p : HeightOneSpectrum (RingOfIntegers K))
    (n : Nat) (sigma : Real) : Real :=
  Finset.univ.prod (fun i : Fin n =>
    Inv.inv (1 - (dedekindPrimeNorm K p : Real) ^
      (((n : Real) - 1) / 2 - (i.val : Real) - sigma)))

/-- Every finite product of the local bounds is at most a fixed product of
Dedekind zeta values in their absolutely convergent half-plane. -/
theorem prod_unramifiedLocalAbsoluteEulerFactor_le
    (n : Nat) (sigma : Real) (hSigma : ((n : Real) + 1) / 2 < sigma)
    (S : Finset (HeightOneSpectrum (RingOfIntegers K))) :
    S.prod (fun p => unramifiedLocalAbsoluteEulerFactor p n sigma) <=
      Finset.univ.prod (fun i : Fin n =>
        (dedekindZeta K ((sigma - (((n : Real) - 1) / 2 - (i.val : Real)) : Real) :
          Complex)).re) := by
  let P := HeightOneSpectrum (RingOfIntegers K)
  let t : Fin n -> Real := fun i => sigma - (((n : Real) - 1) / 2 - (i.val : Real))
  let F : Fin n -> P -> Real := fun i p =>
    Inv.inv (1 - (dedekindPrimeNorm K p : Real) ^ (-t i))
  have ht (i : Fin n) : 1 < t i := by
    have hi : (0 : Real) <= (i.val : Real) := Nat.cast_nonneg _
    dsimp [t]
    linarith
  have hp (p : P) : (1 : Real) < (dedekindPrimeNorm K p : Real) := by
    exact_mod_cast one_lt_dedekindPrimeNorm K p
  have hF (i : Fin n) (p : P) : 1 <= F i p := by
    have h0 : 0 <= (dedekindPrimeNorm K p : Real) ^ (-t i) :=
      Real.rpow_nonneg ((zero_lt_one.trans (hp p)).le) _
    have h1 : (dedekindPrimeNorm K p : Real) ^ (-t i) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (hp p) (neg_lt_zero.mpr (zero_lt_one.trans (ht i)))
    change 1 <= Inv.inv (1 - (dedekindPrimeNorm K p : Real) ^ (-t i))
    have hInv : (1 : Real) / 1 <= 1 / (1 - (dedekindPrimeNorm K p : Real) ^ (-t i)) :=
      div_le_div_of_nonneg_left zero_le_one (sub_pos.mpr h1) (sub_le_self _ h0)
    simpa only [div_one, one_div] using hInv
  have hCast (i : Fin n) (p : P) : (F i p : Complex) =
      Inv.inv (1 - (dedekindPrimeNorm K p : Complex) ^ (-(t i : Complex))) := by
    dsimp only [F]
    rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_cpow ((zero_lt_one.trans (hp p)).le), Complex.ofReal_natCast,
      Complex.ofReal_neg]
  have hP (i : Fin n) : HasProd (F i) (dedekindZeta K (t i : Complex)).re := by
    have hZ := hasProd_dedekindZeta_eulerFactors K
      (s := (t i : Complex)) (by simpa only [Complex.ofReal_re] using ht i)
    have hZ' : HasProd (fun p : P => (F i p : Complex)) (dedekindZeta K (t i : Complex)) := by
      simpa only [hCast] using hZ
    have hR := Complex.continuous_re.continuousAt.tendsto.comp hZ'
    simpa only [HasProd, Function.comp_def, <- Complex.ofReal_prod, Complex.ofReal_re] using hR
  have hAll (i : Fin n) : S.prod (F i) <= (dedekindZeta K (t i : Complex)).re := by
    have hT : Filter.Tendsto (fun A : Finset P => A.prod (F i)) Filter.atTop
        (nhds (dedekindZeta K (t i : Complex)).re) := hP i
    apply ge_of_tendsto hT
    filter_upwards [Filter.eventually_ge_atTop S] with A hSA
    exact Finset.prod_le_prod_of_subset_of_one_le hSA
      (fun p _ => zero_le_one.trans (hF i p)) (fun p _ _ => hF i p)
  have hLocal (p : P) :
      unramifiedLocalAbsoluteEulerFactor p n sigma = Finset.univ.prod (fun i : Fin n => F i p) := by
    unfold unramifiedLocalAbsoluteEulerFactor
    apply Finset.prod_congr rfl
    intro i hi
    have hE : ((n : Real) - 1) / 2 - (i.val : Real) - sigma = -t i := by
      dsimp [t]
      ring
    rw [hE]
  simp only [hLocal, Finset.prod_comm (s := S)]
  exact Finset.prod_le_prod (fun i _ =>
    Finset.prod_nonneg (fun p _ => zero_le_one.trans (hF i p))) (fun i _ => hAll i)

variable (p : HeightOneSpectrum (RingOfIntegers K))
local notation "L" => p.adicCompletion K
local notation "GU" => Units L
local notation "v" => (Valued.v : Valuation L (WithZero (Multiplicative Int)))

private theorem norm_heckeUnramifiedLocalMatrixWeight (n : Nat) (s : Complex)
    (g : Units (Matrix (Fin n) (Fin n) L)) :
    (norm (heckeUnramifiedLocalMatrixWeight p n s g) : Complex) =
      heckeUnramifiedLocalMatrixWeight p n (s.re : Complex) g := by
  let S : Set (Units (Matrix (Fin n) (Fin n) L)) :=
    {x | forall i j : Fin n, Membership.mem (v).integer (x.val i j)}
  unfold heckeUnramifiedLocalMatrixWeight
  by_cases hg : Membership.mem S g
  next =>
    have hDet : IsUnit g.val.det := g.isUnit.map Matrix.detMonoidHom
    have hPos : 0 < norm g.val.det := norm_pos_iff.mpr hDet.ne_zero
    rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg,
      Complex.norm_cpow_eq_rpow_re_of_pos hPos, Complex.add_re, Complex.ofReal_re,
      <- Complex.ofReal_add, <- Complex.ofReal_cpow hPos.le]
  next =>
    rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, norm_zero, Complex.ofReal_zero]

variable [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
variable [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
variable [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
variable [MeasurableSpace (Units (p.adicCompletion K))]
variable [BorelSpace (Units (p.adicCompletion K))]

private theorem integrableAndIntegral_heckeUnramifiedLocalMatrixWeight_localRange
    [SigmaFinite (heckeLocalHaar p)]
    (n : Nat) (u0 : GU) (hu0 : Valued.v u0.val = finiteUniformizerValue)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    (muG : Measure (Units (Matrix (Fin n) (Fin n) L))) [muG.IsMulLeftInvariant] [SFinite muG]
    (hMass : muG (valuationIntegralMatrixSubgroup v n :
      Set (Units (Matrix (Fin n) (Fin n) L))) = 1)
    (sigma : Real) (hsigma : ((n : Real) - 1) / 2 < sigma) :
    let w := heckeUnramifiedLocalMatrixWeight p n (sigma : Complex)
    And (Integrable w muG) (integral muG w = Finset.univ.prod
      (fun i : Fin n =>
        Inv.inv (1 - (((dedekindPrimeNorm K p : Real) ^
          (((n : Real) - 1) / 2 - (i.val : Real) - sigma) : Real) : Complex)))) := by
  let C := valuationIntegralMatrixSubgroup v n
  let _ : MeasurableSpace C := borel C
  let _ : BorelSpace C := BorelSpace.mk rfl
  let nu := Measure.dirac (1 : C)
  let _ : IsProbabilityMeasure nu := inferInstance
  let chi := localAbsoluteMajorantCharacter L n
  let q : Real := dedekindPrimeNorm K p
  let e : Fin n -> Real := fun i => ((n : Real) - 1) / 2 - (i.val : Real)
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast one_lt_dedekindPrimeNorm K p
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hUnit (i : Fin n) (x : GU) (hx : Membership.mem (heckeLocalUnitShell p) x) :
      chi i x = 1 := by
    have hv : Valued.v x.val = 1 := hx
    change ((norm x.val ^ ((i.val : Real) - ((n : Real) - 1) / 2) : Real) : Complex) = 1
    have hNorm : norm x.val = 1 := by
      rw [FinitePlace.norm_def, hv]
      simp
    simp [hNorm]
  have hParam (i : Fin n) :
      chi i u0 * (dedekindPrimeNorm K p : Complex) ^ (-(sigma : Complex)) =
        ((q ^ (e i - sigma) : Real) : Complex) := by
    have hCast : (dedekindPrimeNorm K p : Complex) = (q : Complex) :=
      (Complex.ofReal_natCast (dedekindPrimeNorm K p)).symm
    have hInv : norm u0.val = Inv.inv q :=
      norm_eq_inv_of_valuation_finiteUniformizer p u0.val hu0
    have hExp : -((i.val : Real) - ((n : Real) - 1) / 2) = e i := by
      dsimp [e]
      ring
    change ((norm u0.val ^ ((i.val : Real) - ((n : Real) - 1) / 2) : Real) : Complex) * _ = _
    rw [hInv, <- Real.rpow_neg_eq_inv_rpow, hExp, hCast, <- Complex.ofReal_neg,
      <- Complex.ofReal_cpow hq0.le, <- Complex.ofReal_mul, <- Real.rpow_add hq0]
    rfl
  have hNorm (i : Fin n) :
      norm (chi i u0 * (dedekindPrimeNorm K p : Complex) ^ (-(sigma : Complex))) < 1 := by
    have hExp : e i - sigma < 0 := by
      have hi : (0 : Real) <= (i.val : Real) := Nat.cast_nonneg _
      dsimp [e]
      linarith
    rw [hParam i, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq0.le _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq hExp
  have hCoeff (g : Units (Matrix (Fin n) (Fin n) L)) :
      heckeUnramifiedSphericalCoefficient p n nu (productDiagonalCharacter n chi) g = 1 := by
    have hOne (k : C) :
        valuationSphericalSection v n
          (valuationNormalizedInducingCharacter L n (productDiagonalCharacter n chi))
          (k.val * g) = 1 := by
      unfold valuationSphericalSection
      exact localAbsoluteMajorant_normalizedInducingCharacter L n _
    unfold heckeUnramifiedSphericalCoefficient
    simp [hOne]
  have hInt := integrableAndIntegral_heckeUnramifiedSphericalCoefficient_primeNorm
    p n u0 hu0 muG hMass nu chi hUnit (sigma : Complex) hNorm
  dsimp only at hInt
  simpa only [hCoeff, mul_one, hParam] using hInt

/-- The positive determinant weight on integral matrices is absolutely
integrable. Its integral is the local Euler factor of the trivial spherical
coefficient, expressed with the normalized prime norm. -/
theorem integrableAndIntegral_heckeUnramifiedLocalMatrixWeight
    [SigmaFinite (heckeLocalHaar p)]
    (n : Nat) (u0 : GU) (hu0 : Valued.v u0.val = finiteUniformizerValue)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    (muG : Measure (Units (Matrix (Fin n) (Fin n) L))) [muG.IsMulLeftInvariant] [SFinite muG]
    (hMass : muG (valuationIntegralMatrixSubgroup v n :
      Set (Units (Matrix (Fin n) (Fin n) L))) = 1)
    (sigma : Real) (hsigma : ((n : Real) + 1) / 2 < sigma) :
    let w := heckeUnramifiedLocalMatrixWeight p n (sigma : Complex)
    And (Integrable w muG) (integral muG w = Finset.univ.prod
      (fun i : Fin n =>
        Inv.inv (1 - (((dedekindPrimeNorm K p : Real) ^
          (((n : Real) - 1) / 2 - (i.val : Real) - sigma) : Real) : Complex)))) := by
  exact integrableAndIntegral_heckeUnramifiedLocalMatrixWeight_localRange
    p n u0 hu0 muG hMass sigma (by linarith)

/-- In the half-plane where the product of local majorants converges, a
spherical coefficient bounded by one gives an absolutely integrable local
zeta integrand. The same Euler factor bounds its integral of the norm. -/
theorem integrableAndAbsoluteIntegral_le_unramifiedLocalWeight
    [SigmaFinite (heckeLocalHaar p)]
    (n : Nat) (u0 : GU) (hu0 : Valued.v u0.val = finiteUniformizerValue)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    (muG : Measure (Units (Matrix (Fin n) (Fin n) L))) [muG.IsMulLeftInvariant] [SFinite muG]
    (hMass : muG (valuationIntegralMatrixSubgroup v n :
      Set (Units (Matrix (Fin n) (Fin n) L))) = 1)
    (s : Complex) (hs : ((n : Real) + 1) / 2 < s.re)
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex)
    (hc : Filter.Eventually (fun g => norm (c g) <= 1) (ae muG))
    (hMeas : AEStronglyMeasurable (fun g => heckeUnramifiedLocalMatrixWeight p n s g * c g) muG) :
    let f := fun g => heckeUnramifiedLocalMatrixWeight p n s g * c g
    And (Integrable f muG) (integral muG (fun g => norm (f g)) <=
      unramifiedLocalAbsoluteEulerFactor p n s.re) := by
  let f := fun g => heckeUnramifiedLocalMatrixWeight p n s g * c g
  let W := heckeUnramifiedLocalMatrixWeight p n (s.re : Complex)
  let A := fun i : Fin n => (dedekindPrimeNorm K p : Real) ^
    (((n : Real) - 1) / 2 - (i.val : Real) - s.re)
  have hI := integrableAndIntegral_heckeUnramifiedLocalMatrixWeight p n u0 hu0 muG hMass s.re hs
  have hW : Integrable W muG := hI.1
  have hWnorm (g : Units (Matrix (Fin n) (Fin n) L)) :
      (norm (W g) : Complex) = W g := by
    simpa only [W, Complex.ofReal_re] using
      norm_heckeUnramifiedLocalMatrixWeight p n (s.re : Complex) g
  have hDom : Filter.Eventually (fun g => norm (f g) <= norm (W g)) (ae muG) := by
    filter_upwards [hc] with g hg
    have hEq : norm (heckeUnramifiedLocalMatrixWeight p n s g) = norm (W g) :=
      Complex.ofReal_injective
        ((norm_heckeUnramifiedLocalMatrixWeight p n s g).trans (hWnorm g).symm)
    dsimp [f]
    rw [norm_mul, hEq]
    exact mul_le_of_le_one_right (norm_nonneg _) hg
  have hF : Integrable f muG := hW.norm.mono' hMeas hDom
  have hDomInt : integral muG (fun g => norm (f g)) <= integral muG (fun g => norm (W g)) :=
    integral_mono_ae hF.norm hW.norm hDom
  have hPosInt : integral muG (fun g => norm (W g)) =
      Finset.univ.prod (fun i : Fin n => Inv.inv (1 - A i)) := by
    apply Complex.ofReal_injective
    rw [<- integral_complex_ofReal, show (fun g => (norm (W g) : Complex)) = W from funext hWnorm,
      Complex.ofReal_prod]
    simpa only [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one] using hI.2
  exact And.intro hF (hDomInt.trans_eq hPosInt)

private theorem integrable_heckeLocalZetaIntegrand_of_boundedMatrixTest
    [SigmaFinite (heckeLocalHaar p)]
    (n : Nat) (u0 : GU) (hu0 : Valued.v u0.val = finiteUniformizerValue)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    [MeasurableMul (Units (Matrix (Fin n) (Fin n) L))]
    (muG : Measure (Units (Matrix (Fin n) (Fin n) L))) [muG.IsMulLeftInvariant] [SFinite muG]
    (hMass : muG (valuationIntegralMatrixSubgroup v n :
      Set (Units (Matrix (Fin n) (Fin n) L))) = 1)
    (s : Complex) (hs : ((n : Real) - 1) / 2 < s.re)
    (A : Units (Matrix (Fin n) (Fin n) L))
    (a : Units (Matrix (Fin n) (Fin n) L) -> Complex)
    (hSupport : forall g, Not (a g = 0) -> forall i j : Fin n,
      Membership.mem (v).integer ((A * g).val i j))
    (B : Real) (hB0 : 0 <= B)
    (hB : Filter.Eventually (fun g => norm (a g) <= B) (ae muG))
    (hMeas : AEStronglyMeasurable (fun g => (norm g.val.det : Complex) ^
      (s + (((n : Real) - 1) / 2 : Real)) * a g) muG) :
    Integrable (fun g => (norm g.val.det : Complex) ^
      (s + (((n : Real) - 1) / 2 : Real)) * a g) muG := by
  let G := Units (Matrix (Fin n) (Fin n) L)
  let e := s.re + ((n : Real) - 1) / 2
  let W := heckeUnramifiedLocalMatrixWeight p n (s.re : Complex)
  let S : Set G := {g : G | forall i j : Fin n, Membership.mem (v).integer (g.val i j)}
  let D : Real := norm A.val.det ^ e
  have hPos (g : G) : 0 < norm g.val.det :=
    norm_pos_iff.mpr (g.isUnit.map Matrix.detMonoidHom).ne_zero
  have hD : 0 < D := Real.rpow_pos_of_pos (hPos A) _
  have hComplex (g : G) : norm ((norm g.val.det : Complex) ^
      (s + (((n : Real) - 1) / 2 : Real))) = norm g.val.det ^ e := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hPos g), Complex.add_re, Complex.ofReal_re]
  have hReal (g : G) (hg : Membership.mem S g) : norm (W g) = norm g.val.det ^ e := by
    unfold W heckeUnramifiedLocalMatrixWeight
    rw [Set.indicator_of_mem hg, Complex.norm_cpow_eq_rpow_re_of_pos (hPos g),
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
  have hMul (g : G) : norm (A * g).val.det ^ e = D * norm g.val.det ^ e := by
    rw [show (A * g).val.det = A.val.det * g.val.det from Matrix.det_mul _ _,
      norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  have hW : Integrable W muG :=
    (integrableAndIntegral_heckeUnramifiedLocalMatrixWeight_localRange p n u0 hu0 muG hMass
      s.re hs).1
  have hComp : Integrable (fun g : G => norm (W (A * g))) muG :=
    (measurePreserving_mul_left muG A).integrable_comp_of_integrable hW.norm
  refine (hComp.const_mul (B / D)).mono' hMeas ?_
  filter_upwards [hB] with g hg
  by_cases hZero : a g = 0
  next =>
    rw [hZero, mul_zero, norm_zero]
    exact mul_nonneg (div_nonneg hB0 hD.le) (norm_nonneg _)
  next =>
    have hKeep : Membership.mem S (A * g) := hSupport g hZero
    rw [norm_mul, hComplex, hReal (A * g) hKeep, hMul]
    calc
      norm g.val.det ^ e * norm (a g) <= norm g.val.det ^ e * B :=
        mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (B / D) * (D * norm g.val.det ^ e) := by
        field_simp [hD.ne']

/-- The local Godement--Jacquet integral with a continuous compactly
supported matrix test is absolutely convergent for a measurable matrix
coefficient bounded by one. The hypothesis on the real part is the single-place bound. -/
theorem integrable_heckeLocalZetaIntegrand_of_compactlySupportedTest
    [SigmaFinite (heckeLocalHaar p)]
    (n : Nat) (u0 : GU) (hu0 : Valued.v u0.val = finiteUniformizerValue)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    [MeasurableMul (Units (Matrix (Fin n) (Fin n) L))]
    (muG : Measure (Units (Matrix (Fin n) (Fin n) L))) [muG.IsMulLeftInvariant] [SFinite muG]
    (hMass : muG (valuationIntegralMatrixSubgroup v n :
      Set (Units (Matrix (Fin n) (Fin n) L))) = 1)
    (s : Complex) (hs : ((n : Real) - 1) / 2 < s.re)
    (Phi : Matrix (Fin n) (Fin n) L -> Complex) (hPhi : Continuous Phi)
    (hCompact : HasCompactSupport Phi)
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex)
    (hc : AEStronglyMeasurable c muG)
    (hcBound : Filter.Eventually (fun g => norm (c g) <= 1) (ae muG)) :
    Integrable (fun g => (norm g.val.det : Complex) ^
      (s + (((n : Real) - 1) / 2 : Real)) * (Phi g.val * c g)) muG := by
  classical
  let G := Units (Matrix (Fin n) (Fin n) L)
  let a (g : G) := Phi g.val * c g
  have hEntries (i j : Fin n) : Exists (fun C : Real => forall x,
      Membership.mem (tsupport Phi) x -> norm (x i j) <= C) :=
    hCompact.exists_bound_of_continuousOn
      (f := fun x : Matrix (Fin n) (Fin n) L => x i j)
      (((continuous_apply j).comp (continuous_apply i) :
        Continuous (fun x : Matrix (Fin n) (Fin n) L => x i j)).continuousOn)
  choose C hC using hEntries
  let R (i j : Fin n) := max 1 (C i j)
  have hR (i j : Fin n) : 0 < R i j := zero_lt_one.trans_le (le_max_left _ _)
  have hPrime : (1 : Real) < (dedekindPrimeNorm K p : Real) := by
    exact_mod_cast one_lt_dedekindPrimeNorm K p
  have hu : norm u0.val < 1 := by
    rw [norm_eq_inv_of_valuation_finiteUniformizer p u0.val hu0]
    simpa only [one_div, inv_one] using one_div_lt_one_div_of_lt zero_lt_one hPrime
  have ht : Filter.Tendsto (fun m : Nat => norm u0.val ^ m) Filter.atTop (nhds (0 : Real)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hu
  have hSmall : Filter.Eventually (fun m : Nat => forall i j : Fin n,
      norm u0.val ^ m < 1 / R i j) Filter.atTop :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j =>
      (tendsto_order.1 ht).2 _ (div_pos zero_lt_one (hR i j))))
  choose m hm using hSmall.exists
  let A : G := Units.map (Matrix.scalar (Fin n)).toMonoidHom (u0 ^ m)
  have hSupport (g : G) (hg : Not (a g = 0)) (i j : Fin n) :
      Membership.mem (v).integer ((A * g).val i j) := by
    have hPhiNonzero : Not (Phi g.val = 0) := fun h => hg (by simp [a, h])
    have hT : Membership.mem (tsupport Phi) g.val :=
      subset_closure (show Membership.mem (Function.support Phi) g.val from hPhiNonzero)
    have hNum : norm (g.val i j) <= R i j := (hC i j g.val hT).trans (le_max_right _ _)
    have hScale := (mul_lt_mul_of_pos_right (hm i j) (hR i j)).le
    have hCancel : (1 / R i j) * R i j = 1 := by field_simp [(hR i j).ne']
    rw [hCancel] at hScale
    apply (heckeLocal_mem_integers_iff_norm_le_one p _).mpr
    change norm ((Matrix.scalar (Fin n) (u0 ^ m).val * g.val) i j) <= 1
    rw [Matrix.scalar_apply, Matrix.diagonal_mul, norm_mul, Units.val_pow_eq_pow_val, norm_pow]
    exact (mul_le_mul_of_nonneg_left hNum (pow_nonneg (norm_nonneg _) _)).trans hScale
  choose D hD using hCompact.exists_bound_of_continuousOn hPhi.continuousOn
  let B := max 0 D
  have hPhiBound (x : Matrix (Fin n) (Fin n) L) : norm (Phi x) <= B := by
    by_cases hx : Phi x = 0
    next =>
      rw [hx, norm_zero]
      exact le_max_left _ _
    next =>
      exact (hD x (subset_closure
        (show Membership.mem (Function.support Phi) x from hx))).trans (le_max_right _ _)
  have hBound : Filter.Eventually (fun g => norm (a g) <= B) (ae muG) := by
    filter_upwards [hcBound] with g hg
    dsimp [a]
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hg).trans (hPhiBound g.val)
  have hVal : Continuous (fun g : G => g.val) := Units.continuous_val
  have hBase : Continuous (fun g : G => (norm g.val.det : Complex)) :=
    Complex.continuous_ofReal.comp hVal.matrix_det.norm
  have hPow : Continuous (fun g : G => (norm g.val.det : Complex) ^
      (s + (((n : Real) - 1) / 2 : Real))) :=
    hBase.cpow continuous_const (fun g => Complex.ofReal_mem_slitPlane.mpr
      (norm_pos_iff.mpr (g.isUnit.map Matrix.detMonoidHom).ne_zero))
  have ha : AEStronglyMeasurable a muG :=
    (hPhi.comp hVal).measurable.aestronglyMeasurable.mul hc
  exact integrable_heckeLocalZetaIntegrand_of_boundedMatrixTest p n u0 hu0 muG hMass
    s hs A a hSupport B (le_max_left _ _) hBound (hPow.measurable.aestronglyMeasurable.mul ha)

end AbsoluteEulerMajorant

section LocalUnitZetaTest

open Topology

private theorem isOpenEmbedding_matrixUnitsVal
    (F : Type*) [NormedField F] (n : Nat) :
    IsOpenEmbedding (fun g : Units (Matrix (Fin n) (Fin n) F) => g.val) := by
  classical
  let M := Matrix (Fin n) (Fin n) F
  let G := Units M
  let D : Set M := {A | Not (A.det = 0)}
  have hD : IsOpen D := isOpen_ne_fun continuous_id.matrix_det continuous_const
  let encode (g : G) : D :=
    Subtype.mk g.val (g.isUnit.map Matrix.detMonoidHom).ne_zero
  let decode (A : D) : G := Matrix.GeneralLinearGroup.mkOfDetNeZero A.val A.property
  have hEncode : Continuous encode :=
    Units.continuous_val.subtype_mk (fun g => (encode g).property)
  have hDecode : Continuous decode := by
    apply Units.continuous_iff.mpr
    refine And.intro continuous_subtype_val ?_
    have hEq (A : D) : (Inv.inv (decode A)).val = Inv.inv A.val :=
      Matrix.coe_units_inv (decode A)
    simp only [hEq]
    rw [continuous_iff_continuousAt]
    intro A
    have hFieldInv : ContinuousAt (Ring.inverse : F -> F) A.val.det := by
      rw [show (Ring.inverse : F -> F) = Inv.inv from funext Ring.inverse_eq_inv]
      fun_prop (disch := exact A.property)
    exact (continuousAt_matrix_inv A.val hFieldInv).comp continuous_subtype_val.continuousAt
  let e : Homeomorph G D :=
    { toFun := encode
      invFun := decode
      left_inv := fun g => Units.ext rfl
      right_inv := fun A => Subtype.ext rfl
      continuous_toFun := hEncode
      continuous_invFun := hDecode }
  exact hD.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding

/- The local test uses the same determinant normalization as the
unramified calculation. -/
variable {K : Type*} [Field K] [NumberField K]
variable (p : HeightOneSpectrum (RingOfIntegers K))

local notation "L" => p.adicCompletion K
local notation "v" => (Valued.v : Valuation L (WithZero (Multiplicative Int)))

/-- A coefficient equal to one near the identity has a compactly supported
locally constant matrix test whose Godement--Jacquet integral is identically
one. The test is obtained by normalizing the Haar mass of a compact open
neighborhood inside the integral matrix subgroup. -/
theorem exists_heckeLocalZetaTest_integral_one
    (n : Nat)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L))) [mu.IsHaarMeasure]
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex)
    (hNear : Filter.EventuallyEq (nhds (1 : Units (Matrix (Fin n) (Fin n) L)))
      c (fun _ => 1)) :
    Exists (fun Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex =>
      And (HasCompactSupport (fun A => Phi A)) (forall s : Complex,
        let f := fun g : Units (Matrix (Fin n) (Fin n) L) =>
          (norm g.val.det : Complex) ^ (s + (((n : Real) - 1) / 2 : Real)) *
            (Phi g.val * c g)
        And (Integrable f mu) (integral mu f = 1))) := by
  classical
  let M := Matrix (Fin n) (Fin n) L
  let G := Units M
  let Integers : Set L := p.adicCompletionIntegers K
  have hIntegerComp : IsCompact Integers :=
    isCompact_iff_compactSpace.mpr (compactSpace_heckeLocalIntegers p)
  have hIntegerOpen : IsOpen Integers := Valued.isOpen_valuationSubring L
  have hIntegerZero : Membership.mem Integers (0 : L) := (p.adicCompletionIntegers K).zero_mem
  let _ : LocallyCompactSpace L :=
    hIntegerComp.locallyCompactSpace_of_mem_nhds_of_addGroup (hIntegerOpen.mem_nhds hIntegerZero)
  let _ : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (Fin n -> Fin n -> L))
  let _ : TotallySeparatedSpace L := by
    apply totallySeparatedSpace_iff_exists_isClopen.mpr
    intro x y hxy
    let r := (v).restrict (y - x)
    let D : Set L := {z | (v).restrict (z - x) < r}
    have hD : IsClopen D :=
      (Valued.isClopen_ball L r).preimage (continuous_id.sub continuous_const)
    have hDiff : IsUnit (y - x) := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxy.symm)
    have hr : 0 < r :=
      zero_lt_iff.mpr (hDiff.map (v).restrict.toMonoidWithZeroHom).ne_zero
    have hx : Membership.mem D x := by
      change (v).restrict (x - x) < r
      rw [sub_self, map_zero]
      exact hr
    have hy : Membership.mem (Compl.compl D) y := by
      change Not (r < r)
      exact lt_irrefl r
    exact Exists.intro D (And.intro hD (And.intro hx hy))
  let _ : TotallyDisconnectedSpace M :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n -> Fin n -> L))
  let C : Set G := valuationIntegralMatrixSubgroup v n
  have hCOpen : IsOpen C :=
    isOpen_valuationIntegralMatrixSubgroup v n (Valued.isOpen_valuationSubring L)
  have hC1 : Membership.mem C (1 : G) := (valuationIntegralMatrixSubgroup v n).one_mem
  have hNear1 : Membership.mem (nhds (1 : G)) {g : G | c g = 1} := hNear
  have hBoth := Filter.inter_mem hNear1 (hCOpen.mem_nhds hC1)
  choose V hV using mem_nhds_iff.mp hBoth
  have hVOpen := hV.2.1
  have hV1 := hV.2.2
  have hEmbed := isOpenEmbedding_matrixUnitsVal L n
  let vG : G -> M := fun g => g.val
  have hVImage : IsOpen (vG '' V) := hEmbed.isOpenMap _ hVOpen
  have hMatrixOne : Membership.mem (vG '' V) (1 : M) :=
    Set.mem_image_of_mem vG hV1
  choose S hS using exists_compact_subset hVImage hMatrixOne
  have hSComp := hS.1
  have hSIn := hS.2.1
  have hSsub := hS.2.2
  choose U hU using loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp
    (isOpen_interior.mem_nhds hSIn)
  have hUClopen : IsClopen U := hU.1
  have hU1 := hU.2.1
  have hUsub := hU.2.2
  have hUS : Set.Subset U S := hUsub.trans interior_subset
  have hUComp : IsCompact U := hSComp.of_isClosed_subset hUClopen.1 hUS
  have hUV : Set.Subset U (vG '' V) := hUS.trans hSsub
  let W := Set.preimage vG U
  have hWV : Set.Subset W V := by
    intro g hg
    choose g' hg' using hUV hg
    rw [<- hEmbed.injective hg'.2]
    exact hg'.1
  have hWOpen : IsOpen W := hUClopen.2.preimage Units.continuous_val
  have hW1 : Membership.mem W (1 : G) := hU1
  have hWComp : IsCompact W := hEmbed.isEmbedding.isInducing.isCompact_preimage'
    hUComp (hUV.trans (Set.image_subset_range vG V))
  have hWMeas : MeasurableSet W := hWOpen.measurableSet
  have hPos : 0 < mu W := by
    apply measure_pos_of_nonempty_interior mu
    rw [hWOpen.interior_eq]
    exact Exists.intro (1 : G) hW1
  have hFinite : mu W < (Top.top : ENNReal) := hWComp.measure_lt_top
  have hRealPos : 0 < mu.real W := ENNReal.toReal_pos hPos.ne' hFinite.ne
  let k : Complex := Inv.inv (mu.real W : Complex)
  let Phi : LocallyConstant M Complex := LocallyConstant.const M k * LocallyConstant.charFn Complex hUClopen
  have hPhi (A : M) : Phi A = U.indicator (fun _ => k) A := by
    change k * (LocallyConstant.charFn Complex hUClopen) A = _
    rw [show (LocallyConstant.charFn Complex hUClopen) A =
      U.indicator (fun _ : M => (1 : Complex)) A from rfl]
    by_cases hA : Membership.mem U A
    next => rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA, mul_one]
    next => rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA, mul_zero]
  have hPhiSupport : Set.Subset (Function.support (fun A => Phi A)) U := by
    intro A hA
    by_contra hNot
    exact hA ((hPhi A).trans (Set.indicator_of_notMem hNot _))
  have hPhiComp : HasCompactSupport (fun A => Phi A) :=
    hUComp.of_isClosed_subset isClosed_closure (closure_minimal hPhiSupport hUClopen.1)
  refine Exists.intro Phi (And.intro hPhiComp ?_)
  intro s
  have hEquality : (fun g : G =>
      (norm g.val.det : Complex) ^ (s + (((n : Real) - 1) / 2 : Real)) *
        (Phi g.val * c g)) = W.indicator (fun _ => k) := by
    funext g
    rw [hPhi g.val]
    by_cases hg : Membership.mem W g
    next =>
      have hUV := hV.1 (hWV hg)
      have hDet : norm g.val.det = 1 := norm_det_heckeIntegralMatrixUnit p n g hUV.2
      rw [Set.indicator_of_mem (show Membership.mem U g.val from hg),
        Set.indicator_of_mem hg, hUV.1, hDet, Complex.ofReal_one, Complex.one_cpow, mul_one, one_mul]
    next =>
      rw [Set.indicator_of_notMem (show Not (Membership.mem U g.val) from hg),
        Set.indicator_of_notMem hg, zero_mul, mul_zero]
  dsimp only
  rw [hEquality]
  have _ : IsFiniteMeasure (mu.restrict W) := isFiniteMeasure_restrict.mpr hFinite.ne
  have hInt : IntegrableOn (fun _ : G => k) W mu := integrable_const k
  refine And.intro (hInt.integrable_indicator hWMeas) ?_
  rw [integral_indicator hWMeas, setIntegral_const, Algebra.smul_def]
  dsimp [k]
  field_simp [Complex.ofReal_ne_zero.mpr hRealPos.ne']

private theorem exists_heckeLocalZetaTest_leftTranslate_exact
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [MeasurableMul (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L))) [mu.IsMulLeftInvariant]
    (A : Units (Matrix (Fin n) (Fin n) L))
    (Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex) :
    Exists (fun Psi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex =>
      And (HasCompactSupport (fun X => Psi X)) (And (forall X, Psi X = Phi (A.val * X))
        (forall z : Complex,
        And (Iff
          (Integrable (fun g => (norm g.val.det : Complex) ^ z * (Psi g.val * c (A * g))) mu)
          (Integrable (fun g => (norm g.val.det : Complex) ^ z * (Phi g.val * c g)) mu))
          (integral mu (fun g => (norm g.val.det : Complex) ^ z * (Psi g.val * c (A * g))) =
            (norm A.val.det : Complex) ^ (-z) *
              integral mu (fun g => (norm g.val.det : Complex) ^ z * (Phi g.val * c g)))))) := by
  let M := Matrix (Fin n) (Fin n) L
  let G := Units M
  let e : Homeomorph M M :=
    { toFun := fun X => A.val * X
      invFun := fun X => A.inv * X
      left_inv := fun X => by
        change A.inv * (A.val * X) = X
        rw [<- mul_assoc, A.inv_val, one_mul]
      right_inv := fun X => by
        change A.val * (A.inv * X) = X
        rw [<- mul_assoc, A.val_inv, one_mul]
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  let Psi := LocallyConstant.comap (ContinuousMap.mk e e.continuous) Phi
  have hCompact : IsCompact (Set.preimage e (tsupport (fun X : M => Phi X))) :=
    e.isEmbedding.isInducing.isCompact_preimage' hPhi
      (fun X _ => Set.mem_range.mpr (e.surjective X))
  have hSupport : Set.Subset (Function.support (fun X : M => Psi X))
      (Set.preimage e (tsupport (fun X : M => Phi X))) := by
    intro X hX
    exact subset_closure (show Membership.mem (Function.support (fun Y : M => Phi Y))
      (e X) from hX)
  have hPsi : HasCompactSupport (fun X => Psi X) :=
    hCompact.of_isClosed_subset isClosed_closure
      (closure_minimal hSupport (isClosed_closure.preimage e.continuous))
  refine Exists.intro Psi (And.intro hPsi (And.intro (fun X => rfl) ?_))
  intro z
  let d : Complex := norm A.val.det
  let f (g : G) := (norm g.val.det : Complex) ^ z * (Phi g.val * c g)
  have hDet : Not (A.val.det = 0) := (A.isUnit.map Matrix.detMonoidHom).ne_zero
  have hD : Not (d ^ z = 0) :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hDet)))
  have hPow (g : G) : (norm ((A * g).val.det) : Complex) ^ z =
      d ^ z * (norm g.val.det : Complex) ^ z := by
    rw [show (A * g).val.det = A.val.det * g.val.det from Matrix.det_mul _ _,
      norm_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _) z]
  have hEq (g : G) : (norm g.val.det : Complex) ^ z * (Psi g.val * c (A * g)) =
      d ^ (-z) * f (A * g) := by
    change (norm g.val.det : Complex) ^ z * (Phi (A * g).val * c (A * g)) =
      d ^ (-z) * ((norm (A * g).val.det : Complex) ^ z * (Phi (A * g).val * c (A * g)))
    rw [Complex.cpow_neg, hPow]
    field_simp [hD]
  rw [funext hEq]
  refine And.intro ?_ ?_
  next =>
    refine Iff.intro ?_ (fun h => (h.comp_mul_left A).const_mul _)
    intro hf
    have hNeg : Not (d ^ (-z) = 0) := by
      rw [Complex.cpow_neg]
      exact inv_ne_zero hD
    have hRestore : (fun g : G => Inv.inv (d ^ (-z)) * (d ^ (-z) * f (A * (Inv.inv A * g)))) =
        f := by
      funext g
      have hg : A * (Inv.inv A * g) = g := by
        rw [<- mul_assoc, show A * Inv.inv A = (1 : G) from by simp, one_mul]
      rw [hg]
      field_simp [hNeg]
    change Integrable f mu
    rw [<- hRestore]
    exact (hf.comp_mul_left (Inv.inv A)).const_mul _
  next =>
    rw [integral_const_mul, integral_mul_left_eq_self f A]

/-- A left translate of a compact locally constant matrix test is another
compact locally constant test. Translating the coefficient by the same matrix
preserves absolute integrability and multiplies the zeta integral by the
inverse determinant weight. The identity holds for every complex exponent. -/
theorem exists_heckeLocalZetaTest_leftTranslate
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [MeasurableMul (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L))) [mu.IsMulLeftInvariant]
    (A : Units (Matrix (Fin n) (Fin n) L))
    (Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex) :
    Exists (fun Psi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex =>
      And (HasCompactSupport (fun X => Psi X)) (forall z : Complex,
        And (Iff
          (Integrable (fun g => (norm g.val.det : Complex) ^ z * (Psi g.val * c (A * g))) mu)
          (Integrable (fun g => (norm g.val.det : Complex) ^ z * (Phi g.val * c g)) mu))
          (integral mu (fun g => (norm g.val.det : Complex) ^ z * (Psi g.val * c (A * g))) =
            (norm A.val.det : Complex) ^ (-z) *
              integral mu (fun g => (norm g.val.det : Complex) ^ z * (Phi g.val * c g))))) := by
  choose Psi hPsi using exists_heckeLocalZetaTest_leftTranslate_exact p n mu A Phi hPhi c
  exact Exists.intro Psi (And.intro hPsi.1 hPsi.2.2)

/-- In positive rank, a matrix with uniformizer determinant translates a
compact locally constant zeta test to one whose integral is multiplied by
the residue-field cardinality to the power of the complex exponent.
The translation preserves absolute integrability at each exponent. -/
theorem exists_heckeLocalZetaTest_primeNormTranslate
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))]
    [MeasurableMul (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))]
    (mu : Measure (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))) [mu.IsMulLeftInvariant]
    (u : Units L) (hu : Valued.v u.val = finiteUniformizerValue)
    (Phi : LocallyConstant (Matrix (Fin (n + 1)) (Fin (n + 1)) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L) -> Complex) :
    Exists (fun A : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L) =>
      And (A.val.det = u.val)
        (Exists (fun Psi : LocallyConstant (Matrix (Fin (n + 1)) (Fin (n + 1)) L) Complex =>
          And (HasCompactSupport (fun X => Psi X)) (forall z : Complex,
            And (Iff
              (Integrable (fun g => (norm g.val.det : Complex) ^ z * (Psi g.val * c (A * g))) mu)
              (Integrable (fun g => (norm g.val.det : Complex) ^ z * (Phi g.val * c g)) mu))
              (integral mu (fun g => (norm g.val.det : Complex) ^ z * (Psi g.val * c (A * g))) =
                (dedekindPrimeNorm K p : Complex) ^ z *
                  integral mu (fun g => (norm g.val.det : Complex) ^ z * (Phi g.val * c g))))))) := by
  classical
  let d := Function.update (fun _ : Fin (n + 1) => (1 : L)) 0 u.val
  have hd : (Matrix.diagonal d).det = u.val := by
    rw [Matrix.det_diagonal]
    rw [Finset.prod_eq_single (0 : Fin (n + 1))]
    next => simp [d]
    next =>
      intro i _ hi
      simp [d, Function.update_of_ne hi]
    next => simp
  let A := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) (fun h => u.ne_zero (hd.symm.trans h))
  have hA : A.val.det = u.val := hd
  refine Exists.intro A (And.intro hA ?_)
  choose Psi hPsi using exists_heckeLocalZetaTest_leftTranslate p (n + 1) mu A Phi hPhi c
  refine Exists.intro Psi (And.intro hPsi.1 ?_)
  intro z
  refine And.intro (hPsi.2 z).1 ?_
  have hNorm := norm_eq_inv_of_valuation_finiteUniformizer p u.val hu
  have hPow : (norm A.val.det : Complex) ^ (-z) = (dedekindPrimeNorm K p : Complex) ^ z := by
    rw [hA, hNorm, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) (-z),
      Complex.cpow_neg, inv_inv, Complex.ofReal_natCast]
  rw [<- hPow]
  exact (hPsi.2 z).2

private def heckeLocalDeterminantWeight (n : Nat) (z : Complex) :
    MonoidHom (Units (Matrix (Fin n) (Fin n) L)) Complex where
  toFun g := (norm g.val.det : Complex) ^ z
  map_one' := by
    change (norm (1 : Matrix (Fin n) (Fin n) L).det : Complex) ^ z = 1
    rw [Matrix.det_one, norm_one, Complex.ofReal_one, Complex.one_cpow]
  map_mul' A B := by
    change (norm (A.val * B.val).det : Complex) ^ z =
      (norm A.val.det : Complex) ^ z * (norm B.val.det : Complex) ^ z
    rw [Matrix.det_mul, norm_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _) z]

/-- Powers of one matrix with uniformizer determinant give every integer
power of the prime-norm multiplier. Each translate preserves absolute
integrability at every complex exponent. -/
theorem exists_heckeLocalZetaTest_primeNormIntegerTranslate
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))]
    [MeasurableMul (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))]
    (mu : Measure (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))) [mu.IsMulLeftInvariant]
    (u : Units L) (hu : Valued.v u.val = finiteUniformizerValue)
    (Phi : LocallyConstant (Matrix (Fin (n + 1)) (Fin (n + 1)) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L) -> Complex) :
    Exists (fun A : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L) =>
      And (A.val.det = u.val) (forall m : Int,
        Exists (fun Psi : LocallyConstant (Matrix (Fin (n + 1)) (Fin (n + 1)) L) Complex =>
          And (HasCompactSupport (fun X => Psi X)) (forall z : Complex,
            And (Iff
              (Integrable (fun g => (norm g.val.det : Complex) ^ z * (Psi g.val * c (A ^ m * g))) mu)
              (Integrable (fun g => (norm g.val.det : Complex) ^ z * (Phi g.val * c g)) mu))
              (integral mu (fun g => (norm g.val.det : Complex) ^ z * (Psi g.val * c (A ^ m * g))) =
                ((dedekindPrimeNorm K p : Complex) ^ z) ^ m *
                  integral mu (fun g => (norm g.val.det : Complex) ^ z * (Phi g.val * c g))))))) := by
  choose A hA using exists_heckeLocalZetaTest_primeNormTranslate p n mu u hu Phi hPhi c
  refine Exists.intro A (And.intro hA.1 ?_)
  intro m
  choose Psi hPsi using exists_heckeLocalZetaTest_leftTranslate p (n + 1) mu (A ^ m) Phi hPhi c
  refine Exists.intro Psi (And.intro hPsi.1 ?_)
  intro z
  refine And.intro (hPsi.2 z).1 ?_
  have hNorm := norm_eq_inv_of_valuation_finiteUniformizer p u.val hu
  have hPowA : heckeLocalDeterminantWeight p (n + 1) (-z) A = (dedekindPrimeNorm K p : Complex) ^ z := by
    change (norm A.val.det : Complex) ^ (-z) = _
    rw [hA.1, hNorm, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) (-z),
      Complex.cpow_neg, inv_inv, Complex.ofReal_natCast]
  have hPow : (norm (A ^ m).val.det : Complex) ^ (-z) =
      ((dedekindPrimeNorm K p : Complex) ^ z) ^ m := by
    change heckeLocalDeterminantWeight p (n + 1) (-z) (A ^ m) = _
    rw [map_zpow, hPowA]
  rw [<- hPow]
  exact (hPsi.2 z).2

/-- Multiplying an absolutely convergent local zeta integral by any
Laurent polynomial in the prime-norm multiplier is realized by a finite
linear combination of translated compact locally constant tests and their
translated coefficients. The tests are chosen independently of the
polynomial and the complex exponent. -/
theorem exists_heckeLocalZetaTest_primeNormLaurentTranslate
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))]
    [MeasurableMul (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))]
    (mu : Measure (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))) [mu.IsMulLeftInvariant]
    (u : Units L) (hu : Valued.v u.val = finiteUniformizerValue)
    (Phi : LocallyConstant (Matrix (Fin (n + 1)) (Fin (n + 1)) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L) -> Complex) :
    Exists (fun A : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L) =>
      And (A.val.det = u.val)
        (Exists (fun Psi : Int -> LocallyConstant (Matrix (Fin (n + 1)) (Fin (n + 1)) L)
            Complex =>
          And (forall m, HasCompactSupport (fun X => Psi m X))
            (forall (S : Finset Int) (a : Int -> Complex) (z : Complex),
              let f := fun g : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L) =>
                (norm g.val.det : Complex) ^ z * (Phi g.val * c g)
              let F := fun g : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L) =>
                S.sum (fun m => a m * ((norm g.val.det : Complex) ^ z *
                  (Psi m g.val * c (A ^ m * g))))
              Integrable f mu ->
                And (Integrable F mu)
                  (integral mu F = S.sum (fun m =>
                    a m * ((dedekindPrimeNorm K p : Complex) ^ z) ^ m) * integral mu f))))) := by
  choose A hA using exists_heckeLocalZetaTest_primeNormIntegerTranslate p n mu u hu Phi hPhi c
  have hTrans := hA.2
  choose Psi hPsi using hTrans
  refine Exists.intro A (And.intro hA.1 (Exists.intro Psi (And.intro (fun m => (hPsi m).1) ?_)))
  intro S a z f F hf
  let G := Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L)
  let fShift (m : Int) (g : G) :=
    (norm g.val.det : Complex) ^ z * (Psi m g.val * c (A ^ m * g))
  have hInt (m : Int) : Integrable (fun g => a m * fShift m g) mu :=
    (((hPsi m).2 z).1.mpr hf).const_mul (a m)
  have hF : Integrable F mu := integrable_finsetSum S (fun m _ => hInt m)
  refine And.intro hF ?_
  change integral mu (fun g : G => S.sum (fun m => a m * fShift m g)) =
    S.sum (fun m => a m * ((dedekindPrimeNorm K p : Complex) ^ z) ^ m) * integral mu f
  rw [integral_finsetSum S (fun m _ => hInt m), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_const_mul, show integral mu (fShift m) =
    ((dedekindPrimeNorm K p : Complex) ^ z) ^ m * integral mu f from ((hPsi m).2 z).2, mul_assoc]

/-- A vector fixed near the identity and a dual vector pairing to one give
local zeta tests realizing every Laurent polynomial in the prime-norm
multiplier. The translated matrix coefficients keep the original vector
and use dual vectors in the same translation-stable subspace. Each finite
linear combination is absolutely integrable at every complex exponent. -/
theorem exists_heckeLocalZetaTest_matrixCoefficientLaurentNormalization
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))]
    [BorelSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))]
    (mu : Measure (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))) [mu.IsHaarMeasure]
    (u : Units L) (hu : Valued.v u.val = finiteUniformizerValue)
    (V : Type*) [AddCommGroup V] [Module Complex V]
    (rho : MonoidHom (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L)) (Module.End Complex V))
    (D : Submodule Complex (LinearMap (RingHom.id Complex) V Complex))
    (hStable : forall k : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L),
      forall d : LinearMap (RingHom.id Complex) V Complex,
        Membership.mem D d -> Membership.mem D (d.comp (rho k)))
    (ell : LinearMap (RingHom.id Complex) V Complex) (hell : Membership.mem D ell)
    (vec : V) (hPair : ell vec = 1)
    (hFixed : Filter.Eventually (fun g => rho g vec = vec)
      (nhds (1 : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L)))) :
    Exists (fun Psi : Int -> LocallyConstant (Matrix (Fin (n + 1)) (Fin (n + 1)) L) Complex =>
      Exists (fun ellShift : Int -> LinearMap (RingHom.id Complex) V Complex =>
        And (forall m, And (HasCompactSupport (fun X => Psi m X))
          (Membership.mem D (ellShift m)))
          (forall (S : Finset Int) (a : Int -> Complex) (z : Complex),
            let F := fun g : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L) =>
              S.sum (fun m => a m * ((norm g.val.det : Complex) ^ z *
                (Psi m g.val * ellShift m (rho g vec))))
            And (Integrable F mu)
              (integral mu F = S.sum (fun m =>
                a m * ((dedekindPrimeNorm K p : Complex) ^ z) ^ m))))) := by
  let G := Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L)
  let c (g : G) := ell (rho g vec)
  have hNear : Filter.EventuallyEq (nhds (1 : G)) c (fun _ => 1) :=
    hFixed.mono (fun g hg => by change ell (rho g vec) = 1; rw [hg, hPair])
  choose Phi hPhi using exists_heckeLocalZetaTest_integral_one p (n + 1) mu c hNear
  choose A hA using exists_heckeLocalZetaTest_primeNormLaurentTranslate p n mu u hu Phi hPhi.1 c
  choose Psi hPsi using hA.2
  let ellShift (m : Int) := ell.comp (rho (A ^ m))
  refine Exists.intro Psi (Exists.intro ellShift (And.intro
    (fun m => And.intro (hPsi.1 m) (hStable (A ^ m) ell hell)) ?_))
  intro S a z F
  have hEq (m : Int) (g : G) : c (A ^ m * g) = ellShift m (rho g vec) := by
    change ell (rho (A ^ m * g) vec) = ell (rho (A ^ m) (rho g vec))
    exact congrArg (fun T : Module.End Complex V => ell (T vec)) (map_mul rho (A ^ m) g)
  let f (g : G) := (norm g.val.det : Complex) ^ z * (Phi g.val * c g)
  have hz : And (Integrable f mu) (integral mu f = 1) := by
    simpa only [sub_add_cancel] using
      hPhi.2 (z - ((((n + 1 : Nat) : Real) - 1) / 2 : Real))
  have hSum := hPsi.2 S a z hz.1
  have hUnitIntegral : integral mu (fun g : G =>
      (norm g.val.det : Complex) ^ z * (Phi g.val * c g)) = 1 := hz.2
  rw [hUnitIntegral, mul_one] at hSum
  simpa only [hEq] using hSum

section SmoothDual

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
variable {V : Type*} [AddCommGroup V] [Module Complex V]

local notation "SmoothDualLinearMap" => LinearMap (RingHom.id Complex) V Complex

/-- The smooth dual consists of linear functionals fixed under precomposition
by the action on some neighborhood of the identity. -/
def heckeLocalSmoothDual (rho : MonoidHom G (Module.End Complex V)) :
    Submodule Complex SmoothDualLinearMap where
  carrier := {d | Filter.Eventually (fun g => d.comp (rho g) = d) (nhds (1 : G))}
  zero_mem' := Filter.Eventually.of_forall (fun g => by
    ext x
    rfl)
  add_mem' := fun {a b} ha hb => (ha.and hb).mono (fun g h => by
    ext x
    change a (rho g x) + b (rho g x) = a x + b x
    have ha' : a (rho g x) = a x := DFunLike.congr_fun h.1 x
    have hb' : b (rho g x) = b x := DFunLike.congr_fun h.2 x
    rw [ha', hb'])
  smul_mem' := fun r {d} hd => hd.mono (fun g h => by
    ext x
    exact congrArg (fun value : Complex => r * value) (DFunLike.congr_fun h x))

/-- Precomposition by a group element preserves the smooth dual. -/
theorem heckeLocalSmoothDual_comp_mem
    (rho : MonoidHom G (Module.End Complex V)) (A : G) (d : SmoothDualLinearMap)
    (hd : Membership.mem (heckeLocalSmoothDual rho) d) :
    Membership.mem (heckeLocalSmoothDual rho) (d.comp (rho A)) := by
  change Filter.Eventually (fun g => d.comp (rho g) = d) (nhds (1 : G)) at hd
  change Filter.Eventually (fun g => (d.comp (rho A)).comp (rho g) = d.comp (rho A))
    (nhds (1 : G))
  have hContinuous : Continuous (fun g : G => A * g * Inv.inv A) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hTendsto : Filter.Tendsto (fun g : G => A * g * Inv.inv A)
      (nhds (1 : G)) (nhds (1 : G)) := by
    simpa only [mul_one, mul_inv_cancel] using hContinuous.tendsto (1 : G)
  refine (hTendsto.eventually hd).mono ?_
  intro g hg
  ext x
  change d (rho A (rho g x)) = d (rho A x)
  have hCancel : (A * g * Inv.inv A) * A = A * g := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  calc
    d (rho A (rho g x)) = d (rho (A * g) x) :=
      (congrArg (fun T : Module.End Complex V => d (T x)) (map_mul rho A g)).symm
    _ = d (rho ((A * g * Inv.inv A) * A) x) :=
      congrArg (fun k : G => d (rho k x)) hCancel.symm
    _ = d (rho (A * g * Inv.inv A) (rho A x)) :=
      congrArg (fun T : Module.End Complex V => d (T x))
        (map_mul rho (A * g * Inv.inv A) A)
    _ = d (rho A x) := DFunLike.congr_fun hg (rho A x)

end SmoothDual

section UnitaryDual

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Complex V]

/-- For an inner-product-preserving representation, a nonzero vector fixed
near the identity admits a smooth dual vector pairing to one. -/
theorem exists_heckeLocalSmoothDual_pairing_one
    (rho : MonoidHom G (Module.End Complex V)) (vec : V) (hvec : Not (vec = 0))
    (hUnitary : forall g x y, innerSL Complex (rho g x) (rho g y) = innerSL Complex x y)
    (hFixed : Filter.Eventually (fun g => rho g vec = vec) (nhds (1 : G))) :
    Exists (fun ell : LinearMap (RingHom.id Complex) V Complex =>
      And (Membership.mem (heckeLocalSmoothDual rho) ell) (ell vec = 1)) := by
  let c := innerSL Complex vec vec
  have hC : Not (c = 0) := by
    change Not (innerSL Complex vec vec = 0)
    rw [innerSL_apply_apply]
    exact inner_self_ne_zero.mpr hvec
  let ell := SMul.smul (Inv.inv c) (innerSL Complex vec).toLinearMap
  refine Exists.intro ell (And.intro ?_ ?_)
  next =>
    change Filter.Eventually (fun g => ell.comp (rho g) = ell) (nhds (1 : G))
    refine hFixed.mono ?_
    intro g hg
    ext x
    change Inv.inv c * innerSL Complex vec (rho g x) = Inv.inv c * innerSL Complex vec x
    have h := hUnitary g vec x
    rw [hg] at h
    rw [h]
  next =>
    change Inv.inv c * c = 1
    field_simp [hC]

end UnitaryDual

/-- A nonzero smooth vector in a unitary representation supplies compact
local tests and smooth dual vectors whose integrals realize every Laurent
polynomial in the prime-norm multiplier. The pairing normalization and
absolute convergence hold for every complex exponent. -/
theorem exists_heckeLocalZetaTest_unitaryLaurentNormalization
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))]
    [BorelSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))]
    (mu : Measure (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L))) [mu.IsHaarMeasure]
    (u : Units L) (hu : Valued.v u.val = finiteUniformizerValue)
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Complex V]
    (rho : MonoidHom (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L)) (Module.End Complex V))
    (vec : V) (hvec : Not (vec = 0))
    (hUnitary : forall g x y, innerSL Complex (rho g x) (rho g y) = innerSL Complex x y)
    (hFixed : Filter.Eventually (fun g => rho g vec = vec)
      (nhds (1 : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L)))) :
    Exists (fun Psi : Int -> LocallyConstant (Matrix (Fin (n + 1)) (Fin (n + 1)) L) Complex =>
      Exists (fun ellShift : Int -> LinearMap (RingHom.id Complex) V Complex =>
        And (forall m, And (HasCompactSupport (fun X => Psi m X))
          (Membership.mem (heckeLocalSmoothDual rho) (ellShift m)))
          (forall (S : Finset Int) (a : Int -> Complex) (z : Complex),
            let F := fun g : Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L) =>
              S.sum (fun m => a m * ((norm g.val.det : Complex) ^ z *
                (Psi m g.val * ellShift m (rho g vec))))
            And (Integrable F mu)
              (integral mu F = S.sum (fun m =>
                a m * ((dedekindPrimeNorm K p : Complex) ^ z) ^ m))))) := by
  choose ell hEll using exists_heckeLocalSmoothDual_pairing_one rho vec hvec hUnitary hFixed
  exact exists_heckeLocalZetaTest_matrixCoefficientLaurentNormalization p n mu u hu V rho
    (heckeLocalSmoothDual rho) (heckeLocalSmoothDual_comp_mem rho) ell hEll.1 vec hEll.2 hFixed

/-- The additive valuation index of the determinant of a local matrix unit.
The index of a uniformizer determinant is minus one. -/
def heckeLocalDetValueIndex (n : Nat) (g : Units (Matrix (Fin n) (Fin n) L)) : Int :=
  Multiplicative.toAdd (heckeLocalValueIndex p (Matrix.GeneralLinearGroup.det g))

/-- The determinant valuation index is locally constant on the matrix group. -/
theorem isLocallyConstant_heckeLocalDetValueIndex (n : Nat) :
    IsLocallyConstant (heckeLocalDetValueIndex p n) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro g
  have hn : Not (v g.val.det = 0) :=
    (Valuation.ne_zero_iff v).mpr (g.isUnit.map Matrix.detMonoidHom).ne_zero
  have hDet : Continuous (fun A : Units (Matrix (Fin n) (Fin n) L) => A.val.det) :=
    Units.continuous_val.matrix_det
  refine (hDet.continuousAt.eventually (Valued.locally_const hn)).mono ?_
  intro h hh
  unfold heckeLocalDetValueIndex
  apply congrArg Multiplicative.toAdd
  apply WithZero.coe_inj.mp
  rw [coe_heckeLocalValueIndex, coe_heckeLocalValueIndex]
  exact hh

/-- The determinant norm is the prime norm to the additive valuation index. -/
theorem norm_det_eq_primeNorm_zpow (n : Nat) (g : Units (Matrix (Fin n) (Fin n) L)) :
    norm g.val.det = (dedekindPrimeNorm K p : Real) ^ heckeLocalDetValueIndex p n g := by
  change norm (Matrix.GeneralLinearGroup.det g).val = _
  rw [FinitePlace.norm_def, <- coe_heckeLocalValueIndex,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe]
  change (((Ideal.absNorm p.asIdeal : NNReal) ^ heckeLocalDetValueIndex p n g : NNReal) : Real) = _
  simp [dedekindPrimeNorm]

private theorem norm_det_cpow_eq_primeNorm_zpow (n : Nat)
    (g : Units (Matrix (Fin n) (Fin n) L)) (z : Complex) :
    (norm g.val.det : Complex) ^ z =
      ((dedekindPrimeNorm K p : Complex) ^ z) ^ heckeLocalDetValueIndex p n g := by
  let w := heckeLocalDetValueIndex p n g
  have hArg : ((dedekindPrimeNorm K p : Real) : Complex).arg = 0 :=
    Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)
  have ha : -Real.pi < (w : Real) * ((dedekindPrimeNorm K p : Real) : Complex).arg := by
    rw [hArg, mul_zero]
    exact neg_lt_zero.mpr Real.pi_pos
  have hb : (w : Real) * ((dedekindPrimeNorm K p : Real) : Complex).arg <= Real.pi := by
    rw [hArg, mul_zero]
    exact Real.pi_pos.le
  rw [norm_det_eq_primeNorm_zpow p n g, Complex.ofReal_zpow]
  change ((((dedekindPrimeNorm K p : Real) : Complex) ^ w) ^ z) = _
  rw [<- Complex.cpow_int_mul' ha hb, Complex.cpow_int_mul, Complex.ofReal_natCast]

/-- An integrable coefficient compactly supported in the matrix group meets
finitely many determinant shells. Its weighted integrals are the Laurent
polynomial whose coefficients are the integrals on those shells. -/
theorem integrableAndIntegral_heckeLocalZetaTest_finiteDetShells
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L)))
    (f : Units (Matrix (Fin n) (Fin n) L) -> Complex)
    (hCompact : HasCompactSupport f) (hf : Integrable f mu) :
    Exists (fun S : Finset Int => forall z : Complex,
      let F := fun g : Units (Matrix (Fin n) (Fin n) L) =>
        (norm g.val.det : Complex) ^ z * f g
      And (Integrable F mu)
        (integral mu F = S.sum (fun k =>
          ((dedekindPrimeNorm K p : Complex) ^ z) ^ k *
            integral mu (Set.indicator {g | heckeLocalDetValueIndex p n g = k} f)))) := by
  classical
  let G := Units (Matrix (Fin n) (Fin n) L)
  let w : G -> Int := heckeLocalDetValueIndex p n
  have hw : Continuous w := (isLocallyConstant_heckeLocalDetValueIndex p n).continuous
  have hFinite : Set.Finite (Set.image w (tsupport f)) :=
    (hCompact.image hw).finite_of_discrete
  let S := hFinite.toFinset
  let D (k : Int) : Set G := {g | w g = k}
  have hMeas (k : Int) : MeasurableSet (D k) :=
    measurableSet_eq_fun hw.measurable measurable_const
  have hMem (g : G) (hg : Not (f g = 0)) : Membership.mem S (w g) :=
    hFinite.mem_toFinset.mpr (Set.mem_image_of_mem w
      (subset_closure (show Membership.mem (Function.support f) g from hg)))
  refine Exists.intro S ?_
  intro z F
  let a (k : Int) : Complex := ((dedekindPrimeNorm K p : Complex) ^ z) ^ k
  have hPow (g : G) : (norm g.val.det : Complex) ^ z = a (w g) :=
    norm_det_cpow_eq_primeNorm_zpow p n g z
  have hDecompose : F = fun g : G => S.sum (fun k => a k * Set.indicator (D k) f g) := by
    funext g
    change (norm g.val.det : Complex) ^ z * f g = _
    rw [hPow g]
    by_cases hg : Membership.mem S (w g)
    next =>
      rw [Finset.sum_eq_single_of_mem (w g) hg]
      next => rw [Set.indicator_of_mem (show Membership.mem (D (w g)) g from rfl)]
      next =>
        intro k _ hk
        rw [Set.indicator_of_notMem (show Not (Membership.mem (D k) g) from
            fun hh => hk (Eq.symm hh)), mul_zero]
    next =>
      have hfg : f g = 0 := by
        by_contra h
        exact hg (hMem g h)
      simp [Set.indicator, hfg]
  have hInt (k : Int) : Integrable (fun g => a k * Set.indicator (D k) f g) mu :=
    (hf.indicator (hMeas k)).const_mul (a k)
  refine And.intro (by rw [hDecompose]; exact integrable_finsetSum S (fun k _ => hInt k)) ?_
  rw [hDecompose, integral_finsetSum S (fun k _ => hInt k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul]

/-- A compact local matrix test supported away from singular matrices,
paired with a continuous coefficient, gives an absolutely convergent
Laurent polynomial in the prime-norm multiplier at every exponent. -/
theorem integrableAndIntegral_heckeLocalZetaTest_awayFromSingular
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L))) [IsFiniteMeasureOnCompacts mu]
    (Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (hAway : forall X, Membership.mem (tsupport (fun X => Phi X)) X -> Not (X.det = 0))
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex) (hc : Continuous c) :
    Exists (fun S : Finset Int => forall z : Complex,
      let f := fun g : Units (Matrix (Fin n) (Fin n) L) => Phi g.val * c g
      let F := fun g : Units (Matrix (Fin n) (Fin n) L) =>
        (norm g.val.det : Complex) ^ z * f g
      And (Integrable F mu)
        (integral mu F = S.sum (fun k =>
          ((dedekindPrimeNorm K p : Complex) ^ z) ^ k *
            integral mu (Set.indicator {g | heckeLocalDetValueIndex p n g = k} f)))) := by
  let G := Units (Matrix (Fin n) (Fin n) L)
  let e (g : G) := g.val
  let f (g : G) := Phi g.val * c g
  have hE : IsOpenEmbedding e := isOpenEmbedding_matrixUnitsVal L n
  have hCont : Continuous e := Units.continuous_val
  have hRange (X : Matrix (Fin n) (Fin n) L)
      (hX : Membership.mem (tsupport (fun X => Phi X)) X) :
      Membership.mem (Set.range e) X :=
    Exists.intro (Matrix.GeneralLinearGroup.mkOfDetNeZero X (hAway X hX)) rfl
  let C := Set.preimage e (tsupport (fun X => Phi X))
  have hCompact : IsCompact C := hE.isEmbedding.isInducing.isCompact_preimage' hPhi hRange
  have hClosed : IsClosed C := isClosed_closure.preimage hCont
  have hSub : Set.Subset (Function.support f) C := by
    intro g hg
    apply subset_closure
    intro h
    change Phi g.val = 0 at h
    apply hg
    change Phi g.val * c g = 0
    rw [h, zero_mul]
  have hFComp : HasCompactSupport f :=
    hCompact.of_isClosed_subset isClosed_closure (closure_minimal hSub hClosed)
  have hFCont : Continuous f := (Phi.continuous.comp hCont).mul hc
  exact integrableAndIntegral_heckeLocalZetaTest_finiteDetShells p n mu f hFComp
    (hFCont.integrable_of_hasCompactSupport hFComp)

/-- An absolutely convergent local zeta integral is the absolutely summable
series of its determinant-shell integrals. The unweighted coefficient is
integrable on each shell, independently of the weight at the chosen
complex exponent. -/
theorem hasSum_heckeLocalZetaTest_detShells
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L)))
    (f : Units (Matrix (Fin n) (Fin n) L) -> Complex)
    (z : Complex)
    (hF : Integrable (fun g => (norm g.val.det : Complex) ^ z * f g) mu) :
    let F := fun g : Units (Matrix (Fin n) (Fin n) L) => (norm g.val.det : Complex) ^ z * f g
    let D := fun k : Int => {g : Units (Matrix (Fin n) (Fin n) L) | heckeLocalDetValueIndex p n g = k}
    let b := fun k : Int =>
      ((dedekindPrimeNorm K p : Complex) ^ z) ^ k * integral (mu.restrict (D k)) f
    And (forall k : Int, Integrable f (mu.restrict (D k)))
      (And (Summable (fun k => norm (b k))) (HasSum b (integral mu F))) := by
  intro F D b
  let G := Units (Matrix (Fin n) (Fin n) L)
  let a (k : Int) : Complex := ((dedekindPrimeNorm K p : Complex) ^ z) ^ k
  let w : G -> Int := heckeLocalDetValueIndex p n
  have hw : Continuous w := (isLocallyConstant_heckeLocalDetValueIndex p n).continuous
  have hMeas (k : Int) : MeasurableSet (D k) := measurableSet_eq_fun hw.measurable measurable_const
  have hDisjoint : Pairwise (fun j k => Disjoint (D j) (D k)) := by
    intro j k hjk
    exact Set.disjoint_left.mpr (fun (g : G) hj hk => hjk ((show w g = j from hj).symm.trans hk))
  have hUnion : Set.iUnion D = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    exact Set.mem_iUnion.mpr (Exists.intro (w g) rfl)
  have hEq (k : Int) : Filter.EventuallyEq (ae (mu.restrict (D k))) F (fun g => a k * f g) := by
    refine (ae_restrict_mem (hMeas k)).mono ?_
    intro g hg
    change w g = k at hg
    change (norm g.val.det : Complex) ^ z * f g = a k * f g
    rw [norm_det_cpow_eq_primeNorm_zpow p n g z]
    change a (w g) * f g = a k * f g
    rw [hg]
  have hI (k : Int) : integral (mu.restrict (D k)) F = b k := by
    rw [integral_congr_ae (hEq k), integral_const_mul]
  have hq : Not ((dedekindPrimeNorm K p : Complex) = 0) :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Nat.zero_lt_one.trans (one_lt_dedekindPrimeNorm K p)))
  have hBase : Not ((dedekindPrimeNorm K p : Complex) ^ z = 0) :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  have hLocal (k : Int) : Integrable f (mu.restrict (D k)) := by
    have hn : Not (a k = 0) := zpow_ne_zero k hBase
    have hInv : Filter.EventuallyEq (ae (mu.restrict (D k)))
        (fun g => Inv.inv (a k) * F g) f := by
      refine (hEq k).mono ?_
      intro g hg
      change Inv.inv (a k) * F g = f g
      change F g = a k * f g at hg
      rw [hg]
      field_simp [hn]
    exact (((show Integrable F mu from hF).mono_measure Measure.restrict_le_self).const_mul _).congr hInv
  refine And.intro hLocal ?_
  have hFUnion : IntegrableOn F (Set.iUnion D) mu := by
    rw [hUnion]
    exact (show Integrable F mu from hF).integrableOn
  have hNUnion : IntegrableOn (fun g => norm (F g)) (Set.iUnion D) mu := by
    rw [hUnion]
    exact (show Integrable F mu from hF).norm.integrableOn
  have hSum := hasSum_integral_iUnion hMeas hDisjoint hFUnion
  have hNormSum := hasSum_integral_iUnion hMeas hDisjoint hNUnion
  have hAbs : Summable (fun k => norm (integral (mu.restrict (D k)) F)) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
      hNormSum.summable
  refine And.intro ?_ ?_
  next => simpa only [hI] using hAbs
  next => simpa only [hI, hUnion, Measure.restrict_univ] using hSum

/-- For a compactly supported matrix test, the unweighted shell coefficients
vanish above one finite determinant valuation index. Thus the infinite
tail of the shell series runs toward determinant zero. -/
theorem exists_heckeLocalZetaTest_detShellsSupportBound
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L)))
    (Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex) :
    Exists (fun N : Nat => forall k : Int, (N : Int) < k ->
      integral (mu.restrict {g | heckeLocalDetValueIndex p n g = k})
        (fun g => Phi g.val * c g) = 0) := by
  let M := Matrix (Fin n) (Fin n) L
  let G := Units M
  let w : G -> Int := heckeLocalDetValueIndex p n
  let q : Real := dedekindPrimeNorm K p
  have hQ : 1 < q := by
    change (1 : Real) < (dedekindPrimeNorm K p : Real)
    exact_mod_cast one_lt_dedekindPrimeNorm K p
  have hDet : Continuous (fun X : M => X.det) := continuous_id.matrix_det
  choose C hC using hPhi.exists_bound_of_continuousOn hDet.continuousOn
  have hPowers : Filter.Tendsto (fun m : Nat => q ^ m) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hQ
  have hEventually : Filter.Eventually (fun m : Nat => C < q ^ m) Filter.atTop :=
    hPowers.eventually (Filter.eventually_gt_atTop C)
  choose N hN using Filter.eventually_atTop.mp hEventually
  have hw : Continuous w := (isLocallyConstant_heckeLocalDetValueIndex p n).continuous
  refine Exists.intro N ?_
  intro k hk
  let D : Set G := {g | w g = k}
  have hMeas : MeasurableSet D := measurableSet_eq_fun hw.measurable measurable_const
  have heq : Filter.EventuallyEq (ae (mu.restrict D)) (fun g : G => Phi g.val * c g)
      (fun _ => 0) := by
    refine (ae_restrict_mem hMeas).mono ?_
    intro g hg
    change w g = k at hg
    have hIndex : (N : Int) < w g := by rw [hg]; exact hk
    have hNonneg : 0 <= w g := le_trans (Int.natCast_nonneg N) hIndex.le
    have hNInt : (N : Int) <= (Int.toNat (w g) : Int) := by
      rw [Int.toNat_of_nonneg hNonneg]
      exact hIndex.le
    have hNN : N <= Int.toNat (w g) := by exact_mod_cast hNInt
    have hLarge : C < q ^ Int.toNat (w g) := hN _ hNN
    have hNorm : norm g.val.det = q ^ Int.toNat (w g) := calc
      _ = q ^ w g := norm_det_eq_primeNorm_zpow p n g
      _ = q ^ (Int.toNat (w g) : Int) :=
        congrArg (fun m : Int => q ^ m) (Int.toNat_of_nonneg hNonneg).symm
      _ = q ^ Int.toNat (w g) := zpow_natCast q _
    have hZero : Phi g.val = 0 := by
      by_contra h
      have hSmall := hC g.val (subset_closure
        (show Membership.mem (Function.support (fun X => Phi X)) g.val from h))
      rw [hNorm] at hSmall
      exact (not_lt_of_ge hSmall) hLarge
    change Phi g.val * c g = 0
    rw [hZero, zero_mul]
  change integral (mu.restrict D) (fun g : G => Phi g.val * c g) = 0
  rw [integral_congr_ae heq]
  simp

/-- Removing the matrices with determinant norm below a positive cutoff
leaves a finite Laurent polynomial. The remaining test is exactly the
original test restricted to that strict sublevel set. Wherever the
original integral converges absolutely, the two contributions add to it. -/
theorem exists_heckeLocalZetaTest_singularTail
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L))) [IsFiniteMeasureOnCompacts mu]
    (Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex) (hc : Continuous c)
    (r : Real) (hr : 0 < r) :
    Exists (fun near : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex =>
      Exists (fun S : Finset Int => Exists (fun a : Int -> Complex =>
        And (HasCompactSupport (fun X => near X))
          (And (forall X, near X = Set.indicator {Y | norm Y.det < r} (fun Y => Phi Y) X)
            (forall z : Complex,
              let F := fun g : Units (Matrix (Fin n) (Fin n) L) =>
                (norm g.val.det : Complex) ^ z * (Phi g.val * c g)
              let T := fun g : Units (Matrix (Fin n) (Fin n) L) =>
                (norm g.val.det : Complex) ^ z * (near g.val * c g)
              Integrable F mu -> And (Integrable T mu)
                (integral mu F = S.sum (fun k =>
                  a k * ((dedekindPrimeNorm K p : Complex) ^ z) ^ k) + integral mu T)))))) := by
  classical
  let M := Matrix (Fin n) (Fin n) L
  let G := Units M
  let D : Set M := {X | r <= norm X.det}
  have hDet : Continuous (fun X : M => X.det) := continuous_id.matrix_det
  have hClosed : IsClosed D := isClosed_le continuous_const hDet.norm
  have hOpen : IsOpen D := by
    apply isOpen_iff_mem_nhds.mpr
    intro X hX
    change r <= norm X.det at hX
    have hNe : Not (X.det = 0) := by
      intro h
      rw [h, norm_zero] at hX
      exact (not_le_of_gt hr) hX
    have hValNe : Not (v X.det = 0) := (Valuation.ne_zero_iff v).mpr hNe
    change Filter.Eventually (fun Y : M => r <= norm Y.det) (nhds X)
    refine (hDet.continuousAt.eventually (Valued.locally_const hValNe)).mono ?_
    intro Y hY
    have hNorm : norm Y.det = norm X.det := by
      rw [FinitePlace.norm_def, FinitePlace.norm_def, hY]
    rw [hNorm]
    exact hX
  let hD : IsClopen D := And.intro hClosed hOpen
  let high := Phi.indicator hD
  let near := Phi.indicator hD.compl
  have hCutSupport (U : Set M) (hU : IsClopen U) :
      Set.Subset (tsupport (fun X => Phi.indicator hU X))
        (Set.inter U (tsupport (fun X => Phi X))) := by
    apply closure_minimal ?_ (hU.isClosed.inter isClosed_closure)
    intro X hX
    change Not (Set.indicator U (fun X => Phi X) X = 0) at hX
    by_cases h : Membership.mem U X
    next =>
      rw [Set.indicator_of_mem h] at hX
      exact And.intro h (subset_closure hX)
    next =>
      rw [Set.indicator_of_notMem h] at hX
      exact (hX rfl).elim
  have hHigh : HasCompactSupport (fun X => high X) :=
    hPhi.of_isClosed_subset isClosed_closure (fun X h => (hCutSupport D hD h).2)
  have hNear : HasCompactSupport (fun X => near X) :=
    hPhi.of_isClosed_subset isClosed_closure (fun X h => (hCutSupport (Set.compl D) hD.compl h).2)
  have hAway (X : M) (hX : Membership.mem (tsupport (fun X => high X)) X) :
      Not (X.det = 0) := by
    have hNorm : r <= norm X.det := (hCutSupport D hD hX).1
    intro h
    rw [h, norm_zero] at hNorm
    exact (not_le_of_gt hr) hNorm
  choose S hS using integrableAndIntegral_heckeLocalZetaTest_awayFromSingular
    p n mu high hHigh hAway c hc
  let a (k : Int) := integral mu
    (Set.indicator {g : G | heckeLocalDetValueIndex p n g = k} (fun g => high g.val * c g))
  refine Exists.intro near (Exists.intro S (Exists.intro a (And.intro hNear ?_)))
  have hNearEq (X : M) :
      near X = Set.indicator {Y : M | norm Y.det < r} (fun Y => Phi Y) X := by
    change Set.indicator (Set.compl D) (fun Y => Phi Y) X = _
    rw [show Set.compl D = {Y : M | norm Y.det < r} from Set.ext (fun Y => show Not (r <= norm Y.det) <-> norm Y.det < r from not_le)]
  refine And.intro hNearEq ?_
  intro z F T hF
  let H (g : G) := (norm g.val.det : Complex) ^ z * (high g.val * c g)
  have hSplit (X : M) : Phi X = high X + near X := by
    change Phi X = Set.indicator D (fun Y => Phi Y) X +
      Set.indicator (Set.compl D) (fun Y => Phi Y) X
    by_cases h : Membership.mem D X
    next =>
      have hn : Not (Membership.mem (Set.compl D) X) := fun hu => hu h
      rw [Set.indicator_of_mem h, Set.indicator_of_notMem hn, add_zero]
    next =>
      rw [Set.indicator_of_notMem h,
        Set.indicator_of_mem (show Membership.mem (Set.compl D) X from h), zero_add]
  have hParts : F = fun g : G => H g + T g := by
    funext g
    change (norm g.val.det : Complex) ^ z * (Phi g.val * c g) =
      (norm g.val.det : Complex) ^ z * (high g.val * c g) +
        (norm g.val.det : Complex) ^ z * (near g.val * c g)
    rw [hSplit g.val, add_mul, mul_add]
  have hH : Integrable H mu := (hS z).1
  have hT : Integrable T mu := by
    have hSub : T = fun g : G => F g - H g := by
      funext g
      rw [congrFun hParts g]
      abel
    rw [hSub]
    exact hF.sub hH
  refine And.intro hT ?_
  have hI : integral mu H =
      S.sum (fun k => ((dedekindPrimeNorm K p : Complex) ^ z) ^ k * a k) := (hS z).2
  rw [hParts, integral_add hH hT, hI]
  simp only [mul_comm]

/-- If left translation by a matrix acts on the coefficient by a nonzero
scalar, subtracting the translated test removes the contribution near the
zero matrix. The new integral is the original integral multiplied by the
difference between one and the inverse scalar times the determinant weight. -/
theorem exists_heckeLocalZetaTest_originCancellation
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [MeasurableMul (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L))) [mu.IsMulLeftInvariant]
    (A : Units (Matrix (Fin n) (Fin n) L))
    (Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex)
    (lambda : Complex) (hLambda : Not (lambda = 0))
    (hc : forall g, c (A * g) = lambda * c g) :
    Exists (fun Delta : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex =>
      And (HasCompactSupport (fun X => Delta X))
        (And (forall X, Delta X = Phi X - Phi (A.val * X))
          (And (Filter.EventuallyEq (nhds (0 : Matrix (Fin n) (Fin n) L)) Delta (fun _ => 0))
          (forall z : Complex,
            let F := fun g : Units (Matrix (Fin n) (Fin n) L) =>
              (norm g.val.det : Complex) ^ z * (Phi g.val * c g)
            let D := fun g : Units (Matrix (Fin n) (Fin n) L) =>
              (norm g.val.det : Complex) ^ z * (Delta g.val * c g)
            Integrable F mu -> And (Integrable D mu)
              (integral mu D = (1 - Inv.inv lambda * (norm A.val.det : Complex) ^ (-z)) *
                integral mu F))))) := by
  let M := Matrix (Fin n) (Fin n) L
  let G := Units M
  choose Psi hPsi using exists_heckeLocalZetaTest_leftTranslate_exact p n mu A Phi hPhi c
  let Delta := Phi - Psi
  have hDelta : HasCompactSupport (fun X => Delta X) := hPhi.sub hPsi.1
  have hZero : Psi (0 : M) = Phi 0 := by rw [hPsi.2.1, mul_zero]
  have hNear : Filter.EventuallyEq (nhds (0 : M)) Delta (fun _ => 0) := by
    refine ((Phi.2.eventually_eq 0).and (Psi.2.eventually_eq 0)).mono ?_
    intro X hX
    change Phi X - Psi X = 0
    have hPhiX : Phi X = Phi 0 := hX.1
    have hPsiX : Psi X = Psi 0 := hX.2
    rw [hPhiX, hPsiX, hZero, sub_self]
  have hDifference (X : M) : Delta X = Phi X - Phi (A.val * X) := by
    change Phi X - Psi X = _
    rw [hPsi.2.1]
  refine Exists.intro Delta (And.intro hDelta (And.intro hDifference (And.intro hNear ?_)))
  intro z F D hF
  let T (g : G) := (norm g.val.det : Complex) ^ z * (Psi g.val * c (A * g))
  let H (g : G) := (norm g.val.det : Complex) ^ z * (Psi g.val * c g)
  have hTH (g : G) : T g = lambda * H g := by
    dsimp [T, H]
    rw [hc]
    ring
  have hHT : H = fun g : G => Inv.inv lambda * T g := by
    funext g
    rw [hTH]
    field_simp [hLambda]
  have hTI : Integrable T mu := ((hPsi.2.2 z).1).mpr hF
  have hHI : Integrable H mu := by
    rw [hHT]
    exact hTI.const_mul _
  have hDiff : D = fun g : G => F g - H g := by
    funext g
    change (norm g.val.det : Complex) ^ z * ((Phi g.val - Psi g.val) * c g) =
      (norm g.val.det : Complex) ^ z * (Phi g.val * c g) -
        (norm g.val.det : Complex) ^ z * (Psi g.val * c g)
    ring
  have hTV : integral mu T = (norm A.val.det : Complex) ^ (-z) * integral mu F :=
    (hPsi.2.2 z).2
  refine And.intro (by rw [hDiff]; exact hF.sub hHI) ?_
  rw [hDiff, integral_sub hF hHI, hHT, integral_const_mul, hTV]
  ring

/-- For scalar uniformizer translation, the test difference vanishes near
the zero matrix and its zeta integral is the original integral multiplied
by one minus the scalar-character value times the prime-norm weight. -/
theorem exists_heckeLocalZetaTest_scalarUniformizerCancellation
    (n : Nat) [MeasurableSpace (Units (Matrix (Fin n) (Fin n) L))]
    [MeasurableMul (Units (Matrix (Fin n) (Fin n) L))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) L))) [mu.IsMulLeftInvariant]
    (u : Units L) (hu : Valued.v u.val = finiteUniformizerValue)
    (Phi : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin n) (Fin n) L) -> Complex)
    (lambda : Units Complex)
    (hc : forall g, c (Matrix.GeneralLinearGroup.scalar (Fin n) u * g) = lambda.val * c g) :
    Exists (fun Delta : LocallyConstant (Matrix (Fin n) (Fin n) L) Complex =>
      And (HasCompactSupport (fun X => Delta X))
        (And (forall X, Delta X =
          Phi X - Phi ((Matrix.GeneralLinearGroup.scalar (Fin n) (Inv.inv u)).val * X))
          (And (Filter.EventuallyEq (nhds (0 : Matrix (Fin n) (Fin n) L)) Delta (fun _ => 0))
          (forall z : Complex,
            let F := fun g : Units (Matrix (Fin n) (Fin n) L) =>
              (norm g.val.det : Complex) ^ z * (Phi g.val * c g)
            let D := fun g : Units (Matrix (Fin n) (Fin n) L) =>
              (norm g.val.det : Complex) ^ z * (Delta g.val * c g)
            Integrable F mu -> And (Integrable D mu)
              (integral mu D = (1 - lambda.val *
                ((dedekindPrimeNorm K p : Complex) ^ (-z)) ^ n) * integral mu F))))) := by
  let G := Units (Matrix (Fin n) (Fin n) L)
  let B : G := Matrix.GeneralLinearGroup.scalar (Fin n) u
  let A : G := Matrix.GeneralLinearGroup.scalar (Fin n) (Inv.inv u)
  have hAdjust (g : G) : c (A * g) = (Inv.inv lambda).val * c g := by
    have hBA : B * A = 1 := by
      change Matrix.GeneralLinearGroup.scalar (Fin n) u *
        Matrix.GeneralLinearGroup.scalar (Fin n) (Inv.inv u) = 1
      rw [<- map_mul, mul_inv_cancel, map_one]
    have h := hc (A * g)
    change c (B * (A * g)) = lambda.val * c (A * g) at h
    rw [<- mul_assoc, hBA, one_mul] at h
    rw [Units.val_inv_eq_inv_val, h]
    field_simp [lambda.ne_zero]
  choose Delta hDelta using exists_heckeLocalZetaTest_originCancellation
    p n mu A Phi hPhi c (Inv.inv lambda).val (Inv.inv lambda).ne_zero hAdjust
  have hNorm : norm A.val.det = (dedekindPrimeNorm K p : Real) ^ n := by
    change norm (Matrix.GeneralLinearGroup.det A).val = _
    dsimp only [A]
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val, norm_pow,
      Units.val_inv_eq_inv_val, norm_inv, norm_eq_inv_of_valuation_finiteUniformizer p u.val hu,
      inv_inv]
  have hArg : ((dedekindPrimeNorm K p : Real) : Complex).arg = 0 :=
    Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)
  have hPow (z : Complex) : (norm A.val.det : Complex) ^ (-z) =
      ((dedekindPrimeNorm K p : Complex) ^ (-z)) ^ n := by
    have hLower : -Real.pi < (n : Real) * ((dedekindPrimeNorm K p : Real) : Complex).arg := by
      simpa only [hArg, mul_zero] using neg_lt_zero.mpr Real.pi_pos
    have hUpper : (n : Real) * ((dedekindPrimeNorm K p : Real) : Complex).arg <= Real.pi := by
      simpa only [hArg, mul_zero] using Real.pi_pos.le
    rw [hNorm, Complex.ofReal_pow, <- Complex.cpow_nat_mul' hLower hUpper, Complex.cpow_nat_mul,
      Complex.ofReal_natCast]
  refine Exists.intro Delta (And.intro hDelta.1 (And.intro hDelta.2.1 (And.intro hDelta.2.2.1 ?_)))
  intro z F D hF
  have h := hDelta.2.2.2 z hF
  refine And.intro h.1 ?_
  have hValue : integral mu D =
      (1 - Inv.inv (Inv.inv lambda).val * (norm A.val.det : Complex) ^ (-z)) * integral mu F := h.2
  rw [hValue, Units.val_inv_eq_inv_val, inv_inv, hPow]

/-- In rank one the origin is the whole singular locus. Clearing the
scalar-uniformizer factor gives a finite Laurent polynomial numerator
for the local zeta integral on its domain of absolute convergence. -/
theorem exists_heckeLocalZetaTest_rankOneLaurentNumerator
    [MeasurableSpace (Units (Matrix (Fin 1) (Fin 1) L))]
    [BorelSpace (Units (Matrix (Fin 1) (Fin 1) L))]
    (mu : Measure (Units (Matrix (Fin 1) (Fin 1) L))) [mu.IsHaarMeasure]
    (u : Units L) (hu : Valued.v u.val = finiteUniformizerValue)
    (Phi : LocallyConstant (Matrix (Fin 1) (Fin 1) L) Complex)
    (hPhi : HasCompactSupport (fun X => Phi X))
    (c : Units (Matrix (Fin 1) (Fin 1) L) -> Complex) (hC : Continuous c)
    (lambda : Units Complex)
    (hc : forall g, c (Matrix.GeneralLinearGroup.scalar (Fin 1) u * g) = lambda.val * c g) :
    Exists (fun S : Finset Int => Exists (fun a : Int -> Complex =>
      forall z : Complex,
        let F := fun g : Units (Matrix (Fin 1) (Fin 1) L) =>
          (norm g.val.det : Complex) ^ z * (Phi g.val * c g)
        Integrable F mu ->
          (1 - lambda.val * (dedekindPrimeNorm K p : Complex) ^ (-z)) * integral mu F =
            S.sum (fun k => ((dedekindPrimeNorm K p : Complex) ^ z) ^ k * a k))) := by
  let M := Matrix (Fin 1) (Fin 1) L
  let G := Units M
  choose Delta hDelta using exists_heckeLocalZetaTest_scalarUniformizerCancellation
    p 1 mu u hu Phi hPhi c lambda hc
  have hAvoid (X : M) (hX : Membership.mem (tsupport (fun Y => Delta Y)) X) :
      Not (X.det = 0) := by
    intro hDet
    have hZero : X = 0 := by
      apply Matrix.ext
      intro i j
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      change X i j = 0
      have hEntry : X 0 0 = 0 := (Matrix.det_fin_one X).symm.trans hDet
      rw [hi, hj, hEntry]
    have h0 : Not (Membership.mem (tsupport (fun Y => Delta Y)) (0 : M)) :=
      notMem_tsupport_iff_eventuallyEq.mpr hDelta.2.2.1
    exact h0 (by rw [<- hZero]; exact hX)
  choose S hS using integrableAndIntegral_heckeLocalZetaTest_awayFromSingular p 1 mu
    Delta hDelta.1 hAvoid c hC
  let a (k : Int) := integral mu
    (Set.indicator {g : G | heckeLocalDetValueIndex p 1 g = k} (fun g => Delta g.val * c g))
  refine Exists.intro S (Exists.intro a ?_)
  intro z F hF
  let D (g : G) := (norm g.val.det : Complex) ^ z * (Delta g.val * c g)
  have hCanc : integral mu D =
      (1 - lambda.val * ((dedekindPrimeNorm K p : Complex) ^ (-z)) ^ (1 : Nat)) *
        integral mu F := (hDelta.2.2.2 z hF).2
  rw [pow_one] at hCanc
  exact hCanc.symm.trans (hS z).2

end LocalUnitZetaTest

section FiniteAdelicEulerProduct

open MeasureTheory MeasureTheory.Measure

section

variable {K : Type*} [Field K] [NumberField K]
variable (p : HeightOneSpectrum (RingOfIntegers K))

local notation "L" => p.adicCompletion K
local notation "v" => (Valued.v : Valuation L (WithZero (Multiplicative Int)))

private theorem finiteLocalMatrixUnitSubgroup_eq_valuationIntegralMatrixSubgroup (n : Nat) :
    finiteLocalMatrixUnitSubgroup K n p = valuationIntegralMatrixSubgroup v n := by
  ext g
  rw [mem_valuationIntegralMatrixSubgroup_iff v n g]
  change (And
    (forall i j : Fin n, Membership.mem (p.adicCompletionIntegers K) (g.val i j))
    (forall i j : Fin n, Membership.mem (p.adicCompletionIntegers K) (g.inv i j))) <-> _
  rfl

end

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K

private abbrev localValuedIntegralMatrixSubgroup (n : Nat) (p : P) :=
  valuationIntegralMatrixSubgroup
    (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) n

/-- The finite adelic zeta integral factors into the prescribed local
integrals when the local zeta function is spherical outside a fixed finite
set. The local norm integrals on that set contribute only a finite factor
to the absolute convergence bound. -/
theorem integrableAndHasProd_finiteAdeleSphericalZetaIntegralWithRamifiedPlaces
    (n : Nat) (E : Finset P) [Countable P] [(Filter.atTop : Filter (Finset P)).IsCountablyGenerated]
    [forall S : Finset P, Fintype (S : Set P)]
    [MeasurableSpace FA] [BorelSpace FA]
    [forall p : P, MeasurableSpace (p.adicCompletion K)]
    [forall p : P, BorelSpace (p.adicCompletion K)]
    [forall p : P, MeasurableSpace (Units (p.adicCompletion K))]
    [forall p : P, BorelSpace (Units (p.adicCompletion K))]
    [forall p : P, SigmaFinite (heckeLocalHaar p)]
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [forall p : P, MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [forall p : P, BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [forall p : P, MeasurableSpace (localValuedIntegralMatrixSubgroup K n p)]
    [forall p : P, BorelSpace (localValuedIntegralMatrixSubgroup K n p)]
    [forall S : Finset P, MeasurableSpace ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val)]
    [forall S : Finset P, BorelSpace (FiniteAdeleMatrixHaarChart K n S)]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) FA)))
    (localHaar : forall p : P, Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    [forall p, (localHaar p).IsMulLeftInvariant] [forall p, SigmaFinite (localHaar p)]
    (hLocalMass : forall p, localHaar p (finiteLocalMatrixUnitSubgroup K n p :
      Set (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))) = 1)
    (tailHaar : forall S : Finset P, Measure ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val))
    [forall S, IsProbabilityMeasure (tailHaar S)]
    (hMeasure : forall S : Finset P, mu.comap (finiteAdeleMatrixHaarChartEmbedding K n S) =
      (Measure.pi (fun p : (S : Set P) => localHaar p.val)).prod (tailHaar S))
    (nu : forall p : P, Measure (localValuedIntegralMatrixSubgroup K n p))
    [forall p, IsProbabilityMeasure (nu p)]
    (u0 : forall p : P, Units (p.adicCompletion K))
    (hu0 : forall p, Not (Membership.mem E p) -> Valued.v (u0 p).val = finiteUniformizerValue)
    (chi : forall p : P, Fin n -> MonoidHom (Units (p.adicCompletion K)) Complex)
    (hUnit : forall p, Not (Membership.mem E p) -> forall i x,
      Membership.mem (heckeLocalUnitShell p) x -> chi p i x = 1)
    (s : Complex) (hs : ((n : Real) + 1) / 2 < s.re)
    (hSpherical : forall p, Not (Membership.mem E p) -> Filter.Eventually
      (fun g => norm (heckeUnramifiedSphericalCoefficient p n (nu p)
        (productDiagonalCharacter n (chi p)) g) <= 1) (ae (localHaar p)))
    (hWeighted : forall p, Not (Membership.mem E p) -> forall i, norm (chi p i (u0 p) *
      (dedekindPrimeNorm K p : Complex) ^ (-s)) < 1)
    (f : forall p : P, Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)) -> Complex)
    (a : P -> Complex)
    (hZeta : forall p, Not (Membership.mem E p) ->
      f p = heckeUnramifiedLocalZetaIntegrand p n (nu p) (chi p) s)
    (hEuler : forall p, Not (Membership.mem E p) -> a p = Finset.univ.prod (fun i : Fin n =>
      Inv.inv (1 - chi p i (u0 p) * (dedekindPrimeNorm K p : Complex) ^ (-s))))
    (hRamified : forall p, Membership.mem E p ->
      And (Integrable (f p) (localHaar p)) (integral (localHaar p) (f p) = a p)) :
    let F := finiteAdeleMatrixRestrictedZetaIntegrand K n f
    And (Integrable F mu) (HasProd a (integral mu F)) := by
  classical
  have hOne (p : P) (hp : Not (Membership.mem E p))
      (g : Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))
      (hg : Membership.mem (finiteLocalMatrixUnitSubgroup K n p) g) : f p g = 1 := by
    rw [hZeta p hp]
    apply heckeUnramifiedLocalZetaIntegrand_eq_one_of_mem_integral
      p n (nu p) (chi p) (hUnit p hp) s g
    rw [<- finiteLocalMatrixUnitSubgroup_eq_valuationIntegralMatrixSubgroup p n]
    exact hg
  have hMass (p : P) : localHaar p
      (localValuedIntegralMatrixSubgroup K n p :
        Set (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))) = 1 := by
    rw [show localValuedIntegralMatrixSubgroup K n p = finiteLocalMatrixUnitSubgroup K n p from
      (finiteLocalMatrixUnitSubgroup_eq_valuationIntegralMatrixSubgroup p n).symm]
    exact hLocalMass p
  have hLocal (p : P) : And (Integrable (f p) (localHaar p))
      (integral (localHaar p) (f p) = a p) := by
    by_cases hp : Membership.mem E p
    next => exact hRamified p hp
    next =>
      rw [hZeta p hp, hEuler p hp]
      exact integrableAndIntegral_heckeUnramifiedSphericalCoefficient_primeNorm p n (u0 p) (hu0 p hp)
        (localHaar p) (hMass p) (nu p) (chi p) (hUnit p hp) s (hWeighted p hp)
  let r (p : P) : Real := integral (localHaar p) (fun g => norm (f p g))
  have hr (p : P) : 0 <= r p := integral_nonneg (fun g => norm_nonneg (f p g))
  have hAbsolute (p : P) (hp : Not (Membership.mem E p)) :
      r p <= unramifiedLocalAbsoluteEulerFactor p n s.re := by
    have hInt := (hLocal p).1
    rw [hZeta p hp] at hInt
    dsimp [r]
    rw [hZeta p hp]
    exact (integrableAndAbsoluteIntegral_le_unramifiedLocalWeight p n (u0 p) (hu0 p hp)
      (localHaar p) (hMass p) s hs _ (hSpherical p hp) hInt.aestronglyMeasurable).2
  let C := Finset.univ.prod (fun i : Fin n =>
    (dedekindZeta K ((s.re - (((n : Real) - 1) / 2 - (i.val : Real)) : Real) : Complex)).re)
  have hBound (S : Finset P) (hES : E <= S) : S.prod r <= (E.prod r) * C := by
    have hOutside : (SDiff.sdiff S E).prod r <= C := by
      refine le_trans ?_ (prod_unramifiedLocalAbsoluteEulerFactor_le (K := K) n s.re hs
        (SDiff.sdiff S E))
      exact Finset.prod_le_prod (fun p _ => hr p)
        (fun p hp => hAbsolute p (Finset.mem_sdiff.mp hp).2)
    calc
      S.prod r = ((SDiff.sdiff S E).prod r) * E.prod r := (Finset.prod_sdiff hES).symm
      _ <= C * E.prod r := mul_le_mul_of_nonneg_right hOutside (Finset.prod_nonneg (fun p _ => hr p))
      _ = E.prod r * C := mul_comm _ _
  have hGlobal := integrableAndHasProd_finiteAdeleMatrixRestrictedZetaIntegrand_withExceptions K n E
    mu localHaar tailHaar hMeasure f hOne (fun p => (hLocal p).1) (E.prod r * C) hBound
  refine And.intro hGlobal.1 ?_
  rw [<- funext (fun p => (hLocal p).2)]
  exact hGlobal.2

/-- With normalized chart measures, the finite adelic integral of the
unramified spherical zeta integrand is absolutely convergent and is the
Euler product of its prime-norm factors. The local spherical coefficients
are bounded in norm by one, and each local geometric integral converges. -/
theorem integrableAndHasProd_finiteAdeleUnramifiedSphericalZetaIntegral
    (n : Nat) [Countable P] [(Filter.atTop : Filter (Finset P)).IsCountablyGenerated]
    [forall S : Finset P, Fintype (S : Set P)]
    [MeasurableSpace FA] [BorelSpace FA]
    [forall p : P, MeasurableSpace (p.adicCompletion K)]
    [forall p : P, BorelSpace (p.adicCompletion K)]
    [forall p : P, MeasurableSpace (Units (p.adicCompletion K))]
    [forall p : P, BorelSpace (Units (p.adicCompletion K))]
    [forall p : P, SigmaFinite (heckeLocalHaar p)]
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [forall p : P, MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [forall p : P, BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [forall p : P, MeasurableSpace (localValuedIntegralMatrixSubgroup K n p)]
    [forall p : P, BorelSpace (localValuedIntegralMatrixSubgroup K n p)]
    [forall S : Finset P, MeasurableSpace ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val)]
    [forall S : Finset P, BorelSpace (FiniteAdeleMatrixHaarChart K n S)]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) FA)))
    (localHaar : forall p : P, Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    [forall p, (localHaar p).IsMulLeftInvariant] [forall p, SigmaFinite (localHaar p)]
    (hLocalMass : forall p, localHaar p (finiteLocalMatrixUnitSubgroup K n p :
      Set (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))) = 1)
    (tailHaar : forall S : Finset P, Measure ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val))
    [forall S, IsProbabilityMeasure (tailHaar S)]
    (hMeasure : forall S : Finset P, mu.comap (finiteAdeleMatrixHaarChartEmbedding K n S) =
      (Measure.pi (fun p : (S : Set P) => localHaar p.val)).prod (tailHaar S))
    (nu : forall p : P, Measure (localValuedIntegralMatrixSubgroup K n p))
    [forall p, IsProbabilityMeasure (nu p)]
    (u0 : forall p : P, Units (p.adicCompletion K))
    (hu0 : forall p, Valued.v (u0 p).val = finiteUniformizerValue)
    (chi : forall p : P, Fin n -> MonoidHom (Units (p.adicCompletion K)) Complex)
    (hUnit : forall p i x, Membership.mem (heckeLocalUnitShell p) x -> chi p i x = 1)
    (s : Complex) (hs : ((n : Real) + 1) / 2 < s.re)
    (hSpherical : forall p, Filter.Eventually
      (fun g => norm (heckeUnramifiedSphericalCoefficient p n (nu p)
        (productDiagonalCharacter n (chi p)) g) <= 1) (ae (localHaar p)))
    (hWeighted : forall p i, norm (chi p i (u0 p) *
      (dedekindPrimeNorm K p : Complex) ^ (-s)) < 1) :
    let F := finiteAdeleMatrixRestrictedZetaIntegrand K n
      (fun p => heckeUnramifiedLocalZetaIntegrand p n (nu p) (chi p) s)
    And (Integrable F mu) (HasProd (fun p : P => Finset.univ.prod (fun i : Fin n =>
      Inv.inv (1 - chi p i (u0 p) * (dedekindPrimeNorm K p : Complex) ^ (-s)))) (integral mu F)) := by
  refine integrableAndHasProd_finiteAdeleSphericalZetaIntegralWithRamifiedPlaces
    K n EmptyCollection.emptyCollection mu localHaar hLocalMass tailHaar hMeasure nu u0
    (fun p _ => hu0 p) chi (fun p _ => hUnit p) s hs
    (fun p _ => hSpherical p) (fun p _ => hWeighted p) _ _
    (fun _ _ => rfl) (fun _ _ => rfl) ?_
  intro p hp
  simp at hp

end FiniteAdelicEulerProduct

end Robin1984.GRH
