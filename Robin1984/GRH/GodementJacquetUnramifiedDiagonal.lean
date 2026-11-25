import Mathlib.Algebra.Group.Pi.Units
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.Group.Units
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
  have hChiDiag (a : A) (ha : Membership.mem (valuationDiagonalIntegralSubgroup L n v) a) :
      productDiagonalCharacter n chi a = 1 := by
    have hLocal := (mem_heckeDiagonalIntegral_iff_localUnitShell p n a).mp ha
    change Finset.univ.prod (fun i : Fin n => chi i (MulEquiv.piUnits a i)) = 1
    have h1 (i : Fin n) : chi i (MulEquiv.piUnits a i) = 1 := hUnit i _ (hLocal i)
    simp only [h1, Finset.prod_const_one]
  have hInducing (b : B) (hb : Membership.mem (valuationIntegralMatrixSubgroup v n) b.val) :
      valuationNormalizedInducingCharacter L n (productDiagonalCharacter n chi) b = 1 :=
    valuationNormalizedInducingCharacter_eq_one L v (heckeLocal_mem_integers_iff_norm_le_one p)
      n _ hChiDiag b hb
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

end ActualHaar

end Robin1984.GRH
