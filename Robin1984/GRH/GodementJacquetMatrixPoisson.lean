import Mathlib.MeasureTheory.Integral.Pi
import Robin1984.GRH.GodementJacquetFourier
import Robin1984.GRH.GodementJacquetVectorPoisson

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Poisson summation on the additive adelic matrix space in Godement and Jacquet, Zeta Functions of Simple Algebras.
- Formalization note: Identifies the Fourier coefficients for Schwartz rectangles with the actual adelic trace-pairing integral and proves Poisson summation on rational matrices.
- PROVENANCE-END
-/

/-!
# Poisson summation on adelic matrices

The matrix trace pairs each entry with the transposed frequency entry.
The Fourier integral of a Schwartz rectangle splits into the
archimedean Fourier integral and the finite character integrals.
The self-dual normalization contributes one inverse square root of the
absolute discriminant for each matrix entry.

These integral identities transport the vector Poisson formula to the
sum over rational matrices, allowing the archimedean Schwartz function
to depend jointly on all matrix entries.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical RealInnerProductSpace FourierTransform

private theorem trace_matrixFromVec_mul_eq_sum {A : Type*} [CommSemiring A] {n : Nat}
    (v : Prod (Fin n) (Fin n) -> A) (Y : Matrix (Fin n) (Fin n) A) :
    (godementJacquetMatrixFromVec v * Y).trace =
      Finset.univ.sum (fun i : Prod (Fin n) (Fin n) => v i * Y.vec i.swap) := by
  rw [<- Finset.univ_product_univ, Finset.sum_product]
  unfold Matrix.trace
  rw [Finset.sum_comm]
  rfl

variable (K : Type*) [Field K] [NumberField K]

private abbrev RectAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

private abbrev RectFinite (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev RectArch (K : Type*) [Field K] :=
  DedekindZeta.Theta.minkowskiSpace K

private def rectInfiniteCoordinates (x : InfiniteAdeleRing K) : RectArch K :=
  DedekindZeta.Theta.toMinkowski K (InfiniteAdeleRing.ringEquiv_mixedSpace K x)

private theorem trace_rectInfinite_mul_principal (x : InfiniteAdeleRing K) (t : K) :
    infiniteAdeleTrace (x * algebraMap K (InfiniteAdeleRing K) t) =
      inner Real (rectInfiniteCoordinates K x)
        (DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t)) := by
  let xi := InfiniteAdeleRing.ringEquiv_mixedSpace K x
  let eta := mixedEmbedding K t
  let T := DedekindZeta.Theta.toMinkowski K
  rw [infiniteAdeleTrace_mul_principal]
  change DedekindZeta.Theta.traceForm K xi t =
    inner Real (T xi) (DedekindZeta.Theta.conjMink K (T eta))
  rw [DedekindZeta.Theta.conjMink_apply, ContinuousLinearEquiv.symm_apply_apply,
    DedekindZeta.Theta.toMinkowski_inner]
  simp only [DedekindZeta.Theta.traceForm, DedekindZeta.Theta.conjMixed_fst,
    DedekindZeta.Theta.conjMixed_snd, starRingEnd_apply, star_star]
  rfl

private theorem coe_heckeAdeleAddChar_neg_mul_principal (x : RectAdeles K) (t : K) :
    (heckeAdeleAddChar (-(x * algebraMap K (RectAdeles K) t)) : Complex) =
      (Real.fourierChar (-(inner Real (rectInfiniteCoordinates K x.1)
        (DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t)))) : Complex) *
        (heckeFiniteAdelePrincipalChar (-t) x.2 : Complex) := by
  let ai := x.1 * algebraMap K (InfiniteAdeleRing K) t
  let af := x.2 * algebraMap K (RectFinite K) t
  let zi : RectAdeles K := Prod.mk (-ai) 0
  let zf : RectAdeles K := Prod.mk 0 (-af)
  have hsplit : -(x * algebraMap K (RectAdeles K) t) = zi + zf := by
    apply Prod.ext
    . exact (add_zero (-ai)).symm
    . exact (zero_add (-af)).symm
  rw [hsplit, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hiz : forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K) (zi.2 p) :=
    fun p => (p.adicCompletionIntegers K).zero_mem
  have harch := heckeAdeleAddChar_of_integralFinitePart zi hiz
  have hi : infiniteAdeleTrace zi.1 =
      -(inner Real (rectInfiniteCoordinates K x.1)
        (DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t))) := by
    change infiniteAdeleTrace (-ai) = _
    rw [map_neg, trace_rectInfinite_mul_principal]
  rw [harch, hi]
  have hfin : zf = (Prod.mk (0 : InfiniteAdeleRing K)
      (x.2 * algebraMap K (RectFinite K) (-t)) : RectAdeles K) := by
    rw [map_neg, mul_neg]
  rw [hfin]
  rfl

private theorem rect_coe_addChar_sum {A B : Type*} [AddCommMonoid A]
    (chi : AddChar A Circle) (s : Finset B) (v : B -> A) :
    (chi (s.sum v) : Complex) = s.prod (fun i => (chi (v i) : Complex)) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, AddChar.map_zero_eq_one, Circle.coe_one, Finset.prod_empty]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

variable (I : Type*) [Fintype I]

private abbrev RectArchVector := PiLp 2 (fun _ : I => RectArch K)

private def rectInfiniteVector (x : I -> InfiniteAdeleRing K) : RectArchVector K I :=
  WithLp.toLp 2 (fun i => rectInfiniteCoordinates K (x i))

private theorem rect_trace_phase (x : I -> RectAdeles K) (t : I -> K) :
    (heckeAdeleAddChar (-(Finset.univ.sum (fun i => x i * algebraMap K (RectAdeles K) (t i)))) : Complex) =
      (Real.fourierChar (-(inner Real (rectInfiniteVector K I (fun i => (x i).1))
        (heckeConjMinkowskiVector K I (heckePrincipalMinkowskiVector K I t)))) : Complex) *
      Finset.univ.prod (fun i => (heckeFiniteAdelePrincipalChar (-(t i)) (x i).2 : Complex)) := by
  rw [<- Finset.sum_neg_distrib, rect_coe_addChar_sum]
  simp_rw [coe_heckeAdeleAddChar_neg_mul_principal, Finset.prod_mul_distrib,
    <- rect_coe_addChar_sum Real.fourierChar, Finset.sum_neg_distrib]
  rfl

variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  [MeasurableSpace (RectFinite K)] [BorelSpace (RectFinite K)]

local instance : MeasurableSpace (RectAdeles K) :=
  inferInstanceAs (MeasurableSpace (Prod (InfiniteAdeleRing K) (RectFinite K)))

local instance : SecondCountableTopology (RectArch K) :=
  (DedekindZeta.Theta.toMinkowski K).symm.toHomeomorph.isEmbedding.secondCountableTopology

local instance : BorelSpace (RectArchVector K I) := by
  let h : forall _ : I, BorelSpace (RectArch K) := fun _ => inferInstance
  let t : forall _ : I, SecondCountableTopology (RectArch K) := fun _ => inferInstance
  exact PiLp.borelSpace (p := 2) (X := fun _ : I => RectArch K)

private def rectInfiniteEquiv : MeasurableEquiv (InfiniteAdeleRing K) (RectArch K) :=
  { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv.trans
      (DedekindZeta.Theta.toMinkowski K).toEquiv
    measurable_toFun := (DedekindZeta.Theta.toMinkowski K).continuous.measurable.comp
      (continuous_heckeInfiniteAdele_mixedSpace (K := K)).measurable
    measurable_invFun := (continuous_heckeInfiniteAdele_mixedSpace_symm K).measurable.comp
      (DedekindZeta.Theta.toMinkowski K).symm.continuous.measurable }

omit [MeasurableSpace (RectFinite K)] [BorelSpace (RectFinite K)] in
private theorem measurePreserving_rectInfiniteEquiv :
    MeasurePreserving (rectInfiniteEquiv K) heckeInfiniteAdeleAdditiveHaar volume := by
  let e := rectInfiniteEquiv K
  refine MeasurePreserving.mk e.measurable ?_
  change Measure.map e (Measure.map e.symm volume) = volume
  rw [Measure.map_map e.measurable e.symm.measurable]
  have he : Function.comp e e.symm = id := funext e.apply_symm_apply
  rw [he, Measure.map_id]

private def rectInfiniteVectorEquiv :
    MeasurableEquiv (I -> InfiniteAdeleRing K) (RectArchVector K I) :=
  (MeasurableEquiv.piCongrRight (fun _ : I => rectInfiniteEquiv K)).trans
    (MeasurableEquiv.toLp 2 (I -> RectArch K))

omit [MeasurableSpace (RectFinite K)] [BorelSpace (RectFinite K)] in
private theorem measurePreserving_rectInfiniteVectorEquiv :
    MeasurePreserving (rectInfiniteVectorEquiv K I)
      (Measure.pi (fun _ : I => heckeInfiniteAdeleAdditiveHaar (K := K))) volume := by
  let e := MeasurableEquiv.toLp 2 (I -> RectArch K)
  have hLp : MeasurePreserving e
      (Measure.pi (fun _ : I => (volume : Measure (RectArch K)))) volume :=
    MeasurePreserving.symm e.symm (measurePreserving_euclidean_product_ofLp I (RectArch K))
  exact hLp.comp (measurePreserving_pi _ _ (fun _ : I => measurePreserving_rectInfiniteEquiv K))

private def rectVectorFunction
    (a : I -> RectFinite K) (d : RingOfIntegers K)
    (f : SchwartzMap (RectArchVector K I) Complex) (x : I -> RectAdeles K) : Complex :=
  f (rectInfiniteVector K I (fun i => (x i).1)) *
    Finset.univ.prod (fun i =>
      (heckeFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d)).indicator
        (fun _ => (1 : Complex)) (x i).2)

private noncomputable def rectFourierScale : Complex :=
  (Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex)) ^ Fintype.card I

private theorem rectVectorFourierIntegral
    (a : I -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K I) Complex) (t : I -> K) :
    rectFourierScale K I * integral
      (Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K)))
      (fun x => rectVectorFunction K I a d f x *
        (heckeAdeleAddChar (-(Finset.univ.sum (fun i => x i * algebraMap K (RectAdeles K) (t i)))) :
          Complex)) =
        heckeAdeleVectorRectangleFourierIntegral K I a d f t := by
  let R := RingOfIntegers K
  let dd := algebraMap R K d
  let C (i : I) := heckeFiniteAdelePrincipalCoset (a i) dd
  let muI := heckeInfiniteAdeleAdditiveHaar (K := K)
  let muF := heckeFiniteAdeleHaar (K := K)
  let y := heckeConjMinkowskiVector K I (heckePrincipalMinkowskiVector K I t)
  let A (z : RectArchVector K I) : Complex := f z * (Real.fourierChar (-(inner Real z y)) : Complex)
  let P (i : I) (z : RectFinite K) : Complex :=
    (C i).indicator (fun _ => (1 : Complex)) z * (heckeFiniteAdelePrincipalChar (-(t i)) z : Complex)
  let B (z : I -> RectFinite K) : Complex := Finset.univ.prod (fun i => P i (z i))
  let : SigmaFinite muF := by
    let : LocallyCompactSpace (RectFinite K) := locallyCompactSpace_heckeFiniteAdeles
    let : SecondCountableTopology (RectFinite K) := secondCountableTopology_heckeFiniteAdeles K
    change SigmaFinite (heckeFiniteAdeleHaar (K := K))
    unfold heckeFiniteAdeleHaar
    infer_instance
  let q := MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing K) (RectFinite K) I
  have hq : MeasurePreserving q (Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K)))
      ((Measure.pi (fun _ : I => muI)).prod (Measure.pi (fun _ : I => muF))) :=
    measurePreserving_arrowProdEquivProdArrow _ _ _ (fun _ : I => muI) (fun _ : I => muF)
  have hArch : integral (Measure.pi (fun _ : I => muI)) (fun z => A (rectInfiniteVector K I z)) =
      FourierTransform.fourier (f : RectArchVector K I -> Complex) y := by
    have he := (measurePreserving_rectInfiniteVectorEquiv K I).integral_comp' A
    change integral (Measure.pi (fun _ : I => muI)) (fun z => A (rectInfiniteVector K I z)) =
      integral volume A at he
    rw [he, Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards with z
    exact mul_comm _ _
  have hd' : Not (dd = 0) :=
    (map_ne_zero_iff (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)).mpr hd
  have hFin : integral (Measure.pi (fun _ : I => muF)) B =
      Finset.univ.prod (fun i => integral (muF.restrict (C i))
        (fun z => (heckeFiniteAdelePrincipalChar (-(t i)) z : Complex))) := by
    change integral (Measure.pi (fun _ : I => muF)) (fun z => Finset.univ.prod (fun i => P i (z i))) = _
    rw [integral_fintype_prod_eq_prod]
    apply Finset.prod_congr rfl
    intro i _
    have hC : MeasurableSet (C i) :=
      ((Homeomorph.addLeft (a i)).isOpenMap _ (isOpen_heckeScaledIntegralFiniteAdeles dd hd')).measurableSet
    rw [<- integral_indicator hC]
    apply integral_congr_ae
    filter_upwards with z
    change (C i).indicator (fun _ => (1 : Complex)) z *
      (heckeFiniteAdelePrincipalChar (-(t i)) z : Complex) =
        (C i).indicator (fun w => (heckeFiniteAdelePrincipalChar (-(t i)) w : Complex)) z
    by_cases hz : Membership.mem (C i) z
    . rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
    . rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
  refine (congrArg (fun z : Complex => rectFourierScale K I * z) ?_).trans
    (mul_assoc (rectFourierScale K I) _ _).symm
  let Q (z : Prod (I -> InfiniteAdeleRing K) (I -> RectFinite K)) : Complex :=
    A (rectInfiniteVector K I z.1) * B z.2
  calc
    _ = integral (Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K))) (fun x => Q (q x)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [rect_trace_phase K I]
      change f (rectInfiniteVector K I (fun i => (z i).1)) *
        Finset.univ.prod (fun i => (C i).indicator (fun _ => (1 : Complex)) (z i).2) *
        ((Real.fourierChar (-(inner Real (rectInfiniteVector K I (fun i => (z i).1)) y)) : Complex) *
          Finset.univ.prod (fun i => (heckeFiniteAdelePrincipalChar (-(t i)) (z i).2 : Complex))) = _
      unfold Q A B P
      change _ = _ * Finset.univ.prod (fun i =>
        (C i).indicator (fun _ => (1 : Complex)) (z i).2 *
          (heckeFiniteAdelePrincipalChar (-(t i)) (z i).2 : Complex))
      rw [Finset.prod_mul_distrib]
      ac_rfl
    _ = integral ((Measure.pi (fun _ : I => muI)).prod (Measure.pi (fun _ : I => muF))) Q :=
      hq.integral_comp' Q
    _ = _ := by
      calc
        _ = integral (Measure.pi (fun _ : I => muI)) (fun x => A (rectInfiniteVector K I x)) *
            integral (Measure.pi (fun _ : I => muF)) B :=
          integral_prod_mul (fun x => A (rectInfiniteVector K I x)) B
        _ = _ := (congrArg (fun z : Complex =>
          z * integral (Measure.pi (fun _ : I => muF)) B) hArch).trans
          (congrArg (fun z : Complex =>
            FourierTransform.fourier (f : RectArchVector K I -> Complex) y * z) hFin)

private theorem rectMatrixFourierIntegral {n : Nat}
    (a : Prod (Fin n) (Fin n) -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K (Prod (Fin n) (Fin n))) Complex)
    (Y : Matrix (Fin n) (Fin n) K) :
    let J := Prod (Fin n) (Fin n)
    rectFourierScale K J *
      godementJacquetMatrixFourier K (fun X => rectVectorFunction K J a d f X.vec)
        (Y.map (algebraMap K (RectAdeles K))) =
      heckeAdeleVectorRectangleFourierIntegral K J a d f (fun i => Y.vec i.swap) := by
  let J := Prod (Fin n) (Fin n)
  let t : J -> K := fun i => Y.vec i.swap
  change rectFourierScale K J *
    godementJacquetMatrixFourier K (fun X => rectVectorFunction K J a d f X.vec)
      (Y.map (algebraMap K (RectAdeles K))) = heckeAdeleVectorRectangleFourierIntegral K J a d f t
  rw [<- rectVectorFourierIntegral K J a d hd f t]
  apply congrArg (fun z : Complex => rectFourierScale K J * z)
  unfold godementJacquetMatrixFourier
  apply integral_congr_ae
  filter_upwards with v
  change rectVectorFunction K J a d f (godementJacquetMatrixFromVec v).vec *
    (heckeAdeleAddChar (-(godementJacquetMatrixFromVec v * Y.map (algebraMap K (RectAdeles K))).trace) :
      Complex) = _
  rw [godementJacquetMatrixFromVec_vec, trace_matrixFromVec_mul_eq_sum]
  rfl

omit [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  [MeasurableSpace (RectFinite K)] [BorelSpace (RectFinite K)] in
private theorem rectInfiniteCoordinates_principal (x : K) :
    rectInfiniteCoordinates K (algebraMap K (InfiniteAdeleRing K) x) = DedekindZeta.Theta.eEmb K x := by
  change DedekindZeta.Theta.toMinkowski K
    (InfiniteAdeleRing.ringEquiv_mixedSpace K (algebraMap K (InfiniteAdeleRing K) x)) =
    DedekindZeta.Theta.toMinkowski K (mixedEmbedding K x)
  exact congrArg (DedekindZeta.Theta.toMinkowski K)
    (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := K) (x := x)).symm

omit [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)] in
private theorem rectVectorFunction_principal
    (a : I -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K I) Complex) (x : I -> K) :
    let dd := algebraMap (RingOfIntegers K) K d
    let S : Set (I -> K) := fun x => forall i, InFiniteAdelePrincipalCoset (a i) dd (x i)
    rectVectorFunction K I a d f (fun i => algebraMap K (RectAdeles K) (x i)) =
      S.indicator (fun z => f (heckePrincipalMinkowskiVector K I z)) x := by
  let dd := algebraMap (RingOfIntegers K) K d
  let S : Set (I -> K) := fun x => forall i, InFiniteAdelePrincipalCoset (a i) dd (x i)
  let g := algebraMap K (RectFinite K)
  let C (i : I) := heckeFiniteAdelePrincipalCoset (a i) dd
  let m (i : I) := (C i).indicator (fun _ => (1 : Complex)) (g (x i))
  have hA : rectInfiniteVector K I (fun i => algebraMap K (InfiniteAdeleRing K) (x i)) =
      heckePrincipalMinkowskiVector K I x :=
    congrArg (WithLp.toLp 2) (funext (fun i => rectInfiniteCoordinates_principal K (x i)))
  have hd' : Not (dd = 0) :=
    (map_ne_zero_iff (algebraMap (RingOfIntegers K) K) (FaithfulSMul.algebraMap_injective _ _)).mpr hd
  have hc (i : I) :
      InFiniteAdelePrincipalCoset (a i) dd (x i) <-> Membership.mem (C i) (g (x i)) :=
    finiteAdelePrincipalCoset_iff_mem_translate (a i) dd (x i) hd'
  change f (rectInfiniteVector K I (fun i => algebraMap K (InfiniteAdeleRing K) (x i))) *
    Finset.univ.prod m = S.indicator (fun z => f (heckePrincipalMinkowskiVector K I z)) x
  rw [hA]
  by_cases hx : Membership.mem S x
  case pos =>
    have hm (i : I) : m i = 1 := Set.indicator_of_mem ((hc i).mp (hx i)) _
    rw [Set.indicator_of_mem hx]
    simp only [hm, Finset.prod_const_one, mul_one]
  case neg =>
    have hNot : Not (forall i, InFiniteAdelePrincipalCoset (a i) dd (x i)) := hx
    choose i hi using not_forall.mp hNot
    have hm : m i = 0 := Set.indicator_of_notMem (fun h => hi ((hc i).mpr h)) _
    have hp : Finset.univ.prod m = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hm
    rw [Set.indicator_of_notMem hx, hp, mul_zero]

/-- A joint archimedean Schwartz function multiplied by the
indicator of a product of finite adelic principal cosets. -/
def godementJacquetMatrixRectangle {n : Nat}
    (a : Prod (Fin n) (Fin n) -> RectFinite K) (d : RingOfIntegers K)
    (f : SchwartzMap (RectArchVector K (Prod (Fin n) (Fin n))) Complex)
    (X : Matrix (Fin n) (Fin n) (RectAdeles K)) : Complex :=
  rectVectorFunction K (Prod (Fin n) (Fin n)) a d f X.vec

/-- Fourier transformation for the matrix trace pairing with the
self-dual discriminant normalization. -/
def godementJacquetSelfDualMatrixFourier {n : Nat}
    (phi : Matrix (Fin n) (Fin n) (RectAdeles K) -> Complex)
    (Y : Matrix (Fin n) (Fin n) (RectAdeles K)) : Complex :=
  rectFourierScale K (Prod (Fin n) (Fin n)) * godementJacquetMatrixFourier K phi Y

/-- Poisson summation on rational matrices for a joint archimedean
Schwartz function and a product of finite adelic principal cosets.
The transform uses the matrix trace pairing and the self-dual measure. -/
theorem tsum_godementJacquetMatrixRectangle_eq_normalizedFourier {n : Nat}
    (a : Prod (Fin n) (Fin n) -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K (Prod (Fin n) (Fin n))) Complex) :
    let phi := godementJacquetMatrixRectangle K a d f
    let p := algebraMap K (RectAdeles K)
    tsum (fun X : Matrix (Fin n) (Fin n) K => phi (X.map p)) =
      tsum (fun Y : Matrix (Fin n) (Fin n) K =>
        godementJacquetSelfDualMatrixFourier K phi (Y.map p)) := by
  let J := Prod (Fin n) (Fin n)
  let S : Set (J -> K) := fun x => forall i,
    InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x i)
  let p := algebraMap K (RectAdeles K)
  let phi (X : Matrix (Fin n) (Fin n) (RectAdeles K)) := rectVectorFunction K J a d f X.vec
  let E : Equiv (Matrix (Fin n) (Fin n) K) (J -> K) :=
    { toFun := Matrix.vec
      invFun := godementJacquetMatrixFromVec
      left_inv := fun X => Matrix.vec_inj.mp (godementJacquetMatrixFromVec_vec X.vec)
      right_inv := godementJacquetMatrixFromVec_vec }
  let F : Equiv (Matrix (Fin n) (Fin n) K) (J -> K) :=
    { toFun := fun Y i => Y.vec i.swap
      invFun := fun v => (godementJacquetMatrixFromVec v).transpose
      left_inv := fun Y => Matrix.ext (fun _ _ => rfl)
      right_inv := fun _ => funext (fun i => by cases i; rfl) }
  let L (x : J -> K) := rectVectorFunction K J a d f (fun i => p (x i))
  let R := heckeAdeleVectorRectangleFourierIntegral K J a d f
  change tsum (fun X : Matrix (Fin n) (Fin n) K => phi (X.map p)) =
    tsum (fun Y : Matrix (Fin n) (Fin n) K => rectFourierScale K J * godementJacquetMatrixFourier K phi (Y.map p))
  calc
    _ = tsum L := E.tsum_eq L
    _ = tsum (S.indicator (fun x => f (heckePrincipalMinkowskiVector K J x))) :=
      tsum_congr (rectVectorFunction_principal K J a d hd f)
    _ = tsum (fun x : S => f (heckePrincipalMinkowskiVector K J x.val)) :=
      (tsum_subtype S _).symm
    _ = tsum R := tsum_finiteAdelePrincipalVectorCoset_eq_fourierIntegral K J a d hd f
    _ = tsum (fun Y : Matrix (Fin n) (Fin n) K => R (F Y)) := (F.tsum_eq R).symm
    _ = _ := tsum_congr (fun Y => (rectMatrixFourierIntegral K a d hd f Y).symm)

end Robin1984.GRH
