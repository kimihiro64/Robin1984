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

private theorem rectInfiniteCoordinates_principal (x : K) :
    rectInfiniteCoordinates K (algebraMap K (InfiniteAdeleRing K) x) = DedekindZeta.Theta.eEmb K x := by
  change DedekindZeta.Theta.toMinkowski K
    (InfiniteAdeleRing.ringEquiv_mixedSpace K (algebraMap K (InfiniteAdeleRing K) x)) =
    DedekindZeta.Theta.toMinkowski K (mixedEmbedding K x)
  exact congrArg (DedekindZeta.Theta.toMinkowski K)
    (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := K) (x := x)).symm

private theorem trace_rectInfinite_mul (x y : InfiniteAdeleRing K) :
    infiniteAdeleTrace (x * y) = inner Real (rectInfiniteCoordinates K x)
      (DedekindZeta.Theta.conjMink K (rectInfiniteCoordinates K y)) := by
  let F (z : InfiniteAdeleRing K) := infiniteAdeleTrace (x * z)
  let G (z : InfiniteAdeleRing K) := inner Real (rectInfiniteCoordinates K x)
    (DedekindZeta.Theta.conjMink K (rectInfiniteCoordinates K z))
  have hF : Continuous F := continuous_infiniteAdeleTrace.comp (continuous_const.mul continuous_id)
  have hCoord : Continuous (rectInfiniteCoordinates K) :=
    (DedekindZeta.Theta.toMinkowski K).continuous.comp (continuous_heckeInfiniteAdele_mixedSpace (K := K))
  have hG : Continuous G := continuous_const.inner ((DedekindZeta.Theta.conjMink K).continuous.comp hCoord)
  have hEq : F = G := (InfiniteAdeleRing.denseRange_algebraMap (K := K)).equalizer hF hG (by
    funext t
    change infiniteAdeleTrace (x * algebraMap K (InfiniteAdeleRing K) t) =
      inner Real (rectInfiniteCoordinates K x)
        (DedekindZeta.Theta.conjMink K (rectInfiniteCoordinates K (algebraMap K (InfiniteAdeleRing K) t)))
    rw [rectInfiniteCoordinates_principal, trace_rectInfinite_mul_principal])
  exact congrFun hEq y

private theorem coe_heckeAdeleAddChar_neg_mul (x y : RectAdeles K) :
    (heckeAdeleAddChar (-(x * y)) : Complex) =
      (Real.fourierChar (-(inner Real (rectInfiniteCoordinates K x.1)
        (DedekindZeta.Theta.conjMink K (rectInfiniteCoordinates K y.1)))) : Complex) *
      (heckeFiniteAddChar (x.2 * (-y.2)) : Complex) := by
  let ai := x.1 * y.1
  let af := x.2 * y.2
  let zi : RectAdeles K := Prod.mk (-ai) 0
  let zf : RectAdeles K := Prod.mk 0 (-af)
  have hsplit : -(x * y) = zi + zf := by
    apply Prod.ext
    . exact (add_zero (-ai)).symm
    . exact (zero_add (-af)).symm
  rw [hsplit, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hzi : forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K) (zi.2 p) :=
    fun p => (p.adicCompletionIntegers K).zero_mem
  have harch := heckeAdeleAddChar_of_integralFinitePart zi hzi
  have hi : infiniteAdeleTrace zi.1 = -(inner Real (rectInfiniteCoordinates K x.1)
      (DedekindZeta.Theta.conjMink K (rectInfiniteCoordinates K y.1))) := by
    change infiniteAdeleTrace (-ai) = _
    rw [map_neg, trace_rectInfinite_mul]
  have hf : zf = (Prod.mk (0 : InfiniteAdeleRing K) (x.2 * (-y.2)) : RectAdeles K) := by
    rw [mul_neg]
  rw [harch, hi, hf]
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

private theorem rect_trace_phase_full (x t : I -> RectAdeles K) :
    (heckeAdeleAddChar (-(Finset.univ.sum (fun i => x i * t i))) : Complex) =
      (Real.fourierChar (-(inner Real (rectInfiniteVector K I (fun i => (x i).1))
        (heckeConjMinkowskiVector K I (rectInfiniteVector K I (fun i => (t i).1))))) : Complex) *
      Finset.univ.prod (fun i => (heckeFiniteAddChar ((x i).2 * (-(t i).2)) : Complex)) := by
  rw [<- Finset.sum_neg_distrib, rect_coe_addChar_sum]
  simp_rw [coe_heckeAdeleAddChar_neg_mul, Finset.prod_mul_distrib,
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

private theorem rectVectorFourierIntegral_full
    (a : I -> RectFinite K) (d : RingOfIntegers K)
    (f : SchwartzMap (RectArchVector K I) Complex) (t : I -> RectAdeles K) :
    integral (Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K)))
      (fun x => rectVectorFunction K I a d f x *
        (heckeAdeleAddChar (-(Finset.univ.sum (fun i => x i * t i))) : Complex)) =
      FourierTransform.fourier (f : RectArchVector K I -> Complex)
        (heckeConjMinkowskiVector K I (rectInfiniteVector K I (fun i => (t i).1))) *
      Finset.univ.prod (fun i => heckeFiniteFourierIntegral (heckeFiniteAdeleHaar (K := K))
        ((heckeFiniteAdelePrincipalCoset (a i)
          (algebraMap (RingOfIntegers K) K d)).indicator (fun _ => (1 : Complex))) (-(t i).2)) := by
  let dd := algebraMap (RingOfIntegers K) K d
  let C (i : I) := heckeFiniteAdelePrincipalCoset (a i) dd
  let muI := heckeInfiniteAdeleAdditiveHaar (K := K)
  let muF := heckeFiniteAdeleHaar (K := K)
  let y := heckeConjMinkowskiVector K I (rectInfiniteVector K I (fun i => (t i).1))
  let A (z : RectArchVector K I) : Complex := f z * (Real.fourierChar (-(inner Real z y)) : Complex)
  let P (i : I) (z : RectFinite K) : Complex :=
    (C i).indicator (fun _ => (1 : Complex)) z * (heckeFiniteAddChar (z * (-(t i).2)) : Complex)
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
  have hFin : integral (Measure.pi (fun _ : I => muF)) B =
      Finset.univ.prod (fun i => heckeFiniteFourierIntegral muF
        ((C i).indicator (fun _ => (1 : Complex))) (-(t i).2)) := by
    change integral (Measure.pi (fun _ : I => muF)) (fun z => Finset.univ.prod (fun i => P i (z i))) = _
    rw [integral_fintype_prod_eq_prod]
    rfl
  let Q (z : Prod (I -> InfiniteAdeleRing K) (I -> RectFinite K)) : Complex :=
    A (rectInfiniteVector K I z.1) * B z.2
  calc
    _ = integral (Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K))) (fun x => Q (q x)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [rect_trace_phase_full K I]
      change f (rectInfiniteVector K I (fun i => (z i).1)) *
        Finset.univ.prod (fun i => (C i).indicator (fun _ => (1 : Complex)) (z i).2) *
        ((Real.fourierChar (-(inner Real (rectInfiniteVector K I (fun i => (z i).1)) y)) : Complex) *
          Finset.univ.prod (fun i => (heckeFiniteAddChar ((z i).2 * (-(t i).2)) : Complex))) = _
      unfold Q A B P
      change _ = _ * Finset.univ.prod (fun i =>
        (C i).indicator (fun _ => (1 : Complex)) (z i).2 *
          (heckeFiniteAddChar ((z i).2 * (-(t i).2)) : Complex))
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
  let g := algebraMap K (RectAdeles K)
  let t' (i : I) := g (t i)
  have hArch : rectInfiniteVector K I (fun i => (t' i).1) =
      heckePrincipalMinkowskiVector K I t :=
    congrArg (WithLp.toLp 2) (funext (fun i => rectInfiniteCoordinates_principal K (t i)))
  have hd' : Not (dd = 0) :=
    (map_ne_zero_iff (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)).mpr hd
  have hFin (i : I) :
      heckeFiniteFourierIntegral (heckeFiniteAdeleHaar (K := K))
        ((C i).indicator (fun _ => (1 : Complex))) (-(t' i).2) =
      integral ((heckeFiniteAdeleHaar (K := K)).restrict (C i))
        (fun z => (heckeFiniteAdelePrincipalChar (-(t i)) z : Complex)) := by
    have hC : MeasurableSet (C i) :=
      ((Homeomorph.addLeft (a i)).isOpenMap _ (isOpen_heckeScaledIntegralFiniteAdeles dd hd')).measurableSet
    let gF := algebraMap K (RectFinite K)
    have hn : -(t' i).2 = gF (-(t i)) := (map_neg gF (t i)).symm
    rw [hn, <- integral_indicator hC]
    apply integral_congr_ae
    filter_upwards with z
    change (C i).indicator (fun _ => (1 : Complex)) z *
      (heckeFiniteAdelePrincipalChar (-(t i)) z : Complex) =
      (C i).indicator (fun w => (heckeFiniteAdelePrincipalChar (-(t i)) w : Complex)) z
    by_cases hz : Membership.mem (C i) z
    . rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
    . rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
  change rectFourierScale K I * integral
    (Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K)))
    (fun x => rectVectorFunction K I a d f x *
      (heckeAdeleAddChar (-(Finset.univ.sum (fun i => x i * t' i))) : Complex)) = _
  rw [rectVectorFourierIntegral_full, hArch, <- mul_assoc]
  let A := rectFourierScale K I * FourierTransform.fourier
    (f : RectArchVector K I -> Complex)
    (heckeConjMinkowskiVector K I (heckePrincipalMinkowskiVector K I t))
  exact congrArg (fun p : Complex => A * p) (Finset.prod_congr rfl (fun i _ => hFin i))

private theorem godementJacquetMatrixFourier_rectangle_full {n : Nat}
    (a : Prod (Fin n) (Fin n) -> RectFinite K) (d : RingOfIntegers K)
    (f : SchwartzMap (RectArchVector K (Prod (Fin n) (Fin n))) Complex)
    (Y : Matrix (Fin n) (Fin n) (RectAdeles K)) :
    let J := Prod (Fin n) (Fin n)
    godementJacquetMatrixFourier K (fun X => rectVectorFunction K J a d f X.vec) Y =
      FourierTransform.fourier (f : RectArchVector K J -> Complex)
        (heckeConjMinkowskiVector K J (rectInfiniteVector K J (fun i => (Y.vec i.swap).1))) *
      Finset.univ.prod (fun i : J => heckeFiniteFourierIntegral (heckeFiniteAdeleHaar (K := K))
        ((heckeFiniteAdelePrincipalCoset (a i)
          (algebraMap (RingOfIntegers K) K d)).indicator (fun _ => (1 : Complex))) (-(Y.vec i.swap).2)) := by
  let J := Prod (Fin n) (Fin n)
  let t : J -> RectAdeles K := fun i => Y.vec i.swap
  dsimp only
  rw [<- rectVectorFourierIntegral_full K J a d f t]
  unfold godementJacquetMatrixFourier
  apply integral_congr_ae
  filter_upwards with v
  change rectVectorFunction K J a d f (godementJacquetMatrixFromVec v).vec *
    (heckeAdeleAddChar (-(godementJacquetMatrixFromVec v * Y).trace) : Complex) = _
  rw [godementJacquetMatrixFromVec_vec, trace_matrixFromVec_mul_eq_sum]

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

/-- The self-dual Fourier transform of a Schwartz rectangle at an arbitrary
adelic matrix is an archimedean Fourier transform times the finite
coset transforms. The matrix trace pairing transposes the frequency. -/
theorem godementJacquetSelfDualMatrixFourier_rectangle_apply {n : Nat}
    (a : Prod (Fin n) (Fin n) -> RectFinite K) (d : RingOfIntegers K)
    (f : SchwartzMap (RectArchVector K (Prod (Fin n) (Fin n))) Complex)
    (Y : Matrix (Fin n) (Fin n) (RectAdeles K)) :
    let J := Prod (Fin n) (Fin n)
    godementJacquetSelfDualMatrixFourier K (godementJacquetMatrixRectangle K a d f) Y =
      ((Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex)) ^ Fintype.card J *
        FourierTransform.fourier (f : RectArchVector K J -> Complex)
          (heckeConjMinkowskiVector K J (WithLp.toLp 2 (fun i : J =>
            DedekindZeta.Theta.toMinkowski K
              (InfiniteAdeleRing.ringEquiv_mixedSpace K (Y.vec i.swap).1))))) *
      Finset.univ.prod (fun i : J => heckeFiniteFourierIntegral (heckeFiniteAdeleHaar (K := K))
        ((heckeFiniteAdelePrincipalCoset (a i)
          (algebraMap (RingOfIntegers K) K d)).indicator (fun _ => (1 : Complex))) (-(Y.vec i.swap).2)) := by
  let J := Prod (Fin n) (Fin n)
  change rectFourierScale K J * godementJacquetMatrixFourier K
    (fun X => rectVectorFunction K J a d f X.vec) Y = _
  rw [godementJacquetMatrixFourier_rectangle_full, <- mul_assoc]
  rfl

set_option maxHeartbeats 1000000 in
private theorem matrixRectanglePoissonData {n : Nat}
    (a : Prod (Fin n) (Fin n) -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K (Prod (Fin n) (Fin n))) Complex) :
    let phi := godementJacquetMatrixRectangle K a d f
    let p := algebraMap K (RectAdeles K)
    let P := fun X : Matrix (Fin n) (Fin n) K => phi (X.map p)
    let Q := fun Y : Matrix (Fin n) (Fin n) K =>
      godementJacquetSelfDualMatrixFourier K phi (Y.map p)
    And (Summable P) (And (Summable Q) (tsum P = tsum Q)) := by
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
  have hD : Not (algebraMap (RingOfIntegers K) K d = 0) :=
    (map_ne_zero_iff (algebraMap (RingOfIntegers K) K)
      (FaithfulSMul.algebraMap_injective _ _)).mpr hd
  have hRep : forall i, Exists
      (InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d)) :=
    fun i => exists_finiteAdele_sub_principal_modulus (a i) _ hD
  choose x0 hx0 using hRep
  have hP : Summable L :=
    (summable_subtype_iff_indicator.mp
      (summable_finiteAdelePrincipalVectorCoset K J a d hd x0 hx0 f)).congr
        (fun x => (rectVectorFunction_principal K J a d hd f x).symm)
  have hQ : Summable R :=
    summable_heckeAdeleVectorRectangleFourierIntegral K J a d hd f
  refine And.intro (E.summable_iff.mpr hP) (And.intro ?_ ?_)
  . exact (F.summable_iff.mpr hQ).congr
      (fun Y => (rectMatrixFourierIntegral K a d hd f Y).symm)
  . calc
      _ = tsum L := E.tsum_eq L
      _ = tsum (S.indicator (fun x => f (heckePrincipalMinkowskiVector K J x))) :=
        tsum_congr (rectVectorFunction_principal K J a d hd f)
      _ = tsum (fun x : S => f (heckePrincipalMinkowskiVector K J x.val)) :=
        (tsum_subtype S _).symm
      _ = tsum R := tsum_finiteAdelePrincipalVectorCoset_eq_fourierIntegral K J a d hd f
      _ = tsum (fun Y : Matrix (Fin n) (Fin n) K => R (F Y)) := (F.tsum_eq R).symm
      _ = _ := tsum_congr (fun Y => (rectMatrixFourierIntegral K a d hd f Y).symm)

/-- Absolute convergence of the rational matrix sum of a Schwartz rectangle. -/
theorem summable_godementJacquetMatrixRectangle {n : Nat}
    (a : Prod (Fin n) (Fin n) -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K (Prod (Fin n) (Fin n))) Complex) :
    Summable (fun X : Matrix (Fin n) (Fin n) K =>
      godementJacquetMatrixRectangle K a d f (X.map (algebraMap K (RectAdeles K)))) :=
  (matrixRectanglePoissonData K a d hd f).1

/-- Absolute convergence of the dual rational matrix sum of a Schwartz rectangle. -/
theorem summable_godementJacquetSelfDualMatrixFourier_rectangle {n : Nat}
    (a : Prod (Fin n) (Fin n) -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K (Prod (Fin n) (Fin n))) Complex) :
    Summable (fun Y : Matrix (Fin n) (Fin n) K =>
      godementJacquetSelfDualMatrixFourier K (godementJacquetMatrixRectangle K a d f)
        (Y.map (algebraMap K (RectAdeles K)))) :=
  (matrixRectanglePoissonData K a d hd f).2.1

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
        godementJacquetSelfDualMatrixFourier K phi (Y.map p)) :=
  (matrixRectanglePoissonData K a d hd f).2.2

omit [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (RectFinite K)] [BorelSpace (RectFinite K)] in
private theorem rectCoset_isCompact (a : RectFinite K) (d : K) :
    IsCompact (heckeFiniteAdelePrincipalCoset a d) := by
  have h : IsCompact (heckeScaledIntegralFiniteAdeles d : Set (RectFinite K)) := by
    change IsCompact (Set.image (fun z : RectFinite K => z * algebraMap K (RectFinite K) d)
      ((heckeIntegralFiniteAdeles (K := K)) : Set (RectFinite K)))
    exact (isCompact_integralFiniteAdeles (K := K)).image (continuous_id.mul continuous_const)
  exact h.image (continuous_const.add continuous_id)

omit [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (RectFinite K)] [BorelSpace (RectFinite K)] in
private theorem rectFinite_t2Space : T2Space (RectFinite K) := by
  let p (z : RectFinite K) (q : HeightOneSpectrum (RingOfIntegers K)) := z q
  exact T2Space.of_injective_continuous (show Function.Injective p from DFunLike.coe_injective)
    (continuous_pi (fun q => RestrictedProduct.continuous_eval q))

omit [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (RectFinite K)] [BorelSpace (RectFinite K)] in
private theorem rectVectorFunction_continuous
    (a : I -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K I) Complex) :
    Continuous (rectVectorFunction K I a d f) := by
  let dd := algebraMap (RingOfIntegers K) K d
  have hd' : Not (dd = 0) :=
    (map_ne_zero_iff (algebraMap (RingOfIntegers K) K)
      (FaithfulSMul.algebraMap_injective (RingOfIntegers K) K)).mpr hd
  let C (i : I) := heckeFiniteAdelePrincipalCoset (a i) dd
  have hA : Continuous (fun x : I -> RectAdeles K => rectInfiniteVector K I (fun i => (x i).1)) :=
    (PiLp.continuousLinearEquiv 2 Real (fun _ : I => RectArch K)).symm.continuous.comp
      (continuous_pi (fun i => (DedekindZeta.Theta.toMinkowski K).continuous.comp
        ((continuous_heckeInfiniteAdele_mixedSpace (K := K)).comp
          (continuous_fst.comp (continuous_apply i)))))
  let : T2Space (RectFinite K) := rectFinite_t2Space K
  have hB (i : I) : Continuous (fun z : RectFinite K => (C i).indicator (fun _ => (1 : Complex)) z) := by
    have hO : IsOpen (C i) :=
      (Homeomorph.addLeft (a i)).isOpenMap _ (isOpen_heckeScaledIntegralFiniteAdeles dd hd')
    have hCl : IsClopen (C i) := And.intro (rectCoset_isCompact K (a i) dd).isClosed hO
    exact hCl.continuous_indicator continuous_const
  exact (f.continuous.comp hA).mul (continuous_finsetProd _
    (fun i _ => (hB i).comp (continuous_snd.comp (continuous_apply i))))

omit [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (RectFinite K)] [BorelSpace (RectFinite K)] in
/-- The matrix Schwartz rectangle is continuous on the full adelic matrix space. -/
theorem continuous_godementJacquetMatrixRectangle {n : Nat}
    (a : Prod (Fin n) (Fin n) -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K (Prod (Fin n) (Fin n))) Complex) :
    Continuous (godementJacquetMatrixRectangle K a d f) :=
  (rectVectorFunction_continuous K (Prod (Fin n) (Fin n)) a d hd f).comp
    (continuous_pi (fun i => (continuous_apply i.1).comp (continuous_apply i.2)))

private theorem rectVectorFunction_integrable
    (a : I -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K I) Complex) :
    Integrable (rectVectorFunction K I a d f)
      (Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K))) := by
  let R := RingOfIntegers K
  let dd := algebraMap R K d
  let C (i : I) := heckeFiniteAdelePrincipalCoset (a i) dd
  let muI := heckeInfiniteAdeleAdditiveHaar (K := K)
  let muF := heckeFiniteAdeleHaar (K := K)
  let P (i : I) := (C i).indicator (fun _ => (1 : Complex))
  let B (z : I -> RectFinite K) := Finset.univ.prod (fun i => P i (z i))
  let : LocallyCompactSpace (RectFinite K) := locallyCompactSpace_heckeFiniteAdeles
  let : SecondCountableTopology (RectFinite K) := secondCountableTopology_heckeFiniteAdeles K
  let : SigmaFinite muF := by
    change SigmaFinite (heckeFiniteAdeleHaar (K := K))
    unfold heckeFiniteAdeleHaar
    infer_instance
  let : IsFiniteMeasureOnCompacts muF := by
    change IsFiniteMeasureOnCompacts (heckeFiniteAdeleHaar (K := K))
    unfold heckeFiniteAdeleHaar
    infer_instance
  have hd' : Not (dd = 0) :=
    (map_ne_zero_iff (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)).mpr hd
  have hP (i : I) : Integrable (P i) muF := by
    have hO : IsOpen (C i) :=
      (Homeomorph.addLeft (a i)).isOpenMap _ (isOpen_heckeScaledIntegralFiniteAdeles dd hd')
    have hCpt : IsCompact (C i) := rectCoset_isCompact K (a i) dd
    have hMass : muF (C i) < (Top.top : ENNReal) := hCpt.measure_lt_top
    have hOne : IntegrableOn (fun _ : RectFinite K => (1 : Complex)) (C i) muF :=
      integrableOn_const hMass.ne
    exact hOne.integrable_indicator hO.measurableSet
  have hB : Integrable B (Measure.pi (fun _ : I => muF)) := Integrable.fintype_prod hP
  let e := rectInfiniteVectorEquiv K I
  have hA : Integrable (fun z => f (rectInfiniteVector K I z)) (Measure.pi (fun _ : I => muI)) :=
    ((measurePreserving_rectInfiniteVectorEquiv K I).integrable_comp_emb e.measurableEmbedding).mpr f.integrable
  let q := MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing K) (RectFinite K) I
  have hq : MeasurePreserving q (Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K)))
      ((Measure.pi (fun _ : I => muI)).prod (Measure.pi (fun _ : I => muF))) :=
    measurePreserving_arrowProdEquivProdArrow _ _ _ (fun _ : I => muI) (fun _ : I => muF)
  exact (hq.integrable_comp_emb q.measurableEmbedding).mpr (hA.mul_prod hB)

/-- The matrix Schwartz rectangle is integrable for the product
adelic additive measure in its entry coordinates. -/
theorem integrable_godementJacquetMatrixRectangle_fromVec {n : Nat}
    (a : Prod (Fin n) (Fin n) -> RectFinite K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (RectArchVector K (Prod (Fin n) (Fin n))) Complex) :
    Integrable (fun v => godementJacquetMatrixRectangle K a d f (godementJacquetMatrixFromVec v))
      (Measure.pi (fun _ : Prod (Fin n) (Fin n) => heckeAdeleAdditiveHaar (K := K))) := by
  let J := Prod (Fin n) (Fin n)
  have h : (fun v : J -> RectAdeles K => godementJacquetMatrixRectangle K a d f
      (godementJacquetMatrixFromVec v)) = rectVectorFunction K J a d f := by
    funext v
    change rectVectorFunction K J a d f (godementJacquetMatrixFromVec v).vec =
      rectVectorFunction K J a d f v
    rw [godementJacquetMatrixFromVec_vec]
  rw [h]
  exact rectVectorFunction_integrable K J a d hd f

/-- The self-dual matrix Fourier transform commutes with finite sums
of functions integrable in the adelic matrix entry coordinates. -/
theorem godementJacquetSelfDualMatrixFourier_finsetSum {n : Nat} {A : Type*}
    (s : Finset A)
    (phi : A -> Matrix (Fin n) (Fin n) (RectAdeles K) -> Complex)
    (hphi : forall i, Membership.mem s i ->
      Integrable (fun v => phi i (godementJacquetMatrixFromVec v))
        (Measure.pi (fun _ : Prod (Fin n) (Fin n) => heckeAdeleAdditiveHaar (K := K))))
    (Y : Matrix (Fin n) (Fin n) (RectAdeles K)) :
    godementJacquetSelfDualMatrixFourier K (fun X => s.sum (fun i => phi i X)) Y =
      s.sum (fun i => godementJacquetSelfDualMatrixFourier K (phi i) Y) := by
  let J := Prod (Fin n) (Fin n)
  let mu := Measure.pi (fun _ : J => heckeAdeleAdditiveHaar (K := K))
  let phase (v : J -> RectAdeles K) : Complex :=
    (heckeAdeleAddChar (-(godementJacquetMatrixFromVec v * Y).trace) : Complex)
  let g (i : A) (v : J -> RectAdeles K) := phi i (godementJacquetMatrixFromVec v) * phase v
  have hmat : Continuous (godementJacquetMatrixFromVec : (J -> RectAdeles K) ->
      Matrix (Fin n) (Fin n) (RectAdeles K)) :=
    continuous_matrix (fun i j => continuous_apply (Prod.mk j i))
  have htr : Continuous (fun v : J -> RectAdeles K => (godementJacquetMatrixFromVec v * Y).trace) :=
    (hmat.matrix_mul continuous_const).matrix_trace
  have hPhase : Continuous phase :=
    continuous_subtype_val.comp ((continuous_heckeAdeleAddChar (K := K)).comp htr.neg)
  let e : Homeomorph (InfiniteAdeleRing K) (mixedEmbedding.mixedSpace K) :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
      continuous_toFun := continuous_heckeInfiniteAdele_mixedSpace (K := K)
      continuous_invFun := continuous_heckeInfiniteAdele_mixedSpace_symm K }
  let : SecondCountableTopology (InfiniteAdeleRing K) := e.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (RectFinite K) := secondCountableTopology_heckeFiniteAdeles K
  let : SecondCountableTopology (RectAdeles K) :=
    inferInstanceAs (SecondCountableTopology (Prod (InfiniteAdeleRing K) (RectFinite K)))
  let : BorelSpace (RectAdeles K) :=
    inferInstanceAs (BorelSpace (Prod (InfiniteAdeleRing K) (RectFinite K)))
  have hBound : forall v, norm (phase v) <= 1 := fun v =>
    (Circle.norm_coe (heckeAdeleAddChar (-(godementJacquetMatrixFromVec v * Y).trace))).le
  have hg : forall i, Membership.mem s i -> Integrable (g i) mu := by
    intro i hi
    exact ((hphi i hi).bdd_mul hPhase.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hBound)).congr
      (Filter.Eventually.of_forall (fun v => mul_comm (phase v) (phi i (godementJacquetMatrixFromVec v))))
  calc
    _ = rectFourierScale K J * integral mu (fun v => s.sum (fun i => g i v)) := by
      apply congrArg (fun z : Complex => rectFourierScale K J * z)
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v => Finset.sum_mul s _ (phase v))
    _ = _ := by
      rw [integral_finsetSum s hg, Finset.mul_sum]
      rfl

end Robin1984.GRH
