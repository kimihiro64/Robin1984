import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Topology.Instances.Matrix
import Robin1984.GRH.GodementJacquetCoordinates
import Robin1984.GRH.GodementJacquetHaarNormalization

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and Fourier inversion for the adelic matrix trace pairing.
- Formalization note: Proves Fourier covariance of left and right matrix dilation, including the inverse trace-dual action and its exact determinant-norm factor.
- PROVENANCE-END
-/

/-!
# Fourier covariance on adelic matrices

The action X to a X b is represented on the vector of entries by a
Kronecker product. Under the additive trace pairing, its inverse
dual action takes Y to b inverse Y a inverse. The normalized additive
measure contributes the inverse determinant norm.

In the determinant-one coordinates of the zeta integral, the
measure factor at logarithmic determinant t is exp(-n t).
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory

variable {R : Type*} [CommRing R] {n : Nat}

def godementJacquetMatrixDilation (a b : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup (Prod (Fin n) (Fin n)) R where
  val := Matrix.kroneckerMap (fun x y : R => x * y) b.val.transpose a.val
  inv := Matrix.kroneckerMap (fun x y : R => x * y) b.inv.transpose a.inv
  val_inv := by
    rw [<- Matrix.mul_kronecker_mul, <- Matrix.transpose_mul,
      b.inv_val, a.val_inv, Matrix.transpose_one, Matrix.one_kronecker_one]
  inv_val := by
    rw [<- Matrix.mul_kronecker_mul, <- Matrix.transpose_mul,
      b.val_inv, a.inv_val, Matrix.transpose_one, Matrix.one_kronecker_one]

theorem godementJacquetMatrixDilation_vec (a b : Matrix.GeneralLinearGroup (Fin n) R)
    (X : Matrix (Fin n) (Fin n) R) :
    (godementJacquetMatrixDilation a b).val.mulVec X.vec = (a.val * X * b.val).vec := by
  change (Matrix.kroneckerMap (fun x y : R => x * y) b.val.transpose a.val).mulVec X.vec = _
  simpa only [Matrix.transpose_transpose] using
    Matrix.kronecker_mulVec_vec a.val X b.val.transpose

theorem godementJacquetMatrixDilation_det (a b : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup.det (godementJacquetMatrixDilation a b) =
      (Matrix.GeneralLinearGroup.det a) ^ n * (Matrix.GeneralLinearGroup.det b) ^ n := by
  apply Units.ext
  change (Matrix.kroneckerMap (fun x y : R => x * y) b.val.transpose a.val).det = a.val.det ^ n * b.val.det ^ n
  rw [Matrix.det_kronecker, Matrix.det_transpose, Fintype.card_fin]
  exact mul_comm _ _

theorem godementJacquetMatrixDilation_trace
    (a b : Matrix.GeneralLinearGroup (Fin n) R) (X Y : Matrix (Fin n) (Fin n) R) :
    ((a.val * X * b.val) * Y).trace = (X * (b.val * Y * a.val)).trace := by
  calc
    ((a.val * X * b.val) * Y).trace = (a.val * (X * (b.val * Y))).trace := by
      simp only [mul_assoc]
    _ = ((X * (b.val * Y)) * a.val).trace := Matrix.trace_mul_comm _ _
    _ = (X * (b.val * Y * a.val)).trace := by simp only [mul_assoc]

theorem godementJacquetMatrixDilation_trace_dual
    (a b : Matrix.GeneralLinearGroup (Fin n) R) (X Y : Matrix (Fin n) (Fin n) R) :
    ((a.val * X * b.val) * (b.inv * Y * a.inv)).trace = (X * Y).trace := by
  rw [godementJacquetMatrixDilation_trace]
  have h : b.val * (b.inv * Y * a.inv) * a.val = Y := by
    rw [<- mul_assoc b.val (b.inv * Y) a.inv, <- mul_assoc b.val b.inv Y, b.val_inv,
      one_mul, mul_assoc Y a.inv a.val, a.inv_val, mul_one]
  rw [h]

variable (K : Type*) [Field K] [NumberField K]

theorem godementJacquetMatrixDilation_determinantNorm
    (a b : AdelicGeneralLinearGroup K n) :
    heckeIdelicNorm (Matrix.GeneralLinearGroup.det (godementJacquetMatrixDilation a b)) =
      adelicDeterminantNorm K n a ^ n * adelicDeterminantNorm K n b ^ n := by
  rw [godementJacquetMatrixDilation_det, map_mul, map_pow, map_pow]
  rfl

theorem godementJacquetThetaDilation_determinantNorm
    (hn : 0 < n) (t : Multiplicative Real) (a b : (adelicDeterminantLogNorm K n).ker) :
    heckeIdelicNorm (Matrix.GeneralLinearGroup.det
      (godementJacquetMatrixDilation
        (Inv.inv a.val * adelicDeterminantSection K n t) b.val)) =
      Real.exp ((n : Real) * Multiplicative.toAdd t) := by
  have hNorm (g : (adelicDeterminantLogNorm K n).ker) : adelicDeterminantNorm K n g.val = 1 := by
    have hLog : Real.log (adelicDeterminantNorm K n g.val) = 0 := g.property
    rw [<- Real.exp_log (adelicDeterminantNorm_pos K n g.val), hLog, Real.exp_zero]
  rw [godementJacquetMatrixDilation_determinantNorm, map_mul, map_inv, hNorm a, inv_one, one_mul,
    adelicDeterminantNorm_section K n hn, hNorm b, one_pow, mul_one, <- Real.exp_nat_mul]

section Fourier

private abbrev FourierAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

private abbrev FiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  [MeasurableSpace (FiniteAdeles K)] [BorelSpace (FiniteAdeles K)]

local instance : MeasurableSpace (FourierAdeles K) :=
  inferInstanceAs (MeasurableSpace (Prod (InfiniteAdeleRing K) (FiniteAdeles K)))

/-- Reshape the vector of column-ordered entries into an adelic matrix. -/
def godementJacquetMatrixFromVec {A : Type*} (v : Prod (Fin n) (Fin n) -> A) :
    Matrix (Fin n) (Fin n) A :=
  fun i j => v (Prod.mk j i)

theorem godementJacquetMatrixFromVec_vec {A : Type*} (v : Prod (Fin n) (Fin n) -> A) :
    (godementJacquetMatrixFromVec v).vec = v := by
  funext p
  cases p
  rfl

omit [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  [MeasurableSpace (FiniteAdeles K)] [BorelSpace (FiniteAdeles K)] in
private theorem matrixFromVec_dilation (a b : AdelicGeneralLinearGroup K n)
    (v : Prod (Fin n) (Fin n) -> FourierAdeles K) :
    godementJacquetMatrixFromVec ((godementJacquetMatrixDilation a b).val.mulVec v) =
      a.val * godementJacquetMatrixFromVec v * b.val := by
  apply Matrix.vec_inj.mp
  rw [godementJacquetMatrixFromVec_vec, <- godementJacquetMatrixDilation_vec, godementJacquetMatrixFromVec_vec]

private def matrixFourierIntegrand
    (phi : Matrix (Fin n) (Fin n) (FourierAdeles K) -> Complex)
    (Y : Matrix (Fin n) (Fin n) (FourierAdeles K))
    (v : Prod (Fin n) (Fin n) -> FourierAdeles K) : Complex :=
  phi (godementJacquetMatrixFromVec v) * (heckeAdeleAddChar (-(godementJacquetMatrixFromVec v * Y).trace) : Complex)

/-- Fourier transform with respect to the additive trace pairing on matrices. -/
def godementJacquetMatrixFourier
    (phi : Matrix (Fin n) (Fin n) (FourierAdeles K) -> Complex)
    (Y : Matrix (Fin n) (Fin n) (FourierAdeles K)) : Complex :=
  integral (Measure.pi (fun _ : Prod (Fin n) (Fin n) => heckeAdeleAdditiveHaar (K := K)))
    (matrixFourierIntegrand K phi Y)

/-- Left and right dilation sends the frequency to the inverse trace-dual
dilation and scales the transform by the inverse determinant norm. -/
theorem godementJacquetMatrixFourier_dilate
    (phi : Matrix (Fin n) (Fin n) (FourierAdeles K) -> Complex) (hphi : Continuous phi)
    (a b : AdelicGeneralLinearGroup K n) (Y : Matrix (Fin n) (Fin n) (FourierAdeles K)) :
    godementJacquetMatrixFourier K (fun X => phi (a.val * X * b.val)) Y =
      HSMul.hSMul (Real.toNNReal (heckeIdelicNorm
        (Inv.inv (Matrix.GeneralLinearGroup.det (godementJacquetMatrixDilation a b)))))
        (godementJacquetMatrixFourier K phi (b.inv * Y * a.inv)) := by
  let e : Homeomorph (InfiniteAdeleRing K) (mixedEmbedding.mixedSpace K) :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
      continuous_toFun := continuous_heckeInfiniteAdele_mixedSpace (K := K)
      continuous_invFun := continuous_heckeInfiniteAdele_mixedSpace_symm K }
  let : SecondCountableTopology (InfiniteAdeleRing K) :=
    e.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (FiniteAdeles K) := secondCountableTopology_heckeFiniteAdeles K
  let : SecondCountableTopology (FourierAdeles K) :=
    inferInstanceAs (SecondCountableTopology (Prod (InfiniteAdeleRing K) (FiniteAdeles K)))
  let : BorelSpace (FourierAdeles K) :=
    inferInstanceAs (BorelSpace (Prod (InfiniteAdeleRing K) (FiniteAdeles K)))
  let I := Prod (Fin n) (Fin n)
  let mu := Measure.pi (fun _ : I => heckeAdeleAdditiveHaar (K := K))
  let g := godementJacquetMatrixDilation a b
  let Y' := b.inv * Y * a.inv
  let F := matrixFourierIntegrand K phi Y'
  have hg : Measurable g.val.mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hmat : Continuous (godementJacquetMatrixFromVec : (I -> FourierAdeles K) ->
      Matrix (Fin n) (Fin n) (FourierAdeles K)) :=
    continuous_matrix (fun i j => continuous_apply (Prod.mk j i))
  have htr : Continuous (fun v : I -> FourierAdeles K => (godementJacquetMatrixFromVec v * Y').trace) :=
    (hmat.matrix_mul continuous_const).matrix_trace
  have hphase : Continuous (fun v : I -> FourierAdeles K =>
      (heckeAdeleAddChar (-(godementJacquetMatrixFromVec v * Y').trace) : Complex)) :=
    continuous_subtype_val.comp ((continuous_heckeAdeleAddChar (K := K)).comp htr.neg)
  have hF : StronglyMeasurable F := ((hphi.comp hmat).mul hphase).measurable.stronglyMeasurable
  have hD := (Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit
  have hd : hD.unit = Matrix.GeneralLinearGroup.det g :=
    Units.ext hD.unit_spec
  have hm : Measure.map g.val.mulVec mu =
      HSMul.hSMul (Real.toNNReal (heckeIdelicNorm (Inv.inv (Matrix.GeneralLinearGroup.det g)))) mu := by
    have h := map_adeleMatrix_mulVec_idelicNorm g.val g.isUnit
    rw [hd] at h
    exact h
  have hCov : matrixFourierIntegrand K (fun X => phi (a.val * X * b.val)) Y =
      Function.comp F g.val.mulVec := by
    funext v
    change phi (a.val * godementJacquetMatrixFromVec v * b.val) *
        (heckeAdeleAddChar (-(godementJacquetMatrixFromVec v * Y).trace) : Complex) =
      phi (godementJacquetMatrixFromVec (g.val.mulVec v)) *
        (heckeAdeleAddChar (-(godementJacquetMatrixFromVec (g.val.mulVec v) * Y').trace) : Complex)
    rw [matrixFromVec_dilation K a b v, godementJacquetMatrixDilation_trace_dual a b]
  unfold godementJacquetMatrixFourier
  rw [hCov]
  change integral mu (fun v => F (g.val.mulVec v)) =
    HSMul.hSMul (Real.toNNReal (heckeIdelicNorm (Inv.inv (Matrix.GeneralLinearGroup.det g))))
      (integral mu F)
  rw [<- integral_map_of_stronglyMeasurable hg hF, hm, integral_smul_nnreal_measure]

/-- On the determinant-one double quotient, the Fourier dilation at
logarithmic determinant t has measure factor exp(-n t). -/
theorem godementJacquetMatrixFourier_thetaDilation (hn : 0 < n)
    (t : Multiplicative Real) (a b : (adelicDeterminantLogNorm K n).ker)
    (phi : Matrix (Fin n) (Fin n) (FourierAdeles K) -> Complex) (hphi : Continuous phi)
    (Y : Matrix (Fin n) (Fin n) (FourierAdeles K)) :
    let u := Inv.inv a.val * adelicDeterminantSection K n t
    godementJacquetMatrixFourier K (fun X => phi (u.val * X * b.val.val)) Y =
      HSMul.hSMul (Real.toNNReal (Real.exp (-((n : Real) * Multiplicative.toAdd t))))
        (godementJacquetMatrixFourier K phi (b.val.inv * Y * u.inv)) := by
  dsimp only
  rw [godementJacquetMatrixFourier_dilate K phi hphi]
  rw [map_inv, godementJacquetThetaDilation_determinantNorm K hn t a b, Real.exp_neg]

end Fourier

end Robin1984.GRH
