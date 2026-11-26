import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.Units
import Robin1984.GRH.GodementJacquetArchimedeanSchwartz
import Robin1984.GRH.HeckeEulerProduct

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The archimedean product of Godement-Jacquet zeta integrals.
- Formalization note: Factors a Gaussian zeta integral over the infinite completions with one positive Haar constant.
- PROVENANCE-END
-/

/-!
# The archimedean product of Gaussian zeta integrals

The archimedean matrix-unit group is the finite product of the matrix-unit
groups over the infinite completions. The normalized determinant, the
Gaussian Schwartz test, and a factored coefficient separate over those
places. Absolute integrability at all infinite places gives a global
integral equal to their product times a positive Haar constant.
-/

set_option autoImplicit false

open MeasureTheory NumberField
open scoped Classical RealInnerProductSpace

noncomputable section

namespace Robin1984.GRH

section

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "W" => InfinitePlace K
local notation "ArchM" => Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)
local notation "Mv" => (fun v : W => Matrix (Fin n) (Fin n) (InfinitePlace.Completion v))
local notation "G" => Units ArchM
local notation "Gv" => (fun v : W => Units (Mv v))

private def archMatrixPiRingEquiv : RingEquiv ArchM (forall v : W, Mv v) where
  toFun X v := (Pi.evalRingHom (fun w : W => w.Completion) v).mapMatrix X
  invFun A := Matrix.of (fun i j v => A v i j)
  left_inv _X := Matrix.ext (fun _ _ => rfl)
  right_inv _A := funext (fun _ => Matrix.ext (fun _ _ => rfl))
  map_mul' X Y := funext (fun v =>
    (Pi.evalRingHom (fun w : W => w.Completion) v).mapMatrix.map_mul X Y)
  map_add' X Y := funext (fun v =>
    (Pi.evalRingHom (fun w : W => w.Completion) v).mapMatrix.map_add X Y)

/-- The continuous multiplicative equivalence from the archimedean adelic
matrix group to the product of the matrix groups over the completions. -/
def archGeneralLinearGroup_pi : ContinuousMulEquiv G (forall v : W, Gv v) := by
  let e := archMatrixPiRingEquiv K n
  let u := ContinuousMulEquiv.piUnits (M := Mv)
  have hE : Continuous e := by
    apply continuous_pi
    intro v
    apply continuous_matrix
    intro i j
    exact (continuous_apply v).comp ((continuous_apply j).comp (continuous_apply i))
  have hE' : Continuous e.symm := by
    apply continuous_matrix
    intro i j
    apply continuous_pi
    intro v
    exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply v))
  exact {
    toMulEquiv := (Units.mapEquiv e.toMulEquiv).trans u.toMulEquiv
    continuous_toFun := u.continuous.comp (hE.units_map e.toMonoidHom)
    continuous_invFun := (hE'.units_map e.symm.toMonoidHom).comp u.symm.continuous }

omit [NumberField K] in
/-- The infinite-place projection is evaluation of each matrix entry. -/
theorem archGeneralLinearGroup_pi_val (g : G) (v : W) (i j : Fin n) :
    ((archGeneralLinearGroup_pi K n g) v).val i j = g.val i j v :=
  rfl

/-- The infinite idelic norm of a matrix determinant is the product of the
local determinant norms, with the infinite-place multiplicities. -/
theorem archDeterminantNorm_eq_prod (g : G) :
    heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) =
      Finset.univ.prod (fun v : W =>
        norm (Matrix.GeneralLinearGroup.det ((archGeneralLinearGroup_pi K n g) v)).val ^
          v.mult) := by
  apply Finset.prod_congr rfl
  intro v _
  let ev := Pi.evalRingHom (fun w : W => w.Completion) v
  change norm (ev (Matrix.det g.val)) ^ v.mult = _
  rw [RingHom.map_det ev g.val]
  rfl

set_option maxHeartbeats 900000 in
/-- On the product of the archimedean matrix groups, integrating a factored
integrable function with any Haar measure gives the product of the local
integrals times a fixed positive constant. -/
theorem exists_archMatrixHaar_prod_integral
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G]
    [forall v : W, MeasurableSpace (Gv v)] [forall v : W, BorelSpace (Gv v)]
    [BorelSpace (forall v : W, Gv v)]
    (mu : Measure G) [SFinite mu] [mu.IsHaarMeasure]
    (nu : forall v : W, Measure (Gv v)) [forall v : W, SigmaFinite (nu v)]
    [forall v : W, (nu v).IsHaarMeasure] :
    exists c : NNReal, And (0 < c)
      (forall f : forall v : W, Gv v -> Complex, (forall v, Integrable (f v) (nu v)) ->
        let h (g : G) := Finset.univ.prod (fun v => f v (archGeneralLinearGroup_pi K n g v))
        And (Integrable h mu)
          (integral mu h = HSMul.hSMul c (Finset.univ.prod (fun v => integral (nu v) (f v))))) := by
  let e := archGeneralLinearGroup_pi K n
  let q := e.toHomeomorph.toMeasurableEquiv
  let m := Measure.map q.symm (Measure.pi nu)
  let _ : m.IsHaarMeasure :=
    e.toMulEquiv.symm.isHaarMeasure_map (Measure.pi nu) e.symm.continuous e.continuous
  let c := Measure.haarScalarFactor mu m
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure mu m
  have hm : mu = HSMul.hSMul c m := Measure.isMulLeftInvariant_eq_smul_of_regular mu m
  refine Exists.intro c (And.intro hc ?_)
  intro f hf h
  have hMap : MeasurePreserving q.symm (Measure.pi nu) m :=
    { measurable := q.symm.measurable
      map_eq := rfl }
  have hComp : Integrable (Function.comp h q.symm) (Measure.pi nu) := by
    change Integrable (fun x => Finset.univ.prod (fun v => f v (q (q.symm x) v))) _
    simpa only [MeasurableEquiv.apply_symm_apply] using Integrable.fintype_prod_dep hf
  have hInt : Integrable h m := (hMap.integrable_comp_emb q.symm.measurableEmbedding).mp hComp
  rw [hm, integral_smul_nnreal_measure]
  refine And.intro hInt.smul_measure_nnreal ?_
  change HSMul.hSMul c (integral (Measure.map q.symm (Measure.pi nu)) h) = _
  rw [integral_map_equiv q.symm]
  congr 1
  change integral (Measure.pi nu) (fun x => Finset.univ.prod (fun v => f v (q (q.symm x) v))) = _
  simp only [MeasurableEquiv.apply_symm_apply]
  exact integral_fintype_prod_eq_prod f


omit [NumberField K] in
private theorem archNormAtPlace
    (x : InfiniteAdeleRing K) (v : W) :
    mixedEmbedding.normAtPlace v (InfiniteAdeleRing.ringEquiv_mixedSpace K x) = norm (x v) := by
  by_cases h : v.IsReal
  . rw [mixedEmbedding.normAtPlace_apply_of_isReal h, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    have hDist := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).dist_eq (x v) 0
    simpa only [map_zero, dist_zero_right] using hDist
  . have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    have hDist := (InfinitePlace.Completion.isometry_extensionEmbedding v).dist_eq (x v) 0
    simpa only [map_zero, dist_zero_right] using hDist

private theorem archDeterminantCpow_eq_prod (g : G) (z : Complex) :
    (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^ z =
      Finset.univ.prod (fun v : W =>
        ((norm (Matrix.GeneralLinearGroup.det ((archGeneralLinearGroup_pi K n g) v)).val ^
          v.mult : Real) : Complex) ^ z) := by
  rw [archDeterminantNorm_eq_prod]
  let r (v : W) :=
    norm (Matrix.GeneralLinearGroup.det ((archGeneralLinearGroup_pi K n g) v)).val ^ v.mult
  change ((Finset.univ.prod r : Real) : Complex) ^ z = Finset.univ.prod (fun v => (r v : Complex) ^ z)
  have hr (v : W) : 0 <= r v := pow_nonneg (norm_nonneg _) _
  generalize (Finset.univ : Finset W) = S
  induction S using Finset.induction_on with
  | empty => simp
  | insert v S hv ih =>
    rw [Finset.prod_insert hv, Finset.prod_insert hv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr v) (Finset.prod_nonneg (fun w _ => hr w)), ih]

local notation "Ix" => Prod (Fin n) (Fin n)

/-- The local zeta density with the Gaussian, the matrix coefficient, and
the determinant norm normalized by the degree of the completion. -/
def archLocalGaussianZetaDensity
    (v : W) (s : Complex) (g : Gv v) (a : Complex) : Complex :=
  (Real.exp (-(v.mult : Real) * Real.pi *
    Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n => norm (g.val i j) ^ 2))) : Complex) *
    a * ((norm (Matrix.GeneralLinearGroup.det g).val ^ v.mult : Real) : Complex) ^
      (s + ((n : Complex) - 1) / 2)

private theorem archMinkowskiMatrixGaussian_on_GL (g : G) :
    (archMinkowskiMatrixGaussian K n)
      (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i)))) =
    Finset.univ.prod (fun v : W =>
      (Real.exp (-(v.mult : Real) * Real.pi * Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : Fin n =>
          norm (((archGeneralLinearGroup_pi K n g) v).val i j) ^ 2))) : Complex)) := by
  rw [archMinkowskiMatrixGaussian_factor]
  apply Finset.prod_congr rfl
  intro v _
  have hSum :
      (Finset.univ.sum (fun i : Ix =>
        mixedEmbedding.normAtPlace v (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i)) ^ 2)) =
      Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n =>
        norm (((archGeneralLinearGroup_pi K n g) v).val i j) ^ 2)) := by
    simp_rw [archNormAtPlace, archGeneralLinearGroup_pi_val]
    rw [<- Finset.univ_product_univ, Finset.sum_product]
    change (Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n =>
      norm (g.val j i v) ^ 2))) = _
    exact Finset.sum_comm
  rw [hSum]

private theorem archMinkowskiGaussianZeta_eq_prod
    (a : forall v : W, Gv v -> Complex) (coeff : G -> Complex)
    (hCoeff : forall g : G, coeff g =
      Finset.univ.prod (fun v : W => a v ((archGeneralLinearGroup_pi K n g) v)))
    (s : Complex) (g : G) :
    ((archMinkowskiMatrixGaussian K n)
        (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
          (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i)))) * coeff g) *
      (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
        (s + ((n : Complex) - 1) / 2) =
      Finset.univ.prod (fun v : W =>
        archLocalGaussianZetaDensity K n v s ((archGeneralLinearGroup_pi K n g) v)
          (a v ((archGeneralLinearGroup_pi K n g) v))) := by
  simp only [archLocalGaussianZetaDensity]
  rw [archMinkowskiMatrixGaussian_on_GL, hCoeff g, archDeterminantCpow_eq_prod,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]

set_option maxHeartbeats 1200000 in
/-- For a factored coefficient, local absolute integrability gives the
global archimedean Gaussian zeta integral as a product up to a positive
Haar constant independent of the complex parameter. -/
theorem exists_archGaussianZetaIntegral_of_integrable
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G]
    [forall v : W, MeasurableSpace (Gv v)] [forall v : W, BorelSpace (Gv v)]
    [BorelSpace (forall v : W, Gv v)]
    (mu : Measure G) [SFinite mu] [mu.IsHaarMeasure]
    (nu : forall v : W, Measure (Gv v)) [forall v : W, SigmaFinite (nu v)]
    [forall v : W, (nu v).IsHaarMeasure]
    (a : forall v : W, Gv v -> Complex) (coeff : G -> Complex)
    (hCoeff : forall g : G, coeff g =
      Finset.univ.prod (fun v : W => a v ((archGeneralLinearGroup_pi K n g) v))) :
    let localZeta (s : Complex) (v : W) (g : Gv v) :=
      archLocalGaussianZetaDensity K n v s g (a v g)
    let globalZeta (s : Complex) (g : G) :=
      ((archMinkowskiMatrixGaussian K n)
        (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
          (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i)))) * coeff g) *
        (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
          (s + ((n : Complex) - 1) / 2)
    exists c : NNReal, And (0 < c)
      (forall s : Complex, (forall v, Integrable (localZeta s v) (nu v)) ->
        And (Integrable (globalZeta s) mu)
          (integral mu (globalZeta s) =
            HSMul.hSMul c (Finset.univ.prod (fun v => integral (nu v) (localZeta s v))))) := by
  intro localZeta globalZeta
  choose c hc using exists_archMatrixHaar_prod_integral K n mu nu
  refine Exists.intro c (And.intro hc.1 ?_)
  intro s hInt
  have hEq : globalZeta s = fun g : G =>
      Finset.univ.prod (fun v : W => localZeta s v ((archGeneralLinearGroup_pi K n g) v)) :=
    funext (archMinkowskiGaussianZeta_eq_prod K n a coeff hCoeff s)
  rw [hEq]
  exact hc.2 (localZeta s) hInt


end

end Robin1984.GRH
