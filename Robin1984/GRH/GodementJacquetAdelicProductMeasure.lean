import Robin1984.GRH.GodementJacquetCoordinates

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The archimedean and finite factorization of the adelic general linear group and uniqueness of Haar measure.
- Formalization note: Splits the actual adelic matrix group, determinant weight, and global Haar integral into archimedean and finite parts, with a positive normalization scalar for determinant coordinates.
- PROVENANCE-END
-/

/-!
# Product integration on the adelic matrix group

The adelic matrix group splits continuously into its archimedean and finite
components. Its determinant weight respects this splitting. Transporting
the product of the two Haar measures gives a measure for which separated
integrals factor exactly. The determinant-coordinate measure used in the
theta integral agrees up to a positive scalar.
-/

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace Robin1984.GRH

section

variable (J R S : Type*) [Fintype J] [DecidableEq J] [Semiring R] [Semiring S]

private def matrixRingProdEquiv :
    RingEquiv (Matrix J J (Prod R S)) (Prod (Matrix J J R) (Matrix J J S)) where
  toFun X := Prod.mk ((RingHom.fst R S).mapMatrix X) ((RingHom.snd R S).mapMatrix X)
  invFun X := Matrix.of (fun i j => Prod.mk (X.1 i j) (X.2 i j))
  left_inv _X := Matrix.ext (fun _ _ => Prod.ext rfl rfl)
  right_inv _X := Prod.ext (Matrix.ext (fun _ _ => rfl)) (Matrix.ext (fun _ _ => rfl))
  map_mul' X Y := Prod.ext ((RingHom.fst R S).mapMatrix.map_mul X Y)
    ((RingHom.snd R S).mapMatrix.map_mul X Y)
  map_add' X Y := Prod.ext ((RingHom.fst R S).mapMatrix.map_add X Y)
    ((RingHom.snd R S).mapMatrix.map_add X Y)

variable [TopologicalSpace R] [TopologicalSpace S]

private theorem continuous_matrixRingProdEquiv :
    Continuous (matrixRingProdEquiv J R S) := by
  have hR : Continuous (fun X : Matrix J J (Prod R S) => (RingHom.fst R S).mapMatrix X) := by
    apply continuous_matrix
    intro i j
    exact continuous_fst.comp ((continuous_apply j).comp (continuous_apply i))
  have hS : Continuous (fun X : Matrix J J (Prod R S) => (RingHom.snd R S).mapMatrix X) := by
    apply continuous_matrix
    intro i j
    exact continuous_snd.comp ((continuous_apply j).comp (continuous_apply i))
  exact hR.prodMk hS

private theorem continuous_matrixRingProdEquiv_symm :
    Continuous (matrixRingProdEquiv J R S).symm := by
  apply continuous_matrix
  intro i j
  change Continuous (fun X : Prod (Matrix J J R) (Matrix J J S) => Prod.mk (X.1 i j) (X.2 i j))
  have hR : Continuous (fun X : Matrix J J R => X i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have hS : Continuous (fun X : Matrix J J S => X i j) :=
    (continuous_apply j).comp (continuous_apply i)
  exact (hR.comp continuous_fst).prodMk (hS.comp continuous_snd)

private def matrixUnitsProdEquiv :
    ContinuousMulEquiv (Units (Matrix J J (Prod R S)))
      (Prod (Units (Matrix J J R)) (Units (Matrix J J S))) := by
  let e := matrixRingProdEquiv J R S
  let eU := Units.mapEquiv e.toMulEquiv
  refine {
    toMulEquiv := eU.trans MulEquiv.prodUnits
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  . exact Homeomorph.prodUnits.continuous_toFun.comp
      ((continuous_matrixRingProdEquiv J R S).units_map e.toMonoidHom)
  . exact ((continuous_matrixRingProdEquiv_symm J R S).units_map e.symm.toMonoidHom).comp
      Homeomorph.prodUnits.continuous_invFun

end

/-- The continuous multiplicative equivalence splitting an adelic matrix unit
into its archimedean and finite adelic components. -/
noncomputable def adelicGeneralLinearGroup_prod
    (K : Type*) [Field K] [NumberField K] (n : Nat) :
    ContinuousMulEquiv (AdelicGeneralLinearGroup K n)
      (Prod (Units (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)))
        (Units (Matrix (Fin n) (Fin n) (FiniteAdeleRing (RingOfIntegers K) K)))) :=
  matrixUnitsProdEquiv (Fin n) (InfiniteAdeleRing K) (FiniteAdeleRing (RingOfIntegers K) K)

/-- Both projections of the splitting act entrywise on the underlying matrix. -/
theorem adelicGeneralLinearGroup_prod_val
    (K : Type*) [Field K] [NumberField K] (n : Nat) (g : AdelicGeneralLinearGroup K n) (i j : Fin n) :
    And (((adelicGeneralLinearGroup_prod K n g).1.val i j) = (g.val i j).1)
      (((adelicGeneralLinearGroup_prod K n g).2.val i j) = (g.val i j).2) :=
  And.intro rfl rfl

/-- The norm of the adelic determinant is the product of its two component norms. -/
theorem adelicDeterminantNorm_prod
    (K : Type*) [Field K] [NumberField K] (n : Nat) (g : AdelicGeneralLinearGroup K n) :
    let e := adelicGeneralLinearGroup_prod K n
    adelicDeterminantNorm K n g =
      heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det (e g).1) *
        heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det (e g).2) := by
  intro e
  let A := InfiniteAdeleRing K
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let fA := RingHom.fst A F
  let fF := RingHom.snd A F
  have hA : Units.map fA.toMonoidHom (Matrix.GeneralLinearGroup.det g) =
      Matrix.GeneralLinearGroup.det (e g).1 := by
    apply Units.ext
    exact RingHom.map_det fA g.val
  have hF : Units.map fF.toMonoidHom (Matrix.GeneralLinearGroup.det g) =
      Matrix.GeneralLinearGroup.det (e g).2 := by
    apply Units.ext
    exact RingHom.map_det fF g.val
  change heckeInfiniteIdeleNorm (Units.map fA.toMonoidHom (Matrix.GeneralLinearGroup.det g)) *
    heckeFiniteIdeleNorm (Units.map fF.toMonoidHom (Matrix.GeneralLinearGroup.det g)) = _
  rw [hA, hF]

/-- The complex determinant weight separates because both component norms are positive. -/
theorem adelicDeterminantNorm_cpow_prod
    (K : Type*) [Field K] [NumberField K] (n : Nat) (g : AdelicGeneralLinearGroup K n)
    (z : Complex) :
    let e := adelicGeneralLinearGroup_prod K n
    (adelicDeterminantNorm K n g : Complex) ^ z =
      (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det (e g).1) : Complex) ^ z *
        (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det (e g).2) : Complex) ^ z := by
  intro e
  rw [adelicDeterminantNorm_prod K n g, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (heckeInfiniteIdeleNorm_pos _).le
    (heckeFiniteIdeleNorm_pos _).le z

section

open MeasureTheory

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

private abbrev ArchMatrixUnitGroup :=
  Units (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))

private abbrev FiniteMatrixUnitGroup :=
  Units (Matrix (Fin n) (Fin n) (FiniteAdeleRing (RingOfIntegers K) K))

local notation "G" => AdelicGeneralLinearGroup K n
local notation "A" => ArchMatrixUnitGroup K n
local notation "F" => FiniteMatrixUnitGroup K n

variable [MeasurableSpace (AdelicGeneralLinearGroup K n)] [BorelSpace (AdelicGeneralLinearGroup K n)]
  [MeasurableSpace (ArchMatrixUnitGroup K n)] [MeasurableSpace (FiniteMatrixUnitGroup K n)]
  [BorelSpace (Prod (ArchMatrixUnitGroup K n) (FiniteMatrixUnitGroup K n))]

/-- Transport the product of the two component measures to the adelic matrix group. -/
noncomputable def adelicMatrixProductHaar
    (muA : Measure A) (muF : Measure F) : Measure G :=
  Measure.map (adelicGeneralLinearGroup_prod K n).symm (muA.prod muF)

/-- The transported product of Haar measures is itself Haar. -/
theorem isHaarMeasure_adelicMatrixProductHaar
    [BorelSpace A] [BorelSpace F]
    (muA : Measure A) (muF : Measure F)
    [SFinite muA] [SFinite muF]
    [muA.IsHaarMeasure] [muF.IsHaarMeasure] :
    (adelicMatrixProductHaar K n muA muF).IsHaarMeasure := by
  let e := adelicGeneralLinearGroup_prod K n
  exact e.toMulEquiv.symm.isHaarMeasure_map (muA.prod muF)
    e.symm.continuous e.continuous

/-- A product of integrable functions on the two components is integrable on
the adelic matrix group and its integral is the product of their integrals. -/
theorem integrableAndIntegral_adelicMatrixProductHaar
    (muA : Measure A) (muF : Measure F) [SFinite muA] [SFinite muF]
    (f : A -> Complex) (g : F -> Complex) (hf : Integrable f muA) (hg : Integrable g muF) :
    let e := adelicGeneralLinearGroup_prod K n
    let h (x : G) := f (e x).1 * g (e x).2
    let m := adelicMatrixProductHaar K n muA muF
    And (Integrable h m) (integral m h = integral muA f * integral muF g) := by
  intro e h m
  let v : MeasurableEquiv G (Prod A F) := e.toHomeomorph.toMeasurableEquiv
  have hMap : MeasurePreserving v.symm (muA.prod muF) m :=
    { measurable := v.symm.measurable
      map_eq := rfl }
  have hComp : Integrable (fun x : Prod A F => h (v.symm x)) (muA.prod muF) := by
    change Integrable (fun x : Prod A F => f (v (v.symm x)).1 * g (v (v.symm x)).2) _
    simpa only [MeasurableEquiv.apply_symm_apply] using hf.mul_prod hg
  refine And.intro ((hMap.integrable_comp_emb v.symm.measurableEmbedding).mp hComp) ?_
  change integral (Measure.map v.symm (muA.prod muF)) h = _
  rw [integral_map_equiv v.symm]
  change integral (muA.prod muF) (fun x : Prod A F =>
    f (v (v.symm x)).1 * g (v (v.symm x)).2) = _
  simp only [MeasurableEquiv.apply_symm_apply]
  exact integral_prod_mul f g

/-- The determinant-coordinate Haar measure differs from the transported product
Haar measure by one positive real normalization scalar. -/
theorem adelicDeterminantProductMeasure_eq_smul_matrixProductHaar
    [BorelSpace A] [BorelSpace F]
    [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G]
    [MeasurableSpace (adelicDeterminantLogNorm K n).ker]
    [BorelSpace (adelicDeterminantLogNorm K n).ker]
    (hn : 0 < n)
    (mu : Measure (adelicDeterminantLogNorm K n).ker) [SFinite mu] [mu.IsHaarMeasure]
    (muA : Measure A) (muF : Measure F) [SFinite muA] [SFinite muF]
    [muA.IsHaarMeasure] [muF.IsHaarMeasure] :
    exists c : NNReal, And (0 < c)
      (adelicDeterminantProductMeasure K n hn mu =
        HSMul.hSMul c (adelicMatrixProductHaar K n muA muF)) := by
  let mD := adelicDeterminantProductMeasure K n hn mu
  let mP := adelicMatrixProductHaar K n muA muF
  let _ : mD.IsHaarMeasure := isHaarMeasure_adelicDeterminantProductMeasure K n hn mu
  let _ : mP.IsHaarMeasure := isHaarMeasure_adelicMatrixProductHaar K n muA muF
  exact Exists.intro (Measure.haarScalarFactor mD mP) (And.intro
    (Measure.haarScalarFactor_pos_of_isHaarMeasure mD mP)
    (Measure.isMulLeftInvariant_eq_smul_of_regular mD mP))

end

end Robin1984.GRH
