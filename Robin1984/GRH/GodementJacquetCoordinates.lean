import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Group.Matrix
import Robin1984.GRH.HeckeIdeleClassCoordinates

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and the determinant-norm coordinates in the global zeta integral.
- Formalization note: Splits the adelic general linear group by its positive determinant norm and rewrites the global zeta integral as a logarithmic Mellin integral.
- PROVENANCE-END
-/

/-!
# Determinant coordinates for the Godement-Jacquet zeta integral

For positive rank, a central scalar section splits the determinant norm.
The principal matrices have norm one. Lebesgue measure on the logarithmic
coordinate and Haar measure on the norm-one group give Haar measure on the
full group. In these coordinates the standard zeta integral is a Mellin
integral with exponent `s + (n - 1) / 2`.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

/-- The general linear group over the adele ring of the number field. -/
abbrev AdelicGeneralLinearGroup :=
  Matrix.GeneralLinearGroup (Fin n) (AdeleRing (RingOfIntegers K) K)

/-- The diagonal embedding of rational into adelic invertible matrices. -/
def adelicPrincipalGeneralLinear :
    MonoidHom (Matrix.GeneralLinearGroup (Fin n) K) (AdelicGeneralLinearGroup K n) :=
  Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (RingOfIntegers K) K))

/-- The idelic absolute value of a matrix determinant. -/
def adelicDeterminantNorm : MonoidHom (AdelicGeneralLinearGroup K n) Real :=
  heckeIdelicNorm.comp Matrix.GeneralLinearGroup.det

theorem adelicDeterminantNorm_pos (g : AdelicGeneralLinearGroup K n) :
    0 < adelicDeterminantNorm K n g :=
  heckeIdelicNorm_pos (Matrix.GeneralLinearGroup.det g)

/-- The principal general linear group is closed in the adelic group. -/
theorem isClosed_range_adelicPrincipalGeneralLinear :
    IsClosed (Set.range (adelicPrincipalGeneralLinear K n)) := by
  let A := AdeleRing (RingOfIntegers K) K
  let f := algebraMap K A
  let _ : TopologicalSpace K := TopologicalSpace.induced f inferInstance
  have hf : Topology.IsClosedEmbedding f :=
    { eq_induced := rfl
      injective := AdeleRing.algebraMap_injective (RingOfIntegers K) K
      isClosed_range := isClosed_principalAdeles K }
  have hc := hf.continuous
  let _ : IsTopologicalRing K :=
    { continuous_add := hf.isInducing.continuous_iff.mpr (by
        simp only [Function.comp_def, map_add]
        exact (hc.comp continuous_fst).add (hc.comp continuous_snd))
      continuous_mul := hf.isInducing.continuous_iff.mpr (by
        simp only [Function.comp_def, map_mul]
        exact (hc.comp continuous_fst).mul (hc.comp continuous_snd))
      continuous_neg := hf.isInducing.continuous_iff.mpr (by
        simp only [Function.comp_def, map_neg]
        exact hc.neg) }
  let H := AdeleRing.principalSubgroup (RingOfIntegers K) K
  let _ : DiscreteTopology H := discreteTopology_principalAdeles K
  let toH : K -> H := fun x => Subtype.mk (f x) (Exists.intro x rfl)
  have hToH : Continuous toH := hc.subtype_mk _
  let _ : DiscreteTopology K := DiscreteTopology.of_continuous_injective hToH
    (fun _ _ h => hf.injective (congrArg Subtype.val h))
  exact (hf.generalLinearGroup_map (n := Fin n)).isClosed_range

/-- The product formula makes every principal determinant have norm one. -/
theorem adelicDeterminantNorm_principal (g : Matrix.GeneralLinearGroup (Fin n) K) :
    adelicDeterminantNorm K n (adelicPrincipalGeneralLinear K n g) = 1 := by
  change heckeIdelicNorm (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (RingOfIntegers K) K)) g)) = 1
  rw [Matrix.GeneralLinearGroup.map_det]
  exact (mem_heckeNormOneIdeles K _).mp
    (heckePrincipalNormOneIdele K (Matrix.GeneralLinearGroup.det g)).property

/-- The logarithm of the determinant norm, with additive values written multiplicatively. -/
def adelicDeterminantLogNorm :
    MonoidHom (AdelicGeneralLinearGroup K n) (Multiplicative Real) where
  toFun g := Multiplicative.ofAdd (Real.log (adelicDeterminantNorm K n g))
  map_one' := by
    change Real.log (adelicDeterminantNorm K n 1) = 0
    rw [map_one, Real.log_one]
  map_mul' g h := by
    change Real.log (adelicDeterminantNorm K n (g * h)) =
      Real.log (adelicDeterminantNorm K n g) + Real.log (adelicDeterminantNorm K n h)
    rw [map_mul, Real.log_mul (adelicDeterminantNorm_pos K n g).ne'
      (adelicDeterminantNorm_pos K n h).ne']

/-- Central positive scalars normalized by the rank of the general linear group. -/
def adelicDeterminantSection :
    MonoidHom (Multiplicative Real) (AdelicGeneralLinearGroup K n) where
  toFun t := Matrix.GeneralLinearGroup.scalar (Fin n)
    (heckeIdelicExpSection K (Multiplicative.toAdd t / (n : Real)))
  map_one' := by
    change Matrix.GeneralLinearGroup.scalar (Fin n)
      (heckeIdelicExpSection K (0 / (n : Real))) = 1
    rw [zero_div, heckeIdelicExpSection_zero, map_one]
  map_mul' s t := by
    change Matrix.GeneralLinearGroup.scalar (Fin n)
      (heckeIdelicExpSection K ((Multiplicative.toAdd s + Multiplicative.toAdd t) / (n : Real))) = _
    rw [add_div, heckeIdelicExpSection_add, map_mul]

theorem adelicDeterminantSection_commute (t : Multiplicative Real) (g : AdelicGeneralLinearGroup K n) :
    Commute (adelicDeterminantSection K n t) g :=
  Matrix.GeneralLinearGroup.scalar_commute _ _

theorem adelicDeterminantNorm_section (hn : 0 < n) (t : Multiplicative Real) :
    adelicDeterminantNorm K n (adelicDeterminantSection K n t) =
      Real.exp (Multiplicative.toAdd t) := by
  have hn0 : Not ((n : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hn)
  change heckeIdelicNorm (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin n)
      (heckeIdelicExpSection K (Multiplicative.toAdd t / (n : Real))))) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow,
    heckeIdelicNorm_expSection, <- Real.exp_nat_mul]
  congr 1
  field_simp [hn0]

theorem adelicDeterminantLogNorm_section (hn : 0 < n) (t : Multiplicative Real) :
    adelicDeterminantLogNorm K n (adelicDeterminantSection K n t) = t := by
  change Real.log (adelicDeterminantNorm K n (adelicDeterminantSection K n t)) =
    Multiplicative.toAdd t
  rw [adelicDeterminantNorm_section K n hn, Real.log_exp]

theorem adelicDeterminantLogNorm_principal (g : Matrix.GeneralLinearGroup (Fin n) K) :
    adelicDeterminantLogNorm K n (adelicPrincipalGeneralLinear K n g) = 1 := by
  change Real.log (adelicDeterminantNorm K n (adelicPrincipalGeneralLinear K n g)) = 0
  rw [adelicDeterminantNorm_principal, Real.log_one]

/-- Principal matrices viewed inside the determinant-norm-one subgroup. -/
def adelicPrincipalDeterminantOne :
    MonoidHom (Matrix.GeneralLinearGroup (Fin n) K) (adelicDeterminantLogNorm K n).ker :=
  (adelicPrincipalGeneralLinear K n).codRestrict (adelicDeterminantLogNorm K n).ker
    (fun g => adelicDeterminantLogNorm_principal K n g)

def adelicDeterminantNormOnePart (hn : 0 < n) (g : AdelicGeneralLinearGroup K n) :
    (adelicDeterminantLogNorm K n).ker :=
  Subtype.mk (Inv.inv (adelicDeterminantSection K n (adelicDeterminantLogNorm K n g)) * g) (by
    change adelicDeterminantLogNorm K n
      (Inv.inv (adelicDeterminantSection K n (adelicDeterminantLogNorm K n g)) * g) = 1
    rw [map_mul, map_inv, adelicDeterminantLogNorm_section K n hn, inv_mul_cancel])

/-- The positive-rank group splits as a direct product with the logarithmic norm. -/
def adelicDeterminantCoordinates (hn : 0 < n) :
    MulEquiv (Prod (Multiplicative Real) (adelicDeterminantLogNorm K n).ker)
      (AdelicGeneralLinearGroup K n) where
  toFun p := adelicDeterminantSection K n p.1 * p.2.val
  invFun g := Prod.mk (adelicDeterminantLogNorm K n g) (adelicDeterminantNormOnePart K n hn g)
  left_inv p := by
    have hnorm : adelicDeterminantLogNorm K n (adelicDeterminantSection K n p.1 * p.2.val) =
        p.1 := by
      rw [map_mul, adelicDeterminantLogNorm_section K n hn, p.2.property, mul_one]
    apply Prod.ext hnorm
    apply Subtype.ext
    change Inv.inv (adelicDeterminantSection K n
      (adelicDeterminantLogNorm K n (adelicDeterminantSection K n p.1 * p.2.val))) *
      (adelicDeterminantSection K n p.1 * p.2.val) = p.2.val
    rw [hnorm, <- mul_assoc, inv_mul_cancel, one_mul]
  right_inv g := by
    change adelicDeterminantSection K n (adelicDeterminantLogNorm K n g) *
      (Inv.inv (adelicDeterminantSection K n (adelicDeterminantLogNorm K n g)) * g) = g
    rw [<- mul_assoc, mul_inv_cancel, one_mul]
  map_mul' p q := by
    let sectionHom := adelicDeterminantSection K n
    change sectionHom (p.1 * q.1) * (p.2.val * q.2.val) =
      (sectionHom p.1 * p.2.val) * (sectionHom q.1 * q.2.val)
    rw [map_mul]
    calc
      (sectionHom p.1 * sectionHom q.1) * (p.2.val * q.2.val) =
          sectionHom p.1 * (sectionHom q.1 * p.2.val) * q.2.val := by simp only [mul_assoc]
      _ = sectionHom p.1 * (p.2.val * sectionHom q.1) * q.2.val := by
        rw [(adelicDeterminantSection_commute K n q.1 p.2.val).eq]
      _ = (sectionHom p.1 * p.2.val) * (sectionHom q.1 * q.2.val) := by simp only [mul_assoc]

theorem adelicDeterminantCoordinates_principal (hn : 0 < n)
    (g : Matrix.GeneralLinearGroup (Fin n) K) :
    (adelicDeterminantCoordinates K n hn) (Prod.mk 1 (adelicPrincipalDeterminantOne K n g)) =
      adelicPrincipalGeneralLinear K n g := by
  change adelicDeterminantSection K n 1 * adelicPrincipalGeneralLinear K n g = _
  rw [map_one, one_mul]

theorem adelicDeterminantNorm_coordinates (hn : 0 < n) (t : Multiplicative Real)
    (k : (adelicDeterminantLogNorm K n).ker) :
    adelicDeterminantNorm K n ((adelicDeterminantCoordinates K n hn) (Prod.mk t k)) =
      Real.exp (Multiplicative.toAdd t) := by
  have hkLog : Real.log (adelicDeterminantNorm K n k.val) = 0 := k.property
  have hk : adelicDeterminantNorm K n k.val = 1 := by
    rw [<- Real.exp_log (adelicDeterminantNorm_pos K n k.val), hkLog, Real.exp_zero]
  change adelicDeterminantNorm K n (adelicDeterminantSection K n t * k.val) = _
  rw [map_mul, adelicDeterminantNorm_section K n hn, hk, mul_one]

/-- The zeta-integral weight in logarithmic determinant coordinates. -/
theorem adelicGodementJacquetWeight_coordinates (hn : 0 < n) (t : Multiplicative Real)
    (k : (adelicDeterminantLogNorm K n).ker) (s : Complex) :
    (adelicDeterminantNorm K n ((adelicDeterminantCoordinates K n hn) (Prod.mk t k)) : Complex) ^
        (s + ((n : Complex) - 1) / 2) =
      Complex.exp ((Multiplicative.toAdd t : Real) * (s + ((n : Complex) - 1) / 2)) := by
  rw [adelicDeterminantNorm_coordinates K n hn, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), <- Complex.ofReal_log (Real.exp_pos _).le,
    Real.log_exp]

theorem continuous_adelicDeterminantNorm :
    Continuous (adelicDeterminantNorm K n) :=
  continuous_heckeIdelicNorm.comp Matrix.GeneralLinearGroup.continuous_det

theorem continuous_adelicDeterminantSection :
    Continuous (fun t : Real => adelicDeterminantSection K n (Multiplicative.ofAdd t)) := by
  let A := AdeleRing (RingOfIntegers K) K
  let a : Real -> Units A := fun t => heckeIdelicExpSection K (t / (n : Real))
  have ha : Continuous a := (continuous_heckeIdelicExpSection K).comp
    (continuous_id.div_const (n : Real))
  have hscalar : Continuous (Matrix.scalar (Fin n) : A -> Matrix (Fin n) (Fin n) A) := by
    refine continuous_matrix (fun i j => ?_)
    by_cases h : i = j
    . simp only [Matrix.scalar_apply, Matrix.diagonal_apply, h, if_true]
      exact continuous_id'
    . simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, h, if_false] using
        (continuous_const : Continuous (fun _ : A => (0 : A)))
  refine Units.continuous_iff.mpr (And.intro ?_ ?_)
  . change Continuous (fun t : Real => Matrix.scalar (Fin n) (a t).val)
    exact hscalar.comp (Units.continuous_val.comp ha)
  . change Continuous (fun t : Real => (Inv.inv (Matrix.GeneralLinearGroup.scalar (Fin n)
        (a t))).val)
    simp only [<- map_inv]
    exact hscalar.comp (Units.continuous_val.comp ha.inv)

/-- The determinant-norm product is a homeomorphism in the adelic topology. -/
def adelicDeterminantHomeomorph (hn : 0 < n) :
    Homeomorph (Prod Real (adelicDeterminantLogNorm K n).ker)
      (AdelicGeneralLinearGroup K n) where
  toFun p := (adelicDeterminantCoordinates K n hn) (Prod.mk (Multiplicative.ofAdd p.1) p.2)
  invFun g := Prod.mk (Real.log (adelicDeterminantNorm K n g))
    (adelicDeterminantNormOnePart K n hn g)
  left_inv p :=
    congrArg (fun q : Prod (Multiplicative Real) (adelicDeterminantLogNorm K n).ker =>
      Prod.mk (Multiplicative.toAdd q.1) q.2) <|
        (adelicDeterminantCoordinates K n hn).left_inv (Prod.mk (Multiplicative.ofAdd p.1) p.2)
  right_inv g := (adelicDeterminantCoordinates K n hn).right_inv g
  continuous_toFun := (continuous_adelicDeterminantSection K n).comp continuous_fst |>.mul
    (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hlog : Continuous (fun g : AdelicGeneralLinearGroup K n =>
        Real.log (adelicDeterminantNorm K n g)) :=
      (continuous_adelicDeterminantNorm K n).log (fun g => (adelicDeterminantNorm_pos K n g).ne')
    have hpart : Continuous (adelicDeterminantNormOnePart K n hn) := by
      apply Continuous.subtype_mk
      exact ((continuous_adelicDeterminantSection K n).comp hlog).inv.mul continuous_id
    exact hlog.prodMk hpart

section Integration

open MeasureTheory

variable [MeasurableSpace (AdelicGeneralLinearGroup K n)]
  [BorelSpace (AdelicGeneralLinearGroup K n)]
  [MeasurableSpace (adelicDeterminantLogNorm K n).ker]
  [BorelSpace (adelicDeterminantLogNorm K n).ker]

/-- Haar normalization from Lebesgue measure and a measure on the norm-one group. -/
def adelicDeterminantProductMeasure (hn : 0 < n)
    (mu : Measure (adelicDeterminantLogNorm K n).ker) :
    Measure (AdelicGeneralLinearGroup K n) :=
  Measure.map (adelicDeterminantHomeomorph K n hn) ((volume : Measure Real).prod mu)

/-- With Haar measure on the norm-one group, the normalized product measure is Haar. -/
theorem isHaarMeasure_adelicDeterminantProductMeasure (hn : 0 < n)
    (mu : Measure (adelicDeterminantLogNorm K n).ker) [SFinite mu] [mu.IsHaarMeasure] :
    (adelicDeterminantProductMeasure K n hn mu).IsHaarMeasure := by
  let _ : MeasurableSpace (Multiplicative Real) := inferInstanceAs (MeasurableSpace Real)
  let _ : BorelSpace (Multiplicative Real) := inferInstanceAs (BorelSpace Real)
  let v : Measure (Multiplicative Real) := (volume : Measure Real)
  let _ : v.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure Real))
      toIsOpenPosMeasure := inferInstanceAs ((volume : Measure Real).IsOpenPosMeasure)
      map_mul_left_eq_self := fun t =>
        show Measure.map (fun x : Real => Multiplicative.toAdd t + x) (volume : Measure Real) =
            volume from Measure.IsAddLeftInvariant.map_add_left_eq_self (Multiplicative.toAdd t) }
  let _ : SFinite v := inferInstanceAs (SFinite (volume : Measure Real))
  let E := adelicDeterminantCoordinates K n hn
  let e := adelicDeterminantHomeomorph K n hn
  exact E.isHaarMeasure_map (v.prod mu) e.continuous e.symm.continuous

/-- Fubini rewrites the absolutely integrable zeta integral as a Mellin integral. -/
theorem integral_adelicGodementJacquet_eq_logMellin (hn : 0 < n)
    (mu : Measure (adelicDeterminantLogNorm K n).ker) [SFinite mu]
    (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (c : AdelicGeneralLinearGroup K n -> Complex) (s : Complex)
    (hInt : Integrable (fun g : AdelicGeneralLinearGroup K n =>
      (Phi g.val * c g) * ((adelicDeterminantNorm K n g : Real) : Complex) ^
        (s + ((n : Complex) - 1) / 2)) (adelicDeterminantProductMeasure K n hn mu)) :
    (integral (adelicDeterminantProductMeasure K n hn mu)
      (fun g : AdelicGeneralLinearGroup K n => (Phi g.val * c g) *
        ((adelicDeterminantNorm K n g : Real) : Complex) ^ (s + ((n : Complex) - 1) / 2))) =
      integral (volume : Measure Real) (fun t : Real =>
        (integral mu (fun k =>
          let g := (adelicDeterminantHomeomorph K n hn) (Prod.mk t k)
          Phi g.val * c g)) *
        Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2))) := by
  let e := (adelicDeterminantHomeomorph K n hn).toMeasurableEquiv
  let f : AdelicGeneralLinearGroup K n -> Complex := fun g =>
    (Phi g.val * c g) * ((adelicDeterminantNorm K n g : Real) : Complex) ^
      (s + ((n : Complex) - 1) / 2)
  change integral (Measure.map e ((volume : Measure Real).prod mu)) f = _
  rw [integral_map_equiv e f]
  have heInt : Integrable (fun p => f (e p)) ((volume : Measure Real).prod mu) :=
    (integrable_map_equiv e f).mp hInt
  rw [integral_prod (fun p => f (e p)) heInt]
  congr 1
  funext t
  have hw (k : (adelicDeterminantLogNorm K n).ker) :
      f (e (Prod.mk t k)) =
        (Phi (e (Prod.mk t k)).val * c (e (Prod.mk t k))) *
          Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2)) := by
    unfold f
    rw [show (adelicDeterminantNorm K n (e (Prod.mk t k)) : Complex) ^
        (s + ((n : Complex) - 1) / 2) =
          Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2)) from
        adelicGodementJacquetWeight_coordinates K n hn (Multiplicative.ofAdd t) k s]
  simp only [hw, integral_mul_const]
  rfl

end Integration

end Robin1984.GRH
