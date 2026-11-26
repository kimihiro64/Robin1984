import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Robin1984.GRH.GodementJacquetArchimedeanSphericalLocal
import Robin1984.GRH.GodementJacquetArchimedeanZetaProduct

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The spherical archimedean factors of the standard Godement-Jacquet zeta integral.
- Formalization note: Transports the local spherical evaluations and constructs a global Schwartz test giving the exact product of Gamma factors.
- PROVENANCE-END
-/

/-!
# The normalized spherical archimedean Gamma product

The local spherical Gaussian integral is transported to each infinite
completion. The product formula and a single positive normalization
constant give a Schwartz test whose global archimedean zeta integral is
the product of the real and complex Gamma factors on the common
convergence half-plane.
-/

set_option autoImplicit false

open MeasureTheory NumberField
open scoped Classical Real RealInnerProductSpace

noncomputable section

namespace Robin1984.GRH

section

variable (F : Type*) [RCLike F] [ProperSpace F] [SecondCountableTopology F]
  [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
  [SigmaFinite (volume : Measure F)] (n : Nat)

local notation "ArchM" => Matrix (Fin n) (Fin n) F
local notation "Gl" => Units ArchM
local notation "Pos" => positiveDiagonalSubgroup F n
local notation "Tri" => positiveUpperTriangularMatrixSubgroup F n
local notation "U" => Matrix.unitaryGroup (Fin n) F
local notation "N" => valuationUpperUnitriangularSubgroup F n
local notation "Y" => (Fin n -> Real)
local notation "dF" => Module.finrank Real F

set_option maxHeartbeats 1000000 in
private theorem exists_pos_archSphericalStandardLocalIntegral
    [MeasurableSpace Pos] [BorelSpace Pos]
    [MeasurableSpace Tri] [BorelSpace Tri]
    [MeasurableSpace Gl] [BorelSpace Gl]
    [MeasurableSpace U] [BorelSpace U]
    (hd : Or (dF = 1) (dF = 2))
    (mu : Measure Gl) [mu.IsHaarMeasure] [mu.InnerRegular] [SFinite mu]
    (muU : Measure U) [muU.IsHaarMeasure] [IsProbabilityMeasure muU]
    (z : Fin n -> Complex) (v : Gl -> Complex)
    (hv : forall (r : Y) (_ : forall i, 0 < r i) (u : N) (q : U) (g : Gl),
      g.val = ((Matrix.diagonal (fun i => (r i : F)) * u.val.val.val) * q.val) ->
      v g = Finset.univ.prod (fun i : Fin n =>
        (r i : Complex) ^ ((dF : Complex) * z i +
          (dF : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2))) :
    let b := (dF : Real) * Real.pi
    let coeff (g : Gl) := integral muU (fun q : U => v (Unitary.toUnits q * g))
    let fac (w : Complex) := if dF = 1 then DedekindZeta.LReal w else DedekindZeta.LComplex w
    exists c : Real, And (0 < c)
      (forall (s : Complex) (_ : forall i, 0 < (s + z i).re),
        let a (g : Gl) := archMatrixGaussianZetaDensity dF b s g.val (coeff g)
        And (Integrable a mu) (integral mu a = (c : Complex) *
          Finset.univ.prod (fun i : Fin n => fac (s + z i)))) := by
  intro b coeff fac
  have hdPos : 0 < dF := by
    cases hd with
    | inl h => rw [h]; norm_num
    | inr h => rw [h]; norm_num
  have hb : 0 < b := mul_pos (Nat.cast_pos.mpr hdPos) Real.pi_pos
  choose C HC using exists_pos_archSphericalLocalIntegral_average
    F n mu muU b hb z v hv
  let t : Real := 1 / (2 * (dF : Real))
  have ht : 0 < t := one_div_pos.mpr (mul_pos two_pos (Nat.cast_pos.mpr hdPos))
  refine Exists.intro (C * t ^ n) (And.intro (mul_pos HC.1 (pow_pos ht _)) ?_)
  intro s hs a
  have H := HC.2 s hs
  refine And.intro H.1 ?_
  rw [H.2]
  have hRad (w : Complex) :
      HSMul.hSMul (Inv.inv (2 : Real))
        ((1 / (b : Complex)) ^ ((dF : Complex) * w / 2) *
          Complex.Gamma ((dF : Complex) * w / 2)) = (t : Complex) * fac w := by
    cases hd with
    | inl h =>
      have hFac : fac w = DedekindZeta.LReal w := by simp [fac, h]
      rw [hFac]
      simpa only [b, t, h, Nat.cast_one, one_mul, mul_one,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using sphericalRealRadialFactor w
    | inr h =>
      have h21 : Not ((2 : Nat) = 1) := by decide
      have h4 : (2 : Complex) * 2 = 4 := by norm_num
      simpa only [b, t, fac, h, if_neg h21, Nat.cast_ofNat, Complex.ofReal_div,
        Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, h4] using
        sphericalComplexRadialFactor w
  simp_rw [hRad]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]

end

section MatrixUnits

variable {D F : Type*} [NormedField D] [NormedField F] (n : Nat)

local notation "M1" => Matrix (Fin n) (Fin n) D
local notation "M2" => Matrix (Fin n) (Fin n) F

private def archMatrixRingEquiv (e : RingEquiv D F) : RingEquiv M1 M2 where
  toFun := e.toRingHom.mapMatrix
  invFun := e.symm.toRingHom.mapMatrix
  left_inv A := Matrix.ext (fun i j => e.symm_apply_apply (A i j))
  right_inv A := Matrix.ext (fun i j => e.apply_symm_apply (A i j))
  map_mul' := e.toRingHom.mapMatrix.map_mul
  map_add' := e.toRingHom.mapMatrix.map_add

private def archMatrixUnitsEquiv (e : RingEquiv D F) (he : Isometry e) :
    ContinuousMulEquiv (Units M1) (Units M2) := by
  let p := archMatrixRingEquiv n e
  have hei : Isometry e.symm := Isometry.of_dist_eq (fun x y => by
    rw [<- he.dist_eq (e.symm x) (e.symm y), e.apply_symm_apply, e.apply_symm_apply])
  have hp : Continuous p := by
    apply continuous_matrix
    intro i j
    exact he.continuous.comp ((continuous_apply j).comp (continuous_apply i))
  have hpi : Continuous p.symm := by
    apply continuous_matrix
    intro i j
    exact hei.continuous.comp ((continuous_apply j).comp (continuous_apply i))
  exact {
    toMulEquiv := Units.mapEquiv p.toMulEquiv
    continuous_toFun := hp.units_map p.toMonoidHom
    continuous_invFun := hpi.units_map p.symm.toMonoidHom }

private theorem archMatrixUnitsEquiv_val (e : RingEquiv D F) (he : Isometry e)
    (g : Units M1) (i j : Fin n) :
    (archMatrixUnitsEquiv n e he g).val i j = e (g.val i j) := rfl

private theorem archMatrixUnitsEquiv_det (e : RingEquiv D F) (he : Isometry e) (g : Units M1) :
    (Matrix.GeneralLinearGroup.det (archMatrixUnitsEquiv n e he g)).val =
      e (Matrix.GeneralLinearGroup.det g).val :=
  (RingHom.map_det e.toRingHom g.val).symm

end MatrixUnits

section Completion

variable {K : Type*} [Field K] (n : Nat)
  {F : Type*} [RCLike F]

local notation "Gf" => Units (Matrix (Fin n) (Fin n) F)
local notation "Gv" => (fun v : InfinitePlace K =>
  Units (Matrix (Fin n) (Fin n) (InfinitePlace.Completion v)))

private theorem archLocalGaussianZetaDensity_map
    (v : InfinitePlace K) (e : RingEquiv v.Completion F) (he : Isometry e)
    (hD : Module.finrank Real F = v.mult) (s : Complex) (g : Gv v) (a : Complex) :
    archLocalGaussianZetaDensity K n v s g a =
      archMatrixGaussianZetaDensity (Module.finrank Real F)
        ((Module.finrank Real F : Real) * Real.pi) s
        (archMatrixUnitsEquiv n e he g).val a := by
  have hNorm (x : v.Completion) : norm (e x) = norm x := by
    simpa only [map_zero, dist_zero_right] using he.dist_eq x 0
  rw [archLocalGaussianZetaDensity, archMatrixGaussianZetaDensity, hD, archFrobeniusSq]
  have hDet :
      (archMatrixUnitsEquiv n e he g).val.det = e g.val.det :=
    archMatrixUnitsEquiv_det n e he g
  rw [hDet, hNorm]
  simp_rw [archMatrixUnitsEquiv_val, hNorm]
  have hB : -(v.mult : Real) * Real.pi = -((v.mult : Real) * Real.pi) := by ring
  rw [hB]
  ac_rfl

set_option maxHeartbeats 1000000 in
private theorem archLocalGaussianZetaIntegral_map
    (v : InfinitePlace K) (e : RingEquiv v.Completion F) (he : Isometry e)
    (hD : Module.finrank Real F = v.mult)
    [MeasurableSpace (Gv v)] [BorelSpace (Gv v)]
    [MeasurableSpace Gf] [BorelSpace Gf]
    (mu : Measure Gf) (a : Gf -> Complex) (s : Complex) :
    let p := (archMatrixUnitsEquiv n e he).toHomeomorph.toMeasurableEquiv
    let nu := Measure.map p.symm mu
    let f (g : Gf) := archMatrixGaussianZetaDensity (Module.finrank Real F)
      ((Module.finrank Real F : Real) * Real.pi) s g.val (a g)
    let h (g : Gv v) := archLocalGaussianZetaDensity K n v s g (a (p g))
    Integrable f mu -> And (Integrable h nu) (integral nu h = integral mu f) := by
  intro p nu f h hf
  have hMap : MeasurePreserving p.symm mu nu :=
    { measurable := p.symm.measurable
      map_eq := rfl }
  have hEq : Function.comp h p.symm = f := by
    funext g
    change archLocalGaussianZetaDensity K n v s (p.symm g) (a (p (p.symm g))) = f g
    rw [MeasurableEquiv.apply_symm_apply]
    rw [archLocalGaussianZetaDensity_map n v e he hD s]
    have heq : archMatrixUnitsEquiv n e he (p.symm g) = g :=
      p.apply_symm_apply g
    rw [heq]
  have hI : Integrable (Function.comp h p.symm) mu := by rw [hEq]; exact hf
  refine And.intro ((hMap.integrable_comp_emb p.symm.measurableEmbedding).mp hI) ?_
  rw [show nu = Measure.map p.symm mu from rfl, integral_map_equiv p.symm]
  change integral mu (Function.comp h p.symm) = integral mu f
  rw [hEq]

/-- The canonical identification of a real completion with the real field
preserves distance. -/
theorem archRealCompletionIsometry (v : InfinitePlace K) (hv : v.IsReal) :
    Isometry (InfinitePlace.Completion.ringEquivRealOfIsReal hv) :=
  InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv

/-- The canonical identification of a complex completion with the complex field
preserves distance. -/
theorem archComplexCompletionIsometry (v : InfinitePlace K) (hv : v.IsComplex) :
    Isometry (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv) :=
  InfinitePlace.Completion.isometry_extensionEmbedding v

end Completion


section SphericalCompletion

variable (K : Type*) [Field K] (n : Nat)
  (F : Type*) [RCLike F] [ProperSpace F] [SecondCountableTopology F]
  [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
  [SigmaFinite (volume : Measure F)]

local notation "Gf" => Units (Matrix (Fin n) (Fin n) F)
local notation "Pos" => positiveDiagonalSubgroup F n
local notation "Tri" => positiveUpperTriangularMatrixSubgroup F n
local notation "U" => Matrix.unitaryGroup (Fin n) F
local notation "N" => valuationUpperUnitriangularSubgroup F n
local notation "Y" => (Fin n -> Real)
local notation "Gv" => (fun w : InfinitePlace K =>
  Units (Matrix (Fin n) (Fin n) (InfinitePlace.Completion w)))

set_option maxHeartbeats 1400000 in
private theorem exists_archCompletionSphericalIntegral
    (w : InfinitePlace K) (e : RingEquiv w.Completion F) (he : Isometry e)
    (hRank : Module.finrank Real F = w.mult)
    [MeasurableSpace Pos] [BorelSpace Pos]
    [MeasurableSpace Tri] [BorelSpace Tri]
    [MeasurableSpace Gf] [BorelSpace Gf]
    [MeasurableSpace U] [BorelSpace U]
    [MeasurableSpace (Gv w)] [BorelSpace (Gv w)]
    (mu : Measure Gf) [mu.IsHaarMeasure] [mu.InnerRegular] [SFinite mu]
    (muU : Measure U) [muU.IsHaarMeasure] [IsProbabilityMeasure muU]
    (z : Fin n -> Complex) (sec : Gf -> Complex)
    (hv : forall (r : Y) (_ : forall i, 0 < r i) (u : N) (q : U) (g : Gf),
      g.val = ((Matrix.diagonal (fun i => (r i : F)) * u.val.val.val) * q.val) ->
      sec g = Finset.univ.prod (fun i : Fin n =>
        (r i : Complex) ^ ((Module.finrank Real F : Complex) * z i +
          (Module.finrank Real F : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2))) :
    let p := (archMatrixUnitsEquiv n e he).toHomeomorph.toMeasurableEquiv
    let nu := Measure.map p.symm mu
    let coeff (g : Gf) := integral muU (fun q : U => sec (Unitary.toUnits q * g))
    let fac (x : Complex) := if w.IsReal then DedekindZeta.LReal x else DedekindZeta.LComplex x
    exists C : Real, And (0 < C)
      (forall (s : Complex) (_ : forall i, 0 < (s + z i).re),
        let weight (g : Gv w) := archLocalGaussianZetaDensity K n w s g (coeff (p g))
        And (Integrable weight nu) (integral nu weight =
          (C : Complex) * Finset.univ.prod (fun i : Fin n => fac (s + z i)))) := by
  classical
  intro p nu coeff fac
  have hd : Or (Module.finrank Real F = 1) (Module.finrank Real F = 2) := by
    rw [hRank]
    by_cases h : w.IsReal
    . exact Or.inl (InfinitePlace.mult_isReal (Subtype.mk w h))
    . exact Or.inr (InfinitePlace.mult_isComplex (Subtype.mk w (InfinitePlace.not_isReal_iff_isComplex.mp h)))
  choose C hC using exists_pos_archSphericalStandardLocalIntegral F n hd mu muU z sec hv
  refine Exists.intro C (And.intro hC.1 ?_)
  intro s hs weight
  have hLoc := hC.2 s hs
  have hL := archLocalGaussianZetaIntegral_map n w e he hRank mu coeff s hLoc.1
  refine And.intro hL.1 ?_
  rw [hL.2, hLoc.2]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : w.IsReal
  . have hD : Module.finrank Real F = 1 := hRank.trans (InfinitePlace.mult_isReal (Subtype.mk w h))
    simp [fac, h, hD]
  . have hD : Module.finrank Real F = 2 := hRank.trans
      (InfinitePlace.mult_isComplex (Subtype.mk w (InfinitePlace.not_isReal_iff_isComplex.mp h)))
    simp [fac, h, hD]

end SphericalCompletion

section CompletionRank

variable {K : Type*} [Field K]

/-- The real scalar field has the dimension prescribed by a real place. -/
theorem archRealCompletionRank (w : InfinitePlace K) (hw : w.IsReal) :
    Module.finrank Real Real = w.mult := by
  rw [Module.finrank_self, InfinitePlace.mult_isReal (Subtype.mk w hw)]

/-- The complex scalar field has the real dimension prescribed by a complex place. -/
theorem archComplexCompletionRank (w : InfinitePlace K) (hw : w.IsComplex) :
    Module.finrank Real Complex = w.mult := by
  rw [Complex.finrank_real_complex, InfinitePlace.mult_isComplex (Subtype.mk w hw)]

end CompletionRank



section

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "W" => InfinitePlace K
local notation "G" => Units (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))
local notation "Gv" => (fun v : W =>
  Units (Matrix (Fin n) (Fin n) (InfinitePlace.Completion v)))
local notation "Ix" => Prod (Fin n) (Fin n)
local notation "Arch" => PiLp 2 (fun _ : Ix => DedekindZeta.Theta.minkowskiSpace K)

set_option maxHeartbeats 1400000 in
private theorem exists_archSchwartz_exact_product
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G]
    [forall v : W, MeasurableSpace (Gv v)] [forall v : W, BorelSpace (Gv v)]
    [BorelSpace (forall v : W, Gv v)]
    (mu : Measure G) [SFinite mu] [mu.IsHaarMeasure]
    (nu : forall v : W, Measure (Gv v)) [forall v : W, SigmaFinite (nu v)]
    [forall v : W, (nu v).IsHaarMeasure]
    (a : forall v : W, Gv v -> Complex) (coeff : G -> Complex)
    (hCoeff : forall g : G, coeff g =
      Finset.univ.prod (fun v : W => a v ((archGeneralLinearGroup_pi K n g) v)))
    (tau : Real) (factor : W -> Complex -> Complex)
    (hLocal : forall v : W, exists c : Real, And (0 < c)
      (forall s : Complex, tau < s.re ->
        let f (g : Gv v) := archLocalGaussianZetaDensity K n v s g (a v g)
        And (Integrable f (nu v)) (integral (nu v) f = (c : Complex) * factor v s))) :
    exists f : SchwartzMap Arch Complex,
      forall s : Complex, tau < s.re ->
        let Z (g : G) :=
          (f (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
            (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i)))) * coeff g) *
            (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
              (s + ((n : Complex) - 1) / 2)
        And (Integrable Z mu) (integral mu Z = Finset.univ.prod (fun v => factor v s)) := by
  choose c hc using hLocal
  choose r hr using exists_archGaussianZetaIntegral_of_integrable K n mu nu a coeff hCoeff
  let C : Real := (r : Real) * Finset.univ.prod c
  have hC : 0 < C := mul_pos (NNReal.coe_pos.mpr hr.1) (Finset.prod_pos (fun v _ => (hc v).1))
  let q : Complex := (Inv.inv C : Real)
  let f : SchwartzMap Arch Complex := HSMul.hSMul q (archMinkowskiMatrixGaussian K n)
  refine Exists.intro f ?_
  intro s hs Z
  let raw (g : G) :=
    ((archMinkowskiMatrixGaussian K n)
      (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i)))) * coeff g) *
        (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
          (s + ((n : Complex) - 1) / 2)
  have hRaw := hr.2 s (fun v => ((hc v).2 s hs).1)
  have hRawInt : Integrable raw mu := hRaw.1
  have hEq : Z = fun g : G => q * raw g := by
    funext g
    simp only [Z, f, smul_apply, smul_eq_mul, raw]
    ring
  rw [hEq]
  refine And.intro (hRawInt.const_mul q) ?_
  have hRawIntegral : integral mu raw = (C : Complex) * Finset.univ.prod (fun v => factor v s) := by
    rw [hRaw.2]
    simp_rw [fun v => ((hc v).2 s hs).2]
    rw [Finset.prod_mul_distrib, <- Complex.ofReal_prod]
    change HSMul.hSMul (r : Real) (((Finset.univ.prod c : Real) : Complex) * _) = _
    rw [Complex.real_smul, show (C : Complex) =
      ((r : Real) : Complex) * ((Finset.univ.prod c : Real) : Complex) from Complex.ofReal_mul _ _,
      mul_assoc]
  rw [integral_const_mul, hRawIntegral]
  have hCN : Not ((C : Complex) = 0) := Complex.ofReal_ne_zero.mpr hC.ne'
  rw [show q = Inv.inv (C : Complex) from Complex.ofReal_inv C]
  field_simp [hCN]

end



section SphericalPlaceData

variable (K : Type*) [Field K] (n : Nat)

local notation "W" => InfinitePlace K
local notation "Gv" => (fun w : W => Units (Matrix (Fin n) (Fin n) (InfinitePlace.Completion w)))

/-- The spherical standard Gamma factor at an infinite place. -/
def archSphericalGammaFactor
    (w : W) (z : Fin n -> Complex) (s : Complex) : Complex :=
  Finset.univ.prod (fun i : Fin n =>
    if w.IsReal then DedekindZeta.LReal (s + z i) else DedekindZeta.LComplex (s + z i))

/-- The local spherical coefficient, its Haar measure, and its evaluated Gaussian
zeta integral at an infinite place. -/
structure ArchSphericalPlaceIntegral
    (w : W) (z : Fin n -> Complex) [MeasurableSpace (Gv w)] where
  haar : Measure (Gv w)
  isHaar : haar.IsHaarMeasure
  sigmaFinite : SigmaFinite haar
  coefficient : Gv w -> Complex
  scale : Real
  scale_pos : 0 < scale
  evaluation : forall s : Complex, (forall i, 0 < (s + z i).re) ->
    let f (g : Gv w) := archLocalGaussianZetaDensity K n w s g (coefficient g)
    And (Integrable f haar) (integral haar f = (scale : Complex) * archSphericalGammaFactor K n w z s)

variable (F : Type*) [RCLike F] [ProperSpace F] [SecondCountableTopology F]
  [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
  [SigmaFinite (volume : Measure F)]

local notation "Gf" => Units (Matrix (Fin n) (Fin n) F)
local notation "U" => Matrix.unitaryGroup (Fin n) F
local notation "N" => valuationUpperUnitriangularSubgroup F n
local notation "P" => positiveDiagonalSubgroup F n
local notation "T" => positiveUpperTriangularMatrixSubgroup F n

set_option maxHeartbeats 1600000 in
/-- Constructs the local integral data from a normalized spherical inducing
section and Haar measures on the scalar model of the completion. -/
def archSphericalPlaceIntegral_of_section
    (w : W) (e : RingEquiv w.Completion F) (he : Isometry e)
    (hRank : Module.finrank Real F = w.mult)
    [MeasurableSpace P] [BorelSpace P] [MeasurableSpace T] [BorelSpace T]
    [MeasurableSpace Gf] [BorelSpace Gf] [MeasurableSpace U] [BorelSpace U]
    [MeasurableSpace (Gv w)] [BorelSpace (Gv w)]
    (mu : Measure Gf) [mu.IsHaarMeasure] [mu.InnerRegular] [SigmaFinite mu]
    (muU : Measure U) [muU.IsHaarMeasure] [IsProbabilityMeasure muU]
    (z : Fin n -> Complex) (sec : Gf -> Complex)
    (hSec : forall (r : Fin n -> Real) (_ : forall i, 0 < r i) (u : N) (q : U) (g : Gf),
      g.val = ((Matrix.diagonal (fun i => (r i : F)) * u.val.val.val) * q.val) ->
      sec g = Finset.univ.prod (fun i : Fin n =>
        (r i : Complex) ^ ((Module.finrank Real F : Complex) * z i +
          (Module.finrank Real F : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2))) :
    ArchSphericalPlaceIntegral K n w z := by
  let E := archMatrixUnitsEquiv n e he
  let p := E.toHomeomorph.toMeasurableEquiv
  let nu : Measure (Gv w) := Measure.map p.symm mu
  let coeff (g : Gv w) := integral muU (fun q : U => sec (Unitary.toUnits q * p g))
  let h := exists_archCompletionSphericalIntegral K n F w e he hRank mu muU z sec hSec
  let c := Classical.choose h
  have hc := Classical.choose_spec h
  exact
    { haar := nu
      isHaar := E.toMulEquiv.symm.isHaarMeasure_map mu E.symm.continuous E.continuous
      sigmaFinite := p.symm.sigmaFinite_map
      coefficient := coeff
      scale := c
      scale_pos := hc.1
      evaluation := hc.2 }

end SphericalPlaceData

section SphericalProduct

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "W" => InfinitePlace K
local notation "G" => Units (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))
local notation "Gv" => (fun w : W => Units (Matrix (Fin n) (Fin n) (InfinitePlace.Completion w)))
local notation "Ix" => Prod (Fin n) (Fin n)
local notation "Arch" => PiLp 2 (fun _ : Ix => DedekindZeta.Theta.minkowskiSpace K)

set_option maxHeartbeats 2000000 in
/-- For a coefficient that factors into the supplied local spherical coefficients,
one fixed Schwartz test gives the exact global archimedean Gamma product on the
common convergence half-plane. -/
theorem exists_archSphericalSchwartz_exact_gamma_product
    [forall w : W, MeasurableSpace (Gv w)] [forall w : W, BorelSpace (Gv w)]
    [BorelSpace (forall w : W, Gv w)]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G]
    (mu : Measure G) [SFinite mu] [mu.IsHaarMeasure]
    (z : W -> Fin n -> Complex)
    (D : forall w : W, ArchSphericalPlaceIntegral K n w (z w))
    (tau : Real) (hSpec : forall (s : Complex), tau < s.re ->
      forall (w : W) (i : Fin n), 0 < (s + z w i).re)
    (coeff : G -> Complex)
    (hCoeff : forall g : G, coeff g =
      Finset.univ.prod (fun w : W => (D w).coefficient ((archGeneralLinearGroup_pi K n g) w))) :
    exists f : SchwartzMap Arch Complex,
      forall s : Complex, tau < s.re ->
        let Z (g : G) :=
          (f (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
            (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i)))) * coeff g) *
            (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
              (s + ((n : Complex) - 1) / 2)
        And (Integrable Z mu) (integral mu Z =
          Finset.univ.prod (fun w : W => archSphericalGammaFactor K n w (z w) s)) := by
  let nu (w : W) := (D w).haar
  let _ : forall w : W, SigmaFinite (nu w) := fun w => (D w).sigmaFinite
  let _ : forall w : W, (nu w).IsHaarMeasure := fun w => (D w).isHaar
  exact exists_archSchwartz_exact_product K n mu nu (fun w => (D w).coefficient) coeff hCoeff
    tau (fun w => archSphericalGammaFactor K n w (z w))
    (fun w => Exists.intro (D w).scale
      (And.intro (D w).scale_pos (fun s hs => (D w).evaluation s (hSpec s hs w))))

end SphericalProduct


section

variable (F : Type*) [RCLike F] [ProperSpace F] (n : Nat)

local notation "G" => Units (Matrix (Fin n) (Fin n) F)
local notation "Y" => (Fin n -> Real)
local notation "P" => positiveDiagonalSubgroup F n
local notation "N" => valuationUpperUnitriangularSubgroup F n
local notation "U" => Matrix.unitaryGroup (Fin n) F
local notation "T" => positiveUpperTriangularMatrixSubgroup F n

set_option maxHeartbeats 800000 in
/-- The normalized spherical inducing values for any exponent tuple are realized
by a section constructed from logarithmic Iwasawa coordinates. -/
theorem exists_archSphericalInducingSection (z : Fin n -> Complex) :
    exists sec : G -> Complex, forall (r : Y) (_ : forall i, 0 < r i)
      (u : N) (q : U) (g : G),
      g.val = ((Matrix.diagonal (fun i => (r i : F)) * u.val.val.val) * q.val) ->
      sec g = Finset.univ.prod (fun i : Fin n =>
        (r i : Complex) ^ ((Module.finrank Real F : Complex) * z i +
          (Module.finrank Real F : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2)) := by
  choose e he using exists_archimedeanIwasawaHomeomorph F n
  let D := positiveDiagonalExpHomeomorph F n
  let B := positiveTriangularHomeomorph F n
  let J : Homeomorph (Prod (Prod Y N) U) (Prod T U) :=
    ((D.prodCongr (Homeomorph.refl N)).trans B.symm).prodCongr (Homeomorph.refl U)
  let E := J.trans e
  have hE (p : Prod (Prod Y N) U) : (E p).val =
      (Matrix.diagonal (fun i : Fin n => (Real.exp (p.1.1 i) : F)) *
        p.1.2.val.val.val) * (Inv.inv p.2).val := by
    change (e (J p)).val = _
    rw [he]
    rfl
  let sec (g : G) := Finset.univ.prod (fun i : Fin n =>
    (Real.exp ((E.symm g).1.1 i) : Complex) ^
      ((Module.finrank Real F : Complex) * z i +
        (Module.finrank Real F : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2))
  refine Exists.intro sec ?_
  intro r hr u q g hg
  let p : Prod (Prod Y N) U := Prod.mk (Prod.mk (fun i => Real.log (r i)) u) (Inv.inv q)
  have hLogs : (fun i : Fin n => Real.exp (Real.log (r i))) = r :=
    funext (fun i => Real.exp_log (hr i))
  have hp : E p = g := by
    apply Units.ext
    rw [hE, hg]
    change (Matrix.diagonal (fun i => (Real.exp (Real.log (r i)) : F)) * u.val.val.val) *
      (Inv.inv (Inv.inv q)).val = _
    rw [inv_inv]
    exact congrArg (fun a : Y =>
      (Matrix.diagonal (fun i => (a i : F)) * u.val.val.val) * q.val) hLogs
  have hP : E.symm g = p := by rw [<- hp, E.symm_apply_apply]
  simp only [sec, hP]
  exact Finset.prod_congr rfl (fun i _ => by
    change (Real.exp (Real.log (r i)) : Complex) ^ _ = _
    rw [Real.exp_log (hr i)])

end

end Robin1984.GRH
