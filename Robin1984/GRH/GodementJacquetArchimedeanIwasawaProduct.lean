import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Robin1984.GRH.GodementJacquetArchimedeanIwasawaHaar
import Robin1984.GRH.ValuationUnitriangularMeasure

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Archimedean Iwasawa integration and Gaussian change of variables.
- Formalization note: Splits triangular Haar measure and computes upper-entry masses under diagonal scaling.
- PROVENANCE-END
-/

/-!
# Diagonal, unitriangular, and unitary integration

The upper-triangular multiplication law becomes a measure-preserving shear
in diagonal and unitriangular coordinates. Together with Iwasawa factorization,
this gives the product Haar measure formula up to a positive constant.
The additive product measure on the unitriangular entries then evaluates the
scaled Gaussian row by row.
-/

set_option autoImplicit false

open MeasureTheory

namespace Robin1984.GRH

section

variable (F : Type*) [RCLike F] (n : Nat)

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "A" => Units (Fin n -> F)
local notation "B" => valuationUpperTriangularSubgroup F n
local notation "N" => valuationUpperUnitriangularSubgroup F n
local notation "T" => positiveUpperTriangularMatrixSubgroup F n

/-- The diagonal units whose entries are positive real numbers. -/
def positiveDiagonalSubgroup : Subgroup A where
  carrier := Set.ofPred (fun a : A => forall i, exists r : Real, And (0 < r) (a.val i = (r : F)))
  one_mem' := by
    intro i
    exact Exists.intro 1 (And.intro zero_lt_one RCLike.ofReal_one.symm)
  mul_mem' := by
    intro a b ha hb i
    choose x hx using ha i
    choose y hy using hb i
    refine Exists.intro (x * y) (And.intro (mul_pos hx.1 hy.1) ?_)
    change a.val i * b.val i = ((x * y : Real) : F)
    rw [hx.2, hy.2, RCLike.ofReal_mul]
  inv_mem' := by
    intro a ha i
    choose x hx using ha i
    refine Exists.intro (Inv.inv x) (And.intro (inv_pos.mpr hx.1) ?_)
    have hp : a.val i * a.inv i = 1 := congrFun a.val_inv i
    rw [hx.2] at hp
    have hn : Not ((x : F) = 0) := fun h => (ne_of_gt hx.1) (RCLike.ofReal_eq_zero.mp h)
    have hv : a.inv i = (1 : F) / (x : F) :=
      (eq_div_iff hn).mpr ((mul_comm _ _).trans hp)
    change a.inv i = ((Inv.inv x : Real) : F)
    rw [hv, one_div, RCLike.ofReal_inv]

local notation "P" => positiveDiagonalSubgroup F n

/-- Positive triangular units have diagonal and unitriangular coordinates. -/
def positiveTriangularHomeomorph : Homeomorph T (Prod P N) := by
  let E := valuationTriangularHomeomorph F n
  let incl (t : T) : B := Subtype.mk t.val t.property.1
  let inc (p : Prod P N) : Prod A N := Prod.mk p.1.val p.2
  have hPos (t : T) : Membership.mem P (E (incl t)).1 := t.property.2
  have hT (p : Prod P N) : Membership.mem T (E.symm (inc p)).val := by
    refine And.intro (E.symm (inc p)).property ?_
    intro i
    have h := congrArg Prod.fst (E.apply_symm_apply (inc p))
    have hi : (E.symm (inc p)).val.val i i = p.1.val.val i :=
      congrArg (fun a : A => a.val i) h
    rw [hi]
    exact p.1.property i
  let f (t : T) : Prod P N :=
    Prod.mk (Subtype.mk (E (incl t)).1 (hPos t)) (E (incl t)).2
  let g (p : Prod P N) : T := Subtype.mk (E.symm (inc p)).val (hT p)
  refine
    { toEquiv := { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  . intro t
    apply Subtype.ext
    have ht : inc (f t) = E (incl t) := rfl
    change (E.symm (inc (f t))).val = t.val
    rw [ht, E.symm_apply_apply]
  . intro p
    have hp : incl (g p) = E.symm (inc p) := Subtype.ext rfl
    have he : E (incl (g p)) = inc p := by rw [hp, E.apply_symm_apply]
    apply Prod.ext
    . apply Subtype.ext
      exact congrArg Prod.fst he
    . change (E (incl (g p))).2 = (inc p).2
      exact congrArg (fun q : Prod A N => q.2) he
  . have hc : Continuous incl := continuous_subtype_val.subtype_mk _
    have he : Continuous (fun t : T => E (incl t)) := E.continuous.comp hc
    exact he.fst.subtype_mk (fun t => hPos t) |>.prodMk he.snd
  . have hc : Continuous inc := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact (continuous_subtype_val.comp (E.symm.continuous.comp hc)).subtype_mk _

open MeasureTheory MeasureTheory.Measure in
/-- Product Haar measure in diagonal and unitriangular coordinates is left Haar. -/
theorem isHaarMeasure_positiveTriangularProduct
    [SecondCountableTopology P] [SecondCountableTopology N]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace N] [BorelSpace N]
    [MeasurableSpace T] [BorelSpace T]
    (muP : Measure P) (muN : Measure N)
    [muP.IsHaarMeasure] [muN.IsHaarMeasure] [SFinite muP] [SFinite muN] :
    (Measure.map (positiveTriangularHomeomorph F n).symm (muP.prod muN)).IsHaarMeasure := by
  let E := positiveTriangularHomeomorph F n
  let EM := E.toMeasurableEquiv
  let d := valuationTriangularDiagonalHom F n
  let s := valuationDiagonalSection F n
  let m : Measure (Prod P N) := muP.prod muN
  let nu := m.comap EM
  have hMap : nu = Measure.map E.symm m := by
    apply Measure.ext
    intro a ha
    change m.comap EM a = Measure.map EM.symm m a
    rw [EM.measurableEmbedding.comap_apply, Measure.map_apply EM.symm.measurable ha]
    exact congrArg (fun t => m t) (Equiv.image_eq_preimage_symm EM.toEquiv a)
  have hInv : nu.IsMulLeftInvariant := by
    constructor
    intro t
    let tB : B := Subtype.mk t.val t.property.1
    let u0 : N := (E t).2
    let w (a : P) : N := Subtype.mk (Inv.inv (s a.val) * u0.val * s a.val) (by
      change d (Inv.inv (s a.val) * u0.val * s a.val) = 1
      have hh : d u0.val = 1 := u0.property
      rw [map_mul, map_mul, map_inv, hh, mul_one, inv_mul_cancel])
    have hs : Continuous (fun a : P => s a.val) :=
      (continuous_valuationDiagonalSection F n).comp continuous_subtype_val
    have hw : Continuous w := ((hs.inv.mul continuous_const).mul hs).subtype_mk _
    let S (p : Prod P N) : Prod P N := Prod.mk ((E t).1 * p.1) (w p.1 * p.2)
    have hShear : Measurable (fun p : Prod P N => w p.1 * p.2) :=
      ((hw.comp continuous_fst).mul continuous_snd).measurable
    have hS : MeasurePreserving S m m :=
      (measurePreserving_mul_left muP (E t).1).skew_product hShear
        (Filter.Eventually.of_forall (fun a => map_mul_left_eq_self muN (w a)))
    have hB : tB = s (E t).1.val * u0.val := by
      change tB = s (d tB) * (Inv.inv (s (d tB)) * tB)
      rw [mul_inv_cancel_left]
    have hConj (a : P) : s a.val * (w a).val = u0.val * s a.val := by
      change s a.val * (Inv.inv (s a.val) * u0.val * s a.val) = _
      rw [<- mul_assoc, mul_inv_cancel_left]
    have hRel : Function.comp (fun y : T => t * y) E.symm = Function.comp E.symm S := by
      funext p
      apply Subtype.ext
      change (tB * (s p.1.val * p.2.val)).val =
        (s ((E t).1.val * p.1.val) * ((w p.1).val * p.2.val)).val
      apply congrArg (fun x : B => x.val)
      calc
        _ = (s (E t).1.val * u0.val) * (s p.1.val * p.2.val) :=
          congrArg (fun x => x * _) hB
        _ = s (E t).1.val * ((u0.val * s p.1.val) * p.2.val) := by
          simp only [mul_assoc]
        _ = _ := by rw [map_mul, <- hConj p.1]; simp only [mul_assoc]
    have hLeft : Measurable (fun y : T => t * y) :=
      (continuous_const.mul continuous_id).measurable
    change Measure.map (fun y : T => t * y) nu = nu
    rw [hMap, Measure.map_map hLeft E.symm.continuous.measurable, hRel,
      <- Measure.map_map E.symm.continuous.measurable hS.measurable, hS.map_eq]
  rw [<- hMap]
  exact
    { toIsFiniteMeasureOnCompacts :=
        IsFiniteMeasureOnCompacts.comap' m E.continuous EM.measurableEmbedding
      toIsMulLeftInvariant := hInv
      toIsOpenPosMeasure := IsOpenPosMeasure.comap m E.isOpenEmbedding }

open MeasureTheory MeasureTheory.Measure in
/-- Matrix Haar measure is a positive multiple of the product of the diagonal,
unitriangular, and unitary Haar measures in the stated order. -/
theorem exists_pos_smul_map_fullArchimedeanIwasawaHaar
    [ProperSpace F] [SecondCountableTopology F]
    [SecondCountableTopology P] [SecondCountableTopology N]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace N] [BorelSpace N]
    [MeasurableSpace T] [BorelSpace T]
    [MeasurableSpace (Units M)] [BorelSpace (Units M)]
    [MeasurableSpace (Matrix.unitaryGroup (Fin n) F)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) F)]
    (mu : Measure (Units M)) [mu.IsHaarMeasure] [mu.InnerRegular]
    (muP : Measure P) (muN : Measure N) [muP.IsHaarMeasure] [muN.IsHaarMeasure]
    [SigmaFinite muP] [SigmaFinite muN]
    (muK : Measure (Matrix.unitaryGroup (Fin n) F)) [muK.IsHaarMeasure] [SFinite muK] :
    exists e : Homeomorph (Prod (Prod P N) (Matrix.unitaryGroup (Fin n) F)) (Units M),
      And (forall p, e p =
        ((valuationDiagonalSection F n p.1.1.val * p.1.2.val).val) *
          Unitary.toUnits (Inv.inv p.2))
        (exists c : NNReal, And (0 < c)
          (mu = HSMul.hSMul c (Measure.map e ((muP.prod muN).prod muK)))) := by
  let K := Matrix.unitaryGroup (Fin n) F
  let _ : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> F))
  let op : Homeomorph M (MulOpposite M) := MulOpposite.opHomeomorph
  let _ : SecondCountableTopology (MulOpposite M) := op.symm.isEmbedding.secondCountableTopology
  have hG : Topology.IsEmbedding (Units.embedProduct M) := Units.isEmbedding_embedProduct
  let _ : SecondCountableTopology (Units M) := hG.secondCountableTopology
  have hT : Topology.IsEmbedding (fun t : T => t.val) := Topology.IsEmbedding.subtypeVal
  let _ : SecondCountableTopology T := hT.secondCountableTopology
  have hK : Topology.IsEmbedding (fun k : K => k.val) := Topology.IsEmbedding.subtypeVal
  let _ : SecondCountableTopology K := hK.secondCountableTopology
  let E := positiveTriangularHomeomorph F n
  let m := Measure.map E.symm (muP.prod muN)
  let _ : m.IsHaarMeasure := isHaarMeasure_positiveTriangularProduct F n muP muN
  let _ : SigmaFinite m := E.symm.measurableEmbedding.sigmaFinite_map
  choose e he hScale using
    exists_pos_smul_map_archimedeanIwasawaHaar F n mu m muK
  let J : Homeomorph (Prod (Prod P N) K) (Prod T K) := E.symm.prodCongr (Homeomorph.refl K)
  let X : Homeomorph (Prod (Prod P N) K) (Units M) := J.trans e
  refine Exists.intro X (And.intro ?_ ?_)
  . intro p
    change e (J p) = _
    rw [he]
    rfl
  . choose c hc using hScale
    refine Exists.intro c (And.intro hc.1 ?_)
    have hA : MeasurePreserving J ((muP.prod muN).prod muK) (m.prod muK) := by
      have hE : MeasurePreserving E.symm (muP.prod muN) m :=
        { measurable := E.symm.continuous.measurable, map_eq := rfl }
      exact hE.prod (MeasurePreserving.id muK)
    have hM : Measure.map X ((muP.prod muN).prod muK) = Measure.map e (m.prod muK) := by
      change Measure.map (Function.comp e J) ((muP.prod muN).prod muK) = _
      rw [<- Measure.map_map e.continuous.measurable hA.measurable, hA.map_eq]
    rw [hM]
    exact hc.2

end


section

variable (F : Type*) [NormedField F] [NormedSpace Real F]

local notation "N" n => valuationUpperUnitriangularSubgroup F n

/-- A scalar test applied to the strict upper entries, scaled by their row. -/
noncomputable def archUnipotentScaledKernel (f : F -> Real) :
    (n : Nat) -> (Fin n -> Real) -> (N n) -> Real
  | 0, _, _ => 1
  | n + 1, a, u =>
    let p := valuationUnitriangularFirstRowHomeomorph F n u
    (archUnipotentScaledKernel f n (fun i => a i.succ) p.2) *
      Finset.univ.prod (fun j : Fin n => f (HSMul.hSMul (a 0) (p.1 j)))

variable [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]

local instance archUnipotentMeasurableSpace (n : Nat) : MeasurableSpace (N n) := borel (N n)
local instance archUnipotentBorelSpace (n : Nat) : BorelSpace (N n) := BorelSpace.mk rfl

omit [NormedSpace Real F] [MeasurableSpace F] [BorelSpace F] in
/-- The upper unitriangular group inherits a second-countable topology
from a second-countable scalar field. -/
theorem archUnipotent_secondCountable (n : Nat) :
    SecondCountableTopology (N n) := by
  let M := Matrix (Fin n) (Fin n) F
  let _ : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> F))
  let op : Homeomorph M (MulOpposite M) := MulOpposite.opHomeomorph
  let _ : SecondCountableTopology (MulOpposite M) := op.symm.isEmbedding.secondCountableTopology
  have hG : Topology.IsEmbedding (Units.embedProduct M) := Units.isEmbedding_embedProduct
  let _ : SecondCountableTopology (Units M) := hG.secondCountableTopology
  let _ : SecondCountableTopology (valuationUpperTriangularSubgroup F n) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      (fun b : valuationUpperTriangularSubgroup F n => b.val)).secondCountableTopology
  have hu : Topology.IsEmbedding (fun u : N n => u.val) := Topology.IsEmbedding.subtypeVal
  exact hu.secondCountableTopology

omit [NormedSpace Real F] in
private theorem measurePreserving_archUnipotentRow
    (mu : Measure F) [SigmaFinite mu] (n : Nat)
    [SecondCountableTopology (N n)] [SecondCountableTopology (N (n + 1))] :
    let E : Homeomorph (Prod (N n) (Fin n -> F)) (N (n + 1)) :=
      (Homeomorph.prodComm (N n) (Fin n -> F)).trans
        (valuationUnitriangularFirstRowHomeomorph F n).symm
    MeasurePreserving E ((valuationUnitriangularProductMeasure F mu n).prod
      (Measure.pi (fun _ : Fin n => mu))) (valuationUnitriangularProductMeasure F mu (n + 1)) := by
  let E : Homeomorph (Prod (N n) (Fin n -> F)) (N (n + 1)) :=
    (Homeomorph.prodComm (N n) (Fin n -> F)).trans
      (valuationUnitriangularFirstRowHomeomorph F n).symm
  exact { measurable := E.continuous.measurable, map_eq := rfl }

/-- Integrating all strict upper entries gives the product of the scalar integrals
and one inverse determinant factor for each entry's scaling. -/
theorem integral_archUnipotentScaledKernel
    [FiniteDimensional Real F] (mu : Measure F) [SigmaFinite mu] [mu.IsAddHaarMeasure]
    (f : F -> Real) (n : Nat) (a : Fin n -> Real)
    (ha : forall i, 0 <= a i) :
    (integral (valuationUnitriangularProductMeasure F mu n)
      (archUnipotentScaledKernel F f n a)) =
      Finset.univ.prod (fun i : Fin n =>
        ((Inv.inv (a i ^ Module.finrank Real F)) * integral mu f) ^ (n - (i.val + 1))) := by
  induction n with
  | zero => simp [archUnipotentScaledKernel, valuationUnitriangularProductMeasure]
  | succ n ih =>
    let _ : SecondCountableTopology (N n) := archUnipotent_secondCountable F n
    let _ : SecondCountableTopology (N (n + 1)) := archUnipotent_secondCountable F (n + 1)
    let _ := sigmaFinite_valuationUnitriangularProductMeasure F mu n
    let J := valuationUnitriangularFirstRowHomeomorph F n
    let E : Homeomorph (Prod (N n) (Fin n -> F)) (N (n + 1)) :=
      (Homeomorph.prodComm (N n) (Fin n -> F)).trans J.symm
    let tail := archUnipotentScaledKernel F f n (fun i => a i.succ)
    let row (p : Fin n -> F) := Finset.univ.prod (fun j : Fin n => f (HSMul.hSMul (a 0) (p j)))
    have hE : MeasurePreserving E ((valuationUnitriangularProductMeasure F mu n).prod
        (Measure.pi (fun _ : Fin n => mu))) (valuationUnitriangularProductMeasure F mu (n + 1)) :=
      measurePreserving_archUnipotentRow F mu n
    have hFun (p : Prod (N n) (Fin n -> F)) :
        archUnipotentScaledKernel F f (n + 1) a (E p) = tail p.1 * row p.2 := by
      have hPair : J (E p) = Prod.mk p.2 p.1 := J.apply_symm_apply _
      change tail (J (E p)).2 * row (J (E p)).1 = _
      rw [hPair]
    rw [<- hE.integral_comp E.measurableEmbedding]
    simp_rw [hFun]
    rw [integral_prod_mul]
    have hTail := ih (fun i => a i.succ) (fun i => ha i.succ)
    have hRow :
        integral (Measure.pi (fun _ : Fin n => mu)) row =
          ((Inv.inv (a 0 ^ Module.finrank Real F)) * integral mu f) ^ n := by
      unfold row
      calc
        _ = Finset.univ.prod (fun _ : Fin n => integral mu
            (fun x : F => f (HSMul.hSMul (a 0) x))) :=
          integral_fin_nat_prod_eq_prod
            (fun (_ : Fin n) (x : F) => f (HSMul.hSMul (a 0) x))
        _ = _ := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          apply congrArg (fun x : Real => x ^ n)
          simpa only [smul_eq_mul] using
            Measure.integral_comp_smul_of_nonneg mu f (a 0) (hR := ha 0)
    rw [hTail, hRow, Fin.prod_univ_succ, mul_comm]
    simp only [Fin.val_zero, zero_add, Nat.sub_zero, Fin.val_succ,
      Nat.succ_sub_succ_eq_sub]

open MeasureTheory.Measure in
omit [NormedSpace Real F] in
/-- Product additive Haar measure on the strict upper entries is Haar
on the upper unitriangular group. -/
theorem isHaarMeasure_archUnipotentProduct
    (mu : Measure F) [SigmaFinite mu] [mu.IsAddHaarMeasure] (n : Nat) :
    (valuationUnitriangularProductMeasure F mu n).IsHaarMeasure := by
  have hInv (m : Nat) : (valuationUnitriangularProductMeasure F mu m).IsMulLeftInvariant :=
    isMulLeftInvariant_valuationUnitriangularProductMeasure F mu m
  induction n with
  | zero =>
    change (Measure.dirac (1 : N 0)).IsHaarMeasure
    refine
      { toIsFiniteMeasureOnCompacts := inferInstance
        toIsMulLeftInvariant := hInv 0
        toIsOpenPosMeasure := ?_ }
    constructor
    intro S _ hS
    choose u hu using hS
    have hU : u = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      apply Matrix.ext
      intro i _
      exact Fin.elim0 i
    rw [hU] at hu
    rw [Measure.dirac_apply_of_mem hu]
    exact one_ne_zero
  | succ n ih =>
    let _ : (valuationUnitriangularProductMeasure F mu n).IsHaarMeasure := ih
    let _ : SecondCountableTopology (N n) := archUnipotent_secondCountable F n
    let _ : SecondCountableTopology (N (n + 1)) := archUnipotent_secondCountable F (n + 1)
    let _ := sigmaFinite_valuationUnitriangularProductMeasure F mu n
    let E : Homeomorph (Prod (N n) (Fin n -> F)) (N (n + 1)) :=
      (Homeomorph.prodComm (N n) (Fin n -> F)).trans
        (valuationUnitriangularFirstRowHomeomorph F n).symm
    let EM := E.toMeasurableEquiv
    let m := (valuationUnitriangularProductMeasure F mu n).prod (Measure.pi (fun _ : Fin n => mu))
    have hC : m.comap EM.symm = valuationUnitriangularProductMeasure F mu (n + 1) := by
      have hE : MeasurePreserving E m (valuationUnitriangularProductMeasure F mu (n + 1)) :=
        measurePreserving_archUnipotentRow F mu n
      rw [<- hE.map_eq]
      apply Measure.ext
      intro s hs
      change m.comap EM.symm s = Measure.map EM m s
      rw [EM.symm.measurableEmbedding.comap_apply, Measure.map_apply EM.measurable hs]
      exact congrArg (fun t => m t) (Equiv.image_eq_preimage_symm EM.symm.toEquiv s)
    refine
      { toIsMulLeftInvariant := hInv (n + 1)
        toIsFiniteMeasureOnCompacts := ?_
        toIsOpenPosMeasure := ?_ }
    . rw [<- hC]
      exact IsFiniteMeasureOnCompacts.comap' m E.symm.continuous EM.symm.measurableEmbedding
    . rw [<- hC]
      exact IsOpenPosMeasure.comap m E.symm.isOpenEmbedding

/-- An integrable scalar test stays integrable in the strict upper entries
when the row scales are positive. -/
theorem integrable_archUnipotentScaledKernel
    [FiniteDimensional Real F] (mu : Measure F) [SigmaFinite mu] [mu.IsAddHaarMeasure]
    (f : F -> Real) (hf : Integrable f mu) (n : Nat) (a : Fin n -> Real)
    (ha : forall i, 0 < a i) :
    Integrable (archUnipotentScaledKernel F f n a)
      (valuationUnitriangularProductMeasure F mu n) := by
  induction n with
  | zero =>
    change Integrable (fun _ : N 0 => (1 : Real)) (Measure.dirac 1)
    exact integrable_const _
  | succ n ih =>
    let _ : SecondCountableTopology (N n) := archUnipotent_secondCountable F n
    let _ : SecondCountableTopology (N (n + 1)) := archUnipotent_secondCountable F (n + 1)
    let _ := sigmaFinite_valuationUnitriangularProductMeasure F mu n
    let J := valuationUnitriangularFirstRowHomeomorph F n
    let E : Homeomorph (Prod (N n) (Fin n -> F)) (N (n + 1)) :=
      (Homeomorph.prodComm (N n) (Fin n -> F)).trans J.symm
    let tail := archUnipotentScaledKernel F f n (fun i => a i.succ)
    let row (p : Fin n -> F) := Finset.univ.prod (fun j : Fin n => f (HSMul.hSMul (a 0) (p j)))
    have hE : MeasurePreserving E ((valuationUnitriangularProductMeasure F mu n).prod
        (Measure.pi (fun _ : Fin n => mu))) (valuationUnitriangularProductMeasure F mu (n + 1)) :=
      measurePreserving_archUnipotentRow F mu n
    have hFun (p : Prod (N n) (Fin n -> F)) :
        archUnipotentScaledKernel F f (n + 1) a (E p) = tail p.1 * row p.2 := by
      have hPair : J (E p) = Prod.mk p.2 p.1 := J.apply_symm_apply _
      change tail (J (E p)).2 * row (J (E p)).1 = _
      rw [hPair]
    apply (hE.integrable_comp_emb E.measurableEmbedding).mp
    simp only [Function.comp_def, hFun]
    have hTail : Integrable tail (valuationUnitriangularProductMeasure F mu n) :=
      ih (fun i => a i.succ) (fun i => ha i.succ)
    have hRow : Integrable row (Measure.pi (fun _ : Fin n => mu)) :=
      Integrable.fintype_prod (fun _ : Fin n => hf.comp_smul (ne_of_gt (ha 0)))
    exact hTail.mul_prod hRow

end

section Gaussian

variable (F : Type*) [NormedField F] [InnerProductSpace Real F] [FiniteDimensional Real F]
  [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
  [SigmaFinite (volume : Measure F)]

/-- The scaled unitriangular Gaussian is integrable, with its integral given
by the product of the scalar Gaussian integrals and row scale factors. -/
theorem integrable_integral_archUnipotentGaussian
    (b : Real) (hb : 0 < b) (n : Nat) (a : Fin n -> Real) (ha : forall i, 0 < a i) :
    let g : F -> Real := fun x => Real.exp (-b * norm x ^ 2)
    let mu := valuationUnitriangularProductMeasure F volume n
    And (Integrable (archUnipotentScaledKernel F g n a) mu)
      (integral mu (archUnipotentScaledKernel F g n a) =
        Finset.univ.prod (fun i : Fin n =>
          (Inv.inv (a i ^ Module.finrank Real F) *
            Real.rpow (Real.pi / b) ((Module.finrank Real F : Real) / 2)) ^ (n - (i.val + 1)))) := by
  let g : F -> Real := fun x => Real.exp (-b * norm x ^ 2)
  have hbC : 0 < ((b : Complex).re) := hb
  have hG : Integrable g := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hbC 0 (0 : F)).re
    change Integrable (fun x : F =>
      Complex.re (Complex.exp (-(b : Complex) * ((norm x : Real) : Complex) ^ 2 +
        0 * ((inner Real (0 : F) x : Real) : Complex)))) at h
    simpa only [g, zero_mul, add_zero, <- Complex.ofReal_pow, <- Complex.ofReal_neg,
      <- Complex.ofReal_mul, <- Complex.ofReal_exp, Complex.ofReal_re] using h
  refine And.intro (integrable_archUnipotentScaledKernel F volume g hG n a ha) ?_
  have hi := integral_archUnipotentScaledKernel F volume g n a (fun i => (ha i).le)
  have hInt : integral volume g =
      Real.rpow (Real.pi / b) ((Module.finrank Real F : Real) / 2) :=
    GaussianFourier.integral_rexp_neg_mul_sq_norm hb
  rw [hInt] at hi
  exact hi

end Gaussian

section SiegelUnipotent

variable (F : Type*) [NormedField F] [NormedSpace Real F]

local notation "N" n => valuationUpperUnitriangularSubgroup F n

/-- Sum of the upper-entry log ratios, indexed by matrix rank. -/
def archUpperLogRatioSum : (n : Nat) -> (Fin n -> Real) -> Real
  | 0, _ => 0
  | n + 1, x => archUpperLogRatioSum n (fun i => x i.succ) +
    Finset.univ.sum (fun j : Fin n => x 0 - x j.succ)

/-- Test each upper unipotent entry after conjugation by the positive
diagonal with entries `exp (x i)`. -/
noncomputable def archUnipotentLogRatioKernel (f : F -> Real) :
    (n : Nat) -> (Fin n -> Real) -> (N n) -> Real
  | 0, _, _ => 1
  | n + 1, x, u =>
    let p := valuationUnitriangularFirstRowHomeomorph F n u
    (archUnipotentLogRatioKernel f n (fun i => x i.succ) p.2) *
      Finset.univ.prod (fun j : Fin n =>
        f (HSMul.hSMul (Real.exp (x 0 - x j.succ)) (p.1 j)))

variable [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional Real F]

local instance siegelUnipotentMeasurableSpace (n : Nat) : MeasurableSpace (N n) := borel (N n)
local instance siegelUnipotentBorelSpace (n : Nat) : BorelSpace (N n) := BorelSpace.mk rfl

set_option maxHeartbeats 750000 in
/-- The upper-entry Haar integral for a scalar product test after diagonal
conjugation. Each ratio contributes the negative real dimension in
the Jacobian, and there is one scalar integral per strict upper entry. -/
theorem integrable_integral_archUnipotentLogRatioKernel
    (mu : Measure F) [SigmaFinite mu] [mu.IsAddHaarMeasure]
    (f : F -> Real) (hf : Integrable f mu) (n : Nat) (x : Fin n -> Real) :
    let k := archUnipotentLogRatioKernel F f n x
    let d := (Module.finrank Real F : Real)
    let v := valuationUnitriangularProductMeasure F mu n
    And (Integrable k v) (integral v k =
      Real.exp (-d * archUpperLogRatioSum n x) * (integral mu f) ^ Nat.choose n 2) := by
  induction n with
  | zero =>
    change And (Integrable (fun _ : N 0 => (1 : Real)) (Measure.dirac 1))
      (integral (Measure.dirac (1 : N 0)) (fun _ => (1 : Real)) =
        Real.exp (-(Module.finrank Real F : Real) * 0) * (integral mu f) ^ Nat.choose 0 2)
    exact And.intro (integrable_const _) (by simp)
  | succ n ih =>
    let _ : SecondCountableTopology (N n) := archUnipotent_secondCountable F n
    let _ : SecondCountableTopology (N (n + 1)) := archUnipotent_secondCountable F (n + 1)
    let _ := sigmaFinite_valuationUnitriangularProductMeasure F mu n
    let J := valuationUnitriangularFirstRowHomeomorph F n
    let E : Homeomorph (Prod (N n) (Fin n -> F)) (N (n + 1)) :=
      (Homeomorph.prodComm (N n) (Fin n -> F)).trans J.symm
    let tail := archUnipotentLogRatioKernel F f n (fun i => x i.succ)
    let w (j : Fin n) := x 0 - x j.succ
    let row (p : Fin n -> F) := Finset.univ.prod
      (fun j : Fin n => f (HSMul.hSMul (Real.exp (w j)) (p j)))
    let d := (Module.finrank Real F : Real)
    let Z := integral mu f
    let A := archUpperLogRatioSum n (fun i => x i.succ)
    let B := Finset.univ.sum w
    have hE : MeasurePreserving E ((valuationUnitriangularProductMeasure F mu n).prod
        (Measure.pi (fun _ : Fin n => mu))) (valuationUnitriangularProductMeasure F mu (n + 1)) :=
      measurePreserving_archUnipotentRow F mu n
    have hFun (p : Prod (N n) (Fin n -> F)) :
        archUnipotentLogRatioKernel F f (n + 1) x (E p) = tail p.1 * row p.2 := by
      have hPair : J (E p) = Prod.mk p.2 p.1 := J.apply_symm_apply _
      change tail (J (E p)).2 * row (J (E p)).1 = _
      rw [hPair]
    have hTail := ih (fun i => x i.succ)
    have hRowI : Integrable row (Measure.pi (fun _ : Fin n => mu)) :=
      Integrable.fin_nat_prod (fun j : Fin n => hf.comp_smul (Real.exp_pos (w j)).ne')
    change And (Integrable (archUnipotentLogRatioKernel F f (n + 1) x)
      (valuationUnitriangularProductMeasure F mu (n + 1)))
      (integral (valuationUnitriangularProductMeasure F mu (n + 1))
        (archUnipotentLogRatioKernel F f (n + 1) x) =
        Real.exp (-d * (A + B)) * Z ^ Nat.choose (n + 1) 2)
    constructor
    . apply (hE.integrable_comp_emb E.measurableEmbedding).mp
      simp only [Function.comp_def, hFun]
      exact hTail.1.mul_prod hRowI
    . have hj (j : Fin n) :
          integral mu (fun u : F => f (HSMul.hSMul (Real.exp (w j)) u)) =
            Real.exp (-d * w j) * Z := by
        calc
          _ = Inv.inv ((Real.exp (w j)) ^ Module.finrank Real F) * Z := by
            simpa only [smul_eq_mul] using Measure.integral_comp_smul_of_nonneg
              mu f (Real.exp (w j)) (hR := (Real.exp_pos (w j)).le)
          _ = _ := by rw [<- Real.exp_nat_mul, neg_mul, Real.exp_neg]
      have hRow : integral (Measure.pi (fun _ : Fin n => mu)) row = Real.exp (-d * B) * Z ^ n := by
        unfold row
        rw [@integral_fin_nat_prod_eq_prod Real _ n (fun _ => F) _ (fun _ => mu) _
          (fun (j : Fin n) (u : F) => f (HSMul.hSMul (Real.exp (w j)) u))]
        simp_rw [hj]
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          <- Real.exp_sum, <- Finset.mul_sum]
      have hPow : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
        rw [show 2 = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      rw [<- hE.integral_comp E.measurableEmbedding]
      simp_rw [hFun]
      rw [integral_prod_mul, show integral (valuationUnitriangularProductMeasure F mu n) tail =
        Real.exp (-d * A) * Z ^ Nat.choose n 2 from hTail.2, hRow, hPow, pow_add]
      rw [show -d * (A + B) = -d * A + -d * B by ring, Real.exp_add]
      ring


/-- The unipotent coordinates whose upper entries remain in B after
conjugation by the log diagonal x. -/
def archUnipotentLogRatioBox (n : Nat) (x : Fin n -> Real) (B : Set F) :
    Set (N n) :=
  {u | forall i j : Fin n, i < j ->
    B.Mem (HSMul.hSMul (Real.exp (x i - x j)) (u.val.val.val i j))}

omit [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional Real F] in
/-- Closed entry constraints give a closed set in the diagonal and
unipotent chart, including the dependence on the diagonal coordinates. -/
theorem isClosed_archUnipotentLogRatioBox (n : Nat) (B : Set F) (hB : IsClosed B) :
    IsClosed {p : Prod (Fin n -> Real) (N n) |
      (archUnipotentLogRatioBox F n p.1 B).Mem p.2} := by
  have hV : Continuous (fun u : N n => u.val.val.val) :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val
  have h (i j : Fin n) : Continuous (fun p : Prod (Fin n -> Real) (N n) =>
      HSMul.hSMul (Real.exp (p.1 i - p.1 j)) (p.2.val.val.val i j)) :=
    (Real.continuous_exp.comp (((continuous_apply i).comp continuous_fst).sub
      ((continuous_apply j).comp continuous_fst))).smul ((hV.matrix_elem i j).comp continuous_snd)
  change IsClosed {p : Prod (Fin n -> Real) (N n) | forall i j : Fin n, i < j ->
    B.Mem (HSMul.hSMul (Real.exp (p.1 i - p.1 j)) (p.2.val.val.val i j))}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun _ =>
    hB.preimage (h i j))))

omit [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional Real F] in
private theorem mem_archUnipotentLogRatioBox_succ (n : Nat)
    (x : Fin (n + 1) -> Real) (B : Set F) (u : N (n + 1)) :
    let p := valuationUnitriangularFirstRowHomeomorph F n u
    (archUnipotentLogRatioBox F (n + 1) x B).Mem u <->
      And ((archUnipotentLogRatioBox F n (fun i => x i.succ) B).Mem p.2)
        (forall j : Fin n, B.Mem (HSMul.hSMul (Real.exp (x 0 - x j.succ)) (p.1 j))) := by
  intro p
  constructor
  . intro h
    exact And.intro (fun i j hij => h i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij))
      (fun j => h 0 j.succ (Fin.succ_pos j))
  . intro h i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j => exact h.2 j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hij).elim
      | succ j => exact h.1 i j (Fin.succ_lt_succ_iff.mp hij)

omit [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional Real F] in
/-- Testing the scalar indicator of B in each upper entry gives the
indicator of the entire conjugated unipotent box. -/
theorem archUnipotentLogRatioKernel_indicator (B : Set F) (n : Nat)
    (x : Fin n -> Real) (u : N n) :
    archUnipotentLogRatioKernel F (B.indicator (fun _ => (1 : Real))) n x u =
      (archUnipotentLogRatioBox F n x B).indicator (fun _ => 1) u := by
  induction n with
  | zero =>
    symm
    apply Set.indicator_of_mem
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    let p := valuationUnitriangularFirstRowHomeomorph F n u
    let tail := archUnipotentLogRatioBox F n (fun i => x i.succ) B
    let w (j : Fin n) := HSMul.hSMul (Real.exp (x 0 - x j.succ)) (p.1 j)
    let b := archUnipotentLogRatioBox F (n + 1) x B
    have hs : b.Mem u <-> And (tail.Mem p.2) (forall j, B.Mem (w j)) :=
      mem_archUnipotentLogRatioBox_succ F n x B u
    change archUnipotentLogRatioKernel F (B.indicator (fun _ => (1 : Real))) n
      (fun i => x i.succ) p.2 *
        Finset.univ.prod (fun j => B.indicator (fun _ => (1 : Real)) (w j)) =
      b.indicator (fun _ => 1) u
    rw [ih]
    by_cases ht : tail.Mem p.2
    . rw [Set.indicator_of_mem ht, one_mul]
      by_cases hr : forall j, B.Mem (w j)
      . rw [Set.indicator_of_mem (hs.mpr (And.intro ht hr))]
        simp only [Set.indicator_of_mem (hr _), Finset.prod_const_one]
      . rw [Set.indicator_of_notMem (fun h => hr (hs.mp h).2)]
        choose j hj using not_forall.mp hr
        exact Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)
    . rw [Set.indicator_of_notMem ht, zero_mul,
        Set.indicator_of_notMem (fun h => ht (hs.mp h).1)]


/-- The Haar measure of the strict upper-entry box at a fixed log diagonal.
The diagonal scales its volume by the product of the inverse entry Jacobians. -/
theorem measure_archUnipotentLogRatioBox
    (mu : Measure F) [SigmaFinite mu] [mu.IsAddHaarMeasure]
    (B : Set F) (hB : IsCompact B) (n : Nat) (x : Fin n -> Real) :
    valuationUnitriangularProductMeasure F mu n (archUnipotentLogRatioBox F n x B) =
      ENNReal.ofReal (Real.exp (-(Module.finrank Real F : Real) * archUpperLogRatioSum n x)) *
        (mu B) ^ Nat.choose n 2 := by
  let f := B.indicator (fun _ => (1 : Real))
  let v := valuationUnitriangularProductMeasure F mu n
  let b := archUnipotentLogRatioBox F n x B
  let d := (Module.finrank Real F : Real)
  let _ : SecondCountableTopology (N n) := archUnipotent_secondCountable F n
  have hBFin : mu B < Top.top := hB.measure_lt_top
  have hBm : MeasurableSet B := hB.isClosed.measurableSet
  have hbm : MeasurableSet b :=
    (isClosed_archUnipotentLogRatioBox F n B hB.isClosed).measurableSet.preimage
      (measurable_const.prodMk measurable_id)
  have hF : Integrable f mu :=
    (integrable_indicator_iff hBm).mpr (integrableOn_const hBFin.ne)
  have hk : archUnipotentLogRatioKernel F f n x = b.indicator (fun _ => 1) :=
    funext (archUnipotentLogRatioKernel_indicator F B n x)
  have h := integrable_integral_archUnipotentLogRatioKernel F mu f hF n x
  change And (Integrable (archUnipotentLogRatioKernel F f n x) v)
    (integral v (archUnipotentLogRatioKernel F f n x) =
      Real.exp (-d * archUpperLogRatioSum n x) * (integral mu f) ^ Nat.choose n 2) at h
  rw [hk] at h
  have hOn := (integrable_indicator_iff hbm).mp h.1
  have hbFin : v b < Top.top := by
    simpa using (integrableOn_const_iff (C := (1 : Real))).mp hOn
  have hi := h.2
  change integral v (b.indicator 1) =
    Real.exp (-d * archUpperLogRatioSum n x) * (integral mu (B.indicator 1)) ^ Nat.choose n 2 at hi
  rw [integral_indicator_one hbm, integral_indicator_one hBm] at hi
  change v b = _
  rw [<- ENNReal.ofReal_toReal hbFin.ne, <- show v.real b = (v b).toReal from rfl, hi,
    ENNReal.ofReal_mul (Real.exp_pos _).le, show mu.real B = (mu B).toReal from rfl,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hBFin.ne]

end SiegelUnipotent

end Robin1984.GRH
