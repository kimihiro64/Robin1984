import Robin1984.GRH.GodementJacquetMellinIdentification
import Robin1984.GRH.GodementJacquetThetaAnalyticContinuation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and Tonelli disintegration over a fundamental domain.
- Formalization note: Transforms the original nonnegative zeta kernel into its periodized determinant-coordinate integral, then derives absolute integrability of the theta Mellin kernel.
- PROVENANCE-END
-/

/-!
# Absolute convergence in the matrix-coefficient Mellin identity

The nonnegative zeta kernel unfolds over both the determinant line and the
rational principal quotient. It dominates the norm of the theta kernel.
The resulting Mellin identity requires absolute convergence only for the
original zeta kernel, with measurable test data and summable theta series.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

/-- The nonnegative integral of a periodized three-variable kernel unfolds
against the fundamental-domain measure in the last variable. -/
theorem lintegral_restrictedPeriodizedTripleKernel_eq
    {G Gamma : Type*} [MeasurableSpace G]
    [Group Gamma] [Countable Gamma] [MulAction Gamma G] [MeasurableConstSMul Gamma G]
    (mu : Measure G) [SFinite mu] [SMulInvariantMeasure Gamma G mu]
    (D : Set G) (hD : IsFundamentalDomain Gamma D mu)
    (Q : Real -> G -> G -> ENNReal)
    (hQ : Measurable (fun p : Prod Real (Prod G G) => Q p.1 p.2.1 p.2.2)) :
    let nu := mu.restrict D
    lintegral ((volume : Measure Real).prod (nu.prod nu))
      (fun p : Prod Real (Prod G G) => tsum (fun a : Gamma => Q p.1 p.2.1 (SMul.smul a p.2.2))) =
      lintegral nu (fun A => lintegral (volume : Measure Real) (fun t => lintegral mu (Q t A))) := by
  let m : Measure Real := volume
  let nu := mu.restrict D
  let U (t : Real) (A B : G) := tsum (fun a : Gamma => Q t A (SMul.smul a B))
  have hA : Measurable (fun p : Prod Real (Prod G G) => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hB : Measurable (fun p : Prod Real (Prod G G) => p.2.2) :=
    measurable_snd.comp measurable_snd
  have hUa (a : Gamma) :
      Measurable (fun p : Prod Real (Prod G G) => Q p.1 p.2.1 (SMul.smul a p.2.2)) :=
    hQ.comp (measurable_fst.prodMk (hA.prodMk ((measurable_const_smul a).comp hB)))
  have hU : Measurable (fun p : Prod Real (Prod G G) => U p.1 p.2.1 p.2.2) :=
    Measurable.tsum hUa
  have hGamma (t : Real) (A : G) :
      lintegral nu (U t A) = lintegral mu (Q t A) := by
    have hm (a : Gamma) : Measurable (fun B : G => Q t A (SMul.smul a B)) :=
      (hUa a).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    exact (lintegral_tsum (fun a => (hm a).aemeasurable)).trans (hD.lintegral_eq_tsum'' (Q t A)).symm
  have hAssoc : Measurable (fun p : Prod (Prod Real G) G => U p.1.1 p.1.2 p.2) :=
    hU.comp (MeasurableEquiv.prodAssoc :
      MeasurableEquiv (Prod (Prod Real G) G) (Prod Real (Prod G G))).measurable
  have hFiber : Measurable (fun p : Prod Real G => lintegral nu (U p.1 p.2)) :=
    hAssoc.lintegral_prod_right'
  calc
    _ = lintegral m (fun t => lintegral (nu.prod nu) (fun p : Prod G G => U t p.1 p.2)) :=
      lintegral_prod _ hU.aemeasurable
    _ = lintegral m (fun t => lintegral nu (fun A => lintegral nu (U t A))) := by
      apply lintegral_congr
      intro t
      exact lintegral_prod _ (hU.comp (measurable_const.prodMk measurable_id)).aemeasurable
    _ = lintegral nu (fun A => lintegral m (fun t => lintegral nu (U t A))) :=
      lintegral_lintegral_swap (f := fun t A => lintegral nu (U t A)) hFiber.aemeasurable
    _ = _ := lintegral_congr (fun A => lintegral_congr (fun t => hGamma t A))

private theorem lintegral_tripleMiddleSection_eq {G : Type*} [MeasurableSpace G]
    (mu : Measure G) [SFinite mu] (Q : Real -> G -> G -> ENNReal)
    (hQ : Measurable (fun p : Prod Real (Prod G G) => Q p.1 p.2.1 p.2.2)) (A : G) :
    lintegral ((volume : Measure Real).prod mu) (fun p : Prod Real G => Q p.1 A p.2) =
      lintegral (volume : Measure Real) (fun t => lintegral mu (Q t A)) := by
  have hS : Measurable (fun p : Prod Real G => Q p.1 A p.2) :=
    hQ.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact lintegral_prod _ hS.aemeasurable

private abbrev ZetaTonelliGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker

private theorem secondCountableTopology_godementJacquetMatrixUnits
    (K : Type*) [Field K] [NumberField K] (n : Nat) :
    SecondCountableTopology (AdelicGeneralLinearGroup K n) := by
  let AInf := InfiniteAdeleRing K
  let AF := FiniteAdeleRing (RingOfIntegers K) K
  let AM := Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K)
  let E : Homeomorph AInf (NumberField.mixedEmbedding.mixedSpace K) :=
    { toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
      continuous_toFun := continuous_heckeInfiniteAdele_mixedSpace (K := K)
      continuous_invFun := continuous_heckeInfiniteAdele_mixedSpace_symm K }
  let : SecondCountableTopology AInf := E.isEmbedding.secondCountableTopology
  let : SecondCountableTopology AF := secondCountableTopology_heckeFiniteAdeles K
  let : SecondCountableTopology AM := inferInstanceAs
    (SecondCountableTopology (Fin n -> Fin n -> Prod AInf AF))
  let : SecondCountableTopology (MulOpposite AM) :=
    (MulOpposite.opHomeomorph (M := AM)).symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := AM)).secondCountableTopology

set_option maxHeartbeats 900000 in
/-- Tonelli's theorem unfolds the absolute kernel through both determinant
coordinates and the rational principal quotient. -/
theorem lintegral_godementJacquetPrincipalKernel_eq_unfolded
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (AdelicGeneralLinearGroup K n)] [BorelSpace (AdelicGeneralLinearGroup K n)]
    [MeasurableSpace (ZetaTonelliGroup K n)] [BorelSpace (ZetaTonelliGroup K n)]
    (mu : Measure (ZetaTonelliGroup K n)) [SFinite mu] [mu.IsHaarMeasure]
    (D : Set (ZetaTonelliGroup K n))
    (hD : IsFundamentalDomain (adelicPrincipalDeterminantOne K n).range D mu)
    (H : Prod (AdelicGeneralLinearGroup K n) (ZetaTonelliGroup K n) -> ENNReal)
    (hH : Measurable H) :
    let e := (adelicDeterminantHomeomorph K n hn).toMeasurableEquiv
    let nu := mu.restrict D
    lintegral ((volume : Measure Real).prod (nu.prod nu))
      (fun p : Prod Real (Prod (ZetaTonelliGroup K n) (ZetaTonelliGroup K n)) =>
        tsum (fun a : (adelicPrincipalDeterminantOne K n).range =>
          H (Prod.mk (Inv.inv p.2.1.val * e (Prod.mk p.1 (SMul.smul a p.2.2))) p.2.1))) =
      lintegral ((adelicDeterminantProductMeasure K n hn mu).prod nu) H := by
  let G : Type _ := ZetaTonelliGroup K n
  let L := AdelicGeneralLinearGroup K n
  let Gamma : Type _ := (adelicPrincipalDeterminantOne K n).range
  let : Countable Gamma := countable_adelicPrincipalDeterminantOne K n
  let e := (adelicDeterminantHomeomorph K n hn).toMeasurableEquiv
  let m : Measure Real := volume
  let M := adelicDeterminantProductMeasure K n hn mu
  let nu := mu.restrict D
  let : SFinite M := by
    change SFinite (Measure.map e (m.prod mu))
    infer_instance
  let : M.IsHaarMeasure := isHaarMeasure_adelicDeterminantProductMeasure K n hn mu
  let Q (t : Real) (A B : G) := H (Prod.mk (Inv.inv A.val * e (Prod.mk t B)) A)
  let U (t : Real) (A B : G) := tsum (fun a : Gamma => Q t A (SMul.smul a B))
  let : SecondCountableTopology L := secondCountableTopology_godementJacquetMatrixUnits K n
  let X := Prod Real (Prod G G)
  let E0 : Homeomorph (Prod Real G) L := adelicDeterminantHomeomorph K n hn
  have hVal : Continuous (Subtype.val : G -> L) := continuous_subtype_val
  have hSub : Topology.IsEmbedding (Subtype.val : G -> L) := Topology.IsEmbedding.subtypeVal
  let : SecondCountableTopology G := hSub.secondCountableTopology
  have hInv : Continuous (Inv.inv : L -> L) := continuous_inv
  have hA : Continuous (fun p : X => p.2.1) := continuous_fst.comp continuous_snd
  have hB : Continuous (fun p : X => p.2.2) := continuous_snd.comp continuous_snd
  have hCoord : Continuous (fun p : X => E0 (Prod.mk p.1 p.2.2)) :=
    E0.continuous.comp (continuous_fst.prodMk hB)
  have hArg : Continuous (fun p : X => (Inv.inv p.2.1.val * E0 (Prod.mk p.1 p.2.2) : L)) :=
    (hInv.comp (hVal.comp hA)).mul hCoord
  have hArgM : Measurable (fun p : X => (Inv.inv p.2.1.val * E0 (Prod.mk p.1 p.2.2) : L)) :=
    hArg.measurable
  have hProj : Measurable (fun p : X => p.2.1) := measurable_fst.comp measurable_snd
  have hQ : Measurable (fun p : X => Q p.1 p.2.1 p.2.2) := hH.comp (hArgM.prodMk hProj)
  have hQSlice (A : G) :
      lintegral (m.prod mu) (fun p : Prod Real G => Q p.1 A p.2) =
        lintegral m (fun t => lintegral mu (Q t A)) :=
    lintegral_tripleMiddleSection_eq mu Q hQ A
  have hDet (A : G) :
      lintegral m (fun t => lintegral mu (Q t A)) = lintegral M (fun g : L => H (Prod.mk g A)) := by
    let P (g : L) := H (Prod.mk (Inv.inv A.val * g) A)
    have hM : M = Measure.map e (m.prod mu) := rfl
    calc
      _ = lintegral (m.prod mu) (fun p : Prod Real G => Q p.1 A p.2) :=
        (hQSlice A).symm
      _ = lintegral (Measure.map e (m.prod mu)) P := (lintegral_map_equiv P e).symm
      _ = lintegral M P := by rw [hM]
      _ = _ := lintegral_mul_left_eq_self (fun g : L => H (Prod.mk g A)) (Inv.inv A.val)
  have hPeriodized : lintegral (m.prod (nu.prod nu))
      (fun p : X => U p.1 p.2.1 p.2.2) =
      lintegral nu (fun A => lintegral m (fun t => lintegral mu (Q t A))) :=
    lintegral_restrictedPeriodizedTripleKernel_eq (Gamma := Gamma) mu D hD Q hQ
  change lintegral (m.prod (nu.prod nu)) (fun p : X => U p.1 p.2.1 p.2.2) =
    lintegral (M.prod nu) H
  calc
    _ = lintegral nu (fun A => lintegral m (fun t => lintegral mu (Q t A))) := hPeriodized
    _ = lintegral nu (fun A => lintegral M (fun g : L => H (Prod.mk g A))) := lintegral_congr hDet
    _ = _ := (lintegral_prod_symm H hH.aemeasurable).symm

set_option maxHeartbeats 1600000 in
/-- Absolute convergence of the matrix-coefficient kernel gives absolute
convergence of the theta Mellin kernel once the kernels are measurable. -/
theorem integrable_godementJacquetInvertibleDoubleTheta_of_matrixCoeff
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (AdelicGeneralLinearGroup K n)] [BorelSpace (AdelicGeneralLinearGroup K n)]
    [MeasurableSpace (ZetaTonelliGroup K n)] [BorelSpace (ZetaTonelliGroup K n)]
    (mu : Measure (ZetaTonelliGroup K n)) [SFinite mu] [mu.IsHaarMeasure]
    (D : Set (ZetaTonelliGroup K n))
    (hD : IsFundamentalDomain (adelicPrincipalDeterminantOne K n).range D mu)
    (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (f : AdelicGeneralLinearGroup K n -> Complex)
    (c : ZetaTonelliGroup K n -> Complex) (s : Complex)
    (hPrincipal : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      f (adelicPrincipalGeneralLinear K n a * g) = f g)
    (hCentral : forall t : Real, forall B : ZetaTonelliGroup K n,
      f (adelicDeterminantSection K n (Multiplicative.ofAdd t) * B.val) = f B.val) :
    let nu := mu.restrict D
    let m : Measure Real := volume
    let M := adelicDeterminantProductMeasure K n hn mu
    let F := fun p : Prod (AdelicGeneralLinearGroup K n) (ZetaTonelliGroup K n) =>
      (Phi p.1.val * (f (p.2.val * p.1) * c p.2)) *
        (adelicDeterminantNorm K n p.1 : Complex) ^ (s + ((n : Complex) - 1) / 2)
    let T := fun p : Prod Real (Prod (ZetaTonelliGroup K n) (ZetaTonelliGroup K n)) =>
      (godementJacquetInvertibleDoubleThetaSeries K n Phi p.1 p.2.1 p.2.2 *
        (c p.2.1 * f p.2.2.val)) * Complex.exp ((p.1 : Complex) * (s + ((n : Complex) - 1) / 2))
    Measurable (fun p => enorm (F p)) -> Integrable F (M.prod nu) ->
      AEStronglyMeasurable T (m.prod (nu.prod nu)) -> Integrable T (m.prod (nu.prod nu)) := by
  intro nu m M F T hF hInt hT
  let G : Type _ := ZetaTonelliGroup K n
  let Gamma : Type _ := (adelicPrincipalDeterminantOne K n).range
  let e := (adelicDeterminantHomeomorph K n hn).toMeasurableEquiv
  let z (t : Real) := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let W (t : Real) := Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2))
  let w (g : AdelicGeneralLinearGroup K n) :=
    (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)
  let R (t : Real) (A B : G) (a : Gamma) := Phi ((Inv.inv A.val * (a.val.val * (z t * B.val))).val)
  let U (p : Prod Real (Prod G G)) := tsum fun a : Gamma =>
    enorm (F (Prod.mk (Inv.inv p.2.1.val * e (Prod.mk p.1 (SMul.smul a p.2.2))) p.2.1))
  have hNorm (A : G) : adelicDeterminantNorm K n A.val = 1 := by
    have hLog : Real.log (adelicDeterminantNorm K n A.val) = 0 := A.property
    rw [<- Real.exp_log (adelicDeterminantNorm_pos K n A.val), hLog, Real.exp_zero]
  have hMove (t : Real) (a : Gamma) (B : G) :
      e (Prod.mk t (SMul.smul a B)) = a.val.val * (z t * B.val) := by
    change z t * (a.val.val * B.val) = a.val.val * (z t * B.val)
    rw [<- mul_assoc, (adelicDeterminantSection_commute K n
      (Multiplicative.ofAdd t) a.val.val).eq, mul_assoc]
  have hCoeff (t : Real) (A B : G) (a : Gamma) :
      F (Prod.mk (Inv.inv A.val * e (Prod.mk t (SMul.smul a B))) A) =
        (R t A B a * (c A * f B.val)) * W t := by
    let k : G := SMul.smul a B
    let g := e (Prod.mk t k)
    have hW : w (Inv.inv A.val * g) = W t := by
      change (adelicDeterminantNorm K n (Inv.inv A.val * g) : Complex) ^ _ = W t
      rw [map_mul, map_inv, hNorm A, inv_one, one_mul]
      exact adelicGodementJacquetWeight_coordinates K n hn (Multiplicative.ofAdd t) k s
    have hInv : f g = f B.val := by
      choose P hP using a.property
      have hP' : adelicPrincipalGeneralLinear K n P = a.val.val := congrArg Subtype.val hP
      rw [show g = a.val.val * (z t * B.val) from hMove t a B, <- hP']
      exact (hPrincipal P _).trans (hCentral t B)
    change (Phi ((Inv.inv A.val * g).val) * (f (A.val * (Inv.inv A.val * g)) * c A)) *
      w (Inv.inv A.val * g) = (R t A B a * (c A * f B.val)) * W t
    rw [<- mul_assoc A.val, mul_inv_cancel, one_mul, hInv, hW]
    change (Phi ((Inv.inv A.val * g).val) * (f B.val * c A)) * W t =
      (Phi ((Inv.inv A.val * (a.val.val * (z t * B.val))).val) * (c A * f B.val)) * W t
    rw [show g = a.val.val * (z t * B.val) from hMove t a B, mul_comm (f B.val) (c A)]
  have hLe (p : Prod Real (Prod G G)) : enorm (T p) <= U p := by
    let A := p.2.1
    let B := p.2.2
    let t := p.1
    let b := c A * f B.val
    have hR : tsum (R t A B) = godementJacquetInvertibleDoubleThetaSeries K n Phi t A B :=
      tsum_godementJacquetPrincipalRange_eq_invertibleDoubleThetaSeries K n Phi t A B
    change enorm ((godementJacquetInvertibleDoubleThetaSeries K n Phi t A B * b) * W t) <=
      tsum (fun a : Gamma => enorm (F (Prod.mk (Inv.inv A.val * e (Prod.mk t (SMul.smul a B))) A)))
    rw [<- hR, <- tsum_mul_right, <- tsum_mul_right]
    simp only [hCoeff]
    exact enorm_tsum_le_tsum_enorm (f := fun a : Gamma => (R t A B a * b) * W t)
  have hU : lintegral (m.prod (nu.prod nu)) U = lintegral (M.prod nu) (fun p => enorm (F p)) :=
    lintegral_godementJacquetPrincipalKernel_eq_unfolded K n hn mu D hD _ hF
  exact And.intro hT (lt_of_le_of_lt ((lintegral_mono hLe).trans_eq hU) hInt.2)

set_option maxHeartbeats 1300000 in
/-- The matrix-coefficient zeta integral agrees with the theta Mellin
transform under the usual absolute convergence hypothesis for the zeta
kernel. The theta kernel is measurable and its integrability follows
from the nonnegative unfolding. -/
theorem integral_adelicGodementJacquetMatrixCoeff_eq_logMellin_of_measurable
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (AdelicGeneralLinearGroup K n)] [BorelSpace (AdelicGeneralLinearGroup K n)]
    [MeasurableSpace (ZetaTonelliGroup K n)] [BorelSpace (ZetaTonelliGroup K n)]
    (mu : Measure (ZetaTonelliGroup K n)) [SFinite mu] [mu.IsHaarMeasure]
    (D : Set (ZetaTonelliGroup K n))
    (hD : IsFundamentalDomain (adelicPrincipalDeterminantOne K n).range D mu)
    [MeasurableSpace (Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K))]
    [BorelSpace (Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K))]
    (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (f : AdelicGeneralLinearGroup K n -> Complex)
    (c : ZetaTonelliGroup K n -> Complex) (s : Complex)
    (hPhi : Measurable Phi) (hf : Measurable f) (hc : Measurable c)
    (hSum : forall (t : Real) (A B : ZetaTonelliGroup K n),
      Summable (fun P : Matrix.GeneralLinearGroup (Fin n) K =>
        godementJacquetDoubleThetaTerm K n Phi t A B P.val))
    (hPrincipal : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      f (adelicPrincipalGeneralLinear K n a * g) = f g)
    (hCentral : forall t : Real, forall B : ZetaTonelliGroup K n,
      f (adelicDeterminantSection K n (Multiplicative.ofAdd t) * B.val) = f B.val)
    (hInt : Integrable (fun p : Prod (AdelicGeneralLinearGroup K n) (ZetaTonelliGroup K n) =>
      (Phi p.1.val * (f (p.2.val * p.1) * c p.2)) *
        (adelicDeterminantNorm K n p.1 : Complex) ^ (s + ((n : Complex) - 1) / 2))
      ((adelicDeterminantProductMeasure K n hn mu).prod (mu.restrict D))) :
    integral (adelicDeterminantProductMeasure K n hn mu)
      (fun g => (Phi g.val * integral (mu.restrict D) (fun h => f (h.val * g) * c h)) *
        (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)) =
      godementJacquetLogMellin n
        (fun t => godementJacquetInvertibleDoubleThetaIntegral K n (mu.restrict D) Phi c
          (fun B => f B.val) t) s := by
  let L := AdelicGeneralLinearGroup K n
  let G : Type _ := ZetaTonelliGroup K n
  let X := Prod L G
  let Y := Prod Real (Prod G G)
  let A := AdeleRing (RingOfIntegers K) K
  let J := Matrix (Fin n) (Fin n) A
  let Z := s + ((n : Complex) - 1) / 2
  let : SecondCountableTopology L := secondCountableTopology_godementJacquetMatrixUnits K n
  have hSub : Topology.IsEmbedding (Subtype.val : G -> L) := Topology.IsEmbedding.subtypeVal
  let : SecondCountableTopology G := hSub.secondCountableTopology
  have hGV : Continuous (Subtype.val : G -> L) := continuous_subtype_val
  have hV : Measurable (Units.val : L -> J) := Units.continuous_val.measurable
  have hXL : Measurable (fun q : X => q.1) := measurable_fst
  have hXG : Measurable (fun q : X => q.2) := measurable_snd
  have hProd : Continuous (fun q : X => (q.2.val * q.1 : L)) :=
    (hGV.comp continuous_snd).mul continuous_fst
  have hFG : Measurable (fun q : X => f (q.2.val * q.1)) := hf.comp hProd.measurable
  have hPX : Measurable (fun q : X => Phi q.1.val) := hPhi.comp (hV.comp hXL)
  have hCX : Measurable (fun q : X => c q.2) := hc.comp hXG
  let w (g : L) := (adelicDeterminantNorm K n g : Complex) ^ Z
  let l (g : L) := Real.log (adelicDeterminantNorm K n g)
  have hl : Measurable l := Real.measurable_log.comp (continuous_adelicDeterminantNorm K n).measurable
  have hlC : Measurable (fun g : L => (l g : Complex)) := Complex.continuous_ofReal.measurable.comp hl
  have hw' : Measurable (fun g : L => Complex.exp ((l g : Complex) * Z)) :=
    Complex.continuous_exp.measurable.comp (hlC.mul_const Z)
  have hW (g : L) : w g = Complex.exp ((l g : Complex) * Z) := by
    have h := adelicDeterminantNorm_pos K n g
    change (adelicDeterminantNorm K n g : Complex) ^ Z =
      Complex.exp ((Real.log (adelicDeterminantNorm K n g) : Complex) * Z)
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt h)), Complex.ofReal_log h.le]
  have hw : Measurable w := by
    rw [show w = (fun g : L => Complex.exp ((l g : Complex) * Z)) from funext hW]
    exact hw'
  have hWX : Measurable (fun p : X => w p.1) := hw.comp hXL
  have hF : Measurable (fun q : X => (Phi q.1.val * (f (q.2.val * q.1) * c q.2)) * w q.1) :=
    (hPX.mul (hFG.mul hCX)).mul hWX
  let P := Matrix.GeneralLinearGroup (Fin n) K
  have hP : Function.Injective (Units.val : P -> Matrix (Fin n) (Fin n) K) := Units.val_injective
  let : Countable K := (Module.finBasis Rat K).equivFun.injective.countable
  let : Countable (Matrix (Fin n) (Fin n) K) := inferInstanceAs (Countable (Fin n -> Fin n -> K))
  let : Countable P := hP.countable
  have hTSeries : Measurable (fun q : Y =>
      godementJacquetInvertibleDoubleThetaSeries K n Phi q.1 q.2.1 q.2.2) :=
    measurable_godementJacquetThetaSeries K n P Units.val Phi hPhi hSum
  have hYL : Measurable (fun q : Y => q.2.1) := measurable_fst.comp measurable_snd
  have hYR : Measurable (fun q : Y => q.2.2) := measurable_snd.comp measurable_snd
  have hTY : Measurable (fun q : Y => Complex.exp ((q.1 : Complex) * Z)) :=
    (Complex.continuous_exp.measurable.comp
      (Complex.continuous_ofReal.measurable.mul_const Z)).comp measurable_fst
  have hSY : Measurable (fun q : Y => f q.2.2.val) := hf.comp (hGV.measurable.comp hYR)
  have hCY : Measurable (fun q : Y => c q.2.1) := hc.comp hYL
  have hThetaMeas : Measurable (fun q : Y =>
      (godementJacquetInvertibleDoubleThetaSeries K n Phi q.1 q.2.1 q.2.2 *
        (c q.2.1 * f q.2.2.val)) * Complex.exp ((q.1 : Complex) * Z)) :=
    (hTSeries.mul (hCY.mul hSY)).mul hTY
  have hTheta := integrable_godementJacquetInvertibleDoubleTheta_of_matrixCoeff
    K n hn mu D hD Phi f c s hPrincipal hCentral hF.enorm hInt hThetaMeas.aestronglyMeasurable
  exact integral_adelicGodementJacquetMatrixCoeff_eq_logMellin
    K n hn mu D hD Phi f c s hPrincipal hCentral hInt hTheta

end Robin1984.GRH
