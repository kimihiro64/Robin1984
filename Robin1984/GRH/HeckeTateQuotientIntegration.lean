import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Robin1984.GRH.HeckeIdeleClassCoordinates
import Robin1984.GRH.HeckeTateFundamentalDomain

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's unfolding of the multiplicative idele integral over principal ideles and the logarithmic norm.
- Formalization note: Transports the product of Lebesgue measure and the norm-one measure, proves the quotient measure identity, and applies unfolding over the full principal subgroup.
- PROVENANCE-END
-/

/-!
# Unfolding the multiplicative idele integral

The principal subgroup acts on the norm-one coordinate. A section there
gives a section of the full quotient. Restricting multiplicative measure
to it yields the product of Lebesgue measure in logarithmic norm and the
norm-one class measure.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory

variable {G H : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]

/-- Transport additive Lebesgue measure times a measure on the norm-one group. -/
noncomputable def heckeLogProductMeasure
    (e : Homeomorph G (Prod Real H)) (mu : Measure H) : Measure G :=
  Measure.map e.symm (volume.prod mu)

/-- The log norm coordinates preserve the transported product measure. -/
theorem measurePreserving_heckeLogProductMeasure
    (e : Homeomorph G (Prod Real H)) (mu : Measure H) :
    MeasurePreserving e (heckeLogProductMeasure e mu) (volume.prod mu) := by
  have he : Measurable e := e.continuous.measurable
  have hs : Measurable e.symm := e.symm.continuous.measurable
  refine MeasurePreserving.mk he ?_
  change Measure.map e (Measure.map e.symm (volume.prod mu)) = volume.prod mu
  rw [Measure.map_map he hs]
  have hId : Function.comp (e : G -> Prod Real H) (e.symm : Prod Real H -> G) = id :=
    funext e.apply_symm_apply
  rw [hId, Measure.map_id]

/-- Translation in log norm coordinates preserves the product measure. -/
theorem isMulRightInvariant_heckeLogProductMeasure
    [Group G] [IsTopologicalGroup G] [Group H] [IsTopologicalGroup H]
    (e : Homeomorph G (Prod Real H))
    (hMul : forall a b : G, e (a * b) = Prod.mk ((e a).1 + (e b).1) ((e a).2 * (e b).2))
    (mu : Measure H) [SFinite mu] [mu.IsMulRightInvariant] :
    (heckeLogProductMeasure e mu).IsMulRightInvariant := by
  constructor
  intro a
  let t : Real := (e a).1
  let c : H := (e a).2
  let T : Prod Real H -> Prod Real H := Prod.map (fun s => s + t) (fun h => h * c)
  have h1 := measurePreserving_add_right volume t
  have h2 := measurePreserving_mul_right mu c
  have hT : Measurable T := h1.measurable.prodMap h2.measurable
  have hMap : Measure.map T (volume.prod mu) = volume.prod mu := by
    rw [<- Measure.map_prod_map volume mu h1.measurable h2.measurable, h1.map_eq, h2.map_eq]
  have hf : Measurable (fun b : G => b * a) := (continuous_mul_const a).measurable
  have hs : Measurable e.symm := e.symm.continuous.measurable
  have hEq : Function.comp (fun b : G => b * a) e.symm = Function.comp e.symm T := by
    funext p
    apply e.injective
    change e (e.symm p * a) = e (e.symm (T p))
    rw [hMul, e.apply_symm_apply, e.apply_symm_apply]
    rfl
  change Measure.map (fun b : G => b * a) (Measure.map e.symm (volume.prod mu)) =
    Measure.map e.symm (volume.prod mu)
  rw [Measure.map_map hf hs, hEq, <- Measure.map_map hs hT, hMap]

variable (K : Type*) [Field K] [NumberField K]

private abbrev TateGlobalIdeles := Units (AdeleRing (RingOfIntegers K) K)

/-- Multiplicative measure on the ideles in the logarithmic norm normalization. -/
noncomputable def heckeIdelicLogNormMeasure
    [MeasurableSpace (TateGlobalIdeles K)] [BorelSpace (TateGlobalIdeles K)]
    [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]
    (mu : Measure (heckeNormOneIdeles K)) : Measure (TateGlobalIdeles K) :=
  heckeLogProductMeasure (heckeIdelicLogNormHomeomorph K) mu

/-- Right invariance on the norm-one part gives right invariance on the ideles. -/
theorem isMulRightInvariant_heckeIdelicLogNormMeasure
    [MeasurableSpace (TateGlobalIdeles K)] [BorelSpace (TateGlobalIdeles K)]
    [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]
    (mu : Measure (heckeNormOneIdeles K)) [SFinite mu] [mu.IsMulRightInvariant] :
    (heckeIdelicLogNormMeasure K mu).IsMulRightInvariant :=
  isMulRightInvariant_heckeLogProductMeasure
    (heckeIdelicLogNormHomeomorph K) (heckeIdelicLogNormHomeomorph_mul K) mu

/-- A norm-one section determines a section in the full logarithmic norm coordinates. -/
noncomputable def heckeFullTateFundamentalSet (S : Set (heckeNormOneIdeles K)) :
    Set (TateGlobalIdeles K) :=
  Set.preimage (heckeIdelicLogNormHomeomorph K) (Set.prod Set.univ S)

/-- The quotient in log norm coordinates commutes with the norm-one quotient. -/
theorem heckeIdeleClassLogNormHomeomorph_mk (a : TateGlobalIdeles K) :
    heckeIdeleClassLogNormHomeomorph K (QuotientGroup.mk a) =
      Prod.map id (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range)
        (heckeIdelicLogNormHomeomorph K a) := rfl

/-- Restricting the idelic product measure to the section gives the product quotient measure. -/
theorem map_heckeIdeleClassLogNormHomeomorph_quotientMeasure
    [MeasurableSpace (TateGlobalIdeles K)] [BorelSpace (TateGlobalIdeles K)]
    [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]
    [MeasurableSpace (heckeIdeleClass K)] [BorelSpace (heckeIdeleClass K)]
    [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeles K)) [SFinite mu]
    {S : Set (heckeNormOneIdeles K)} (hS : MeasurableSet S) :
    Measure.map (heckeIdeleClassLogNormHomeomorph K)
      (Measure.map (QuotientGroup.mk' (heckeFullPrincipalIdele K).range)
        ((heckeIdelicLogNormMeasure K mu).restrict (heckeFullTateFundamentalSet K S))) =
      volume.prod (heckeNormOneClassQuotientMeasure K mu S) := by
  let e := heckeIdelicLogNormHomeomorph K
  let E := heckeIdeleClassLogNormHomeomorph K
  let q := QuotientGroup.mk' (heckeFullPrincipalIdele K).range
  let q1 := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
  let B : Set (Prod Real (heckeNormOneIdeles K)) := Set.prod Set.univ S
  have hSfull : MeasurableSet (heckeFullTateFundamentalSet K S) :=
    (MeasurableSet.univ.prod hS).preimage e.continuous.measurable
  have he : Measurable e.symm := e.symm.continuous.measurable
  have hE : Measurable E := E.continuous.measurable
  have hq : Measurable q := (show Continuous q from QuotientGroup.continuous_mk).measurable
  have hq1 : Measurable q1 := (show Continuous q1 from QuotientGroup.continuous_mk).measurable
  have hPre : Set.preimage e.symm (heckeFullTateFundamentalSet K S) = B := by
    ext p
    change Iff (Membership.mem B (e (e.symm p))) (Membership.mem B p)
    rw [e.apply_symm_apply]
  have hComp : Function.comp E (Function.comp q e.symm) = Prod.map id q1 := by
    funext p
    change E (QuotientGroup.mk (e.symm p)) = Prod.map id q1 p
    rw [heckeIdeleClassLogNormHomeomorph_mk]
    change Prod.map id q1 (e (e.symm p)) = Prod.map id q1 p
    rw [e.apply_symm_apply]
  change Measure.map E (Measure.map q
      ((Measure.map e.symm (volume.prod mu)).restrict (heckeFullTateFundamentalSet K S))) =
    volume.prod (Measure.map q1 (mu.restrict S))
  rw [Measure.restrict_map he hSfull, hPre, Measure.map_map hq he,
    Measure.map_map hE (hq.comp he), hComp]
  have hProd : ((volume : Measure Real).restrict Set.univ).prod (mu.restrict S) =
      (volume.prod mu).restrict B := Measure.prod_restrict Set.univ S
  rw [<- hProd, Measure.restrict_univ,
    <- Measure.map_prod_map volume (mu.restrict S) measurable_id hq1, Measure.map_id]

/-- Each full idele class has a unique representative over the norm-one section. -/
theorem isFundamentalDomain_heckeFullTateFundamentalSet
    [MeasurableSpace (TateGlobalIdeles K)] [BorelSpace (TateGlobalIdeles K)]
    [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]
    (mu : Measure (TateGlobalIdeles K)) {S : Set (heckeNormOneIdeles K)}
    (hS : MeasurableSet S)
    (hInj : Set.InjOn (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S)
    (hSur : Set.image (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S = Set.univ) :
    IsFundamentalDomain (heckeFullPrincipalIdele K).range.op (heckeFullTateFundamentalSet K S) mu := by
  let e := heckeIdelicLogNormHomeomorph K
  let E := heckeIdeleClassLogNormHomeomorph K
  let q := QuotientGroup.mk' (heckeFullPrincipalIdele K).range
  let q1 := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
  let W := heckeFullTateFundamentalSet K S
  have hW : MeasurableSet W := (MeasurableSet.univ.prod hS).preimage e.continuous.measurable
  have hEq (a : TateGlobalIdeles K) : E (q a) = Prod.map id q1 (e a) :=
    heckeIdeleClassLogNormHomeomorph_mk K a
  apply isFundamentalDomain_of_quotientSection (heckeFullPrincipalIdele K).range mu hW
  . intro a ha b hb hab
    have hE := (hEq a).symm.trans ((congrArg (fun c => E c) hab).trans (hEq b))
    have ha' : Membership.mem S (e a).2 := ha.2
    have hb' : Membership.mem S (e b).2 := hb.2
    have hFirst : (e a).1 = (e b).1 :=
      congrArg (fun z : Prod Real (heckeNormOneIdeleClass K) => z.1) hE
    have hSecond : q1 (e a).2 = q1 (e b).2 :=
      congrArg (fun z : Prod Real (heckeNormOneIdeleClass K) => z.2) hE
    exact e.injective (Prod.ext hFirst (hInj ha' hb' hSecond))
  . apply Set.eq_univ_of_forall
    intro c
    let p := E c
    have hp : Membership.mem (Set.image q1 S) p.2 := by
      have hAll : Set.image q1 S = Set.univ := hSur
      rw [hAll]
      exact Set.mem_univ _
    choose b hb hbq using hp
    let a := e.symm (Prod.mk p.1 b)
    have ha : e a = Prod.mk p.1 b := e.apply_symm_apply _
    have haW : Membership.mem W a := by
      change Membership.mem (Set.prod Set.univ S) (e a)
      rw [ha]
      exact And.intro (Set.mem_univ _) hb
    have haq : q a = c := by
      apply E.injective
      rw [hEq, ha]
      exact Prod.ext rfl hbq
    exact Exists.intro a (And.intro haW haq)

/-- A countable field has countably many principal ideles. -/
theorem countable_heckeFullPrincipalIdeles :
    Countable (heckeFullPrincipalIdele K).range := by
  let : Countable (Units K) := countable_units_numberField K
  let P := heckeFullPrincipalIdele K
  have h : Function.Surjective P.rangeRestrict := by
    intro a
    choose b hb using a.property
    exact Exists.intro b (Subtype.ext hb)
  exact h.countable

/-- The full quotient measure induced from a log norm fundamental set. -/
noncomputable def heckeFullTateQuotientMeasure
    [MeasurableSpace (TateGlobalIdeles K)] [BorelSpace (TateGlobalIdeles K)]
    [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]
    [MeasurableSpace (heckeIdeleClass K)]
    (mu : Measure (heckeNormOneIdeles K)) (S : Set (heckeNormOneIdeles K)) :
    Measure (heckeIdeleClass K) :=
  Measure.map (QuotientGroup.mk' (heckeFullPrincipalIdele K).range)
    ((heckeIdelicLogNormMeasure K mu).restrict (heckeFullTateFundamentalSet K S))

/-- Unfold the principal-idele sum against the product of log norm and the finite class measure. -/
theorem integral_heckeIdelicLogNormMeasure_eq_integral_automorphize
    [MeasurableSpace (TateGlobalIdeles K)] [BorelSpace (TateGlobalIdeles K)]
    [MeasurableSpace (heckeNormOneIdeles K)] [BorelSpace (heckeNormOneIdeles K)]
    [MeasurableSpace (heckeIdeleClass K)] [BorelSpace (heckeIdeleClass K)]
    [MeasurableSpace (heckeNormOneIdeleClass K)] [BorelSpace (heckeNormOneIdeleClass K)]
    (mu : Measure (heckeNormOneIdeles K)) [SFinite mu] [mu.IsMulRightInvariant]
    {S : Set (heckeNormOneIdeles K)} (hS : MeasurableSet S)
    (hInj : Set.InjOn (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S)
    (hSur : Set.image (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S = Set.univ)
    (f : TateGlobalIdeles K -> Complex)
    (hInt : Integrable f (heckeIdelicLogNormMeasure K mu))
    (hAuto : AEStronglyMeasurable (QuotientGroup.automorphize f)
      (heckeFullTateQuotientMeasure K mu S)) :
    integral (heckeIdelicLogNormMeasure K mu) f =
      integral (volume.prod (heckeNormOneClassQuotientMeasure K mu S))
        (fun p : Prod Real (heckeNormOneIdeleClass K) =>
          QuotientGroup.automorphize f ((heckeIdeleClassLogNormHomeomorph K).symm p)) := by
  let M := heckeIdelicLogNormMeasure K mu
  let P := (heckeFullPrincipalIdele K).range
  let : Countable P := countable_heckeFullPrincipalIdeles K
  let : M.IsMulRightInvariant := isMulRightInvariant_heckeIdelicLogNormMeasure K mu
  let E := heckeIdeleClassLogNormHomeomorph K
  let N := heckeFullTateQuotientMeasure K mu S
  let V := (volume : Measure Real).prod (heckeNormOneClassQuotientMeasure K mu S)
  have hF := isFundamentalDomain_heckeFullTateFundamentalSet K M hS hInj hSur
  have hUnfold : integral M f = integral N (QuotientGroup.automorphize f) :=
    QuotientGroup.integral_eq_integral_automorphize hF hInt hAuto
  have hMap : Measure.map E N = V :=
    map_heckeIdeleClassLogNormHomeomorph_quotientMeasure K mu hS
  have hE : Measurable E := E.continuous.measurable
  have hInv : Measurable E.symm := E.symm.continuous.measurable
  have hMapInv : Measure.map E.symm V = N := by
    rw [<- hMap, Measure.map_map hInv hE]
    have hId : Function.comp (E.symm : Prod Real (heckeNormOneIdeleClass K) -> heckeIdeleClass K) E = id :=
      funext E.symm_apply_apply
    rw [hId, Measure.map_id]
  have hAuto' : AEStronglyMeasurable (QuotientGroup.automorphize f) (Measure.map E.symm V) := by
    rw [hMapInv]
    exact hAuto
  calc
    _ = integral N (QuotientGroup.automorphize f) := hUnfold
    _ = integral (Measure.map E.symm V) (QuotientGroup.automorphize f) := by rw [hMapInv]
    _ = _ := integral_map hInv.aemeasurable hAuto'

end Robin1984.GRH
