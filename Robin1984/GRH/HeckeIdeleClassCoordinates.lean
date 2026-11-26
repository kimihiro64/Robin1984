import Robin1984.GRH.HeckeTateThetaDecay

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The logarithmic-norm splitting of the idele group and the idele class group in Tate's thesis.
- Formalization note: Uses the explicit positive archimedean section and principal multiplication to construct the two homeomorphisms and verify their coordinate laws.
- PROVENANCE-END
-/

/-!
# Logarithmic norm coordinates on ideles and idele classes

The exponential scale in the archimedean component splits the norm map
continuously. Removing that scale gives the norm-one part. The principal
idele action preserves the logarithmic norm, so the splitting descends
to the true idele class group.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField NumberField.mixedEmbedding IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

private abbrev TateGlobalIdeles := Units (AdeleRing (RingOfIntegers K) K)

private noncomputable def tateArchScaleRingHom : RingHom Real (InfiniteAdeleRing K) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp (algebraMap Real (mixedSpace K))

private theorem tateIdelicExpSection_val (t : Real) :
    (heckeIdelicExpSection K t).val =
      Prod.mk (tateArchScaleRingHom K (Real.exp (t / (Module.finrank Rat K : Real)))) 1 := rfl

/-- The logarithmic norm section takes zero to the unit idele. -/
@[simp] theorem heckeIdelicExpSection_zero :
    heckeIdelicExpSection K 0 = 1 := by
  apply Units.ext
  rw [tateIdelicExpSection_val, zero_div, Real.exp_zero, map_one]
  rfl

/-- Adding the parameters of the logarithmic norm section multiplies the ideles. -/
theorem heckeIdelicExpSection_add (s t : Real) :
    heckeIdelicExpSection K (s + t) = heckeIdelicExpSection K s * heckeIdelicExpSection K t := by
  apply Units.ext
  rw [Units.val_mul, tateIdelicExpSection_val, tateIdelicExpSection_val, tateIdelicExpSection_val]
  apply Prod.ext
  . change tateArchScaleRingHom K (Real.exp ((s + t) / (Module.finrank Rat K : Real))) =
      tateArchScaleRingHom K (Real.exp (s / (Module.finrank Rat K : Real))) *
      tateArchScaleRingHom K (Real.exp (t / (Module.finrank Rat K : Real)))
    rw [add_div, Real.exp_add, map_mul]
  . exact (mul_one _).symm

/-- Negating the logarithmic norm parameter inverts the idele. -/
theorem heckeIdelicExpSection_neg (t : Real) :
    heckeIdelicExpSection K (-t) = Inv.inv (heckeIdelicExpSection K t) := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [<- heckeIdelicExpSection_add, neg_add_cancel, heckeIdelicExpSection_zero]

/-- The archimedean scaling section is continuous in the idele topology. -/
theorem continuous_heckeIdelicExpSection : Continuous (heckeIdelicExpSection K) := by
  have hA : Continuous (tateArchScaleRingHom K) := by
    change Continuous (fun r : Real =>
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (algebraMap Real (mixedSpace K) r))
    have hM : Continuous (algebraMap Real (mixedSpace K)) := by
      change Continuous (fun r : Real => algebraMap Real (mixedSpace K) r)
      simp only [Algebra.algebraMap_eq_smul_one]
      exact continuous_id.smul continuous_const
    exact (continuous_heckeInfiniteAdele_mixedSpace_symm K).comp hM
  have hVal : Continuous (fun t : Real => (heckeIdelicExpSection K t).val) := by
    have hFormula : Continuous (fun t : Real =>
        Prod.mk (tateArchScaleRingHom K (Real.exp (t / (Module.finrank Rat K : Real))))
          (1 : FiniteAdeleRing (RingOfIntegers K) K)) :=
      (hA.comp (Real.continuous_exp.comp (continuous_id.div_const _))).prodMk continuous_const
    exact hFormula.congr (fun t => (tateIdelicExpSection_val K t).symm)
  refine Units.continuous_iff.mpr (And.intro hVal ?_)
  exact (hVal.comp continuous_neg).congr
    (fun t => congrArg Units.val (heckeIdelicExpSection_neg K t))

/-- Dividing an idele by its exponential norm component gives a norm-one idele. -/
noncomputable def heckeNormOnePart (a : TateGlobalIdeles K) : heckeNormOneIdeles K :=
  Subtype.mk (Inv.inv (heckeIdelicExpSection K (Real.log (heckeIdelicNorm a))) * a) (by
    apply (mem_heckeNormOneIdeles K _).mpr
    rw [map_mul, map_inv, heckeIdelicNorm_expSection, Real.exp_log (heckeIdelicNorm_pos a)]
    field_simp [(heckeIdelicNorm_pos a).ne'])

/-- The ideles split topologically into the logarithmic norm and its kernel. -/
noncomputable def heckeIdelicLogNormHomeomorph :
    Homeomorph (TateGlobalIdeles K) (Prod Real (heckeNormOneIdeles K)) where
  toFun a := Prod.mk (Real.log (heckeIdelicNorm a)) (heckeNormOnePart K a)
  invFun p := heckeIdelicExpSection K p.1 * p.2.val
  left_inv a := by
    change heckeIdelicExpSection K (Real.log (heckeIdelicNorm a)) *
      (Inv.inv (heckeIdelicExpSection K (Real.log (heckeIdelicNorm a))) * a) = a
    rw [<- mul_assoc, mul_inv_cancel, one_mul]
  right_inv p := by
    have hnorm : heckeIdelicNorm (heckeIdelicExpSection K p.1 * p.2.val) = Real.exp p.1 := by
      rw [map_mul, heckeIdelicNorm_expSection,
        (mem_heckeNormOneIdeles K _).mp p.2.property, mul_one]
    have h : Real.log (heckeIdelicNorm (heckeIdelicExpSection K p.1 * p.2.val)) = p.1 := by
      rw [hnorm, Real.log_exp]
    apply Prod.ext h
    apply Subtype.ext
    change Inv.inv (heckeIdelicExpSection K
      (Real.log (heckeIdelicNorm (heckeIdelicExpSection K p.1 * p.2.val)))) *
        (heckeIdelicExpSection K p.1 * p.2.val) = p.2.val
    rw [h, <- mul_assoc, inv_mul_cancel, one_mul]
  continuous_toFun := by
    have hLog : Continuous (fun a : TateGlobalIdeles K => Real.log (heckeIdelicNorm a)) :=
      continuous_heckeIdelicNorm.log (fun a => (heckeIdelicNorm_pos a).ne')
    have hPart : Continuous (heckeNormOnePart K) := by
      apply Continuous.subtype_mk
      exact ((continuous_heckeIdelicExpSection K).comp hLog).inv.mul continuous_id
    exact hLog.prodMk hPart
  continuous_invFun :=
    ((continuous_heckeIdelicExpSection K).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)

/-- The full principal idele embedding is the norm-one embedding followed by inclusion. -/
noncomputable def heckeFullPrincipalIdele : MonoidHom (Units K) (TateGlobalIdeles K) :=
  (heckeNormOneIdeles K).subtype.comp (heckePrincipalNormOneIdele K)

/-- The full idele class group is the quotient of the ideles by the principal ideles. -/
noncomputable abbrev heckeIdeleClass :=
  HasQuotient.Quotient (TateGlobalIdeles K) (heckeFullPrincipalIdele K).range

private theorem tateLogNorm_principal_mul (u : Units K) (a : TateGlobalIdeles K) :
    Real.log (heckeIdelicNorm (heckeFullPrincipalIdele K u * a)) =
      Real.log (heckeIdelicNorm a) := by
  have hP : heckeIdelicNorm (heckeFullPrincipalIdele K u) = 1 :=
    (mem_heckeNormOneIdeles K _).mp (heckePrincipalNormOneIdele K u).property
  rw [map_mul, hP, one_mul]

private theorem tateNormOnePart_principal_mul (u : Units K) (a : TateGlobalIdeles K) :
    heckeNormOnePart K (heckeFullPrincipalIdele K u * a) =
      heckePrincipalNormOneIdele K u * heckeNormOnePart K a := by
  apply Subtype.ext
  change Inv.inv (heckeIdelicExpSection K
      (Real.log (heckeIdelicNorm (heckeFullPrincipalIdele K u * a)))) *
        (heckeFullPrincipalIdele K u * a) =
    heckeFullPrincipalIdele K u *
      (Inv.inv (heckeIdelicExpSection K (Real.log (heckeIdelicNorm a))) * a)
  rw [tateLogNorm_principal_mul K u a]
  ac_rfl

private noncomputable def tateFullFromCoordinates :
    Prod Real (heckeNormOneIdeleClass K) -> heckeIdeleClass K := by
  let qAll := QuotientGroup.mk' (heckeFullPrincipalIdele K).range
  intro p
  refine Quotient.lift (fun a : heckeNormOneIdeles K => qAll (heckeIdelicExpSection K p.1 * a.val)) ?_ p.2
  intro a b h
  have hb : Membership.mem (heckePrincipalNormOneIdele K).range (Inv.inv a * b) :=
    QuotientGroup.leftRel_apply.mp h
  choose u hu using hb
  have hEq : heckePrincipalNormOneIdele K u * a = b := by
    rw [hu, mul_comm (Inv.inv a * b) a, <- mul_assoc, mul_inv_cancel, one_mul]
  have huVal : heckeFullPrincipalIdele K u * a.val = b.val := congrArg Subtype.val hEq
  have hArg : heckeIdelicExpSection K p.1 * b.val =
      heckeFullPrincipalIdele K u * (heckeIdelicExpSection K p.1 * a.val) := by
    rw [<- huVal]
    ac_rfl
  have hOne : qAll (heckeFullPrincipalIdele K u) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Exists.intro u rfl)
  rw [hArg, qAll.map_mul (heckeFullPrincipalIdele K u), hOne]
  exact (one_mul (qAll (heckeIdelicExpSection K p.1 * a.val))).symm

private noncomputable def tateCoordinatesFromFull :
    heckeIdeleClass K -> Prod Real (heckeNormOneIdeleClass K) := by
  let qOne := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
  refine Quotient.lift (fun a : TateGlobalIdeles K =>
    Prod.map id qOne (heckeIdelicLogNormHomeomorph K a)) ?_
  intro a b h
  have hb : Membership.mem (heckeFullPrincipalIdele K).range (Inv.inv a * b) :=
    QuotientGroup.leftRel_apply.mp h
  choose u hu using hb
  have hEq : heckeFullPrincipalIdele K u * a = b := by
    rw [hu, mul_comm (Inv.inv a * b) a, <- mul_assoc, mul_inv_cancel, one_mul]
  rw [<- hEq]
  have hFirst := (tateLogNorm_principal_mul K u a).symm
  have hOne : qOne (heckePrincipalNormOneIdele K u) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Exists.intro u rfl)
  apply Prod.ext hFirst
  change qOne (heckeNormOnePart K a) =
    qOne (heckeNormOnePart K (heckeFullPrincipalIdele K u * a))
  rw [tateNormOnePart_principal_mul, qOne.map_mul, hOne]
  exact (one_mul (qOne (heckeNormOnePart K a))).symm

private theorem tateCoordinatesFromFull_mk (a : TateGlobalIdeles K) :
    tateCoordinatesFromFull K (QuotientGroup.mk a) =
      Prod.map id (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range)
        (heckeIdelicLogNormHomeomorph K a) := rfl

private theorem tateFullFromCoordinates_mk (p : Prod Real (heckeNormOneIdeles K)) :
    tateFullFromCoordinates K
      (Prod.map id (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) p) =
      QuotientGroup.mk' (heckeFullPrincipalIdele K).range
        ((heckeIdelicLogNormHomeomorph K).symm p) := by
  cases p
  rfl

/-- Full idele classes split as the real logarithmic norm and the norm-one class group. -/
noncomputable def heckeIdeleClassLogNormHomeomorph :
    Homeomorph (heckeIdeleClass K) (Prod Real (heckeNormOneIdeleClass K)) where
  toFun := tateCoordinatesFromFull K
  invFun := tateFullFromCoordinates K
  left_inv c := by
    refine Quotient.inductionOn c ?_
    intro a
    let qAll := QuotientGroup.mk' (heckeFullPrincipalIdele K).range
    let e := heckeIdelicLogNormHomeomorph K
    change tateFullFromCoordinates K (tateCoordinatesFromFull K (QuotientGroup.mk a)) = _
    rw [tateCoordinatesFromFull_mk, tateFullFromCoordinates_mk, Homeomorph.symm_apply_apply]
    rfl
  right_inv p := by
    let qOne := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
    let e := heckeIdelicLogNormHomeomorph K
    cases p with
    | mk t c =>
      refine Quotient.inductionOn c ?_
      intro a
      change tateCoordinatesFromFull K (tateFullFromCoordinates K (Prod.map id qOne (Prod.mk t a))) =
        Prod.map id qOne (Prod.mk t a)
      rw [tateFullFromCoordinates_mk]
      change tateCoordinatesFromFull K (QuotientGroup.mk (e.symm (Prod.mk t a))) = _
      rw [tateCoordinatesFromFull_mk, Homeomorph.apply_symm_apply]
  continuous_toFun := by
    let qOne := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
    apply (QuotientGroup.isQuotientMap_mk (heckeFullPrincipalIdele K).range).continuous_iff.mpr
    exact ((continuous_id.prodMap (show Continuous qOne from QuotientGroup.continuous_mk)).comp
      (heckeIdelicLogNormHomeomorph K).continuous).congr
        (fun a => (tateCoordinatesFromFull_mk K a).symm)
  continuous_invFun := by
    let qOne := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
    let qAll := QuotientGroup.mk' (heckeFullPrincipalIdele K).range
    let j : Prod Real (heckeNormOneIdeles K) -> Prod Real (heckeNormOneIdeleClass K) :=
      Prod.map id qOne
    have hj : Continuous j := continuous_id.prodMap QuotientGroup.continuous_mk
    have hId : IsOpenMap (id : Real -> Real) := (Homeomorph.refl Real).isOpenMap
    have hOpen : IsOpenMap j := hId.prodMap QuotientGroup.isOpenMap_coe
    have hSur : Function.Surjective j := by
      intro p
      choose a ha using (Quotient.mk_surjective p.2)
      exact Exists.intro (Prod.mk p.1 a) (Prod.ext rfl ha)
    apply (hOpen.isQuotientMap hj hSur).continuous_iff.mpr
    exact ((show Continuous qAll from QuotientGroup.continuous_mk).comp
      (heckeIdelicLogNormHomeomorph K).symm.continuous).congr
        (fun p => (tateFullFromCoordinates_mk K p).symm)

/-- In logarithmic norm coordinates, idele multiplication adds the real coordinate. -/
theorem heckeIdelicLogNormHomeomorph_mul (a b : TateGlobalIdeles K) :
    heckeIdelicLogNormHomeomorph K (a * b) =
      Prod.mk ((heckeIdelicLogNormHomeomorph K a).1 + (heckeIdelicLogNormHomeomorph K b).1)
        ((heckeIdelicLogNormHomeomorph K a).2 * (heckeIdelicLogNormHomeomorph K b).2) := by
  have hlog : Real.log (heckeIdelicNorm (a * b)) =
      Real.log (heckeIdelicNorm a) + Real.log (heckeIdelicNorm b) := by
    rw [map_mul, Real.log_mul (heckeIdelicNorm_pos a).ne' (heckeIdelicNorm_pos b).ne']
  apply Prod.ext hlog
  apply Subtype.ext
  change Inv.inv (heckeIdelicExpSection K (Real.log (heckeIdelicNorm (a * b)))) * (a * b) =
    (Inv.inv (heckeIdelicExpSection K (Real.log (heckeIdelicNorm a))) * a) *
      (Inv.inv (heckeIdelicExpSection K (Real.log (heckeIdelicNorm b))) * b)
  rw [hlog, heckeIdelicExpSection_add, mul_inv_rev]
  ac_rfl

/-- The quotient homeomorphism has the same additive and multiplicative coordinates. -/
theorem heckeIdeleClassLogNormHomeomorph_mul (a b : heckeIdeleClass K) :
    heckeIdeleClassLogNormHomeomorph K (a * b) =
      Prod.mk ((heckeIdeleClassLogNormHomeomorph K a).1 + (heckeIdeleClassLogNormHomeomorph K b).1)
        ((heckeIdeleClassLogNormHomeomorph K a).2 * (heckeIdeleClassLogNormHomeomorph K b).2) := by
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  let q := QuotientGroup.mk' (heckeFullPrincipalIdele K).range
  change tateCoordinatesFromFull K (q x * q y) =
    Prod.mk ((tateCoordinatesFromFull K (q x)).1 + (tateCoordinatesFromFull K (q y)).1)
      ((tateCoordinatesFromFull K (q x)).2 * (tateCoordinatesFromFull K (q y)).2)
  rw [<- q.map_mul]
  change tateCoordinatesFromFull K (QuotientGroup.mk (x * y)) =
    Prod.mk ((tateCoordinatesFromFull K (QuotientGroup.mk x)).1 +
      (tateCoordinatesFromFull K (QuotientGroup.mk y)).1)
      ((tateCoordinatesFromFull K (QuotientGroup.mk x)).2 *
        (tateCoordinatesFromFull K (QuotientGroup.mk y)).2)
  rw [tateCoordinatesFromFull_mk, tateCoordinatesFromFull_mk, tateCoordinatesFromFull_mk,
    heckeIdelicLogNormHomeomorph_mul]
  apply Prod.ext rfl
  exact (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range).map_mul _ _

end Robin1984.GRH
