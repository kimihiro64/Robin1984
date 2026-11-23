import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Topology.Algebra.Group.Quotient
import Robin1984.GRH.HeckeAdelicFourier
import Robin1984.GRH.HeckeFiniteIdealClass

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Compactness of norm-one idele classes via Dirichlet's unit theorem and finiteness of the ideal class group, as in Tate's thesis.
- Formalization note: Constructs compact representatives for the quotient of norm-one ideles by principal ideles.
- PROVENANCE-END
-/

/-!
# Compactness of norm-one idele classes

Dirichlet's unit theorem provides compact representatives at each positive
archimedean norm. Finitely many ideal classes and compact finite integral
units give a compact set meeting every norm-one idele class. The principal
subgroup is closed and discrete.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField NumberField.mixedEmbedding NumberField.Units IsDedekindDomain
open NumberField.Units.dirichletUnitTheorem
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

private theorem exists_normOneCone_normBound :
    Exists (fun R : Real => forall x : mixedSpace K, Membership.mem (fundamentalCone K) x ->
      mixedEmbedding.norm x = 1 -> norm x <= R) := by
  let B := (basisUnitLattice K).ofZLatticeBasis Real (unitLattice K)
  have hB : IsCompact (B.parallelepiped : Set (logSpace K)) := B.parallelepiped.isCompact
  choose T hT using isBounded_iff_forall_norm_le.mp hB.isBounded
  let R := max T 0
  let e : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some
  let A : Finset (InfinitePlace K) := Finset.univ.erase e
  let S : Real := max R ((A.card : Real) * R)
  refine Exists.intro (Real.exp S) ?_
  intro x hx hx1
  have hm : Membership.mem (ZSpan.fundamentalDomain B) (logMap x) := hx.1
  have hL : norm (logMap x) <= R := (hT _ (ZSpan.fundamentalDomain_subset_parallelepiped B hm)).trans
    (le_max_left _ _)
  let g := fun w : InfinitePlace K => (w.mult : Real) * Real.log (normAtPlace w x)
  have hSmall (w : InfinitePlace K) (hw : Not (w = e)) : abs (g w) <= R := by
    let v : Subtype (fun w : InfinitePlace K => Not (w = e)) := Subtype.mk w hw
    have hCoord : logMap x v = g w := logMap_apply_of_norm_eq_one hx1 v
    rw [<- hCoord, <- Real.norm_eq_abs]
    exact (norm_le_pi_norm (logMap x) v).trans hL
  have hPos (w : InfinitePlace K) : 0 < normAtPlace w x :=
    fundamentalCone.normAtPlace_pos_of_mem hx w
  have hprod : Finset.univ.prod (fun w : InfinitePlace K => normAtPlace w x ^ w.mult) = 1 :=
    (mixedEmbedding.norm_apply x).symm.trans hx1
  have hsum : Finset.univ.sum g = 0 := by
    have hLog := Real.log_prod (s := Finset.univ)
      (f := fun w : InfinitePlace K => normAtPlace w x ^ w.mult)
      (fun w _ => pow_ne_zero _ (hPos w).ne')
    simpa only [g, hprod, Real.log_one, Real.log_pow] using hLog.symm
  have he : A.sum g + g e = Finset.univ.sum g :=
    Finset.sum_erase_add _ g (Finset.mem_univ e)
  have he' : g e = -(A.sum g) := by linarith only [he, hsum]
  have hLarge : abs (g e) <= (A.card : Real) * R := by
    rw [he', abs_neg]
    calc
      abs (A.sum g) <= A.sum (fun w => abs (g w)) := Finset.abs_sum_le_sum_abs _ _
      _ <= A.sum (fun _ => R) := by
        apply Finset.sum_le_sum
        intro w hw
        exact hSmall w (Finset.mem_erase.mp hw).1
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hAll (w : InfinitePlace K) : abs (g w) <= S := by
    by_cases h : w = e
    . subst w
      exact hLarge.trans (le_max_right _ _)
    . exact (hSmall w h).trans (le_max_left _ _)
  rw [norm_eq_sup'_normAtPlace]
  apply Finset.sup'_le
  intro w _
  have hOne : 1 <= (w.mult : Real) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (InfinitePlace.mult_ne_zero (w := w))
  have hComp : abs (g w) = (w.mult : Real) * abs (Real.log (normAtPlace w x)) := by
    simp only [g, abs_mul, Nat.abs_cast]
  have hLogW : Real.log (normAtPlace w x) <= S := by
    calc
      _ <= abs (Real.log (normAtPlace w x)) := le_abs_self _
      _ <= (w.mult : Real) * abs (Real.log (normAtPlace w x)) :=
        le_mul_of_one_le_left (abs_nonneg _) hOne
      _ = abs (g w) := hComp.symm
      _ <= S := hAll w
  calc
    normAtPlace w x = Real.exp (Real.log (normAtPlace w x)) := (Real.exp_log (hPos w)).symm
    _ <= Real.exp S := Real.exp_le_exp.mpr hLogW

/-- A compact archimedean set meets every integral-unit orbit at norm one. -/
theorem exists_compact_mixedNormOne_unitRepresentatives :
    Exists (fun C : Set (mixedSpace K) =>
      And (IsCompact C) (And
        (forall x : mixedSpace K, Membership.mem C x -> mixedEmbedding.norm x = 1)
        (forall x : mixedSpace K, mixedEmbedding.norm x = 1 ->
          Exists (fun u : Units (RingOfIntegers K) => Membership.mem C (HSMul.hSMul u x))))) := by
  choose R hR using exists_normOneCone_normBound K
  let S := Set.ofPred (fun x : mixedSpace K => mixedEmbedding.norm x = 1)
  let C := Inter.inter (Metric.closedBall (0 : mixedSpace K) R) S
  have hS : IsClosed S := isClosed_eq (mixedEmbedding.continuous_norm K) continuous_const
  have hC : IsCompact C := (isCompact_closedBall _ _).inter_right hS
  refine Exists.intro C (And.intro hC (And.intro (fun _ hx => hx.2) ?_))
  intro x hx
  have h0 : Not (mixedEmbedding.norm x = 0) := by rw [hx]; exact one_ne_zero
  choose u hu using fundamentalCone.exists_unit_smul_mem h0
  have hNu : mixedEmbedding.norm (HSMul.hSMul u x) = 1 := by
    rw [norm_unit_smul, hx]
  refine Exists.intro u (And.intro ?_ hNu)
  exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hR _ hu hNu)


/-- A compact archimedean set meets every integral-unit orbit at any positive norm. -/
theorem exists_compact_mixedNorm_unitRepresentatives (r : Real) (hr : 0 < r) :
    Exists (fun C : Set (mixedSpace K) =>
      And (IsCompact C) (And
        (forall x : mixedSpace K, Membership.mem C x -> mixedEmbedding.norm x = r)
        (forall x : mixedSpace K, mixedEmbedding.norm x = r ->
          Exists (fun u : Units (RingOfIntegers K) => Membership.mem C (HSMul.hSMul u x))))) := by
  choose C hC using exists_compact_mixedNormOne_unitRepresentatives K
  let n := Module.finrank Rat K
  let c : Real := Real.rpow r (Inv.inv (n : Real))
  have hinv (t : Real) (ht : Not (t = 0)) : Inv.inv t * t = 1 := by
    rw [mul_comm, <- div_eq_mul_inv, div_self ht]
  have hn : 0 < (n : Real) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank Rat K)
  have hc : 0 < c := Real.rpow_pos_of_pos hr _
  have hcn : c ^ n = r := by
    calc
      c ^ n = c ^ (n : Real) := (Real.rpow_natCast c n).symm
      _ = r ^ (Inv.inv (n : Real) * (n : Real)) :=
        (Real.rpow_mul hr.le (Inv.inv (n : Real)) (n : Real)).symm
      _ = r := by rw [hinv _ hn.ne', Real.rpow_one]
  let S := Set.image (fun x : mixedSpace K => HSMul.hSMul c x) C
  have hCont : Continuous (fun x : mixedSpace K => HSMul.hSMul c x) := by
    let L := HSMul.hSMul c (ContinuousLinearMap.id Real (mixedSpace K))
    exact L.continuous
  have hS : IsCompact S := hC.1.image hCont
  refine Exists.intro S (And.intro hS (And.intro ?_ ?_))
  . intro y hy
    choose x hx using hy
    rw [<- hx.2, mixedEmbedding.norm_smul, abs_of_pos hc, hcn, hC.2.1 x hx.1, mul_one]
  . intro x hx
    let z : mixedSpace K := HSMul.hSMul (Inv.inv c) x
    have hz : mixedEmbedding.norm z = 1 := by
      change mixedEmbedding.norm (HSMul.hSMul (Inv.inv c) x) = 1
      rw [mixedEmbedding.norm_smul, abs_inv, abs_of_pos hc, inv_pow, hcn, hx, hinv _ hr.ne']
    choose u hu using hC.2.2 z hz
    refine Exists.intro u (Exists.intro (HSMul.hSMul u z) (And.intro hu ?_))
    change HSMul.hSMul c (HSMul.hSMul u (HSMul.hSMul (Inv.inv c) x)) = HSMul.hSMul u x
    rw [unitSMul_smul, unitSMul_smul, mul_smul_comm, smul_smul,
      mul_comm c (Inv.inv c), hinv _ hc.ne', one_smul]

omit [NumberField K] in
private theorem continuous_heckeInfiniteAdele_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  apply continuous_pi
  intro w
  by_cases hw : InfinitePlace.IsReal w
  . let v : Subtype (InfinitePlace.IsReal : InfinitePlace K -> Prop) := Subtype.mk w hw
    let k := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    have he (z : mixedSpace K) : E.symm z w = k.symm (z.1 v) := by
      have h : k (E.symm z w) = z.1 v :=
        congrArg (fun y : mixedSpace K => y.1 v) (E.apply_symm_apply z)
      rw [<- h, k.symm_apply_apply]
    exact (k.symm.continuous.comp ((continuous_apply v).comp continuous_fst)).congr
      (fun z => (he z).symm)
  . have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let v : Subtype (InfinitePlace.IsComplex : InfinitePlace K -> Prop) := Subtype.mk w hc
    let k := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    have he (z : mixedSpace K) : E.symm z w = k.symm (z.2 v) := by
      have h : k (E.symm z w) = z.2 v :=
        congrArg (fun y : mixedSpace K => y.2 v) (E.apply_symm_apply z)
      rw [<- h, k.symm_apply_apply]
    exact (k.symm.continuous.comp ((continuous_apply v).comp continuous_snd)).congr
      (fun z => (he z).symm)

private abbrev ArchNormFiber (r : Real) :=
  Subtype (fun z : mixedSpace K => mixedEmbedding.norm z = r)

private theorem mixedNormFiber_mul_inv (r : Real) (hr : 0 < r) (z : ArchNormFiber K r) :
    z.val * Inv.inv z.val = 1 := by
  apply DedekindZeta.Theta.mul_inv_cancel_of_norm_ne_zero K
  rw [z.property]
  exact hr.ne'

private noncomputable def heckeInfiniteUnitOfMixed (r : Real) (hr : 0 < r)
    (z : ArchNormFiber K r) : Units (InfiniteAdeleRing K) :=
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  { val := E.symm z.val
    inv := E.symm (Inv.inv z.val)
    val_inv := by rw [<- map_mul, mixedNormFiber_mul_inv K r hr, map_one]
    inv_val := by rw [<- map_mul, mul_comm, mixedNormFiber_mul_inv K r hr, map_one] }

private theorem continuous_heckeInfiniteUnitOfMixed (r : Real) (hr : 0 < r) :
    Continuous (heckeInfiniteUnitOfMixed K r hr) := by
  have hR (z : ArchNormFiber K r) (v : Subtype (InfinitePlace.IsReal : InfinitePlace K -> Prop)) :
      Not (z.val.1 v = 0) := by
    have h : z.val.1 v * Inv.inv (z.val.1 v) = 1 :=
      congrArg (fun x : mixedSpace K => x.1 v) (mixedNormFiber_mul_inv K r hr z)
    intro hz
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  have hC (z : ArchNormFiber K r) (v : Subtype (InfinitePlace.IsComplex : InfinitePlace K -> Prop)) :
      Not (z.val.2 v = 0) := by
    have h : z.val.2 v * Inv.inv (z.val.2 v) = 1 :=
      congrArg (fun x : mixedSpace K => x.2 v) (mixedNormFiber_mul_inv K r hr z)
    intro hz
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  have hInv : Continuous (fun z : ArchNormFiber K r => Inv.inv z.val) := by
    apply Continuous.prodMk
    . apply continuous_pi
      intro v
      change Continuous (fun z : ArchNormFiber K r => Inv.inv (z.val.1 v))
      have h : forall z : ArchNormFiber K r, Not (z.val.1 v = 0) := fun z => hR z v
      fun_prop (disch := first | assumption | exact h _)
    . apply continuous_pi
      intro v
      change Continuous (fun z : ArchNormFiber K r => Inv.inv (z.val.2 v))
      have h : forall z : ArchNormFiber K r, Not (z.val.2 v = 0) := fun z => hC z v
      fun_prop (disch := first | assumption | exact h _)
  exact Units.continuous_iff.mpr (And.intro
    ((continuous_heckeInfiniteAdele_mixedSpace_symm K).comp continuous_subtype_val)
    ((continuous_heckeInfiniteAdele_mixedSpace_symm K).comp hInv))

/-- The infinite idele attached to a unit of the ring of integers. -/
noncomputable def heckeGlobalIntegralUnitToInfinite (u : Units (RingOfIntegers K)) :
    Units (InfiniteAdeleRing K) :=
  Units.map ((algebraMap K (InfiniteAdeleRing K)).comp (algebraMap (RingOfIntegers K) K)).toMonoidHom u

/-- At a prescribed positive norm, infinite ideles have compact representatives modulo global units. -/
theorem exists_compact_heckeInfiniteIdeleNorm_unitRepresentatives (r : Real) (hr : 0 < r) :
    Exists (fun C : Set (Units (InfiniteAdeleRing K)) => And (IsCompact C) (And
      (forall a : Units (InfiniteAdeleRing K), Membership.mem C a -> heckeInfiniteIdeleNorm a = r)
      (forall a : Units (InfiniteAdeleRing K), heckeInfiniteIdeleNorm a = r ->
        Exists (fun u : Units (RingOfIntegers K) =>
          Membership.mem C (heckeGlobalIntegralUnitToInfinite K u * a))))) := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  choose S hS using exists_compact_mixedNorm_unitRepresentatives K r hr
  let C := Set.image (heckeInfiniteUnitOfMixed K r hr) (Set.preimage Subtype.val S)
  have hClosed : IsClosed (Set.ofPred (fun z : mixedSpace K => mixedEmbedding.norm z = r)) :=
    isClosed_eq (mixedEmbedding.continuous_norm K) continuous_const
  have hPre : IsCompact (Set.preimage (Subtype.val : ArchNormFiber K r -> mixedSpace K) S) :=
    hClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hS.1
  refine Exists.intro C (And.intro (hPre.image (continuous_heckeInfiniteUnitOfMixed K r hr))
    (And.intro ?_ ?_))
  . intro a ha
    choose z hz hz' using ha
    rw [<- mixedEmbedding_norm_infiniteIdele, <- hz']
    change mixedEmbedding.norm (E (E.symm z.val)) = r
    rw [E.apply_symm_apply]
    exact z.property
  . intro a ha
    have h : mixedEmbedding.norm (E a.val) = r := by
      rw [mixedEmbedding_norm_infiniteIdele, ha]
    choose u hu using hS.2.2 (E a.val) h
    have hz : mixedEmbedding.norm (HSMul.hSMul u (E a.val)) = r := hS.2.1 _ hu
    refine Exists.intro u (Exists.intro (Subtype.mk _ hz) (And.intro hu ?_))
    apply Units.ext
    apply E.injective
    change E (E.symm (HSMul.hSMul u (E a.val))) =
      E (algebraMap K (InfiniteAdeleRing K) (algebraMap (RingOfIntegers K) K u.val) * a.val)
    rw [E.apply_symm_apply, map_mul, unitSMul_smul]
    exact congrArg (fun z : mixedSpace K => z * E a.val)
      (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := K))

private abbrev GlobalIdeles :=
  Units (AdeleRing (RingOfIntegers K) K)

private abbrev LocalFiniteIdeles :=
  Units (FiniteAdeleRing (RingOfIntegers K) K)

private abbrev FractionalIntegerIdeal :=
  FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K

/-- The subgroup of ideles whose global idelic norm equals one. -/
noncomputable def heckeNormOneIdeles : Subgroup (Units (AdeleRing (RingOfIntegers K) K)) :=
  (heckeIdelicNorm (K := K)).toHomUnits.ker

private theorem mem_heckeNormOneIdeles (a : GlobalIdeles K) :
    Membership.mem (heckeNormOneIdeles K) a <-> heckeIdelicNorm a = 1 := by
  change _ = _ <-> _
  exact Iff.intro (congrArg Units.val) (fun h => Units.ext h)

/-- The principal idele has norm one by the product formula. -/
noncomputable def heckePrincipalNormOneIdele : MonoidHom (Units K) (heckeNormOneIdeles K) :=
  (Units.map (algebraMap K (AdeleRing (RingOfIntegers K) K)).toMonoidHom).codRestrict
    (heckeNormOneIdeles K) (fun a => (mem_heckeNormOneIdeles K _).mpr (heckeIdelicNorm_principal a))

/-- The group of norm-one idele classes modulo principal ideles. -/
noncomputable abbrev heckeNormOneIdeleClass :=
  HasQuotient.Quotient (heckeNormOneIdeles K) (heckePrincipalNormOneIdele K).range

private theorem finiteIdele_algebraUnit_mem_integralUnits (u : Units (RingOfIntegers K)) :
    Membership.mem heckeIntegralFiniteUnitGroup
      (FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K
        (Units.map (algebraMap (RingOfIntegers K) K).toMonoidHom u)) := by
  apply (heckeFiniteIdeleIdealHom_eq_one_iff _).mp
  rw [heckeFiniteIdeleIdealHom_principal]
  apply Units.ext
  change (toPrincipalIdeal (RingOfIntegers K) K
    (Units.map (algebraMap (RingOfIntegers K) K).toMonoidHom u)).val =
      (1 : FractionalIntegerIdeal K)
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton (nonZeroDivisors (RingOfIntegers K))
    (algebraMap (RingOfIntegers K) K u.val) = 1
  rw [<- FractionalIdeal.coeIdeal_span_singleton,
    Ideal.span_singleton_eq_top.mpr u.isUnit, FractionalIdeal.coeIdeal_top]

/-- A compact subset of the norm-one ideles surjects onto the norm-one idele class group. -/
theorem exists_compact_heckeNormOneIdeleRepresentatives :
    Exists (fun S : Set (heckeNormOneIdeles K) =>
      And (IsCompact S)
        (Set.image (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S = Set.univ)) := by
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let : MeasurableSpace F := borel F
  let : BorelSpace F := BorelSpace.mk rfl
  let I := GlobalIdeles K
  let A := Units (InfiniteAdeleRing K)
  let B := LocalFiniteIdeles K
  let T : Homeomorph I (Prod A B) := Homeomorph.prodUnits
  let H := heckeNormOneIdeles K
  let P := heckePrincipalNormOneIdele K
  let q := QuotientGroup.mk' P.range
  let C := ClassGroup (RingOfIntegers K)
  let U := heckeIntegralFiniteUnitGroup (K := K)
  let infPart : MonoidHom I A :=
    Units.map (RingHom.fst (InfiniteAdeleRing K) F).toMonoidHom
  let finPart : MonoidHom I B :=
    Units.map (RingHom.snd (InfiniteAdeleRing K) F).toMonoidHom
  let pinf : MonoidHom (Units K) A := Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom
  let pfin := FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K
  have hInfP (x : Units K) : infPart (P x).val = pinf x := Units.ext rfl
  have hFinP (x : Units K) : finPart (P x).val = pfin x := Units.ext rfl
  have hNorm (y : H) :
      heckeInfiniteIdeleNorm (infPart y.val) * heckeFiniteIdeleNorm (finPart y.val) = 1 :=
    (mem_heckeNormOneIdeles K y.val).mp y.property
  choose b hb using (surjective_heckeFiniteIdeleClass (K := K))
  let r (k : C) : Real := Inv.inv (heckeFiniteIdeleNorm (b k))
  have hr (k : C) : 0 < r k := inv_pos.mpr (heckeFiniteIdeleNorm_pos (b k))
  choose V hVc hV using (fun k : C => exists_compact_heckeInfiniteIdeleNorm_unitRepresentatives K (r k) (hr k))
  let W (k : C) : Set B := Set.image (fun u : B => b k * u) U.carrier
  have hW (k : C) : IsCompact (W k) :=
    isCompact_heckeIntegralFiniteUnitGroup.image (continuous_const.mul continuous_id)
  let D (k : C) : Set I := Set.image T.symm (Set.prod (V k) (W k))
  have hD (k : C) : IsCompact (D k) := ((hVc k).prod (hW k)).image T.symm.continuous
  let E : Set I := Set.iUnion D
  have hE : IsCompact E := isCompact_iUnion hD
  have hH : IsClosed H.carrier := by
    have hEq : H.carrier = Set.ofPred (fun a : I => heckeIdelicNorm a = 1) :=
      Set.ext (mem_heckeNormOneIdeles K)
    rw [hEq]
    exact isClosed_eq continuous_heckeIdelicNorm continuous_const
  let S : Set H := Set.preimage Subtype.val E
  have hS : IsCompact S := hH.isClosedEmbedding_subtypeVal.isCompact_preimage hE
  have hPq (x : Units K) : q (P x) = 1 :=
    (QuotientGroup.eq_one_iff (P x)).mpr (Exists.intro x rfl)
  have hCover : Set.image q S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    choose a ha using (Quotient.mk_surjective w)
    let k : C := heckeFiniteIdeleClass (finPart a.val)
    have hSame : heckeFiniteIdeleClass (finPart a.val) = heckeFiniteIdeleClass (b k) := (hb k).symm
    choose x u hu hFin using heckeFiniteIdele_exists_principal_mul_integral (finPart a.val) (b k) hSame
    let z : H := P (Inv.inv x) * a
    have hZf : finPart z.val = b k * u := by
      change finPart ((P (Inv.inv x)).val * a.val) = _
      rw [map_mul, hFinP, map_inv, hFin, <- mul_assoc, <- mul_assoc, inv_mul_cancel, one_mul]
    have hNz : heckeInfiniteIdeleNorm (infPart z.val) = r k := by
      have h := hNorm z
      rw [hZf, map_mul, heckeFiniteIdeleNorm_eq_one_of_integralUnit u hu, mul_one] at h
      exact eq_inv_of_mul_eq_one_left h
    choose v hv using (hV k).2 (infPart z.val) hNz
    let vK := Units.map (algebraMap (RingOfIntegers K) K).toMonoidHom v
    let y : H := P vK * z
    have hYi : Membership.mem (V k) (infPart y.val) := by
      change Membership.mem (V k) (infPart ((P vK).val * z.val))
      rw [map_mul, hInfP]
      exact hv
    have hYf : Membership.mem (W k) (finPart y.val) := by
      have hVf : Membership.mem U (pfin vK) := finiteIdele_algebraUnit_mem_integralUnits K v
      refine Exists.intro (pfin vK * u) (And.intro (U.mul_mem hVf hu) ?_)
      change b k * (pfin vK * u) = finPart ((P vK).val * z.val)
      rw [map_mul, hFinP, hZf]
      ac_rfl
    have hY : Membership.mem S y := by
      change Membership.mem (Set.iUnion D) y.val
      apply Set.mem_iUnion.mpr
      refine Exists.intro k (Exists.intro (T y.val) (And.intro ?_ (T.symm_apply_apply y.val)))
      exact And.intro hYi hYf
    have hYq : q y = w := by
      change q (P vK * (P (Inv.inv x) * a)) = w
      rw [map_mul, map_mul, hPq, hPq]
      calc
        _ = q a := (one_mul (1 * q a)).trans (one_mul (q a))
        _ = w := ha
    exact Exists.intro y (And.intro hY hYq)
  exact Exists.intro S (And.intro hS hCover)

/-- The norm-one idele class group of a number field is compact. -/
theorem compactSpace_heckeNormOneIdeleClass : CompactSpace (heckeNormOneIdeleClass K) := by
  choose S hS using exists_compact_heckeNormOneIdeleRepresentatives K
  refine CompactSpace.mk ?_
  rw [<- hS.2]
  exact hS.1.image QuotientGroup.continuous_mk

/-- Principal ideles are discrete in the group of norm-one ideles. -/
theorem discreteTopology_heckePrincipalNormOneIdeles :
    DiscreteTopology (heckePrincipalNormOneIdele K).range := by
  let A := AdeleRing (RingOfIntegers K) K
  let H := (heckePrincipalNormOneIdele K).range
  let P := heckePrincipalNormOneIdele K
  choose U hU using exists_adelicNeighborhood_inter_principal_eq_zero K
  let f : H -> A := fun a => a.val.val.val - 1
  have hF : Continuous f := by
    have hV : Continuous (fun a : H => a.val.val.val) :=
      (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val
    exact hV.sub continuous_const
  have hEq : Set.preimage f U = ({1} : Set H) := by
    ext a
    constructor
    . intro ha
      choose x hx using a.property
      have h : f a = algebraMap K A (x.val - 1) := by
        change a.val.val.val - 1 = _
        rw [<- hx, map_sub, map_one]
        rfl
      have hX : x.val - 1 = 0 := hU.2.2 _ (by rw [<- h]; exact ha)
      have hx1 : x = 1 := Units.ext (sub_eq_zero.mp hX)
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      change a.val = P 1
      rw [<- hx, hx1]
    . intro ha
      rw [Set.mem_singleton_iff.mp ha]
      change Membership.mem U ((1 : A) - 1)
      rw [sub_self]
      exact hU.2.1
  change DiscreteTopology H
  apply discreteTopology_of_isOpen_singleton_one
  rw [<- hEq]
  exact hU.1.preimage hF

/-- The principal ideles form a closed subgroup of the norm-one ideles. -/
theorem isClosed_heckePrincipalNormOneIdeles :
    IsClosed ((heckePrincipalNormOneIdele K).range :
      Set (heckeNormOneIdeles K)) := by
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let : T2Space F := by
    let projection (a : F) (p : HeightOneSpectrum (RingOfIntegers K)) := a p
    have hInj : Function.Injective projection := DFunLike.coe_injective
    have hCont : Continuous projection := continuous_pi (fun p =>
      RestrictedProduct.continuous_eval p)
    exact T2Space.of_injective_continuous hInj hCont
  let : T2Space (InfiniteAdeleRing K) :=
    show T2Space (forall v : InfinitePlace K, v.Completion) from inferInstance
  let : T2Space (AdeleRing (RingOfIntegers K) K) :=
    show T2Space (Prod (InfiniteAdeleRing K) F) from inferInstance
  let : DiscreteTopology (heckePrincipalNormOneIdele K).range :=
    discreteTopology_heckePrincipalNormOneIdeles K
  exact Subgroup.isClosed_of_discrete

/-- The norm-one idele class group is Hausdorff. -/
theorem t2Space_heckeNormOneIdeleClass : T2Space (heckeNormOneIdeleClass K) := by
  let : IsClosed ((heckePrincipalNormOneIdele K).range :
    Set (heckeNormOneIdeles K)) := isClosed_heckePrincipalNormOneIdeles K
  infer_instance

end Robin1984.GRH
