import Robin1984.GRH.HeckeAdeleTraceDual

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Additive Haar measure and Fourier integration over the compact open integral finite adeles.
- Formalization note: Normalizes finite additive Haar measure on the integral subgroup and evaluates its principal-frequency Fourier integral through the trace-dual ideal.
- PROVENANCE-END
-/

/-!
# Additive Haar measure on the finite adeles

The integral local coordinates form a compact open subgroup. Haar measure
normalized there integrates each principal-frequency character to one on
the corresponding trace-dual ideal and to zero elsewhere.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev HeckeFiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev HeckeAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

/-- The compact open additive subgroup given by all local integer rings. -/
def heckeIntegralFiniteAdeles : AddSubgroup (HeckeFiniteAdeles K) where
  carrier := {a | forall p : HeightOneSpectrum (RingOfIntegers K),
    Membership.mem (p.adicCompletionIntegers K) (a p)}
  zero_mem' := fun p => (p.adicCompletionIntegers K).zero_mem
  add_mem' ha hb := fun p => add_mem (ha p) (hb p)
  neg_mem' ha := fun p => neg_mem (ha p)

/-- The integral subgroup is open in the restricted product topology. -/
theorem isOpen_heckeIntegralFiniteAdeles :
    IsOpen (heckeIntegralFiniteAdeles (K := K) : Set (HeckeFiniteAdeles K)) :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun p : HeightOneSpectrum (RingOfIntegers K) => p.adicCompletion K)
    (A := fun p => (p.adicCompletionIntegers K : Set (p.adicCompletion K)))
    (fun p => Valued.isOpen_valuationSubring (p.adicCompletion K))

private def heckeIntegralFinitePositiveCompact : PositiveCompacts (HeckeFiniteAdeles K) where
  toCompacts := {
    carrier := (heckeIntegralFiniteAdeles (K := K) : Set (HeckeFiniteAdeles K))
    isCompact' := isCompact_integralFiniteAdeles (K := K) }
  interior_nonempty' := by
    rw [isOpen_heckeIntegralFiniteAdeles.interior_eq]
    exact Exists.intro 0 (heckeIntegralFiniteAdeles (K := K)).zero_mem

/-- The finite adele ring is locally compact under addition. -/
theorem locallyCompactSpace_heckeFiniteAdeles : LocallyCompactSpace (HeckeFiniteAdeles K) :=
  (heckeIntegralFinitePositiveCompact (K := K)).locallyCompactSpace_of_addGroup

variable [MeasurableSpace (HeckeFiniteAdeles K)] [BorelSpace (HeckeFiniteAdeles K)]

/-- Additive Haar measure giving the product of the finite integer rings
mass one. -/
noncomputable def heckeFiniteAdeleHaar : Measure (HeckeFiniteAdeles K) :=
  Measure.addHaarMeasure heckeIntegralFinitePositiveCompact

instance heckeFiniteAdeleHaar_isAddLeftInvariant :
    Measure.IsAddLeftInvariant (heckeFiniteAdeleHaar (K := K)) :=
  inferInstanceAs (Measure.IsAddLeftInvariant
    (Measure.addHaarMeasure (heckeIntegralFinitePositiveCompact (K := K))))

/-- The chosen Haar measure gives the integral subgroup mass one. -/
theorem heckeFiniteAdeleHaar_integral :
    heckeFiniteAdeleHaar (heckeIntegralFiniteAdeles (K := K) : Set (HeckeFiniteAdeles K)) = 1 := by
  change Measure.addHaarMeasure (heckeIntegralFinitePositiveCompact (K := K))
    (heckeIntegralFinitePositiveCompact (K := K) : Set (HeckeFiniteAdeles K)) = 1
  exact Measure.addHaarMeasure_self

/-- The finite Fourier integral of the integral subgroup, at a frequency
scaled by a principal modulus, is the indicator of the trace-dual ideal. -/
theorem integral_heckeFiniteAdeleHaar_character
    (d : RingOfIntegers K) (hd : Not (d = 0)) (t : K) :
    integral (heckeFiniteAdeleHaar.restrict
        (heckeIntegralFiniteAdeles (K := K) : Set (HeckeFiniteAdeles K)))
      (fun a : HeckeFiniteAdeles K =>
        ((heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K)
          (a * algebraMap K (HeckeFiniteAdeles K) (algebraMap (RingOfIntegers K) K d * t)) :
          HeckeAdeles K)) : Complex)) =
      if Membership.mem
        (DedekindZeta.Theta.dualIdeal K (Ideal.span ({d} : Set (RingOfIntegers K))) :
          Submodule (RingOfIntegers K) K) t then 1 else 0 := by
  let A := HeckeFiniteAdeles K
  let H : AddSubgroup A := heckeIntegralFiniteAdeles
  let mu : Measure A := heckeFiniteAdeleHaar
  let e := algebraMap K A (algebraMap (RingOfIntegers K) K d * t)
  let psi (a : A) := ((heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K) (a * e) :
    HeckeAdeles K)) : Complex)
  let J := integral (mu.restrict (H : Set A)) psi
  let Q := (DedekindZeta.Theta.dualIdeal K (Ideal.span ({d} : Set (RingOfIntegers K))) :
    Submodule (RingOfIntegers K) K)
  change J = if Membership.mem Q t then 1 else 0
  have hH : MeasurableSet (H : Set A) := isOpen_heckeIntegralFiniteAdeles.measurableSet
  have hAdd (x y : A) : psi (x + y) = psi x * psi y := by
    let r (a : A) : HeckeAdeles K := Prod.mk 0 (a * e)
    have hr : r (x + y) = r x + r y := by
      change Prod.mk (0 : InfiniteAdeleRing K) ((x + y) * e) =
        Prod.mk ((0 : InfiniteAdeleRing K) + 0) (x * e + y * e)
      rw [zero_add, add_mul]
    change ((heckeAdeleAddChar (r (x + y))) : Complex) =
      ((heckeAdeleAddChar (r x)) : Complex) * ((heckeAdeleAddChar (r y)) : Complex)
    rw [hr, AddChar.map_add_eq_mul, Circle.coe_mul]
  by_cases ht : Membership.mem Q t
  case pos =>
    rw [if_pos ht]
    have hGood := (heckeAdeleAddChar_finitePrincipalIdeal_annihilator_iff d hd t).mpr ht
    have hConst : Set.EqOn psi (fun _ => (1 : Complex)) (H : Set A) := by
      intro a ha
      have h := hGood a ha
      exact congrArg (fun z : Circle => (z : Complex)) h
    change integral (mu.restrict (H : Set A)) psi = 1
    rw [setIntegral_congr_fun hH hConst, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ]
    have hMu : mu (H : Set A) = 1 := heckeFiniteAdeleHaar_integral
    rw [hMu, ENNReal.toReal_one, one_smul]
  case neg =>
    rw [if_neg ht]
    by_contra hJ
    apply ht
    apply (heckeAdeleAddChar_finitePrincipalIdeal_annihilator_iff d hd t).mp
    intro a ha
    have haH : Membership.mem H a := ha
    let : Measure.IsAddLeftInvariant mu := heckeFiniteAdeleHaar_isAddLeftInvariant
    have hShift : Set.image (fun b : A => b + a) (H : Set A) = (H : Set A) := by
      ext y
      constructor
      case mp =>
        intro hy
        choose b hb using hy
        rw [<- hb.2]
        exact H.add_mem hb.1 haH
      case mpr =>
        intro hy
        exact Exists.intro (y - a) (And.intro (H.sub_mem hy haH) (sub_add_cancel _ _))
    have hMP : MeasurePreserving (fun b : A => b + a) mu mu :=
      measurePreserving_add_right mu a
    have hI := hMP.setIntegral_image_emb (Homeomorph.addRight a).measurableEmbedding
      psi (H : Set A)
    have hTranslate : (fun b : A => psi (b + a)) = fun b => psi a * psi b := by
      funext b
      rw [add_comm b a, hAdd]
    rw [hShift, hTranslate, integral_const_mul] at hI
    change J = psi a * J at hI
    have hZero : (psi a - 1) * J = 0 := by
      rw [sub_mul, one_mul, <- hI, sub_self]
    apply Subtype.ext
    exact sub_eq_zero.mp ((mul_eq_zero.mp hZero).resolve_right hJ)

/-- The principal multiple of the integral finite adeles. -/
noncomputable def heckeScaledIntegralFiniteAdeles (d : K) : AddSubgroup (HeckeFiniteAdeles K) :=
  heckeIntegralFiniteAdeles.map {
    toFun := fun z => z * algebraMap K (HeckeFiniteAdeles K) d
    map_zero' := zero_mul _
    map_add' := fun _ _ => add_mul _ _ _ }

/-- Division by the principal scalar tests membership in the scaled subgroup. -/
theorem mem_heckeScaledIntegralFiniteAdeles_iff
    (d : K) (hd : Not (d = 0)) (x : HeckeFiniteAdeles K) :
    Membership.mem (heckeScaledIntegralFiniteAdeles d) x <->
    forall p : HeightOneSpectrum (RingOfIntegers K), Membership.mem (p.adicCompletionIntegers K)
      (x p / algebraMap K (p.adicCompletion K) d) := by
  let A := HeckeFiniteAdeles K
  let g := algebraMap K A
  have hInv : Inv.inv d * d = 1 := by field_simp [hd]
  constructor
  case mp =>
    intro hx
    choose y hy using AddSubgroup.mem_map.mp hx
    intro p
    let e := algebraMap K (p.adicCompletion K)
    have he : Not (e d = 0) := (map_ne_zero_iff e e.injective).mpr hd
    have hEq : y * g d = x := hy.2
    rw [<- hEq]
    change Membership.mem (p.adicCompletionIntegers K) (y p * e d / e d)
    rw [(div_eq_iff he).mpr (show y p * e d = y p * e d from rfl)]
    exact hy.1 p
  case mpr =>
    intro h
    apply AddSubgroup.mem_map.mpr
    refine Exists.intro (x * g (Inv.inv d)) (And.intro ?_ ?_)
    case refine_1 =>
      intro p
      let e := algebraMap K (p.adicCompletion K)
      have he : Not (e d = 0) := (map_ne_zero_iff e e.injective).mpr hd
      have hE : e (Inv.inv d) = 1 / e d := by
        apply (eq_div_iff he).2
        rw [<- map_mul, hInv, map_one]
      change Membership.mem (p.adicCompletionIntegers K) (x p * e (Inv.inv d))
      rw [hE, one_div, <- div_eq_mul_inv]
      exact h p
    case refine_2 =>
      change (x * g (Inv.inv d)) * g d = x
      rw [mul_assoc, <- map_mul, hInv, map_one, mul_one]

private theorem heckeScaledIntegralFiniteAdeles_le (d : RingOfIntegers K) :
    heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d) <=
      heckeIntegralFiniteAdeles := by
  intro x hx
  choose y hy using AddSubgroup.mem_map.mp hx
  have hEq : y * algebraMap K (HeckeFiniteAdeles K) (algebraMap (RingOfIntegers K) K d) = x :=
    hy.2
  rw [<- hEq]
  intro p
  change Membership.mem (p.adicCompletionIntegers K)
    (y p * algebraMap (RingOfIntegers K) (p.adicCompletion K) d)
  exact mul_mem (hy.1 p) (HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers K) K p d)

/-- Scaling the compact open integral finite adeles by a principal
integer divides their Haar mass by the norm of its principal ideal. -/
theorem heckeFiniteAdeleHaar_scaledIntegral_mass
    (d : RingOfIntegers K) (hd : Not (d = 0)) :
    (Ideal.absNorm (Ideal.span ({d} : Set (RingOfIntegers K))) : ENNReal) *
      heckeFiniteAdeleHaar (heckeScaledIntegralFiniteAdeles
        (algebraMap (RingOfIntegers K) K d) : Set (HeckeFiniteAdeles K)) = 1 := by
  let R := RingOfIntegers K
  let A := HeckeFiniteAdeles K
  let e := algebraMap R K
  let g := algebraMap K A
  let dd := e d
  let H : AddSubgroup A := heckeIntegralFiniteAdeles
  let D := heckeScaledIntegralFiniteAdeles dd
  let I : Ideal R := Ideal.span {d}
  let Q := HasQuotient.Quotient R I
  let mu : Measure A := heckeFiniteAdeleHaar
  let : Measure.IsAddLeftInvariant mu := heckeFiniteAdeleHaar_isAddLeftInvariant
  have hD : Not (dd = 0) := (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective R K)).mpr hd
  have hI : Not (I = 0) := fun h => hd (Ideal.span_singleton_eq_bot.mp h)
  let : I.toAddSubgroup.FiniteIndex := Ideal.finiteIndex hI
  let : Finite Q := inferInstanceAs (Finite (HasQuotient.Quotient R I.toAddSubgroup))
  let : Fintype Q := Fintype.ofFinite Q
  have hSurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  let repr (c : Q) := Classical.choose (hSurj c)
  have hRepr (c : Q) : Ideal.Quotient.mk I (repr c) = c :=
    Classical.choose_spec (hSurj c)
  let rho (c : Q) := g (e (repr c))
  let C (c : Q) := Set.image (fun z : A => rho c + z) (D : Set A)
  have hHtoD : D <= H := heckeScaledIntegralFiniteAdeles_le d
  have hG (b : R) : Membership.mem H (g (e b)) :=
    fun p => HeightOneSpectrum.coe_algebraMap_mem R K p b
  have hCoeff (b : R) : Membership.mem D (g (e b)) <-> Membership.mem I b := by
    rw [mem_heckeScaledIntegralFiniteAdeles_iff dd hD]
    change (forall p : HeightOneSpectrum R, Membership.mem (p.adicCompletionIntegers K)
      (algebraMap K (p.adicCompletion K) (e b) / algebraMap K (p.adicCompletion K) dd)) <-> _
    rw [principal_mem_finiteAdele_modulus_iff (e b) dd hD, Ideal.mem_span_singleton]
    apply exists_congr
    intro y
    rw [<- map_mul]
    exact (FaithfulSMul.algebraMap_injective R K).eq_iff
  have hDisjoint : Pairwise (fun c j : Q => Disjoint (C c) (C j)) := by
    intro c j hne
    apply Set.disjoint_left.mpr
    intro a ha hb
    choose x hx using ha
    choose y hy using hb
    have hEq : rho c + x = rho j + y := hx.2.trans hy.2.symm
    have hDiff : rho c - rho j = y - x := by
      calc
        rho c - rho j = (rho c + x) - (rho j + x) := by abel
        _ = y - x := by rw [hEq]; abel
    have hIn : Membership.mem D (g (e (repr c - repr j))) := by
      rw [map_sub e, map_sub g]
      change Membership.mem D (rho c - rho j)
      rw [hDiff]
      exact D.sub_mem hy.1 hx.1
    apply hne
    have hRel := (Ideal.Quotient.eq (I := I)).mpr ((hCoeff _).mp hIn)
    rw [hRepr, hRepr] at hRel
    exact hRel
  have hCover : Set.iUnion C = (H : Set A) := by
    ext a
    constructor
    case mp =>
      intro ha
      choose c hc using Set.mem_iUnion.mp ha
      choose x hx using hc
      rw [<- hx.2]
      exact H.add_mem (hG (repr c)) (hHtoD hx.1)
    case mpr =>
      intro ha
      choose x hx using exists_finiteAdele_sub_principal_modulus a dd hD
      have hIn : Membership.mem D (a - g x) :=
        (mem_heckeScaledIntegralFiniteAdeles_iff dd hD _).mpr hx
      have hxH : Membership.mem H (g x) := by
        have hh := H.sub_mem ha (hHtoD hIn)
        rw [sub_sub_cancel] at hh
        exact hh
      have hxR : Exists (fun b : R => x = e b) := by
        have hLoc : forall p : HeightOneSpectrum R, Membership.mem (p.adicCompletionIntegers K)
            (algebraMap K (p.adicCompletion K) x / algebraMap K (p.adicCompletion K) 1) := by
          intro p
          rw [map_one, div_one]
          exact hxH p
        simpa only [one_mul] using
          (principal_mem_finiteAdele_modulus_iff x 1 one_ne_zero).mp hLoc
      choose b hb using hxR
      let i := Ideal.Quotient.mk I b
      have hbI : Membership.mem I (b - repr i) :=
        (Ideal.Quotient.eq (I := I)).mp (hRepr i).symm
      have hShift := (hCoeff (b - repr i)).mpr hbI
      rw [map_sub e, map_sub g, <- hb] at hShift
      change Membership.mem D (g x - rho i) at hShift
      have hz : Membership.mem D (a - rho i) := by
        have hEq : a - rho i = (a - g x) + (g x - rho i) := by abel
        rw [hEq]
        exact D.add_mem hIn hShift
      have hzEq : rho i + (a - rho i) = a :=
        (add_comm _ _).trans (sub_add_cancel _ _)
      exact Set.mem_iUnion.mpr (Exists.intro i (Exists.intro (a - rho i) (And.intro hz hzEq)))
  have hDOpen : IsOpen (D : Set A) := by
    have hEq : (D : Set A) = Set.preimage (fun x : A => x * g (Inv.inv dd)) (H : Set A) := by
      ext x
      constructor
      case mp =>
        intro hx
        choose y hy using AddSubgroup.mem_map.mp hx
        have hx' : y * g dd = x := hy.2
        have hInv : dd * Inv.inv dd = 1 := by field_simp [hD]
        change Membership.mem H (x * g (Inv.inv dd))
        rw [<- hx', mul_assoc, <- map_mul, hInv, map_one, mul_one]
        exact hy.1
      case mpr =>
        intro hx
        change Membership.mem H (x * g (Inv.inv dd)) at hx
        apply AddSubgroup.mem_map.mpr
        refine Exists.intro (x * g (Inv.inv dd)) (And.intro hx ?_)
        have hInv : Inv.inv dd * dd = 1 := by field_simp [hD]
        change x * g (Inv.inv dd) * g dd = x
        rw [mul_assoc, <- map_mul, hInv, map_one, mul_one]
    rw [hEq]
    exact isOpen_heckeIntegralFiniteAdeles.preimage (continuous_id.mul continuous_const)
  have hMeas (i : Q) : MeasurableSet (C i) :=
    ((Homeomorph.addLeft (rho i)).isOpenMap _ hDOpen).measurableSet
  have hVol (i : Q) : mu (C i) = mu (D : Set A) := by
    have hp := (measurePreserving_add_left mu (rho i)).measure_preimage (hMeas i).nullMeasurableSet
    have hPre : Set.preimage (fun z : A => rho i + z) (C i) = (D : Set A) :=
      Set.preimage_image_eq _ (fun _ _ h => add_left_cancel h)
    rw [hPre] at hp
    exact hp.symm
  have hNorm : Ideal.absNorm I = Nat.card Q := rfl
  change (Ideal.absNorm I : ENNReal) * mu (D : Set A) = 1
  calc
    _ = tsum (fun _ : Q => mu (D : Set A)) := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNorm,
        Nat.card_eq_fintype_card]
    _ = tsum (fun i : Q => mu (C i)) := tsum_congr (fun i => (hVol i).symm)
    _ = mu (Set.iUnion C) := (measure_iUnion hDisjoint hMeas).symm
    _ = 1 := by rw [hCover]; exact heckeFiniteAdeleHaar_integral

end Robin1984.GRH
