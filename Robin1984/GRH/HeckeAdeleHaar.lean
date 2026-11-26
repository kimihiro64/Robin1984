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

/-- The canonical finite additive character evaluated at a principal frequency. -/
noncomputable def heckeFiniteAdelePrincipalChar (t : K) : AddChar (HeckeFiniteAdeles K) Circle where
  toFun a := heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K) (a * algebraMap K (HeckeFiniteAdeles K) t))
  map_zero_eq_one' := by
    change heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K) (0 * algebraMap K (HeckeFiniteAdeles K) t)) = 1
    rw [zero_mul]
    exact AddChar.map_zero_eq_one _
  map_add_eq_mul' x y := by
    let r (a : HeckeFiniteAdeles K) : AdeleRing (RingOfIntegers K) K :=
      Prod.mk 0 (a * algebraMap K (HeckeFiniteAdeles K) t)
    have hr : r (x + y) = r x + r y := by
      change Prod.mk (0 : InfiniteAdeleRing K) ((x + y) * algebraMap K (HeckeFiniteAdeles K) t) =
        Prod.mk ((0 : InfiniteAdeleRing K) + 0)
          (x * algebraMap K (HeckeFiniteAdeles K) t + y * algebraMap K (HeckeFiniteAdeles K) t)
      rw [zero_add, add_mul]
    change heckeAdeleAddChar (r (x + y)) = heckeAdeleAddChar (r x) * heckeAdeleAddChar (r y)
    rw [hr, AddChar.map_add_eq_mul]

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

private theorem integral_addChar_subgroup
    (H : AddSubgroup (HeckeFiniteAdeles K)) (hH : MeasurableSet (H : Set (HeckeFiniteAdeles K)))
    (chi : AddChar (HeckeFiniteAdeles K) Circle) :
    integral (heckeFiniteAdeleHaar.restrict (H : Set (HeckeFiniteAdeles K))) (fun z => (chi z : Complex)) =
      if forall z, Membership.mem H z -> chi z = 1 then
        ((heckeFiniteAdeleHaar (H : Set (HeckeFiniteAdeles K))).toReal : Complex)
      else 0 := by
  let mu : Measure (HeckeFiniteAdeles K) := heckeFiniteAdeleHaar
  let psi (a : HeckeFiniteAdeles K) : Complex := chi a
  let J := integral (mu.restrict (H : Set (HeckeFiniteAdeles K))) psi
  change J = if forall z, Membership.mem H z -> chi z = 1 then
    ((mu (H : Set (HeckeFiniteAdeles K))).toReal : Complex) else 0
  by_cases ht : forall z, Membership.mem H z -> chi z = 1
  case pos =>
    rw [if_pos ht]
    have hConst : Set.EqOn psi (fun _ => (1 : Complex)) (H : Set (HeckeFiniteAdeles K)) := by
      intro z hz
      exact congrArg (fun a : Circle => (a : Complex)) (ht z hz)
    change integral (mu.restrict (H : Set (HeckeFiniteAdeles K))) psi = _
    rw [setIntegral_congr_fun hH hConst, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, Complex.real_smul, mul_one]
  case neg =>
    rw [if_neg ht]
    by_contra hJ
    apply ht
    intro a ha
    let : Measure.IsAddLeftInvariant mu := heckeFiniteAdeleHaar_isAddLeftInvariant
    have hShift : Set.image (fun b : HeckeFiniteAdeles K => b + a) (H : Set (HeckeFiniteAdeles K)) = (H : Set (HeckeFiniteAdeles K)) := by
      ext y
      constructor
      case mp =>
        intro hy
        choose b hb using hy
        rw [<- hb.2]
        exact H.add_mem hb.1 ha
      case mpr =>
        intro hy
        exact Exists.intro (y - a) (And.intro (H.sub_mem hy ha) (sub_add_cancel _ _))
    have hMP : MeasurePreserving (fun b : HeckeFiniteAdeles K => b + a) mu mu :=
      measurePreserving_add_right mu a
    have hI := hMP.setIntegral_image_emb (Homeomorph.addRight a).measurableEmbedding
      psi (H : Set (HeckeFiniteAdeles K))
    have hTranslate : (fun b : HeckeFiniteAdeles K => psi (b + a)) = fun b => psi a * psi b := by
      funext b
      rw [add_comm b a]
      simp only [psi, AddChar.map_add_eq_mul, Circle.coe_mul]
    rw [hShift, hTranslate, integral_const_mul] at hI
    change J = psi a * J at hI
    have hZero : (psi a - 1) * J = 0 := by
      rw [sub_mul, one_mul, <- hI, sub_self]
    apply Subtype.ext
    exact sub_eq_zero.mp ((mul_eq_zero.mp hZero).resolve_right hJ)

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
  let chi := heckeFiniteAdelePrincipalChar (algebraMap (RingOfIntegers K) K d * t)
  let Q := (DedekindZeta.Theta.dualIdeal K (Ideal.span ({d} : Set (RingOfIntegers K))) :
    Submodule (RingOfIntegers K) K)
  change integral (mu.restrict (H : Set A)) (fun z => (chi z : Complex)) =
    if Membership.mem Q t then 1 else 0
  have hAnn : (forall z, Membership.mem H z -> chi z = 1) <-> Membership.mem Q t :=
    heckeAdeleAddChar_finitePrincipalIdeal_annihilator_iff d hd t
  rw [integral_addChar_subgroup H isOpen_heckeIntegralFiniteAdeles.measurableSet chi]
  by_cases ht : Membership.mem Q t
  case pos =>
    rw [if_pos ht, if_pos (hAnn.mpr ht)]
    change ((mu (H : Set A)).toReal : Complex) = 1
    rw [show mu (H : Set A) = 1 from heckeFiniteAdeleHaar_integral, ENNReal.toReal_one,
      Complex.ofReal_one]
  case neg =>
    rw [if_neg ht, if_neg (fun h => ht (hAnn.mp h))]

/-- The principal multiple of the integral finite adeles. -/
noncomputable def heckeScaledIntegralFiniteAdeles (d : K) : AddSubgroup (HeckeFiniteAdeles K) :=
  heckeIntegralFiniteAdeles.map {
    toFun := fun z => z * algebraMap K (HeckeFiniteAdeles K) d
    map_zero' := zero_mul _
    map_add' := fun _ _ => add_mul _ _ _ }

omit [MeasurableSpace (HeckeFiniteAdeles K)] [BorelSpace (HeckeFiniteAdeles K)] in
/-- A nonzero principal multiple of the integral finite adeles is open. -/
theorem isOpen_heckeScaledIntegralFiniteAdeles (d : K) (hd : Not (d = 0)) :
    IsOpen (heckeScaledIntegralFiniteAdeles d : Set (HeckeFiniteAdeles K)) := by
  let H : AddSubgroup (HeckeFiniteAdeles K) := heckeIntegralFiniteAdeles
  let D := heckeScaledIntegralFiniteAdeles d
  let g := algebraMap K (HeckeFiniteAdeles K)
  have hEq : (D : Set (HeckeFiniteAdeles K)) =
      Set.preimage (fun x : HeckeFiniteAdeles K => x * g (Inv.inv d)) (H : Set (HeckeFiniteAdeles K)) := by
    ext x
    constructor
    case mp =>
      intro hx
      choose y hy using AddSubgroup.mem_map.mp hx
      have hx' : y * g d = x := hy.2
      have hInv : d * Inv.inv d = 1 := by field_simp [hd]
      change Membership.mem H (x * g (Inv.inv d))
      rw [<- hx', mul_assoc, <- map_mul, hInv, map_one, mul_one]
      exact hy.1
    case mpr =>
      intro hx
      change Membership.mem H (x * g (Inv.inv d)) at hx
      apply AddSubgroup.mem_map.mpr
      refine Exists.intro (x * g (Inv.inv d)) (And.intro hx ?_)
      have hInv : Inv.inv d * d = 1 := by field_simp [hd]
      change x * g (Inv.inv d) * g d = x
      rw [mul_assoc, <- map_mul, hInv, map_one, mul_one]
  change IsOpen (D : Set (HeckeFiniteAdeles K))
  rw [hEq]
  exact isOpen_heckeIntegralFiniteAdeles.preimage (continuous_id.mul continuous_const)

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

/-- Multiplication by an integral principal scalar preserves integrality. -/
theorem heckeScaledIntegralFiniteAdeles_le (d : RingOfIntegers K) :
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

private noncomputable def heckePrincipalResidueRepresentative (d : RingOfIntegers K)
    (c : HasQuotient.Quotient (RingOfIntegers K) (Ideal.span ({d} : Set (RingOfIntegers K)))) :
    RingOfIntegers K :=
  Classical.choose (Ideal.Quotient.mk_surjective c)

/-- The principal finite adele attached to a chosen residue representative. -/
noncomputable def heckePrincipalResidueCenter (d : RingOfIntegers K)
    (c : HasQuotient.Quotient (RingOfIntegers K) (Ideal.span ({d} : Set (RingOfIntegers K)))) :
    HeckeFiniteAdeles K :=
  algebraMap K (HeckeFiniteAdeles K)
    (algebraMap (RingOfIntegers K) K (heckePrincipalResidueRepresentative d c))

/-- A translate of the scaled integral finite adeles. -/
def heckeFiniteAdelePrincipalCoset (a : HeckeFiniteAdeles K) (d : K) :
    Set (HeckeFiniteAdeles K) :=
  Set.image (fun z => a + z) (heckeScaledIntegralFiniteAdeles d : Set (HeckeFiniteAdeles K))

/-- The coset of a residue class modulo a principal integral ideal. -/
noncomputable def heckePrincipalResidueCoset (d : RingOfIntegers K)
    (c : HasQuotient.Quotient (RingOfIntegers K) (Ideal.span ({d} : Set (RingOfIntegers K)))) :
    Set (HeckeFiniteAdeles K) :=
  heckeFiniteAdelePrincipalCoset (heckePrincipalResidueCenter d c)
    (algebraMap (RingOfIntegers K) K d)

private noncomputable def idealResidueCenter (I : Ideal (RingOfIntegers K))
    (i : HasQuotient.Quotient (RingOfIntegers K) I) : HeckeFiniteAdeles K :=
  algebraMap K (HeckeFiniteAdeles K) (algebraMap (RingOfIntegers K) K
    (Classical.choose (Ideal.Quotient.mk_surjective i)))

private noncomputable def idealResidueCoset
    (I : Ideal (RingOfIntegers K)) (D : AddSubgroup (HeckeFiniteAdeles K))
    (i : HasQuotient.Quotient (RingOfIntegers K) I) : Set (HeckeFiniteAdeles K) :=
  Set.image (fun z => idealResidueCenter I i + z) (D : Set (HeckeFiniteAdeles K))

omit [MeasurableSpace (HeckeFiniteAdeles K)] [BorelSpace (HeckeFiniteAdeles K)] in
private theorem idealResidueCosets_partition
    (I : Ideal (RingOfIntegers K)) (D : AddSubgroup (HeckeFiniteAdeles K))
    (hD : D <= heckeIntegralFiniteAdeles)
    (hCoeff : forall b : RingOfIntegers K,
      Membership.mem D (algebraMap K (HeckeFiniteAdeles K) (algebraMap (RingOfIntegers K) K b)) <->
        Membership.mem I b)
    (hApprox : forall a : HeckeFiniteAdeles K, Membership.mem heckeIntegralFiniteAdeles a ->
      exists b : RingOfIntegers K,
        Membership.mem D (a - algebraMap K (HeckeFiniteAdeles K) (algebraMap (RingOfIntegers K) K b))) :
    And (Pairwise (fun i j => Disjoint (idealResidueCoset I D i) (idealResidueCoset I D j)))
      (Set.iUnion (idealResidueCoset I D) =
        (heckeIntegralFiniteAdeles (K := K) : Set (HeckeFiniteAdeles K))) := by
  let R := RingOfIntegers K
  let e := algebraMap R K
  let g := algebraMap K (HeckeFiniteAdeles K)
  let H : AddSubgroup (HeckeFiniteAdeles K) := heckeIntegralFiniteAdeles
  let Q := HasQuotient.Quotient R I
  let repr (c : Q) := Classical.choose (Ideal.Quotient.mk_surjective c)
  have hRepr (c : Q) : Ideal.Quotient.mk I (repr c) = c :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective c)
  let rho (c : Q) := idealResidueCenter I c
  let C (c : Q) := idealResidueCoset I D c
  have hG (b : R) : Membership.mem H (g (e b)) :=
    fun p => HeightOneSpectrum.coe_algebraMap_mem R K p b
  constructor
  . intro i j hne
    apply Set.disjoint_left.mpr
    intro a ha hb
    choose x hx using ha
    choose y hy using hb
    have hEq : rho i + x = rho j + y := hx.2.trans hy.2.symm
    have hDiff : rho i - rho j = y - x := by
      calc
        rho i - rho j = (rho i + x) - (rho j + x) := by abel
        _ = y - x := by rw [hEq]; abel
    have hIn : Membership.mem D (g (e (repr i - repr j))) := by
      rw [map_sub e, map_sub g]
      change Membership.mem D (rho i - rho j)
      rw [hDiff]
      exact D.sub_mem hy.1 hx.1
    apply hne
    have hRel := (Ideal.Quotient.eq (I := I)).mpr ((hCoeff _).mp hIn)
    rw [hRepr, hRepr] at hRel
    exact hRel
  . ext a
    constructor
    . intro ha
      choose i hi using Set.mem_iUnion.mp ha
      choose x hx using hi
      rw [<- hx.2]
      exact H.add_mem (hG (repr i)) (hD hx.1)
    . intro ha
      choose b hb using hApprox a ha
      let i := Ideal.Quotient.mk I b
      have hbI : Membership.mem I (b - repr i) :=
        (Ideal.Quotient.eq (I := I)).mp (hRepr i).symm
      have hShift := (hCoeff (b - repr i)).mpr hbI
      rw [map_sub e, map_sub g] at hShift
      change Membership.mem D (g (e b) - rho i) at hShift
      have hz : Membership.mem D (a - rho i) := by
        have hEq : a - rho i = (a - g (e b)) + (g (e b) - rho i) := by abel
        rw [hEq]
        exact D.add_mem hb hShift
      have hzEq : rho i + (a - rho i) = a :=
        (add_comm _ _).trans (sub_add_cancel _ _)
      exact Set.mem_iUnion.mpr (Exists.intro i (Exists.intro (a - rho i) (And.intro hz hzEq)))

set_option maxHeartbeats 700000 in
/-- A subgroup covered by integral principal residue classes has reciprocal ideal norm mass. -/
theorem heckeFiniteAdeleHaar_of_ideal_kernel
    (I : Ideal (RingOfIntegers K)) (hI : Not (I = 0))
    (D : AddSubgroup (HeckeFiniteAdeles K)) (hD : D <= heckeIntegralFiniteAdeles) (hOpen : IsOpen (D : Set (HeckeFiniteAdeles K)))
    (hCoeff : forall b : RingOfIntegers K,
      Membership.mem D (algebraMap K (HeckeFiniteAdeles K) (algebraMap (RingOfIntegers K) K b)) <->
        Membership.mem I b)
    (hApprox : forall a : HeckeFiniteAdeles K, Membership.mem heckeIntegralFiniteAdeles a ->
      exists b : RingOfIntegers K,
        Membership.mem D (a - algebraMap K (HeckeFiniteAdeles K) (algebraMap (RingOfIntegers K) K b))) :
    (Ideal.absNorm I : ENNReal) * heckeFiniteAdeleHaar (D : Set (HeckeFiniteAdeles K)) = 1 := by
  let Q := HasQuotient.Quotient (RingOfIntegers K) I
  let mu : Measure (HeckeFiniteAdeles K) := heckeFiniteAdeleHaar
  let : Measure.IsAddLeftInvariant mu := heckeFiniteAdeleHaar_isAddLeftInvariant
  let : I.toAddSubgroup.FiniteIndex := Ideal.finiteIndex hI
  let : Finite Q := inferInstanceAs (Finite (HasQuotient.Quotient (RingOfIntegers K) I.toAddSubgroup))
  let : Fintype Q := Fintype.ofFinite Q
  let rho (i : Q) := idealResidueCenter I i
  let C (i : Q) := idealResidueCoset I D i
  have hParts := idealResidueCosets_partition I D hD hCoeff hApprox
  have hMeas (i : Q) : MeasurableSet (C i) :=
    ((Homeomorph.addLeft (rho i)).isOpenMap _ hOpen).measurableSet
  have hVol (i : Q) : mu (C i) = mu (D : Set (HeckeFiniteAdeles K)) := by
    have hp := (measurePreserving_add_left mu (rho i)).measure_preimage (hMeas i).nullMeasurableSet
    have hPre : Set.preimage (fun z => rho i + z) (C i) = (D : Set (HeckeFiniteAdeles K)) :=
      Set.preimage_image_eq _ (fun _ _ h => add_left_cancel h)
    rw [hPre] at hp
    exact hp.symm
  have hNorm : Ideal.absNorm I = Nat.card Q := rfl
  change (Ideal.absNorm I : ENNReal) * mu (D : Set (HeckeFiniteAdeles K)) = 1
  calc
    _ = tsum (fun _ : Q => mu (D : Set (HeckeFiniteAdeles K))) := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNorm,
        Nat.card_eq_fintype_card]
    _ = tsum (fun i : Q => mu (C i)) := tsum_congr (fun i => (hVol i).symm)
    _ = mu (Set.iUnion C) := (measure_iUnion hParts.1 hMeas).symm
    _ = 1 := by rw [hParts.2]; exact heckeFiniteAdeleHaar_integral

private theorem heckePrincipalResidueConditions
    (d : RingOfIntegers K) (hd : Not (d = 0)) :
    let e := algebraMap (RingOfIntegers K) K
    let g := algebraMap K (HeckeFiniteAdeles K)
    let D := heckeScaledIntegralFiniteAdeles (e d)
    let I := Ideal.span ({d} : Set (RingOfIntegers K))
    And (forall b : RingOfIntegers K, Membership.mem D (g (e b)) <-> Membership.mem I b)
      (forall a : HeckeFiniteAdeles K, Membership.mem heckeIntegralFiniteAdeles a ->
        exists b : RingOfIntegers K, Membership.mem D (a - g (e b))) := by
  let R := RingOfIntegers K
  let A := HeckeFiniteAdeles K
  let e := algebraMap R K
  let g := algebraMap K A
  let dd := e d
  let H : AddSubgroup A := heckeIntegralFiniteAdeles
  let D := heckeScaledIntegralFiniteAdeles dd
  let I := Ideal.span ({d} : Set R)
  have hD : Not (dd = 0) := (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective R K)).mpr hd
  change And (forall b : R, Membership.mem D (g (e b)) <-> Membership.mem I b)
    (forall a : A, Membership.mem H a -> exists b : R, Membership.mem D (a - g (e b)))
  constructor
  . intro b
    rw [mem_heckeScaledIntegralFiniteAdeles_iff dd hD]
    change (forall p : HeightOneSpectrum R, Membership.mem (p.adicCompletionIntegers K)
      (algebraMap K (p.adicCompletion K) (e b) / algebraMap K (p.adicCompletion K) dd)) <-> _
    rw [principal_mem_finiteAdele_modulus_iff (e b) dd hD, Ideal.mem_span_singleton]
    apply exists_congr
    intro y
    rw [<- map_mul]
    exact (FaithfulSMul.algebraMap_injective R K).eq_iff
  . intro a ha
    choose x hx using exists_finiteAdele_sub_principal_modulus a dd hD
    have hIn : Membership.mem D (a - g x) :=
      (mem_heckeScaledIntegralFiniteAdeles_iff dd hD (a - g x)).mpr hx
    have hxH : Membership.mem H (g x) := by
      have hDle : D <= H := heckeScaledIntegralFiniteAdeles_le d
      have hSub : Membership.mem H (a - (a - g x)) := H.sub_mem ha (hDle hIn)
      rwa [sub_sub_cancel] at hSub
    have hxR : Exists (fun b : R => x = e b) := by
      have hLoc : forall p : HeightOneSpectrum R, Membership.mem (p.adicCompletionIntegers K)
          (algebraMap K (p.adicCompletion K) x / algebraMap K (p.adicCompletion K) 1) := by
        intro p
        rw [map_one, div_one]
        exact hxH p
      simpa only [one_mul] using
        (principal_mem_finiteAdele_modulus_iff x 1 one_ne_zero).mp hLoc
    choose b hb using hxR
    exact Exists.intro b (by rw [<- hb]; exact hIn)

/-- The residue-class cosets of a nonzero principal ideal partition the
integral finite adeles. -/
theorem heckePrincipalResidueCosets_partition
    (d : RingOfIntegers K) (hd : Not (d = 0)) :
    And (Pairwise (fun c j => Disjoint (heckePrincipalResidueCoset d c)
      (heckePrincipalResidueCoset d j)))
      (Set.iUnion (heckePrincipalResidueCoset d) =
        (heckeIntegralFiniteAdeles (K := K) : Set (HeckeFiniteAdeles K))) := by
  let I := Ideal.span ({d} : Set (RingOfIntegers K))
  let D := heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d)
  have h := heckePrincipalResidueConditions d hd
  exact idealResidueCosets_partition I D (heckeScaledIntegralFiniteAdeles_le d) h.1 h.2

/-- Scaling the compact open integral finite adeles by a principal
integer divides their Haar mass by the norm of its principal ideal. -/
theorem heckeFiniteAdeleHaar_scaledIntegral_mass
    (d : RingOfIntegers K) (hd : Not (d = 0)) :
    (Ideal.absNorm (Ideal.span ({d} : Set (RingOfIntegers K))) : ENNReal) *
      heckeFiniteAdeleHaar (heckeScaledIntegralFiniteAdeles
        (algebraMap (RingOfIntegers K) K d) : Set (HeckeFiniteAdeles K)) = 1 := by
  let R := RingOfIntegers K
  let e := algebraMap R K
  let I := Ideal.span ({d} : Set R)
  let D := heckeScaledIntegralFiniteAdeles (e d)
  have hI : Not (I = 0) := fun h => hd (Ideal.span_singleton_eq_bot.mp h)
  have hD : Not (e d = 0) := (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective R K)).mpr hd
  have h := heckePrincipalResidueConditions d hd
  exact heckeFiniteAdeleHaar_of_ideal_kernel I hI D (heckeScaledIntegralFiniteAdeles_le d)
    (isOpen_heckeScaledIntegralFiniteAdeles (e d) hD) h.1 h.2

omit [MeasurableSpace (HeckeFiniteAdeles K)] [BorelSpace (HeckeFiniteAdeles K)] in
private theorem principalFiniteChar_scaledIntegral_iff
    (d : RingOfIntegers K) (hd : Not (d = 0)) (t : K) :
    let D := heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d)
    (forall z, Membership.mem D z -> heckeFiniteAdelePrincipalChar t z = 1) <->
      Membership.mem
        (DedekindZeta.Theta.dualIdeal K (Ideal.span ({d} : Set (RingOfIntegers K))) :
          Submodule (RingOfIntegers K) K) t := by
  let e := algebraMap (RingOfIntegers K) K
  let g := algebraMap K (HeckeFiniteAdeles K)
  let D := heckeScaledIntegralFiniteAdeles (e d)
  let H : AddSubgroup (HeckeFiniteAdeles K) := heckeIntegralFiniteAdeles
  have hComp (z : HeckeFiniteAdeles K) :
      heckeFiniteAdelePrincipalChar t (z * g (e d)) =
        heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K) (z * g (e d * t))) := by
    change heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K) ((z * g (e d)) * g t)) = _
    rw [mul_assoc, <- map_mul]
  change (forall z, Membership.mem D z -> heckeFiniteAdelePrincipalChar t z = 1) <-> _
  rw [<- heckeAdeleAddChar_finitePrincipalIdeal_annihilator_iff d hd t]
  constructor
  case mp =>
    intro h z hz
    rw [<- hComp]
    exact h (z * g (e d)) (AddSubgroup.mem_map.mpr (Exists.intro z (And.intro hz rfl)))
  case mpr =>
    intro h z hz
    choose b hb using AddSubgroup.mem_map.mp hz
    have heq : b * g (e d) = z := hb.2
    rw [<- heq, hComp]
    exact h b hb.1

private theorem scaledIntegral_real_mass
    (d : RingOfIntegers K) (hd : Not (d = 0)) :
    (heckeFiniteAdeleHaar (heckeScaledIntegralFiniteAdeles
        (algebraMap (RingOfIntegers K) K d) : Set (HeckeFiniteAdeles K))).toReal =
      Inv.inv (Ideal.absNorm (Ideal.span ({d} : Set (RingOfIntegers K))) : Real) := by
  let I := Ideal.span ({d} : Set (RingOfIntegers K))
  let m := heckeFiniteAdeleHaar (heckeScaledIntegralFiniteAdeles
    (algebraMap (RingOfIntegers K) K d) : Set (HeckeFiniteAdeles K))
  have h := congrArg ENNReal.toReal (heckeFiniteAdeleHaar_scaledIntegral_mass d hd)
  change ((Ideal.absNorm I : ENNReal) * m).toReal = (1 : ENNReal).toReal at h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at h
  have hn : Not ((Ideal.absNorm I : Real) = 0) := by
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  change m.toReal = _
  rw [<- one_div]
  exact (eq_div_iff hn).mpr ((mul_comm _ _).trans h)

/-- The finite Fourier integral over a principal coset equals its phase times
the inverse ideal norm on the trace-dual ideal and vanishes off that ideal. -/
theorem integral_heckeFiniteAdeleHaar_principalCoset
    (a : HeckeFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0)) (t : K) :
    let I := Ideal.span ({d} : Set (RingOfIntegers K))
    let D := heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d)
    integral (heckeFiniteAdeleHaar.restrict (Set.image (fun z : HeckeFiniteAdeles K => a + z) (D : Set (HeckeFiniteAdeles K))))
      (fun z => (heckeFiniteAdelePrincipalChar t z : Complex)) =
      if Membership.mem (DedekindZeta.Theta.dualIdeal K I : Submodule (RingOfIntegers K) K) t
      then (heckeFiniteAdelePrincipalChar t a : Complex) * Inv.inv (Ideal.absNorm I : Complex) else 0 := by
  let R := RingOfIntegers K
  let e := algebraMap R K
  let D := heckeScaledIntegralFiniteAdeles (e d)
  let mu : Measure (HeckeFiniteAdeles K) := heckeFiniteAdeleHaar
  let psi (z : HeckeFiniteAdeles K) : Complex := heckeFiniteAdelePrincipalChar t z
  let : Measure.IsAddLeftInvariant mu := heckeFiniteAdeleHaar_isAddLeftInvariant
  have hMP : MeasurePreserving (fun z : HeckeFiniteAdeles K => a + z) mu mu :=
    measurePreserving_add_left mu a
  have hI := hMP.setIntegral_image_emb (Homeomorph.addLeft a).measurableEmbedding psi (D : Set (HeckeFiniteAdeles K))
  have hTranslate : (fun z : HeckeFiniteAdeles K => psi (a + z)) = fun z => psi a * psi z := by
    funext z
    simp only [psi, AddChar.map_add_eq_mul, Circle.coe_mul]
  rw [hTranslate, integral_const_mul] at hI
  have hd' : Not (e d = 0) := (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective R K)).mpr hd
  dsimp only
  rw [show integral (mu.restrict (Set.image (fun z : HeckeFiniteAdeles K => a + z) (D : Set (HeckeFiniteAdeles K)))) psi =
      psi a * integral (mu.restrict (D : Set (HeckeFiniteAdeles K))) psi from hI]
  let I := Ideal.span ({d} : Set R)
  have hAnn : (forall z, Membership.mem D z -> heckeFiniteAdelePrincipalChar t z = 1) <->
      Membership.mem (DedekindZeta.Theta.dualIdeal K I : Submodule R K) t :=
    principalFiniteChar_scaledIntegral_iff d hd t
  rw [integral_addChar_subgroup D (isOpen_heckeScaledIntegralFiniteAdeles (e d) hd').measurableSet (heckeFiniteAdelePrincipalChar t)]
  by_cases hT : Membership.mem (DedekindZeta.Theta.dualIdeal K I : Submodule R K) t
  case pos =>
    rw [if_pos hT, if_pos (hAnn.mpr hT), scaledIntegral_real_mass d hd,
      Complex.ofReal_inv, Complex.ofReal_natCast]
  case neg =>
    rw [if_neg hT, if_neg (fun h => hT (hAnn.mp h)), mul_zero]

end Robin1984.GRH
