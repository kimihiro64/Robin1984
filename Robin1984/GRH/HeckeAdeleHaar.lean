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

end Robin1984.GRH
