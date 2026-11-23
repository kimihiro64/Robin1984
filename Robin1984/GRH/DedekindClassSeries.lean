import DedekindZeta.PerClass

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The decomposition of the Dedekind Dirichlet series by ideal classes.
- Formalization note: The half-plane class formula for an arbitrary integral representative.
- PROVENANCE-END
-/

/-!
# The half-plane class formula for an arbitrary integral representative

The principal-ideal reindexing in the Formal Frontier per-class
calculation works for any nonzero integral ideal. It is independent of
the choice of section of the class-group map.
-/

open NumberField

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

local notation "R" => RingOfIntegers K
local notation "F" => FractionalIdeal (nonZeroDivisors R) K
local notation "NZI" => (nonZeroDivisors (Ideal R))

private abbrev inverseClassIdeals (c : ClassGroup R) :=
  {b : NonzeroIdeal K // idealClass K b = Inv.inv c}

private abbrev principalMultiples (a : Ideal R) :=
  {I : NZI // And (Dvd.dvd a I.val) (Submodule.IsPrincipal I.val)}

private def monoidIdeal (b : NonzeroIdeal K) : NZI :=
  Subtype.mk b.val (mem_nonZeroDivisors_iff_ne_zero.mpr b.property)

private theorem ideal_mul_left_injective (a : Ideal R) (ha : Not (a = 0)) :
    Function.Injective (fun b : Ideal R => a * b) := by
  intro b c h
  have hA : Not ((a : F) = 0) := (FractionalIdeal.coeIdeal_ne_zero'
    (P := K) (S := nonZeroDivisors R) le_rfl).mpr (by simpa only [Ideal.zero_eq_bot] using ha)
  have hCancel : Inv.inv (a : F) * (a : F) = 1 := by
    rw [mul_comm, <- div_eq_mul_inv, div_self hA]
  have hF := congrArg (fun I : Ideal R => (I : F)) h
  change ((a * b : Ideal R) : F) = ((a * c : Ideal R) : F) at hF
  simp only [FractionalIdeal.coeIdeal_mul] at hF
  apply FractionalIdeal.coeIdeal_injective' (S := nonZeroDivisors R) (P := K) le_rfl
  have hMul := congrArg (fun I : F => Inv.inv (a : F) * I) hF
  simpa only [<- mul_assoc, hCancel, one_mul] using hMul

private noncomputable def idealClassPrincipalMultipleEquiv (A : NZI) :
    Equiv (inverseClassIdeals K (ClassGroup.mk0 A)) (principalMultiples K A.val) := by
  let f : inverseClassIdeals K (ClassGroup.mk0 A) -> principalMultiples K A.val := fun b => by
    let I := A * monoidIdeal K b.val
    have hClass : ClassGroup.mk0 I = 1 := by
      unfold I
      rw [map_mul]
      change ClassGroup.mk0 A * idealClass K b.val = 1
      rw [b.property, mul_inv_cancel]
    exact Subtype.mk I (And.intro (dvd_mul_right _ _)
      ((ClassGroup.mk0_eq_one_iff I.property).mp hClass))
  refine Equiv.ofBijective f (And.intro ?hInj ?hSurj)
  case hInj =>
    intro b c h
    have hMul := congrArg (fun I : principalMultiples K A.val => I.val.val) h
    change A.val * b.val.val = A.val * c.val.val at hMul
    apply Subtype.ext
    apply Subtype.ext
    exact ideal_mul_left_injective K A.val
      (mem_nonZeroDivisors_iff_ne_zero.mp A.property) hMul
  case hSurj =>
    intro J
    choose b hb using J.property.1
    have hb0 : Not (b = 0) := by
      intro h
      rw [h, mul_zero] at hb
      exact (mem_nonZeroDivisors_iff_ne_zero.mp J.val.property) hb
    let B : NonzeroIdeal K := Subtype.mk b hb0
    have hJ : J.val = A * monoidIdeal K B := Subtype.ext hb
    have hOne : ClassGroup.mk0 J.val = 1 :=
      (ClassGroup.mk0_eq_one_iff J.val.property).mpr J.property.2
    rw [hJ, map_mul] at hOne
    have hB : idealClass K B = Inv.inv (ClassGroup.mk0 A) := by
      rw [eq_inv_iff_mul_eq_one, mul_comm]
      exact hOne
    exact Exists.intro (Subtype.mk B hB) (Subtype.ext hJ.symm)

/-- On `1 < s.re` the completed partial zeta of an arbitrary nonzero
ideal is the class series attached to its inverse class. -/
theorem completedPartialZeta_integralIdeal_eq (A : NZI) {s : Complex} (hs : 1 < s.re) :
    completedPartialZeta K A.val s =
      ZInfty K s * tsum (fun b : inverseClassIdeals K (ClassGroup.mk0 A) =>
        (Ideal.absNorm b.val.val : Complex) ^ (-s)) := by
  have ha : Not (A.val = 0) := mem_nonZeroDivisors_iff_ne_zero.mp A.property
  rw [GammaIntegral.completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum s hs ha]
  let e := idealClassPrincipalMultipleEquiv K A
  let u (I : principalMultiples K A.val) : Complex := (Ideal.absNorm I.val.val : Complex) ^ (-s)
  let v (b : inverseClassIdeals K (ClassGroup.mk0 A)) : Complex :=
    (Ideal.absNorm b.val.val : Complex) ^ (-s)
  let aNorm : Complex := Ideal.absNorm A.val
  change aNorm ^ s * ZInfty K s * tsum u = ZInfty K s * tsum v
  have hNorm : (tsum u) = aNorm ^ (-s) * tsum v := by
    calc
      _ = tsum (fun b : inverseClassIdeals K (ClassGroup.mk0 A) => u (e b)) :=
        (e.tsum_eq u).symm
      _ = tsum (fun b => aNorm ^ (-s) * v b) := by
        apply tsum_congr
        intro b
        change (Ideal.absNorm (A.val * b.val.val) : Complex) ^ (-s) = _
        rw [map_mul Ideal.absNorm, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      _ = _ := tsum_mul_left
  have hAne : Not (aNorm = 0) := Nat.cast_ne_zero.mpr (fun h =>
    ha (by simpa only [Ideal.zero_eq_bot] using Ideal.absNorm_eq_zero_iff.mp h))
  have hCancel : aNorm ^ s * aNorm ^ (-s) = 1 := by
    rw [<- Complex.cpow_add _ _ hAne, add_neg_cancel, Complex.cpow_zero]
  rw [hNorm]
  calc
    aNorm ^ s * ZInfty K s * (aNorm ^ (-s) * tsum v) =
      (aNorm ^ s * aNorm ^ (-s)) * (ZInfty K s * tsum v) := by ring
    _ = _ := by rw [hCancel, one_mul]

end DedekindZeta
