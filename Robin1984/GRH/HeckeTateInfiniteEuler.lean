import DedekindZeta.GammaIntegral
import Robin1984.GRH.HeckeAdelicFourier
import Robin1984.GRH.SchwartzGaussian

/-!
# The archimedean Tate integral

The character-weighted polynomial Gaussian is absolutely integrable under
the normalized multiplicative measure. Its integral is the product of the
shifted real and complex Gamma factors.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's archimedean zeta integrals for real and complex local characters.
- Formalization note: Evaluates the character-weighted polynomial Gaussian under the normalized multiplicative Haar measure.
- PROVENANCE-END
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField NumberField.InfinitePlace IsDedekindDomain Complex MeasureTheory
open scoped Classical

private def realTatePolynomial (n : Nat) (x : Real) : Complex :=
  (x : Complex) ^ n

private def complexTatePolynomial (m : Int) (z : Complex) : Complex :=
  if 0 <= m then (starRingEnd Complex z) ^ m.toNat else z ^ m.natAbs

private theorem realTatePolynomial_mul_parity (n : Nat) (a : Units Real) :
    realTatePolynomial n a.val * (if 0 < a.val then 1 else (-1 : Complex) ^ n) =
      ((abs a.val : Real) : Complex) ^ n := by
  by_cases h : 0 < a.val
  case pos => rw [if_pos h, mul_one, abs_of_pos h, realTatePolynomial]
  case neg =>
    rw [if_neg h, abs_of_nonpos (le_of_not_gt h), Complex.ofReal_neg, realTatePolynomial, <- mul_pow]
    congr 1
    ring

private theorem complexTatePolynomial_mul_phase (m : Int) (a : Units Complex) :
    complexTatePolynomial m a.val * ((complexUnitPhase a ^ m : Circle) : Complex) =
      (norm a.val : Complex) ^ m.natAbs := by
  let z := a.val
  let r : Complex := (norm z : Complex)
  let u := complexUnitPhase a
  have hr : Not (r = 0) :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr a.ne_zero)
  have hz : Not (z = 0) := a.ne_zero
  have hU : (u : Complex) = z / r := rfl
  have hPos : starRingEnd Complex z * (u : Complex) = r := by
    rw [hU, <- mul_div_assoc, mul_comm (starRingEnd Complex z) z, Complex.mul_conj,
      <- Complex.sq_norm, Complex.ofReal_pow]
    change r ^ 2 / r = r
    field_simp [hr]
  have hNeg : z * Inv.inv (u : Complex) = r := by
    rw [hU, inv_div]
    field_simp [hz]
  cases m with
  | ofNat n =>
    have hn : 0 <= (Int.ofNat n) := Int.natCast_nonneg n
    rw [complexTatePolynomial, if_pos hn, Circle.coe_zpow]
    change (starRingEnd Complex z) ^ n * ((u : Complex) ^ (n : Int)) = r ^ n
    rw [zpow_natCast, <- mul_pow, hPos]
  | negSucc n =>
    have hn : Not (0 <= Int.negSucc n) := (Int.negSucc_lt_zero n).not_ge
    rw [complexTatePolynomial, if_neg hn, Circle.coe_zpow]
    change z ^ (n + 1) * ((u : Complex) ^ Int.negSucc n) = r ^ (n + 1)
    rw [zpow_negSucc, <- inv_pow, <- mul_pow, hNeg]

private theorem radialPower_add_frequency (r : Real) (hr : 0 < r)
    (s : Complex) (n : Nat) (tau : Real) :
    (r : Complex) ^ n * (r : Complex) ^ s *
      Complex.exp (((tau * Real.log r : Real) : Complex) * Complex.I) =
      (r : Complex) ^ (s + (n : Complex) + (tau : Complex) * Complex.I) := by
  have hr0 : Not ((r : Complex) = 0) := Complex.ofReal_ne_zero.mpr hr.ne'
  have hFreq :
      Complex.exp (((tau * Real.log r : Real) : Complex) * Complex.I) =
        (r : Complex) ^ ((tau : Complex) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hr0, <- Complex.ofReal_log hr.le, Complex.ofReal_mul]
    congr 1
    ring
  rw [hFreq, <- Complex.cpow_natCast, <- Complex.cpow_add _ _ hr0, <- Complex.cpow_add _ _ hr0,
    add_comm (n : Complex) s]

variable {K : Type*} [Field K] [NumberField K]

/-- The real polynomial cancels the local parity. The remaining radial
frequency translates the Mellin exponent by the real Gamma shift. -/
private theorem realTatePolynomial_mul_character_cpow
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsReal)
    (s : Complex) (a : Units Real) :
    realTatePolynomial (realInfiniteHeckeParameters chi hv).1 a.val *
      (realInfiniteHeckeCharacter chi hv a : Complex) *
      ((abs a.val : Real) : Complex) ^ s =
      ((abs a.val : Real) : Complex) ^ (s + realInfiniteHeckeShift chi hv) := by
  let params := realInfiniteHeckeParameters chi hv
  have hChi := (realInfiniteHeckeParameters_spec chi hv).2 a
  rw [hChi, <- mul_assoc, realTatePolynomial_mul_parity,
    mul_right_comm, radialPower_add_frequency (abs a.val) (abs_pos.mpr a.ne_zero)]
  unfold realInfiniteHeckeShift
  congr 1
  ring

/-- The complex polynomial cancels the angular character. The remaining radial
powers are the exponent in the shifted complex Gamma factor. -/
private theorem complexTatePolynomial_mul_character_cpow
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsComplex)
    (s : Complex) (a : Units Complex) :
    complexTatePolynomial (complexInfiniteHeckeParameters chi hv).1 a.val *
      (complexInfiniteHeckeCharacter chi hv a : Complex) *
      (norm a.val : Complex) ^ (2 * s) =
      (norm a.val : Complex) ^ (2 * (s + complexInfiniteHeckeShift chi hv)) := by
  have hChi := complexInfiniteHeckeParameters_spec chi hv a
  rw [hChi, <- mul_assoc, complexTatePolynomial_mul_phase,
    mul_right_comm, radialPower_add_frequency (norm a.val) (norm_pos_iff.mpr a.ne_zero)]
  unfold complexInfiniteHeckeShift
  push_cast
  congr 1
  ring

/-- The real weighted polynomial Gaussian in additive measure coordinates. -/
private def realTateArchimedeanDensity
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsReal)
    (s : Complex) (x : Real) : Complex :=
  HSMul.hSMul (Inv.inv (abs x) : Real)
    ((Real.exp (-Real.pi * x ^ 2) : Complex) *
      if hx : Not (x = 0) then
        realTatePolynomial (realInfiniteHeckeParameters chi hv).1 x *
          (realInfiniteHeckeCharacter chi hv (Units.mk0 x hx) : Complex) *
          ((abs x : Real) : Complex) ^ s
      else 0)

/-- The complex weighted polynomial Gaussian in additive measure coordinates. -/
private def complexTateArchimedeanDensity
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsComplex)
    (s : Complex) (z : Complex) : Complex :=
  HSMul.hSMul (2 / Real.pi * Inv.inv (norm z ^ 2) : Real)
    ((Real.exp (-2 * Real.pi * norm z ^ 2) : Complex) *
      if hz : Not (z = 0) then
        complexTatePolynomial (complexInfiniteHeckeParameters chi hv).1 z *
          (complexInfiniteHeckeCharacter chi hv (Units.mk0 z hz) : Complex) *
          (norm z : Complex) ^ (2 * s)
      else 0)

private theorem realTateArchimedeanDensity_eq_realFactor
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsReal)
    (s : Complex) (x : Real) :
    realTateArchimedeanDensity chi hv s x =
      DedekindZeta.GammaIntegral.realFactor (s + realInfiniteHeckeShift chi hv) x := by
  unfold realTateArchimedeanDensity DedekindZeta.GammaIntegral.realFactor
  by_cases hx : x = 0
  case pos => simp [hx]
  case neg =>
    rw [dif_pos hx]
    exact congrArg (fun c : Complex => HSMul.hSMul (Inv.inv (abs x) : Real)
      ((Real.exp (-Real.pi * x ^ 2) : Complex) * c))
      (realTatePolynomial_mul_character_cpow chi hv s (Units.mk0 x hx))

private theorem complexTateArchimedeanDensity_eq_complexFactor
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsComplex)
    (s : Complex) (z : Complex) :
    complexTateArchimedeanDensity chi hv s z =
      DedekindZeta.GammaIntegral.complexFactor (s + complexInfiniteHeckeShift chi hv) z := by
  unfold complexTateArchimedeanDensity DedekindZeta.GammaIntegral.complexFactor
  by_cases hz : z = 0
  case pos => simp [hz]
  case neg =>
    rw [dif_pos hz]
    exact congrArg (fun c : Complex => HSMul.hSMul (2 / Real.pi * Inv.inv (norm z ^ 2) : Real)
      ((Real.exp (-2 * Real.pi * norm z ^ 2) : Complex) * c))
      (complexTatePolynomial_mul_character_cpow chi hv s (Units.mk0 z hz))

/-- The actual real Tate test integrates to the shifted standard real factor. -/
private theorem integral_realTateArchimedeanDensity
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsReal)
    {s : Complex} (hs : 0 < s.re) :
    integral volume (realTateArchimedeanDensity chi hv s) =
      DedekindZeta.LReal (s + realInfiniteHeckeShift chi hv) := by
  rw [funext (realTateArchimedeanDensity_eq_realFactor chi hv s),
    <- DedekindZeta.GammaIntegral.gammaReal_eq_integral]
  apply DedekindZeta.GammaIntegral.gammaReal_eq
  rw [Complex.add_re]
  exact add_pos_of_pos_of_nonneg hs (realInfiniteHeckeShift_re_nonneg chi hv)

/-- The actual complex Tate test integrates to the shifted standard complex factor. -/
private theorem integral_complexTateArchimedeanDensity
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsComplex)
    {s : Complex} (hs : 0 < s.re) :
    integral volume (complexTateArchimedeanDensity chi hv s) =
      DedekindZeta.LComplex (s + complexInfiniteHeckeShift chi hv) := by
  rw [funext (complexTateArchimedeanDensity_eq_complexFactor chi hv s),
    <- DedekindZeta.GammaIntegral.gammaComplex_eq_integral]
  apply DedekindZeta.GammaIntegral.gammaComplex_eq
  rw [Complex.add_re]
  exact add_pos_of_pos_of_nonneg hs (complexInfiniteHeckeShift_re_nonneg chi hv)


/-- The inclusion of infinite ideles as ideles with finite component one. -/
def heckeInfiniteIdeleInclusion (K : Type*) [Field K] [NumberField K] :
    MonoidHom (Units (InfiniteAdeleRing K)) (Units (AdeleRing (RingOfIntegers K) K)) :=
  Units.map ((MonoidHom.id (InfiniteAdeleRing K)).prod
    (1 : MonoidHom (InfiniteAdeleRing K) (FiniteAdeleRing (RingOfIntegers K) K)))

/-- The unit in the completion at one place of an infinite idele. -/
def heckeInfiniteIdeleAt (v : InfinitePlace K) (a : Units (InfiniteAdeleRing K)) :
    Units v.Completion :=
  Units.map (Pi.evalMonoidHom (fun w : InfinitePlace K => w.Completion) v) a

/-- On an infinite idele, the global character is the product of its
local archimedean characters. -/
private theorem heckeCharacter_on_infiniteIdele_eq_prod
    (chi : UnitaryHeckeCharacter K) (a : Units (InfiniteAdeleRing K)) :
    chi.val (heckeInfiniteIdeleInclusion K a) =
      Finset.univ.prod (fun v : InfinitePlace K =>
        infiniteLocalHeckeCharacter chi v (heckeInfiniteIdeleAt v a)) := by
  classical
  let E := InfiniteAdeleRing K
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let A := Prod E F
  let embedded (v : InfinitePlace K) : Units A :=
    Units.map ((MonoidHom.mulSingle (fun w : InfinitePlace K => w.Completion) v).prod
      (1 : MonoidHom v.Completion F)) (heckeInfiniteIdeleAt v a)
  have hProd : Finset.univ.prod embedded = heckeInfiniteIdeleInclusion K a := by
    apply Units.ext
    change (Units.coeHom A) (Finset.univ.prod embedded) = _
    rw [map_prod (Units.coeHom A) embedded Finset.univ]
    apply Prod.ext
    . change (MonoidHom.fst E F) (Finset.univ.prod (fun v => (embedded v).val)) = a.val
      rw [map_prod (MonoidHom.fst E F) (fun v => (embedded v).val) Finset.univ]
      change Finset.univ.prod (fun v : InfinitePlace K => Pi.mulSingle v (a.val v)) = a.val
      exact Finset.univ_prod_mulSingle a.val
    . change (MonoidHom.snd E F) (Finset.univ.prod (fun v => (embedded v).val)) = 1
      rw [map_prod (MonoidHom.snd E F) (fun v => (embedded v).val) Finset.univ]
      exact Finset.prod_eq_one (fun v _ => rfl)
  let embeddedA (v : InfinitePlace K) : Units (AdeleRing (RingOfIntegers K) K) := embedded v
  have hProdA : Finset.univ.prod embeddedA = heckeInfiniteIdeleInclusion K a := hProd
  rw [<- hProdA, map_prod chi.val embeddedA Finset.univ]
  apply Finset.prod_congr rfl
  intro v _
  rfl

/-- The product of the weighted local Gaussian densities on the mixed space,
with the multiplicative Haar densities included in the local factors. -/
private def heckeTateInfiniteVolumeDensity (chi : UnitaryHeckeCharacter K)
    (s : Complex) (x : mixedEmbedding.mixedSpace K) : Complex :=
  (Finset.univ.prod (fun (v : {w : InfinitePlace K // w.IsReal}) =>
    realTateArchimedeanDensity chi v.property s (x.1 v))) *
  (Finset.univ.prod (fun (v : {w : InfinitePlace K // w.IsComplex}) =>
    complexTateArchimedeanDensity chi v.property s (x.2 v)))

/-- Integrating the real and complex densities on the mixed space gives
the product of the shifted standard Gamma factors. -/
private theorem integral_heckeTateInfiniteVolumeDensity
    (chi : UnitaryHeckeCharacter K) {s : Complex} (hs : 0 < s.re) :
    integral volume (heckeTateInfiniteVolumeDensity chi s) =
      (Finset.univ.prod (fun (v : {w : InfinitePlace K // w.IsReal}) =>
        DedekindZeta.LReal (s + realInfiniteHeckeShift chi v.property))) *
      (Finset.univ.prod (fun (v : {w : InfinitePlace K // w.IsComplex}) =>
        DedekindZeta.LComplex (s + complexInfiniteHeckeShift chi v.property))) := by
  classical
  let R := {w : InfinitePlace K // w.IsReal}
  let C := {w : InfinitePlace K // w.IsComplex}
  let f (v : R) := realTateArchimedeanDensity chi v.property s
  let g (v : C) := complexTateArchimedeanDensity chi v.property s
  let F (x : R -> Real) := Finset.univ.prod (fun v => f v (x v))
  let G (x : C -> Complex) := Finset.univ.prod (fun v => g v (x v))
  change integral volume (fun x : Prod (R -> Real) (C -> Complex) => F x.1 * G x.2) = _
  rw [Measure.volume_eq_prod, integral_prod_mul F G]
  change (integral volume (fun x : R -> Real => Finset.univ.prod (fun v => f v (x v)))) *
    (integral volume (fun x : C -> Complex => Finset.univ.prod (fun v => g v (x v)))) = _
  rw [integral_fintype_prod_volume_eq_prod f, integral_fintype_prod_volume_eq_prod g]
  simp only [f, g, integral_realTateArchimedeanDensity _ _ hs,
    integral_complexTateArchimedeanDensity _ _ hs]
  rfl


private def realTatePlaceTest {v : InfinitePlace K} (chi : UnitaryHeckeCharacter K)
    (hv : v.IsReal) (x : Real) : Complex :=
  realTatePolynomial (realInfiniteHeckeParameters chi hv).1 x *
    (Real.exp (-Real.pi * x ^ 2) : Complex)

private def complexTatePlaceTest {v : InfinitePlace K} (chi : UnitaryHeckeCharacter K)
    (hv : v.IsComplex) (z : Complex) : Complex :=
  complexTatePolynomial (complexInfiniteHeckeParameters chi hv).1 z *
    (Real.exp (-2 * Real.pi * norm z ^ 2) : Complex)

/-- The polynomial Gaussian fixed by the real parity and the complex
angular weights, before multiplying by the character or the norm power. -/
def heckeTateInfiniteTest (chi : UnitaryHeckeCharacter K)
    (x : mixedEmbedding.mixedSpace K) : Complex :=
  (Finset.univ.prod (fun v : {v : InfinitePlace K // v.IsReal} =>
    realTatePlaceTest chi v.property (x.1 v))) *
  (Finset.univ.prod (fun v : {v : InfinitePlace K // v.IsComplex} =>
    complexTatePlaceTest chi v.property (x.2 v)))

private theorem cast_finset_prod_cpow {T : Type*} (S : Finset T) (r : T -> Real)
    (h : forall v, 0 <= r v) (s : Complex) :
    ((S.prod r : Real) : Complex) ^ s = S.prod (fun v => (r v : Complex) ^ s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert v S hv ih =>
    rw [Finset.prod_insert hv, Finset.prod_insert hv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (h v) (Finset.prod_nonneg (fun w _ => h w)), ih]

set_option maxHeartbeats 1000000 in
/-- On an archimedean idele, the product volume density is the same as the
global Tate test weighted by the character and the idelic norm. -/
private theorem heckeTateInfiniteVolumeDensity_on_idele
    (chi : UnitaryHeckeCharacter K) (s : Complex) (a : Units (InfiniteAdeleRing K)) :
    let x := InfiniteAdeleRing.ringEquiv_mixedSpace K a.val
    heckeTateInfiniteVolumeDensity chi s x =
      (((2 / Real.pi) ^ nrComplexPlaces K * Inv.inv (mixedEmbedding.norm x) : Real) : Complex) *
        (heckeTateInfiniteTest chi x *
          (chi.val (heckeInfiniteIdeleInclusion K a) : Complex) *
          (mixedEmbedding.norm x : Complex) ^ s) := by
  classical
  let R := {v : InfinitePlace K // v.IsReal}
  let C := {v : InfinitePlace K // v.IsComplex}
  let x := InfiniteAdeleRing.ringEquiv_mixedSpace K a.val
  let er (v : R) := InfinitePlace.Completion.ringEquivRealOfIsReal v.property
  let ec (v : C) := InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property
  let U (v : R) := Units.map (er v).toMonoidHom (heckeInfiniteIdeleAt v.val a)
  let V (v : C) := Units.map (ec v).toMonoidHom (heckeInfiniteIdeleAt v.val a)
  let r (v : R) : Real := abs (x.1 v)
  let c (v : C) : Real := norm (x.2 v)
  let mu (v : R) : Real := Inv.inv (r v)
  let nu (v : C) : Real := 2 / Real.pi * Inv.inv (c v ^ 2)
  let rc (v : R) : Complex := realInfiniteHeckeCharacter chi v.property (U v)
  let cc (v : C) : Complex := complexInfiniteHeckeCharacter chi v.property (V v)
  have hU (v : R) : (U v).val = x.1 v := rfl
  have hV (v : C) : (V v).val = x.2 v := rfl
  have hR (v : R) : realTateArchimedeanDensity chi v.property s (x.1 v) =
      (mu v : Complex) * realTatePlaceTest chi v.property (x.1 v) * rc v * ((r v : Real) : Complex) ^ s := by
    have hv : Not (x.1 v = 0) := by rw [<- hU v]; exact (U v).ne_zero
    unfold realTateArchimedeanDensity
    rw [dif_pos hv, show Units.mk0 (x.1 v) hv = U v from Units.ext (hU v).symm]
    rw [show HSMul.hSMul (Inv.inv (abs (x.1 v)) : Real) =
        fun z : Complex => ((mu v : Real) : Complex) * z from funext (fun _ => Complex.real_smul)]
    unfold realTatePlaceTest rc r
    ring
  have hC (v : C) : complexTateArchimedeanDensity chi v.property s (x.2 v) =
      (nu v : Complex) * complexTatePlaceTest chi v.property (x.2 v) * cc v * (c v : Complex) ^ (2 * s) := by
    have hv : Not (x.2 v = 0) := by rw [<- hV v]; exact (V v).ne_zero
    unfold complexTateArchimedeanDensity
    rw [dif_pos hv, show Units.mk0 (x.2 v) hv = V v from Units.ext (hV v).symm]
    rw [show HSMul.hSMul (2 / Real.pi * Inv.inv (norm (x.2 v) ^ 2) : Real) =
        fun z : Complex => ((nu v : Real) : Complex) * z from funext (fun _ => Complex.real_smul)]
    unfold complexTatePlaceTest cc c
    ring
  have hN : mixedEmbedding.norm x = (Finset.univ.prod r) *
      (Finset.univ.prod (fun v => c v ^ 2)) := by
    rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod]
    congr 1
    . apply Finset.prod_congr rfl
      intro v _
      rw [mult_isReal, mixedEmbedding.normAtPlace_apply_of_isReal v.property, pow_one, Real.norm_eq_abs]
    . apply Finset.prod_congr rfl
      intro v _
      rw [mult_isComplex, mixedEmbedding.normAtPlace_apply_of_isComplex v.property]
  have hNormPows : (Finset.univ.prod (fun v => (r v : Complex) ^ s)) *
      (Finset.univ.prod (fun v => (c v : Complex) ^ (2 * s))) =
        (mixedEmbedding.norm x : Complex) ^ s := by
    have hr (v : R) : 0 <= r v := abs_nonneg _
    have hc (v : C) : 0 <= c v ^ 2 := sq_nonneg _
    rw [hN, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg (fun v _ => hr v))
        (Finset.prod_nonneg (fun v _ => hc v)),
      cast_finset_prod_cpow Finset.univ r hr, cast_finset_prod_cpow Finset.univ (fun v => c v ^ 2) hc]
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    have h := Complex.cpow_mul_ofReal_nonneg (norm_nonneg (x.2 v)) ((2 : Nat) : Real) s
    rw [Real.rpow_natCast] at h
    exact h
  have hDensity : (Finset.univ.prod (fun v => (mu v : Complex))) *
      (Finset.univ.prod (fun v => (nu v : Complex))) =
        (((2 / Real.pi) ^ nrComplexPlaces K * Inv.inv (mixedEmbedding.norm x) : Real) : Complex) := by
    rw [<- Complex.ofReal_prod, <- Complex.ofReal_prod, <- Complex.ofReal_mul, hN]
    unfold mu nu
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_inv_distrib, Finset.prod_inv_distrib,
      mul_inv_rev]
    congr 1
    change Inv.inv (Finset.univ.prod r) *
        ((2 / Real.pi) ^ nrComplexPlaces K * Inv.inv (Finset.univ.prod (fun v => c v ^ 2))) = _
    ring
  have hRC (v : R) : rc v = (infiniteLocalHeckeCharacter chi v.val (heckeInfiniteIdeleAt v.val a) : Complex) := by
    have hEq : Units.map (er v).symm.toMonoidHom (U v) = heckeInfiniteIdeleAt v.val a :=
      Units.ext ((er v).symm_apply_apply _)
    change (infiniteLocalHeckeCharacter chi v.val (Units.map (er v).symm.toMonoidHom (U v)) : Complex) = _
    rw [hEq]
  have hCC (v : C) : cc v = (infiniteLocalHeckeCharacter chi v.val (heckeInfiniteIdeleAt v.val a) : Complex) := by
    have hEq : Units.map (ec v).symm.toMonoidHom (V v) = heckeInfiniteIdeleAt v.val a :=
      Units.ext ((ec v).symm_apply_apply _)
    change (infiniteLocalHeckeCharacter chi v.val (Units.map (ec v).symm.toMonoidHom (V v)) : Complex) = _
    rw [hEq]
  have hChar : (Finset.univ.prod rc) * (Finset.univ.prod cc) =
      (chi.val (heckeInfiniteIdeleInclusion K a) : Complex) := by
    simp only [hRC, hCC]
    rw [heckeCharacter_on_infiniteIdele_eq_prod]
    change _ = Circle.coeHom _
    rw [map_prod, prod_eq_prod_mul_prod]
    rfl
  change heckeTateInfiniteVolumeDensity chi s x = _
  unfold heckeTateInfiniteVolumeDensity heckeTateInfiniteTest
  simp only [hR, hC, Finset.prod_mul_distrib]
  rw [<- hDensity, <- hNormPows, <- hChar]
  ring


private theorem isUnit_mixedSpace_of_norm_ne_zero {x : mixedEmbedding.mixedSpace K}
    (hx : Not (mixedEmbedding.norm x = 0)) : IsUnit x := by
  have h := mixedEmbedding.norm_ne_zero_iff.mp hx
  apply Prod.isUnit_iff.mpr
  constructor
  . apply Pi.isUnit_iff.mpr
    intro v
    apply isUnit_iff_ne_zero.mpr
    intro hv
    apply h v.val
    rw [mixedEmbedding.normAtPlace_apply_of_isReal v.property, hv, norm_zero]
  . apply Pi.isUnit_iff.mpr
    intro v
    apply isUnit_iff_ne_zero.mpr
    intro hv
    apply h v.val
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex v.property, hv, norm_zero]

/-- The archimedean Tate integrand on the mixed multiplicative space,
extended by zero on the set of nonunits. -/
def heckeTateInfiniteWeight (chi : UnitaryHeckeCharacter K)
    (s : Complex) (x : mixedEmbedding.mixedSpace K) : Complex :=
  if hx : IsUnit x then
    let a := Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toMonoidHom hx.unit
    heckeTateInfiniteTest chi x * (chi.val (heckeInfiniteIdeleInclusion K a) : Complex) *
      (mixedEmbedding.norm x : Complex) ^ s
  else 0

private theorem heckeTateInfiniteVolumeDensity_eq_zero_of_not_isUnit
    (chi : UnitaryHeckeCharacter K) (s : Complex) (x : mixedEmbedding.mixedSpace K)
    (hx : Not (IsUnit x)) :
    heckeTateInfiniteVolumeDensity chi s x = 0 := by
  have hn : mixedEmbedding.norm x = 0 := Classical.byContradiction
    (fun h => hx (isUnit_mixedSpace_of_norm_ne_zero h))
  choose v hv using mixedEmbedding.norm_eq_zero_iff.mp hn
  unfold heckeTateInfiniteVolumeDensity
  by_cases hr : v.IsReal
  case pos =>
    let w : {v : InfinitePlace K // v.IsReal} := Subtype.mk v hr
    have h0 : x.1 w = 0 := by
      rw [mixedEmbedding.normAtPlace_apply_of_isReal hr] at hv
      exact norm_eq_zero.mp hv
    have hFactor : realTateArchimedeanDensity chi w.property s (x.1 w) = 0 := by
      simp [realTateArchimedeanDensity, h0]
    rw [Finset.prod_eq_zero (Finset.mem_univ w) hFactor, zero_mul]
  case neg =>
    let w : {v : InfinitePlace K // v.IsComplex} :=
      Subtype.mk v (not_isReal_iff_isComplex.mp hr)
    have h0 : x.2 w = 0 := by
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex w.property] at hv
      exact norm_eq_zero.mp hv
    have hFactor : complexTateArchimedeanDensity chi w.property s (x.2 w) = 0 := by
      simp [complexTateArchimedeanDensity, h0]
    rw [Finset.prod_eq_zero (Finset.mem_univ w) hFactor, mul_zero]

private theorem nonzero_realHeckeGamma (chi : UnitaryHeckeCharacter K)
    {v : InfinitePlace K} (hv : v.IsReal) {s : Complex} (hs : 0 < s.re) :
    Not (DedekindZeta.LReal (s + realInfiniteHeckeShift chi hv) = 0) := by
  let w := s + realInfiniteHeckeShift chi hv
  have hw : 0 < w.re := add_pos_of_pos_of_nonneg hs (realInfiniteHeckeShift_re_nonneg chi hv)
  have hw2 : 0 < (w / 2).re := by
    rw [show (w / 2).re = w.re / 2 by simp [div_eq_mul_inv, Complex.mul_re, Complex.inv_re]]
    positivity
  unfold DedekindZeta.LReal
  exact mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (Complex.Gamma_ne_zero_of_re_pos hw2)

private theorem nonzero_complexHeckeGamma (chi : UnitaryHeckeCharacter K)
    {v : InfinitePlace K} (hv : v.IsComplex) {s : Complex} (hs : 0 < s.re) :
    Not (DedekindZeta.LComplex (s + complexInfiniteHeckeShift chi hv) = 0) := by
  let w := s + complexInfiniteHeckeShift chi hv
  have hw : 0 < w.re := add_pos_of_pos_of_nonneg hs (complexInfiniteHeckeShift_re_nonneg chi hv)
  have hp : Not ((2 : Complex) * (Real.pi : Complex) = 0) :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold DedekindZeta.LComplex
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl hp)))
    (Complex.Gamma_ne_zero_of_re_pos hw)

set_option maxHeartbeats 900000 in
/-- The normalized infinite Tate integral is absolutely convergent and is
the product of the standard shifted Gamma factors. -/
theorem integral_heckeTateInfiniteWeight
    (chi : UnitaryHeckeCharacter K) {s : Complex} (hs : 0 < s.re) :
    And (Integrable (heckeTateInfiniteWeight chi s) (DedekindZeta.GammaIntegral.mulHaar K))
      (integral (DedekindZeta.GammaIntegral.mulHaar K) (heckeTateInfiniteWeight chi s) =
        (Finset.univ.prod (fun v : {w : InfinitePlace K // w.IsReal} =>
          DedekindZeta.LReal (s + realInfiniteHeckeShift chi v.property))) *
        (Finset.univ.prod (fun v : {w : InfinitePlace K // w.IsComplex} =>
          DedekindZeta.LComplex (s + complexInfiniteHeckeShift chi v.property)))) := by
  classical
  let d (x : mixedEmbedding.mixedSpace K) : Real :=
    (2 / Real.pi) ^ nrComplexPlaces K * Inv.inv (mixedEmbedding.norm x)
  let D (x : mixedEmbedding.mixedSpace K) := ENNReal.ofReal (d x)
  have hd : Measurable D :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Measurable.inv (mixedEmbedding.continuous_norm (K := K)).measurable))
  have hD : Filter.Eventually (fun x => D x < Top.top)
      (ae (volume : Measure (mixedEmbedding.mixedSpace K))) :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hPos (x : mixedEmbedding.mixedSpace K) : 0 <= d x :=
    mul_nonneg (pow_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) _)
      (inv_nonneg.mpr (mixedEmbedding.norm_nonneg x))
  have hEq : (fun x => HSMul.hSMul (D x).toReal (heckeTateInfiniteWeight chi s x)) =
      heckeTateInfiniteVolumeDensity chi s := by
    funext x
    rw [show (D x).toReal = d x from ENNReal.toReal_ofReal (hPos x), Complex.real_smul]
    unfold heckeTateInfiniteWeight
    by_cases hx : IsUnit x
    case pos =>
      rw [dif_pos hx]
      let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
      let a := Units.map e.symm.toMonoidHom hx.unit
      have hX : e a.val = x := by
        change e (e.symm hx.unit.val) = x
        rw [e.apply_symm_apply, IsUnit.unit_spec]
      have h := heckeTateInfiniteVolumeDensity_on_idele chi s a
      change heckeTateInfiniteVolumeDensity chi s (e a.val) =
        (d (e a.val) : Complex) * (heckeTateInfiniteTest chi (e a.val) *
          (chi.val (heckeInfiniteIdeleInclusion K a) : Complex) *
          (mixedEmbedding.norm (e a.val) : Complex) ^ s) at h
      rw [hX] at h
      exact h.symm
    case neg =>
      rw [dif_neg hx, mul_zero, heckeTateInfiniteVolumeDensity_eq_zero_of_not_isUnit chi s x hx]
  have hFormula := integral_heckeTateInfiniteVolumeDensity chi hs
  have hIntegrable : Integrable (heckeTateInfiniteVolumeDensity chi s) volume := by
    by_contra h
    rw [integral_undef h] at hFormula
    exact (mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun v _ => nonzero_realHeckeGamma chi v.property hs))
      (Finset.prod_ne_zero_iff.mpr (fun v _ => nonzero_complexHeckeGamma chi v.property hs))) hFormula.symm
  change And (Integrable (heckeTateInfiniteWeight chi s) (volume.withDensity D))
    (integral (volume.withDensity D) (heckeTateInfiniteWeight chi s) = _)
  rw [integrable_withDensity_iff_integrable_smul' hd hD,
    integral_withDensity_eq_integral_toReal_smul hd hD, hEq]
  exact And.intro hIntegrable hFormula

section InfiniteUnitMeasure

variable [MeasurableSpace (Units (mixedEmbedding.mixedSpace K))]
  [BorelSpace (Units (mixedEmbedding.mixedSpace K))]

theorem measurableEmbedding_heckeInfiniteUnitVal :
    MeasurableEmbedding (fun a : Units (mixedEmbedding.mixedSpace K) => a.val) :=
  Units.isOpenEmbedding_val.measurableEmbedding

/-- The normalized multiplicative archimedean measure on the unit group. -/
def heckeInfiniteUnitMeasure (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (Units (mixedEmbedding.mixedSpace K))] :
    Measure (Units (mixedEmbedding.mixedSpace K)) :=
  Measure.comap (fun a : Units (mixedEmbedding.mixedSpace K) => a.val)
    (DedekindZeta.GammaIntegral.mulHaar K)

/-- The normalized measure is supported on the units, so the unit inclusion
pushes the group measure to the full mixed-space density. -/
theorem map_heckeInfiniteUnitMeasure_val
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (Units (mixedEmbedding.mixedSpace K))]
    [BorelSpace (Units (mixedEmbedding.mixedSpace K))] :
    Measure.map (fun a : Units (mixedEmbedding.mixedSpace K) => a.val)
      (heckeInfiniteUnitMeasure K) = DedekindZeta.GammaIntegral.mulHaar K := by
  let f (a : Units (mixedEmbedding.mixedSpace K)) := a.val
  let H := DedekindZeta.GammaIntegral.mulHaar K
  let bad := Compl.compl (Set.range f)
  have hf : MeasurableEmbedding f := measurableEmbedding_heckeInfiniteUnitVal
  have hBad : MeasurableSet bad := hf.measurableSet_range.compl
  have hNull : H bad = 0 := by
    change (volume.withDensity (fun x : mixedEmbedding.mixedSpace K =>
      ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * Inv.inv (mixedEmbedding.norm x)))) bad = 0
    rw [withDensity_apply _ hBad]
    have hZero : Filter.EventuallyEq (ae (volume.restrict bad))
        (fun x : mixedEmbedding.mixedSpace K =>
          ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * Inv.inv (mixedEmbedding.norm x)))
        (fun _ => 0) := by
      apply (ae_restrict_mem hBad).mono
      intro x hx
      have hn : mixedEmbedding.norm x = 0 := by
        by_contra h
        exact hx (isUnit_mixedSpace_of_norm_ne_zero h)
      simp [hn]
    rw [lintegral_congr_ae hZero]
    simp
  change Measure.map f (Measure.comap f H) = H
  rw [hf.map_comap]
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hNull)

/-- The archimedean unit measure is invariant under multiplication by
any infinite unit. -/
theorem isMulRightInvariant_heckeInfiniteUnitMeasure :
    (heckeInfiniteUnitMeasure K).IsMulRightInvariant := by
  constructor
  intro a
  let f (x : Units (mixedEmbedding.mixedSpace K)) := x.val
  let T (x : Units (mixedEmbedding.mixedSpace K)) := x * a
  let t (x : mixedEmbedding.mixedSpace K) := x * a.val
  let H := DedekindZeta.GammaIntegral.mulHaar K
  let M := heckeInfiniteUnitMeasure K
  have hf : MeasurableEmbedding f := measurableEmbedding_heckeInfiniteUnitVal
  have ht : Measurable t := (continuous_mul_const a.val).measurable
  have hT : Measurable T := (continuous_mul_const a).measurable
  have hEq : Function.comp f T = Function.comp t f := rfl
  have hNorm : Not (mixedEmbedding.norm a.val = 0) := by
    let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
    let b := Units.map e.symm.toMonoidHom a
    have hA : e b.val = a.val := e.apply_symm_apply a.val
    rw [<- hA, mixedEmbedding_norm_infiniteIdele]
    exact (heckeInfiniteIdeleNorm_pos b).ne'
  have hMul : Measure.map t H = H := by
    change Measure.map (fun x : mixedEmbedding.mixedSpace K => x * a.val)
      (DedekindZeta.mixedMulHaar K) = DedekindZeta.mixedMulHaar K
    exact DedekindZeta.mixedMulHaar_map_mul_right K hNorm
  have hMap : Measure.map f M = H := map_heckeInfiniteUnitMeasure_val K
  change Measure.map T M = M
  have hImages : Measure.map f (Measure.map T M) = Measure.map f M := by
    rw [Measure.map_map hf.measurable hT, hEq, <- Measure.map_map ht hf.measurable, hMap, hMul]
  have ho := congrArg (Measure.comap f) hImages
  rw [hf.comap_map, hf.comap_map] at ho
  exact ho

end InfiniteUnitMeasure

section TateSchwartz

open Function

private abbrev TateRealPlaces (K : Type*) [Field K] := {v : InfinitePlace K // v.IsReal}
private abbrev TateComplexPlaces (K : Type*) [Field K] := {v : InfinitePlace K // v.IsComplex}

private def realTateCoordinate (v : TateRealPlaces K) :
    ContinuousLinearMap (RingHom.id Real) (mixedEmbedding.mixedSpace K) Real :=
  (ContinuousLinearMap.proj v).comp
    (ContinuousLinearMap.fst Real (TateRealPlaces K -> Real) (TateComplexPlaces K -> Complex))

private def complexTateCoordinate (v : TateComplexPlaces K) :
    ContinuousLinearMap (RingHom.id Real) (mixedEmbedding.mixedSpace K) Complex :=
  (ContinuousLinearMap.proj v).comp
    (ContinuousLinearMap.snd Real (TateRealPlaces K -> Real) (TateComplexPlaces K -> Complex))

private theorem temperateGrowth_finset_prod {T X : Type*} [NormedAddCommGroup X]
    [NormedSpace Real X] (S : Finset T) (f : T -> X -> Complex)
    (hf : forall i, Membership.mem S i -> (f i).HasTemperateGrowth) :
    (fun x : X => S.prod (fun i => f i x)).HasTemperateGrowth := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact HasTemperateGrowth.const (1 : Complex)
  | insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i S)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem normSq_le_tateQuadratic (x : mixedEmbedding.mixedSpace K) :
    norm x ^ 2 <= (Finset.univ.sum (fun v : TateRealPlaces K => (x.1 v) ^ 2)) +
      2 * (Finset.univ.sum (fun v : TateComplexPlaces K => norm (x.2 v) ^ 2)) := by
  classical
  let R := Finset.univ.sum (fun v : TateRealPlaces K => (x.1 v) ^ 2)
  let C := Finset.univ.sum (fun v : TateComplexPlaces K => norm (x.2 v) ^ 2)
  have hR : 0 <= R := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 <= C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hRle : norm x.1 <= Real.sqrt (R + 2 * C) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro v
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    have hv : (x.1 v) ^ 2 <= R :=
      Finset.single_le_sum (fun (w : TateRealPlaces K) _ => sq_nonneg (x.1 w)) (Finset.mem_univ v)
    linarith
  have hCle : norm x.2 <= Real.sqrt (R + 2 * C) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro v
    apply Real.le_sqrt_of_sq_le
    have hv : norm (x.2 v) ^ 2 <= C :=
      Finset.single_le_sum (fun (w : TateComplexPlaces K) _ => sq_nonneg (norm (x.2 w))) (Finset.mem_univ v)
    linarith
  have hNorm : norm x <= Real.sqrt (R + 2 * C) := by
    rw [Prod.norm_def]
    exact max_le hRle hCle
  exact (Real.le_sqrt (norm_nonneg _) (by linarith)).mp hNorm

set_option maxHeartbeats 1400000 in
/-- The polynomial Gaussian used in the Tate integral is a Schwartz test on the
full archimedean mixed space. -/
theorem exists_heckeTateInfiniteSchwartz (chi : UnitaryHeckeCharacter K) :
    exists f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex,
      forall x, f x = heckeTateInfiniteTest chi x := by
  classical
  let qr (x : mixedEmbedding.mixedSpace K) :=
    Finset.univ.sum (fun v : TateRealPlaces K => (x.1 v) ^ 2)
  let qc (x : mixedEmbedding.mixedSpace K) :=
    Finset.univ.sum (fun v : TateComplexPlaces K => norm (x.2 v) ^ 2)
  let q (x : mixedEmbedding.mixedSpace K) := -Real.pi * (qr x + 2 * qc x)
  have hqr : qr.HasTemperateGrowth := by
    apply HasTemperateGrowth.sum
    intro v _
    exact (realTateCoordinate v).hasTemperateGrowth.pow 2
  have hqc : qc.HasTemperateGrowth := by
    apply HasTemperateGrowth.sum
    intro v _
    have hNorm : (fun z : Complex => norm z ^ 2).HasTemperateGrowth := hasTemperateGrowth_norm_sq Complex
    exact hNorm.comp (complexTateCoordinate v).hasTemperateGrowth
  have hq : q.HasTemperateGrowth :=
    (HasTemperateGrowth.const (-Real.pi)).mul (hqr.add ((HasTemperateGrowth.const (2 : Real)).mul hqc))
  have hNeg (x : mixedEmbedding.mixedSpace K) : q x <= -Real.pi * norm x ^ 2 :=
    mul_le_mul_of_nonpos_left (normSq_le_tateQuadratic x) (neg_nonpos.mpr Real.pi_pos.le)
  let P (x : mixedEmbedding.mixedSpace K) :=
    (Finset.univ.prod (fun v : TateRealPlaces K =>
      realTatePolynomial (realInfiniteHeckeParameters chi v.property).1 (x.1 v))) *
    (Finset.univ.prod (fun v : TateComplexPlaces K =>
      complexTatePolynomial (complexInfiniteHeckeParameters chi v.property).1 (x.2 v)))
  have hR (v : TateRealPlaces K) :
      (fun x : mixedEmbedding.mixedSpace K =>
        realTatePolynomial (realInfiniteHeckeParameters chi v.property).1 (x.1 v)).HasTemperateGrowth :=
    (Complex.hasTemperateGrowth_ofReal.comp (realTateCoordinate v).hasTemperateGrowth).pow _
  have hC (v : TateComplexPlaces K) :
      (fun x : mixedEmbedding.mixedSpace K =>
        complexTatePolynomial (complexInfiniteHeckeParameters chi v.property).1 (x.2 v)).HasTemperateGrowth := by
    let m := (complexInfiniteHeckeParameters chi v.property).1
    change (fun x : mixedEmbedding.mixedSpace K => complexTatePolynomial m (x.2 v)).HasTemperateGrowth
    by_cases h : 0 <= m
    case pos =>
      simp only [complexTatePolynomial, if_pos h]
      have hConj : (fun z : Complex => starRingEnd Complex z).HasTemperateGrowth :=
        Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth
      exact (hConj.comp (complexTateCoordinate v).hasTemperateGrowth).pow _
    case neg =>
      simp only [complexTatePolynomial, if_neg h]
      exact (complexTateCoordinate v).hasTemperateGrowth.pow _
  have hPoly : P.HasTemperateGrowth :=
    (temperateGrowth_finset_prod Finset.univ _ (fun v _ => hR v)).mul
      (temperateGrowth_finset_prod Finset.univ _ (fun v _ => hC v))
  let G : SchwartzMap (mixedEmbedding.mixedSpace K) Complex :=
    SchwartzMap.postcompCLM Complex.ofRealCLM (schwartzExp_of_negativeQuadratic hq Real.pi_pos hNeg)
  refine Exists.intro (SchwartzMap.smulLeftCLM Complex P G) ?_
  intro x
  rw [SchwartzMap.smulLeftCLM_apply hPoly]
  change P x * (Real.exp (q x) : Complex) = _
  have hGaussian :
      (Real.exp (q x) : Complex) =
        (Finset.univ.prod (fun v : TateRealPlaces K =>
          (Real.exp (-Real.pi * (x.1 v) ^ 2) : Complex))) *
        (Finset.univ.prod (fun v : TateComplexPlaces K =>
          (Real.exp (-2 * Real.pi * norm (x.2 v) ^ 2) : Complex))) := by
    rw [<- Complex.ofReal_prod, <- Complex.ofReal_prod, <- Complex.ofReal_mul,
      <- Real.exp_sum, <- Real.exp_sum, <- Real.exp_add]
    congr 2
    unfold q qr qc
    rw [<- Finset.mul_sum, <- Finset.mul_sum]
    ring
  rw [hGaussian]
  simp only [P, heckeTateInfiniteTest, realTatePlaceTest, complexTatePlaceTest,
    Finset.prod_mul_distrib]
  ring

end TateSchwartz

section TateFourier

open FourierTransform
open scoped RealInnerProductSpace

/-- The real Gaussian in the normalization of the Tate test. -/
def realTateGaussian (x : Real) : Complex :=
  Complex.exp (-(Real.pi : Complex) * (x : Complex) ^ 2)

private theorem realTateGaussian_eq_ofReal (x : Real) :
    realTateGaussian x = (Real.exp (-Real.pi * x ^ 2) : Complex) := by
  simp only [realTateGaussian, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_pow]

private theorem fourier_realTateGaussian : fourier realTateGaussian = realTateGaussian := by
  unfold realTateGaussian
  simpa only [mul_one, Complex.one_cpow, div_one, one_mul] using
    (fourier_gaussian_pi (b := (1 : Complex)) (by norm_num))

private theorem fourier_realTateGaussian_mul_coordinate (y : Real) :
    fourier (fun x : Real => (x : Complex) * realTateGaussian x) y =
      -Complex.I * (y : Complex) * realTateGaussian y := by
  let c : Complex := -2 * Real.pi
  let h (x : Real) := (x : Complex) * realTateGaussian x
  have hPi : 0 < (Real.pi : Complex).re := Real.pi_pos
  have hInt : Integrable realTateGaussian := integrable_cexp_neg_mul_sq hPi
  have hOdd : Integrable h := integrable_mul_cexp_neg_mul_sq hPi
  have hDeriv (x : Real) : HasDerivAt realTateGaussian (c * h x) x := by
    have hq : HasDerivAt (fun t : Real => -Real.pi * t ^ 2) (-Real.pi * (2 * x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_mul (-Real.pi)
    have hExp := ((Real.hasDerivAt_exp (-Real.pi * x ^ 2)).comp x hq).ofReal_comp
    convert hExp using 1
    . funext t
      exact realTateGaussian_eq_ofReal t
    . dsimp only [c, h, Function.comp_apply]
      rw [realTateGaussian_eq_ofReal]
      push_cast
      ring
  have hD : deriv realTateGaussian = fun x => c * h x := funext (fun x => (hDeriv x).deriv)
  have hDI : Integrable (deriv realTateGaussian) := by
    rw [hD]
    exact hOdd.const_mul c
  have hScaling : fourier (fun x => c * h x) y = c * fourier h y := by
    simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    rw [<- integral_const_mul]
    congr 1
    funext t
    ring
  have H := congrFun (Real.fourier_deriv hInt
    (fun x => (hDeriv x).differentiableAt) hDI) y
  rw [hD, hScaling, fourier_realTateGaussian, smul_eq_mul] at H
  have hc : Not (c = 0) := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  apply (mul_right_inj' hc).mp
  exact H.trans (by dsimp [c]; ring)

/-- A real Tate test of parity zero or one transforms into itself times the
corresponding power of the Fourier phase. -/
theorem fourier_realTatePolynomialGaussian (n : Nat) (hn : Or (n = 0) (n = 1)) (y : Real) :
    fourier (fun x : Real => (x : Complex) ^ n * realTateGaussian x) y =
      (-Complex.I) ^ n * (y : Complex) ^ n * realTateGaussian y := by
  rcases hn with h | h
  . subst n
    simpa only [pow_zero, one_mul] using congrFun fourier_realTateGaussian y
  . subst n
    simpa only [pow_one] using fourier_realTateGaussian_mul_coordinate y

private def complexTateGaussian (z : Complex) : Complex :=
  (Real.exp (-2 * Real.pi * norm z ^ 2) : Complex)

private def complexTateMonomial (n : Nat) (z : Complex) : Complex :=
  z ^ n * complexTateGaussian z

set_option backward.isDefEq.respectTransparency false in
private theorem hasLineDerivAt_complexTateMonomial (n : Nat) (z u : Complex) :
    HasLineDerivAt Real (complexTateMonomial n)
      (((n : Complex) * z ^ (n - 1) * u) * complexTateGaussian z +
        z ^ n * (complexTateGaussian z *
          (-4 * (Real.pi : Complex) * (inner Real z u : Complex)))) z u := by
  have hIdF : HasFDerivAt (fun x : Complex => x) (ContinuousLinearMap.id Real Complex) z :=
    hasFDerivAt_id z
  have hId : HasLineDerivAt Real (fun x : Complex => x) u z u := hIdF.hasLineDerivAt u
  have hnorm : HasLineDerivAt Real (fun x : Complex => norm x ^ 2)
      (2 * inner Real z u) z u := by
    simpa only [_root_.smul_apply, two_smul, two_mul, add_apply, innerSL_apply_apply] using
      (hasStrictFDerivAt_norm_sq z).hasFDerivAt.hasLineDerivAt u
  have hQ : HasLineDerivAt Real (fun x : Complex => -2 * Real.pi * norm x ^ 2)
      (-2 * Real.pi * (2 * inner Real z u)) z u := by
    exact (show HasDerivAt (fun t : Real => norm (z + HSMul.hSMul t u) ^ 2)
      (2 * inner Real z u) 0 from hnorm).const_mul (-2 * Real.pi)
  have hGauss : HasLineDerivAt Real complexTateGaussian
      (complexTateGaussian z * (-4 * (Real.pi : Complex) * (inner Real z u : Complex))) z u := by
    change HasDerivAt (fun t : Real => (Real.exp (-2 * Real.pi * norm (z + HSMul.hSMul t u) ^ 2) : Complex)) _ 0
    have hDeriv : HasDerivAt (fun t : Real => -2 * Real.pi * norm (z + HSMul.hSMul t u) ^ 2)
        (-2 * Real.pi * (2 * inner Real z u)) 0 := hQ
    have hExp := Real.hasDerivAt_exp (-2 * Real.pi * norm (z + HSMul.hSMul (0 : Real) u) ^ 2)
    convert (hExp.comp 0 hDeriv).ofReal_comp using 1 <;>
      simp only [zero_smul, add_zero, complexTateGaussian, Function.comp_apply] <;>
      push_cast <;> ring
  change HasDerivAt (fun t : Real => complexTateMonomial n (z + HSMul.hSMul t u)) _ 0
  have hID : HasDerivAt (fun t : Real => z + HSMul.hSMul t u) u 0 := hId
  have hG : HasDerivAt (fun t : Real => complexTateGaussian (z + HSMul.hSMul t u))
      (complexTateGaussian z * (-4 * (Real.pi : Complex) * (inner Real z u : Complex))) 0 := hGauss
  convert (hID.pow n).mul hG using 1 <;>
    first
    | rfl
    | simp only [Pi.pow_apply, zero_smul, add_zero]

private theorem complexTate_inner_coordinates (z : Complex) :
    (inner Real z (1 : Complex) : Complex) + Complex.I * (inner Real z Complex.I : Complex) = z := by
  have hR : inner Real z (1 : Complex) = z.re := by simp [Complex.inner]
  have hI : inner Real z Complex.I = z.im := by simp [Complex.inner, Complex.mul_re]
  rw [hR, hI, mul_comm Complex.I]
  exact Complex.re_add_im z

private abbrev complexTateLineDerivative (u : Complex) (f : SchwartzMap Complex Complex) :
    SchwartzMap Complex Complex :=
  LineDeriv.lineDerivOp u f

set_option backward.isDefEq.respectTransparency false in
private theorem complexTateMonomial_lineDerivativeCombination
    (f g : SchwartzMap Complex Complex) (n : Nat)
    (hf : forall z, f z = complexTateMonomial n z)
    (hg : forall z, g z = complexTateMonomial (n + 1) z) :
    complexTateLineDerivative 1 f +
      HSMul.hSMul Complex.I (complexTateLineDerivative Complex.I f) =
        HSMul.hSMul (-4 * (Real.pi : Complex)) g := by
  ext z
  have hD (u : Complex) : complexTateLineDerivative u f z =
      ((n : Complex) * z ^ (n - 1) * u) * complexTateGaussian z +
        z ^ n * (complexTateGaussian z *
          (-4 * (Real.pi : Complex) * (inner Real z u : Complex))) := by
    unfold complexTateLineDerivative
    rw [SchwartzMap.lineDerivOp_apply, show (f : Complex -> Complex) = complexTateMonomial n from funext hf]
    exact (hasLineDerivAt_complexTateMonomial n z u).lineDeriv
  change complexTateLineDerivative 1 f z + Complex.I * complexTateLineDerivative Complex.I f z =
    (-4 * (Real.pi : Complex)) * g z
  rw [hD, hD, hg, complexTateMonomial]
  calc
    _ = ((n : Complex) * z ^ (n - 1) * complexTateGaussian z) * (1 + Complex.I * Complex.I) +
        (z ^ n * complexTateGaussian z) * (-4 * (Real.pi : Complex)) *
          ((inner Real z (1 : Complex) : Complex) + Complex.I * (inner Real z Complex.I : Complex)) := by ring
    _ = _ := by
      rw [Complex.I_mul_I, complexTate_inner_coordinates, pow_succ]
      ring

set_option backward.isDefEq.respectTransparency false in
private theorem fourier_complexTateMonomial_succ
    (f g : SchwartzMap Complex Complex) (n : Nat)
    (hf : forall z, f z = complexTateMonomial n z)
    (hg : forall z, g z = complexTateMonomial (n + 1) z)
    (w : Complex) :
    fourier g w = (-Complex.I / 2) * w * fourier f w := by
  have hD := complexTateMonomial_lineDerivativeCombination f g n hf hg
  have hF (u : Complex) :
      fourier (complexTateLineDerivative u f) w =
        (2 * (Real.pi : Complex) * Complex.I) * ((inner Real w u : Complex) * fourier f w) := by
    unfold complexTateLineDerivative
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    have hGrowth : (fun z : Complex => inner Real z u).HasTemperateGrowth :=
      ((innerSL Real).flip u).hasTemperateGrowth
    change (2 * (Real.pi : Complex) * Complex.I) *
      (SchwartzMap.smulLeftCLM Complex (fun z => inner Real z u) (fourier f)) w = _
    rw [SchwartzMap.smulLeftCLM_apply hGrowth]
    rfl
  have H := congrArg (fun h => (SchwartzMap.fourierTransformCLM Complex h) w) hD
  simp only [map_add, map_smul, SchwartzMap.fourierTransformCLM_apply] at H
  change fourier (complexTateLineDerivative 1 f) w +
      Complex.I * fourier (complexTateLineDerivative Complex.I f) w =
        (-4 * (Real.pi : Complex)) * fourier g w at H
  rw [hF, hF] at H
  have hC : Not ((-4 * (Real.pi : Complex)) = 0) :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  apply (mul_right_inj' hC).mp
  calc
    _ = _ := H.symm
    _ = (2 * (Real.pi : Complex) * Complex.I) *
        ((inner Real w (1 : Complex) : Complex) + Complex.I * (inner Real w Complex.I : Complex)) *
        fourier f w := by ring
    _ = _ := by rw [complexTate_inner_coordinates]; ring

private theorem fourier_complexTateGaussian_eq (w : Complex) :
    fourier complexTateGaussian w =
      (1 / 2 : Complex) * (Real.exp (-Real.pi * norm w ^ 2 / 2) : Complex) := by
  have hb : 0 < ((2 : Complex) * (Real.pi : Complex)).re := by
    norm_num [Complex.mul_re]
    all_goals positivity
  have hf : complexTateGaussian = fun z : Complex =>
      Complex.exp (-((2 : Complex) * (Real.pi : Complex)) * (norm z : Complex) ^ 2) := by
    funext z
    rw [complexTateGaussian, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hf, fourier_gaussian_innerProductSpace hb, Complex.finrank_real_complex]
  have hExp : (((2 : Nat) : Complex) / 2) = 1 := by norm_num
  rw [hExp, Complex.cpow_one, Complex.ofReal_exp]
  have hPi : Not ((Real.pi : Complex) = 0) := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hHalf : (Real.pi : Complex) / (2 * (Real.pi : Complex)) = 1 / 2 := by
    field_simp
  rw [hHalf]
  congr 2
  push_cast
  field_simp

private theorem fourier_complexTateMonomial_of_schwartz
    (f : Nat -> SchwartzMap Complex Complex)
    (hf : forall n z, f n z = complexTateMonomial n z) (n : Nat) (w : Complex) :
    fourier (f n) w =
      (-Complex.I / 2) ^ n * w ^ n * ((1 / 2 : Complex) *
        (Real.exp (-Real.pi * norm w ^ 2 / 2) : Complex)) := by
  induction n with
  | zero =>
    change fourier (f 0 : Complex -> Complex) w = _
    have h : (f 0 : Complex -> Complex) = complexTateGaussian := by
      funext z
      simpa only [complexTateMonomial, pow_zero, one_mul] using hf 0 z
    rw [h, fourier_complexTateGaussian_eq, pow_zero, pow_zero, one_mul, one_mul]
  | succ n ih =>
    rw [fourier_complexTateMonomial_succ (f n) (f (n + 1)) n (hf n) (hf (n + 1)), ih,
      pow_succ, pow_succ]
    ring

private def complexTateGaussianSchwartz : SchwartzMap Complex Complex :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    (schwartzExp_of_negativeQuadratic
      ((Function.HasTemperateGrowth.const (-(2 * Real.pi))).mul
        (Function.hasTemperateGrowth_norm_sq Complex))
      (show 0 < 2 * Real.pi by positivity) (fun _ => le_rfl))

private def complexTateMonomialSchwartz (n : Nat) : SchwartzMap Complex Complex :=
  SchwartzMap.smulLeftCLM Complex (fun z : Complex => z ^ n) complexTateGaussianSchwartz

private theorem complexTateMonomialSchwartz_apply (n : Nat) (z : Complex) :
    complexTateMonomialSchwartz n z = complexTateMonomial n z := by
  have hP : (fun w : Complex => w ^ n).HasTemperateGrowth :=
    (ContinuousLinearMap.id Real Complex).hasTemperateGrowth.pow n
  rw [complexTateMonomialSchwartz, SchwartzMap.smulLeftCLM_apply hP]
  change z ^ n * (Real.exp (-(2 * Real.pi) * norm z ^ 2) : Complex) =
    z ^ n * (Real.exp (-2 * Real.pi * norm z ^ 2) : Complex)
  have hArg : -(2 * Real.pi) * norm z ^ 2 = -2 * Real.pi * norm z ^ 2 := by ring
  rw [hArg]

/-- The Euclidean Fourier transform of a holomorphic monomial times the
complex Tate Gaussian. -/
theorem fourier_complexTatePolynomialGaussian (n : Nat) (w : Complex) :
    fourier (fun z : Complex => z ^ n * (Real.exp (-2 * Real.pi * norm z ^ 2) : Complex)) w =
      (-Complex.I / 2) ^ n * w ^ n * ((1 / 2 : Complex) *
        (Real.exp (-Real.pi * norm w ^ 2 / 2) : Complex)) := by
  have h := fourier_complexTateMonomial_of_schwartz complexTateMonomialSchwartz
    complexTateMonomialSchwartz_apply n w
  change fourier (complexTateMonomialSchwartz n : Complex -> Complex) w = _ at h
  rw [show (complexTateMonomialSchwartz n : Complex -> Complex) = complexTateMonomial n
    from funext (complexTateMonomialSchwartz_apply n)] at h
  exact h

/-- The complex trace pairing evaluates the Euclidean Fourier transform at
twice the conjugate frequency and uses twice Euclidean measure. The resulting
transform changes the angular monomial to its conjugate and contributes the
Fourier phase. -/
theorem fourier_complexTatePolynomialGaussian_trace (n : Nat) (w : Complex) :
    (2 : Complex) *
        fourier (fun z : Complex => z ^ n * (Real.exp (-2 * Real.pi * norm z ^ 2) : Complex))
          (2 * starRingEnd Complex w) =
      (-Complex.I) ^ n * (starRingEnd Complex w) ^ n *
        (Real.exp (-2 * Real.pi * norm w ^ 2) : Complex) := by
  rw [fourier_complexTatePolynomialGaussian]
  have hNorm : norm ((2 : Complex) * starRingEnd Complex w) = 2 * norm w := by
    simp
  have hExp : -Real.pi * (2 * norm w) ^ 2 / 2 = -2 * Real.pi * norm w ^ 2 := by ring
  rw [hNorm, hExp, mul_pow]
  have hPhase : (-Complex.I / 2) ^ n * (2 : Complex) ^ n = (-Complex.I) ^ n := by
    rw [<- mul_pow]
    congr 1
    ring
  rw [<- hPhase]
  ring

end TateFourier

end Robin1984.GRH
