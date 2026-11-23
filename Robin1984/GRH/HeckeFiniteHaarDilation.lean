import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Robin1984.GRH.HeckeAdeleHaar

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Distributive Haar characters for additive Haar measure and normalized local valuations of number fields.
- Formalization note: Proves Fourier scaling on the finite adeles and computes the additive Haar modulus from integral principal residue classes and local uniformizers.
- PROVENANCE-END
-/

/-!
# Fourier dilation on the finite adeles

The additive Haar character controls the Fourier transform under
multiplication by an idele. The volume of a dilated integral subgroup
is determined by the index of its principal residue classes. A local
uniformizer acts by the reciprocal of the norm of its prime ideal.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K]

private abbrev FiniteDilationAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

variable [MeasurableSpace (FiniteDilationAdeles K)] [BorelSpace (FiniteDilationAdeles K)]


/-- The factor by which multiplication by a finite idele dilates additive Haar measure. -/
noncomputable def heckeFiniteAdditiveModulus : MonoidHom (Units (FiniteDilationAdeles K)) NNReal := by
  letI : LocallyCompactSpace (FiniteDilationAdeles K) := locallyCompactSpace_heckeFiniteAdeles
  exact distribHaarChar (FiniteDilationAdeles K)

/-- The additive Fourier integral on the finite adeles at a finite-adelic frequency. -/
noncomputable def heckeFiniteFourierIntegral
    (mu : Measure (FiniteDilationAdeles K)) (value : FiniteDilationAdeles K -> Complex) (y : FiniteDilationAdeles K) : Complex :=
  integral mu (fun z => value z *
    (heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K) (z * y)) : Complex))

theorem integral_finiteAdele_mul_unit
    (mu : Measure (FiniteDilationAdeles K)) [mu.IsAddHaarMeasure] [mu.Regular]
    (b : Units (FiniteDilationAdeles K)) (F : FiniteDilationAdeles K -> Complex) :
    integral mu (fun z => F (z * (b : FiniteDilationAdeles K))) =
      HSMul.hSMul (heckeFiniteAdditiveModulus (Inv.inv b)) (integral mu F) := by
  let : LocallyCompactSpace (FiniteDilationAdeles K) := locallyCompactSpace_heckeFiniteAdeles
  let pulled : Measure (FiniteDilationAdeles K) := HSMul.hSMul (DomMulAct.mk (Inv.inv b)) mu
  have hMeasure : pulled = HSMul.hSMul (heckeFiniteAdditiveModulus (Inv.inv b)) mu := by
    change HSMul.hSMul (DomMulAct.mk (Inv.inv b)) mu = _
    rw [isAddLeftInvariant_eq_smul_of_regular (HSMul.hSMul (DomMulAct.mk (Inv.inv b)) mu) mu,
      addHaarScalarFactor_smul_eq_distribHaarChar]
    rfl
  calc
    integral mu (fun z => F (z * (b : FiniteDilationAdeles K))) = integral pulled F := by
      dsimp only [pulled]
      rw [integral_domSMul]
      change integral mu (fun z => F (z * (b : FiniteDilationAdeles K))) =
        integral mu (fun z => F (HSMul.hSMul (Inv.inv (Inv.inv b)) z))
      rw [inv_inv]
      apply congrArg (fun f : FiniteDilationAdeles K -> Complex => integral mu f)
      funext z
      change F (z * (b : FiniteDilationAdeles K)) = F ((b : FiniteDilationAdeles K) * z)
      rw [mul_comm z]
    _ = _ := by rw [hMeasure, integral_smul_nnreal_measure]

theorem heckeFiniteFourierIntegral_translate
    (mu : Measure (FiniteDilationAdeles K)) [mu.IsAddHaarMeasure] [mu.Regular]
    (value : FiniteDilationAdeles K -> Complex) (b : Units (FiniteDilationAdeles K)) (y : FiniteDilationAdeles K) :
    heckeFiniteFourierIntegral mu (fun z => value (z * (b : FiniteDilationAdeles K))) y =
      HSMul.hSMul (heckeFiniteAdditiveModulus (Inv.inv b))
        (heckeFiniteFourierIntegral mu value (y * b.inv)) := by
  let F (u : FiniteDilationAdeles K) := value u *
    (heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K) (u * (y * b.inv))) : Complex)
  have h (z : FiniteDilationAdeles K) : z * (b : FiniteDilationAdeles K) * (y * b.inv) = z * y := by
    calc
      z * (b : FiniteDilationAdeles K) * (y * b.inv) = (z * y) * ((b : FiniteDilationAdeles K) * b.inv) := by ac_rfl
      _ = z * y := by rw [b.val_inv, mul_one]
  calc
    _ = integral mu (fun z => F (z * (b : FiniteDilationAdeles K))) := by
      apply integral_congr_ae
      apply ae_of_all
      intro z
      dsimp only [F]
      rw [h]
    _ = _ := integral_finiteAdele_mul_unit mu b F


/-- The finite additive modulus is the mass of the dilated integral subgroup. -/
theorem heckeFiniteAdditiveModulus_eq_measure
    (b : Units (FiniteDilationAdeles K)) :
    (heckeFiniteAdditiveModulus b : ENNReal) =
      heckeFiniteAdeleHaar (HSMul.hSMul b
        (heckeIntegralFiniteAdeles (K := K) : Set (FiniteDilationAdeles K))) := by
  let : LocallyCompactSpace (FiniteDilationAdeles K) := locallyCompactSpace_heckeFiniteAdeles
  let : (heckeFiniteAdeleHaar (K := K)).IsAddHaarMeasure := by
    unfold heckeFiniteAdeleHaar
    infer_instance
  let : (heckeFiniteAdeleHaar (K := K)).Regular := by
    unfold heckeFiniteAdeleHaar
    infer_instance
  have h := distribHaarChar_mul (heckeFiniteAdeleHaar (K := K)) b
    (heckeIntegralFiniteAdeles (K := K) : Set (FiniteDilationAdeles K))
  rw [heckeFiniteAdeleHaar_integral, mul_one] at h
  exact h

/-- Integral local unit coordinates preserve the chosen additive Haar measure. -/
theorem heckeFiniteAdditiveModulus_eq_one_of_integral
    (b : Units (FiniteDilationAdeles K))
    (hVal : Membership.mem heckeIntegralFiniteAdeles (b : FiniteDilationAdeles K))
    (hInv : Membership.mem heckeIntegralFiniteAdeles b.inv) :
    heckeFiniteAdditiveModulus b = 1 := by
  let S : Set (FiniteDilationAdeles K) := (heckeIntegralFiniteAdeles (K := K) : Set (FiniteDilationAdeles K))
  have hS : HSMul.hSMul b S = S := by
    ext z
    constructor
    . intro hz
      change Exists (fun y : FiniteDilationAdeles K => And (Membership.mem S y) (HSMul.hSMul b y = z)) at hz
      choose y hy using hz
      rw [<- hy.2]
      change forall p : HeightOneSpectrum (RingOfIntegers K),
        Membership.mem (p.adicCompletionIntegers K) (b.val p * y p)
      intro p
      exact (p.adicCompletionIntegers K).mul_mem _ _ (hVal p) (hy.1 p)
    . intro hz
      change Exists (fun y : FiniteDilationAdeles K => And (Membership.mem S y) (HSMul.hSMul b y = z))
      refine Exists.intro (b.inv * z) (And.intro ?_ ?_)
      . intro p
        exact (p.adicCompletionIntegers K).mul_mem _ _ (hInv p) (hz p)
      . change (b : FiniteDilationAdeles K) * (b.inv * z) = z
        rw [<- mul_assoc, b.val_inv, one_mul]
  apply ENNReal.coe_injective
  rw [heckeFiniteAdditiveModulus_eq_measure]
  change heckeFiniteAdeleHaar (HSMul.hSMul b S) = (1 : NNReal)
  rw [hS, heckeFiniteAdeleHaar_integral, ENNReal.coe_one]

/-- The dilated subgroup of integral finite adeles. -/
noncomputable def heckeFiniteIdeleIntegralImage (b : Units (FiniteDilationAdeles K)) : AddSubgroup (FiniteDilationAdeles K) :=
  heckeIntegralFiniteAdeles.map {
    toFun := fun z => (b : FiniteDilationAdeles K) * z
    map_zero' := mul_zero _
    map_add' := fun _ _ => mul_add _ _ _ }

omit [MeasurableSpace (FiniteDilationAdeles K)] [BorelSpace (FiniteDilationAdeles K)] in
theorem mem_heckeFiniteIdeleIntegralImage_iff (b : Units (FiniteDilationAdeles K)) (z : FiniteDilationAdeles K) :
    Membership.mem (heckeFiniteIdeleIntegralImage b) z <->
      Membership.mem heckeIntegralFiniteAdeles (b.inv * z) := by
  constructor
  . intro hz
    choose x hx using AddSubgroup.mem_map.mp hz
    have he : (b : FiniteDilationAdeles K) * x = z := hx.2
    rw [<- he, <- mul_assoc, b.inv_val, one_mul]
    exact hx.1
  . intro hz
    apply AddSubgroup.mem_map.mpr
    refine Exists.intro (b.inv * z) (And.intro hz ?_)
    change (b : FiniteDilationAdeles K) * (b.inv * z) = z
    rw [<- mul_assoc, b.val_inv, one_mul]

set_option maxHeartbeats 900000 in
/-- The modulus of an integral finite idele is the reciprocal norm of the
ideal that it cuts out on integral principal adeles. -/
theorem heckeFiniteAdditiveModulus_mul_absNorm_of_integral
    (b : Units (FiniteDilationAdeles K)) (hVal : Membership.mem heckeIntegralFiniteAdeles (b : FiniteDilationAdeles K))
    (I : Ideal (RingOfIntegers K)) (hI : Not (I = 0))
    (hKernel : forall a : RingOfIntegers K,
      Membership.mem (heckeFiniteIdeleIntegralImage b)
          (algebraMap K (FiniteDilationAdeles K) (algebraMap (RingOfIntegers K) K a)) <->
        Membership.mem I a) :
    (Ideal.absNorm I : ENNReal) * (heckeFiniteAdditiveModulus b : ENNReal) = 1 := by
  let R := RingOfIntegers K
  let g := algebraMap K (FiniteDilationAdeles K)
  let e := algebraMap R K
  let H : AddSubgroup (FiniteDilationAdeles K) := heckeIntegralFiniteAdeles
  let D := heckeFiniteIdeleIntegralImage b
  have hD : D <= H := by
    intro z hz
    choose x hx using AddSubgroup.mem_map.mp hz
    have he : (b : FiniteDilationAdeles K) * x = z := hx.2
    rw [<- he]
    intro p
    exact (p.adicCompletionIntegers K).mul_mem _ _ (hVal p) (hx.1 p)
  have hOpen : IsOpen (D : Set (FiniteDilationAdeles K)) :=
    (Homeomorph.smul b).isOpenMap _ isOpen_heckeIntegralFiniteAdeles
  choose d hd using exists_finiteAdele_integral_multiple b.inv
  let dd := e d
  have hdK : Not (dd = 0) :=
    (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective R K)).mpr hd.1
  have hSmall : heckeScaledIntegralFiniteAdeles dd <= D := by
    intro z hz
    choose x hx using AddSubgroup.mem_map.mp hz
    have he : x * g dd = z := hx.2
    apply (mem_heckeFiniteIdeleIntegralImage_iff b z).mpr
    rw [<- he]
    have hEq : b.inv * (x * g dd) = (b.inv * g dd) * x := by ac_rfl
    rw [hEq]
    have hDenom : Membership.mem H (b.inv * g dd) := hd.2
    intro p
    exact (p.adicCompletionIntegers K).mul_mem _ _ (hDenom p) (hx.1 p)
  have hApprox (z : FiniteDilationAdeles K) (hz : Membership.mem H z) :
      exists a : R, Membership.mem D (z - g (e a)) := by
    choose x hx using exists_finiteAdele_sub_principal_modulus z dd hdK
    have hScaled : Membership.mem (heckeScaledIntegralFiniteAdeles dd) (z - g x) := by
      apply (mem_heckeScaledIntegralFiniteAdeles_iff dd hdK (z - g x)).mpr
      intro p
      change Membership.mem (p.adicCompletionIntegers K)
        ((z p - algebraMap K (p.adicCompletion K) x) / algebraMap K (p.adicCompletion K) dd)
      exact hx p
    have hIn : Membership.mem D (z - g x) := hSmall hScaled
    have hxH : Membership.mem H (g x) := by
      have hInH : Membership.mem H (z - g x) := hD hIn
      have hsub : Membership.mem H (z - (z - g x)) := H.sub_mem hz hInH
      rwa [sub_sub_cancel] at hsub
    have hxR : Exists (fun a : R => x = e a) := by
      have hLoc : forall p : HeightOneSpectrum R, Membership.mem (p.adicCompletionIntegers K)
          (algebraMap K (p.adicCompletion K) x / algebraMap K (p.adicCompletion K) 1) := by
        intro p
        rw [map_one, div_one]
        exact hxH p
      simpa only [one_mul] using
        (principal_mem_finiteAdele_modulus_iff x 1 one_ne_zero).mp hLoc
    choose a ha using hxR
    exact Exists.intro a (by rw [<- ha]; exact hIn)
  rw [heckeFiniteAdditiveModulus_eq_measure]
  change (Ideal.absNorm I : ENNReal) * heckeFiniteAdeleHaar (D : Set (FiniteDilationAdeles K)) = 1
  exact heckeFiniteAdeleHaar_of_ideal_kernel I hI D hD hOpen hKernel hApprox


/-- A finite idele supported at one place. -/
noncomputable def heckeFiniteLocalIdele
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    MonoidHom (Units (p.adicCompletion K)) (Units (FiniteDilationAdeles K)) :=
  (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteDilationAdeles K)).toMonoidHom).comp (localIdeleHom K p)

omit [MeasurableSpace (FiniteDilationAdeles K)] [BorelSpace (FiniteDilationAdeles K)] in
private theorem heckeFiniteLocalIdele_at (p : HeightOneSpectrum (RingOfIntegers K))
    (a : Units (p.adicCompletion K)) :
    (heckeFiniteLocalIdele p a).val p = a.val := by
  classical
  change Function.update (fun _ : HeightOneSpectrum (RingOfIntegers K) => 1) p a.val p = a.val
  exact Function.update_self p a.val _

omit [MeasurableSpace (FiniteDilationAdeles K)] [BorelSpace (FiniteDilationAdeles K)] in
private theorem heckeFiniteLocalIdele_away
    (p q : HeightOneSpectrum (RingOfIntegers K)) (hq : Not (q = p))
    (a : Units (p.adicCompletion K)) :
    (heckeFiniteLocalIdele p a).val q = 1 := by
  classical
  change Function.update (fun _ : HeightOneSpectrum (RingOfIntegers K) => 1) p a.val q = 1
  exact Function.update_of_ne hq a.val _

private theorem finiteUniformizerValue_le_one : finiteUniformizerValue <= 1 := by
  apply le_of_lt
  change ((Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) : WithZero (Multiplicative Int)) <
     ((1 : Multiplicative Int) : WithZero (Multiplicative Int))
  exact (@WithZero.coe_lt_coe (Multiplicative Int)
    (@instLTMultiplicative Int Int.instLTInt) (Multiplicative.ofAdd (-1 : Int)) 1).mpr
      (show (-1 : Int) < 0 by decide)

omit [MeasurableSpace (FiniteDilationAdeles K)] [BorelSpace (FiniteDilationAdeles K)] in
set_option maxHeartbeats 1100000 in
/-- The additive Haar modulus of a finite local uniformizer is the reciprocal
of the norm of its prime ideal. -/
theorem heckeFiniteAdditiveModulus_uniformizer_mul_absNorm
    (p : HeightOneSpectrum (RingOfIntegers K)) (u : Units (p.adicCompletion K))
    (hu : Valued.v (u : p.adicCompletion K) = finiteUniformizerValue) :
    (Ideal.absNorm p.asIdeal : ENNReal) *
      (heckeFiniteAdditiveModulus (heckeFiniteLocalIdele p u) : ENNReal) = 1 := by
  let : MeasurableSpace (FiniteDilationAdeles K) := borel (FiniteDilationAdeles K)
  let : BorelSpace (FiniteDilationAdeles K) := BorelSpace.mk rfl
  let R := RingOfIntegers K
  let e := algebraMap R K
  let g := algebraMap K (FiniteDilationAdeles K)
  let b := heckeFiniteLocalIdele p u
  let V : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
  have hb : Membership.mem heckeIntegralFiniteAdeles (b : FiniteDilationAdeles K) := by
    intro q
    by_cases hq : q = p
    . subst q
      change Membership.mem (p.adicCompletionIntegers K) (b.val p)
      rw [heckeFiniteLocalIdele_at, HeightOneSpectrum.mem_adicCompletionIntegers, hu]
      exact finiteUniformizerValue_le_one
    . change Membership.mem (q.adicCompletionIntegers K) (b.val q)
      rw [heckeFiniteLocalIdele_away p q hq]
      exact (q.adicCompletionIntegers K).one_mem
  have hInv : (Inv.inv b : Units (FiniteDilationAdeles K)) = heckeFiniteLocalIdele p (Inv.inv u) :=
    (map_inv (heckeFiniteLocalIdele p) u).symm
  have hAt : b.inv p = u.inv := by
    change ((Inv.inv b : Units (FiniteDilationAdeles K)).val) p = u.inv
    rw [hInv, heckeFiniteLocalIdele_at]
    rfl
  have hAway (q : HeightOneSpectrum R) (hq : Not (q = p)) : b.inv q = 1 := by
    change ((Inv.inv b : Units (FiniteDilationAdeles K)).val) q = 1
    rw [hInv, heckeFiniteLocalIdele_away p q hq]
  have hUV : V u.val * V u.inv = 1 := by rw [<- map_mul, u.val_inv, map_one]
  have hVU : V u.inv * V u.val = 1 := by rw [<- map_mul, u.inv_val, map_one]
  apply heckeFiniteAdditiveModulus_mul_absNorm_of_integral b hb p.asIdeal p.ne_bot
  intro a
  rw [mem_heckeFiniteIdeleIntegralImage_iff]
  let x := algebraMap K (p.adicCompletion K) (e a)
  have hVal : V x = p.intValuation a := by
    change Valued.v ((e a : K) : p.adicCompletion K) = p.intValuation a
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have hIdeal : V x <= V u.val <-> Membership.mem p.asIdeal a := by
    rw [hVal, show V u.val = finiteUniformizerValue from hu]
    simpa [pow_one, finiteUniformizerValue, WithZero.exp] using p.intValuation_le_pow_iff_mem a 1
  constructor
  . intro h
    have hp : Membership.mem (p.adicCompletionIntegers K) (b.inv p * x) := h p
    rw [hAt, HeightOneSpectrum.mem_adicCompletionIntegers] at hp
    change V (u.inv * x) <= 1 at hp
    rw [map_mul] at hp
    have hle := mul_le_mul_of_nonneg_left hp (show 0 <= V u.val from zero_le)
    rw [<- mul_assoc, hUV, one_mul, mul_one] at hle
    exact hIdeal.mp hle
  . intro h q
    by_cases hq : q = p
    . subst q
      change Membership.mem (p.adicCompletionIntegers K) (b.inv p * x)
      rw [hAt, HeightOneSpectrum.mem_adicCompletionIntegers]
      change V (u.inv * x) <= 1
      rw [map_mul]
      have hle := mul_le_mul_of_nonneg_left (hIdeal.mpr h) (show 0 <= V u.inv from zero_le)
      rwa [hVU] at hle
    . change Membership.mem (q.adicCompletionIntegers K)
        (b.inv q * algebraMap (RingOfIntegers K) (q.adicCompletion K) a)
      rw [hAway q hq, one_mul]
      exact HeightOneSpectrum.coe_algebraMap_mem R K q a

end Robin1984.GRH
