import Mathlib.RingTheory.FractionalIdeal.Norm
import Robin1984.GRH.HeckeTateClassPoisson

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The finite local Fourier transforms in Tate's thesis.
- Formalization note: Identifies the finite Tate Fourier transform with the inverse-character test scaled by the different and conductor.
- PROVENANCE-END
-/

/-!
# Finite Fourier transform of the canonical Tate test

The trace pairing identifies the annihilator of the integral adeles with
the inverse different. Conductor translation and unit covariance impose
the exact support and determine the Fourier test there. The finite norm
of the different-conductor scaling is the reciprocal arithmetic conductor.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open IsDedekindDomain NumberField MeasureTheory
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

/-- A nonzero fractional ideal is integral if every local exponent is
nonnegative. -/
theorem fractionalIdeal_le_one_of_count_nonneg
    (J : FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)
    (hJ : Not (J = 0))
    (hExp : forall p : HeightOneSpectrum (RingOfIntegers K), 0 <= FractionalIdeal.count K p J) :
    J <= 1 := by
  let f (p : HeightOneSpectrum (RingOfIntegers K)) :=
    (p.asIdeal : FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K) ^
      FractionalIdeal.count K p J
  let g (_ : HeightOneSpectrum (RingOfIntegers K)) :
      FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K := 1
  have hf : Function.HasFiniteMulSupport f := by
    apply (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)).subset
    intro p hp hZero
    exact hp (by simp only [f, hZero, zpow_zero])
  have hg : Function.HasFiniteMulSupport g := by simp [g, Function.HasFiniteMulSupport]
  have hfg : f <= g := by
    intro p
    change (p.asIdeal : FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K) ^
      FractionalIdeal.count K p J <= 1
    rw [<- Int.toNat_of_nonneg (hExp p), zpow_natCast]
    exact pow_le_one' FractionalIdeal.coeIdeal_le_one _
  calc
    J = finprod f := (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ).symm
    _ <= finprod g := finprod_le_finprod' hf hg hfg
    _ = 1 := finprod_one

/-- The normalized finite valuation has its ordinary multiplicative
order, so a unit index is at most one exactly when its additive index
is nonpositive. -/
theorem tate_valueIndex_le_one_iff (z : Multiplicative Int) :
    Iff (@LE.le (WithZero (Multiplicative Int)) (inferInstance : LE (WithZero (Multiplicative Int)))
          (z : WithZero (Multiplicative Int)) (1 : WithZero (Multiplicative Int)))
      (Multiplicative.toAdd z <= (0 : Int)) := by
  exact @WithZero.coe_le_coe (Multiplicative Int) (inferInstance : LE (Multiplicative Int))
    z (1 : Multiplicative Int)

private abbrev F (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

/-- A finite idele is integral at every place exactly when its
associated fractional ideal is integral. -/
theorem heckeFiniteIdele_val_integral_iff_ideal_le_one (b : Units (F K)) :
    Iff (Membership.mem (heckeIntegralFiniteAdeles (K := K)) b.val)
      (heckeFiniteIdeleFractionalIdeal b <= 1) := by
  have hAt (p : HeightOneSpectrum (RingOfIntegers K)) :
      Iff (Membership.mem (p.adicCompletionIntegers K) (b.val p))
        (0 <= heckeFiniteIdeleExponent b p) := by
    let z := heckeLocalValueIndex p (heckeFiniteIdeleComponent p b)
    have hz : (z : WithZero (Multiplicative Int)) = Valued.v (b.val p) :=
      coe_heckeLocalValueIndex p (heckeFiniteIdeleComponent p b)
    change (Valued.v (b.val p) <= (1 : WithZero (Multiplicative Int))) <->
      0 <= -(Multiplicative.toAdd z)
    rw [<- hz, tate_valueIndex_le_one_iff, neg_nonneg]
  constructor
  . intro h
    apply fractionalIdeal_le_one_of_count_nonneg _ (heckeFiniteIdeleFractionalIdeal_ne_zero b)
    intro p
    rw [count_heckeFiniteIdeleFractionalIdeal]
    exact (hAt p).mp (h p)
  . intro h p
    apply (hAt p).mpr
    rw [<- count_heckeFiniteIdeleFractionalIdeal]
    have hCount := FractionalIdeal.count_mono K p (heckeFiniteIdeleFractionalIdeal_ne_zero b) h
    simpa only [FractionalIdeal.count_one] using hCount

/-- Multiplication by a finite idele carries a diagonal field element
into the integral adeles exactly on the inverse fractional ideal. -/
theorem principal_mul_heckeFiniteIdele_integral_iff
    (d : Units (F K)) (t : K) :
    Iff (Membership.mem (heckeIntegralFiniteAdeles (K := K)) (d.val * algebraMap K (F K) t))
      (Membership.mem (Inv.inv (heckeFiniteIdeleFractionalIdeal d)) t) := by
  by_cases ht : t = 0
  . subst t
    constructor
    . intro _
      exact FractionalIdeal.zero_mem _
    . intro _
      rw [map_zero, mul_zero]
      exact (heckeIntegralFiniteAdeles (K := K)).zero_mem
  . let u := Units.mk0 t ht
    let b := FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K u
    let A := heckeFiniteIdeleFractionalIdeal d
    let J := FractionalIdeal.spanSingleton (nonZeroDivisors (RingOfIntegers K)) t
    have hMap := congrArg Units.val (map_mul (heckeFiniteIdeleIdealHom (K := K)) d b)
    have hB := congrArg Units.val (heckeFiniteIdeleIdealHom_principal u)
    rw [coe_toPrincipalIdeal] at hB
    change heckeFiniteIdeleFractionalIdeal b = J at hB
    change heckeFiniteIdeleFractionalIdeal (d * b) = A * heckeFiniteIdeleFractionalIdeal b at hMap
    have hVal : d.val * algebraMap K (F K) t = (d * b).val := rfl
    rw [hVal, heckeFiniteIdele_val_integral_iff_ideal_le_one, hMap, hB]
    change A * J <= 1 <-> Membership.mem (Inv.inv A) t
    rw [<- FractionalIdeal.spanSingleton_le_iff_mem]
    change A * J <= 1 <-> J <= Inv.inv A
    have hANe : Not (A = 0) := heckeFiniteIdeleFractionalIdeal_ne_zero d
    have hInv : A * Inv.inv A = 1 := (Units.mk0 A hANe).val_inv
    constructor
    . intro h
      calc
        J = (J * A) * Inv.inv A := by rw [mul_assoc, hInv, mul_one]
        _ <= 1 * Inv.inv A := mul_le_mul_left (by simpa only [mul_comm J A] using h) _
        _ = Inv.inv A := one_mul _
    . intro h
      exact (mul_le_mul_right h A).trans hInv.le

/-- The full additive annihilator of the integral adeles is obtained by
dilating those adeles by the inverse of any idele representing the different. -/
theorem heckeFiniteAddChar_annihilator_iff_different_mul_integral
    (d : Units (F K))
    (hd : heckeFiniteIdeleFractionalIdeal d = DedekindZeta.Theta.differentFractionalIdeal K)
    (y : F K) :
    Iff (forall x : F K, Membership.mem (heckeIntegralFiniteAdeles (K := K)) x ->
      heckeFiniteAddChar (x * y) = 1)
      (Membership.mem (heckeIntegralFiniteAdeles (K := K)) (d.val * y)) := by
  let H := heckeIntegralFiniteAdeles (K := K)
  let g := algebraMap K (F K)
  have hMul {a b : F K} (ha : Membership.mem H a) (hb : Membership.mem H b) :
      Membership.mem H (a * b) := fun q =>
    (q.adicCompletionIntegers K).toSubring.mul_mem (ha q) (hb q)
  have hdInt : Membership.mem H d.val := by
    apply (heckeFiniteIdele_val_integral_iff_ideal_le_one d).mpr
    rw [hd]
    exact FractionalIdeal.coeIdeal_le_one
  have hDual : DedekindZeta.Theta.dualIdeal K (Ideal.span (Set.singleton (1 : RingOfIntegers K))) =
      Inv.inv (heckeFiniteIdeleFractionalIdeal d) := by
    have hOne : ((Ideal.span (Set.singleton (1 : RingOfIntegers K))) :
        FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K) = 1 := by
      have hTop : Ideal.span (Set.singleton (1 : RingOfIntegers K)) =
          (Top.top : Ideal (RingOfIntegers K)) := Ideal.span_singleton_eq_top.mpr isUnit_one
      exact (congrArg (fun I : Ideal (RingOfIntegers K) =>
        (I : FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)) hTop).trans
        (FractionalIdeal.coeIdeal_top (nonZeroDivisors (RingOfIntegers K)))
    rw [DedekindZeta.Theta.dualIdeal, hOne, one_mul, hd]
  rw [heckeFiniteAddChar_annihilator_iff_traceDualRepresentative]
  constructor
  . intro h
    choose t ht using h
    have hT := (principal_mul_heckeFiniteIdele_integral_iff d t).mpr ((Eq.mp (congrArg (fun J => Membership.mem J t) hDual) ht.1))
    have hDiff : Membership.mem H (d.val * (y - g t)) := hMul hdInt ht.2
    have hSum : Membership.mem H (d.val * (y - g t) + d.val * g t) := H.add_mem hDiff hT
    rw [mul_sub, sub_add_cancel] at hSum
    exact hSum
  . intro h
    choose t ht using exists_finiteAdele_sub_principal_integral y
    have hDiff : Membership.mem H (d.val * (y - g t)) := hMul hdInt ht
    have hY : Membership.mem H (d.val * y) := h
    have hSub : Membership.mem H (d.val * y - d.val * (y - g t)) := H.sub_mem hY hDiff
    rw [mul_sub, sub_sub_cancel] at hSub
    refine Exists.intro t (And.intro ?_ ht)
    rw [hDual]
    exact (principal_mul_heckeFiniteIdele_integral_iff d t).mp hSub

private abbrev Frac (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K

/-- The idelic finite norm is the reciprocal of the associated fractional
ideal's arithmetic norm. -/
theorem heckeFiniteIdeleNorm_eq_inv_fractionalIdeal_absNorm (b : Units (F K)) :
    heckeFiniteIdeleNorm b =
      Inv.inv ((FractionalIdeal.absNorm (heckeFiniteIdeleFractionalIdeal b) : Rat) : Real) := by
  let P := HeightOneSpectrum (RingOfIntegers K)
  let J := heckeFiniteIdeleFractionalIdeal b
  let e := heckeFiniteIdeleExponent b
  let f (p : P) : Frac K := (p.asIdeal : Frac K) ^ e p
  let N : MonoidHom (Frac K) Real := (Rat.castHom Real).toMonoidHom.comp
    (FractionalIdeal.absNorm : MonoidWithZeroHom (Frac K) Rat).toMonoidHom
  have hFinite : Function.HasFiniteMulSupport f := by
    apply (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)).subset
    intro p hp hZero
    apply hp
    have he : e p = 0 := by
      exact (count_heckeFiniteIdeleFractionalIdeal b p).symm.trans hZero
    simp [f, he]
  have hLocal (p : P) : norm (b.val p) = Inv.inv (N (f p)) := by
    let a := heckeFiniteIdeleComponent p b
    let i := Multiplicative.toAdd (heckeLocalValueIndex p a)
    have hn : norm (b.val p) = (dedekindPrimeNorm K p : Real) ^ i := by
      change norm a.val = _
      rw [FinitePlace.norm_def, <- coe_heckeLocalValueIndex p a,
        WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe]
      change (((Ideal.absNorm p.asIdeal : NNReal) ^ i : NNReal) : Real) =
        (Ideal.absNorm p.asIdeal : Real) ^ i
      norm_cast
    have hN : N (f p) = (dedekindPrimeNorm K p : Real) ^ e p := by
      change ((FractionalIdeal.absNorm ((p.asIdeal : Frac K) ^ e p) : Rat) : Real) = _
      simp [FractionalIdeal.coeIdeal_absNorm, dedekindPrimeNorm]
    rw [hn, hN, <- zpow_neg]
    change _ ^ i = _ ^ (-(-i))
    rw [neg_neg]
  calc
    heckeFiniteIdeleNorm b = finprod (fun p : P => norm (b.val p)) := rfl
    _ = finprod (fun p : P => Inv.inv (N (f p))) := finprod_congr hLocal
    _ = Inv.inv (finprod (fun p : P => N (f p))) := finprod_inv_distrib _
    _ = _ := by rw [<- map_finprod N hFinite]; rfl

/-- The finite idele attached to the product of the different and the
character conductor has inverse arithmetic conductor as its norm. -/
theorem heckeFiniteIdeleNorm_different_mul_conductor
    (chi : UnitaryHeckeCharacter K) (d c : Units (F K))
    (hd : heckeFiniteIdeleFractionalIdeal d = DedekindZeta.Theta.differentFractionalIdeal K)
    (hc : heckeFiniteIdeleFractionalIdeal c = (heckeConductorIdeal chi : Frac K)) :
    heckeFiniteIdeleNorm (d * c) = Inv.inv (heckeArithmeticConductor chi) := by
  have hD : DedekindZeta.Theta.differentFractionalIdeal K =
      (differentIdeal Int (RingOfIntegers K) : Frac K) := rfl
  rw [map_mul, heckeFiniteIdeleNorm_eq_inv_fractionalIdeal_absNorm d,
    heckeFiniteIdeleNorm_eq_inv_fractionalIdeal_absNorm c, hd, hc, hD,
    FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm,
    Rat.cast_natCast, Rat.cast_natCast, NumberField.absNorm_differentIdeal K (RingOfIntegers K),
    heckeArithmeticConductor, mul_inv_rev, mul_comm]

/-- The fractional ideal of the finite conductor has exactly the local
conductor exponents used by the Tate test. -/
theorem count_heckeConductorIdeal (chi : UnitaryHeckeCharacter K)
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    FractionalIdeal.count K p (heckeConductorIdeal chi : Frac K) = (heckeConductorExponent chi p : Int) := by
  let S := (finite_heckeRamifiedPlaces chi).toFinset
  let J (q : HeightOneSpectrum (RingOfIntegers K)) : Ideal (RingOfIntegers K) :=
    q.asIdeal ^ heckeConductorExponent chi q
  let A (q : HeightOneSpectrum (RingOfIntegers K)) : Frac K :=
    (q.asIdeal : Frac K) ^ heckeConductorExponent chi q
  have hCast (T : Finset (HeightOneSpectrum (RingOfIntegers K))) :
      ((T.prod J : Ideal (RingOfIntegers K)) : Frac K) = T.prod A := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert i T hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, FractionalIdeal.coeIdeal_mul, ih]
      simp only [A, FractionalIdeal.coeIdeal_pow]
  have hEq : (heckeConductorIdeal chi : Frac K) = S.prod A := hCast S
  have hNZ (q : HeightOneSpectrum (RingOfIntegers K)) : Not (A q = 0) :=
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr q.ne_bot)
  rw [hEq, FractionalIdeal.count_prod K p S A (fun q _ => hNZ q)]
  have hSelf : FractionalIdeal.count K p (A p) = (heckeConductorExponent chi p : Int) := by
    rw [show A p = _ from rfl, FractionalIdeal.count_pow, FractionalIdeal.count_self, mul_one]
  have hAway (q : HeightOneSpectrum (RingOfIntegers K)) (hq : Not (q = p)) :
      FractionalIdeal.count K p (A q) = 0 := by
    rw [show A q = _ from rfl, FractionalIdeal.count_pow,
      FractionalIdeal.count_maximal_coprime K p hq, mul_zero]
  by_cases hp : Membership.mem S p
  . rw [Finset.sum_eq_single_of_mem p hp (fun q _ hq => hAway q hq), hSelf]
  . have hUnram : HeckeUnramifiedAt chi p := by
      by_contra hRam
      apply hp
      change Membership.mem (finite_heckeRamifiedPlaces chi).toFinset p
      exact ((finite_heckeRamifiedPlaces chi).mem_toFinset).mpr hRam
    have hExp := (heckeConductorExponent_eq_zero_iff chi p).mpr hUnram
    rw [hExp, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro q hq
    apply hAway q
    intro hqp
    exact hp (Eq.mp (congrArg (fun q => Membership.mem S q) hqp) hq)

/-- Some finite idele represents the conductor ideal and has its prescribed
local normalized valuations at every place. -/
theorem exists_heckeFiniteIdele_conductor (chi : UnitaryHeckeCharacter K) :
    exists b : Units (F K),
      And (heckeFiniteIdeleFractionalIdeal b = (heckeConductorIdeal chi : Frac K))
        (forall p : HeightOneSpectrum (RingOfIntegers K),
          (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) (b.val p) =
            ((Multiplicative.ofAdd (-(heckeConductorExponent chi p : Int)) : Multiplicative Int) :
              WithZero (Multiplicative Int))) := by
  let J := heckeConductorIdeal chi
  have hJ0 : Not (J = 0) := by
    intro h
    have hNorm := heckeConductorIdeal_absNorm_pos chi
    change 0 < Ideal.absNorm J at hNorm
    rw [h, map_zero] at hNorm
    exact (lt_irrefl (0 : Nat)) hNorm
  have hNe : Not ((J : Frac K) = 0) := FractionalIdeal.coeIdeal_ne_zero.mpr hJ0
  choose b hb using surjective_heckeFiniteIdeleIdealHom (K := K) (Units.mk0 (J : Frac K) hNe)
  have hId : heckeFiniteIdeleFractionalIdeal b = (J : Frac K) := congrArg Units.val hb
  refine Exists.intro b (And.intro hId ?_)
  intro p
  let z := heckeLocalValueIndex p (heckeFiniteIdeleComponent p b)
  have hz : (z : WithZero (Multiplicative Int)) = Valued.v (b.val p) :=
    coe_heckeLocalValueIndex p (heckeFiniteIdeleComponent p b)
  have hExp := count_heckeFiniteIdeleFractionalIdeal b p
  rw [hId, show J = heckeConductorIdeal chi from rfl, count_heckeConductorIdeal] at hExp
  change (heckeConductorExponent chi p : Int) = -(Multiplicative.toAdd z) at hExp
  have hZAdd : Multiplicative.toAdd z = -(heckeConductorExponent chi p : Int) := by omega
  have hZ : z = Multiplicative.ofAdd (-(heckeConductorExponent chi p : Int)) :=
    congrArg Multiplicative.ofAdd hZAdd
  rw [<- hz, hZ]

private abbrev Value := WithZero (Multiplicative Int)

/-- Two complementary valuation bounds imply integrality of the product. -/
theorem tate_value_product_bound
    {x y a b : Value} (hx : x <= a) (hy : y <= b) :
    x * y <= a * b :=
  @mul_le_mul' (WithZero (Multiplicative Int)) inferInstance
    (inferInstance : Preorder (WithZero (Multiplicative Int)))
    inferInstance inferInstance x a y b hx hy

/-- Multiplying by the inverse depth preserves the corresponding lower bound. -/
theorem tate_value_mul_at_complementary_depths
    (n : Int) (a b : Value)
    (ha : a <= ((Multiplicative.ofAdd n : Multiplicative Int) : Value))
    (hb : b <= ((Multiplicative.ofAdd (-n) : Multiplicative Int) : Value)) :
    a * b <= 1 := by
  have hBound := tate_value_product_bound ha hb
  have hCut : ((Multiplicative.ofAdd n : Multiplicative Int) : Value) *
      ((Multiplicative.ofAdd (-n) : Multiplicative Int) : Value) = 1 := by
    rw [<- WithZero.coe_mul]
    change ((Multiplicative.ofAdd (n + (-n)) : Multiplicative Int) : Value) = 1
    rw [add_neg_cancel]
    rfl
  rw [hCut] at hBound
  exact hBound

private theorem heckeFiniteIdeleInclusion_local
    (p : HeightOneSpectrum (RingOfIntegers K)) (a : Units (p.adicCompletion K)) :
    heckeFiniteIdeleInclusion (heckeFiniteLocalIdele p a) = localIdeleHom K p a := by
  apply Units.ext
  exact Prod.ext rfl rfl

private theorem heckeFiniteLocalIdele_isIntegralUnit
    (p : HeightOneSpectrum (RingOfIntegers K)) (a : Units (p.adicCompletion K))
    (ha : Valued.v (a : p.adicCompletion K) = 1) :
    Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) (heckeFiniteLocalIdele p a) := by
  apply (mem_heckeIntegralFiniteUnitGroup_iff_valued_one (heckeFiniteLocalIdele p a)).mpr
  intro q
  by_cases hq : q = p
  . subst q
    rw [heckeFiniteLocalIdele_at]
    exact ha
  . rw [heckeFiniteLocalIdele_away p q hq, map_one]

/-- Translating by an integral adele whose local depths meet the conductor
does not change the additive Tate test. -/
theorem heckeFiniteAdditiveTateTest_translate_at_conductor
    (chi : UnitaryHeckeCharacter K) (b : F K)
    (hb : Membership.mem (heckeIntegralFiniteAdeles (K := K)) b)
    (hDepth : forall p : HeightOneSpectrum (RingOfIntegers K),
      (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) (b p) <=
        ((Multiplicative.ofAdd (-(heckeConductorExponent chi p : Int)) : Multiplicative Int) :
          WithZero (Multiplicative Int))) (z : F K) :
    heckeFiniteAdditiveTateTest chi (z + b) = heckeFiniteAdditiveTateTest chi z := by
  let H := heckeIntegralFiniteAdeles (K := K)
  by_cases hz : Membership.mem H z
  . have hzB : Membership.mem H (z + b) := H.add_mem hz hb
    have hz' : Membership.mem (heckeIntegralFiniteAdeles (K := K)) z := hz
    have hzB' : Membership.mem (heckeIntegralFiniteAdeles (K := K)) (z + b) := hzB
    simp only [heckeFiniteAdditiveTateTest, if_pos hz', if_pos hzB']
    apply Finset.prod_congr rfl
    intro p _
    apply heckeLocalAdditiveTateTest_eq_of_sub_le p chi
    change (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
      (z p + b p - z p) <= _
    rw [add_sub_cancel_left]
    exact hDepth p
  . have hzB : Not (Membership.mem H (z + b)) := by
      intro h
      have hz' := H.sub_mem h hb
      rw [add_sub_cancel_right] at hz'
      exact hz hz'
    have hz' : Not (Membership.mem (heckeIntegralFiniteAdeles (K := K)) z) := hz
    have hzB' : Not (Membership.mem (heckeIntegralFiniteAdeles (K := K)) (z + b)) := hzB
    simp only [heckeFiniteAdditiveTateTest, if_neg hz', if_neg hzB']

/-- A finite collection of unit coordinates extends to an integral
finite idele. -/
theorem exists_heckeIntegralFiniteUnit_matching
    (S : Finset (HeightOneSpectrum (RingOfIntegers K))) (x : F K)
    (hx : forall p : HeightOneSpectrum (RingOfIntegers K), Membership.mem S p ->
      (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) (x p) = 1) :
    exists b : Units (F K),
      And (Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) b)
        (forall p : HeightOneSpectrum (RingOfIntegers K), Membership.mem S p -> b.val p = x p) := by
  have hLocal (p : HeightOneSpectrum (RingOfIntegers K)) :
      exists u : Units (p.adicCompletion K),
        And ((Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) u.val = 1)
          (Membership.mem S p -> u.val = x p) := by
    by_cases hp : Membership.mem S p
    . have hNe : Not (x p = 0) := by
        intro h
        have hVal := hx p hp
        rw [h, map_zero] at hVal
        exact zero_ne_one hVal
      exact Exists.intro (Units.mk0 (x p) hNe) (And.intro (hx p hp) (fun _ => rfl))
    . refine Exists.intro (1 : Units (p.adicCompletion K)) (And.intro ?_ (fun h => (hp h).elim))
      rw [Units.val_one, map_one]
  choose u hu using hLocal
  let b := S.prod (fun p => heckeFiniteLocalIdele p (u p))
  have hAt (p : HeightOneSpectrum (RingOfIntegers K)) (hp : Membership.mem S p) :
      heckeFiniteIdeleComponent p b = u p := by
    change heckeFiniteIdeleComponent p (S.prod (fun q => heckeFiniteLocalIdele q (u q))) = u p
    rw [map_prod, Finset.prod_eq_single_of_mem p hp]
    . apply Units.ext
      exact heckeFiniteLocalIdele_at p (u p)
    . intro q _ hq
      apply Units.ext
      exact heckeFiniteLocalIdele_away q p (Ne.symm hq) (u q)
  have hAway (p : HeightOneSpectrum (RingOfIntegers K)) (hp : Not (Membership.mem S p)) :
      heckeFiniteIdeleComponent p b = 1 := by
    change heckeFiniteIdeleComponent p (S.prod (fun q => heckeFiniteLocalIdele q (u q))) = 1
    rw [map_prod]
    apply Finset.prod_eq_one
    intro q hq
    have hpq : Not (p = q) := fun e => hp (by rw [e]; exact hq)
    apply Units.ext
    exact heckeFiniteLocalIdele_away q p hpq (u q)
  refine Exists.intro b (And.intro ?_ ?_)
  . apply (mem_heckeIntegralFiniteUnitGroup_iff_valued_one b).mpr
    intro p
    change Valued.v ((heckeFiniteIdeleComponent p b).val) = 1
    by_cases hp : Membership.mem S p
    . rw [hAt p hp]
      exact (hu p).1
    . rw [hAway p hp, Units.val_one, map_one]
  . intro p hp
    change (heckeFiniteIdeleComponent p b).val = x p
    rw [hAt p hp]
    exact (hu p).2 hp

/-- The inverse character has the same ramified finite places. -/
theorem heckeRamifiedFinset_inverse (chi : UnitaryHeckeCharacter K) :
    (finite_heckeRamifiedPlaces (unitaryHeckeInverse chi)).toFinset =
      (finite_heckeRamifiedPlaces chi).toFinset := by
  ext p
  rw [(finite_heckeRamifiedPlaces (unitaryHeckeInverse chi)).mem_toFinset,
    (finite_heckeRamifiedPlaces chi).mem_toFinset]
  change Not (HeckeUnramifiedAt (unitaryHeckeInverse chi) p) <->
    Not (HeckeUnramifiedAt chi p)
  apply not_congr
  rw [<- heckeConductorExponent_eq_zero_iff, <- heckeConductorExponent_eq_zero_iff,
    heckeConductorExponent_inverse]

/-- The finite additive Tate test is normalized to one at the identity. -/
theorem heckeFiniteAdditiveTateTest_one (chi : UnitaryHeckeCharacter K) :
    heckeFiniteAdditiveTateTest chi (1 : F K) = 1 := by
  have hInt : Membership.mem (heckeIntegralFiniteAdeles (K := K)) (1 : F K) :=
    fun p => (p.adicCompletionIntegers K).one_mem
  rw [heckeFiniteAdditiveTateTest, if_pos hInt]
  apply Finset.prod_eq_one
  intro p hp
  have hpRam : Not (HeckeUnramifiedAt chi p) :=
    ((finite_heckeRamifiedPlaces chi).mem_toFinset).mp hp
  change heckeLocalAdditiveTateTest p chi 1 = 1
  have hV : (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
      (1 : p.adicCompletion K) = 1 := map_one _
  rw [heckeLocalAdditiveTateTest, if_neg hpRam, dif_pos hV]
  simp

/-- The additive test vanishes off the local unit condition at any
ramified place. -/
theorem heckeFiniteAdditiveTateTest_eq_zero_of_ramified_not_unit
    (chi : UnitaryHeckeCharacter K) (x : F K)
    (p : HeightOneSpectrum (RingOfIntegers K))
    (hp : Not (HeckeUnramifiedAt chi p))
    (hv : Not ((Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
      (x p) = 1)) :
    heckeFiniteAdditiveTateTest chi x = 0 := by
  by_cases hx : Membership.mem (heckeIntegralFiniteAdeles (K := K)) x
  . rw [heckeFiniteAdditiveTateTest, if_pos hx]
    apply Finset.prod_eq_zero ((finite_heckeRamifiedPlaces chi).mem_toFinset.mpr hp)
    rw [heckeLocalAdditiveTateTest, if_neg hp, dif_neg hv]
  . rw [heckeFiniteAdditiveTateTest, if_neg hx]

variable [MeasurableSpace (F K)] [BorelSpace (F K)]

/-- A nonzero Fourier value annihilates every additive translation
that preserves the test. -/
theorem heckeFiniteFourierIntegral_nonzero_annihilates_translation
    (mu : Measure (F K)) [mu.IsAddHaarMeasure]
    (T : F K -> Complex) (b y : F K) (hT : forall z, T (z + b) = T z)
    (hy : Not (heckeFiniteFourierIntegral mu T y = 0)) :
    heckeFiniteAddChar (b * y) = 1 := by
  let G (z : F K) := T z * (heckeFiniteAddChar (z * y) : Complex)
  let I := heckeFiniteFourierIntegral mu T y
  have hI : integral mu G = I := rfl
  have hShift : integral mu (fun z : F K => G (z + b)) = I :=
    (integral_add_right_eq_self G b).trans hI
  have hFactor (z : F K) :
      G (z + b) = (heckeFiniteAddChar (b * y) : Complex) * G z := by
    change T (z + b) * (heckeFiniteAddChar ((z + b) * y) : Complex) = _
    rw [hT z, add_mul, AddChar.map_add_eq_mul]
    change T z * ((heckeFiniteAddChar (z * y) : Complex) * (heckeFiniteAddChar (b * y) : Complex)) =
      (heckeFiniteAddChar (b * y) : Complex) * (T z * (heckeFiniteAddChar (z * y) : Complex))
    ring
  have hE : (heckeFiniteAddChar (b * y) : Complex) * I = I := by
    rw [<- hI, <- integral_const_mul]
    exact (integral_congr_ae (Filter.Eventually.of_forall fun z => (hFactor z).symm)).trans hShift
  apply Subtype.ext
  change (heckeFiniteAddChar (b * y) : Complex) = 1
  have h : ((heckeFiniteAddChar (b * y) : Complex) - 1) * I = 0 := by
    rw [sub_mul, hE, one_mul, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hy)

omit [BorelSpace (F K)] in
/-- The finite Fourier transform is constant on cosets of the full additive
annihilator of the integral finite adeles. -/
theorem heckeFiniteFourierIntegral_TateTest_add_annihilator
    (mu : Measure (F K)) (chi : UnitaryHeckeCharacter K) (y b : F K)
    (hb : forall x : F K, Membership.mem (heckeIntegralFiniteAdeles (K := K)) x ->
      heckeFiniteAddChar (x * b) = 1) :
    heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) (y + b) =
      heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) y := by
  apply integral_congr_ae
  filter_upwards with x
  change heckeFiniteAdditiveTateTest chi x * (heckeFiniteAddChar (x * (y + b)) : Complex) =
    heckeFiniteAdditiveTateTest chi x * (heckeFiniteAddChar (x * y) : Complex)
  by_cases hx : Membership.mem (heckeIntegralFiniteAdeles (K := K)) x
  . rw [mul_add, AddChar.map_add_eq_mul, hb x hx, mul_one]
  . simp only [heckeFiniteAdditiveTateTest, if_neg hx, zero_mul]

/-- A nonzero finite Fourier value lies in the trace dual of the conductor
lattice, expressed by integrality after multiplying by the two ideles. -/
theorem heckeFiniteFourierIntegral_TateTest_support_conductor_different
    (mu : Measure (F K)) [mu.IsAddHaarMeasure]
    (chi : UnitaryHeckeCharacter K) (d c : Units (F K))
    (hd : heckeFiniteIdeleFractionalIdeal d = DedekindZeta.Theta.differentFractionalIdeal K)
    (hc : heckeFiniteIdeleFractionalIdeal c = (heckeConductorIdeal chi :
      FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))
    (hcVal : forall p : HeightOneSpectrum (RingOfIntegers K),
      (Valued.v : Valuation (p.adicCompletion K) Value) (c.val p) =
        ((Multiplicative.ofAdd (-(heckeConductorExponent chi p : Int)) : Multiplicative Int) : Value))
    (y : F K) (hy : Not (heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) y = 0)) :
    Membership.mem (heckeIntegralFiniteAdeles (K := K)) (d.val * (c.val * y)) := by
  let H := heckeIntegralFiniteAdeles (K := K)
  have hcInt : Membership.mem H c.val := by
    apply (heckeFiniteIdele_val_integral_iff_ideal_le_one c).mpr
    rw [hc]
    exact FractionalIdeal.coeIdeal_le_one
  apply (heckeFiniteAddChar_annihilator_iff_different_mul_integral d hd (c.val * y)).mp
  intro x hx
  have hB : Membership.mem H (x * c.val) :=
    fun p => (p.adicCompletionIntegers K).toSubring.mul_mem (hx p) (hcInt p)
  have hDepth (p : HeightOneSpectrum (RingOfIntegers K)) :
      (Valued.v : Valuation (p.adicCompletion K) Value) ((x * c.val) p) <=
        ((Multiplicative.ofAdd (-(heckeConductorExponent chi p : Int)) : Multiplicative Int) : Value) := by
    let v := (Valued.v : Valuation (p.adicCompletion K) Value)
    change v (x p * c.val p) <= _
    have hX : v (x p) <= 1 := hx p
    rw [map_mul]
    have hCut : v (c.val p) <=
        ((Multiplicative.ofAdd (-(heckeConductorExponent chi p : Int)) : Multiplicative Int) : Value) :=
      (hcVal p).le
    simpa only [one_mul] using tate_value_product_bound hX hCut
  have hZ := heckeFiniteFourierIntegral_nonzero_annihilates_translation mu
    (heckeFiniteAdditiveTateTest chi) (x * c.val) y
    (heckeFiniteAdditiveTateTest_translate_at_conductor chi (x * c.val) hB hDepth) hy
  simpa only [mul_assoc] using hZ

/-- At a ramified place a frequency that is too integral after correcting
for the different has zero Fourier value. This holds at every depth
strictly below the local conductor exponent. -/
theorem heckeFiniteFourierIntegral_TateTest_eq_zero_of_relative_depth
    (mu : Measure (F K)) [mu.IsAddHaarMeasure] [mu.Regular]
    (chi : UnitaryHeckeCharacter K) (d : Units (F K))
    (hd : heckeFiniteIdeleFractionalIdeal d = DedekindZeta.Theta.differentFractionalIdeal K)
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    (hn : n < heckeConductorExponent chi p) (y : F K)
    (hy : (Valued.v : Valuation (p.adicCompletion K) Value) ((d.val * y) p) <=
      ((Multiplicative.ofAdd (n : Int) : Multiplicative Int) : Value)) :
    heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) y = 0 := by
  have hNot : Not (HeckeTrivialAtDepth chi p n) := by
    intro h
    exact (not_le_of_gt hn) (heckeConductorExponent_le h)
  unfold HeckeTrivialAtDepth at hNot
  push Not at hNot
  choose a ha using hNot
  let u := heckeFiniteLocalIdele p a
  have hUnit : Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) u :=
    heckeFiniteLocalIdele_isIntegralUnit p a ha.1
  have hChar : Not ((chi.val (heckeFiniteIdeleInclusion u) : Complex) = 1) := by
    intro h
    apply ha.2.2
    apply Subtype.ext
    rw [<- heckeFiniteIdeleInclusion_local p a]
    exact h
  have hInt : Membership.mem (heckeIntegralFiniteAdeles (K := K)) (d.val * (y * (u.val - 1))) := by
    intro q
    change Membership.mem (q.adicCompletionIntegers K)
      (d.val q * (y q * (u.val q - 1)))
    by_cases hq : q = p
    . subst q
      let v := (Valued.v : Valuation (p.adicCompletion K) Value)
      change v (d.val p * (y p * (u.val p - 1))) <= (1 : Value)
      have hAt : u.val p = a.val := heckeFiniteLocalIdele_at p a
      rw [hAt, <- mul_assoc, map_mul]
      exact tate_value_mul_at_complementary_depths (n : Int) _ _ hy ha.2.1
    . have hAway : u.val q = 1 := heckeFiniteLocalIdele_away p q hq a
      rw [hAway, sub_self, mul_zero, mul_zero]
      exact (q.adicCompletionIntegers K).zero_mem
  exact heckeFiniteFourierIntegral_TateTest_eq_zero_of_trivial_additive_pairing mu chi y u hUnit hChar
    ((heckeFiniteAddChar_annihilator_iff_different_mul_integral d hd (y * (u.val - 1))).mpr hInt)

private def tateDepthValue (k : Int) : Value :=
  ((Multiplicative.ofAdd k : Multiplicative Int) : Value)

private theorem tateDepthValue_zero : tateDepthValue 0 = 1 := rfl

private theorem tateDepthValue_mul (m n : Int) :
    tateDepthValue m * tateDepthValue n = tateDepthValue (m + n) := rfl

/-- In the normalized discrete order, a value below one is at most
the value at exponent minus one, including the zero value. -/
theorem tate_value_le_uniformizer_of_lt_one
    (x : Value) (hx : x < 1) :
    x <= tateDepthValue (-1) := by
  cases x with
  | none =>
    change (Bot.bot : Value) <= _
    exact bot_le
  | some z =>
    have hZ : @LT.lt (Multiplicative Int) (inferInstance : LT (Multiplicative Int))
        z (1 : Multiplicative Int) :=
      (@WithZero.coe_lt_coe (Multiplicative Int) (inferInstance : LT (Multiplicative Int))
        z (1 : Multiplicative Int)).mp hx
    have hInt : Multiplicative.toAdd z < (0 : Int) := hZ
    have hCut : Multiplicative.toAdd z <= (-1 : Int) := by omega
    exact (@WithZero.coe_le_coe (Multiplicative Int) (inferInstance : LE (Multiplicative Int))
      z (Multiplicative.ofAdd (-1 : Int))).mpr hCut

/-- Moving the conductor depth to the right of a discrete valuation bound
adds its exponent, preserving the direction of the inequality. -/
theorem tate_value_le_of_mul_conductor_le_uniformizer
    (x : Value) (n : Int)
    (h : x * tateDepthValue (-n) <= tateDepthValue (-1)) :
    x <= tateDepthValue (n - 1) := by
  have hScale : tateDepthValue n <= tateDepthValue n := le_rfl
  have hBound := tate_value_product_bound hScale h
  have hX : tateDepthValue n * (x * tateDepthValue (-n)) = x := by
    rw [mul_left_comm, tateDepthValue_mul, add_neg_cancel, tateDepthValue_zero, mul_one]
  rw [hX, tateDepthValue_mul] at hBound
  exact hBound

/-- Nonzero finite Fourier values lie in the correctly scaled conductor
lattice and are units at every ramified place after that scaling. -/
theorem heckeFiniteFourierIntegral_TateTest_nonzero_normalized_support
    (mu : Measure (F K)) [mu.IsAddHaarMeasure] [mu.Regular]
    (chi : UnitaryHeckeCharacter K) (d c : Units (F K))
    (hd : heckeFiniteIdeleFractionalIdeal d = DedekindZeta.Theta.differentFractionalIdeal K)
    (hc : heckeFiniteIdeleFractionalIdeal c = (heckeConductorIdeal chi :
      FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))
    (hcVal : forall p : HeightOneSpectrum (RingOfIntegers K),
      (Valued.v : Valuation (p.adicCompletion K) Value) (c.val p) =
        tateDepthValue (-(heckeConductorExponent chi p : Int)))
    (y : F K) (hy : Not (heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) y = 0)) :
    And (Membership.mem (heckeIntegralFiniteAdeles (K := K)) (d.val * (c.val * y)))
      (forall p : HeightOneSpectrum (RingOfIntegers K), Not (HeckeUnramifiedAt chi p) ->
        (Valued.v : Valuation (p.adicCompletion K) Value) ((d.val * (c.val * y)) p) = 1) := by
  let x := d.val * (c.val * y)
  have hInt : Membership.mem (heckeIntegralFiniteAdeles (K := K)) x :=
    heckeFiniteFourierIntegral_TateTest_support_conductor_different mu chi d c hd hc hcVal y hy
  refine And.intro hInt ?_
  intro p hp
  let v := (Valued.v : Valuation (p.adicCompletion K) Value)
  change v (x p) = 1
  by_contra hNe
  have hLe : v (x p) <= 1 := hInt p
  have hLt : v (x p) < 1 :=
    @lt_of_le_of_ne (WithZero (Multiplicative Int))
      (inferInstance : PartialOrder (WithZero (Multiplicative Int))) _ _ hLe hNe
  have hCut := tate_value_le_uniformizer_of_lt_one (v (x p)) hLt
  let e := heckeConductorExponent chi p
  have hExp : 0 < e :=
    Nat.pos_of_ne_zero (fun hz => hp ((heckeConductorExponent_eq_zero_iff chi p).mp hz))
  have hValEq : v (x p) = v ((d.val * y) p) * tateDepthValue (-(e : Int)) := by
    change v (d.val p * (c.val p * y p)) = v (d.val p * y p) * _
    rw [mul_comm (c.val p) (y p), <- mul_assoc, map_mul, hcVal p]
  rw [hValEq] at hCut
  have hResid := tate_value_le_of_mul_conductor_le_uniformizer (v ((d.val * y) p)) (e : Int) hCut
  let n := e - 1
  have hSmall : n < e := by dsimp only [n]; omega
  have hN : (n : Int) = (e : Int) - 1 := by dsimp only [n]; omega
  have hFreq : v ((d.val * y) p) <= tateDepthValue (n : Int) := by
    rw [hN]
    exact hResid
  exact hy (heckeFiniteFourierIntegral_TateTest_eq_zero_of_relative_depth mu chi d hd p n hSmall y hFreq)

/-- Exact finite Fourier transform of the Tate test. Its scalar is the
Fourier value at the inverse of the different times the conductor. -/
theorem heckeFiniteFourierIntegral_TateTest_eq_mul_inverse
    (mu : Measure (F K)) [mu.IsAddHaarMeasure] [mu.Regular]
    (chi : UnitaryHeckeCharacter K) (d c : Units (F K))
    (hd : heckeFiniteIdeleFractionalIdeal d = DedekindZeta.Theta.differentFractionalIdeal K)
    (hc : heckeFiniteIdeleFractionalIdeal c = (heckeConductorIdeal chi :
      FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))
    (hcVal : forall p : HeightOneSpectrum (RingOfIntegers K),
      (Valued.v : Valuation (p.adicCompletion K) Value) (c.val p) =
        tateDepthValue (-(heckeConductorExponent chi p : Int)))
    (y : F K) :
    heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) y =
      heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) (d * c).inv *
        heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi) (d.val * (c.val * y)) := by
  let H := heckeIntegralFiniteAdeles (K := K)
  let S := (finite_heckeRamifiedPlaces chi).toFinset
  let x := d.val * (c.val * y)
  let b := (d * c).inv
  let opp := unitaryHeckeInverse chi
  let fourier := heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi)
  change fourier y = fourier b * heckeFiniteAdditiveTateTest opp x
  have hRam (p : HeightOneSpectrum (RingOfIntegers K)) :
      Membership.mem S p <-> Not (HeckeUnramifiedAt chi p) :=
    (finite_heckeRamifiedPlaces chi).mem_toFinset
  have hSupport (hy : Not (fourier y = 0)) :
      And (Membership.mem H x) (forall p : HeightOneSpectrum (RingOfIntegers K),
        Membership.mem S p ->
        (Valued.v : Valuation (p.adicCompletion K) Value) (x p) = 1) := by
    have h := heckeFiniteFourierIntegral_TateTest_nonzero_normalized_support mu chi d c hd hc hcVal y hy
    exact And.intro h.1 (fun p hp => h.2 p ((hRam p).mp hp))
  by_cases hx : Membership.mem H x
  . by_cases hShell : forall p : HeightOneSpectrum (RingOfIntegers K),
        Membership.mem S p ->
        (Valued.v : Valuation (p.adicCompletion K) Value) (x p) = 1
    . choose u hu using exists_heckeIntegralFiniteUnit_matching S x hShell
      have huInt : Membership.mem H u.val := ((mem_heckeIntegralFiniteUnitGroup u).mp hu.1).1
      have hBase : d.val * b = c.inv := by
        change d.val * (c.inv * d.inv) = c.inv
        rw [mul_left_comm d.val c.inv, d.val_inv, mul_one]
      have hCancel : c.inv * x = d.val * y := by
        change c.inv * (d.val * (c.val * y)) = d.val * y
        rw [mul_left_comm c.inv d.val, <- mul_assoc c.inv, c.inv_val, one_mul]
      have hDiff : d.val * (y - b * u.val) = c.inv * (x - u.val) := by
        rw [mul_sub, mul_sub, hCancel, <- mul_assoc, hBase]
      have hIntDiff : Membership.mem H (d.val * (y - b * u.val)) := by
        rw [hDiff]
        intro p
        change Membership.mem (p.adicCompletionIntegers K) (c.inv p * (x p - u.val p))
        by_cases hp : Membership.mem S p
        . rw [hu.2 p hp, sub_self, mul_zero]
          exact (p.adicCompletionIntegers K).zero_mem
        . have hup : HeckeUnramifiedAt chi p := not_not.mp (mt (hRam p).mpr hp)
          have hExp := (heckeConductorExponent_eq_zero_iff chi p).mpr hup
          have hv := hcVal p
          rw [hExp, Int.natCast_zero, neg_zero, tateDepthValue_zero] at hv
          have huLoc := (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
            (a := heckeFiniteIdeleComponent p c)).mpr hv
          exact (p.adicCompletionIntegers K).mul_mem _ _ huLoc.2 (sub_mem (hx p) (huInt p))
      have hShift := heckeFiniteFourierIntegral_TateTest_add_annihilator mu chi
        (b * u.val) (y - b * u.val)
        ((heckeFiniteAddChar_annihilator_iff_different_mul_integral d hd _).mpr hIntDiff)
      rw [add_comm (b * u.val), sub_add_cancel] at hShift
      have hTest : heckeFiniteAdditiveTateTest opp x = heckeFiniteAdditiveTateTest opp u.val := by
        change heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi) x =
          heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi) u.val
        rw [heckeFiniteAdditiveTateTest, if_pos hx, heckeFiniteAdditiveTateTest, if_pos huInt,
          heckeRamifiedFinset_inverse]
        apply Finset.prod_congr rfl
        intro p hp
        rw [hu.2 p hp]
      have huTest := heckeFiniteAdditiveTateTest_mul_integralUnit_apply opp (1 : F K) u hu.1
      rw [one_mul, heckeFiniteAdditiveTateTest_one, one_mul] at huTest
      have hChar : opp.val (heckeFiniteIdeleInclusion (Inv.inv u)) =
          chi.val (heckeFiniteIdeleInclusion u) := by
        change Inv.inv (chi.val (heckeFiniteIdeleInclusion (Inv.inv u))) = _
        rw [map_inv, map_inv, inv_inv]
      rw [hChar] at huTest
      rw [hTest, huTest, mul_comm]
      exact hShift.trans (heckeFiniteFourierIntegral_TateTest_mul_integralUnit mu chi b u hu.1)
    . push Not at hShell
      choose p hp using hShell
      have hOpp : Not (HeckeUnramifiedAt opp p) := by
        intro h
        apply (hRam p).mp hp.1
        apply (heckeConductorExponent_eq_zero_iff chi p).mp
        rw [<- heckeConductorExponent_inverse]
        exact (heckeConductorExponent_eq_zero_iff opp p).mpr h
      rw [heckeFiniteAdditiveTateTest_eq_zero_of_ramified_not_unit opp x p hOpp hp.2,
        mul_zero]
      by_contra hy
      exact hp.2 ((hSupport hy).2 p hp.1)
  . rw [heckeFiniteAdditiveTateTest, if_neg hx, mul_zero]
    by_contra hy
    exact hx (hSupport hy).1

/-- The finite dual test in adelic Poisson summation is the Tate test for
the inverse character evaluated at the different-conductor multiple. -/
theorem heckeTateDualFiniteTest_eq_mul_inverse
    (chi : UnitaryHeckeCharacter K) (d c : Units (F K))
    (hd : heckeFiniteIdeleFractionalIdeal d = DedekindZeta.Theta.differentFractionalIdeal K)
    (hc : heckeFiniteIdeleFractionalIdeal c = (heckeConductorIdeal chi :
      FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))
    (hcVal : forall p : HeightOneSpectrum (RingOfIntegers K),
      (Valued.v : Valuation (p.adicCompletion K) Value) (c.val p) =
        tateDepthValue (-(heckeConductorExponent chi p : Int)))
    (y : F K) :
    heckeTateDualFiniteTest chi y =
      heckeTateDualFiniteTest chi (d * c).inv *
        heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi) ((d * c).val * y) := by
  let b := d * c
  let n : Units (F K) :=
    { val := -1
      inv := -1
      val_inv := by rw [neg_mul_neg, mul_one]
      inv_val := by rw [neg_mul_neg, mul_one] }
  have hn : Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) n := by
    apply (mem_heckeIntegralFiniteUnitGroup_iff_valued_one n).mpr
    intro p
    change (Valued.v : Valuation (p.adicCompletion K) Value) (-(1 : p.adicCompletion K)) = 1
    rw [Valuation.map_neg, map_one]
  let : LocallyCompactSpace (F K) := locallyCompactSpace_heckeFiniteAdeles
  let : (heckeFiniteAdeleHaar (K := K)).IsAddHaarMeasure := by
    unfold heckeFiniteAdeleHaar
    infer_instance
  let : (heckeFiniteAdeleHaar (K := K)).Regular := by
    unfold heckeFiniteAdeleHaar
    infer_instance
  let fourier := heckeFiniteFourierIntegral heckeFiniteAdeleHaar (heckeFiniteAdditiveTateTest chi)
  let scalar := (chi.val (heckeFiniteIdeleInclusion n) : Complex)
  have hNeg (z : F K) : fourier (-z) = scalar * fourier z := by
    have h := heckeFiniteFourierIntegral_TateTest_mul_integralUnit
      heckeFiniteAdeleHaar chi z n hn
    have hN : z * n.val = -z := mul_neg_one z
    rw [hN] at h
    exact h
  have hFourier : fourier y = fourier b.inv *
      heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi) (b.val * y) := by
    change _ = fourier b.inv *
      heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi) ((d.val * c.val) * y)
    rw [mul_assoc]
    exact heckeFiniteFourierIntegral_TateTest_eq_mul_inverse
      heckeFiniteAdeleHaar chi d c hd hc hcVal y
  let h := Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex)
  change h * fourier (-y) = h * fourier (-b.inv) *
    heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi) (b.val * y)
  rw [hNeg, hNeg, hFourier]
  simp only [mul_assoc]

end Robin1984.GRH
