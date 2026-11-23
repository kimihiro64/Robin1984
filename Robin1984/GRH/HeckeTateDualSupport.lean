import Robin1984.GRH.HeckeTateThetaDecay

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's finite additive Fourier transform, duality of an integral modulus, and the restricted product of local fields.
- Formalization note: Bounds the Fourier transform of the finite Hecke test by the mass of the finite integral adeles and gives it a compact support.
- PROVENANCE-END
-/

/-!
# The finite Fourier dual of a Tate test

The finite Hecke test is locally constant and compactly supported. Its
Fourier transform vanishes away from the annihilator of the conductor
modulus and is uniformly bounded by the mass of the integral subgroup.
This supplies the finite dual input to the Tate theta estimate.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev F (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev A (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

/-- The additive character on the finite adeles from the global trace pairing. -/
noncomputable def heckeFiniteAddChar : AddChar (F K) Circle where
  toFun a := heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K) a : A K)
  map_zero_eq_one' := AddChar.map_zero_eq_one heckeAdeleAddChar
  map_add_eq_mul' a b := by
    have h : (Prod.mk (0 : InfiniteAdeleRing K) (a + b) : A K) =
        (Prod.mk (0 : InfiniteAdeleRing K) a : A K) + Prod.mk 0 b :=
      Prod.ext (by simp) rfl
    rw [h]
    exact AddChar.map_add_eq_mul (heckeAdeleAddChar (K := K))
      (Prod.mk (0 : InfiniteAdeleRing K) a) (Prod.mk (0 : InfiniteAdeleRing K) b)

private theorem heckeFiniteAddChar_eq_one_of_integral (a : F K)
    (ha : Membership.mem (heckeIntegralFiniteAdeles (K := K)) a) :
    heckeFiniteAddChar a = 1 := by
  let b : A K := Prod.mk (0 : InfiniteAdeleRing K) a
  have hb (p : HeightOneSpectrum (RingOfIntegers K)) :
      Membership.mem (p.adicCompletionIntegers K) (b.2 p) := ha p
  calc
    heckeFiniteAddChar a = heckeAdeleAddChar b := rfl
    _ = Real.fourierChar (infiniteAdeleTrace b.1) := heckeAdeleAddChar_of_integralFinitePart b hb
    _ = 1 := by
      change Real.fourierChar (infiniteAdeleTrace (0 : InfiniteAdeleRing K)) = 1
      rw [map_zero, AddChar.map_zero_eq_one]

private theorem finiteIntegral_mul_mem {a b : F K}
    (ha : Membership.mem (heckeIntegralFiniteAdeles (K := K)) a)
    (hb : Membership.mem (heckeIntegralFiniteAdeles (K := K)) b) :
    Membership.mem (heckeIntegralFiniteAdeles (K := K)) (a * b) := by
  intro p
  exact (p.adicCompletionIntegers K).mul_mem _ _ (ha p) (hb p)

private theorem finiteIntegral_of_globalInteger (c : RingOfIntegers K) :
    Membership.mem (heckeIntegralFiniteAdeles (K := K))
      (algebraMap K (F K) (algebraMap (RingOfIntegers K) K c)) := by
  intro p
  exact HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers K) K p c

/-- The annihilator of an integral principal modulus is contained in a compact set. -/
theorem exists_compact_heckeFiniteChar_annihilator_cover
    (d : RingOfIntegers K) (hd : Not (d = 0)) :
    Exists (fun V : Set (F K) => And (IsCompact V)
      (forall y : F K, (forall a : F K, Membership.mem (heckeIntegralFiniteAdeles (K := K)) a ->
        heckeFiniteAddChar (a * (algebraMap K (F K) (algebraMap (RingOfIntegers K) K d) * y)) = 1) ->
          Membership.mem V y)) := by
  let R := RingOfIntegers K
  let H := heckeIntegralFiniteAdeles (K := K)
  let k := algebraMap R K
  let g := algebraMap K (F K)
  let Q := DedekindZeta.Theta.dualIdeal K (Ideal.span (Set.singleton (1 : R)))
  choose c hc hcQ using Q.isFractional
  have hc0 : Not (c = 0) := nonZeroDivisors.ne_zero hc
  let D := c * d
  have hD0 : Not (k D = 0) := (map_ne_zero_iff k (IsFractionRing.injective R K)).mpr (mul_ne_zero hc0 hd)
  let V := Set.image (fun a : F K => g (Inv.inv (k D)) * a) (H : Set (F K))
  have hV : IsCompact V := isCompact_integralFiniteAdeles.image (continuous_const.mul continuous_id)
  refine Exists.intro V (And.intro hV ?_)
  intro y hy
  choose t ht using exists_finiteAdele_sub_principal_integral (g (k d) * y)
  let z := g (k d) * y - g t
  have hz : Membership.mem H z := ht
  have htChar (a : F K) (ha : Membership.mem H a) :
      heckeFiniteAddChar (a * g t) = 1 := by
    have h := hy a ha
    have hZ := heckeFiniteAddChar_eq_one_of_integral (a * z) (finiteIntegral_mul_mem ha hz)
    have he : a * (g (k d) * y) = a * z + a * g t := by
      change _ = a * (g (k d) * y - g t) + a * g t
      ring
    rw [he, AddChar.map_add_eq_mul, hZ, one_mul] at h
    exact h
  have htQ : Membership.mem Q t := by
    apply (heckeAdeleAddChar_finitePrincipalIdeal_annihilator_iff (1 : R) one_ne_zero t).mp
    intro a ha
    change heckeFiniteAddChar (a * g (k 1 * t)) = 1
    rw [map_one, one_mul]
    exact htChar a ha
  choose e he using hcQ t htQ
  have he' : k e = k c * t := he
  have hct : Membership.mem H (g (k c) * g t) := by
    rw [<- map_mul, <- he']
    exact finiteIntegral_of_globalInteger e
  have hcZ : Membership.mem H (g (k c) * z) :=
    finiteIntegral_mul_mem (finiteIntegral_of_globalInteger c) hz
  have hDy : Membership.mem H (g (k D) * y) := by
    have hEq : g (k D) * y = g (k c) * z + g (k c) * g t := by
      change g (k (c * d)) * y = g (k c) * (g (k d) * y - g t) + g (k c) * g t
      rw [map_mul k, map_mul g]
      ring
    rw [hEq]
    exact H.add_mem hcZ hct
  refine Exists.intro (g (k D) * y) (And.intro hDy ?_)
  change g (Inv.inv (k D)) * (g (k D) * y) = y
  rw [<- mul_assoc, <- map_mul]
  have hInv : Inv.inv (k D) * k D = 1 := by
    rw [mul_comm, <- div_eq_mul_inv, div_self hD0]
  rw [hInv, map_one, one_mul]

private theorem continuous_of_constant_on_open_differences
    (T : F K -> Complex) (S : Set (F K)) (hS : IsOpen S) (h0 : Membership.mem S 0)
    (hT : forall x y : F K, Membership.mem S (x - y) -> T x = T y) :
    Continuous T := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let U := Set.preimage (fun y : F K => y - x) S
  have hU : IsOpen U := hS.preimage (continuous_id.sub continuous_const)
  have hx : Membership.mem U x := by
    change Membership.mem S (x - x)
    rw [sub_self]
    exact h0
  have hEv : Filter.EventuallyEq (nhds x) (fun _ : F K => T x) T := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hT y x hy).symm
  exact continuousAt_const.congr_of_eventuallyEq hEv.symm

/-- The finite Hecke test is locally constant on conductor congruence classes. -/
theorem continuous_heckeFiniteAdditiveTateTest (chi : UnitaryHeckeCharacter K) :
    Continuous (heckeFiniteAdditiveTateTest chi) := by
  choose d hd using exists_principal_modulus_heckeFiniteAdditiveTateTest chi
  let e := algebraMap (RingOfIntegers K) K
  have hd0 : Not (e d = 0) := (map_ne_zero_iff e (IsFractionRing.injective _ _)).mpr hd.1
  let S := heckeScaledIntegralFiniteAdeles (e d)
  exact continuous_of_constant_on_open_differences (heckeFiniteAdditiveTateTest chi)
    (S : Set (F K)) (isOpen_heckeScaledIntegralFiniteAdeles (e d) hd0) S.zero_mem hd.2

section Fourier

variable [MeasurableSpace (F K)] [BorelSpace (F K)]

/-- A nonzero Fourier coefficient requires the frequency to annihilate the translations that preserve the test. -/
theorem heckeFiniteFourierIntegral_nonzero_forces_annihilator
    (mu : Measure (F K)) [mu.IsAddHaarMeasure]
    (T : F K -> Complex)
    (d : RingOfIntegers K)
    (hT : forall a : F K, Membership.mem (heckeIntegralFiniteAdeles (K := K)) a ->
      forall z : F K, T (z + a * algebraMap K (F K) (algebraMap (RingOfIntegers K) K d)) = T z)
    (y : F K) (hy : Not (heckeFiniteFourierIntegral mu T y = 0)) :
    forall a : F K, Membership.mem (heckeIntegralFiniteAdeles (K := K)) a ->
      heckeFiniteAddChar (a * (algebraMap K (F K) (algebraMap (RingOfIntegers K) K d) * y)) = 1 := by
  intro a ha
  let c := algebraMap K (F K) (algebraMap (RingOfIntegers K) K d)
  let h := a * c
  let Freq (z : F K) : Complex := T z * (heckeFiniteAddChar (z * y) : Complex)
  let I := heckeFiniteFourierIntegral mu T y
  have hI : integral mu Freq = I := rfl
  have hShift : integral mu (fun z : F K => Freq (z + h)) = I :=
    (integral_add_right_eq_self Freq h).trans hI
  have hFactor (z : F K) :
      Freq (z + h) = (heckeFiniteAddChar (h * y) : Complex) * Freq z := by
    change T (z + a * c) * (heckeFiniteAddChar ((z + h) * y) : Complex) = _
    rw [hT a ha z, add_mul, AddChar.map_add_eq_mul]
    change T z * ((heckeFiniteAddChar (z * y) : Complex) * (heckeFiniteAddChar (h * y) : Complex)) =
      (heckeFiniteAddChar (h * y) : Complex) * (T z * (heckeFiniteAddChar (z * y) : Complex))
    ring
  have hE : (heckeFiniteAddChar (h * y) : Complex) * I = I := by
    rw [<- hI, <- integral_const_mul]
    exact (integral_congr_ae (Filter.Eventually.of_forall fun z => (hFactor z).symm)).trans hShift
  have hOne : (heckeFiniteAddChar (h * y) : Complex) = 1 := by
    have h : ((heckeFiniteAddChar (h * y) : Complex) - 1) * I = 0 := by
      rw [sub_mul, hE, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hy)
  have hChar : heckeFiniteAddChar (h * y) = 1 := Subtype.ext hOne
  change heckeFiniteAddChar (a * (c * y)) = 1
  rw [<- mul_assoc]
  exact hChar

/-- The finite Fourier dual of a Hecke test has compact support. -/
theorem exists_compactSupport_heckeFiniteFourierIntegral_TateTest
    (mu : Measure (F K)) [mu.IsAddHaarMeasure]
    (chi : UnitaryHeckeCharacter K) :
    Exists (fun S : Set (F K) => And (IsCompact S)
      (forall y : F K, Not (Membership.mem S y) ->
        heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) y = 0)) := by
  choose d hd using exists_principal_modulus_heckeFiniteAdditiveTateTest chi
  choose S hS using exists_compact_heckeFiniteChar_annihilator_cover d hd.1
  refine Exists.intro S (And.intro hS.1 ?_)
  intro y hy
  by_contra h
  apply hy
  apply hS.2 y
  apply heckeFiniteFourierIntegral_nonzero_forces_annihilator mu _ d ?_ _ h
  intro a ha z
  apply hd.2
  rw [add_sub_cancel_left]
  let e := algebraMap (RingOfIntegers K) K
  have hD : Not (e d = 0) := (map_ne_zero_iff e (IsFractionRing.injective _ _)).mpr hd.1
  apply (mem_heckeScaledIntegralFiniteAdeles_iff (e d) hD _).mpr
  intro p
  let ep := algebraMap K (p.adicCompletion K)
  have hdp := (map_ne_zero_iff ep ep.injective).mpr hD
  change Membership.mem (p.adicCompletionIntegers K) (a p * ep (e d) / ep (e d))
  have hEq : a p * ep (e d) / ep (e d) = a p := (div_eq_iff hdp).mpr rfl
  rw [hEq]
  exact ha p

omit [BorelSpace (F K)] in
/-- The finite Fourier dual has absolute value at most the additive mass of the integral finite adeles. -/
theorem norm_heckeFiniteFourierIntegral_TateTest_le
    (mu : Measure (F K)) [mu.IsAddHaarMeasure]
    (chi : UnitaryHeckeCharacter K) (y : F K) :
    norm (heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) y) <=
      mu.real (heckeIntegralFiniteAdeles (K := K) : Set (F K)) := by
  let S : Set (F K) := heckeIntegralFiniteAdeles (K := K)
  let g (z : F K) := heckeFiniteAdditiveTateTest chi z *
    (heckeFiniteAddChar (z * y) : Complex)
  have hZero (z : F K) (hz : Not (Membership.mem S z)) : g z = 0 := by
    have hz' : Not (Membership.mem (heckeIntegralFiniteAdeles (K := K)) z) := hz
    change heckeFiniteAdditiveTateTest chi z * (heckeFiniteAddChar (z * y) : Complex) = 0
    rw [heckeFiniteAdditiveTateTest, if_neg hz', zero_mul]
  have hEq : integral (mu.restrict S) g = integral mu g :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hZero
  have hS : IsCompact S := isCompact_integralFiniteAdeles
  have hG (z : F K) (_hz : Membership.mem S z) : norm (g z) <= 1 := by
    change norm (heckeFiniteAdditiveTateTest chi z * (heckeFiniteAddChar (z * y) : Complex)) <= 1
    rw [Complex.norm_mul, Circle.norm_coe, mul_one]
    exact norm_heckeFiniteAdditiveTateTest_le_one chi z
  have hI : norm (integral (mu.restrict S) g) <= 1 * mu.real S :=
    norm_setIntegral_le_of_norm_le_const hS.measure_lt_top hG
  change norm (integral mu g) <= mu.real S
  rw [<- hEq, <- one_mul (mu.real S)]
  exact hI

/-- The finite Fourier dual satisfies the same uniform theta decay bound on compact representatives. -/
theorem exists_uniform_heckeDualTateTheta_bound_on_normOne_representatives
    (mu : Measure (F K)) [mu.IsAddHaarMeasure]
    (chi : UnitaryHeckeCharacter K)
    (f : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) Complex)
    (N : Nat) (hN : (Module.finrank Int (NumberField.mixedEmbedding.integerLattice K) : Real) < (N : Real)) :
    Exists (fun S : Set (heckeNormOneIdeles K) => And (IsCompact S)
      (And (Set.image (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S = Set.univ)
        (Exists (fun D : Real => And (0 <= D)
          (forall a : heckeNormOneIdeles K, Membership.mem S a -> forall t : Real,
            And (Summable (heckeTateThetaNormOneAbsTerm f
                (fun y => heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) (-y)) a t))
              (tsum (heckeTateThetaNormOneAbsTerm f
                (fun y => heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi) (-y)) a t) <=
                D * Real.exp (-(N : Real) * (t / (Module.finrank Rat K : Real))))))))) := by
  choose V hV using exists_compactSupport_heckeFiniteFourierIntegral_TateTest mu chi
  let W := Set.image (fun y : F K => -y) V
  have hW : IsCompact W := hV.1.image continuous_neg
  have hV' (y : F K) (hy : Not (Membership.mem W y)) : Not (Membership.mem V (-y)) := by
    intro h
    apply hy
    exact Exists.intro (-y) (And.intro h (neg_neg y))
  exact exists_uniform_heckeTateTheta_bound_on_normOne_representatives f _ W hW
    (fun y hy => hV.2 (-y) (hV' y hy)) _ ENNReal.toReal_nonneg
    (fun y => norm_heckeFiniteFourierIntegral_TateTest_le mu chi (-y)) N hN

omit [BorelSpace (F K)] in
/-- The finite Fourier dual is locally constant on integral congruence classes. -/
theorem continuous_heckeFiniteFourierIntegral_TateTest
    (mu : Measure (F K)) (chi : UnitaryHeckeCharacter K) :
    Continuous (heckeFiniteFourierIntegral mu (heckeFiniteAdditiveTateTest chi)) := by
  let S := heckeIntegralFiniteAdeles (K := K)
  apply continuous_of_constant_on_open_differences _ (S : Set (F K))
    isOpen_heckeIntegralFiniteAdeles S.zero_mem
  intro y x hy
  apply integral_congr_ae
  filter_upwards with z
  change heckeFiniteAdditiveTateTest chi z * (heckeFiniteAddChar (z * y) : Complex) =
    heckeFiniteAdditiveTateTest chi z * (heckeFiniteAddChar (z * x) : Complex)
  by_cases hz : Membership.mem S z
  . have hChar := heckeFiniteAddChar_eq_one_of_integral (z * (y - x)) (finiteIntegral_mul_mem hz hy)
    have hMul : z * y = z * x + z * (y - x) := by ring
    rw [hMul, AddChar.map_add_eq_mul, hChar, mul_one]
  . have hZero : heckeFiniteAdditiveTateTest chi z = 0 := by
      change Not (Membership.mem (heckeIntegralFiniteAdeles (K := K)) z) at hz
      rw [heckeFiniteAdditiveTateTest, if_neg hz]
    rw [hZero, zero_mul, zero_mul]

end Fourier

end Robin1984.GRH
