import Robin1984.GRH.HeckeAdelePoisson
import Robin1984.GRH.HeckeConductor

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's finite test functions, local conductor congruences, and adelic Poisson summation.
- Formalization note: Extends the local Tate densities to the additive fields, expands the finite test and its idele translates through principal cosets, and proves Poisson summation for them.
- PROVENANCE-END
-/

/-!
# Finite Tate test functions

At an unramified place the additive test is the indicator of the integral
elements. At a ramified place it is the inverse local character on the
unit shell. The finite adelic product is constant on the cosets of a
nonzero principal ideal contained in the conductor ideal. The finite
test and each finite idele translate have finite coset expansions.
These give Poisson summation with the actual finite Fourier integral
for every archimedean Schwartz function.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform

variable {K : Type*} [Field K] [NumberField K]

private abbrev Local (p : HeightOneSpectrum (RingOfIntegers K)) := p.adicCompletion K
private abbrev ExponentValue := WithZero (Multiplicative Int)

private noncomputable abbrev localVal (p : HeightOneSpectrum (RingOfIntegers K)) :
    Valuation (Local p) ExponentValue := Valued.v

private def depthCut (n : Nat) : ExponentValue :=
  (Multiplicative.ofAdd (-(n : Int)) : Multiplicative Int)

private theorem depthCut_lt_one (n : Nat) (hn : 0 < n) : depthCut n < 1 := by
  change ((Multiplicative.ofAdd (-(n : Int)) : Multiplicative Int) : ExponentValue) <
    ((1 : Multiplicative Int) : ExponentValue)
  exact (@WithZero.coe_lt_coe (Multiplicative Int)
    (@instLTMultiplicative Int Int.instLTInt) (Multiplicative.ofAdd (-(n : Int))) 1).mpr
      (show -(n : Int) < 0 by exact neg_lt_zero.mpr (by exact_mod_cast hn))

private theorem depthCut_le_one (n : Nat) : depthCut n <= 1 := by
  by_cases hn : n = 0
  case pos =>
    rw [hn]
    exact le_rfl
  case neg => exact (depthCut_lt_one n (Nat.pos_of_ne_zero hn)).le

private theorem valOne_nonzero (p : HeightOneSpectrum (RingOfIntegers K))
    (x : Local p) (hx : localVal p x = 1) : Not (x = 0) := by
  intro h
  rw [h, map_zero] at hx
  exact zero_ne_one hx

/-- The local Tate density on the full additive completion. -/
noncomputable def heckeLocalAdditiveTateTest (p : HeightOneSpectrum (RingOfIntegers K))
    (chi : UnitaryHeckeCharacter K) (x : Local p) : Complex :=
  if HeckeUnramifiedAt chi p then
    if localVal p x <= 1 then 1 else 0
  else
    if h : localVal p x = 1 then
      (chi.val (localIdeleHom K p (Inv.inv (Units.mk0 x (valOne_nonzero p x h)))) : Complex)
    else 0

private theorem valuation_sub_comm (p : HeightOneSpectrum (RingOfIntegers K))
    (x y : Local p) : localVal p (y - x) = localVal p (x - y) := by
  rw [<- neg_sub x y, (localVal p).map_neg]

private theorem val_le_one_of_sub (p : HeightOneSpectrum (RingOfIntegers K))
    {x y : Local p} (hy : localVal p y <= 1) (h : localVal p (x - y) <= 1) :
    localVal p x <= 1 := by
  have hx : x = (x - y) + y := (sub_add_cancel x y).symm
  calc
    localVal p x = localVal p ((x - y) + y) := congrArg (localVal p) hx
    _ <= 1 := (localVal p).map_add_le h hy

private theorem val_eq_one_of_sub (p : HeightOneSpectrum (RingOfIntegers K))
    {x y : Local p} (hy : localVal p y = 1) (h : localVal p (x - y) < 1) :
    localVal p x = 1 := by
  refine le_antisymm (val_le_one_of_sub p hy.le h.le) ?_
  by_contra hlt
  have hx : localVal p x < 1 := lt_of_not_ge hlt
  have hsub : localVal p (y - x) < 1 := (valuation_sub_comm p x y).trans_lt h
  have he : y = (y - x) + x := (sub_add_cancel y x).symm
  have hlt : localVal p y < 1 := calc
    localVal p y = localVal p ((y - x) + x) := congrArg (localVal p) he
    _ <= max (localVal p (y - x)) (localVal p x) := (localVal p).map_add _ _
    _ < 1 := max_lt hsub hx
  exact (not_lt_of_ge hy.ge) hlt

/-- The local additive density is invariant under the conductor congruence. -/
theorem heckeLocalAdditiveTateTest_eq_of_sub_le (p : HeightOneSpectrum (RingOfIntegers K))
    (chi : UnitaryHeckeCharacter K) (x y : Local p)
    (h : localVal p (x - y) <= depthCut (heckeConductorExponent chi p)) :
    heckeLocalAdditiveTateTest p chi x = heckeLocalAdditiveTateTest p chi y := by
  let n := heckeConductorExponent chi p
  have hOpp : localVal p (y - x) <= depthCut n := (valuation_sub_comm p x y).trans_le h
  by_cases hu : HeckeUnramifiedAt chi p
  case pos =>
    have hCut := depthCut_le_one n
    have hIff : localVal p x <= 1 <-> localVal p y <= 1 :=
      Iff.intro (fun hx => val_le_one_of_sub p hx (hOpp.trans hCut))
        (fun hy => val_le_one_of_sub p hy (h.trans hCut))
    simp only [heckeLocalAdditiveTateTest, if_pos hu, hIff]
  case neg =>
    have hn : 0 < n := Nat.pos_of_ne_zero
      (fun hz => hu ((heckeConductorExponent_eq_zero_iff chi p).mp hz))
    have hCut := depthCut_lt_one n hn
    have hUpper (hx : localVal p x = 1) : localVal p y = 1 :=
      val_eq_one_of_sub p hx (hOpp.trans_lt hCut)
    have hLower (hy : localVal p y = 1) : localVal p x = 1 :=
      val_eq_one_of_sub p hy (h.trans_lt hCut)
    rw [heckeLocalAdditiveTateTest, heckeLocalAdditiveTateTest, if_neg hu, if_neg hu]
    by_cases hx : localVal p x = 1
    case pos =>
      have hy := hUpper hx
      rw [dif_pos hx, dif_pos hy]
      let a := Units.mk0 x (valOne_nonzero p x hx)
      let b := Units.mk0 y (valOne_nonzero p y hy)
      have hRatioUnit : localVal p ((a / b : Units (Local p)) : Local p) = 1 := by
        change localVal p (x / y) = 1
        rw [(localVal p).map_div, hx, hy, div_one]
      have hRatioDepth : localVal p (((a / b : Units (Local p)) : Local p) - 1) <= depthCut n := by
        change localVal p (x / y - 1) <= depthCut n
        rw [div_sub_one (valOne_nonzero p y hy), (localVal p).map_div, hy, div_one]
        exact h
      have hTrivial := heckeTrivialAtDepth_conductorExponent chi p (a / b) hRatioUnit hRatioDepth
      have hSame : chi.val (localIdeleHom K p a) = chi.val (localIdeleHom K p b) := by
        apply div_eq_one.mp
        rw [<- map_div, <- map_div]
        exact hTrivial
      apply congrArg (fun z : Circle => (z : Complex))
      change chi.val (localIdeleHom K p (Inv.inv a)) =
        chi.val (localIdeleHom K p (Inv.inv b))
      rw [map_inv, map_inv, map_inv, map_inv, hSame]
    case neg =>
      have hy : Not (localVal p y = 1) := fun hy => hx (hLower hy)
      rw [dif_neg hx, dif_neg hy]

/-- Restriction to local units gives the test used in the Euler factor integral. -/
theorem heckeLocalAdditiveTateTest_coe_unit (p : HeightOneSpectrum (RingOfIntegers K))
    (chi : UnitaryHeckeCharacter K) (a : Units (Local p)) :
    heckeLocalAdditiveTateTest p chi (a : Local p) = heckeLocalTateTest p chi a := by
  by_cases hu : HeckeUnramifiedAt chi p
  case pos =>
    have h : localVal p (a : Local p) <= 1 <-> Membership.mem (heckeLocalIntegralUnits p) a := by
      change localVal p (a : Local p) <= 1 <-> Multiplicative.toAdd (heckeLocalValueIndex p a) <= 0
      have hv := coe_heckeLocalValueIndex p a
      change (heckeLocalValueIndex p a : ExponentValue) = localVal p (a : Local p) at hv
      rw [<- hv]
      exact @WithZero.coe_le_coe (Multiplicative Int) (@instLEMultiplicative Int Int.instLEInt)
        (heckeLocalValueIndex p a) 1
    rw [heckeLocalAdditiveTateTest, heckeLocalTateTest, if_pos hu, if_pos hu]
    by_cases hv : localVal p (a : Local p) <= 1
    case pos =>
      rw [if_pos hv, Set.indicator_of_mem (h.mp hv)]
    case neg =>
      rw [if_neg hv, Set.indicator_of_notMem (fun ha => hv (h.mpr ha))]
  case neg =>
    rw [heckeLocalAdditiveTateTest, heckeLocalTateTest, if_neg hu, if_neg hu, heckeLocalRamifiedTest]
    by_cases hv : localVal p (a : Local p) = 1
    case pos =>
      have ha : Membership.mem (heckeLocalUnitShell p) a := hv
      have hUnit : Units.mk0 (a : Local p) (valOne_nonzero p (a : Local p) hv) = a :=
        Units.ext rfl
      rw [dif_pos hv, Set.indicator_of_mem ha, hUnit]
    case neg =>
      have ha : Not (Membership.mem (heckeLocalUnitShell p) a) := hv
      rw [dif_neg hv, Set.indicator_of_notMem ha]

private abbrev FiniteTateAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private theorem localVal_principal_le_of_mem (p : HeightOneSpectrum (RingOfIntegers K))
    (d : RingOfIntegers K) (n : Nat) (hd : Membership.mem (p.asIdeal ^ n) d) :
    localVal p (algebraMap K (Local p) (algebraMap (RingOfIntegers K) K d)) <= depthCut n := by
  change Valued.v ((algebraMap (RingOfIntegers K) K d : K) : Local p) <= depthCut n
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (p.intValuation_le_pow_iff_mem d n).mpr hd

/-- The finite adelic Tate test of a unitary Hecke character. -/
noncomputable def heckeFiniteAdditiveTateTest (chi : UnitaryHeckeCharacter K)
    (x : FiniteTateAdeles K) : Complex :=
  if Membership.mem (heckeIntegralFiniteAdeles (K := K)) x then
    (finite_heckeRamifiedPlaces chi).toFinset.prod (fun p => heckeLocalAdditiveTateTest p chi (x p))
  else 0

set_option maxHeartbeats 800000 in
/-- A single nonzero global integer modulus works at every ramified place. -/
theorem exists_principal_modulus_heckeFiniteAdditiveTateTest (chi : UnitaryHeckeCharacter K) :
    exists d : RingOfIntegers K, And (Not (d = 0))
      (forall x y : FiniteTateAdeles K,
        Membership.mem (heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d)) (x - y) ->
          heckeFiniteAdditiveTateTest chi x = heckeFiniteAdditiveTateTest chi y) := by
  let R := RingOfIntegers K
  let A := FiniteTateAdeles K
  let I := heckeConductorIdeal chi
  let S := (finite_heckeRamifiedPlaces chi).toFinset
  let H : AddSubgroup A := heckeIntegralFiniteAdeles
  have hI : Not (I = Bot.bot) := fun h =>
    (Nat.ne_of_gt (heckeConductorIdeal_absNorm_pos chi)) (Ideal.absNorm_eq_zero_iff.mpr h)
  choose d hd using Submodule.exists_mem_ne_zero_of_ne_bot (p := (I : Submodule R R)) hI
  refine Exists.intro d (And.intro hd.2 ?_)
  intro x y hxy
  let dd := algebraMap R K d
  let g := algebraMap K A
  let D := heckeScaledIntegralFiniteAdeles dd
  change Membership.mem D (x - y) at hxy
  choose z hz using AddSubgroup.mem_map.mp hxy
  have hzH : Membership.mem H z := hz.1
  have hDiff : x - y = z * g dd := hz.2.symm
  have hDiffH : Membership.mem H (x - y) := by
    let : MeasurableSpace A := borel A
    let : BorelSpace A := BorelSpace.mk rfl
    exact heckeScaledIntegralFiniteAdeles_le d hxy
  have hIff : Membership.mem H x <-> Membership.mem H y := by
    constructor
    case mp =>
      intro hx
      have hy := H.sub_mem hx hDiffH
      rwa [sub_sub_cancel] at hy
    case mpr =>
      intro hy
      have hx := H.add_mem hDiffH hy
      rwa [sub_add_cancel] at hx
  by_cases hx : Membership.mem H x
  case pos =>
    have hy := hIff.mp hx
    rw [heckeFiniteAdditiveTateTest, heckeFiniteAdditiveTateTest, if_pos hx, if_pos hy]
    apply Finset.prod_congr rfl
    intro p hp
    have hIp : I <= p.asIdeal ^ heckeConductorExponent chi p := by
      change S.prod (fun q => q.asIdeal ^ heckeConductorExponent chi q) <= _
      exact Ideal.prod_le_inf.trans (Finset.inf_le hp)
    have hdVal := localVal_principal_le_of_mem p d _ (hIp hd.1)
    have hzVal : localVal p (z p) <= 1 := hzH p
    have hPair : x p - y p = z p * algebraMap K (Local p) dd :=
      congrArg (fun u : A => u p) hDiff
    apply heckeLocalAdditiveTateTest_eq_of_sub_le p chi
    rw [hPair, (localVal p).map_mul]
    calc
      _ <= 1 * localVal p (algebraMap K (Local p) dd) :=
        mul_le_mul_of_nonneg_right hzVal zero_le
      _ <= _ := by rw [one_mul]; exact hdVal
  case neg =>
    have hy : Not (Membership.mem H y) := fun hy => hx (hIff.mpr hy)
    rw [heckeFiniteAdditiveTateTest, heckeFiniteAdditiveTateTest, if_neg hx, if_neg hy]

private theorem heckeIntegralFiniteAdeles_mul_mem {x y : FiniteTateAdeles K}
    (hx : Membership.mem heckeIntegralFiniteAdeles x)
    (hy : Membership.mem heckeIntegralFiniteAdeles y) :
    Membership.mem heckeIntegralFiniteAdeles (x * y) :=
  fun p => (p.adicCompletionIntegers K).mul_mem _ _ (hx p) (hy p)

private theorem exists_principal_multiple_mem_heckeIntegralFiniteAdeles (b : FiniteTateAdeles K) :
    exists j : RingOfIntegers K, And (Not (j = 0))
      (Membership.mem heckeIntegralFiniteAdeles
        (b * algebraMap K (FiniteTateAdeles K) (algebraMap (RingOfIntegers K) K j))) := by
  choose j hj using exists_finiteAdele_integral_multiple b
  exact Exists.intro j (And.intro hj.1 hj.2)

set_option maxHeartbeats 700000 in
/-- A principal rescaling of an idele translate of the finite Tate test is
supported on the integral adeles and invariant under a principal modulus. -/
private theorem exists_integral_rescaling_finiteTateTest
    (chi : UnitaryHeckeCharacter K) (b : Units (FiniteTateAdeles K)) :
    exists j : RingOfIntegers K, And (Not (j = 0))
      (exists d : RingOfIntegers K, And (Not (d = 0))
        (let V (z : FiniteTateAdeles K) := heckeFiniteAdditiveTateTest chi
              (z * algebraMap K (FiniteTateAdeles K) (Inv.inv (algebraMap (RingOfIntegers K) K j)) * (b : FiniteTateAdeles K))
         And
           (forall z : FiniteTateAdeles K, Not (Membership.mem heckeIntegralFiniteAdeles z) -> V z = 0)
           (forall z w : FiniteTateAdeles K,
             Membership.mem (heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K (d * j)))
               (z - w) -> V z = V w))) := by
  let R := RingOfIntegers K
  let g := algebraMap K (FiniteTateAdeles K)
  let r := algebraMap R K
  let H : AddSubgroup (FiniteTateAdeles K) := heckeIntegralFiniteAdeles
  choose j hj using exists_principal_multiple_mem_heckeIntegralFiniteAdeles ((b.inv : FiniteTateAdeles K))
  choose e he using exists_principal_multiple_mem_heckeIntegralFiniteAdeles (b : FiniteTateAdeles K)
  choose d hd using exists_principal_modulus_heckeFiniteAdditiveTateTest chi
  have hjK : Not (r j = 0) :=
    (map_ne_zero_iff r (FaithfulSMul.algebraMap_injective R K)).mpr hj.1
  have hInverse : Inv.inv (r j) * r j = 1 := by field_simp [hjK]
  have hScalar : g (Inv.inv (r j)) * g (r j) = 1 := by
    rw [<- map_mul, hInverse, map_one]
  let u : FiniteTateAdeles K := g (Inv.inv (r j)) * (b : FiniteTateAdeles K)
  have hUnit : u * (b.inv * g (r j)) = 1 := by
    calc
      u * (b.inv * g (r j)) = (g (Inv.inv (r j)) * g (r j)) * ((b : FiniteTateAdeles K) * b.inv) := by
        dsimp only [u]
        ac_rfl
      _ = 1 := by rw [hScalar, b.val_inv, mul_one]
  let D := (d * e) * j
  have hM : Not (d * e = 0) := mul_ne_zero hd.1 he.1
  refine Exists.intro j (And.intro hj.1 (Exists.intro (d * e) (And.intro hM (And.intro ?_ ?_))))
  . intro z hz
    have hZero : Not (Membership.mem H (z * u)) := by
      intro hzu
      have hback := heckeIntegralFiniteAdeles_mul_mem hzu hj.2
      rw [mul_assoc, hUnit, mul_one] at hback
      exact hz hback
    change heckeFiniteAdditiveTateTest chi (z * g (Inv.inv (r j)) * (b : FiniteTateAdeles K)) = 0
    rw [mul_assoc]
    exact if_neg hZero
  . intro z w hzw
    change heckeFiniteAdditiveTateTest chi (z * g (Inv.inv (r j)) * (b : FiniteTateAdeles K)) =
      heckeFiniteAdditiveTateTest chi (w * g (Inv.inv (r j)) * (b : FiniteTateAdeles K))
    rw [mul_assoc z, mul_assoc w]
    apply hd.2
    rw [<- sub_mul]
    choose v hv using AddSubgroup.mem_map.mp hzw
    refine AddSubgroup.mem_map.mpr (Exists.intro (v * ((b : FiniteTateAdeles K) * g (r e)))
      (And.intro (heckeIntegralFiniteAdeles_mul_mem hv.1 he.2) ?_))
    have hDiff : v * g (r D) = z - w := hv.2
    change v * ((b : FiniteTateAdeles K) * g (r e)) * g (r d) = (z - w) * u
    rw [<- hDiff]
    have hCancel : g (r j) * g (Inv.inv (r j)) = 1 := by rw [mul_comm, hScalar]
    symm
    calc
      v * g (r D) * u =
          (v * ((b : FiniteTateAdeles K) * g (r e)) * g (r d)) *
            (g (r j) * g (Inv.inv (r j))) := by
        dsimp only [D, u]
        rw [map_mul r, map_mul r, map_mul g, map_mul g]
        ac_rfl
      _ = _ := by rw [hCancel, mul_one]

variable [MeasurableSpace (FiniteTateAdeles K)] [BorelSpace (FiniteTateAdeles K)]

set_option maxHeartbeats 800000 in
/-- A test supported on the integral adeles and constant modulo a principal
ideal is a finite sum of indicators of its residue classes. -/
theorem exists_principalCoset_expansion_of_supported
    (value : FiniteTateAdeles K -> Complex) (d : RingOfIntegers K) (hd : Not (d = 0))
    (hsupport : forall x : FiniteTateAdeles K, Not (Membership.mem heckeIntegralFiniteAdeles x) -> value x = 0)
    (hmod : forall x y : FiniteTateAdeles K,
      Membership.mem (heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d))
        (x - y) -> value x = value y) :
    exists centers : Finset (FiniteTateAdeles K), forall x : FiniteTateAdeles K,
      value x = centers.sum (fun a =>
        value a * (heckeFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d)).indicator
          (fun _ => (1 : Complex)) x) := by
  classical
  let R := RingOfIntegers K
  let A := FiniteTateAdeles K
  let H : AddSubgroup A := heckeIntegralFiniteAdeles
  let D := heckeScaledIntegralFiniteAdeles (algebraMap R K d)
  let I : Ideal R := Ideal.span {d}
  let Q := HasQuotient.Quotient R I
  have hI : Not (I = 0) := fun h => hd (Ideal.span_singleton_eq_bot.mp h)
  let : I.toAddSubgroup.FiniteIndex := Ideal.finiteIndex hI
  let : Finite Q := inferInstanceAs (Finite (HasQuotient.Quotient R I.toAddSubgroup))
  let : Fintype Q := Fintype.ofFinite Q
  let rho (c : Q) := heckePrincipalResidueCenter d c
  let C (c : Q) := heckePrincipalResidueCoset d c
  have hParts := heckePrincipalResidueCosets_partition d hd
  have hCover : Set.iUnion C = (H : Set A) := hParts.2
  have hDisjoint : Pairwise (fun i j : Q => Disjoint (C i) (C j)) := hParts.1
  have hCenter (i : Q) : Membership.mem (C i) (rho i) :=
    Exists.intro 0 (And.intro D.zero_mem (add_zero _))
  have hInj : Function.Injective rho := by
    intro i j hij
    by_contra hne
    have hj : Membership.mem (C j) (rho i) := by rw [hij]; exact hCenter j
    exact Set.disjoint_left.mp (hDisjoint hne) (hCenter i) hj
  let emb : Function.Embedding Q A := {
    toFun := rho
    inj' := hInj }
  let centers : Finset A := Finset.univ.map emb
  refine Exists.intro centers ?_
  intro x
  dsimp only [centers]
  rw [Finset.sum_map]
  change value x = Finset.univ.sum (fun i : Q => value (rho i) *
    (C i).indicator (fun _ => (1 : Complex)) x)
  by_cases hx : Membership.mem H x
  case pos =>
    have hxU : Membership.mem (Set.iUnion C) x := by rw [hCover]; exact hx
    choose i hi using Set.mem_iUnion.mp hxU
    rw [Finset.sum_eq_single i]
    . rw [Set.indicator_of_mem hi, mul_one]
      choose z hz using hi
      have hzX : rho i + z = x := hz.2
      have hDiff : x - rho i = z := by rw [<- hzX, add_sub_cancel_left]
      apply hmod x (rho i)
      rw [hDiff]
      exact hz.1
    . intro j _ hji
      have hNo : Not (Membership.mem (C j) x) :=
        fun h => Set.disjoint_left.mp (hDisjoint hji) h hi
      rw [Set.indicator_of_notMem hNo, mul_zero]
    . intro h
      exact False.elim (h (Finset.mem_univ i))
  case neg =>
    have hZero : value x = 0 := hsupport x hx
    rw [hZero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hNo : Not (Membership.mem (C i) x) := by
      intro h
      have hU : Membership.mem (Set.iUnion C) x := Set.mem_iUnion.mpr (Exists.intro i h)
      rw [hCover] at hU
      exact hx hU
    rw [Set.indicator_of_notMem hNo, mul_zero]

/-- The finite Tate test is a finite linear combination of principal coset indicators. -/
theorem heckeFiniteAdditiveTateTest_eq_sum_principalCosets (chi : UnitaryHeckeCharacter K) :
    exists d : RingOfIntegers K, And (Not (d = 0))
      (exists centers : Finset (FiniteTateAdeles K),
        forall x : FiniteTateAdeles K,
          heckeFiniteAdditiveTateTest chi x = centers.sum (fun a =>
            heckeFiniteAdditiveTateTest chi a *
              (heckeFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d)).indicator
                (fun _ => (1 : Complex)) x)) := by
  choose d hd using exists_principal_modulus_heckeFiniteAdditiveTateTest chi
  have hsupport (x : FiniteTateAdeles K)
      (hx : Not (Membership.mem heckeIntegralFiniteAdeles x)) :
      heckeFiniteAdditiveTateTest chi x = 0 := by
    rw [heckeFiniteAdditiveTateTest, if_neg hx]
  exact Exists.intro d (And.intro hd.1
    (exists_principalCoset_expansion_of_supported (heckeFiniteAdditiveTateTest chi)
      d hd.1 hsupport hd.2))

set_option maxHeartbeats 1000000 in
/-- Each finite idele translate of the finite Tate test is a finite sum of
principal coset indicators. -/
theorem heckeFiniteAdditiveTateTest_translate_eq_sum_principalCosets
    (chi : UnitaryHeckeCharacter K) (b : Units (FiniteTateAdeles K)) :
    exists d : RingOfIntegers K, And (Not (d = 0))
      (exists centers : Finset (FiniteTateAdeles K), forall x : FiniteTateAdeles K,
        heckeFiniteAdditiveTateTest chi (x * (b : FiniteTateAdeles K)) =
          centers.sum (fun a =>
            heckeFiniteAdditiveTateTest chi (a * (b : FiniteTateAdeles K)) *
              (heckeFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d)).indicator
                (fun _ => (1 : Complex)) x)) := by
  classical
  let R := RingOfIntegers K
  let r := algebraMap R K
  let g := algebraMap K (FiniteTateAdeles K)
  let C (a : FiniteTateAdeles K) (m : R) := heckeFiniteAdelePrincipalCoset a (r m)
  choose j hj using exists_integral_rescaling_finiteTateTest chi b
  choose d hd using hj.2
  let c := g (r j)
  let ci := g (Inv.inv (r j))
  let V (z : FiniteTateAdeles K) := heckeFiniteAdditiveTateTest chi (z * ci * (b : FiniteTateAdeles K))
  have hjK : Not (r j = 0) :=
    (map_ne_zero_iff r (FaithfulSMul.algebraMap_injective R K)).mpr hj.1
  have hInverse : r j * Inv.inv (r j) = 1 := by field_simp [hjK]
  have hcc : c * ci = 1 := by
    change g (r j) * g (Inv.inv (r j)) = 1
    rw [<- map_mul, hInverse, map_one]
  have hci : ci * c = 1 := by rw [mul_comm, hcc]
  have hm : Not (d * j = 0) := mul_ne_zero hd.1 hj.1
  choose centers hCenters using
    exists_principalCoset_expansion_of_supported V (d * j) hm hd.2.1 hd.2.2
  have hProduct : forall z : FiniteTateAdeles K, z * g (r (d * j)) = z * g (r d) * c := by
    intro z
    change z * g (r (d * j)) = z * g (r d) * g (r j)
    rw [map_mul r, map_mul g, mul_assoc]
  have hCoset (a x : FiniteTateAdeles K) :
      Membership.mem (C a (d * j)) (x * c) <-> Membership.mem (C (a * ci) d) x := by
    constructor
    . intro hx
      choose y hy using hx
      choose z hz using AddSubgroup.mem_map.mp hy.1
      have hzY : z * g (r (d * j)) = y := hz.2
      have hyA : a + y = x * c := hy.2
      refine Exists.intro (z * g (r d))
        (And.intro (AddSubgroup.mem_map.mpr (Exists.intro z (And.intro hz.1 rfl))) ?_)
      have hScaled := congrArg (fun t : FiniteTateAdeles K => t * ci) hyA
      rwa [<- hzY, hProduct, add_mul, mul_assoc (z * g (r d)), mul_assoc x, hcc,
        mul_one, mul_one] at hScaled
    . intro hx
      choose y hy using hx
      choose z hz using AddSubgroup.mem_map.mp hy.1
      have hzY : z * g (r d) = y := hz.2
      have hyA : a * ci + y = x := hy.2
      refine Exists.intro (z * g (r (d * j)))
        (And.intro (AddSubgroup.mem_map.mpr (Exists.intro z (And.intro hz.1 rfl))) ?_)
      have hScaled := congrArg (fun t : FiniteTateAdeles K => t * c) hyA
      rwa [<- hzY, add_mul, mul_assoc a, hci, mul_one, <- hProduct] at hScaled
  let emb : Function.Embedding (FiniteTateAdeles K) (FiniteTateAdeles K) := {
    toFun := fun a => a * ci
    inj' := by
      intro a a' h
      change a * ci = a' * ci at h
      have h' := congrArg (fun t : FiniteTateAdeles K => t * c) h
      simpa only [mul_assoc, hci, mul_one] using h' }
  refine Exists.intro d (And.intro hd.1 (Exists.intro (centers.map emb) ?_))
  intro x
  rw [Finset.sum_map]
  have hv : V (x * c) = heckeFiniteAdditiveTateTest chi (x * (b : FiniteTateAdeles K)) := by
    change heckeFiniteAdditiveTateTest chi (x * c * ci * (b : FiniteTateAdeles K)) = _
    rw [mul_assoc x c ci, hcc, mul_one]
  rw [<- hv, hCenters]
  apply Finset.sum_congr rfl
  intro a ha
  change V a * (C a (d * j)).indicator (fun _ => (1 : Complex)) (x * c) =
    V a * (C (a * ci) d).indicator (fun _ => (1 : Complex)) x
  congr 1
  by_cases hx : Membership.mem (C a (d * j)) (x * c)
  . rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hCoset a x).mp hx)]
  . rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h => hx ((hCoset a x).mpr h))]

omit [MeasurableSpace (FiniteTateAdeles K)] [BorelSpace (FiniteTateAdeles K)] in
private theorem isOpen_heckeFiniteAdelePrincipalCoset (a : FiniteTateAdeles K) (d : K) (hd : Not (d = 0)) :
    IsOpen (heckeFiniteAdelePrincipalCoset a d) :=
  (Homeomorph.addLeft a).isOpenMap _ (isOpen_heckeScaledIntegralFiniteAdeles d hd)

omit [MeasurableSpace (FiniteTateAdeles K)] [BorelSpace (FiniteTateAdeles K)] in
private theorem continuous_heckeFiniteAdelePrincipalChar_coe (t : K) :
    Continuous (fun z : FiniteTateAdeles K => (heckeFiniteAdelePrincipalChar t z : Complex)) := by
  let F (z : FiniteTateAdeles K) : AdeleRing (RingOfIntegers K) K :=
    Prod.mk 0 (z * algebraMap K (FiniteTateAdeles K) t)
  have hF : Continuous F := continuous_const.prodMk (continuous_id.mul continuous_const)
  change Continuous (fun z : FiniteTateAdeles K => (heckeAdeleAddChar (F z) : Complex))
  exact continuous_subtype_val.comp ((continuous_heckeAdeleAddChar (K := K)).comp hF)

private theorem integrableOn_heckeFiniteAdelePrincipalChar_coset
    (a : FiniteTateAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0)) (t : K) :
    IntegrableOn (fun z : FiniteTateAdeles K => (heckeFiniteAdelePrincipalChar t z : Complex))
      (heckeFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d))
      heckeFiniteAdeleHaar := by
  let R := RingOfIntegers K
  let dd := algebraMap R K d
  let D := heckeScaledIntegralFiniteAdeles dd
  let C := heckeFiniteAdelePrincipalCoset a dd
  let mu : Measure (FiniteTateAdeles K) := heckeFiniteAdeleHaar
  let n : ENNReal := Ideal.absNorm (Ideal.span ({d} : Set R))
  let : Measure.IsAddLeftInvariant mu := heckeFiniteAdeleHaar_isAddLeftInvariant
  have hd' : Not (dd = 0) :=
    (map_ne_zero_iff (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)).mpr hd
  have hC : MeasurableSet C := (isOpen_heckeFiniteAdelePrincipalCoset a dd hd').measurableSet
  have hMeasure : mu C = mu (D : Set (FiniteTateAdeles K)) := by
    have hp := (measurePreserving_add_left mu a).measure_preimage hC.nullMeasurableSet
    have hPre : Set.preimage (fun z : FiniteTateAdeles K => a + z) C = (D : Set (FiniteTateAdeles K)) :=
      Set.preimage_image_eq _ (fun _ _ h => add_left_cancel h)
    rw [hPre] at hp
    exact hp.symm
  have hM : n * mu (D : Set (FiniteTateAdeles K)) = 1 :=
    heckeFiniteAdeleHaar_scaledIntegral_mass d hd
  have hn : Not (n = 0) := by
    intro h
    rw [h, zero_mul] at hM
    exact zero_ne_one hM
  have hTop : Not (mu (D : Set (FiniteTateAdeles K)) = Top.top) := by
    intro h
    rw [h, ENNReal.mul_top hn] at hM
    exact (ne_of_gt (show (1 : ENNReal) < Top.top by simp)) hM
  let : IsFiniteMeasure (mu.restrict C) := by
    constructor
    rw [Measure.restrict_apply_univ, hMeasure]
    exact lt_top_iff_ne_top.mpr hTop
  change Integrable (fun z : FiniteTateAdeles K => (heckeFiniteAdelePrincipalChar t z : Complex)) (mu.restrict C)
  exact (integrable_const (1 : Real)).mono'
    (continuous_heckeFiniteAdelePrincipalChar_coe t).aestronglyMeasurable
    (ae_of_all _ (fun z => (Circle.norm_coe (heckeFiniteAdelePrincipalChar t z)).le))

private theorem finiteTateIntegral_eq_sum
    (value : FiniteTateAdeles K -> Complex)
    (d : RingOfIntegers K) (hd : Not (d = 0)) (centers : Finset (FiniteTateAdeles K))
    (hValue : forall z : FiniteTateAdeles K,
      value z = centers.sum (fun a => value a *
        (heckeFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d)).indicator
          (fun _ => (1 : Complex)) z))
    (t : K) :
    integral heckeFiniteAdeleHaar (fun z : FiniteTateAdeles K =>
      value z * (heckeFiniteAdelePrincipalChar t z : Complex)) =
      centers.sum (fun a =>
        value a * integral (heckeFiniteAdeleHaar.restrict
          (heckeFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d)))
          (fun z => (heckeFiniteAdelePrincipalChar t z : Complex))) := by
  let A := FiniteTateAdeles K
  let dd := algebraMap (RingOfIntegers K) K d
  let C (a : A) := heckeFiniteAdelePrincipalCoset a dd
  let psi (z : A) := (heckeFiniteAdelePrincipalChar t z : Complex)
  let G (a z : A) := value a * (C a).indicator psi z
  let mu : Measure A := heckeFiniteAdeleHaar
  have hd' : Not (dd = 0) :=
    (map_ne_zero_iff (algebraMap (RingOfIntegers K) K)
      (FaithfulSMul.algebraMap_injective (RingOfIntegers K) K)).mpr hd
  have hMeas (a : A) : MeasurableSet (C a) :=
    (isOpen_heckeFiniteAdelePrincipalCoset a dd hd').measurableSet
  have hInt (a : A) (_ : Membership.mem centers a) : Integrable (G a) mu := by
    have h := (integrable_indicator_iff (hMeas a)).mpr
      (integrableOn_heckeFiniteAdelePrincipalChar_coset a d hd t)
    exact h.const_mul (value a)
  have hPoint (z : A) : value z * psi z = centers.sum (fun a => G a z) := by
    rw [hValue z, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    change value a * (C a).indicator (fun _ => (1 : Complex)) z * psi z = G a z
    dsimp only [G]
    by_cases ha : Membership.mem (C a) z
    case pos => simp only [Set.indicator_of_mem ha, mul_one]
    case neg => simp only [Set.indicator_of_notMem ha, mul_zero, zero_mul]
  calc
    integral mu (fun z => value z * psi z) = integral mu (fun z => centers.sum (fun a => G a z)) :=
      integral_congr_ae (ae_of_all _ hPoint)
    _ = centers.sum (fun a => integral mu (G a)) := integral_finsetSum centers hInt
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [G]
      rw [integral_const_mul, integral_indicator (hMeas a)]

set_option maxHeartbeats 2000000 in
private theorem tsum_finiteTateTest_eq_fourierIntegral_of_expansion
    (value : FiniteTateAdeles K -> Complex)
    (d : RingOfIntegers K) (hd : Not (d = 0)) (centers : Finset (FiniteTateAdeles K))
    (hCenter : forall x : FiniteTateAdeles K,
      value x = centers.sum (fun a => value a *
        (heckeFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d)).indicator
          (fun _ => (1 : Complex)) x))
    (f : SchwartzMap (DedekindZeta.Theta.minkowskiSpace K) Complex) :
    tsum (fun x : K => f (DedekindZeta.Theta.eEmb K x) *
        value (algebraMap K (FiniteTateAdeles K) x)) =
      tsum (fun t : K =>
        let y := DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t)
        Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
          FourierTransform.fourier (f : DedekindZeta.Theta.minkowskiSpace K -> Complex) y *
          integral heckeFiniteAdeleHaar (fun z : FiniteTateAdeles K =>
            value z * (heckeFiniteAdelePrincipalChar (-t) z : Complex))) := by
  let A := FiniteTateAdeles K
  let V := DedekindZeta.Theta.minkowskiSpace K
  let g := algebraMap K A
  let F (a : A) : SchwartzMap V Complex := HSMul.hSMul (value a) f
  have hPr (x : K) :
      f (DedekindZeta.Theta.eEmb K x) * value (g x) =
        centers.sum (fun a => heckeAdeleRectanglePrincipalValue a d (F a) x) := by
    rw [show value (g x) = _ from hCenter (g x), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [heckeAdeleRectanglePrincipalValue, F, smul_apply, smul_eq_mul]
    ring
  have hFourier (a : A) (y : V) :
      FourierTransform.fourier (F a : V -> Complex) y =
        value a * FourierTransform.fourier (f : V -> Complex) y := by
    change (SchwartzMap.fourierTransformCLM Complex (F a)) y =
      value a * (SchwartzMap.fourierTransformCLM Complex f) y
    dsimp only [F]
    rw [map_smul, smul_apply, smul_eq_mul]
  have hFr (t : K) :
      centers.sum (fun a => heckeAdeleRectangleFourierIntegral a d (F a) t) =
        let y := DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t)
        Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
          FourierTransform.fourier (f : V -> Complex) y *
          integral heckeFiniteAdeleHaar (fun z : A =>
            value z * (heckeFiniteAdelePrincipalChar (-t) z : Complex)) := by
    dsimp only
    rw [finiteTateIntegral_eq_sum value d hd centers hCenter (-t), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [heckeAdeleRectangleFourierIntegral]
    rw [hFourier]
    ring
  refine (tsum_congr hPr).trans ?_
  refine (tsum_heckeAdeleFiniteRectangles_eq_fourierIntegral centers (fun a => a)
    (fun _ => d) (fun _ _ => hd) F).trans ?_
  exact tsum_congr hFr

/-- Poisson summation for the finite Tate test and an archimedean Schwartz function. -/
theorem tsum_heckeFiniteAdditiveTateTest_eq_fourierIntegral
    (chi : UnitaryHeckeCharacter K)
    (f : SchwartzMap (DedekindZeta.Theta.minkowskiSpace K) Complex) :
    tsum (fun x : K => f (DedekindZeta.Theta.eEmb K x) *
        heckeFiniteAdditiveTateTest chi (algebraMap K (FiniteTateAdeles K) x)) =
      tsum (fun t : K =>
        let y := DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t)
        Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
          FourierTransform.fourier (f : DedekindZeta.Theta.minkowskiSpace K -> Complex) y *
          integral heckeFiniteAdeleHaar (fun z : FiniteTateAdeles K =>
            heckeFiniteAdditiveTateTest chi z * (heckeFiniteAdelePrincipalChar (-t) z : Complex))) := by
  choose d hd using heckeFiniteAdditiveTateTest_eq_sum_principalCosets chi
  choose centers hCenter using hd.2
  exact tsum_finiteTateTest_eq_fourierIntegral_of_expansion
    (heckeFiniteAdditiveTateTest chi) d hd.1 centers hCenter f

/-- Poisson summation for any finite idele translate of the finite Tate test
and any archimedean Schwartz function. -/
theorem tsum_heckeFiniteAdditiveTateTest_translate_eq_fourierIntegral
    (chi : UnitaryHeckeCharacter K) (b : Units (FiniteTateAdeles K))
    (f : SchwartzMap (DedekindZeta.Theta.minkowskiSpace K) Complex) :
    tsum (fun x : K => f (DedekindZeta.Theta.eEmb K x) *
        heckeFiniteAdditiveTateTest chi (algebraMap K (FiniteTateAdeles K) x * (b : FiniteTateAdeles K))) =
      tsum (fun t : K =>
        let y := DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t)
        Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
          FourierTransform.fourier (f : DedekindZeta.Theta.minkowskiSpace K -> Complex) y *
          integral heckeFiniteAdeleHaar (fun z : FiniteTateAdeles K =>
            heckeFiniteAdditiveTateTest chi (z * (b : FiniteTateAdeles K)) * (heckeFiniteAdelePrincipalChar (-t) z : Complex))) := by
  choose d hd using heckeFiniteAdditiveTateTest_translate_eq_sum_principalCosets chi b
  choose centers hCenter using hd.2
  exact tsum_finiteTateTest_eq_fourierIntegral_of_expansion
    (fun z => heckeFiniteAdditiveTateTest chi (z * (b : FiniteTateAdeles K)))
    d hd.1 centers hCenter f

end Robin1984.GRH
