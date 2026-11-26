import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Robin1984.GRH.HeckeFiniteHaarDilation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The finite idele description of the ideal class group and normalized valuations in a number field.
- Formalization note: Constructs the surjective ideal homomorphism and proves the compactness of its integral unit kernel.
- PROVENANCE-END
-/

/-!
# Finite ideles and fractional ideal classes

The finite idele homomorphism to nonzero fractional ideals is surjective. Its
compact kernel is the group of integral finite units. Taking the ideal class
gives the relation between finite idele representatives used in norm-one
idele class compactness.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev F (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev Frac (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K

/-- The normalized valuation exponent of a finite idele at a finite place. -/
noncomputable def heckeFiniteIdeleExponent (b : Units (F K))
    (p : HeightOneSpectrum (RingOfIntegers K)) : Int :=
  -(Multiplicative.toAdd (heckeLocalValueIndex p (heckeFiniteIdeleComponent p b)))

private theorem heckeFiniteIdeleExponent_one (p : HeightOneSpectrum (RingOfIntegers K)) :
    heckeFiniteIdeleExponent (1 : Units (F K)) p = 0 := by
  rw [heckeFiniteIdeleExponent, map_one, map_one]
  rfl

private theorem heckeFiniteIdeleExponent_mul (a b : Units (F K))
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    heckeFiniteIdeleExponent (a * b) p =
      heckeFiniteIdeleExponent a p + heckeFiniteIdeleExponent b p := by
  simp only [heckeFiniteIdeleExponent, map_mul]
  change -(Multiplicative.toAdd (heckeLocalValueIndex p (heckeFiniteIdeleComponent p a)) +
    Multiplicative.toAdd (heckeLocalValueIndex p (heckeFiniteIdeleComponent p b))) = _
  exact neg_add _ _

private theorem eventually_zero_heckeFiniteIdeleExponent (b : Units (F K)) :
    Filter.Eventually (fun p => heckeFiniteIdeleExponent b p = 0) Filter.cofinite := by
  have h := (FiniteAdeleRing.isUnit_iff.mp b.isUnit).2
  apply h.mono
  intro p hp
  have hp' : heckeLocalValueIndex p (heckeFiniteIdeleComponent p b) = 1 := by
    apply WithZero.coe_inj.mp
    rw [coe_heckeLocalValueIndex]
    exact hp
  rw [heckeFiniteIdeleExponent, hp']
  rfl

/-- The fractional ideal whose exponents are the local exponents of the finite idele. -/
noncomputable def heckeFiniteIdeleFractionalIdeal (b : Units (F K)) : Frac K :=
  finprod (fun p : HeightOneSpectrum (RingOfIntegers K) =>
    (p.asIdeal : Frac K) ^ (heckeFiniteIdeleExponent b p))

/-- The prime ideal exponent in the ideal associated with a finite idele. -/
theorem count_heckeFiniteIdeleFractionalIdeal (b : Units (F K))
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    FractionalIdeal.count K p (heckeFiniteIdeleFractionalIdeal b) =
      heckeFiniteIdeleExponent b p :=
  FractionalIdeal.count_finprod K p (heckeFiniteIdeleExponent b)
    (eventually_zero_heckeFiniteIdeleExponent b)

/-- A finite idele determines a nonzero fractional ideal. -/
theorem heckeFiniteIdeleFractionalIdeal_ne_zero (b : Units (F K)) :
    Not (heckeFiniteIdeleFractionalIdeal b = 0) := by
  let E := fun p : HeightOneSpectrum (RingOfIntegers K) => heckeFiniteIdeleExponent b p
  have hF : Set.Finite (Set.ofPred (fun p => Not (E p = 0))) :=
    Filter.eventually_cofinite.mp (eventually_zero_heckeFiniteIdeleExponent b)
  have hSub : Set.Subset
      (Function.mulSupport (fun p => (HeightOneSpectrum.asIdeal p : Frac K) ^ E p))
      (Set.ofPred (fun p => Not (E p = 0))) := by
    intro p hp h0
    apply hp
    change (p.asIdeal : Frac K) ^ E p = 1
    rw [h0, zpow_zero]
  change Not (finprod (fun p => (HeightOneSpectrum.asIdeal p : Frac K) ^ E p) = 0)
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hSub hF]
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot)

private theorem frac_eq_of_counts {I J : Frac K} (hI : Not (I = 0)) (hJ : Not (J = 0))
    (h : forall p : HeightOneSpectrum (RingOfIntegers K),
      FractionalIdeal.count K p I = FractionalIdeal.count K p J) : I = J := by
  rw [<- FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    <- FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  apply finprod_congr
  intro p
  rw [h p]

/-- The homomorphism from finite ideles to nonzero fractional ideals. -/
noncomputable def heckeFiniteIdeleIdealHom :
    MonoidHom (Units (F K)) (Units (Frac K)) where
  toFun b := Units.mk0 (heckeFiniteIdeleFractionalIdeal b) (heckeFiniteIdeleFractionalIdeal_ne_zero b)
  map_one' := by
    apply Units.ext
    change heckeFiniteIdeleFractionalIdeal (1 : Units (F K)) = 1
    apply frac_eq_of_counts (heckeFiniteIdeleFractionalIdeal_ne_zero _)
      (show Not ((1 : Frac K) = 0) from one_ne_zero)
    intro p
    rw [count_heckeFiniteIdeleFractionalIdeal, heckeFiniteIdeleExponent_one,
      FractionalIdeal.count_one]
  map_mul' a b := by
    apply Units.ext
    change heckeFiniteIdeleFractionalIdeal (a * b) =
      heckeFiniteIdeleFractionalIdeal a * heckeFiniteIdeleFractionalIdeal b
    have ha := heckeFiniteIdeleFractionalIdeal_ne_zero a
    have hb := heckeFiniteIdeleFractionalIdeal_ne_zero b
    apply frac_eq_of_counts (heckeFiniteIdeleFractionalIdeal_ne_zero _) (mul_ne_zero ha hb)
    intro p
    rw [FractionalIdeal.count_mul K p ha hb, count_heckeFiniteIdeleFractionalIdeal,
      count_heckeFiniteIdeleFractionalIdeal, count_heckeFiniteIdeleFractionalIdeal,
      heckeFiniteIdeleExponent_mul]


private theorem count_heckeFiniteIdele_principal_integral
    (u : Units K) (a : RingOfIntegers K) (hu : u.val = algebraMap (RingOfIntegers K) K a)
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    FractionalIdeal.count K p (heckeFiniteIdeleFractionalIdeal
      (FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K u)) =
      FractionalIdeal.count K p ((Ideal.span (Set.singleton a) :
        Ideal (RingOfIntegers K)) : Frac K) := by
  have ha : Not (a = 0) := by
    intro ha
    apply u.ne_zero
    rw [hu, ha, map_zero]
  have hj : Not (Ideal.span (Set.singleton a) = (0 : Ideal (RingOfIntegers K))) := by
    intro hj
    exact ha (Ideal.span_singleton_eq_bot.mp hj)
  rw [count_heckeFiniteIdeleFractionalIdeal]
  let v := heckeLocalValueIndex p
    (heckeFiniteIdeleComponent p (FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K u))
  let n := FractionalIdeal.count K p ((Ideal.span (Set.singleton a) :
      Ideal (RingOfIntegers K)) : Frac K)
  have hv : (v : WithZero (Multiplicative Int)) = WithZero.exp (-n) := by
    dsimp only [v]
    rw [coe_heckeLocalValueIndex]
    change Valued.v (u.val : p.adicCompletion K) = _
    rw [hu, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg p ha]
    exact congrArg (fun m : Int => WithZero.exp (-m))
      (FractionalIdeal.count_coe K p hj).symm
  have h : v = Multiplicative.ofAdd (-n) := WithZero.coe_inj.mp hv
  change -(Multiplicative.toAdd v) = n
  rw [h]
  exact neg_neg _

private theorem heckeFiniteIdeleIdealHom_principal_integral
    (u : Units K) (a : RingOfIntegers K) (hu : u.val = algebraMap (RingOfIntegers K) K a) :
    heckeFiniteIdeleIdealHom (FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K u) =
      toPrincipalIdeal (RingOfIntegers K) K u := by
  apply Units.ext
  have hP : Not ((toPrincipalIdeal (RingOfIntegers K) K u).val = 0) :=
    (toPrincipalIdeal (RingOfIntegers K) K u).ne_zero
  change heckeFiniteIdeleFractionalIdeal (FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K u) =
    (toPrincipalIdeal (RingOfIntegers K) K u).val
  apply frac_eq_of_counts (heckeFiniteIdeleFractionalIdeal_ne_zero _) hP
  intro p
  rw [coe_toPrincipalIdeal, hu, <- FractionalIdeal.coeIdeal_span_singleton]
  exact count_heckeFiniteIdele_principal_integral u a hu p

/-- The ideal associated with a principal finite idele is the corresponding principal ideal. -/
theorem heckeFiniteIdeleIdealHom_principal (u : Units K) :
    heckeFiniteIdeleIdealHom (FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K u) =
      toPrincipalIdeal (RingOfIntegers K) K u := by
  let R := RingOfIntegers K
  let A := (heckeFiniteIdeleIdealHom (K := K)).comp (FiniteAdeleRing.unitEmbedding R K)
  let B := toPrincipalIdeal R K
  choose q hq using IsLocalization.surj (nonZeroDivisors R) u.val
  have hD : Not (algebraMap R K (q.2 : R) = 0) := by
    intro h
    apply mem_nonZeroDivisors_iff_ne_zero.mp q.2.property
    apply IsFractionRing.injective R K
    rw [h, map_zero]
  let d := Units.mk0 (algebraMap R K (q.2 : R)) hD
  have hd : A d = B d := heckeFiniteIdeleIdealHom_principal_integral d q.2 rfl
  have hn : A (u * d) = B (u * d) :=
    heckeFiniteIdeleIdealHom_principal_integral (u * d) q.1 hq
  change A u = B u
  apply mul_right_cancel (b := B d)
  calc
    A u * B d = A u * A d := by rw [hd]
    _ = A (u * d) := (map_mul A u d).symm
    _ = B (u * d) := hn
    _ = B u * B d := map_mul B u d


/-- Every nonzero fractional ideal has a finite idele representative. -/
theorem surjective_heckeFiniteIdeleIdealHom :
    Function.Surjective (heckeFiniteIdeleIdealHom (K := K)) := by
  classical
  intro I
  let c := fun p : HeightOneSpectrum (RingOfIntegers K) => FractionalIdeal.count K p I.val
  have hS : Set.Finite (Set.ofPred (fun p => Not (c p = 0))) :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I.val)
  let s := hS.toFinset
  have hLocal (p : HeightOneSpectrum (RingOfIntegers K)) :
      Exists (fun a : Units (p.adicCompletion K) => Valued.v a.val = WithZero.exp (-(c p))) := by
    choose v hv using HeightOneSpectrum.valuedAdicCompletion_surjective K p (WithZero.exp (-(c p)))
    have hv0 : Not (v = 0) := by
      intro h
      rw [h, map_zero] at hv
      exact WithZero.coe_ne_zero hv.symm
    exact Exists.intro (Units.mk0 v hv0) hv
  choose u hu using hLocal
  let a := s.prod (fun p => heckeFiniteLocalIdele p (u p))
  have hIndex (p : HeightOneSpectrum (RingOfIntegers K)) :
      heckeLocalValueIndex p (u p) = Multiplicative.ofAdd (-(c p)) := by
    apply WithZero.coe_inj.mp
    rw [coe_heckeLocalValueIndex]
    exact hu p
  have hAt (p : HeightOneSpectrum (RingOfIntegers K)) (hp : Membership.mem s p) :
      heckeFiniteIdeleComponent p a = u p := by
    change heckeFiniteIdeleComponent p (s.prod (fun q => heckeFiniteLocalIdele q (u q))) = u p
    rw [map_prod, Finset.prod_eq_single_of_mem p hp]
    . apply Units.ext
      exact heckeFiniteLocalIdele_at p (u p)
    . intro q _ hq
      apply Units.ext
      exact heckeFiniteLocalIdele_away q p (Ne.symm hq) (u q)
  have hAway (p : HeightOneSpectrum (RingOfIntegers K)) (hp : Not (Membership.mem s p)) :
      heckeFiniteIdeleComponent p a = 1 := by
    change heckeFiniteIdeleComponent p (s.prod (fun q => heckeFiniteLocalIdele q (u q))) = 1
    rw [map_prod]
    apply Finset.prod_eq_one
    intro q hq
    have hpq : Not (p = q) := fun h => hp (by rw [h]; exact hq)
    apply Units.ext
    exact heckeFiniteLocalIdele_away q p hpq (u q)
  refine Exists.intro a ?_
  apply Units.ext
  change heckeFiniteIdeleFractionalIdeal a = I.val
  apply frac_eq_of_counts (heckeFiniteIdeleFractionalIdeal_ne_zero _) I.ne_zero
  intro p
  rw [count_heckeFiniteIdeleFractionalIdeal]
  change heckeFiniteIdeleExponent a p = c p
  by_cases hp : Membership.mem s p
  . rw [heckeFiniteIdeleExponent, hAt p hp, hIndex]
    exact neg_neg _
  . have hz : c p = 0 := by
      by_contra h
      exact hp (hS.mem_toFinset.mpr h)
    rw [heckeFiniteIdeleExponent, hAway p hp, map_one, hz]
    rfl

private noncomputable def heckeIntegralFiniteAdeleSubmonoid : Submonoid (F K) where
  carrier := (heckeIntegralFiniteAdeles (K := K)).carrier
  one_mem' := by
    change forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K) ((1 : F K) p)
    intro p
    exact (p.adicCompletionIntegers K).one_mem
  mul_mem' := by
    intro a b ha hb
    change forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K) ((a * b) p)
    intro p
    exact (p.adicCompletionIntegers K).mul_mem _ _ (ha p) (hb p)

/-- The compact subgroup of finite ideles that are units at every finite place. -/
noncomputable def heckeIntegralFiniteUnitGroup : Subgroup (Units (F K)) :=
  (heckeIntegralFiniteAdeleSubmonoid (K := K)).units

/-- Membership in the integral unit subgroup can be tested on the value and inverse. -/
theorem mem_heckeIntegralFiniteUnitGroup (b : Units (F K)) :
    Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) b <->
      And (Membership.mem (heckeIntegralFiniteAdeles (K := K)) b.val)
        (Membership.mem (heckeIntegralFiniteAdeles (K := K)) b.inv) :=
  Iff.rfl

/-- The subgroup of integral finite units is compact. -/
theorem isCompact_heckeIntegralFiniteUnitGroup :
    IsCompact (heckeIntegralFiniteUnitGroup (K := K)).carrier := by
  let : T2Space (F K) := by
    let projection (a : F K) (p : HeightOneSpectrum (RingOfIntegers K)) := a p
    have hInj : Function.Injective projection := DFunLike.coe_injective
    have hCont : Continuous projection := continuous_pi (fun p =>
      RestrictedProduct.continuous_eval p)
    exact T2Space.of_injective_continuous hInj hCont
  apply Submonoid.units_isCompact
  exact isCompact_integralFiniteAdeles

/-- Integral finite units have finite idelic norm one. -/
theorem heckeFiniteIdeleNorm_eq_one_of_integralUnit
    [MeasurableSpace (F K)] [BorelSpace (F K)]
    (b : Units (F K)) (hb : Membership.mem heckeIntegralFiniteUnitGroup b) :
    heckeFiniteIdeleNorm b = 1 := by
  have h := (mem_heckeIntegralFiniteUnitGroup b).mp hb
  rw [<- heckeFiniteAdditiveModulus_eq_ideleNorm b,
    heckeFiniteAdditiveModulus_eq_one_of_integral b h.1 h.2]
  rfl

private theorem heckeFiniteIdeleExponent_eq_zero_iff (b : Units (F K))
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    heckeFiniteIdeleExponent b p = 0 <-> Valued.v (b.val p) = 1 := by
  let z := heckeLocalValueIndex p (heckeFiniteIdeleComponent p b)
  have hz : (z : WithZero (Multiplicative Int)) = Valued.v (b.val p) :=
    coe_heckeLocalValueIndex p (heckeFiniteIdeleComponent p b)
  have h1 : z = 1 <-> Valued.v (b.val p) = 1 := by
    rw [<- hz]
    exact WithZero.coe_inj.symm
  change -(Multiplicative.toAdd z) = 0 <-> _
  rw [neg_eq_zero, <- h1]
  exact Iff.intro (fun h => congrArg Multiplicative.ofAdd h)
    (fun h => congrArg Multiplicative.toAdd h)

/-- Integral finite units are characterized by trivial valuation at every place. -/
theorem mem_heckeIntegralFiniteUnitGroup_iff_valued_one (b : Units (F K)) :
    Membership.mem heckeIntegralFiniteUnitGroup b <->
      forall p : HeightOneSpectrum (RingOfIntegers K), Valued.v (b.val p) = 1 := by
  rw [mem_heckeIntegralFiniteUnitGroup]
  constructor
  . intro h p
    exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (K := K) (v := p) (a := heckeFiniteIdeleComponent p b)).mp (And.intro (h.1 p) (h.2 p))
  . intro h
    have hP (p : HeightOneSpectrum (RingOfIntegers K)) :=
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
        (K := K) (v := p) (a := heckeFiniteIdeleComponent p b)).mpr (h p)
    exact And.intro (fun p => (hP p).1) (fun p => (hP p).2)

/-- The kernel of the ideal map is exactly the integral unit subgroup. -/
theorem heckeFiniteIdeleIdealHom_eq_one_iff (b : Units (F K)) :
    heckeFiniteIdeleIdealHom b = 1 <-> Membership.mem heckeIntegralFiniteUnitGroup b := by
  rw [mem_heckeIntegralFiniteUnitGroup_iff_valued_one]
  constructor
  . intro h p
    have hc : heckeFiniteIdeleFractionalIdeal b = 1 := congrArg Units.val h
    apply (heckeFiniteIdeleExponent_eq_zero_iff b p).mp
    rw [<- count_heckeFiniteIdeleFractionalIdeal, hc, FractionalIdeal.count_one]
  . intro h
    apply Units.ext
    change heckeFiniteIdeleFractionalIdeal b = 1
    apply frac_eq_of_counts (heckeFiniteIdeleFractionalIdeal_ne_zero _)
      (show Not ((1 : Frac K) = 0) from one_ne_zero)
    intro p
    rw [count_heckeFiniteIdeleFractionalIdeal, FractionalIdeal.count_one]
    exact (heckeFiniteIdeleExponent_eq_zero_iff b p).mpr (h p)

/-- The ideal class of a finite idele. -/
noncomputable def heckeFiniteIdeleClass :
    MonoidHom (Units (F K)) (ClassGroup (RingOfIntegers K)) :=
  (ClassGroup.mk K).comp heckeFiniteIdeleIdealHom

private theorem heckeClassGroup_equiv_mk_self (I : Units (Frac K)) :
    ClassGroup.equiv K (ClassGroup.mk K I) =
      QuotientGroup.mk' (toPrincipalIdeal (RingOfIntegers K) K).range I := by
  rw [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self]
  rfl

/-- Every ideal class has a finite idele representative. -/
theorem surjective_heckeFiniteIdeleClass :
    Function.Surjective (heckeFiniteIdeleClass (K := K)) := by
  intro c
  let e := ClassGroup.equiv (R := RingOfIntegers K) K
  choose I hI using QuotientGroup.mk'_surjective (toPrincipalIdeal (RingOfIntegers K) K).range (e c)
  choose b hb using surjective_heckeFiniteIdeleIdealHom I
  refine Exists.intro b (e.injective ?_)
  change ClassGroup.equiv K (ClassGroup.mk K (heckeFiniteIdeleIdealHom b)) = e c
  rw [hb, heckeClassGroup_equiv_mk_self]
  exact hI

private theorem exists_principal_of_heckeClass_eq_one (I : Units (Frac K))
    (h : ClassGroup.mk K I = 1) :
    Exists (fun u : Units K => toPrincipalIdeal (RingOfIntegers K) K u = I) := by
  have he := congrArg (ClassGroup.equiv (R := RingOfIntegers K) K) h
  rw [heckeClassGroup_equiv_mk_self, map_one, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at he
  exact he

/-- Two finite ideles in the same ideal class differ by a principal idele and an integral finite unit. -/
theorem heckeFiniteIdele_exists_principal_mul_integral
    (a b : Units (F K)) (h : heckeFiniteIdeleClass a = heckeFiniteIdeleClass b) :
    Exists (fun x : Units K => Exists (fun u : Units (F K) =>
      And (Membership.mem heckeIntegralFiniteUnitGroup u)
        (a = FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K x * b * u))) := by
  let I := heckeFiniteIdeleIdealHom (K := K)
  let d := a * Inv.inv b
  have hd : ClassGroup.mk K (I d) = 1 := by
    change heckeFiniteIdeleClass (a * Inv.inv b) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  choose x hx using exists_principal_of_heckeClass_eq_one (I d) hd
  let v := FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K x * b
  have hv : I a = I v := by
    calc
      I a = I d * I b := by
        change I a = I (a * Inv.inv b) * I b
        rw [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]
      _ = toPrincipalIdeal (RingOfIntegers K) K x * I b := by rw [hx]
      _ = I v := by
        change _ = heckeFiniteIdeleIdealHom
          (FiniteAdeleRing.unitEmbedding (RingOfIntegers K) K x * b)
        rw [map_mul, heckeFiniteIdeleIdealHom_principal]
  let u := Inv.inv v * a
  have hU : I u = 1 := by
    change I (Inv.inv v * a) = 1
    rw [map_mul, map_inv, hv, inv_mul_cancel]
  refine Exists.intro x (Exists.intro u (And.intro ((heckeFiniteIdeleIdealHom_eq_one_iff u).mp hU) ?_))
  change a = v * (Inv.inv v * a)
  rw [<- mul_assoc, mul_inv_cancel, one_mul]

end Robin1984.GRH
