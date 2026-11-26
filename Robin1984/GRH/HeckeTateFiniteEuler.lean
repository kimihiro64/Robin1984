import Robin1984.GRH.HeckeTateFiniteIntegral

/-!
# The finite Tate Euler integral

The actual normalized finite Tate density is absolutely integrable on the
half-plane of convergence. Its integral is the rank-one Euler product.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The finite Euler product in Tate's thesis.
- Formalization note: The normalized finite Tate integral converges absolutely and equals the Hecke Euler product for real part greater than one.
- PROVENANCE-END
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open IsDedekindDomain NumberField MeasureTheory Set
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

/-- The weighted local factor of the finite Tate density at a single place. -/
private def heckeFiniteTateLocalDensity (chi : UnitaryHeckeCharacter K) (s : Complex)
    (p : HeightOneSpectrum (RingOfIntegers K)) (a : Units (p.adicCompletion K)) : Complex :=
  heckeLocalAdditiveTateTest p chi a.val *
    (Complex.exp (s * (Real.log (norm a.val) : Complex)) *
      (chi.val (localIdeleHom K p a) : Complex))

/-- The finite Tate density is the product of its local factors over any
finite set containing the nonunit components and all ramified places. -/
private theorem heckeFiniteTateDensity_eq_prod_local
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (chi : UnitaryHeckeCharacter K) (s : Complex)
    (b : Units (FiniteAdeleRing (RingOfIntegers K) K))
    (S : Finset (HeightOneSpectrum (RingOfIntegers K)))
    (hRam : (finite_heckeRamifiedPlaces chi).toFinset <= S)
    (hUnit : forall p, Not (Membership.mem S p) -> Valued.v (b.val p) = 1) :
    heckeFiniteTateDensity chi s b =
      S.prod (fun p => heckeFiniteTateLocalDensity chi s p (heckeFiniteIdeleComponent p b)) := by
  classical
  let P := HeightOneSpectrum (RingOfIntegers K)
  let a (p : P) := heckeFiniteIdeleComponent p b
  let single (p : P) := heckeFiniteLocalIdele p (a p)
  let part := S.prod single
  have hAt (q : P) (hq : Membership.mem S q) :
      heckeFiniteIdeleComponent q part = a q := by
    change heckeFiniteIdeleComponent q (S.prod single) = a q
    rw [map_prod, Finset.prod_eq_single_of_mem q hq]
    . apply Units.ext
      exact heckeFiniteLocalIdele_at q (a q)
    . intro p _ hp
      apply Units.ext
      exact heckeFiniteLocalIdele_away p q (Ne.symm hp) (a p)
  have hAway (q : P) (hq : Not (Membership.mem S q)) :
      heckeFiniteIdeleComponent q part = 1 := by
    change heckeFiniteIdeleComponent q (S.prod single) = 1
    rw [map_prod]
    apply Finset.prod_eq_one
    intro p hp
    have hne : Not (q = p) := fun h => hq (by rw [h]; exact hp)
    apply Units.ext
    exact heckeFiniteLocalIdele_away p q hne (a p)
  let u := Inv.inv part * b
  have hu : Membership.mem (heckeIntegralFiniteUnitGroup (K := K)) u := by
    apply (mem_heckeIntegralFiniteUnitGroup_iff_valued_one u).mpr
    intro p
    change Valued.v (heckeFiniteIdeleComponent p (Inv.inv part * b)).val = 1
    rw [map_mul, map_inv]
    by_cases hp : Membership.mem S p
    . rw [hAt p hp, inv_mul_cancel]
      exact map_one _
    . rw [hAway p hp, inv_one, one_mul]
      exact hUnit p hp
  have hbu : part * u = b := by
    unfold u
    rw [<- mul_assoc, mul_inv_cancel, one_mul]
  have hD : heckeFiniteTateDensity chi s b = heckeFiniteTateDensity chi s part := by
    rw [<- hbu]
    exact heckeFiniteTateDensity_mul_integralUnit chi s part u hu
  have hAtVal (p : P) (hp : Membership.mem S p) : part.val p = (a p).val :=
    congrArg Units.val (hAt p hp)
  have hAwayVal (p : P) (hp : Not (Membership.mem S p)) : part.val p = 1 :=
    congrArg Units.val (hAway p hp)
  have hT : heckeFiniteAdditiveTateTest chi part.val =
      S.prod (fun p => heckeLocalAdditiveTateTest p chi (a p).val) := by
    by_cases hPart : Membership.mem (heckeIntegralFiniteAdeles (K := K)) part.val
    case pos =>
      have hB (p : P) (hp : Membership.mem S p) :
          Membership.mem (p.adicCompletionIntegers K) (a p).val := by
        rw [<- hAtVal p hp]
        exact hPart p
      rw [heckeFiniteAdditiveTateTest, if_pos hPart]
      calc
        _ = (finite_heckeRamifiedPlaces chi).toFinset.prod
            (fun p => heckeLocalAdditiveTateTest p chi (a p).val) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [hAtVal p (hRam hp)]
        _ = _ := by
          apply Finset.prod_subset hRam
          intro p hp hNot
          have hUnram : HeckeUnramifiedAt chi p := by
            by_contra h
            exact hNot ((finite_heckeRamifiedPlaces chi).mem_toFinset.mpr h)
          have hv : Valued.v (a p).val <= 1 :=
            (HeightOneSpectrum.mem_adicCompletionIntegers (RingOfIntegers K) K p).mp (hB p hp)
          rw [heckeLocalAdditiveTateTest, if_pos hUnram, if_pos hv]
    case neg =>
      have hBad : exists p : P, Not (Membership.mem (p.adicCompletionIntegers K) (part.val p)) := by
        exact not_forall.mp hPart
      choose p hp using hBad
      have hP : Membership.mem S p := by
        by_contra h
        exact hp (by rw [hAwayVal p h]; exact (p.adicCompletionIntegers K).one_mem)
      have hbad : Not (Valued.v (a p).val <= 1) := by
        intro hv
        apply hp
        rw [hAtVal p hP]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers (RingOfIntegers K) K p).mpr hv
      have hTest0 : heckeLocalAdditiveTateTest p chi (a p).val = 0 := by
        by_cases hU : HeckeUnramifiedAt chi p
        . rw [heckeLocalAdditiveTateTest, if_pos hU, if_neg hbad]
        . have hne : Not (Valued.v (a p).val = 1) := fun h => hbad h.le
          rw [heckeLocalAdditiveTateTest, if_neg hU, dif_neg hne]
      rw [heckeFiniteAdditiveTateTest, if_neg hPart]
      exact (Finset.prod_eq_zero hP hTest0).symm
  have hNorm : heckeFiniteIdeleNorm part = S.prod (fun p => norm (a p).val) := by
    change heckeFiniteIdeleNorm (S.prod single) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [<- heckeFiniteAdditiveModulus_eq_ideleNorm]
    exact heckeFiniteAdditiveModulus_localIdele_eq_norm p (a p)
  have hIncl (p : P) :
      heckeFiniteIdeleInclusion (single p) = localIdeleHom K p (a p) := by
    apply Units.ext
    exact Prod.ext rfl rfl
  have hChar : (chi.val (heckeFiniteIdeleInclusion part) : Complex) =
      S.prod (fun p => (chi.val (localIdeleHom K p (a p)) : Complex)) := by
    change (chi.val (heckeFiniteIdeleInclusion (S.prod single)) : Complex) = _
    rw [map_prod, map_prod]
    calc
      _ = S.prod (fun p => (chi.val (heckeFiniteIdeleInclusion (single p)) : Complex)) :=
        map_prod Circle.coeHom _ _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p _
        rw [hIncl]
  have hPow :
      Complex.exp (s * (Real.log (heckeFiniteIdeleNorm part) : Complex)) =
        S.prod (fun p => Complex.exp (s * (Real.log (norm (a p).val) : Complex))) := by
    rw [hNorm, Real.log_prod (fun p _ => norm_ne_zero_iff.mpr (a p).ne_zero),
      Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  rw [hD, heckeFiniteTateDensity, hT, hPow, hChar]
  simp only [heckeFiniteTateLocalDensity, <- Finset.prod_mul_distrib, a]

/-- The model local weight uses the normalized local absolute value. -/
private theorem heckeFiniteTateLocalDensity_eq_localTest_mul_weight
    (chi : UnitaryHeckeCharacter K) (s : Complex) (p : HeightOneSpectrum (RingOfIntegers K))
    (a : Units (p.adicCompletion K)) :
    heckeFiniteTateLocalDensity chi s p a =
      heckeLocalTateTest p chi a * heckeLocalTateWeight p chi s a := by
  let i := Multiplicative.toAdd (heckeLocalValueIndex p a)
  have hn : norm a.val = (dedekindPrimeNorm K p : Real) ^ i := by
    rw [FinitePlace.norm_def, <- coe_heckeLocalValueIndex p a,
      WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe]
    change (((Ideal.absNorm p.asIdeal : NNReal) ^ i : NNReal) : Real) =
      (Ideal.absNorm p.asIdeal : Real) ^ i
    norm_cast
  have hLog : (Real.log (norm a.val) : Complex) =
      (i : Complex) * (Real.log (dedekindPrimeNorm K p : Real) : Complex) := by
    rw [hn, Real.log_zpow, Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [heckeFiniteTateLocalDensity, heckeLocalAdditiveTateTest_coe_unit, hLog]
  change heckeLocalTateTest p chi a *
      (Complex.exp (s * ((i : Complex) * (Real.log (dedekindPrimeNorm K p : Real) : Complex))) *
        (chi.val (localIdeleHom K p a) : Complex)) =
    heckeLocalTateTest p chi a *
      ((chi.val (localIdeleHom K p a) : Complex) *
        Complex.exp ((i : Complex) * (Real.log (dedekindPrimeNorm K p : Real) : Complex) * s))
  rw [show s * ((i : Complex) * (Real.log (dedekindPrimeNorm K p : Real) : Complex)) =
    (i : Complex) * (Real.log (dedekindPrimeNorm K p : Real) : Complex) * s by ring]
  ac_rfl


/-- The weighted local density is the Euler parameter to the nonnegative
ideal exponent. Negative ideal exponents give zero. -/
private theorem heckeLocalTateTest_mul_weight_eq_primePower
    (chi : UnitaryHeckeCharacter K) (s : Complex) (p : HeightOneSpectrum (RingOfIntegers K))
    (a : Units (p.adicCompletion K)) :
    heckeLocalTateTest p chi a * heckeLocalTateWeight p chi s a =
      let n := -Multiplicative.toAdd (heckeLocalValueIndex p a)
      if 0 <= n then
        (heckeLocalParameter chi p * (dedekindPrimeNorm K p : Complex) ^ (-s)) ^ n.toNat
      else 0 := by
  classical
  let index (x : Units (p.adicCompletion K)) : Int := Multiplicative.toAdd (heckeLocalValueIndex p x)
  have hShell (x : Units (p.adicCompletion K)) :
      Membership.mem (heckeLocalUnitShell p) x <-> index x = 0 := by
    change Valued.v (x : p.adicCompletion K) = (1 : WithZero (Multiplicative Int)) <-> _
    rw [<- coe_heckeLocalValueIndex p x]
    change ((heckeLocalValueIndex p x : WithZero (Multiplicative Int)) =
      ((1 : Multiplicative Int) : WithZero (Multiplicative Int))) <-> _
    rw [WithZero.coe_inj]
    rfl
  have hInt :
      Membership.mem (heckeLocalIntegralUnits p) a <-> 0 <= -index a := by
    change index a <= 0 <-> 0 <= -index a
    exact neg_nonneg.symm
  change heckeLocalTateTest p chi a * heckeLocalTateWeight p chi s a =
    if 0 <= -index a then
      (heckeLocalParameter chi p * (dedekindPrimeNorm K p : Complex) ^ (-s)) ^
        (-index a).toNat
    else 0
  by_cases hUnram : HeckeUnramifiedAt chi p
  case pos =>
    rw [heckeLocalTateTest, if_pos hUnram]
    by_cases hn : 0 <= -index a
    case pos =>
      rw [Set.indicator_of_mem (hInt.mpr hn), one_mul, if_pos hn]
      choose v hv using HeightOneSpectrum.valuedAdicCompletion_surjective K p finiteUniformizerValue
      have hv0 : Not (v = 0) := by
        intro h
        rw [h, Valuation.map_zero] at hv
        exact WithZero.coe_ne_zero hv.symm
      let pi := Units.mk0 v hv0
      have hPi : index pi = -1 := by
        have hPiInd : heckeLocalValueIndex p pi = Multiplicative.ofAdd (-1 : Int) := by
          apply WithZero.coe_inj.mp
          rw [coe_heckeLocalValueIndex p pi]
          exact hv
        exact congrArg Multiplicative.toAdd hPiInd
      have hMul (x y : Units (p.adicCompletion K)) : index (x * y) = index x + index y := by
        exact congrArg Multiplicative.toAdd ((heckeLocalValueIndex p).map_mul x y)
      have hInv (x : Units (p.adicCompletion K)) : index (Inv.inv x) = -index x := by
        exact congrArg Multiplicative.toAdd ((heckeLocalValueIndex p).map_inv x)
      have hPow (m : Nat) : index (pi ^ m) = -(m : Int) := by
        induction m with
        | zero =>
          change Multiplicative.toAdd (heckeLocalValueIndex p (pi ^ (0 : Nat))) = _
          rw [pow_zero, map_one]
          rfl
        | succ m ih =>
          rw [pow_succ, hMul, ih, hPi, Nat.cast_succ]
          ring
      let n := (-index a).toNat
      have hnCast : (n : Int) = -index a := Int.toNat_of_nonneg hn
      let u := Inv.inv (pi ^ n) * a
      have hu : Membership.mem (heckeLocalUnitShell p) u := by
        apply (hShell u).mpr
        change index (Inv.inv (pi ^ n) * a) = 0
        rw [hMul, hInv, hPow, hnCast]
        ring
      have ha : a = pi ^ n * u := by
        dsimp only [u]
        rw [<- mul_assoc, mul_inv_cancel, one_mul]
      calc
        _ = heckeLocalTateWeight p chi s (pi ^ n * u) := congrArg _ ha
        _ = _ := by
          rw [map_mul, map_pow, heckeLocalTateWeight_eq_one p chi hUnram s u hu, mul_one,
            heckeLocalTateWeight_uniformizer p chi hUnram s pi hv]
    case neg =>
      rw [Set.indicator_of_notMem (fun h => hn (hInt.mp h)), zero_mul, if_neg hn]
  case neg =>
    rw [heckeLocalTateTest, if_neg hUnram, heckeLocalRamifiedTest]
    by_cases ha : index a = 0
    case pos =>
      have hn : 0 <= -index a := by rw [ha, neg_zero]
      rw [Set.indicator_of_mem ((hShell a).mpr ha), if_pos hn, ha, neg_zero, Int.toNat_zero,
        pow_zero]
      have hWeight :
          heckeLocalTateWeight p chi s a = (chi.val (localIdeleHom K p a) : Complex) := by
        change (chi.val (localIdeleHom K p a) : Complex) *
          Complex.exp ((index a : Complex) * (Real.log (dedekindPrimeNorm K p : Real) : Complex) * s) = _
        simp [ha]
      rw [hWeight]
      have hc : chi.val (localIdeleHom K p (Inv.inv a)) *
          chi.val (localIdeleHom K p a) = 1 := by
        rw [<- map_mul, <- map_mul, inv_mul_cancel, map_one, map_one]
      simpa only [Circle.coe_mul, Circle.coe_one] using congrArg (fun z : Circle => (z : Complex)) hc
    case neg =>
      rw [Set.indicator_of_notMem (fun h => ha ((hShell a).mp h)), zero_mul]
      by_cases hn : 0 <= -index a
      case pos =>
        have hz : heckeLocalParameter chi p = 0 := by
          unfold heckeLocalParameter
          rw [if_neg hUnram]
        have hN : Not ((-index a).toNat = 0) := by
          intro h
          apply ha
          have hnCast := Int.toNat_of_nonneg hn
          rw [h, Nat.cast_zero] at hnCast
          exact neg_eq_zero.mp hnCast.symm
        rw [if_pos hn, hz, zero_mul, zero_pow hN]
      case neg =>
        rw [if_neg hn]


/-- At a fractional ideal, the coefficient is a finite product of the
local Euler parameters if all relevant prime exponents are nonnegative. -/
private theorem heckeFiniteTateIdealWeight_eq_primeProduct
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (chi : UnitaryHeckeCharacter K) (s : Complex)
    (I : Units (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))
    (S : Finset (HeightOneSpectrum (RingOfIntegers K)))
    (hRam : (finite_heckeRamifiedPlaces chi).toFinset <= S)
    (hSupp : forall p, Not (Membership.mem S p) -> FractionalIdeal.count K p I.val = 0) :
    heckeFiniteTateIdealWeight chi s I =
      if forall p, Membership.mem S p -> 0 <= FractionalIdeal.count K p I.val then
        S.prod (fun p =>
          (heckeLocalParameter chi p * (dedekindPrimeNorm K p : Complex) ^ (-s)) ^
            (FractionalIdeal.count K p I.val).toNat)
      else 0 := by
  classical
  let b := Classical.choose (surjective_heckeFiniteIdeleIdealHom (K := K) I)
  have hI : heckeFiniteIdeleIdealHom b = I :=
    Classical.choose_spec (surjective_heckeFiniteIdeleIdealHom (K := K) I)
  have hCount (p : HeightOneSpectrum (RingOfIntegers K)) :
      FractionalIdeal.count K p I.val = heckeFiniteIdeleExponent b p := by
    rw [<- hI]
    exact count_heckeFiniteIdeleFractionalIdeal b p
  have hUnit (p : HeightOneSpectrum (RingOfIntegers K)) (hp : Not (Membership.mem S p)) :
      Valued.v (b.val p) = 1 := by
    have hIdx : Multiplicative.toAdd (heckeLocalValueIndex p (heckeFiniteIdeleComponent p b)) = 0 :=
      neg_eq_zero.mp ((hCount p).symm.trans (hSupp p hp))
    have hVal : heckeLocalValueIndex p (heckeFiniteIdeleComponent p b) = 1 :=
      congrArg Multiplicative.ofAdd hIdx
    change Valued.v (heckeFiniteIdeleComponent p b).val = 1
    rw [<- coe_heckeLocalValueIndex, hVal]
    rfl
  have hLoc (p : HeightOneSpectrum (RingOfIntegers K)) :
      heckeFiniteTateLocalDensity chi s p (heckeFiniteIdeleComponent p b) =
        if 0 <= FractionalIdeal.count K p I.val then
          (heckeLocalParameter chi p * (dedekindPrimeNorm K p : Complex) ^ (-s)) ^
            (FractionalIdeal.count K p I.val).toNat
        else 0 := by
    rw [heckeFiniteTateLocalDensity_eq_localTest_mul_weight, heckeLocalTateTest_mul_weight_eq_primePower,
      hCount]
    rfl
  change heckeFiniteTateDensity chi s b = _
  rw [heckeFiniteTateDensity_eq_prod_local chi s b S hRam hUnit]
  by_cases hNonneg : forall p, Membership.mem S p -> 0 <= FractionalIdeal.count K p I.val
  case pos =>
    rw [if_pos hNonneg]
    apply Finset.prod_congr rfl
    intro p hp
    rw [hLoc, if_pos (hNonneg p hp)]
  case neg =>
    rw [if_neg hNonneg]
    choose p hp using not_forall.mp hNonneg
    have hpS : Membership.mem S p := Classical.byContradiction (fun h => hp (fun hS => False.elim (h hS)))
    apply Finset.prod_eq_zero hpS
    rw [hLoc, if_neg (fun h => hp (fun _ => h))]


section FiniteEulerProduct

local notation "PrimePlace" => HeightOneSpectrum (RingOfIntegers K)
local notation "FracIdeal" => FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K

private def exponentFractionalIdeal (e : Finsupp PrimePlace Nat) : Units FracIdeal := by
  classical
  let f (p : PrimePlace) : FracIdeal := (p.asIdeal : FracIdeal) ^ (e p : Int)
  have hSupport : Set.Subset (Function.mulSupport f) (e.support : Set PrimePlace) := by
    intro p hp
    by_contra h
    have he : e p = 0 := Finsupp.notMem_support_iff.mp h
    exact hp (by simp [f, he])
  refine Units.mk0 (finprod f) ?_
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hSupport e.support.finite_toSet]
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot)

private theorem count_exponentFractionalIdeal (e : Finsupp PrimePlace Nat) (p : PrimePlace) :
    FractionalIdeal.count K p (exponentFractionalIdeal e).val = (e p : Int) := by
  change FractionalIdeal.count K p
    (finprod (fun q : PrimePlace => (q.asIdeal : FracIdeal) ^ (e q : Int))) = _
  apply FractionalIdeal.count_finprod
  apply Filter.eventually_cofinite.mpr
  apply e.support.finite_toSet.subset
  intro q h
  apply Finsupp.mem_support_iff.mpr
  intro hq
  exact h (by simp [hq])

private theorem exponentFractionalIdeal_injective :
    Function.Injective (exponentFractionalIdeal (K := K)) := by
  intro e f h
  ext p
  have hC := congrArg (fun I : Units FracIdeal => FractionalIdeal.count K p I.val) h
  rw [count_exponentFractionalIdeal, count_exponentFractionalIdeal] at hC
  exact_mod_cast hC

private theorem exponentFractionalIdeal_range (I : Units FracIdeal) :
    Membership.mem (Set.range (exponentFractionalIdeal (K := K))) I <->
      forall p : PrimePlace, 0 <= FractionalIdeal.count K p I.val := by
  classical
  constructor
  case mp =>
    intro h p
    choose e he using h
    rw [<- he, count_exponentFractionalIdeal]
    exact Int.natCast_nonneg _
  case mpr =>
    intro h
    let hF := FractionalIdeal.finite_factors I.val
    let e : Finsupp PrimePlace Nat :=
      Finsupp.onFinset hF.toFinset (fun p => (FractionalIdeal.count K p I.val).toNat)
        (fun p hp => hF.mem_toFinset.mpr (fun h0 => hp (by
          change FractionalIdeal.count K p I.val = 0 at h0
          rw [h0, Int.toNat_zero])))
    refine Exists.intro e (Units.ext ?_)
    rw [<- FractionalIdeal.finprod_heightOneSpectrum_factorization' K (exponentFractionalIdeal e).ne_zero,
      <- FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
    apply finprod_congr
    intro p
    rw [count_exponentFractionalIdeal]
    exact congrArg (fun n : Int => (p.asIdeal : FracIdeal) ^ n) (Int.toNat_of_nonneg (h p))

private def heckeTateEulerWeight (chi : UnitaryHeckeCharacter K) (s : Complex) (p : PrimePlace) :
    Complex :=
  heckeLocalParameter chi p * (dedekindPrimeNorm K p : Complex) ^ (-s)

private theorem norm_heckeTateEulerWeight_le (chi : UnitaryHeckeCharacter K) (s : Complex)
    (p : PrimePlace) :
    norm (heckeTateEulerWeight chi s p) <= norm ((dedekindPrimeNorm K p : Complex) ^ (-s)) := by
  rw [heckeTateEulerWeight, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_heckeLocalParameter_le_one chi p)

private theorem heckeTateIdealWeight_exponentFractionalIdeal
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (chi : UnitaryHeckeCharacter K) (s : Complex) (e : Finsupp PrimePlace Nat) :
    heckeFiniteTateIdealWeight chi s (exponentFractionalIdeal e) =
      exponentWeight (heckeTateEulerWeight chi s) e := by
  classical
  let S := Union.union e.support (finite_heckeRamifiedPlaces chi).toFinset
  have hRam : (finite_heckeRamifiedPlaces chi).toFinset <= S := Finset.subset_union_right
  have hSupp (p : PrimePlace) (hp : Not (Membership.mem S p)) :
      FractionalIdeal.count K p (exponentFractionalIdeal e).val = 0 := by
    rw [count_exponentFractionalIdeal, Finsupp.notMem_support_iff.mp
      (fun h => hp (Finset.mem_union_left _ h)), Nat.cast_zero]
  have hPos (p : PrimePlace) (_ : Membership.mem S p) :
      0 <= FractionalIdeal.count K p (exponentFractionalIdeal e).val := by
    rw [count_exponentFractionalIdeal]
    exact Int.natCast_nonneg _
  rw [heckeFiniteTateIdealWeight_eq_primeProduct chi s _ S hRam hSupp, if_pos hPos]
  unfold exponentWeight
  rw [Finsupp.prod_of_support_subset _ (show e.support <= S from Finset.subset_union_left)
    _ (fun p _ => pow_zero (heckeTateEulerWeight chi s p))]
  apply Finset.prod_congr rfl
  intro p _
  rw [count_exponentFractionalIdeal, Int.toNat_natCast]
  rfl

private theorem heckeTateIdealWeight_zero_off_range
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (chi : UnitaryHeckeCharacter K) (s : Complex) (I : Units FracIdeal)
    (h : Not (Membership.mem (Set.range (exponentFractionalIdeal (K := K))) I)) :
    heckeFiniteTateIdealWeight chi s I = 0 := by
  classical
  let hF := FractionalIdeal.finite_factors I.val
  let S := Union.union hF.toFinset (finite_heckeRamifiedPlaces chi).toFinset
  have hRam : (finite_heckeRamifiedPlaces chi).toFinset <= S := Finset.subset_union_right
  have hSupp (p : PrimePlace) (hp : Not (Membership.mem S p)) :
      FractionalIdeal.count K p I.val = 0 := by
    by_contra h0
    exact hp (Finset.mem_union_left _ (hF.mem_toFinset.mpr h0))
  have hNeg : Not (forall p, Membership.mem S p -> 0 <= FractionalIdeal.count K p I.val) := by
    intro hPos
    apply h
    apply (exponentFractionalIdeal_range I).mpr
    intro p
    by_cases hp : Membership.mem S p
    . exact hPos p hp
    . rw [hSupp p hp]
  rw [heckeFiniteTateIdealWeight_eq_primeProduct chi s I S hRam hSupp, if_neg hNeg]

set_option maxHeartbeats 600000 in
/-- The normalized finite Tate integral converges absolutely and equals the
Hecke Euler product on the half-plane of absolute convergence. -/
theorem integral_heckeFiniteTateDensity_eq_heckeEulerL
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [MeasurableSpace (Units (FiniteAdeleRing (RingOfIntegers K) K))]
    [BorelSpace (Units (FiniteAdeleRing (RingOfIntegers K) K))]
    [MeasurableSpace (Units FracIdeal)] [MeasurableSingletonClass (Units FracIdeal)]
    (mu : Measure (Units (FiniteAdeleRing (RingOfIntegers K) K))) [mu.IsMulLeftInvariant]
    (hUnit : mu (heckeIntegralFiniteUnitGroup (K := K) :
      Set (Units (FiniteAdeleRing (RingOfIntegers K) K))) = 1)
    (chi : UnitaryHeckeCharacter K) {s : Complex} (hs : 1 < s.re) :
    And (Integrable (heckeFiniteTateDensity chi s) mu)
      (integral mu (heckeFiniteTateDensity chi s) = heckeEulerL K chi s) := by
  classical
  let e := exponentFractionalIdeal (K := K)
  let J := Set.range e
  let a := heckeTateEulerWeight chi s
  let w := heckeFiniteTateIdealWeight chi s
  have hInj : Function.Injective e := exponentFractionalIdeal_injective
  have hTerms (b : Finsupp PrimePlace Nat) : w (e b) = exponentWeight a b :=
    heckeTateIdealWeight_exponentFractionalIdeal chi s b
  have hZero (I : Units FracIdeal) (hI : Not (Membership.mem J I)) : w I = 0 :=
    heckeTateIdealWeight_zero_off_range chi s I hI
  have hSum := summable_norm_exponentWeight_of_dedekindPrimeNorm K a hs (norm_heckeTateEulerWeight_le chi s)
  have hSub : Summable (Function.comp (fun I => norm (w I)) e) :=
    hSum.congr (fun b => congrArg norm (hTerms b).symm)
  have hFull : Summable (fun I => norm (w I)) :=
    (hInj.summable_iff (fun I hI => by rw [hZero I hI, norm_zero])).mp hSub
  have hIntegral := integral_heckeFiniteTateDensity_eq_idealSum mu hUnit chi s hFull
  refine And.intro hIntegral.1 (hIntegral.2.trans ?_)
  have hSumEq : tsum w = tsum (exponentWeight a) := by
    have hSupport : Set.Subset (Function.support w) J := fun I hI =>
      Classical.byContradiction (fun h => hI (hZero I h))
    calc
      _ = tsum (fun b => w (e b)) := (hInj.tsum_eq hSupport).symm
      _ = _ := tsum_congr hTerms
  rw [hSumEq]
  have hPointwise (p : PrimePlace) : norm (a p) < 1 := by
    apply (norm_heckeTateEulerWeight_le chi s p).trans_lt
    have hp : (1 : Real) < (dedekindPrimeNorm K p : Real) := by
      exact_mod_cast one_lt_dedekindPrimeNorm K p
    rw [<- Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hp),
      Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (neg_lt_zero.mpr (zero_lt_one.trans hs))
  exact (hasProd_eulerFactors_of_exponentWeight a hPointwise hSum).unique (hasProd_heckeEulerL K chi hs)

end FiniteEulerProduct


end Robin1984.GRH
