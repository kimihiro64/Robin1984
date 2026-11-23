import Mathlib.Topology.Algebra.Group.Units
import Robin1984.GRH.HeckeEulerProduct

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The conductor of a continuous unitary character of the idele class group over a number field.
- Formalization note: Proves finite ramification and existence of the least local conductor exponents. Constructs the conductor ideal and proves positivity and invariance of the arithmetic conductor.
- PROVENANCE-END
-/

/-!
# The conductor of a unitary Hecke character

Continuity on the ideles gives a finite set of ramified finite places.
At each finite place, continuity and the local valuation give a least
depth of a principal congruence subgroup on which the character is
trivial. The product of these prime powers is the conductor ideal.
-/

set_option autoImplicit false

open Complex Filter IsDedekindDomain NumberField Set

namespace Robin1984.GRH

private theorem complex_eq_one_of_unitNorm_of_re_pow {z : Complex}
    (hu : norm z = 1) (hr : forall n : Nat, (1 : Real) / 2 < (z ^ n).re) :
    z = 1 := by
  by_contra hn
  have hp : 0 < norm (z - 1) := norm_pos_iff.mpr (sub_ne_zero.mpr hn)
  let n := Classical.choose (exists_nat_gt ((4 : Real) / norm (z - 1)))
  have hnLarge : 4 / norm (z - 1) < (n : Real) :=
    Classical.choose_spec (exists_nat_gt ((4 : Real) / norm (z - 1)))
  have hFour : (4 / norm (z - 1) : Real) * norm (z - 1) = 4 := by
    field_simp [ne_of_gt hp]
  have hLarge : 4 < (n : Real) * norm (z - 1) := by
    simpa only [hFour] using mul_lt_mul_of_pos_right hnLarge hp
  let S : Complex := (Finset.range n).sum (fun j => z ^ j)
  have hSre : (n : Real) / 2 <= S.re := by
    rw [show S.re = (Finset.range n).sum (fun j => (z ^ j).re) by
      exact Complex.re_sum _ _]
    calc
      (n : Real) / 2 = (Finset.range n).sum (fun _ => (1 : Real) / 2) := by
        simp [div_eq_mul_inv, nsmul_eq_mul]
      _ <= _ := Finset.sum_le_sum (fun j _ => (hr j).le)
  have hS : S * (z - 1) = z ^ n - 1 := geom_sum_mul z n
  have hUpper : norm S * norm (z - 1) <= 2 := by
    rw [<- norm_mul, hS]
    simpa [norm_pow, hu, one_add_one_eq_two] using norm_sub_le (z ^ n) (1 : Complex)
  have hLower : (n : Real) / 2 * norm (z - 1) <= 2 :=
    (mul_le_mul_of_nonneg_right (hSre.trans (Complex.re_le_norm S)) hp.le).trans hUpper
  nlinarith

private theorem eventually_single_eq_one_of_continuous {I : Type*} {G : I -> Type*}
    [DecidableEq I] [forall i, Monoid (G i)] [forall i, TopologicalSpace (G i)]
    (chi : MonoidHom (forall i, G i) Circle)
    (hc : Continuous (fun x : forall i, G i => (chi x : Complex))) :
    Filter.Eventually (fun i : I => forall a : G i, chi (Pi.mulSingle i a) = 1)
      Filter.cofinite := by
  classical
  let bad (i : I) : Prop :=
    exists a : G i, Not ((1 : Real) / 2 < ((chi (Pi.mulSingle i a) : Circle) : Complex).re)
  let f (i : I) : forall j, G j :=
    if h : bad i then Pi.mulSingle i h.choose else 1
  have ht : Filter.Tendsto f Filter.cofinite (nhds (1 : forall j, G j)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have heq : Filter.EventuallyEq Filter.cofinite (fun i => f i j) (fun _ => (1 : G j)) := by
      filter_upwards [(Set.finite_singleton j).compl_mem_cofinite] with i hi
      by_cases hbad : bad i
      case pos =>
        have hji : Not (j = i) := fun e => hi e.symm
        simp only [f, dif_pos hbad, Pi.mulSingle_eq_of_ne hji]
      case neg =>
        simp only [f, dif_neg hbad, Pi.one_apply]
    exact (Filter.tendsto_congr' heq).mpr tendsto_const_nhds
  have hComp : Filter.Tendsto (fun i => (chi (f i) : Complex)) Filter.cofinite
      (nhds (1 : Complex)) := by
    simpa [Function.comp_def] using (hc.tendsto (1 : forall j, G j)).comp ht
  have hOpen : IsOpen {z : Complex | (1 : Real) / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hOne : (1 : Real) / 2 < (1 : Complex).re := by norm_num
  filter_upwards [hComp.eventually (hOpen.mem_nhds hOne)] with i hi
  have hGood : Not (bad i) := by
    intro h
    apply h.choose_spec
    simpa only [Set.mem_ofPred_eq, f, dif_pos h] using hi
  intro a
  apply Subtype.ext
  change (chi (Pi.mulSingle i a) : Complex) = 1
  apply complex_eq_one_of_unitNorm_of_re_pow (Circle.norm_coe _)
  intro n
  by_contra h
  apply hGood
  refine Exists.intro (a ^ n) ?_
  simpa only [Pi.mulSingle_pow, map_pow, Circle.coe_pow] using h

private abbrev FiniteIntegralAdeleDomain (K : Type*) [Field K] [NumberField K] :=
  (p : HeightOneSpectrum (RingOfIntegers K)) -> p.adicCompletionIntegers K

private noncomputable def finiteIntegralAdeleHom (K : Type*) [Field K] [NumberField K] :
    MonoidHom (FiniteIntegralAdeleDomain K) (AdeleRing (RingOfIntegers K) K) where
  toFun a := (1, RestrictedProduct.structureMap
    (fun p : HeightOneSpectrum (RingOfIntegers K) => p.adicCompletion K)
    (fun p : HeightOneSpectrum (RingOfIntegers K) => p.adicCompletionIntegers K) cofinite a)
  map_one' := by
    refine Prod.ext rfl ?_
    apply DFunLike.ext
    intro p
    rfl
  map_mul' _ _ := by
    refine Prod.ext (one_mul (1 : InfiniteAdeleRing K)).symm ?_
    apply DFunLike.ext
    intro p
    rfl

private theorem continuous_finiteIntegralAdeleHom (K : Type*) [Field K] [NumberField K] :
    Continuous (finiteIntegralAdeleHom K) := by
  have hopen (p : HeightOneSpectrum (RingOfIntegers K)) :
      IsOpen (p.adicCompletionIntegers K : Set (p.adicCompletion K)) :=
    Valued.isOpen_valuationSubring (p.adicCompletion K)
  change Continuous (fun a : FiniteIntegralAdeleDomain K =>
    ((1 : InfiniteAdeleRing K), RestrictedProduct.structureMap
      (fun p : HeightOneSpectrum (RingOfIntegers K) => p.adicCompletion K)
      (fun p : HeightOneSpectrum (RingOfIntegers K) => p.adicCompletionIntegers K) cofinite a))
  exact continuous_const.prodMk (RestrictedProduct.isOpenEmbedding_structureMap hopen).continuous

private abbrev FiniteIntegralIdeleDomain (K : Type*) [Field K] [NumberField K] :=
  (p : HeightOneSpectrum (RingOfIntegers K)) -> Units (p.adicCompletionIntegers K)

private noncomputable def finiteIntegralIdeleHom (K : Type*) [Field K] [NumberField K] :
    MonoidHom (FiniteIntegralIdeleDomain K) (Units (AdeleRing (RingOfIntegers K) K)) :=
  (Units.map (finiteIntegralAdeleHom K)).comp (MulEquiv.piUnits.symm.toMonoidHom)

private theorem continuous_finiteIntegralIdeleHom (K : Type*) [Field K] [NumberField K] :
    Continuous (finiteIntegralIdeleHom K) := by
  let equiv : ContinuousMulEquiv (Units (FiniteIntegralAdeleDomain K))
      (FiniteIntegralIdeleDomain K) := ContinuousMulEquiv.piUnits
  exact (Units.continuous_map (continuous_finiteIntegralAdeleHom K)).comp equiv.symm.continuous

private noncomputable def localIntegralUnitOfValuationOne {K : Type*} [Field K] [NumberField K]
    {p : HeightOneSpectrum (RingOfIntegers K)} (a : Units (p.adicCompletion K))
    (ha : (Valued.v (a : p.adicCompletion K) : WithZero (Multiplicative Int)) = 1) :
    Units (p.adicCompletionIntegers K) where
  val := Subtype.mk a.val (le_of_eq ha)
  inv := Subtype.mk a.inv (by
    change (Valued.v ((Inv.inv a : Units (p.adicCompletion K)) : p.adicCompletion K) :
      WithZero (Multiplicative Int)) <= 1
    rw [Units.val_inv_eq_inv_val, Valuation.map_inv, ha, inv_one])
  val_inv := Subtype.ext a.val_inv
  inv_val := Subtype.ext a.inv_val

private theorem finiteIntegralIdeleHom_mulSingle {K : Type*} [Field K] [NumberField K]
    [DecidableEq (HeightOneSpectrum (RingOfIntegers K))]
    (p : HeightOneSpectrum (RingOfIntegers K)) (b : Units (p.adicCompletionIntegers K))
    (a : Units (p.adicCompletion K)) (hba : (b.val : p.adicCompletion K) = a.val) :
    finiteIntegralIdeleHom K (Pi.mulSingle p b) = localIdeleHom K p a := by
  apply Units.ext
  refine Prod.ext rfl ?_
  apply DFunLike.ext
  intro q
  have hleft : ((finiteIntegralIdeleHom K (Pi.mulSingle p b)).val).2 q =
      (((Pi.mulSingle p b : FiniteIntegralIdeleDomain K) q).val : q.adicCompletion K) := rfl
  have hright : ((localIdeleHom K p a).val).2 q =
      @Function.update (HeightOneSpectrum (RingOfIntegers K)) (fun v => v.adicCompletion K)
        (Classical.decEq _) (fun _ => 1) p a.val q := rfl
  rw [hleft, hright]
  by_cases hq : q = p
  case pos =>
    subst q
    rw [Pi.mulSingle_eq_same]
    let _ : DecidableEq (HeightOneSpectrum (RingOfIntegers K)) := Classical.decEq _
    simpa only [Function.update_self] using hba
  case neg =>
    rw [Pi.mulSingle_eq_of_ne hq]
    let _ : DecidableEq (HeightOneSpectrum (RingOfIntegers K)) := Classical.decEq _
    rw [Function.update_of_ne hq]
    rfl

/-- A continuous unitary Hecke character is unramified at almost every finite place. -/
theorem finite_heckeRamifiedPlaces {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) :
    Set.Finite {p : HeightOneSpectrum (RingOfIntegers K) | Not (HeckeUnramifiedAt chi p)} := by
  classical
  let phi : MonoidHom (FiniteIntegralIdeleDomain K) Circle :=
    chi.val.toMonoidHom.comp (finiteIntegralIdeleHom K)
  have hCont : Continuous (fun x : FiniteIntegralIdeleDomain K => (phi x : Complex)) :=
    continuous_subtype_val.comp (chi.val.continuous.comp (continuous_finiteIntegralIdeleHom K))
  apply Filter.eventually_cofinite.mp
  filter_upwards [eventually_single_eq_one_of_continuous phi hCont] with p hp
  intro a ha
  let b := localIntegralUnitOfValuationOne a ha
  have hEq : finiteIntegralIdeleHom K (Pi.mulSingle p b) = localIdeleHom K p a :=
    finiteIntegralIdeleHom_mulSingle p b a rfl
  rw [<- hEq]
  exact hp b

private theorem exists_unit_product_neighborhood {F : Type*} [Field F] [TopologicalSpace F]
    {R : ValuationSubring F} (U : Set (Units R)) (hU : Membership.mem (nhds 1) U) :
    exists A B : Set F, Membership.mem (nhds (1 : F)) A /\
      Membership.mem (nhds (1 : F)) B /\
      forall a : Units R, Membership.mem A (a.val : F) -> Membership.mem B (a.inv : F) ->
        Membership.mem U a := by
  let f : Units R -> Prod F F := fun a => ((a.val : F), (a.inv : F))
  have hval : Topology.IsEmbedding (fun x : R => (x : F)) :=
    Topology.IsEmbedding.subtypeVal
  have hEmb : Topology.IsEmbedding f :=
    (hval.prodMap (hval.comp MulOpposite.opHomeomorph.symm.isEmbedding)).comp
      Units.isEmbedding_embedProduct
  have hpull : Membership.mem (Filter.comap f (nhds ((1 : F), (1 : F)))) U := by
    change Membership.mem (Filter.comap f (nhds (f 1))) U
    rwa [<- hEmb.isInducing.nhds_eq_comap 1]
  choose V hV hpre using Filter.mem_comap.mp hpull
  rw [nhds_prod_eq] at hV
  choose A hA B hB hsub using Filter.mem_prod_iff.mp hV
  exact Exists.intro A (Exists.intro B (And.intro hA (And.intro hB
    (fun a ha hb => hpre (hsub (And.intro ha hb))))))

private theorem exists_finite_valuation_ball_in_nhds_one {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (U : Set (p.adicCompletion K))
    (hU : Membership.mem (nhds (1 : p.adicCompletion K)) U) :
    exists gamma : WithZero (Multiplicative Int), 0 < gamma /\
      forall a : p.adicCompletion K, Valued.v (a - 1) < gamma -> Membership.mem U a := by
  choose g hg using Valued.mem_nhds.mp hU
  refine Exists.intro g.val.embedding ?_
  constructor
  case left =>
    exact bot_lt_iff_ne_bot.mpr ((map_ne_zero _).mpr g.ne_zero)
  case right =>
    intro a ha
    exact hg ((Valuation.restrict_lt_iff_lt_embedding Valued.v).mpr ha)

section LocalValuation

variable {K : Type*} [Field K] [NumberField K]
variable {p : HeightOneSpectrum (RingOfIntegers K)}

local notation "Fv" => p.adicCompletion K
local notation "Ov" => p.adicCompletionIntegers K
local notation "Vv" => (Valued.v : Valuation Fv (WithZero (Multiplicative Int)))

private theorem valuation_of_integral_unit_eq_one (u : Units Ov) :
    Vv (u.val : Fv) = 1 := by
  have hv : Vv (u.val : Fv) <= 1 := u.val.property
  have hi : Vv (u.inv : Fv) <= 1 := u.inv.property
  have hp : (u.val : Fv) * (u.inv : Fv) = 1 :=
    congrArg (fun x : Ov => (x : Fv)) u.val_inv
  apply le_antisymm hv
  calc
    1 = Vv (u.val : Fv) * Vv (u.inv : Fv) := by
      rw [<- map_mul, hp, map_one]
    _ <= Vv (u.val : Fv) * 1 := by gcongr
    _ = _ := mul_one _

private theorem valuation_integral_unit_inv_sub_one (u : Units Ov) :
    Vv ((u.inv : Fv) - 1) = Vv ((u.val : Fv) - 1) := by
  have hp : (u.val : Fv) * (u.inv : Fv) = 1 :=
    congrArg (fun x : Ov => (x : Fv)) u.val_inv
  have hi : Vv (u.inv : Fv) = 1 := valuation_of_integral_unit_eq_one (Inv.inv u)
  have hsub : (u.inv : Fv) - 1 = -(((u.val : Fv) - 1) * (u.inv : Fv)) := by
    calc
      _ = (u.inv : Fv) - (u.val : Fv) * (u.inv : Fv) := by rw [hp]
      _ = _ := by ring
  rw [hsub, Valuation.map_neg, map_mul, hi, mul_one]

private theorem valuation_pow_sub_one_lt (a : Fv) (ha : Vv a = 1)
    {gamma : WithZero (Multiplicative Int)} (hpos : 0 < gamma)
    (hab : Vv (a - 1) < gamma) (n : Nat) :
    Vv (a ^ n - 1) < gamma := by
  induction n with
  | zero => simpa using hpos
  | succ n ih =>
    have hsub : a ^ (n + 1) - 1 = (a ^ n - 1) * a + (a - 1) := by ring
    rw [hsub]
    apply Valuation.map_add_lt
    case hx =>
      rw [map_mul, ha, mul_one]
      exact ih
    case hy =>
      exact hab

end LocalValuation

/-- A Hecke character is trivial on the local units congruent to one at the given depth. -/
def HeckeTrivialAtDepth {K : Type*} [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat) : Prop :=
  forall a : Units (p.adicCompletion K), (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) (a : p.adicCompletion K) = 1 ->
    (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) ((a : p.adicCompletion K) - 1) <=
      ((Multiplicative.ofAdd (-(n : Int)) : Multiplicative Int) : WithZero (Multiplicative Int)) ->
    chi.val (localIdeleHom K p a) = 1

/-- A local component is trivial on some principal congruence subgroup. -/
theorem exists_heckeTrivialAtDepth {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K)
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    exists n : Nat, HeckeTrivialAtDepth chi p n := by
  classical
  let v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
  let localChar : MonoidHom (Units (p.adicCompletionIntegers K)) Circle :=
    (chi.val.toMonoidHom.comp (finiteIntegralIdeleHom K)).comp
      (MonoidHom.mulSingle (fun q => Units (q.adicCompletionIntegers K)) p)
  have hsingle : Continuous
      (fun b : Units (p.adicCompletionIntegers K) => (Pi.mulSingle p b : FiniteIntegralIdeleDomain K)) := by
    apply continuous_pi
    intro q
    by_cases hq : q = p
    case pos =>
      subst q
      simp only [Pi.mulSingle_eq_same]
      exact continuous_id
    case neg =>
      simpa only [Pi.mulSingle_eq_of_ne hq] using
        (continuous_const : Continuous (fun _ : Units (p.adicCompletionIntegers K) => (1 : Units (q.adicCompletionIntegers K))))
  have hchar : Continuous (fun b : Units (p.adicCompletionIntegers K) => (localChar b : Complex)) :=
    continuous_subtype_val.comp (chi.val.continuous.comp
      ((continuous_finiteIntegralIdeleHom K).comp hsingle))
  let U : Set (Units (p.adicCompletionIntegers K)) := {b | (1 : Real) / 2 < (localChar b : Complex).re}
  have hU : Membership.mem (nhds 1) U := by
    apply (isOpen_lt continuous_const (Complex.continuous_re.comp hchar)).mem_nhds
    change (1 : Real) / 2 < (localChar 1 : Complex).re
    rw [map_one]
    norm_num
  choose A B hA hB hUsub using exists_unit_product_neighborhood U hU
  choose ga hga hAsub using exists_finite_valuation_ball_in_nhds_one p A hA
  choose gb hgb hBsub using exists_finite_valuation_ball_in_nhds_one p B hB
  let g := min ga gb
  have hg : 0 < g := lt_min hga hgb
  choose t ht using WithZero.ne_zero_iff_exists.mp (ne_of_gt hg)
  choose n hn using exists_nat_gt (-Multiplicative.toAdd t)
  have hnt : @LT.lt (Multiplicative Int) (@instLTMultiplicative Int Int.instLTInt)
      (Multiplicative.ofAdd (-(n : Int))) t := by
    change -(n : Int) < Multiplicative.toAdd t
    simpa only [neg_neg] using neg_lt_neg hn
  have hnlt : ((Multiplicative.ofAdd (-(n : Int)) : Multiplicative Int) :
      WithZero (Multiplicative Int)) < g := by
    rw [<- ht]
    exact (@WithZero.coe_lt_coe (Multiplicative Int) (@instLTMultiplicative Int Int.instLTInt)
      (Multiplicative.ofAdd (-(n : Int))) t).mpr hnt
  refine Exists.intro n ?_
  intro a ha hdepth
  let b := localIntegralUnitOfValuationOne a ha
  have hMap : finiteIntegralIdeleHom K (Pi.mulSingle p b) = localIdeleHom K p a :=
    finiteIntegralIdeleHom_mulSingle p b a rfl
  rw [<- hMap]
  change localChar b = 1
  apply Subtype.ext
  change (localChar b : Complex) = 1
  apply complex_eq_one_of_unitNorm_of_re_pow (Circle.norm_coe _)
  intro j
  have hb : v ((b.val : p.adicCompletion K) - 1) < g := lt_of_le_of_lt hdepth hnlt
  have hj : v (((b ^ j).val : p.adicCompletion K) - 1) < g := by
    rw [Units.val_pow_eq_pow_val]
    change v ((b.val : p.adicCompletion K) ^ j - 1) < g
    exact valuation_pow_sub_one_lt _ (valuation_of_integral_unit_eq_one b) hg hb j
  have hjInv : v (((b ^ j).inv : p.adicCompletion K) - 1) < g := by
    rw [valuation_integral_unit_inv_sub_one]
    exact hj
  have hUj : Membership.mem U (b ^ j) :=
    hUsub _ (hAsub _ (hj.trans_le (min_le_left _ _)))
      (hBsub _ (hjInv.trans_le (min_le_right _ _)))
  change (1 : Real) / 2 < (localChar (b ^ j) : Complex).re at hUj
  simpa only [map_pow, Circle.coe_pow] using hUj

/-- The least depth at which the local component is trivial. -/
noncomputable def heckeConductorExponent {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K)) : Nat := by
  classical
  exact Nat.find (exists_heckeTrivialAtDepth chi p)

theorem heckeTrivialAtDepth_conductorExponent {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K)) :
    HeckeTrivialAtDepth chi p (heckeConductorExponent chi p) := by
  classical
  exact Nat.find_spec (exists_heckeTrivialAtDepth chi p)

theorem heckeConductorExponent_le {K : Type*} [Field K] [NumberField K]
    {chi : UnitaryHeckeCharacter K} {p : HeightOneSpectrum (RingOfIntegers K)}
    {n : Nat} (h : HeckeTrivialAtDepth chi p n) :
    heckeConductorExponent chi p <= n := by
  classical
  exact Nat.find_min' (exists_heckeTrivialAtDepth chi p) h

theorem heckeConductorExponent_eq_zero_iff {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K)) :
    heckeConductorExponent chi p = 0 <-> HeckeUnramifiedAt chi p := by
  constructor
  case mp =>
    intro hz a ha
    have h := heckeTrivialAtDepth_conductorExponent chi p
    rw [hz] at h
    apply h a ha
    let v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
    change v ((a : p.adicCompletion K) - 1) <= 1
    exact v.map_sub_le ha.le (by rw [map_one])
  case mpr =>
    intro h
    exact Nat.eq_zero_of_le_zero (heckeConductorExponent_le (fun a ha _ => h a ha))

/-- The conductor ideal is the product of the ramified primes to their local exponents. -/
noncomputable def heckeConductorIdeal {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) : Ideal (RingOfIntegers K) := by
  classical
  exact (finite_heckeRamifiedPlaces chi).toFinset.prod
    (fun p => p.asIdeal ^ heckeConductorExponent chi p)

theorem heckeConductorIdeal_absNorm_pos {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) :
    0 < Ideal.absNorm (heckeConductorIdeal chi) := by
  classical
  rw [heckeConductorIdeal, map_prod]
  apply Finset.prod_pos
  intro p _
  rw [map_pow]
  exact pow_pos (Nat.pos_of_ne_zero (fun hz => p.ne_bot (Ideal.absNorm_eq_zero_iff.mp hz))) _

private theorem heckeTrivialAtDepth_inverse_iff {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat) :
    HeckeTrivialAtDepth (unitaryHeckeInverse chi) p n <-> HeckeTrivialAtDepth chi p n := by
  change (forall a : Units (p.adicCompletion K), _ -> _ ->
    Inv.inv (chi.val (localIdeleHom K p a)) = 1) <-> _
  simp only [HeckeTrivialAtDepth, inv_eq_one]

theorem heckeConductorExponent_inverse {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K)) :
    heckeConductorExponent (unitaryHeckeInverse chi) p = heckeConductorExponent chi p := by
  refine le_antisymm ?left_le ?right_le
  case left_le =>
    exact heckeConductorExponent_le ((heckeTrivialAtDepth_inverse_iff chi p _).mpr
      (heckeTrivialAtDepth_conductorExponent chi p))
  case right_le =>
    exact heckeConductorExponent_le ((heckeTrivialAtDepth_inverse_iff chi p _).mp
      (heckeTrivialAtDepth_conductorExponent (unitaryHeckeInverse chi) p))

theorem heckeConductorIdeal_inverse {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) :
    heckeConductorIdeal (unitaryHeckeInverse chi) = heckeConductorIdeal chi := by
  classical
  unfold heckeConductorIdeal
  refine Finset.prod_congr ?same_support ?same_factor
  case same_support =>
    apply Finset.ext
    intro p
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, <- heckeConductorExponent_eq_zero_iff,
      heckeConductorExponent_inverse]
  case same_factor =>
    intro p _
    rw [heckeConductorExponent_inverse]

/-- The arithmetic conductor of the rank-one standard completion over the base field. -/
noncomputable def heckeArithmeticConductor {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) : Real :=
  ((NumberField.discr K).natAbs : Real) * (Ideal.absNorm (heckeConductorIdeal chi) : Real)

theorem heckeArithmeticConductor_pos {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) :
    0 < heckeArithmeticConductor chi :=
  mul_pos (Nat.cast_pos.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)))
    (Nat.cast_pos.mpr (heckeConductorIdeal_absNorm_pos chi))

theorem heckeArithmeticConductor_inverse {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) :
    heckeArithmeticConductor (unitaryHeckeInverse chi) = heckeArithmeticConductor chi := by
  rw [heckeArithmeticConductor, heckeConductorIdeal_inverse]
  rfl

end Robin1984.GRH
