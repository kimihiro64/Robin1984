import Robin1984.GRH.HeckeIdeleClassCompactness

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Uniform decay of adelic theta sums on compact idele representatives in Tate's thesis.
- Formalization note: Combines a common denominator on compact finite supports with archimedean Schwartz decay and summability over one lattice.
- PROVENANCE-END
-/

/-!
# Uniform decay of the Tate theta sum

A single principal denominator works over any compact family of finite
idele translates of a compact finite test support. The resulting theta
sum is dominated by a summable power on the integer lattice, uniformly
over the compact norm-one representatives.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev TateFiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

/-- Every compact set of finite adeles has a common nonzero integral denominator. -/
theorem exists_commonDenominator_of_isCompact_finiteAdeles
    (S : Set (TateFiniteAdeles K)) (hS : IsCompact S) :
    Exists (fun d : RingOfIntegers K => And (Not (d = 0))
      (forall a : TateFiniteAdeles K, Membership.mem S a ->
        forall p : HeightOneSpectrum (RingOfIntegers K),
          Membership.mem (p.adicCompletionIntegers K)
            (a p * algebraMap (RingOfIntegers K) (p.adicCompletion K) d))) := by
  let R := RingOfIntegers K
  let F := TateFiniteAdeles K
  let A := Set.ofPred (fun a : F => forall p : HeightOneSpectrum R,
    Membership.mem (p.adicCompletionIntegers K) (a p))
  let D := Subtype (fun d : R => Not (d = 0))
  let V (d : D) : Set F := Set.preimage (fun a => a * algebraMap R F d.val) A
  have hA : IsOpen A :=
    RestrictedProduct.isOpen_forall_mem
      (R := fun p : HeightOneSpectrum R => p.adicCompletion K)
      (A := fun p => (p.adicCompletionIntegers K : Set (p.adicCompletion K)))
      (fun p => Valued.isOpen_valuationSubring (p.adicCompletion K))
  have hV (d : D) : IsOpen (V d) :=
    hA.preimage (continuous_id.mul continuous_const)
  have hCover : Set.Subset S (Set.iUnion V) := by
    intro a _
    choose d hd using exists_finiteAdele_integral_multiple a
    exact Set.mem_iUnion.mpr (Exists.intro (Subtype.mk d hd.1) hd.2)
  choose T hT using hS.elim_finite_subcover V hV hCover
  let d := T.prod (fun x : D => x.val)
  refine Exists.intro d (And.intro (Finset.prod_ne_zero_iff.mpr (fun x _ => x.property)) ?_)
  intro a ha p
  choose x hx using Set.mem_iUnion.mp (hT ha)
  choose hxT hxV using Set.mem_iUnion.mp hx
  have hMul : Dvd.dvd x.val d := Finset.dvd_prod_of_mem (fun x : D => x.val) hxT
  choose y hy using hMul
  have hLocal := (show Membership.mem A (a * algebraMap R F x.val) from hxV) p
  let e := algebraMap R (p.adicCompletion K)
  change Membership.mem (p.adicCompletionIntegers K) (a p * e x.val) at hLocal
  change Membership.mem (p.adicCompletionIntegers K) (a p * e d)
  rw [hy, map_mul, <- mul_assoc]
  exact (p.adicCompletionIntegers K).mul_mem _ _ hLocal
    (HeightOneSpectrum.coe_algebraMap_mem R K p y)

/-- The principal points meeting compact families of translated finite test supports share one denominator. -/
theorem exists_commonDenominator_of_compact_finiteIdele_test
    (C : Set (Units (TateFiniteAdeles K))) (hC : IsCompact C)
    (S : Set (TateFiniteAdeles K)) (hS : IsCompact S) :
    Exists (fun d : RingOfIntegers K => And (Not (d = 0))
      (forall a : Units (TateFiniteAdeles K), Membership.mem C a ->
        forall x : K, Membership.mem S (a.val * algebraMap K (TateFiniteAdeles K) x) ->
          Exists (fun z : RingOfIntegers K =>
            algebraMap (RingOfIntegers K) K z = x * algebraMap (RingOfIntegers K) K d))) := by
  let R := RingOfIntegers K
  let F := TateFiniteAdeles K
  let W := Set.image (fun b : Prod (Units F) F => b.1.inv * b.2) (Set.prod C S)
  have hW : IsCompact W :=
    (hC.prod hS).image ((Units.continuous_coe_inv.comp continuous_fst).mul continuous_snd)
  choose d hd using exists_commonDenominator_of_isCompact_finiteAdeles W hW
  refine Exists.intro d (And.intro hd.1 ?_)
  intro a ha x hx
  let g := algebraMap K F
  have hxW : Membership.mem W (g x) := by
    refine Exists.intro (Prod.mk a (a.val * g x)) (And.intro (And.intro ha hx) ?_)
    change a.inv * (a.val * g x) = g x
    rw [<- mul_assoc, a.inv_val, one_mul]
  have hInt := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := R) K
    (x * algebraMap R K d) (by
      intro p
      let e := algebraMap K (p.adicCompletion K)
      have hp := hd.2 (g x) hxW p
      change Valued.v (e x * algebraMap R (p.adicCompletion K) d) <=
        (1 : WithZero (Multiplicative Int)) at hp
      have hEq : e (x * algebraMap R K d) = e x * algebraMap R (p.adicCompletion K) d := by
        rw [map_mul, IsScalarTower.algebraMap_apply R K (p.adicCompletion K) d]
      rw [<- hEq] at hp
      change Valued.v ((x * algebraMap R K d : K) : p.adicCompletion K) <=
        (1 : WithZero (Multiplicative Int)) at hp
      rw [HeightOneSpectrum.adicCompletion.valued_coe] at hp
      exact hp)
  exact hInt

omit [NumberField K] in
private theorem continuous_heckeInfiniteAdele_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  change Continuous (fun a : InfiniteAdeleRing K => Prod.mk (E a).1 (E a).2)
  apply Continuous.prodMk
  . apply continuous_pi
    intro v
    let k := InfinitePlace.Completion.isometryEquivRealOfIsReal v.property
    change Continuous (fun a : InfiniteAdeleRing K => k (a v.val))
    exact k.continuous.comp (continuous_apply v.val)
  . apply continuous_pi
    intro v
    let k := InfinitePlace.Completion.isometryEquivComplexOfIsComplex v.property
    change Continuous (fun a : InfiniteAdeleRing K => k (a v.val))
    exact k.continuous.comp (continuous_apply v.val)

/-- Multiplication by a compact family of infinite ideles has a uniform positive lower norm bound. -/
theorem exists_uniform_heckeInfiniteIdele_normLower
    (C : Set (Units (InfiniteAdeleRing K))) (hC : IsCompact C) :
    Exists (fun M : Real => And (0 < M)
      (forall b : Units (InfiniteAdeleRing K), Membership.mem C b ->
        forall x : NumberField.mixedEmbedding.mixedSpace K,
          norm x <= M * norm ((InfiniteAdeleRing.ringEquiv_mixedSpace K b.val) * x))) := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let F := Set.image (fun b : Units (InfiniteAdeleRing K) => E b.inv) C
  have hF : IsCompact F :=
    hC.image (continuous_heckeInfiniteAdele_mixedSpace.comp Units.continuous_coe_inv)
  choose T hT using isBounded_iff_forall_norm_le.mp hF.isBounded
  let M := max T 1
  refine Exists.intro M (And.intro (zero_lt_one.trans_le (le_max_right T 1)) ?_)
  intro b hb x
  have hTb : norm (E b.inv) <= M :=
    (hT _ (Exists.intro b (And.intro hb rfl))).trans (le_max_left T 1)
  calc
    norm x = norm (E b.inv * (E b.val * x)) := by
      rw [<- mul_assoc, <- map_mul, b.inv_val, map_one, one_mul]
    _ <= norm (E b.inv) * norm (E b.val * x) := norm_mul_le _ _
    _ <= M * norm (E b.val * x) := mul_le_mul_of_nonneg_right hTb (norm_nonneg _)

private noncomputable def heckeInfiniteExpSection (K : Type*) [Field K] [NumberField K]
    (t : Real) : Units (InfiniteAdeleRing K) :=
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let c := Real.exp (t / (Module.finrank Rat K : Real))
  let f := E.symm.toRingHom.comp (algebraMap Real (NumberField.mixedEmbedding.mixedSpace K))
  Units.map f.toMonoidHom (Units.mk0 c (Real.exp_pos _).ne')

/-- The idele with finite component one and common positive archimedean scale of logarithmic norm t. -/
noncomputable def heckeIdelicExpSection (K : Type*) [Field K] [NumberField K]
    (t : Real) : Units (AdeleRing (RingOfIntegers K) K) :=
  MulEquiv.prodUnits.symm (Prod.mk (heckeInfiniteExpSection K t) 1)

/-- The exponential section lifts the real logarithmic parameter to an idele of the prescribed norm. -/
theorem heckeIdelicNorm_expSection (t : Real) :
    heckeIdelicNorm (heckeIdelicExpSection K t) = Real.exp t := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let n := Module.finrank Rat K
  let c := Real.exp (t / (n : Real))
  change heckeInfiniteIdeleNorm (heckeInfiniteExpSection K t) *
    heckeFiniteIdeleNorm (1 : Units (TateFiniteAdeles K)) = Real.exp t
  rw [map_one, mul_one, <- mixedEmbedding_norm_infiniteIdele]
  change NumberField.mixedEmbedding.norm
    (E (E.symm (algebraMap Real (NumberField.mixedEmbedding.mixedSpace K) c))) = Real.exp t
  rw [E.apply_symm_apply, Algebra.algebraMap_eq_smul_one,
    NumberField.mixedEmbedding.norm_smul, abs_of_pos (Real.exp_pos _), map_one, mul_one]
  change Real.exp (t / (n : Real)) ^ n = Real.exp t
  have hn : Not ((n : Real) = 0) := by
    have h : 0 < (n : Real) := by
      exact_mod_cast (Module.finrank_pos : 0 < Module.finrank Rat K)
    exact h.ne'
  rw [<- Real.exp_nat_mul]
  congr 1
  calc
    (n : Real) * (t / (n : Real)) = t * ((n : Real) / (n : Real)) := by
      rw [<- mul_div_assoc, <- mul_div_assoc, mul_comm (n : Real) t]
    _ = t := by rw [div_self hn, mul_one]

/-- Schwartz seminorms bound the scaled archimedean factors uniformly on a compact family of infinite ideles. -/
theorem exists_uniform_heckeInfiniteIdele_schwartzDecay
    (C : Set (Units (InfiniteAdeleRing K))) (hC : IsCompact C)
    (f : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) Complex) (N : Nat) :
    Exists (fun D : Real => And (0 <= D)
      (forall b : Units (InfiniteAdeleRing K), Membership.mem C b ->
        forall (x : NumberField.mixedEmbedding.mixedSpace K) (c : Real), 0 <= c ->
          c ^ N * norm x ^ N *
            norm (f (HSMul.hSMul c (InfiniteAdeleRing.ringEquiv_mixedSpace K b.val * x))) <= D)) := by
  choose M hM using exists_uniform_heckeInfiniteIdele_normLower C hC
  let A := SchwartzMap.seminorm Real N 0 f
  refine Exists.intro (M ^ N * A) (And.intro (mul_nonneg (pow_nonneg hM.1.le _) (apply_nonneg _ _)) ?_)
  intro b hb x c hc
  let y := InfiniteAdeleRing.ringEquiv_mixedSpace K b.val * x
  let z := HSMul.hSMul c y
  have hz : norm z = c * norm y := by
    change norm (HSMul.hSMul c y) = c * norm y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  have hBase : c * norm x <= M * norm z := by
    rw [hz, mul_left_comm M c]
    exact mul_le_mul_of_nonneg_left (hM.2 b hb x) hc
  have hPow : (c * norm x) ^ N <= (M * norm z) ^ N := by
    gcongr
  calc
    c ^ N * norm x ^ N * norm (f z) = (c * norm x) ^ N * norm (f z) := by rw [mul_pow]
    _ <= (M * norm z) ^ N * norm (f z) := mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
    _ = M ^ N * (norm z ^ N * norm (f z)) := by rw [mul_pow, mul_assoc]
    _ <= M ^ N * A := mul_le_mul_of_nonneg_left
      (SchwartzMap.norm_pow_mul_le_seminorm Real f N z) (pow_nonneg hM.1.le _)

/-- The absolute value of a single nonzero principal term with separated archimedean and finite tests. -/
noncomputable def heckeTateThetaAbsTerm
    (f : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) Complex)
    (T : TateFiniteAdeles K -> Complex) (a : Units (InfiniteAdeleRing K))
    (b : Units (TateFiniteAdeles K)) (c : Real) (x : K) : Real :=
  if x = 0 then 0 else
    norm (f (HSMul.hSMul c
      (InfiniteAdeleRing.ringEquiv_mixedSpace K a.val * NumberField.mixedEmbedding K x))) *
    norm (T (b.val * algebraMap K (TateFiniteAdeles K) x))

/-- The sum of absolute principal terms is summable and decays uniformly with the archimedean scale. -/
theorem exists_uniform_heckeTateTheta_tsum_bound
    (CI : Set (Units (InfiniteAdeleRing K))) (hCI : IsCompact CI)
    (CF : Set (Units (TateFiniteAdeles K))) (hCF : IsCompact CF)
    (f : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) Complex)
    (T : TateFiniteAdeles K -> Complex) (S : Set (TateFiniteAdeles K)) (hS : IsCompact S)
    (hST : forall z : TateFiniteAdeles K, Not (Membership.mem S z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z : TateFiniteAdeles K, norm (T z) <= B)
    (N : Nat) (hN : (Module.finrank Int (NumberField.mixedEmbedding.integerLattice K) : Real) < (N : Real)) :
    Exists (fun D : Real => And (0 <= D)
      (forall (a : Units (InfiniteAdeleRing K)), Membership.mem CI a ->
        forall (b : Units (TateFiniteAdeles K)), Membership.mem CF b ->
          forall c : Real, 0 < c ->
            And (Summable (heckeTateThetaAbsTerm f T a b c))
              (tsum (heckeTateThetaAbsTerm f T a b c) <= D * Inv.inv (c ^ N)))) := by
  let R := RingOfIntegers K
  let L := NumberField.mixedEmbedding.integerLattice K
  let e := NumberField.mixedEmbedding K
  let k := algebraMap R K
  have hk : Function.Injective k := IsFractionRing.injective R K
  choose d hd using exists_commonDenominator_of_compact_finiteIdele_test CF hCF S hS
  choose A hA using exists_uniform_heckeInfiniteIdele_schwartzDecay CI hCI f N
  have hd0 : Not (k d = 0) := fun h => hd.1 (hk (h.trans (map_zero k).symm))
  let j (z : R) : K := k z / k d
  have hj : Function.Injective j := by
    intro z w h
    apply hk
    exact (div_left_inj' hd0).mp h
  let i (z : R) : L := Subtype.mk (e (k z)) (Exists.intro z rfl)
  have hi : Function.Injective i := by
    intro z w h
    exact hk (e.injective (congrArg Subtype.val h))
  let w (z : R) : Real := Inv.inv (norm (e (k z)) ^ N)
  have hw (z : R) : 0 <= w z := inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)
  have hSum : Summable w := by
    have hs := (ZLattice.summable_norm_rpow L (-(N : Real)) (neg_lt_neg hN)).comp_injective hi
    apply hs.congr
    intro z
    change (norm (e (k z))) ^ (-(N : Real)) = _
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  let Q := A * (norm (e (k d)) ^ N * B)
  have hQ : 0 <= Q := mul_nonneg hA.1 (mul_nonneg (pow_nonneg (norm_nonneg _) _) hB)
  refine Exists.intro (Q * tsum w) (And.intro (mul_nonneg hQ (tsum_nonneg hw)) ?_)
  intro a ha b hb c hc
  let g := heckeTateThetaAbsTerm f T a b c
  have hg (x : K) : 0 <= g x := by
    change 0 <= heckeTateThetaAbsTerm f T a b c x
    rw [heckeTateThetaAbsTerm]
    split
    . exact le_rfl
    . exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hZero (x : K) (hx : Not (Membership.mem (Set.range j) x)) : g x = 0 := by
    have hxS : Not (Membership.mem S (b.val * algebraMap K (TateFiniteAdeles K) x)) := by
      intro hs
      choose z hz using hd.2 b hb x hs
      apply hx
      exact Exists.intro z ((div_eq_iff hd0).mpr hz)
    change heckeTateThetaAbsTerm f T a b c x = 0
    rw [heckeTateThetaAbsTerm, hST _ hxS, norm_zero, mul_zero]
    exact ite_self _
  let q := Q * Inv.inv (c ^ N)
  have hq : 0 <= q := mul_nonneg hQ (inv_nonneg.mpr (pow_nonneg hc.le _))
  have hTerm (z : R) : g (j z) <= q * w z := by
    by_cases hz : z = 0
    . have hx : j z = 0 := by
        change k z / k d = _
        rw [hz, map_zero, zero_div]
      change heckeTateThetaAbsTerm f T a b c (j z) <= _
      rw [heckeTateThetaAbsTerm, if_pos hx]
      exact mul_nonneg hq (hw z)
    . let x := j z
      have hx : Not (x = 0) := div_ne_zero ((map_ne_zero_iff k hk).mpr hz) hd0
      let u := norm (f (HSMul.hSMul c (InfiniteAdeleRing.ringEquiv_mixedSpace K a.val * e x)))
      let v := norm (T (b.val * algebraMap K (TateFiniteAdeles K) x))
      have hu : 0 <= u := norm_nonneg _
      have hv : 0 <= v := norm_nonneg _
      have hgu : g x = u * v := by
        change heckeTateThetaAbsTerm f T a b c x = _
        rw [heckeTateThetaAbsTerm, if_neg hx]
      have hZ : e (k z) = e x * e (k d) := by
        rw [<- map_mul]
        congr 1
        exact (div_eq_iff hd0).mp (show k z / k d = x from rfl)
      have hLe : norm (e (k z)) <= norm (e x) * norm (e (k d)) := by
        rw [hZ]
        exact norm_mul_le _ _
      have hPow : norm (e (k z)) ^ N <= norm (e x) ^ N * norm (e (k d)) ^ N := by
        rw [<- mul_pow]
        gcongr
      have hD : c ^ N * norm (e x) ^ N * u <= A := hA.2 a ha (e x) c hc.le
      have hP : (c ^ N * norm (e (k z)) ^ N) * g x <= Q := by
        calc
          _ = c ^ N * norm (e (k z)) ^ N * (u * v) := by rw [hgu]
          _ <= c ^ N * (norm (e x) ^ N * norm (e (k d)) ^ N) * (u * v) := by gcongr
          _ = (c ^ N * norm (e x) ^ N * u) * (norm (e (k d)) ^ N * v) := by ring
          _ <= A * (norm (e (k d)) ^ N * B) :=
            mul_le_mul hD (mul_le_mul_of_nonneg_left (hBT _) (pow_nonneg (norm_nonneg _) _))
              (mul_nonneg (pow_nonneg (norm_nonneg _) _) hv) hA.1
      have hcN : 0 < c ^ N := pow_pos hc _
      have hzN : 0 < norm (e (k z)) ^ N := pow_pos
        (norm_pos_iff.mpr ((map_ne_zero_iff e e.injective).mpr ((map_ne_zero_iff k hk).mpr hz))) _
      have hinv (y : Real) (hy : Not (y = 0)) : y * Inv.inv y = 1 := by
        rw [<- div_eq_mul_inv, div_self hy]
      apply le_of_mul_le_mul_left _ (mul_pos hcN hzN)
      calc
        _ <= Q := hP
        _ = (c ^ N * norm (e (k z)) ^ N) * (q * w z) := by
          change Q = (c ^ N * norm (e (k z)) ^ N) *
            ((Q * Inv.inv (c ^ N)) * Inv.inv (norm (e (k z)) ^ N))
          symm
          calc
            _ = Q * (c ^ N * Inv.inv (c ^ N)) *
                (norm (e (k z)) ^ N * Inv.inv (norm (e (k z)) ^ N)) := by ring
            _ = Q := by rw [hinv _ hcN.ne', hinv _ hzN.ne', mul_one, mul_one]
  have hM : Summable (fun z : R => q * w z) := hSum.mul_left _
  have hG : Summable (fun z : R => g (j z)) :=
    Summable.of_nonneg_of_le (fun z => hg (j z)) hTerm hM
  have hSu : Summable g := (hj.summable_iff hZero).mp hG
  refine And.intro hSu ?_
  have hSupp : Set.Subset (Function.support g) (Set.range j) := by
    intro x hx
    by_contra hn
    exact hx (hZero x hn)
  calc
    tsum g = tsum (fun z : R => g (j z)) := (hj.tsum_eq hSupp).symm
    _ <= tsum (fun z : R => q * w z) := hG.tsum_le_tsum hTerm hM
    _ = (Q * tsum w) * Inv.inv (c ^ N) := by
      rw [tsum_mul_left]
      change (Q * Inv.inv (c ^ N)) * tsum w = _
      ring

private theorem norm_heckeLocalAdditiveTateTest_le_one
    (p : HeightOneSpectrum (RingOfIntegers K)) (chi : UnitaryHeckeCharacter K)
    (x : p.adicCompletion K) : norm (heckeLocalAdditiveTateTest p chi x) <= 1 := by
  rw [heckeLocalAdditiveTateTest]
  split
  . split <;> simp
  . split
    . rw [Circle.norm_coe]
    . simp

/-- A unitary Hecke test takes values of absolute value at most one. -/
theorem norm_heckeFiniteAdditiveTateTest_le_one
    (chi : UnitaryHeckeCharacter K) (x : TateFiniteAdeles K) :
    norm (heckeFiniteAdditiveTateTest chi x) <= 1 := by
  rw [heckeFiniteAdditiveTateTest]
  split
  . rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun p _ => norm_heckeLocalAdditiveTateTest_le_one p chi (x p))
  . rw [norm_zero]
    exact zero_le_one

/-- The absolute principal term at a norm-one idele and a prescribed logarithmic scale. -/
noncomputable def heckeTateThetaNormOneAbsTerm
    (f : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) Complex)
    (T : TateFiniteAdeles K -> Complex)
    (a : heckeNormOneIdeles K) (t : Real) (x : K) : Real :=
  let e : Homeomorph (Units (AdeleRing (RingOfIntegers K) K))
      (Prod (Units (InfiniteAdeleRing K)) (Units (TateFiniteAdeles K))) := Homeomorph.prodUnits
  let b := e a.val
  heckeTateThetaAbsTerm f T b.1 b.2
    (Real.exp (t / (Module.finrank Rat K : Real))) x

/-- The theta sum has a uniform exponential bound on compact representatives of every norm-one idele class. -/
theorem exists_uniform_heckeTateTheta_bound_on_normOne_representatives
    (f : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) Complex)
    (T : TateFiniteAdeles K -> Complex) (V : Set (TateFiniteAdeles K)) (hV : IsCompact V)
    (hVT : forall z : TateFiniteAdeles K, Not (Membership.mem V z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z : TateFiniteAdeles K, norm (T z) <= B)
    (N : Nat) (hN : (Module.finrank Int (NumberField.mixedEmbedding.integerLattice K) : Real) < (N : Real)) :
    Exists (fun S : Set (heckeNormOneIdeles K) => And (IsCompact S)
      (And (Set.image (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S = Set.univ)
        (Exists (fun D : Real => And (0 <= D)
          (forall a : heckeNormOneIdeles K, Membership.mem S a -> forall t : Real,
            And (Summable (heckeTateThetaNormOneAbsTerm f T a t))
              (tsum (heckeTateThetaNormOneAbsTerm f T a t) <= D *
                Real.exp (-(N : Real) * (t / (Module.finrank Rat K : Real))))))))) := by
  choose S hS using exists_compact_heckeNormOneIdeleRepresentatives K
  let e : Homeomorph (Units (AdeleRing (RingOfIntegers K) K))
      (Prod (Units (InfiniteAdeleRing K)) (Units (TateFiniteAdeles K))) := Homeomorph.prodUnits
  let aInf (a : heckeNormOneIdeles K) := (e a.val).1
  let aFin (a : heckeNormOneIdeles K) := (e a.val).2
  let I := Set.image aInf S
  let F := Set.image aFin S
  have hI : IsCompact I := hS.1.image (continuous_fst.comp (e.continuous.comp continuous_subtype_val))
  have hF : IsCompact F := hS.1.image (continuous_snd.comp (e.continuous.comp continuous_subtype_val))
  choose D hD using exists_uniform_heckeTateTheta_tsum_bound I hI F hF f T V hV hVT B hB hBT N hN
  refine Exists.intro S (And.intro hS.1 (And.intro hS.2 (Exists.intro D (And.intro hD.1 ?_))))
  intro a ha t
  have hInf : Membership.mem I (aInf a) := Exists.intro a (And.intro ha rfl)
  have hFin : Membership.mem F (aFin a) := Exists.intro a (And.intro ha rfl)
  have h := hD.2 (aInf a) hInf (aFin a) hFin _ (Real.exp_pos (t / (Module.finrank Rat K : Real)))
  refine And.intro h.1 ?_
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul]
  exact h.2

/-- The norm-one uniform bound applies to the finite test of every unitary Hecke character. -/
theorem exists_uniform_heckeCharacterTateTheta_bound_on_normOne_representatives
    (chi : UnitaryHeckeCharacter K)
    (f : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) Complex)
    (N : Nat) (hN : (Module.finrank Int (NumberField.mixedEmbedding.integerLattice K) : Real) < (N : Real)) :
    Exists (fun S : Set (heckeNormOneIdeles K) => And (IsCompact S)
      (And (Set.image (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range) S = Set.univ)
        (Exists (fun D : Real => And (0 <= D)
          (forall a : heckeNormOneIdeles K, Membership.mem S a -> forall t : Real,
            And (Summable (heckeTateThetaNormOneAbsTerm f (heckeFiniteAdditiveTateTest chi) a t))
              (tsum (heckeTateThetaNormOneAbsTerm f (heckeFiniteAdditiveTateTest chi) a t) <=
                D * Real.exp (-(N : Real) * (t / (Module.finrank Rat K : Real))))))))) := by
  refine exists_uniform_heckeTateTheta_bound_on_normOne_representatives f _ _
    isCompact_integralFiniteAdeles ?_ 1 zero_le_one (norm_heckeFiniteAdditiveTateTest_le_one chi) N hN
  intro z hz
  have hz' : Not (Membership.mem (heckeIntegralFiniteAdeles (K := K)) z) := hz
  rw [heckeFiniteAdditiveTateTest, if_neg hz']

end Robin1984.GRH
