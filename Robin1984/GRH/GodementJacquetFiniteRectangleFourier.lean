import Robin1984.GRH.GodementJacquetFiniteRectangleDilation
import Robin1984.GRH.HeckeTateFiniteFourier

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Fourier transforms of compact open cosets in Tate's thesis and in Godement and Jacquet, Zeta Functions of Simple Algebras.
- Formalization note: Proves compact support and a uniform Haar mass bound on the Fourier transform of a principal finite adelic coset.
- PROVENANCE-END
-/

/-!
# Fourier support of finite adelic cosets

The Fourier transform of a principal finite coset is supported in the trace
dual of its additive subgroup. The support lies in a compact set for
nonzero modulus, and the coset's additive Haar mass bounds the transform.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

private abbrev FF (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

variable {K : Type*} [Field K] [NumberField K]
  [MeasurableSpace (FF K)] [BorelSpace (FF K)]

omit [MeasurableSpace (FF K)] [BorelSpace (FF K)] in
/-- A principal finite coset indicator is invariant under translation by its subgroup. -/
private theorem principalCosetIndicator_add
    (a : FF K) (d : K) (b : FF K)
    (hb : Membership.mem (heckeScaledIntegralFiniteAdeles d) b) (z : FF K) :
    (heckeFiniteAdelePrincipalCoset a d).indicator (fun _ => (1 : Complex)) (z + b) =
      (heckeFiniteAdelePrincipalCoset a d).indicator (fun _ => (1 : Complex)) z := by
  let H := heckeScaledIntegralFiniteAdeles d
  let S := heckeFiniteAdelePrincipalCoset a d
  have h : Iff (Membership.mem S (z + b)) (Membership.mem S z) := by
    constructor
    . intro hz
      change Exists (fun v : FF K => And (Membership.mem H v) (a + v = z + b)) at hz
      choose v hv using hz
      change Exists (fun u : FF K => And (Membership.mem H u) (a + u = z))
      refine Exists.intro (v - b) (And.intro (H.sub_mem hv.1 hb) ?_)
      rw [<- add_sub_assoc, hv.2, add_sub_cancel_right]
    . intro hz
      change Exists (fun v : FF K => And (Membership.mem H v) (a + v = z)) at hz
      choose v hv using hz
      change Exists (fun u : FF K => And (Membership.mem H u) (a + u = z + b))
      refine Exists.intro (v + b) (And.intro (H.add_mem hv.1 hb) ?_)
      rw [<- add_assoc, hv.2]
  change S.indicator (fun _ => (1 : Complex)) (z + b) =
    S.indicator (fun _ => (1 : Complex)) z
  by_cases hz : Membership.mem S z
  . rw [Set.indicator_of_mem (h.mpr hz), Set.indicator_of_mem hz]
  . rw [Set.indicator_of_notMem (fun h' => hz (h.mp h')), Set.indicator_of_notMem hz]

/-- A principal finite coset has Fourier support in its reciprocal
dilation of the inverse different. This holds at every finite adelic point. -/
theorem heckeFiniteFourierIntegral_principalCoset_support
    (mu : Measure (FF K)) [mu.IsAddHaarMeasure]
    (a : FF K) (d : K) (D : Units (FF K))
    (hD : heckeFiniteIdeleFractionalIdeal D = DedekindZeta.Theta.differentFractionalIdeal K)
    (y : FF K)
    (hy : Not (heckeFiniteFourierIntegral mu
      ((heckeFiniteAdelePrincipalCoset a d).indicator (fun _ => (1 : Complex))) y = 0)) :
    Membership.mem (heckeIntegralFiniteAdeles (K := K)) (D.val * (algebraMap K (FF K) d * y)) := by
  let g := algebraMap K (FF K)
  apply (heckeFiniteAddChar_annihilator_iff_different_mul_integral D hD (g d * y)).mp
  intro x hx
  have hb : Membership.mem (heckeScaledIntegralFiniteAdeles d) (x * g d) :=
    AddSubgroup.mem_map.mpr (Exists.intro x (And.intro hx rfl))
  have h := heckeFiniteFourierIntegral_nonzero_annihilates_translation mu
    ((heckeFiniteAdelePrincipalCoset a d).indicator (fun _ => (1 : Complex)))
    (x * g d) y (principalCosetIndicator_add a d (x * g d) hb) hy
  rwa [mul_assoc] at h

/-- The Fourier transform of a principal finite coset vanishes outside a compact set. -/
theorem exists_compact_heckeFiniteFourierIntegral_principalCoset_support
    (mu : Measure (FF K)) [mu.IsAddHaarMeasure]
    (a : FF K) (d : RingOfIntegers K) (hd : Not (d = 0)) :
    Exists (fun V : Set (FF K) => And (IsCompact V)
      (forall y : FF K, Not (Membership.mem V y) ->
        heckeFiniteFourierIntegral mu ((heckeFiniteAdelePrincipalCoset a
          (algebraMap (RingOfIntegers K) K d)).indicator (fun _ => (1 : Complex))) y = 0)) := by
  let dd := algebraMap (RingOfIntegers K) K d
  let g := algebraMap K (FF K)
  let T := (heckeFiniteAdelePrincipalCoset a dd).indicator (fun _ => (1 : Complex))
  choose V hV using exists_compact_heckeFiniteChar_annihilator_cover d hd
  refine Exists.intro V (And.intro hV.1 ?_)
  intro y hy
  by_contra hZero
  apply hy
  apply hV.2 y
  intro x hx
  have hb : Membership.mem (heckeScaledIntegralFiniteAdeles dd) (x * g dd) :=
    AddSubgroup.mem_map.mpr (Exists.intro x (And.intro hx rfl))
  have h := heckeFiniteFourierIntegral_nonzero_annihilates_translation mu T
    (x * g dd) y (principalCosetIndicator_add a dd (x * g dd) hb) hZero
  rwa [mul_assoc] at h

omit [BorelSpace (FF K)] in
/-- A finite coset's additive Haar mass bounds its Fourier transform uniformly. -/
theorem norm_heckeFiniteFourierIntegral_principalCoset_le
    (mu : Measure (FF K)) [mu.IsAddHaarMeasure] (a : FF K) (d : K) (y : FF K) :
    norm (heckeFiniteFourierIntegral mu
      ((heckeFiniteAdelePrincipalCoset a d).indicator (fun _ => (1 : Complex))) y) <=
      mu.real (heckeFiniteAdelePrincipalCoset a d) := by
  let S := heckeFiniteAdelePrincipalCoset a d
  let G (z : FF K) := S.indicator (fun _ => (1 : Complex)) z *
    (heckeFiniteAddChar (z * y) : Complex)
  have hS : IsCompact S :=
    ((isCompact_integralFiniteAdeles (K := K)).image (continuous_id.mul continuous_const)).image
      (continuous_const.add continuous_id)
  have hZero (z : FF K) (hz : Not (Membership.mem S z)) : G z = 0 := by
    simp only [G, Set.indicator_of_notMem hz, zero_mul]
  have hEq : integral (mu.restrict S) G = integral mu G :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hZero
  have hG (z : FF K) (hz : Membership.mem S z) : norm (G z) <= 1 := by
    simp only [G, Set.indicator_of_mem hz, one_mul, Circle.norm_coe, le_refl]
  have hI : norm (integral (mu.restrict S) G) <= 1 * mu.real S :=
    norm_setIntegral_le_of_norm_le_const hS.measure_lt_top hG
  change norm (integral mu G) <= mu.real S
  rw [<- hEq, <- one_mul (mu.real S)]
  exact hI

omit [MeasurableSpace (FF K)] [BorelSpace (FF K)] in
private theorem fourierCosetPhase_eq_one_of_integral (x : FF K)
    (hx : Membership.mem (heckeIntegralFiniteAdeles (K := K)) x) :
    heckeFiniteAddChar x = 1 := by
  let z : AdeleRing (RingOfIntegers K) K := Prod.mk (0 : InfiniteAdeleRing K) x
  change heckeAdeleAddChar z = 1
  rw [heckeAdeleAddChar_of_integralFinitePart z hx]
  change Real.fourierChar (infiniteAdeleTrace (0 : InfiniteAdeleRing K)) = 1
  rw [map_zero, AddChar.map_zero_eq_one]

omit [BorelSpace (FF K)] in
/-- If a principal integer clears the denominators of a finite adelic
test's support, the Fourier transform is periodic modulo that integer. -/
theorem heckeFiniteFourierIntegral_add_eq_of_principal_denominator
    (mu : Measure (FF K)) (T : FF K -> Complex) (S : Set (FF K))
    (hSupport : forall x, Not (Membership.mem S x) -> T x = 0)
    (d : RingOfIntegers K)
    (hd : forall x : FF K, Membership.mem S x -> forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K)
        (x p * algebraMap (RingOfIntegers K) (p.adicCompletion K) d))
    (y b : FF K)
    (hb : Membership.mem (heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d)) b) :
    heckeFiniteFourierIntegral mu T (y + b) = heckeFiniteFourierIntegral mu T y := by
  let R := RingOfIntegers K
  let a := algebraMap K (FF K) (algebraMap R K d)
  choose z hz using AddSubgroup.mem_map.mp hb
  have hzB : z * a = b := hz.2
  apply integral_congr_ae
  filter_upwards with x
  change T x * (heckeFiniteAddChar (x * (y + b)) : Complex) =
    T x * (heckeFiniteAddChar (x * y) : Complex)
  by_cases hx : Membership.mem S x
  . have hM : Membership.mem (heckeIntegralFiniteAdeles (K := K)) (x * a) := by
      intro p
      change Membership.mem (p.adicCompletionIntegers K)
        (x p * algebraMap K (p.adicCompletion K) (algebraMap R K d))
      rw [<- IsScalarTower.algebraMap_apply R K (p.adicCompletion K) d]
      exact hd x hx p
    have hI : Membership.mem (heckeIntegralFiniteAdeles (K := K)) (x * b) := by
      have h : x * b = (x * a) * z := by rw [<- hzB]; ring
      rw [h]
      exact fun p => (p.adicCompletionIntegers K).toSubring.mul_mem (hM p) (hz.1 p)
    rw [mul_add, AddChar.map_add_eq_mul, fourierCosetPhase_eq_one_of_integral (x * b) hI, mul_one]
  . rw [hSupport x hx, zero_mul, zero_mul]

/-- The finite coefficient in the matrix Fourier transform expands into a
finite sum of principal rectangle indicators with a common nonzero modulus. -/
theorem exists_finiteFourierRectangle_indicator_expansion
    (K : Type*) [Field K] [NumberField K] (I : Type*) [Fintype I]
    [MeasurableSpace (FF K)] [BorelSpace (FF K)]
    (mu : Measure (FF K)) [mu.IsAddHaarMeasure]
    (a : I -> FF K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (swap : Equiv I I) :
    let e := algebraMap (RingOfIntegers K) K
    let G (i : I) (y : FF K) := heckeFiniteFourierIntegral mu
      ((heckeFiniteAdelePrincipalCoset (a i) (e d)).indicator (fun _ => (1 : Complex))) y
    let F (y : I -> FF K) := Finset.univ.prod (fun i => G i (-(y (swap i))))
    Exists (fun b : RingOfIntegers K => And (Not (b = 0))
      (Exists (fun T : Finset (Set (I -> FF K)) =>
        Exists (fun x : Set (I -> FF K) -> I -> FF K =>
          And (forall C, Membership.mem T C ->
            C = finiteAdelePrincipalRectangle K I (x C) (e b))
            (forall y, F y = T.sum (fun C => C.indicator (fun _ => F (x C)) y)))))) := by
  let e := algebraMap (RingOfIntegers K) K
  let C (i : I) := heckeFiniteAdelePrincipalCoset (a i) (e d)
  let G (i : I) (y : FF K) :=
    heckeFiniteFourierIntegral mu ((C i).indicator (fun _ => (1 : Complex))) y
  let F (y : I -> FF K) := Finset.univ.prod (fun i => G i (-(y (swap i))))
  choose V hV using fun i : I =>
    exists_compact_heckeFiniteFourierIntegral_principalCoset_support mu (a i) d hd
  let W (i : I) := Set.image (fun v : FF K => -v) (V (swap.symm i))
  let S := Set.pi Set.univ W
  have hS : IsCompact S := isCompact_univ_pi (fun i => (hV (swap.symm i)).1.image continuous_neg)
  have hZero (y : I -> FF K) (hy : Not (Membership.mem S y)) : F y = 0 := by
    have hn : Not (forall i, Membership.mem (W i) (y i)) := fun h => hy (Set.mem_univ_pi.mpr h)
    choose i hi using not_forall.mp hn
    let j := swap.symm i
    have hj : Not (Membership.mem (V j) (-(y (swap j)))) := by
      intro h
      apply hi
      exact Exists.intro (-(y (swap j))) (And.intro h (by simp [j]))
    exact Finset.prod_eq_zero (Finset.mem_univ j) ((hV j).2 (-(y (swap j))) hj)
  let U := Set.iUnion C
  have hU : IsCompact U := isCompact_iUnion (fun i =>
    ((isCompact_integralFiniteAdeles (K := K)).image (continuous_id.mul continuous_const)).image
      (continuous_const.add continuous_id))
  choose b hb using exists_commonDenominator_of_isCompact_finiteAdeles U hU
  let Hb := heckeScaledIntegralFiniteAdeles (e b)
  have hb' : Not (e b = 0) :=
    (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective (RingOfIntegers K) K)).mpr hb.1
  have hPeriod (y z : I -> FF K) (hz : forall i, Membership.mem Hb (z i)) : F (y + z) = F y := by
    apply Finset.prod_congr rfl
    intro i _
    change G i (-(y (swap i) + z (swap i))) = G i (-(y (swap i)))
    rw [neg_add]
    exact heckeFiniteFourierIntegral_add_eq_of_principal_denominator mu
      ((C i).indicator (fun _ => (1 : Complex))) U
      (fun x hx => Set.indicator_of_notMem (fun h =>
        hx (Set.mem_iUnion.mpr (Exists.intro i h))) _)
      b hb.2 (-(y (swap i))) (-(z (swap i))) (Hb.neg_mem (hz (swap i)))
  exact Exists.intro b (And.intro hb.1 (exists_finiteAdelePrincipalRectangle_indicator_expansion K I (e b) hb' F S hS hZero hPeriod))

end Robin1984.GRH
