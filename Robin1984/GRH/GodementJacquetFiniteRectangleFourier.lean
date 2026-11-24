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

end Robin1984.GRH
