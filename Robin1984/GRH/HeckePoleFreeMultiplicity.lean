import Robin1984.GRH.HeckeTateFunctionalEquation
import Robin1984.GRH.StandardAutomorphicMultiplicity

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Tate's completion of a unitary Hecke L-function and the Gaussian prime-power criterion for prescribed zero orders.
- Formalization note: Instantiates the individual standard multiplicity theorem for every pole-free unitary Hecke character over a number field.
- PROVENANCE-END
-/

/-!
# Prescribed zero orders for pole-free unitary Hecke characters

The functional equation transfers the dual Euler-product growth bound to
the left half-plane. Together with the Tate strip bound, this gives order
at most one for the individual completed functions. Their ordinary
logarithmic derivatives use the individual Hecke prime-power coefficients.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField Set
open Complex.Hadamard
open scoped Topology
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

private theorem heckeEulerL_eq_exp_individualPrimePowerLog
    (chi : UnitaryHeckeCharacter K) (s : Complex) :
    heckeEulerL K chi s =
      Complex.exp (complexPrimePowerEulerLog
        (fun pn : HeckePrimePowers K => (dedekindPrimePowerNorm K pn : Real))
        (heckePrimePowerCoefficient K chi) s) := by
  unfold heckeEulerL complexPrimePowerEulerLog
  apply congrArg Complex.exp
  apply tsum_congr
  intro pn
  change
    (heckeLocalParameter chi pn.1 ^ (pn.2 + 1) / ((pn.2 + 1 : Nat) : Complex)) *
        ((dedekindPrimePowerNorm K pn : Real) : Complex) ^ (-s) =
      (heckePrimePowerCoefficient K chi pn /
        (Real.log (dedekindPrimePowerNorm K pn : Real) : Complex)) *
        ((dedekindPrimePowerNorm K pn : Real) : Complex) ^ (-s)
  apply congrArg (fun z : Complex => z * ((dedekindPrimePowerNorm K pn : Real) : Complex) ^ (-s))
  have hLog :
      Real.log (dedekindPrimePowerNorm K pn : Real) =
        ((pn.2 + 1 : Nat) : Real) * Real.log (dedekindPrimeNorm K pn.1 : Real) := by
    rw [dedekindPrimePowerNorm, Nat.cast_pow, Real.log_pow]
  have hPrime : (1 : Real) < (dedekindPrimeNorm K pn.1 : Real) := by
    exact_mod_cast one_lt_dedekindPrimeNorm K pn.1
  have hLogNe : Not ((Real.log (dedekindPrimeNorm K pn.1 : Real) : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hPrime).ne'
  rw [hLog, heckePrimePowerCoefficient]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [hLogNe]

private theorem individualHeckeNormPower_two_le (pn : HeckePrimePowers K) :
    (2 : Real) <= (dedekindPrimePowerNorm K pn : Real) := by
  have h := one_lt_dedekindPrimeNorm K pn.1
  have hn : 2 <= dedekindPrimeNorm K pn.1 := Nat.succ_le_of_lt h
  have hp : 1 <= dedekindPrimeNorm K pn.1 ^ pn.2 :=
    Nat.one_le_pow pn.2 (dedekindPrimeNorm K pn.1) h.le
  have hPow : 2 <= dedekindPrimePowerNorm K pn := by
    rw [dedekindPrimePowerNorm, pow_succ']
    exact hn.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (dedekindPrimeNorm K pn.1) hp)
  exact_mod_cast hPow

private theorem heckeCompletedEuler_rightOrderBound
    (chi : UnitaryHeckeCharacter K) (L : Complex -> Complex)
    (hEuler : forall s : Complex, 1 < s.re -> L s = heckeTateStandardCompletedEulerValue chi s) :
    forall eps : Real, 0 < eps -> exists C : Real, And (0 < C)
      (forall s : Complex, 3 <= s.re ->
        norm (L s) <= Real.exp (C * (1 + norm s) ^ (1 + eps))) := by
  let q (pn : HeckePrimePowers K) := (dedekindPrimePowerNorm K pn : Real)
  let b := heckePrimePowerCoefficient K chi
  let B := tsum (fun pn => (Real.log 2) ^ (-1 : Int) * (norm (b pn) * q pn ^ (-(2 : Real))))
  refine standardCompletion_orderOneBound_on_right (heckeArithmeticConductor_pos chi) 0
    (fun v : {w : InfinitePlace K // w.IsReal} => realInfiniteHeckeShift chi v.property)
    (fun v : {w : InfinitePlace K // w.IsComplex} => complexInfiniteHeckeShift chi v.property)
    (fun v => (by norm_num : -(1 : Real) / 2 < 0).trans_le
      (realInfiniteHeckeShift_re_nonneg chi v.property))
    (fun v => (by norm_num : -(1 : Real) / 2 < 0).trans_le
      (complexInfiniteHeckeShift_re_nonneg chi v.property))
    (ordinary := heckeEulerL K chi) B ?_ ?_
  . intro s hs
    rw [heckeEulerL_eq_exp_individualPrimePowerLog, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    exact (Complex.re_le_norm _).trans (norm_complexPrimePowerEulerLog_le q b
      (individualHeckeNormPower_two_le K) (summable_heckePrimePowerCoefficient K chi (by norm_num))
      ((by norm_num : (2 : Real) <= 3).trans hs))
  . intro s hs
    rw [hEuler s ((by norm_num : (1 : Real) < 3).trans_le hs)]
    simp only [heckeTateStandardCompletedEulerValue, pow_zero, one_mul]

/-- The individual pole-free completed Hecke functions have order at most one. -/
theorem exists_heckeCompletedEulerFamily_entireOrderOne
    : exists L : UnitaryHeckeCharacter K -> Complex -> Complex,
      forall (i : HeckePoleFreeCharacter K),
        And (EntireOfOrderAtMost 1 (L i.val))
          (forall s : Complex, 1 < s.re -> L i.val s = heckeTateStandardCompletedEulerValue i.val s) := by
  choose L hL using exists_heckeCompletedEulerFamily_functionalEquation K
  refine Exists.intro L ?_
  intro i
  choose z hz using i.property
  have h := hL i.val z hz
  have hdInv : exists y, Not (heckeNormOneClassCharacter (unitaryHeckeInverse i.val) y = 1) := by
    refine Exists.intro z ?_
    have hQ : heckeNormOneClassCharacter (unitaryHeckeInverse i.val) z =
        Inv.inv (heckeNormOneClassCharacter i.val z) := by
      choose a ha using QuotientGroup.mk'_surjective (heckePrincipalNormOneIdele K).range z
      rw [<- ha, heckeNormOneClassCharacter_mk, heckeNormOneClassCharacter_mk]
      rfl
    rw [hQ, inv_eq_one]
    exact hz
  choose y hy using hdInv
  choose B hB using h.2.2.1
  choose w hw using h.2.2.2
  refine And.intro (entireOrderOne_of_dualRightBounds_and_stripBound h.1
    (heckeCompletedEuler_rightOrderBound K i.val (L i.val) h.2.1)
    (heckeCompletedEuler_rightOrderBound K (unitaryHeckeInverse i.val)
      (L (unitaryHeckeInverse i.val)) (hL (unitaryHeckeInverse i.val) y hy).2.1)
    (fun s => by rw [hw.2 s, norm_mul, hw.1, one_mul]) ?_) h.2.1
  intro eps heps
  refine Exists.intro (max B 1) (And.intro (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) ?_)
  intro s hleft hright
  have hb : 1 <= 1 + norm s := le_add_of_nonneg_right (norm_nonneg _)
  have hBase : 1 <= (1 + norm s) ^ (1 + eps) := hb.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hb (show (1 : Real) <= 1 + eps by linarith))
  have hMul : B <= max B 1 * (1 + norm s) ^ (1 + eps) :=
    (le_max_left B 1).trans (le_mul_of_one_le_right ((zero_le_one : (0 : Real) <= 1).trans (le_max_right _ _)) hBase)
  apply (hB s hleft hright).trans (hMul.trans ?_)
  calc
    _ <= max B 1 * (1 + norm s) ^ (1 + eps) + 1 :=
      le_add_of_nonneg_right zero_le_one
    _ <= _ := Real.add_one_le_exp _

private abbrev HeckeRealPlaces (K : Type*) [Field K] [NumberField K] :=
  {v : InfinitePlace K // v.IsReal}

private abbrev HeckeComplexPlaces (K : Type*) [Field K] [NumberField K] :=
  {v : InfinitePlace K // v.IsComplex}

private def heckePoleFreeMultiplicityData
    (L F : HeckePoleFreeCharacter K -> Complex -> Complex) :
    StandardMultiplicityFamilyData (HeckePoleFreeCharacter K) (fun _ => HeckePrimePowers K) where
  completedL := L
  poleRemoved := F
  primePowerNorm _ := dedekindPrimePowerNorm K
  coefficient i := heckePrimePowerCoefficient K i.val
  poleOrder _ := 0
  conductor i := heckeArithmeticConductor i.val
  realFactorCount _ := Fintype.card (HeckeRealPlaces K)
  complexFactorCount _ := Fintype.card (HeckeComplexPlaces K)
  realShift i j := realInfiniteHeckeShift i.val ((Fintype.equivFin (HeckeRealPlaces K)).symm j).property
  complexShift i j := complexInfiniteHeckeShift i.val
    ((Fintype.equivFin (HeckeComplexPlaces K)).symm j).property

private theorem heckePoleFreeMultiplicityData_factor
    (L F : HeckePoleFreeCharacter K -> Complex -> Complex)
    (i : HeckePoleFreeCharacter K) (s : Complex) :
    standardMultiplicityCompletionFactor (heckePoleFreeMultiplicityData K L F) i s =
      standardCompletionFactor (heckeArithmeticConductor i.val) 0
        (fun v : HeckeRealPlaces K => realInfiniteHeckeShift i.val v.property)
        (fun v : HeckeComplexPlaces K => complexInfiniteHeckeShift i.val v.property) s := by
  let eR := (Fintype.equivFin (HeckeRealPlaces K)).symm
  let eC := (Fintype.equivFin (HeckeComplexPlaces K)).symm
  let fr (v : HeckeRealPlaces K) := DedekindZeta.LReal (s + realInfiniteHeckeShift i.val v.property)
  let fc (v : HeckeComplexPlaces K) := DedekindZeta.LComplex (s + complexInfiniteHeckeShift i.val v.property)
  change s ^ (0 : Nat) * (heckeArithmeticConductor i.val : Complex) ^ (s / 2) *
    (Finset.univ.prod (fun j => fr (eR j))) * (Finset.univ.prod (fun j => fc (eC j))) =
      s ^ (0 : Nat) * (heckeArithmeticConductor i.val : Complex) ^ (s / 2) *
        (Finset.univ.prod fr) * (Finset.univ.prod fc)
  rw [Equiv.prod_comp eR fr, Equiv.prod_comp eC fc]

private theorem heckePrimePowerNorm_finite_lt (T : Real) :
    Set.Finite {pn : HeckePrimePowers K | (dedekindPrimePowerNorm K pn : Real) < T} := by
  apply (finite_primePowerNorm_le K (Nat.ceil T)).subset
  intro pn hp
  have h : ((dedekindPrimePowerNorm K pn : Nat) : Real) <= (Nat.ceil T : Real) :=
    le_trans (show (dedekindPrimePowerNorm K pn : Real) <= T from hp.le) (Nat.le_ceil T)
  exact_mod_cast h

private theorem heckePrimePowers_countable : Countable (HeckePrimePowers K) := by
  refine Set.countable_univ_iff.mp ?_
  have hUnion : (Set.univ : Set (HeckePrimePowers K)) =
      Set.iUnion (fun n : Nat => {pn : HeckePrimePowers K | dedekindPrimePowerNorm K pn <= n}) := by
    ext pn
    constructor
    . intro _
      refine Set.mem_iUnion.mpr (Exists.intro (dedekindPrimePowerNorm K pn) ?_)
      change dedekindPrimePowerNorm K pn <= dedekindPrimePowerNorm K pn
      exact le_rfl
    . intro _
      exact Set.mem_univ pn
  rw [hUnion]
  exact Set.countable_iUnion (fun n => (finite_primePowerNorm_le K n).countable)

private theorem heckePoleFreeMultiplicityData_analytics
    (L : HeckePoleFreeCharacter K -> Complex -> Complex)
    (hL : forall i, EntireOfOrderAtMost 1 (L i))
    (hEuler : forall i (s : Complex), 1 < s.re -> L i s = heckeTateStandardCompletedEulerValue i.val s) :
    exists F : HeckePoleFreeCharacter K -> Complex -> Complex,
      HasStandardMultiplicityAnalytics (heckePoleFreeMultiplicityData K L F) := by
  have hOrdinary (i : HeckePoleFreeCharacter K) :=
    exists_entireOrderOne_of_standardCompletion_noPole
      (heckeArithmeticConductor_pos i.val)
      (fun v : HeckeRealPlaces K => realInfiniteHeckeShift i.val v.property)
      (fun v : HeckeComplexPlaces K => complexInfiniteHeckeShift i.val v.property)
      (fun v => (by norm_num : -(1 : Real) / 2 < 0).trans_le
        (realInfiniteHeckeShift_re_nonneg i.val v.property))
      (fun v => (by norm_num : -(1 : Real) / 2 < 0).trans_le
        (complexInfiniteHeckeShift_re_nonneg i.val v.property)) (hL i)
  choose F hF hCompletion using hOrdinary
  have hEq (i : HeckePoleFreeCharacter K) (s : Complex) (hs : 1 < s.re) :
      F i s = heckeEulerL K i.val s := by
    let q := heckeArithmeticConductor i.val
    let mu (v : HeckeRealPlaces K) := realInfiniteHeckeShift i.val v.property
    let nu (v : HeckeComplexPlaces K) := complexInfiniteHeckeShift i.val v.property
    have hHalf := (by norm_num : (1 : Real) / 2 < 1).trans hs
    have hNonzero := standardCompletionFactor_ne_zero (heckeArithmeticConductor_pos i.val) 0 mu nu
      (fun v => (by norm_num : -(1 : Real) / 2 < 0).trans_le
        (realInfiniteHeckeShift_re_nonneg i.val v.property))
      (fun v => (by norm_num : -(1 : Real) / 2 < 0).trans_le
        (complexInfiniteHeckeShift_re_nonneg i.val v.property)) hHalf
    have h := (hCompletion i s hHalf).symm.trans (hEuler i s hs)
    change standardCompletionFactor q 0 mu nu s * F i s =
      standardCompletionFactor q 0 mu nu s * heckeEulerL K i.val s at h
    apply sub_eq_zero.mp
    have hSub : standardCompletionFactor q 0 mu nu s * (F i s - heckeEulerL K i.val s) = 0 := by
      rw [mul_sub, h, sub_self]
    exact (mul_eq_zero.mp hSub).resolve_left hNonzero
  refine Exists.intro F
    { conductor_pos := fun i => heckeArithmeticConductor_pos i.val
      real_shift := fun i j => (by norm_num : -(1 : Real) / 2 < 0).trans_le
        (realInfiniteHeckeShift_re_nonneg i.val ((Fintype.equivFin (HeckeRealPlaces K)).symm j).property)
      complex_shift := fun i j => (by norm_num : -(1 : Real) / 2 < 0).trans_le
        (complexInfiniteHeckeShift_re_nonneg i.val ((Fintype.equivFin (HeckeComplexPlaces K)).symm j).property)
      norm_ge_two := fun _ => individualHeckeNormPower_two_le K
      norms_locally_finite := fun _ => heckePrimePowerNorm_finite_lt K
      log_derivative_summable := fun i _ hr => summable_heckePrimePowerCoefficient K i.val hr
      ordinary_entire := fun i => (hF i).1
      completed_order_one := hL
      completion := fun i s hs => ?_
      euler_log_derivative := fun i s hs => ?_ }
  . rw [heckePoleFreeMultiplicityData_factor]
    exact hCompletion i s hs
  . have hOpen : IsOpen {z : Complex | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hNear : Filter.EventuallyEq (nhds s) (F i) (heckeEulerL K i.val) := by
      filter_upwards [hOpen.mem_nhds hs] with z hz
      exact hEq i z hz
    change logDeriv (F i) s = ((0 : Nat) : Complex) / (s - 1) -
      tsum (fun pn : HeckePrimePowers K => heckePrimePowerCoefficient K i.val pn *
        ((dedekindPrimePowerNorm K pn : Real) : Complex) ^ (-s))
    rw [(logDeriv_congr_nhds hNear).eq_of_nhds, Nat.cast_zero, zero_div, zero_sub]
    exact logDeriv_heckeEulerL K i.val hs

/-- The centered, triangularly weighted sum of the individual Hecke
prime-power coefficients, extended by zero to negative log scale. -/
def heckePrimePowerMultiplicitySignal (chi : UnitaryHeckeCharacter K) (t : Real) : Complex :=
  if t < 0 then 0 else
    let x := Real.exp t
    (Real.exp (-t / (Nat.cast 2 : Real)) : Complex) *
      (-tsum (fun pn : HeckePrimePowers K =>
        (Set.Ioi (dedekindPrimePowerNorm K pn : Real)).indicator (fun y : Real =>
          heckePrimePowerCoefficient K chi pn *
            (1 - ((dedekindPrimePowerNorm K pn : Real) : Complex) / (y : Complex))) x))

private theorem heckePoleFreeMultiplicityData_logSignal
    (L F : HeckePoleFreeCharacter K -> Complex -> Complex) (i : HeckePoleFreeCharacter K) :
    standardMultiplicityLogSignal (heckePoleFreeMultiplicityData K L F) i =
      heckePrimePowerMultiplicitySignal K i.val := by
  funext t
  simp only [standardMultiplicityLogSignal, heckePoleFreeMultiplicityData,
    heckePrimePowerMultiplicitySignal, Nat.cast_zero, zero_div, Complex.ofReal_zero, zero_mul, zero_sub]

private theorem eq_of_heckeCompletedEulerValue
    (chi : UnitaryHeckeCharacter K) {f g : Complex -> Complex}
    (hf : Differentiable Complex f) (hg : Differentiable Complex g)
    (hF : forall s : Complex, 1 < s.re -> f s = heckeTateStandardCompletedEulerValue chi s)
    (hG : forall s : Complex, 1 < s.re -> g s = heckeTateStandardCompletedEulerValue chi s) :
    f = g := by
  have hOpen : IsOpen {z : Complex | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hTwo : Membership.mem {z : Complex | 1 < z.re} (2 : Complex) := by
    change (1 : Real) < (2 : Complex).re
    norm_num
  have hNear : Filter.EventuallyEq (nhds (2 : Complex)) f g := by
    filter_upwards [hOpen.mem_nhds hTwo] with z hz
    exact (hF z hz).trans (hG z hz).symm
  funext s
  exact ((hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ _) hNear) (mem_univ s)

/-- Under the critical-line hypothesis for the pole-free unitary Hecke
family, prescribed zero orders are equivalent to the individual
prime-power inequalities with the same exceptions. -/
theorem heckePoleFree_prescribedOrders_iff_globalMultiplicityInequality
    (L : HeckePoleFreeCharacter K -> Complex -> Complex)
    (hL : forall i, Differentiable Complex (L i))
    (hEuler : forall i (s : Complex), 1 < s.re -> L i s = heckeTateStandardCompletedEulerValue i.val s)
    (E J : HeckePoleFreeCharacter K -> Finset Real)
    (order : HeckePoleFreeCharacter K -> Real -> Nat)
    (hRH : CompletedFamilyRH L) :
    (forall i, HasPrescribedZeroOrders (L i) (E i) (J i) (order i)) <->
      (forall i, ExceptionalPrimePowerMultiplicityInequality
        (heckePrimePowerMultiplicitySignal K i.val) (E i) (J i) (order i)) := by
  choose G hG using exists_heckeCompletedEulerFamily_entireOrderOne K
  have hOrder (i : HeckePoleFreeCharacter K) : EntireOfOrderAtMost 1 (L i) := by
    rw [eq_of_heckeCompletedEulerValue K i.val (hL i) (hG i).1.1 (hEuler i) (hG i).2]
    exact (hG i).1
  choose F hF using heckePoleFreeMultiplicityData_analytics K L hOrder hEuler
  let : Countable (HeckePrimePowers K) := heckePrimePowers_countable K
  have h := grandRH_prescribedOrders_iff_globalMultiplicityInequality
    (heckePoleFreeMultiplicityData K L F) hF E J order hRH
  simp_rw [heckePoleFreeMultiplicityData_logSignal] at h
  exact h

end Robin1984.GRH
