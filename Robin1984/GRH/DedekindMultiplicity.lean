import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Robin1984.GRH.MultiplicityArithmetic

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The additive holomorphic order formula and the Gaussian prime-power multiplicity comparison.
- Formalization note: Under Dedekind ERH each factor has only critical-line zeros in the open strip; the weighted gap detects all excess orders.
- PROVENANCE-END
-/

/-!
# Forced zero orders of a Dedekind zeta function

A finite factorization with positive exponents gives a pointwise lower bound
on every zero order. Under Dedekind ERH, the exponent-weighted global
prime-power inequality detects equality at all nontrivial zeros.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Complex.Hadamard Filter MeasureTheory Set
open scoped Topology Classical

/-- Analytic zero order adds with the exponents in a finite holomorphic product. -/
theorem analyticOrderAt_positiveWeightedProduct {i : Type*}
    (J : Finset i) (e : i -> Nat) (F : i -> Complex -> Complex) (z : Complex)
    (hA : forall j, Membership.mem J j -> AnalyticAt Complex (F j) z) :
    And (AnalyticAt Complex (fun w => J.prod (fun j => F j w ^ e j)) z)
      (analyticOrderAt (fun w => J.prod (fun j => F j w ^ e j)) z =
        J.sum (fun j => (e j : ENat) * analyticOrderAt (F j) z)) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact And.intro analyticAt_const (analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero)
  | insert j J hj ih =>
    have hJ := ih (fun k hk => hA k (Finset.mem_insert_of_mem hk))
    have hHead : AnalyticAt Complex (fun w => F j w ^ e j) z :=
      (hA j (Finset.mem_insert_self _ _)).pow _
    simp only [Finset.prod_insert hj, Finset.sum_insert hj]
    refine And.intro (hHead.mul hJ.1) ?_
    change analyticOrderAt ((fun w => F j w ^ e j) *
      (fun w => J.prod (fun k => F k w ^ e k))) z = _
    rw [analyticOrderAt_mul hHead hJ.1, hJ.2]
    have hPow := analyticOrderAt_pow (hA j (Finset.mem_insert_self _ _)) (e j)
    have hFun : (fun w => F j w ^ e j) = F j ^ e j := by
      funext w
      rw [Pi.pow_apply]
    have hPow' : analyticOrderAt (fun w => F j w ^ e j) z =
        (e j : ENat) * analyticOrderAt (F j) z := by
      simpa only [hFun, nsmul_eq_mul] using hPow
    rw [hPow']

/-- The weighted sum of multiplicities attains the forced baseline
exactly when each positive-weight factor has order at most one. -/
theorem weightedMultiplicity_eq_forcedMinimum_iff {i : Type*}
    (J : Finset i) (e m : i -> Nat) (hPos : forall j, Membership.mem J j -> 0 < e j) :
    (J.sum (fun j => e j * m j) =
      J.sum (fun j => e j * (if m j = 0 then 0 else 1))) <->
      (forall j, Membership.mem J j -> m j <= 1) := by
  have hLe (j : i) (_ : Membership.mem J j) :
      e j * (if m j = 0 then 0 else 1) <= e j * m j := by
    apply Nat.mul_le_mul_left
    split
    case isTrue => exact Nat.zero_le _
    case isFalse _ h => exact Nat.pos_of_ne_zero h
  constructor
  case mp =>
    intro h j hj
    have hEq := (Finset.sum_eq_sum_iff_of_le hLe).mp h.symm j hj
    have hE : (if m j = 0 then 0 else 1) = m j :=
      Nat.eq_of_mul_eq_mul_left (hPos j hj) hEq
    rw [<- hE]
    split
    case isTrue => exact Nat.zero_le _
    case isFalse => exact le_rfl
  case mpr =>
    intro h
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h0 : m j = 0
    case pos => simp [h0]
    case neg =>
      have h1 : m j = 1 := Nat.le_antisymm (h j hj) (Nat.pos_of_ne_zero h0)
      simp [h1]

private theorem analyticOrderNatAt_eq_zero_iff_of_finite
    {F : Complex -> Complex} {z : Complex} (hA : AnalyticAt Complex F z)
    (hFinite : Not (analyticOrderAt F z = Top.top)) :
    analyticOrderNatAt F z = 0 <-> Not (F z = 0) := by
  have hCast : ((analyticOrderNatAt F z : Nat) : ENat) = analyticOrderAt F z :=
    ENat.natCast_toNat hFinite
  constructor
  case mp =>
    intro h
    apply hA.analyticOrderAt_eq_zero.mp
    simpa only [h, Nat.cast_zero] using hCast.symm
  case mpr =>
    intro h
    simp [analyticOrderNatAt, hA.analyticOrderAt_eq_zero.mpr h]

/-- A holomorphic unit times a finite positive-weight product has exactly
the zero order forced by vanishing of its factors precisely when each
factor has order at most one at that point. -/
theorem analyticOrderNatAt_eq_positiveFactorBaseline_iff {i : Type*}
    (J : Finset i) (e : i -> Nat) (F : i -> Complex -> Complex)
    (Z U : Complex -> Complex) (z : Complex)
    (hE : forall j, Membership.mem J j -> 0 < e j)
    (hA : forall j, Membership.mem J j -> AnalyticAt Complex (F j) z)
    (hFinite : forall j, Membership.mem J j -> Not (analyticOrderAt (F j) z = Top.top))
    (hU : AnalyticAt Complex U z) (hU0 : Not (U z = 0))
    (hEq : Filter.EventuallyEq (nhds z) Z (U * (fun w => J.prod (fun j => F j w ^ e j)))) :
    (analyticOrderNatAt Z z = J.sum (fun j => e j * (if F j z = 0 then 1 else 0))) <->
      (forall j, Membership.mem J j -> analyticOrderNatAt (F j) z <= 1) := by
  let N (j : i) := analyticOrderNatAt (F j) z
  have hProduct := analyticOrderAt_positiveWeightedProduct J e F z hA
  have hOrd : analyticOrderAt Z z = ((J.sum (fun j => e j * N j) : Nat) : ENat) := by
    rw [analyticOrderAt_congr hEq, analyticOrderAt_mul hU hProduct.1,
      hU.analyticOrderAt_eq_zero.mpr hU0, zero_add, hProduct.2, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Nat.cast_mul, show ((N j : Nat) : ENat) = analyticOrderAt (F j) z from ENat.natCast_toNat (hFinite j hj)]
  have hNat : analyticOrderNatAt Z z = J.sum (fun j => e j * N j) := by
    simpa only [analyticOrderNatAt, ENat.toNat_natCast] using congrArg ENat.toNat hOrd
  have hForced : J.sum (fun j => e j * (if F j z = 0 then 1 else 0)) =
      J.sum (fun j => e j * (if N j = 0 then 0 else 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have h0 := analyticOrderNatAt_eq_zero_iff_of_finite (hA j hj) (hFinite j hj)
    by_cases hz : F j z = 0
    case pos =>
      have hn : Not (N j = 0) := fun hn => (h0.mp hn) hz
      simp only [if_pos hz, if_neg hn]
    case neg =>
      have hn : N j = 0 := h0.mpr hz
      simp only [if_neg hz, if_pos hn]
  rw [hNat, hForced]
  exact weightedMultiplicity_eq_forcedMinimum_iff J e N hE

/-- A weighted aggregate of per-factor inequalities with nonnegative gaps
holds exactly when every factor attains equality. -/
theorem positiveWeightedGap_le_iff {i : Type*} (J : Finset i) (w E M : i -> Real)
    (hPos : forall j, Membership.mem J j -> 0 < w j)
    (hGap : forall j, Membership.mem J j -> M j <= E j) :
    (J.sum (fun j => w j * E j) <= J.sum (fun j => w j * M j)) <->
      (forall j, Membership.mem J j -> E j <= M j) := by
  have hTerm (j : i) (hj : Membership.mem J j) : w j * M j <= w j * E j :=
    mul_le_mul_of_nonneg_left (hGap j hj) (hPos j hj).le
  constructor
  case mp =>
    intro h j hj
    have hEq := le_antisymm (Finset.sum_le_sum hTerm) h
    have hEqJ := (Finset.sum_eq_sum_iff_of_le hTerm).mp hEq j hj
    by_contra h
    have hStrict := mul_lt_mul_of_pos_left (lt_of_not_ge h) (hPos j hj)
    rw [hEqJ] at hStrict
    exact (lt_irrefl _) hStrict
  case mpr =>
    intro h
    exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (h j hj) (hPos j hj).le)

universe u v w

/-- Finite positive-weight factor data and its individual prime-power series. -/
structure DedekindMultiplicityFactorization (index : Type v) (powers : index -> Type w) where
  factors : Finset index
  exponent : index -> Nat
  zeta : Complex -> Complex
  unit : Complex -> Complex
  ordinary : index -> Complex -> Complex
  primePowerNorm : forall j, powers j -> Real
  coefficient : forall j, powers j -> Complex
  poleOrder : index -> Real

/-- The epsilon form of the order-one bound for an entire function. -/
def HasMultiplicityOrderOne (F : Complex -> Complex) : Prop :=
  Differentiable Complex F /\
    forall eps : Real, 0 < eps -> exists C : Real, 0 < C /\
      forall s : Complex, norm (F s) <= Real.exp (C * (1 + norm s) ^ (1 + eps))

/-- The given positive holomorphic factorization belongs to the actual Dedekind
zeta function, with each factor supplying its own signed Euler logarithm. -/
structure HasDedekindMultiplicityFactorization (K : Type u) [Field K] [NumberField K]
    {index : Type v} {powers : index -> Type w} (f : DedekindMultiplicityFactorization index powers) : Prop where
  zeta_continuation : IsDedekindZetaContinuation K f.zeta
  exponent_positive : forall j, Membership.mem f.factors j -> 0 < f.exponent j
  factorization :
    forall s : Complex, 0 < s.re -> s.re < 1 ->
      f.zeta s = f.unit s * f.factors.prod (fun j => f.ordinary j s ^ f.exponent j)
  unit_analytic :
    forall s : Complex, 0 < s.re -> s.re < 1 -> AnalyticAt Complex f.unit s
  unit_nonzero :
    forall s : Complex, 0 < s.re -> s.re < 1 -> Not (f.unit s = 0)
  order_one : forall j, Membership.mem f.factors j -> HasMultiplicityOrderOne (f.ordinary j)
  right_nonvanishing :
    forall j, Membership.mem f.factors j ->
      forall s : Complex, 1 <= s.re -> Not (f.ordinary j s = 0)
  norms_positive :
    forall j, Membership.mem f.factors j -> forall n, 1 <= f.primePowerNorm j n
  norms_locally_finite :
    forall j, Membership.mem f.factors j -> forall T : Real,
      Set.Finite {n : powers j | f.primePowerNorm j n < T}
  coefficients_summable :
    forall j, Membership.mem f.factors j -> forall r : Real, 1 < r ->
      Summable (fun n => norm (f.coefficient j n) * (f.primePowerNorm j n) ^ (-r))
  euler_log_derivative : forall j, Membership.mem f.factors j ->
    forall s : Complex, 1 < s.re ->
      logDeriv (f.ordinary j) s = (f.poleOrder j : Complex) / (s - 1) -
        tsum (fun n => f.coefficient j n * (f.primePowerNorm j n : Complex) ^ (-s))

/-- Each vanishing factor contributes its positive integer exponent
to the forced order of the Dedekind zeta function. -/
def DedekindOrderForcedByFactors {index : Type v} {powers : index -> Type w}
    (f : DedekindMultiplicityFactorization index powers) : Prop :=
  forall s : Complex, 0 < s.re -> s.re < 1 ->
    analyticOrderNatAt f.zeta s =
      f.factors.sum (fun j => f.exponent j * (if f.ordinary j s = 0 then 1 else 0))

/-- The complex prime-power signal of a factor in the specified product. -/
def dedekindFactorMultiplicityInput {index : Type v} {powers : index -> Type w}
    (f : DedekindMultiplicityFactorization index powers) (j : index) : Real -> Complex :=
  triangularLogSignal (complexTriangularRemainder (f.primePowerNorm j) (f.coefficient j) (f.poleOrder j))

/-- Add the two sides of the global Gaussian inequality with the factor
exponents as weights. -/
def DedekindGlobalMultiplicityInequality {index : Type v} {powers : index -> Type w}
    (f : DedekindMultiplicityFactorization index powers) : Prop :=
  f.factors.sum (fun j => (f.exponent j : Real) *
    spectralSquareEnergy (gaussianMultiplicitySignal (dedekindFactorMultiplicityInput f j) 1)) <=
  f.factors.sum (fun j => (f.exponent j : Real) *
    Filter.limsup (fun t : Real =>
      (gaussianMultiplicitySignal (dedekindFactorMultiplicityInput f j) 2 t).re) atTop)

/-- **Dedekind ERH and forced zero orders.** Under Dedekind ERH, the
critical-strip zeros of a Dedekind zeta function have exactly the orders
forced by the given positive holomorphic factorization if and only if
the weighted global prime-power inequality holds. -/
theorem dedekindERH_iff_globalMultiplicityInequality
    (hERH : forall (K : Type u) [Field K] [NumberField K], DedekindRH K)
    (K : Type u) [Field K] [NumberField K]
    {index : Type v} {powers : index -> Type w} [forall j, Countable (powers j)]
    (f : DedekindMultiplicityFactorization index powers)
    (h : HasDedekindMultiplicityFactorization K f) :
    DedekindOrderForcedByFactors f <-> DedekindGlobalMultiplicityInequality f := by
  let E (j : index) := spectralSquareEnergy
    (gaussianMultiplicitySignal (dedekindFactorMultiplicityInput f j) 1)
  let M (j : index) := Filter.limsup (fun t : Real =>
    (gaussianMultiplicitySignal (dedekindFactorMultiplicityInput f j) 2 t).re) atTop
  let Simple (j : index) := forall z : Complex, z.re = 1 / 2 ->
    f.ordinary j z = 0 -> analyticOrderNatAt (f.ordinary j) z <= 1
  have hZeta := (dedekindRH_iff_zeros_of_continuation h.zeta_continuation).mp (hERH K)
  have hLine (j : index) (hj : Membership.mem f.factors j) (s : Complex)
      (hs0 : 0 < s.re) (hs1 : s.re < 1) (hz : f.ordinary j s = 0) : s.re = 1 / 2 := by
    have hp : f.ordinary j s ^ f.exponent j = 0 := by
      rw [hz, zero_pow (Nat.ne_of_gt (h.exponent_positive j hj))]
    have hZeroProduct : f.factors.prod (fun k => f.ordinary k s ^ f.exponent k) = 0 :=
      Finset.prod_eq_zero hj hp
    apply hZeta s hs0 hs1
    rw [h.factorization s hs0 hs1, hZeroProduct, mul_zero]
  have hNonzero (j : index) (hj : Membership.mem f.factors j) :
      Not (f.ordinary j 1 = 0) := h.right_nonvanishing j hj 1 (by norm_num)
  have hDiff (j : index) (hj : Membership.mem f.factors j) : Differentiable Complex (f.ordinary j) :=
    (h.order_one j hj).1
  have hFiniteOrder (j : index) (hj : Membership.mem f.factors j) (s : Complex) :
      Not (analyticOrderAt (f.ordinary j) s = Top.top) := by
    intro he
    have hEq := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
      (fun w => (hDiff j hj).analyticAt w)).mp he
    exact hNonzero j hj (congrFun hEq 1)
  have hArithmetic (j : index) (hj : Membership.mem f.factors j) :
      And (M j <= E j) ((E j <= M j) <-> Simple j) := by
    have hZero (s : Complex) (hs : f.ordinary j s = 0) : s.re <= 1 / 2 := by
      by_contra hh
      have hsHalf : 1 / 2 < s.re := lt_of_not_ge hh
      have hs1 : s.re < 1 := lt_of_not_ge (fun hh1 => h.right_nonvanishing j hj s hh1 hs)
      have hsLine := hLine j hj s (by linarith only [hsHalf]) hs1 hs
      rw [hsLine] at hsHalf
      exact (lt_irrefl _) hsHalf
    exact complexArithmeticMultiplicityComparison (f.primePowerNorm j) (f.coefficient j)
      (f.poleOrder j) (f.ordinary j) (h.norms_positive j hj) (h.norms_locally_finite j hj)
      (h.coefficients_summable j hj) (h.order_one j hj)
      (Exists.intro 1 (hNonzero j hj)) hZero (h.euler_log_derivative j hj)
  have hWeighted : DedekindGlobalMultiplicityInequality f <->
      forall j, Membership.mem f.factors j -> E j <= M j :=
    positiveWeightedGap_le_iff f.factors (fun j => (f.exponent j : Real)) E M
      (fun j hj => by exact_mod_cast h.exponent_positive j hj)
      (fun j hj => (hArithmetic j hj).1)
  have hLocal (z : Complex) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
      (analyticOrderNatAt f.zeta z =
        f.factors.sum (fun j => f.exponent j * (if f.ordinary j z = 0 then 1 else 0))) <->
      (forall j, Membership.mem f.factors j -> analyticOrderNatAt (f.ordinary j) z <= 1) := by
    have hNear : Filter.EventuallyEq (nhds z) f.zeta
        (f.unit * (fun s => f.factors.prod (fun j => f.ordinary j s ^ f.exponent j))) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz0,
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz1] with s hs0 hs1
      exact h.factorization s hs0 hs1
    exact analyticOrderNatAt_eq_positiveFactorBaseline_iff f.factors f.exponent f.ordinary
      f.zeta f.unit z h.exponent_positive (fun j hj => (hDiff j hj).analyticAt z)
      (fun j hj => hFiniteOrder j hj z) (h.unit_analytic z hz0 hz1)
      (h.unit_nonzero z hz0 hz1) hNear
  constructor
  case mp =>
    intro hForced
    apply hWeighted.mpr
    intro j hj
    apply (hArithmetic j hj).2.mpr
    intro s hS _
    have hs0 : 0 < s.re := by rw [hS]; norm_num
    have hs1 : s.re < 1 := by rw [hS]; norm_num
    exact ((hLocal s hs0 hs1).mp (hForced s hs0 hs1)) j hj
  case mpr =>
    intro hInequality s hs0 hs1
    apply (hLocal s hs0 hs1).mpr
    intro j hj
    by_cases hz : f.ordinary j s = 0
    case pos =>
      exact ((hArithmetic j hj).2.mp (hWeighted.mp hInequality j hj))
        s (hLine j hj s hs0 hs1 hz) hz
    case neg =>
      have hOrd := (analyticOrderNatAt_eq_zero_iff_of_finite
        ((hDiff j hj).analyticAt s) (hFiniteOrder j hj s)).mpr hz
      rw [hOrd]
      exact zero_le_one

end Robin1984.GRH
