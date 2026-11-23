import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Robin1984.GRH.AutomorphicCompletion

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The absolutely convergent logarithmic Euler product and its derivative on the right half-plane.
- Formalization note: Differentiates the log sum termwise and proves nonvanishing and the logarithmic derivative needed by the completed-family criterion.
- PROVENANCE-END
-/

/-!
# The exponential Euler product for the triangular criterion

Absolute convergence above the line with real part one supplies a uniform
majorant on every smaller open right half-plane. The derivative and
nonvanishing of the pole-cleared function follow from its exponential
Euler product and feed the completed-family criterion.
-/

set_option autoImplicit false

open Complex Complex.Hadamard Filter Set Topology

namespace Robin1984.GRH

private noncomputable def grandPrimePowerLogTerm {powers : Type*}
    (d : GrandRobinEulerData powers) (i : powers) (s : Complex) : Complex :=
  ((d.coefficient i : Complex) / (Real.log (d.normPower i) : Complex)) *
    (d.normPower i : Complex) ^ (-s)

/-- The logarithm of the paired Euler product on the half-plane of
absolute convergence, expressed by its prime-power coefficients. -/
noncomputable def grandEulerLog {powers : Type*} (d : GrandRobinEulerData powers)
    (s : Complex) : Complex :=
  tsum (fun i => grandPrimePowerLogTerm d i s)

private theorem hasDerivAt_grandPrimePowerLogTerm {powers : Type*}
    (d : GrandRobinEulerData powers) (i : powers) (hTwo : 2 <= d.normPower i) (s : Complex) :
    HasDerivAt (grandPrimePowerLogTerm d i)
      (-((d.coefficient i : Complex) * (d.normPower i : Complex) ^ (-s))) s := by
  have hq : 0 < d.normPower i := (by norm_num : (0 : Real) < 2).trans_le hTwo
  have hlog : 0 < Real.log (d.normPower i) :=
    Real.log_pos ((by norm_num : (1 : Real) < 2).trans_le hTwo)
  have hd := ((hasDerivAt_neg' s).const_cpow
    (c := (d.normPower i : Complex)) (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne'))).const_mul
      ((d.coefficient i : Complex) / (Real.log (d.normPower i) : Complex))
  change HasDerivAt (grandPrimePowerLogTerm d i) _ s at hd
  convert hd using 1
  rw [<- Complex.ofReal_log hq.le]
  field_simp [Complex.ofReal_ne_zero.mpr hlog.ne']

private theorem norm_grandPrimePowerLogTerm_le {powers : Type*}
    (d : GrandRobinEulerData powers) (i : powers) (hTwo : 2 <= d.normPower i)
    {a : Real} {s : Complex} (hs : a <= s.re) :
    norm (grandPrimePowerLogTerm d i s) <=
      (Real.log 2) ^ (-1 : Int) * (norm (d.coefficient i) * d.normPower i ^ (-a)) := by
  have hq : 0 < d.normPower i := (by norm_num : (0 : Real) < 2).trans_le hTwo
  have hlog : 0 < Real.log (d.normPower i) :=
    Real.log_pos ((by norm_num : (1 : Real) < 2).trans_le hTwo)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLog := Real.log_le_log (by norm_num : (0 : Real) < 2) hTwo
  rw [grandPrimePowerLogTerm, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hlog.le, Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re]
  calc
    _ <= (norm (d.coefficient i) / Real.log 2) * d.normPower i ^ (-a) :=
      mul_le_mul (div_le_div_of_nonneg_left (norm_nonneg _) h2 hLog)
        (Real.rpow_le_rpow_of_exponent_le ((by norm_num : (1 : Real) <= 2).trans hTwo)
          (neg_le_neg hs)) (Real.rpow_nonneg hq.le _) (div_nonneg (norm_nonneg _) h2.le)
    _ = _ := by simp only [zpow_neg, zpow_one, div_eq_mul_inv]; ac_rfl

/-- The Euler log differentiates termwise on the ordinary half-plane of
absolute convergence. -/
theorem hasDerivAt_grandEulerLog {powers : Type*} [Countable powers]
    (d : GrandRobinEulerData powers) (hTwo : forall i, 2 <= d.normPower i)
    (hSummable : forall r : Real, 1 < r ->
      Summable (fun i => norm (d.coefficient i) * d.normPower i ^ (-r)))
    {s : Complex} (hs : 1 < s.re) :
    HasDerivAt (grandEulerLog d)
      (-tsum (fun i => (d.coefficient i : Complex) * (d.normPower i : Complex) ^ (-s))) s := by
  choose a ha using exists_between hs
  let D : Set Complex := {z | a < z.re}
  have hOpen : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hsD : Membership.mem D s := ha.2
  have hSumm := (hSummable a ha.1).mul_left ((Real.log 2) ^ (-1 : Int))
  have hDiff (i : powers) : DifferentiableOn Complex (grandPrimePowerLogTerm d i) D :=
    fun z _ => (hasDerivAt_grandPrimePowerLogTerm d i (hTwo i) z).differentiableAt.differentiableWithinAt
  have hBound (i : powers) (z : Complex) (hz : Membership.mem D z) :=
    norm_grandPrimePowerLogTerm_le d i (hTwo i) (show a < z.re from hz).le
  have hSum := hasSum_deriv_of_summable_norm hSumm hDiff hOpen hBound hsD
  have hL : DifferentiableAt Complex (grandEulerLog d) s :=
    (differentiableOn_tsum_of_summable_norm hSumm hDiff hOpen hBound).differentiableAt
      (hOpen.mem_nhds hsD)
  have hLocal (i : powers) := (hasDerivAt_grandPrimePowerLogTerm d i (hTwo i) s).deriv
  change HasSum (fun i => deriv (grandPrimePowerLogTerm d i) s) (deriv (grandEulerLog d) s) at hSum
  simp only [hLocal] at hSum
  have hDeriv : deriv (grandEulerLog d) s =
      -tsum (fun i => (d.coefficient i : Complex) * (d.normPower i : Complex) ^ (-s)) := by
    rw [<- hSum.tsum_eq, tsum_neg]
  rw [<- hDeriv]
  exact hL.hasDerivAt

/-- The exponential Euler product gives right-half-plane nonvanishing
and the required logarithmic derivative of the pole-cleared function. -/
theorem grandEulerAnalytic_of_eulerLog {powers : Type*} [Countable powers]
    (d : GrandRobinEulerData powers) (m : Nat) (hPole : d.poleOrder = (m : Real))
    (hTwo : forall i, 2 <= d.normPower i)
    (hSummable : forall r : Real, 1 < r ->
      Summable (fun i => norm (d.coefficient i) * d.normPower i ^ (-r)))
    (hEuler : forall z : Complex, 1 < z.re ->
      d.poleRemoved z = (z - 1) ^ m * Complex.exp (grandEulerLog d z))
    {s : Complex} (hs : 1 < s.re) :
    And (Not (d.poleRemoved s = 0))
      (logDeriv d.poleRemoved s = (d.poleOrder : Complex) / (s - 1) -
        tsum (fun i => (d.coefficient i : Complex) * (d.normPower i : Complex) ^ (-s))) := by
  have hs1 : Not (s - 1 = 0) := by
    intro hz
    have hr := congrArg Complex.re (sub_eq_zero.mp hz)
    rw [Complex.one_re] at hr
    exact (ne_of_gt hs) hr
  have hPow := pow_ne_zero m hs1
  have hExp := Complex.exp_ne_zero (grandEulerLog d s)
  refine And.intro (by rw [hEuler s hs]; exact mul_ne_zero hPow hExp) ?_
  have hNear : Filter.EventuallyEq (nhds s) d.poleRemoved
      (fun z => (z - 1) ^ m * Complex.exp (grandEulerLog d z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact hEuler z hz
  have hD1 : HasDerivAt (fun z : Complex => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have hDL := hasDerivAt_grandEulerLog d hTwo hSummable hs
  have hDE : HasDerivAt (fun z => Complex.exp (grandEulerLog d z))
      (Complex.exp (grandEulerLog d s) *
        (-tsum (fun i => (d.coefficient i : Complex) * (d.normPower i : Complex) ^ (-s)))) s :=
    (Complex.hasDerivAt_exp (grandEulerLog d s)).comp s hDL
  rw [(logDeriv_congr_nhds hNear).eq_of_nhds,
    logDeriv_mul (f := fun z : Complex => (z - 1) ^ m)
      (g := fun z => Complex.exp (grandEulerLog d z)) s hPow hExp
      (hD1.differentiableAt.pow m) hDE.differentiableAt]
  have hLP : logDeriv (fun z : Complex => (z - 1) ^ m) s = (m : Complex) / (s - 1) := by
    rw [logDeriv_fun_pow hD1.differentiableAt, logDeriv_apply, hD1.deriv, mul_one_div]
  have hLE : logDeriv (fun z => Complex.exp (grandEulerLog d z)) s =
      -tsum (fun i => (d.coefficient i : Complex) * (d.normPower i : Complex) ^ (-s)) := by
    rw [logDeriv_apply, hDE.deriv]
    exact (div_eq_iff hExp).mpr (mul_comm _ _)
  rw [hLP, hLE, hPole, Complex.ofReal_natCast]
  exact (sub_eq_add_neg _ _).symm

/-- For a standard family with the exponential Euler product, the
criterion derives both nonvanishing and the logarithmic derivative on
the half-plane of absolute convergence from that product. -/
theorem grandRobinCompletedCriterion_of_eulerProduct
    {Representation : Type*} {powers : Representation -> Type*}
    {realPlaces complexPlaces : Representation -> Type*}
    [forall pi, Countable (powers pi)]
    [forall pi, Fintype (realPlaces pi)] [forall pi, Fintype (complexPlaces pi)]
    (completedL equationFactor : Representation -> Complex -> Complex)
    (dual : Representation -> Representation)
    (data : forall pi, GrandRobinEulerData (powers pi))
    (conductor : Representation -> Real) (originOrder : Representation -> Nat)
    (mu : forall pi, realPlaces pi -> Complex) (nu : forall pi, complexPlaces pi -> Complex)
    (hConductor : forall pi, 0 < conductor pi)
    (hMu : forall pi i, -(1 : Real) / 2 < (mu pi i).re)
    (hNu : forall pi i, -(1 : Real) / 2 < (nu pi i).re)
    (hPole : forall pi, (data pi).poleOrder = (originOrder pi : Real))
    (hTwo : forall pi i, 2 <= (data pi).normPower i)
    (hFinite : forall pi T, Set.Finite {i : powers pi | (data pi).normPower i < T})
    (hSummable : forall pi (r : Real), 1 < r ->
      Summable (fun i => norm ((data pi).coefficient i) * ((data pi).normPower i) ^ (-r)))
    (hEntire : forall pi, Differentiable Complex (data pi).poleRemoved)
    (hCompletedOrder : forall pi, EntireOfOrderAtMost 1 (completedL pi))
    (hEulerProduct : forall pi s, 1 < s.re ->
      (data pi).poleRemoved s = (s - 1) ^ (originOrder pi) * Complex.exp (grandEulerLog (data pi) s))
    (hCompletion : forall pi s, (1 / 2 : Real) < s.re ->
      completedL pi s * completedL (dual pi) s =
        standardCompletionFactor (conductor pi) (originOrder pi) (mu pi) (nu pi) s *
          (data pi).poleRemoved s)
    (hEquation : forall pi s, completedL (dual pi) (1 - s) =
      equationFactor pi s * completedL pi s) :
    CompletedFamilyRH completedL <-> forall pi, GrandRobinTriangularBound (data pi) := by
  have hInputs (pi : Representation) (s : Complex) (hs : 1 < s.re) :=
    grandEulerAnalytic_of_eulerLog (data pi) (originOrder pi) (hPole pi) (hTwo pi)
      (hSummable pi) (hEulerProduct pi) hs
  exact grandRobinCompletedCriterion_of_standardCompletion completedL equationFactor dual data
    conductor originOrder mu nu hConductor hMu hNu
    (fun pi i => (by norm_num : (1 : Real) <= 2).trans (hTwo pi i)) hFinite hSummable hEntire
    hCompletedOrder (fun pi s hs => (hInputs pi s hs).1)
    (fun pi s hs => (hInputs pi s hs).2) hCompletion hEquation

end Robin1984.GRH
