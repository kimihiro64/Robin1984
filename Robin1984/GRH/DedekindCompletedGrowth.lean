import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order
import Robin1984.GRH.DedekindCompleteContinuation
import Robin1984.GRH.MellinStretchedExponential

/-!
# Growth of the completed Dedekind zeta function

The two radial theta tails have stretched exponential decay. Their Mellin
moments give an exponential logarithmic growth bound for the entire
completed Dedekind zeta function after clearing its two poles.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The theta integral proof of order one for the completed Dedekind zeta function.
- Formalization note: Use the actual radial theta pair for every ideal class.
- Content basis: Mellin moment bounds, covolume normalization, and a finite class sum.
- Dependency status: Optional GRH extension and the pinned Dedekind-zeta theta modules.
-/

open Asymptotics Filter MeasureTheory NumberField Set
open scoped nonZeroDivisors

namespace Robin1984.GRH

noncomputable def logarithmicGrowthScale (s : Complex) : Real :=
  (1 + norm s) * Real.log (2 + norm s)

/-- A global upper bound of the form `A * exp (B * (1 + |s|) * log (2 + |s|))`. -/
def HasLogarithmicExponentialBound (f : Complex -> Complex) : Prop :=
  exists A B : Real, And (0 <= A) (And (0 <= B)
    (forall s : Complex, norm (f s) <= A * Real.exp (B * logarithmicGrowthScale s)))

private theorem logarithmicGrowthScale_nonneg (s : Complex) :
    0 <= logarithmicGrowthScale s :=
  mul_nonneg (add_nonneg zero_le_one (norm_nonneg _))
    (Real.log_nonneg (by linarith only [norm_nonneg s]))

private theorem logGrowth_const (c : Complex) :
    HasLogarithmicExponentialBound (fun _ => c) := by
  refine Exists.intro (norm c) (Exists.intro 0 (And.intro (norm_nonneg _) (And.intro le_rfl ?_)))
  intro s
  simp

private theorem logGrowth_id : HasLogarithmicExponentialBound (fun s => s) := by
  refine Exists.intro 1 (Exists.intro 1 (And.intro zero_le_one (And.intro zero_le_one ?_)))
  intro s
  change norm s <= 1 * Real.exp (1 * logarithmicGrowthScale s)
  simp only [one_mul]
  have hLog : 0 <= Real.log (2 + norm s) :=
    Real.log_nonneg (by linarith only [norm_nonneg s])
  calc
    _ <= 2 + norm s := by linarith
    _ = Real.exp (Real.log (2 + norm s)) :=
      (Real.exp_log (by linarith only [norm_nonneg s])).symm
    _ <= _ := Real.exp_le_exp.mpr (by
      unfold logarithmicGrowthScale
      nlinarith only [mul_nonneg (norm_nonneg s) hLog])

private theorem logGrowth_add {f g : Complex -> Complex}
    (hf : HasLogarithmicExponentialBound f) (hg : HasLogarithmicExponentialBound g) :
    HasLogarithmicExponentialBound (fun s => f s + g s) := by
  choose Af Bf hF using hf
  choose Ag Bg hG using hg
  let B := max Bf Bg
  refine Exists.intro (Af + Ag) (Exists.intro B
    (And.intro (add_nonneg hF.1 hG.1) (And.intro (hF.2.1.trans (le_max_left _ _)) ?_)))
  intro s
  have hE (b : Real) (hb : b <= B) :
      Real.exp (b * logarithmicGrowthScale s) <= Real.exp (B * logarithmicGrowthScale s) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb (logarithmicGrowthScale_nonneg s))
  calc
    _ <= norm (f s) + norm (g s) := norm_add_le _ _
    _ <= Af * Real.exp (B * logarithmicGrowthScale s) +
        Ag * Real.exp (B * logarithmicGrowthScale s) :=
      add_le_add ((hF.2.2 s).trans (mul_le_mul_of_nonneg_left (hE Bf (le_max_left _ _)) hF.1))
        ((hG.2.2 s).trans (mul_le_mul_of_nonneg_left (hE Bg (le_max_right _ _)) hG.1))
    _ = _ := (add_mul _ _ _).symm

private theorem logGrowth_mul {f g : Complex -> Complex}
    (hf : HasLogarithmicExponentialBound f) (hg : HasLogarithmicExponentialBound g) :
    HasLogarithmicExponentialBound (fun s => f s * g s) := by
  choose Af Bf hF using hf
  choose Ag Bg hG using hg
  refine Exists.intro (Af * Ag) (Exists.intro (Bf + Bg)
    (And.intro (mul_nonneg hF.1 hG.1) (And.intro (add_nonneg hF.2.1 hG.2.1) ?_)))
  intro s
  rw [norm_mul]
  calc
    _ <= (Af * Real.exp (Bf * logarithmicGrowthScale s)) *
        (Ag * Real.exp (Bg * logarithmicGrowthScale s)) :=
      mul_le_mul (hF.2.2 s) (hG.2.2 s) (norm_nonneg _)
        (mul_nonneg hF.1 (Real.exp_pos _).le)
    _ = _ := by rw [add_mul, Real.exp_add]; ring

private theorem logGrowth_cpow_of_pos {b : Real} (hb : 0 < b) :
    HasLogarithmicExponentialBound (fun s => (b : Complex) ^ s) := by
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B := abs (Real.log b) / Real.log 2
  have hB : 0 <= B := div_nonneg (abs_nonneg _) hLog2.le
  refine Exists.intro 1 (Exists.intro B (And.intro zero_le_one (And.intro hB ?_)))
  intro s
  rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb, Real.rpow_def_of_pos hb]
  apply Real.exp_le_exp.mpr
  have hRe := Complex.re_le_norm (-s)
  rw [Complex.neg_re, norm_neg] at hRe
  have hAbsRe : abs s.re <= norm s :=
    abs_le.mpr (And.intro (by linarith only [hRe]) (Complex.re_le_norm s))
  have hB2 : B * Real.log 2 = abs (Real.log b) := by
    unfold B
    field_simp [hLog2.ne']
  have hNorm1 : norm s <= 1 + norm s := by linarith
  calc
    _ <= abs (Real.log b * s.re) := le_abs_self _
    _ = abs (Real.log b) * abs s.re := abs_mul _ _
    _ <= abs (Real.log b) * (1 + norm s) :=
      mul_le_mul_of_nonneg_left (hAbsRe.trans hNorm1) (abs_nonneg _)
    _ = (B * (1 + norm s)) * Real.log 2 := by rw [<- hB2]; ring
    _ <= _ := by
      unfold logarithmicGrowthScale
      rw [<- mul_assoc]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num)
        (le_add_of_nonneg_right (norm_nonneg _)))
        (mul_nonneg hB (add_nonneg zero_le_one (norm_nonneg _)))

private theorem stretchedExp_bound_of_isBigO {f : Real -> Complex} {a p : Real}
    (ha : 0 < a) (hp : 0 < p) (hc : ContinuousOn f (Ioi (0 : Real)))
    (hd : Asymptotics.IsBigO atTop f (fun t : Real => Real.exp (-a * t ^ p))) :
    exists A : Real, And (0 <= A)
      (forall t : Real, 1 <= t -> norm (f t) <= A * Real.exp (-a * t ^ p)) := by
  choose A hA hAE using hd.exists_nonneg
  choose Y hY using eventually_atTop.mp hAE.bound
  let M := max Y 1
  have hM : 1 <= M := le_max_right _ _
  have hC : ContinuousOn f (Icc (1 : Real) M) :=
    hc.mono (fun t ht => zero_lt_one.trans_le ht.1)
  choose B hB using isCompact_Icc.exists_bound_of_continuousOn hC
  have hB0 : 0 <= B := (norm_nonneg (f 1)).trans (hB 1 (And.intro le_rfl hM))
  let D := B * Real.exp (a * M ^ p)
  refine Exists.intro (max A D) (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro t ht
  by_cases h : Y <= t
  case pos =>
    have htY := hY t h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at htY
    exact htY.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  case neg =>
    have htM := (le_of_not_ge h).trans (le_max_left Y 1)
    have hPow := Real.rpow_le_rpow (zero_le_one.trans ht) htM hp.le
    have hE : 1 <= Real.exp (a * M ^ p) * Real.exp (-a * t ^ p) := by
      rw [<- Real.exp_add, <- Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hPow ha.le])
    calc
      _ <= B := hB t (And.intro ht htM)
      _ <= D * Real.exp (-a * t ^ p) := by
        unfold D
        rw [mul_assoc]
        exact le_mul_of_one_le_right hB0 hE
      _ <= _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

private theorem logGrowth_mellinMoment {f : Real -> Complex} {a p : Real}
    (ha : 0 < a) (hp : 0 < p) (hc : ContinuousOn f (Ioi (0 : Real)))
    (hd : Asymptotics.IsBigO atTop f (fun t : Real => Real.exp (-a * t ^ p)))
    (hi : forall s : Complex, IntegrableOn
      (fun t : Real => f t * (t : Complex) ^ (s - 1)) (Ioi (1 : Real)))
    (z : Complex -> Complex) (hz : forall s : Complex, (z s).re - 1 <= norm s) :
    HasLogarithmicExponentialBound (fun s =>
      integral (volume.restrict (Ioi (1 : Real))) (fun t : Real => f t * (t : Complex) ^ (z s - 1))) := by
  choose A hA using stretchedExp_bound_of_isBigO ha hp hc hd
  choose C K hK using norm_mellinMoment_le_logarithmicGrowth f hA.1 ha hp hA.2 hi
  refine Exists.intro C (Exists.intro K (And.intro hK.1 (And.intro hK.2.1 ?_)))
  intro s
  simpa only [logarithmicGrowthScale, mul_assoc] using hK.2.2 (z s) (norm s) (norm_nonneg _) (hz s)

open DedekindZeta DedekindZeta.MellinPrinciple DedekindZeta.ConeRadialReduction

private theorem logGrowth_mellinTail {f g : Real -> Complex} {b C : Complex} {a p : Real}
    (h : IsMellinPair f g b b C 1 a p) :
    HasLogarithmicExponentialBound (mellinTail f g b b C 1) := by
  have hp : 0 < p := by
    cases h with
    | mk _ _ _ _ hp _ _ _ _ => exact hp
  have hF := logGrowth_mellinMoment h.hc hp (h.hf_cont.sub continuousOn_const)
    h.hf_decay (fun _ => mellinTail_integrable_left h) (fun s => s)
    (fun s => (sub_le_self _ zero_le_one).trans (Complex.re_le_norm s))
  have hG := logGrowth_mellinMoment h.hc hp (h.hg_cont.sub continuousOn_const)
    h.hg_decay (fun _ => mellinTail_integrable_left h.swap) (fun s => 1 - s) (fun s => by
      have hs := Complex.re_le_norm (-s)
      rw [Complex.neg_re, norm_neg] at hs
      rw [Complex.sub_re, Complex.one_re]
      linarith only [hs])
  have hSum := logGrowth_add hF (logGrowth_mul (logGrowth_const C) hG)
  choose A B hB using hSum
  refine Exists.intro A (Exists.intro B (And.intro hB.1 (And.intro hB.2.1 ?_)))
  intro s
  unfold mellinTail
  rw [integral_add (mellinTail_integrable_left h) (mellinTail_integrable_right h)]
  simp only [Complex.ofReal_one, mul_assoc, integral_const_mul]
  exact hB.2.2 s

private theorem logGrowth_poleClearedMellin {f g : Real -> Complex}
    {b C : Complex} {a p : Real} (h : IsMellinPair f g b b C 1 a p) :
    HasLogarithmicExponentialBound (poleClearedMellin f g b C) := by
  have hSub : HasLogarithmicExponentialBound (fun s : Complex => s - 1) := by
    simpa only [sub_eq_add_neg] using logGrowth_add logGrowth_id (logGrowth_const (-1))
  exact logGrowth_add
    (logGrowth_add (logGrowth_mul (logGrowth_const (-b)) hSub)
      (logGrowth_mul (logGrowth_const (C * b)) logGrowth_id))
    (logGrowth_mul (logGrowth_mul logGrowth_id hSub) (logGrowth_mellinTail h))

private theorem logGrowth_completedIdealPoleCleared (K : Type*) [Field K] [NumberField K]
    (a : Ideal (RingOfIntegers K)) (ha : Not (a = 0)) :
    HasLogarithmicExponentialBound (completedIdealPoleCleared K a) := by
  have hCov : 0 < Theta.covolume K a := by
    rw [Theta.covolume]
    apply mul_pos
    case ha =>
      exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff (I := a)).not.mpr ha)
    case hb =>
      exact Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  choose c alpha hPair using exists_isMellinPair_radialTheta (K := K) a ha
  exact logGrowth_mul (logGrowth_mul (logGrowth_const (1 / (Units.torsionOrder K : Complex)))
    (logGrowth_cpow_of_pos hCov)) (logGrowth_poleClearedMellin hPair)

private theorem logGrowth_finset_sum {I : Type*} (S : Finset I) (f : I -> Complex -> Complex)
    (hf : forall i, Membership.mem S i -> HasLogarithmicExponentialBound (f i)) :
    HasLogarithmicExponentialBound (fun z => S.sum (fun i => f i z)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using logGrowth_const 0
  | insert i S hi ih =>
    have hHead := hf i (Finset.mem_insert_self _ _)
    have hTail := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using logGrowth_add hHead hTail

/-- The completed Dedekind zeta, with its poles cleared, satisfies the
global logarithmic exponential growth estimate. -/
theorem completedDedekindPoleCleared_logarithmicGrowth (K : Type*) [Field K] [NumberField K] :
    HasLogarithmicExponentialBound (completedDedekindPoleCleared K) := by
  unfold completedDedekindPoleCleared
  apply logGrowth_finset_sum
  intro c _
  apply logGrowth_completedIdealPoleCleared
  let I : (nonZeroDivisors (Ideal (RingOfIntegers K))) :=
    Function.surjInv ClassGroup.mk0_surjective c
  exact mem_nonZeroDivisors_iff_ne_zero.mp I.property

/-- The pole-cleared completed Dedekind zeta function is entire of order
at most one, with the epsilon margins used in Hadamard factorization. -/
theorem completedDedekindPoleCleared_entireOfOrderAtMost_one
    (K : Type*) [Field K] [NumberField K] :
    Complex.Hadamard.EntireOfOrderAtMost 1 (completedDedekindPoleCleared K) := by
  refine And.intro (fun s => (analyticAt_completedDedekindPoleCleared K s).differentiableAt) ?_
  choose A B hAB using completedDedekindPoleCleared_logarithmicGrowth K
  intro eps heps
  let c : Real := (2 : Real) ^ eps / eps
  let D := Real.log (A + 1) + B * c + 1
  have hA1 : 0 < A + 1 := add_pos_of_nonneg_of_pos hAB.1 zero_lt_one
  have hLogA : 0 <= Real.log (A + 1) :=
    Real.log_nonneg (by linarith only [hAB.1])
  have h2 : (0 : Real) < 2 := by norm_num
  have hc : 0 <= c := div_nonneg (Real.rpow_pos_of_pos h2 eps).le heps.le
  have hD : 0 < D :=
    add_pos_of_nonneg_of_pos (add_nonneg hLogA (mul_nonneg hAB.2.1 hc)) zero_lt_one
  refine Exists.intro D (And.intro hD ?_)
  intro s
  let u := 1 + norm s
  let v := 2 + norm s
  have hu1 : 1 <= u := le_add_of_nonneg_right (norm_nonneg _)
  have hu : 0 < u := zero_lt_one.trans_le hu1
  have hv : 0 < v := add_pos_of_pos_of_nonneg h2 (norm_nonneg _)
  have hvu : v <= 2 * u := by unfold u v; linarith only [norm_nonneg s]
  have hvLog : Real.log v <= v ^ eps / eps := by
    have h := Real.add_one_le_exp (Real.log v * eps)
    rw [<- Real.rpow_def_of_pos hv eps] at h
    have h' : Real.log v * eps <= v ^ eps := by linarith only [h]
    have h'' := div_le_div_of_nonneg_right h' heps.le
    rwa [show Real.log v * eps / eps = Real.log v from by field_simp [heps.ne']] at h''
  have huPow : u * u ^ eps = u ^ (1 + eps) := by
    rw [Real.rpow_add hu, Real.rpow_one]
  have hScale : logarithmicGrowthScale s <= c * u ^ (1 + eps) := calc
    _ = u * Real.log v := rfl
    _ <= u * (v ^ eps / eps) := mul_le_mul_of_nonneg_left hvLog hu.le
    _ <= u * ((2 * u) ^ eps / eps) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Real.rpow_le_rpow hv.le hvu heps.le) heps.le) hu.le
    _ = c * (u * u ^ eps) := by
      rw [Real.mul_rpow h2.le hu.le]
      unfold c
      ring
    _ = _ := by rw [huPow]
  have hPow1 : 1 <= u ^ (1 + eps) :=
    Real.one_le_rpow hu1 (add_nonneg zero_le_one heps.le)
  have hExp : Real.log (A + 1) + B * logarithmicGrowthScale s <= D * u ^ (1 + eps) := calc
    _ <= Real.log (A + 1) * u ^ (1 + eps) + B * (c * u ^ (1 + eps)) :=
      add_le_add (le_mul_of_one_le_right hLogA hPow1)
        (mul_le_mul_of_nonneg_left hScale hAB.2.1)
    _ = (Real.log (A + 1) + B * c) * u ^ (1 + eps) := by ring
    _ <= _ := mul_le_mul_of_nonneg_right (by unfold D; linarith) (zero_le_one.trans hPow1)
  calc
    _ <= A * Real.exp (B * logarithmicGrowthScale s) := hAB.2.2 s
    _ <= (A + 1) * Real.exp (B * logarithmicGrowthScale s) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = Real.exp (Real.log (A + 1) + B * logarithmicGrowthScale s) := by
      rw [Real.exp_add, Real.exp_log hA1]
    _ <= _ := Real.exp_le_exp.mpr hExp


end Robin1984.GRH
