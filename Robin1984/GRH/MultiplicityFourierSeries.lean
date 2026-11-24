import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Sequences

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Cesaro means and simultaneous phase recurrence for absolutely convergent Fourier series.
- Formalization note: Complex orthogonality gives the squared mean, compactness supplies recurrence for the upper limit, and the convolution lemmas connect these identities to the arithmetic signal.
- PROVENANCE-END
-/

/-!
# Global Fourier criterion for multiplicity

For spectra with a common positive weight and its square, the squared
mean is bounded by the second spectrum's upper limit exactly when every
multiplicity is at most one. Convolution acts on each frequency by its
Fourier multiplier.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Filter MeasureTheory Set
open scoped Topology Interval Classical

/-- The complex average over time from zero to T. -/
def fourierCesaro (f : Real -> Complex) (T : Real) : Complex :=
  Inv.inv (T : Complex) * intervalIntegral f 0 T volume

theorem fourierCesaro_constant_one_tendsto :
    Tendsto (fourierCesaro (fun _ => 1)) atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : Real)] with T hT
  have ht : Not ((T : Complex) = 0) := by
    exact_mod_cast (zero_lt_one.trans_le hT).ne'
  unfold fourierCesaro
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul, mul_one]
  field_simp [ht]

/-- Averaging a nonconstant pure Fourier mode over a real interval gives zero. -/
theorem fourierCesaro_nonconstant_tendsto_zero (c : Complex)
    (hc : Not (c = 0)) (hre : c.re = 0) :
    Tendsto (fourierCesaro (fun t => Complex.exp (c * (t : Complex)))) atTop (nhds 0) := by
  have hnorm (t : Real) : norm (Complex.exp (c * (t : Complex))) = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, hre]
  have hbound : Filter.Eventually (fun T : Real =>
      norm (fourierCesaro (fun t => Complex.exp (c * (t : Complex))) T) <=
        Inv.inv T * (2 / norm c)) atTop := by
    filter_upwards [eventually_ge_atTop (1 : Real)] with T hT
    have hTp : 0 < T := zero_lt_one.trans_le hT
    unfold fourierCesaro
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTp.le, norm_div]
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ (norm_nonneg c))
      (inv_nonneg.mpr hTp.le)
    calc
      norm (Complex.exp (c * (T : Complex)) - 1) <= norm (Complex.exp (c * (T : Complex))) +
        norm (1 : Complex) := norm_sub_le _ _
      _ = 2 := by rw [hnorm, norm_one]; norm_num
  have hlim : Tendsto (fun t : Real => Inv.inv t * (2 / norm c)) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_inv_atTop_zero : Tendsto (fun t : Real => Inv.inv t) atTop (nhds 0)).mul
        (tendsto_const_nhds : Tendsto (fun _ : Real => 2 / norm c) atTop (nhds (2 / norm c)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hbound hlim

/-- The mean of an absolutely summable pure Fourier series is its zero-frequency mass. -/
theorem fourierCesaro_tsum_tendsto {i : Type*} [Countable i]
    (a c : i -> Complex) (hc : forall j, (c j).re = 0)
    (ha : Summable (fun j => norm (a j))) :
    Tendsto (fourierCesaro (fun t => tsum (fun j => a j * Complex.exp (c j * (t : Complex)))))
      atTop (nhds (tsum (fun j => if c j = 0 then a j else 0))) := by
  let wave (j : i) (t : Real) := a j * Complex.exp (c j * (t : Complex))
  have hcont (j : i) : Continuous (wave j) :=
    continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hnorm (j : i) (t : Real) : norm (wave j t) = norm (a j) := by
    unfold wave
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re, hc j]
  have hIntNorm (j : i) (T : Real) (hT : 0 <= T) :
      integral (volume.restrict (Set.Ioc 0 T)) (fun x => norm (wave j x)) = T * norm (a j) := by
    rw [<- intervalIntegral.integral_of_le hT]
    simp only [hnorm, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hPoint (j : i) : Tendsto (fourierCesaro (wave j)) atTop
      (nhds (if c j = 0 then a j else 0)) := by
    have hCoeff : fourierCesaro (wave j) =
        fun T => a j * fourierCesaro (fun t => Complex.exp (c j * (t : Complex))) T := by
      funext T
      unfold fourierCesaro wave
      rw [intervalIntegral.integral_const_mul]
      ac_rfl
    rw [hCoeff]
    by_cases hz : c j = 0
    case pos =>
      simpa only [hz, zero_mul, Complex.exp_zero, if_true, mul_one] using
        fourierCesaro_constant_one_tendsto.const_mul (a j)
    case neg =>
      simpa only [if_neg hz, mul_zero] using
        (fourierCesaro_nonconstant_tendsto_zero (c j) hz (hc j)).const_mul (a j)
  have hBound : Filter.Eventually (fun T : Real =>
      forall j : i, norm (fourierCesaro (wave j) T) <= norm (a j)) atTop := by
    filter_upwards [eventually_ge_atTop (1 : Real)] with T hT
    intro j
    have hpos : 0 < T := zero_lt_one.trans_le hT
    have hInt : norm (integral (volume.restrict (Set.Ioc 0 T)) (wave j)) <=
        integral (volume.restrict (Set.Ioc 0 T)) (fun x => norm (wave j x)) :=
      norm_integral_le_integral_norm (wave j)
    rw [hIntNorm j T hpos.le] at hInt
    unfold fourierCesaro
    rw [intervalIntegral.integral_of_le hpos.le, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hpos.le]
    calc
      _ <= Inv.inv T * (T * norm (a j)) := mul_le_mul_of_nonneg_left hInt
        (inv_nonneg.mpr hpos.le)
      _ = norm (a j) := by field_simp [hpos.ne']
  have hLim := tendsto_tsum_of_dominated_convergence ha hPoint hBound
  apply hLim.congr'
  filter_upwards [eventually_ge_atTop (0 : Real)] with T hT
  have hEach (j : i) : Integrable (wave j) (volume.restrict (Set.Ioc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp ((hcont j).intervalIntegrable 0 T)
  have hSum : Summable (fun j => integral (volume.restrict (Set.Ioc 0 T))
      (fun x => norm (wave j x))) := by
    simpa only [hIntNorm _ _ hT] using ha.mul_left T
  change tsum (fun j => fourierCesaro (wave j) T) =
    fourierCesaro (fun t => tsum (fun j => wave j t)) T
  simp only [fourierCesaro, intervalIntegral.integral_of_le hT]
  rw [<- integral_tsum_of_summable_integral_norm hEach hSum, tsum_mul_left]

private theorem fourier_phasePair (a b x y : Complex) (t : Real) (hy : y.re = 0) :
    (a * Complex.exp (x * (t : Complex))) *
      (starRingEnd Complex) (b * Complex.exp (y * (t : Complex))) =
    (a * (starRingEnd Complex) b) * Complex.exp ((x - y) * (t : Complex)) := by
  have hY : (starRingEnd Complex) y = -y := by
    apply Complex.ext <;> simp [hy]
  rw [map_mul, <- Complex.exp_conj, map_mul, hY, Complex.conj_ofReal,
    sub_mul, sub_eq_add_neg, Complex.exp_add, neg_mul]
  ac_rfl

private theorem fourier_normSq_tsum_eq_pair {i : Type*}
    (a c : i -> Complex) (hc : forall j, (c j).re = 0)
    (ha : Summable (fun j => norm (a j))) (t : Real) :
    ((norm (tsum (fun j => a j * Complex.exp (c j * (t : Complex)))) ^ 2 : Real) : Complex) =
      tsum (fun p : Prod i i => (a p.1 * (starRingEnd Complex) (a p.2)) *
        Complex.exp ((c p.1 - c p.2) * (t : Complex))) := by
  let f (j : i) : Complex := a j * Complex.exp (c j * (t : Complex))
  have hWave (j : i) : norm (f j) = norm (a j) := by
    unfold f
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re, hc j]
  have hF : Summable (fun j => norm (f j)) := by simpa only [hWave] using ha
  let g (j : i) : Complex := (starRingEnd Complex) (f j)
  have hG : Summable (fun j => norm (g j)) := by simpa only [g, Complex.norm_conj] using hF
  have hConj : (starRingEnd Complex) (tsum f) = tsum g :=
    Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.map_tsum hF.of_norm
  have hProd : tsum f * tsum g = tsum (fun p : Prod i i => f p.1 * g p.2) :=
    tsum_mul_tsum_of_summable_norm hF hG
  change ((norm (tsum f) ^ 2 : Real) : Complex) = _
  rw [Complex.ofReal_pow, <- Complex.mul_conj' (tsum f), hConj, hProd]
  exact tsum_congr (fun p => fourier_phasePair (a p.1) (a p.2) (c p.1) (c p.2) t (hc p.2))

private theorem fourier_diagonalMass_eq {i : Type*}
    (a c : i -> Complex) (hDistinct : Function.Injective c) :
    tsum (fun p : Prod i i => if c p.1 - c p.2 = 0 then
      a p.1 * (starRingEnd Complex) (a p.2) else 0) =
      tsum (fun j => ((norm (a j) ^ 2 : Real) : Complex)) := by
  classical
  let A (p : Prod i i) : Complex := a p.1 * (starRingEnd Complex) (a p.2)
  let diag : Set (Prod i i) := {p | p.1 = p.2}
  have hIndicator : (fun p : Prod i i => if c p.1 - c p.2 = 0 then A p else 0) =
      Set.indicator diag A := by
    funext p
    by_cases h : p.1 = p.2
    case pos => simp [diag, h]
    case neg =>
      have hn : Not (c p.1 = c p.2) := fun he => h (hDistinct he)
      have hz : Not (c p.1 - c p.2 = 0) := fun he => hn (sub_eq_zero.mp he)
      simp [diag, h, hz]
  change tsum (fun p : Prod i i => if c p.1 - c p.2 = 0 then A p else 0) = _
  rw [hIndicator, <- tsum_subtype]
  let q : Equiv i diag :=
    { toFun := fun j => Subtype.mk (Prod.mk j j) rfl
      invFun := fun p => p.val.1
      left_inv := fun _ => rfl
      right_inv := fun p => Subtype.ext (Prod.ext rfl p.property) }
  rw [<- q.tsum_eq (fun p : diag => A p.val)]
  refine tsum_congr ?_
  intro j
  change a j * (starRingEnd Complex) (a j) = ((norm (a j) ^ 2 : Real) : Complex)
  rw [Complex.ofReal_pow]
  exact Complex.mul_conj' (a j)

set_option maxHeartbeats 650000 in
/-- Mean-square orthogonality for an absolutely summable series of distinct Fourier modes. -/
theorem fourierCesaro_normSq_tsum_tendsto {i : Type*} [Countable i]
    (a c : i -> Complex) (hc : forall j, (c j).re = 0) (hDistinct : Function.Injective c)
    (ha : Summable (fun j => norm (a j))) :
    Tendsto (fourierCesaro (fun t =>
      ((norm (tsum (fun j => a j * Complex.exp (c j * (t : Complex)))) ^ 2 : Real) : Complex)))
      atTop (nhds (tsum (fun j => ((norm (a j) ^ 2 : Real) : Complex)))) := by
  let A (p : Prod i i) : Complex := a p.1 * (starRingEnd Complex) (a p.2)
  let D (p : Prod i i) : Complex := c p.1 - c p.2
  have hD (p : Prod i i) : (D p).re = 0 := by
    simp only [D, Complex.sub_re, hc, sub_self]
  have haC : Summable (fun j => norm ((starRingEnd Complex) (a j))) := by
    simpa only [Complex.norm_conj] using ha
  have hA : Summable (fun p : Prod i i => norm (A p)) :=
    Summable.mul_norm (f := a) (g := fun j => (starRingEnd Complex) (a j)) ha haC
  have hInput : (fun t : Real => ((norm (tsum (fun j => a j *
      Complex.exp (c j * (t : Complex)))) ^ 2 : Real) : Complex)) =
      fun t : Real => tsum (fun p : Prod i i => A p * Complex.exp (D p * (t : Complex))) :=
    funext (fourier_normSq_tsum_eq_pair a c hc ha)
  have hMean := fourierCesaro_tsum_tendsto A D hD hA
  have hResult : tsum (fun p : Prod i i => if D p = 0 then A p else 0) =
      tsum (fun j => ((norm (a j) ^ 2 : Real) : Complex)) :=
    fourier_diagonalMass_eq a c hDistinct
  simpa only [<- hInput, hResult] using hMean

private theorem exists_tendsto_near_unity_fourier_phases {i : Type*} [Countable i]
    (gamma : i -> Real) :
    exists time : Nat -> Real, Tendsto time atTop atTop /\
      forall j, Tendsto (fun n => Complex.exp (((gamma j * time n : Real) : Complex) *
        Complex.I)) atTop (nhds 1) := by
  let seq (n : Nat) (j : i) : Circle := Circle.exp (gamma j * (n : Real))
  have hx (n : Nat) : Membership.mem (Set.univ : Set (i -> Circle)) (seq n) :=
    Set.mem_univ _
  choose l hl phi hphi hLim using (isCompact_univ : IsCompact
    (Set.univ : Set (i -> Circle))).tendsto_subseq hx
  have hGap (n k : Nat) : phi n + k <= phi (n + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      exact Nat.succ_le_of_lt (ih.trans_lt (hphi (Nat.lt_succ_self (n + k))))
  let d (n : Nat) : Nat := phi (n + n) - phi n
  have hd (n : Nat) : n <= d n := Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hGap n n)
  have hLeap : Tendsto (fun n : Nat => n + n) atTop atTop :=
    tendsto_atTop.2 (fun N => (eventually_ge_atTop N).mono fun n hn =>
      hn.trans (Nat.le_add_right n n))
  refine Exists.intro (fun n => (d n : Real)) (And.intro ?_ ?_)
  case refine_1 =>
    apply tendsto_atTop.2
    intro b
    choose N hN using exists_nat_ge b
    exact (eventually_ge_atTop N).mono (fun n hn =>
      hN.trans (by exact_mod_cast hn.trans (hd n)))
  case refine_2 =>
    intro j
    have hj : Tendsto (fun n : Nat => seq (phi n) j) atTop (nhds (l j)) :=
      tendsto_pi_nhds.mp hLim j
    have hV : Tendsto (fun n : Nat => (seq (phi n) j : Complex)) atTop
        (nhds (l j : Complex)) :=
      continuous_subtype_val.continuousAt.tendsto.comp hj
    have hnz : Not ((l j : Complex) = 0) := by
      intro h
      have hz := Circle.norm_coe (l j)
      rw [h, norm_zero] at hz
      exact zero_ne_one hz
    have hRatio := (hV.comp hLeap).div hV hnz
    rw [div_self hnz] at hRatio
    convert hRatio using 1
    funext n
    change Complex.exp (((gamma j * (d n : Real) : Real) : Complex) * Complex.I) =
      (seq (phi (n + n)) j : Complex) / (seq (phi n) j : Complex)
    have hOrder := hphi.monotone (Nat.le_add_right n n)
    unfold d seq
    rw [Nat.cast_sub hOrder, mul_sub, Complex.ofReal_sub, sub_mul, Complex.exp_sub]
    rfl

/-- For nonnegative, summable Fourier amplitudes, the upper limit of the real
part of the series is its total amplitude. -/
theorem limsup_re_positive_fourierSeries_eq_tsum {i : Type*} [Countable i]
    (w gamma : i -> Real) (hW : forall j, 0 <= w j) (hSum : Summable w) :
    Filter.limsup (fun t : Real => (tsum (fun j => (w j : Complex) *
      Complex.exp (((gamma j * t : Real) : Complex) * Complex.I))).re) atTop =
      tsum w := by
  let wave (j : i) (t : Real) : Complex :=
    (w j : Complex) * Complex.exp (((gamma j * t : Real) : Complex) * Complex.I)
  let S (t : Real) : Complex := tsum (fun j => wave j t)
  let M : Real := tsum w
  have hNorm (j : i) (t : Real) : norm (wave j t) = w j := by
    unfold wave
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hW j)]
  have hBound (t : Real) : norm (S t) <= M := by
    have hn : Summable (fun j => norm (wave j t)) := by
      simpa only [hNorm] using hSum
    have h := norm_tsum_le_tsum_norm hn
    simpa only [hNorm] using h
  have hRe (t : Real) : -(M) <= (S t).re /\ (S t).re <= M :=
    abs_le.mp ((Complex.abs_re_le_norm (S t)).trans (hBound t))
  have hUpper : IsBoundedUnder (fun a b : Real => a <= b) atTop (fun t => (S t).re) :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall (fun t => (hRe t).2))
  have hLower : IsCoboundedUnder (fun a b : Real => a <= b) atTop (fun t => (S t).re) :=
    IsCoboundedUnder.of_frequently_ge
      ((Filter.Eventually.of_forall (fun t => (hRe t).1)).frequently)
  change Filter.limsup (fun t : Real => (S t).re) atTop = M
  refine le_antisymm (limsup_le_of_le hLower (Filter.Eventually.of_forall (fun t => (hRe t).2))) ?_
  choose time hTime hPhase using exists_tendsto_near_unity_fourier_phases gamma
  have hEach (j : i) : Tendsto (fun n => wave j (time n)) atTop (nhds (w j : Complex)) := by
    simpa only [wave, mul_one] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (w j : Complex)) atTop
        (nhds (w j : Complex))).mul (hPhase j)
  have hS : Tendsto (fun n => S (time n)) atTop (nhds (M : Complex)) := by
    rw [Complex.ofReal_tsum]
    exact tendsto_tsum_of_dominated_convergence hSum hEach
      (Filter.Eventually.of_forall (fun n j => (hNorm j (time n)).le))
  have hR : Tendsto (fun n => (S (time n)).re) atTop (nhds M) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hS
  by_contra h
  have hlt : Filter.limsup (fun t : Real => (S t).re) atTop < M := lt_of_not_ge h
  let b := (Filter.limsup (fun t : Real => (S t).re) atTop + M) / 2
  have hb : b < M := by dsimp [b]; linarith only [hlt]
  have hcb : Filter.limsup (fun t : Real => (S t).re) atTop < b := by dsimp [b]; linarith only [hlt]
  have hFreq : Filter.Frequently (fun t : Real => b <= (S t).re) atTop := by
    apply frequently_atTop.2
    intro L
    have hL := (tendsto_atTop.1 hTime) L
    have hB := hR.eventually (lt_mem_nhds hb)
    choose n hn using (hL.and hB).exists
    exact Exists.intro (time n) (And.intro hn.1 hn.2.le)
  exact (not_le_of_gt hcb) (le_limsup_of_frequently_le hFreq hUpper)

/-- Comparing the weighted square and first powers detects orders above one. -/
theorem global_weighted_multiplicity_iff {i : Type*} (m : i -> Nat) (w : i -> Real)
    (hw : forall j, 0 < w j)
    (hE : Summable (fun j => w j * (m j : Real) ^ 2))
    (hS : Summable (fun j => w j * (m j : Real))) :
    (tsum (fun j => w j * (m j : Real) ^ 2) <= tsum (fun j => w j * (m j : Real))) <->
      (forall j, m j <= 1) := by
  let d : i -> Real := fun j => w j * (m j : Real) ^ 2 - w j * (m j : Real)
  have hD : Summable d := hE.sub hS
  have hnonneg : forall j, 0 <= d j := by
    intro j
    by_cases h0 : m j = 0
    case pos => simp [d, h0]
    case neg =>
      have hm : 1 <= (m j : Real) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have h0m : 0 <= (m j : Real) := by positivity
      have hsq : (m j : Real) <= (m j : Real) ^ 2 := by
        simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hm h0m
      exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left hsq (hw j).le)
  constructor
  case mp =>
    intro h j
    have hz : tsum d <= 0 := by
      unfold d
      rw [hE.tsum_sub hS]
      exact sub_nonpos.mpr h
    have hdj : d j <= 0 := (hD.le_tsum j (fun a _ => hnonneg a)).trans hz
    by_contra hj
    have hm : 1 < (m j : Real) := by exact_mod_cast lt_of_not_ge hj
    have hp : 0 < (m j : Real) := zero_lt_one.trans hm
    have hsq : (m j : Real) < (m j : Real) ^ 2 := by
      simpa only [mul_one, pow_two] using mul_lt_mul_of_pos_left hm hp
    have hdj' : 0 < d j := sub_pos.mpr (mul_lt_mul_of_pos_left hsq (hw j))
    exact (not_lt_of_ge hdj) hdj'
  case mpr =>
    intro h
    have hEq : (fun j => w j * (m j : Real) ^ 2) = fun j => w j * (m j : Real) := by
      funext j
      cases Nat.le_one_iff_eq_zero_or_eq_one.mp (h j) with
      | inl hj => simp [hj]
      | inr hj => simp [hj]
    rw [hEq]

/-- The squared mean of one spectrum is at most the upper limit of the
other exactly when each zero has multiplicity at most one. The two spectra
use the same positive weight and its square, respectively. -/
theorem fourierSpectrumMultiplicityCriterion {i : Type*} [Countable i]
    (m : i -> Nat) (w gamma : i -> Real) (hPositive : forall j, 0 < w j)
    (hDistinct : Function.Injective gamma)
    (hFirst : Summable (fun j => (m j : Real) * w j))
    (hSecond : Summable (fun j => w j ^ 2 * (m j : Real)))
    (hSquare : Summable (fun j => w j ^ 2 * (m j : Real) ^ 2)) :
    (Filter.limsup (fun T : Real => (fourierCesaro (fun t =>
      ((norm (tsum (fun j => ((m j : Real) * w j : Real) *
        Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))) ^ 2 : Real) : Complex))
      T).re) atTop <=
      Filter.limsup (fun t : Real => (tsum (fun j => ((w j ^ 2 * (m j : Real) : Real) : Complex) *
        Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))).re) atTop) <->
      (forall j, m j <= 1) := by
  let c (j : i) : Complex := (gamma j : Complex) * Complex.I
  let a (j : i) : Complex := ((m j : Real) * w j : Real)
  let b (j : i) : Real := w j ^ 2 * (m j : Real)
  have hc (j : i) : (c j).re = 0 := by simp [c, Complex.mul_re]
  have hInj : Function.Injective c := by
    intro j k h
    have hh := congrArg Complex.im h
    apply hDistinct
    simpa [c, Complex.mul_im] using hh
  have hA (j : i) : norm (a j) = (m j : Real) * w j := by
    unfold a
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
      (hPositive j).le)]
  have hSum : Summable (fun j => norm (a j)) := by simpa only [hA] using hFirst
  have hSquareAmplitude (j : i) : norm (a j) ^ 2 = w j ^ 2 * (m j : Real) ^ 2 := by
    rw [hA, mul_pow, mul_comm]
  let F (T : Real) : Complex := fourierCesaro (fun t =>
    ((norm (tsum (fun j => a j * Complex.exp (c j * (t : Complex)))) ^ 2 : Real) : Complex)) T
  have hMean := fourierCesaro_normSq_tsum_tendsto a c hc hInj hSum
  have hMeanC : Tendsto F atTop (nhds ((tsum (fun j => w j ^ 2 * (m j : Real) ^ 2) : Real) :
      Complex)) := by
    rw [Complex.ofReal_tsum]
    simpa only [F, hSquareAmplitude] using hMean
  have hReal : Tendsto (fun T : Real => (F T).re) atTop
      (nhds (tsum (fun j => w j ^ 2 * (m j : Real) ^ 2))) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hMeanC
  have hPhase (j : i) (t : Real) : c j * (t : Complex) =
      ((gamma j * t : Real) : Complex) * Complex.I := by
    simp only [c, Complex.ofReal_mul]
    ring
  have hUpper := limsup_re_positive_fourierSeries_eq_tsum b gamma
    (fun j => mul_nonneg (sq_nonneg _) (by positivity)) hSecond
  have hUpper' : Filter.limsup (fun t : Real => (tsum (fun j => (b j : Complex) *
      Complex.exp (c j * (t : Complex)))).re) atTop = tsum b := by
    simpa only [hPhase] using hUpper
  change (Filter.limsup (fun T : Real => (F T).re) atTop <=
    Filter.limsup (fun t : Real => (tsum (fun j => (b j : Complex) *
      Complex.exp (c j * (t : Complex)))).re) atTop) <-> _
  rw [hReal.limsup_eq, hUpper']
  exact global_weighted_multiplicity_iff m (fun j => w j ^ 2) (fun j => sq_pos_of_pos (hPositive j))
    hSquare hSecond

/-- Convolve a signal against a complex integrable kernel. -/
def spectralConvolution (k H : Real -> Complex) (t : Real) : Complex :=
  integral volume (fun v => k v * H (t - v))

/-- The Fourier multiplier with angular frequency represented by a purely imaginary number. -/
def angularFourierTransform (k : Real -> Complex) (c : Complex) : Complex :=
  integral volume (fun v : Real => k v * Complex.exp (-c * (v : Complex)))

private theorem norm_exp_of_pure_frequency (c : Complex) (hc : c.re = 0) (t : Real) :
    norm (Complex.exp (c * (t : Complex))) = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, hc]

/-- An integrable convolution kernel acts diagonally on every absolutely
summable series of real-frequency complex exponentials. -/
theorem spectralConvolution_fourierSeries {i : Type*} [Countable i]
    (a c : i -> Complex) (ha : Summable (fun j => norm (a j)))
    (hc : forall j, (c j).re = 0) (k : Real -> Complex) (hk : Integrable k)
    (t : Real) :
    spectralConvolution k (fun u => tsum (fun j => a j * Complex.exp (c j * (u : Complex)))) t =
      tsum (fun j => (a j * angularFourierTransform k (c j)) *
        Complex.exp (c j * (t : Complex))) := by
  let F (j : i) (v : Real) : Complex :=
    k v * (a j * Complex.exp (c j * ((t - v : Real) : Complex)))
  have hNorm (j : i) (v : Real) : norm (F j v) = norm (k v) * norm (a j) := by
    simp only [F, norm_mul, norm_exp_of_pure_frequency (c j) (hc j), mul_one]
  have hInt (j : i) : Integrable (F j) := by
    have hExp : Continuous (fun v : Real => a j * Complex.exp (c j * ((t - v : Real) : Complex))) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id))))
    exact (hk.norm.mul_const _).mono' (hk.aestronglyMeasurable.mul hExp.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun v => (hNorm j v).le))
  have hIntNorm (j : i) : integral volume (fun v => norm (F j v)) =
      integral volume (fun v => norm (k v)) * norm (a j) := by
    simp only [hNorm, integral_mul_const]
  have hS : Summable (fun j => integral volume (fun v => norm (F j v))) := by
    simp only [hIntNorm]
    exact ha.mul_left _
  calc
    _ = integral volume (fun v => tsum (fun j => F j v)) := by
      unfold spectralConvolution
      refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
      unfold F
      dsimp only
      rw [tsum_mul_left]
    _ = tsum (fun j => integral volume (F j)) :=
      (integral_tsum_of_summable_integral_norm hInt hS).symm
    _ = _ := by
      refine tsum_congr ?_
      intro j
      have hF : F j = fun v : Real => (a j * Complex.exp (c j * (t : Complex))) *
          (k v * Complex.exp (-c j * (v : Complex))) := by
        funext v
        simp only [F, Complex.ofReal_sub, mul_sub, Complex.exp_sub, neg_mul,
          Complex.exp_neg, div_eq_mul_inv]
        ac_rfl
      rw [hF, integral_const_mul, angularFourierTransform]
      ac_rfl

/-- Convolution against an integrable kernel preserves a bounded error
that tends to zero along the positive real axis. -/
theorem tendsto_spectralConvolution_of_tendsto_zero {k R : Real -> Complex}
    (hk : Integrable k) (hR : Measurable R) {C : Real} (hC : forall u, norm (R u) <= C)
    (hLim : Tendsto R atTop (nhds 0)) :
    Tendsto (spectralConvolution k R) atTop (nhds 0) := by
  let F (t v : Real) : Complex := k v * R (t - v)
  have hF (t : Real) : AEStronglyMeasurable (F t) volume :=
    hk.aestronglyMeasurable.mul (hR.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hDom (t v : Real) : norm (F t v) <= norm (k v) * C := by
    change norm (k v * R (t - v)) <= norm (k v) * C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hEach (v : Real) : Tendsto (fun t => F t v) atTop (nhds 0) := by
    have ht : Tendsto (fun t : Real => t - v) atTop atTop :=
      tendsto_atTop.2 (fun L => (eventually_ge_atTop (L + v)).mono (fun _ h => le_sub_iff_add_le.mpr h))
    have hK : Tendsto (fun _ : Real => k v) atTop (nhds (k v)) := tendsto_const_nhds
    have h := hK.mul (hLim.comp ht)
    simpa only [F, Function.comp_def, mul_zero] using h
  have h := tendsto_integral_filter_of_dominated_convergence
    (F := F) (f := fun _ => 0) (fun v => norm (k v) * C)
    (Filter.Eventually.of_forall hF)
    (Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (hDom t)))
    (hk.norm.mul_const C) (Filter.Eventually.of_forall hEach)
  change Tendsto (fun t : Real => integral volume (F t)) atTop (nhds 0)
  simpa only [integral_zero] using h

/-- With one spectral index for each occurrence of a zero, the global
inequality is equivalent to each ordinate occurring only once. -/
theorem fourierOccurrenceMultiplicityCriterion {i : Type*} [Countable i]
    (w gamma : i -> Real) (hW : forall j, 0 < w j)
    (hSum : Summable w) (hSquare : Summable (fun j => w j ^ 2)) :
    (Filter.limsup (fun T : Real => (fourierCesaro (fun t =>
      ((norm (tsum (fun j => (w j : Complex) *
        Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))) ^ 2 : Real) : Complex)) T).re)
        atTop <=
      Filter.limsup (fun t : Real => (tsum (fun j => ((w j ^ 2 : Real) : Complex) *
        Complex.exp ((gamma j : Complex) * Complex.I * (t : Complex)))).re) atTop) <->
      Function.Injective gamma := by
  let c (j : i) : Complex := (gamma j : Complex) * Complex.I
  let a (j : i) : Complex := (w j : Complex)
  let e (p : Prod i i) : Real := if gamma p.1 = gamma p.2 then w p.1 * w p.2 else 0
  let d (p : Prod i i) : Real := if p.1 = p.2 then w p.1 ^ 2 else 0
  let A (p : Prod i i) : Complex := a p.1 * (starRingEnd Complex) (a p.2)
  let D (p : Prod i i) : Complex := c p.1 - c p.2
  have hc (j : i) : (c j).re = 0 := by simp [c, Complex.mul_re]
  have hD (p : Prod i i) : (D p).re = 0 := by simp only [D, Complex.sub_re, hc, sub_self]
  have ha (j : i) : norm (a j) = w j := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hW j)]
  have hSumA : Summable (fun j => norm (a j)) := by simpa only [ha] using hSum
  have hConjA : Summable (fun j => norm ((starRingEnd Complex) (a j))) := by
    simpa only [Complex.norm_conj] using hSumA
  have hSumPair : Summable (fun p : Prod i i => norm (A p)) :=
    Summable.mul_norm (f := a) (g := fun j => (starRingEnd Complex) (a j)) hSumA hConjA
  have hDZero (p : Prod i i) : D p = 0 <-> gamma p.1 = gamma p.2 := by
    change c p.1 - c p.2 = 0 <-> gamma p.1 = gamma p.2
    rw [sub_eq_zero]
    constructor
    case mp =>
      intro hh
      simpa [c, Complex.mul_im] using congrArg Complex.im hh
    case mpr =>
      intro hh
      unfold c
      rw [hh]
  have hCoeff : (fun p : Prod i i => if D p = 0 then A p else 0) =
      fun p : Prod i i => (e p : Complex) := by
    funext p
    by_cases he : gamma p.1 = gamma p.2
    case pos => simp [e, A, a, he, (hDZero p).mpr he]
    case neg =>
      have hz : Not (D p = 0) := fun h => he ((hDZero p).mp h)
      simp [e, he, hz]
  let E (T : Real) : Complex := fourierCesaro (fun t =>
    ((norm (tsum (fun j => a j * Complex.exp (c j * (t : Complex)))) ^ 2 : Real) : Complex)) T
  have hInput : (fun t : Real =>
      ((norm (tsum (fun j => a j * Complex.exp (c j * (t : Complex)))) ^ 2 : Real) : Complex)) =
      fun t : Real => tsum (fun p : Prod i i => A p * Complex.exp (D p * (t : Complex))) :=
    funext (fourier_normSq_tsum_eq_pair a c hc hSumA)
  have hMean := fourierCesaro_tsum_tendsto A D hD hSumPair
  have hELim : Tendsto E atTop (nhds ((tsum e : Real) : Complex)) := by
    rw [Complex.ofReal_tsum]
    simpa only [E, <- hInput, hCoeff] using hMean
  have hEReal : Tendsto (fun T : Real => (E T).re) atTop (nhds (tsum e)) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hELim
  have hPhase (j : i) (t : Real) : c j * (t : Complex) =
      ((gamma j * t : Real) : Complex) * Complex.I := by
    simp only [c, Complex.ofReal_mul]
    ring
  have hUpper := limsup_re_positive_fourierSeries_eq_tsum (fun j => w j ^ 2) gamma
    (fun j => sq_nonneg (w j)) hSquare
  have hUpper' : Filter.limsup (fun t : Real => (tsum (fun j => ((w j ^ 2 : Real) : Complex) *
      Complex.exp (c j * (t : Complex)))).re) atTop = tsum (fun j => w j ^ 2) := by
    simpa only [hPhase] using hUpper
  have hProd : Summable (fun p : Prod i i => w p.1 * w p.2) :=
    hSum.mul_of_nonneg hSum (fun j => (hW j).le) (fun j => (hW j).le)
  have hEP (p : Prod i i) : 0 <= e p /\ e p <= w p.1 * w p.2 := by
    by_cases he : gamma p.1 = gamma p.2 <;> simp [e, he, mul_nonneg (hW p.1).le (hW p.2).le]
  have hDE (p : Prod i i) : 0 <= d p /\ d p <= e p := by
    by_cases hh : p.1 = p.2
    case pos => simp [d, e, hh, pow_two, mul_self_nonneg]
    case neg => simpa only [d, if_neg hh, le_refl, true_and] using (hEP p).1
  have hSumE : Summable e := Summable.of_nonneg_of_le (fun p => (hEP p).1) (fun p => (hEP p).2) hProd
  have hSumD : Summable d := Summable.of_nonneg_of_le (fun p => (hDE p).1) (fun p => (hDE p).2) hSumE
  have hDiag : tsum d = tsum (fun j => w j ^ 2) := by
    let diag : Set (Prod i i) := {p | p.1 = p.2}
    have hIndicator : d = Set.indicator diag (fun p : Prod i i => w p.1 ^ 2) := by
      funext p
      by_cases hh : p.1 = p.2 <;> simp [d, diag, hh]
    rw [hIndicator, <- tsum_subtype]
    let q : Equiv i diag :=
      { toFun := fun j => Subtype.mk (Prod.mk j j) rfl
        invFun := fun p => p.val.1
        left_inv := fun _ => rfl
        right_inv := fun p => Subtype.ext (Prod.ext rfl p.property) }
    exact (q.tsum_eq (fun p : diag => w p.val.1 ^ 2)).symm
  change (Filter.limsup (fun T : Real => (E T).re) atTop <=
    Filter.limsup (fun t : Real => (tsum (fun j => ((w j ^ 2 : Real) : Complex) *
      Complex.exp (c j * (t : Complex)))).re) atTop) <-> _
  rw [hEReal.limsup_eq, hUpper', <- hDiag]
  constructor
  case mp =>
    intro h j k hjk
    by_contra hne
    let q : Prod i i := Prod.mk j k
    have hDiff : Summable (fun p : Prod i i => e p - d p) := hSumE.sub hSumD
    have hNonneg (p : Prod i i) : 0 <= e p - d p := sub_nonneg.mpr (hDE p).2
    have hZero : tsum (fun p : Prod i i => e p - d p) <= 0 := by
      rw [hSumE.tsum_sub hSumD]
      exact sub_nonpos.mpr h
    have hOne := (hDiff.le_tsum q (fun p _ => hNonneg p)).trans hZero
    have hq : 0 < e q - d q := by
      simpa [e, d, q, hjk, hne] using mul_pos (hW j) (hW k)
    exact (not_lt_of_ge hOne) hq
  case mpr =>
    intro h
    have he : e = d := by
      funext p
      by_cases hp : gamma p.1 = gamma p.2
      case pos => simp [e, d, h hp, pow_two]
      case neg =>
        have hne : Not (p.1 = p.2) := fun hi => hp (congrArg gamma hi)
        simp [e, d, hp, hne]
    rw [he]

/-- The time average of a locally integrable error tending to zero also
tends to zero. -/
theorem fourierCesaro_tendsto_zero_of_tendsto_zero {f : Real -> Complex}
    (hInt : forall a b : Real, IntervalIntegrable f volume a b)
    (hLim : Tendsto f atTop (nhds 0)) :
    Tendsto (fourierCesaro f) atTop (nhds 0) := by
  apply Metric.tendsto_nhds.2
  intro eps hEps
  have hHalf : 0 < eps / 2 := half_pos hEps
  have hTail := (Metric.tendsto_nhds.1 hLim) (eps / 2) hHalf
  choose A hA using eventually_atTop.1 hTail
  let B := max A 0
  let C := norm (intervalIntegral f 0 B volume)
  have hB : 0 <= B := le_max_right A 0
  have hNear (t : Real) (ht : B <= t) : norm (f t) < eps / 2 := by
    simpa only [dist_zero_right] using hA t ((le_max_left A 0).trans ht)
  have hHeadLimit : Tendsto (fun t : Real => Inv.inv t * C) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_inv_atTop_zero : Tendsto (fun t : Real => Inv.inv t) atTop (nhds 0)).mul
        (tendsto_const_nhds : Tendsto (fun _ : Real => C) atTop (nhds C))
  have hHead := hHeadLimit.eventually (gt_mem_nhds hHalf)
  filter_upwards [hHead, eventually_ge_atTop (max B 1)] with T hTsmall hT
  have hBT : B <= T := (le_max_left B 1).trans hT
  have hTP : 0 < T := zero_lt_one.trans_le ((le_max_right B 1).trans hT)
  have hTb : norm (intervalIntegral f B T volume) <= (eps / 2) * (T - B) := by
    rw [<- abs_of_nonneg (sub_nonneg.mpr hBT)]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le hBT] at ht
    exact (hNear t ht.1.le).le
  have hTailBound : Inv.inv T * ((eps / 2) * (T - B)) <= eps / 2 := by
    calc
      _ <= Inv.inv T * ((eps / 2) * T) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (sub_le_self _ hB) hHalf.le) (inv_nonneg.mpr hTP.le)
      _ = eps / 2 := by
        rw [mul_left_comm, mul_comm (Inv.inv T) T, <- div_eq_mul_inv, div_self hTP.ne', mul_one]
  rw [dist_zero_right, fourierCesaro, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hTP.le, <- intervalIntegral.integral_add_adjacent_intervals (hInt 0 B) (hInt B T)]
  calc
    _ <= Inv.inv T * (C + norm (intervalIntegral f B T volume)) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.mpr hTP.le)
    _ <= Inv.inv T * (C + (eps / 2) * (T - B)) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl C) hTb) (inv_nonneg.mpr hTP.le)
    _ < eps := by rw [mul_add]; linarith only [hTsmall, hTailBound]

private theorem eventual_abs_le_one_of_tendsto_zero {f : Real -> Real}
    (h : Tendsto f atTop (nhds 0)) :
    Filter.Eventually (fun t => abs (f t) <= 1) atTop :=
  ((Metric.tendsto_nhds.1 h) 1 zero_lt_one).mono (fun t ht => by
    simpa only [dist_zero_right, Real.norm_eq_abs] using ht.le)

/-- An error tending to zero preserves the upper limit of a bounded real
signal. -/
theorem limsup_add_tendsto_zero {S E : Real -> Real} {M : Real}
    (hS : forall t, abs (S t) <= M) (hE : Tendsto E atTop (nhds 0)) :
    Filter.limsup (S + E) atTop = Filter.limsup S atTop := by
  have hLower : IsBoundedUnder (fun a b : Real => b <= a) atTop S :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall (fun t => (abs_le.mp (hS t)).1))
  have hUpper : IsBoundedUnder (fun a b : Real => a <= b) atTop S :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall (fun t => (abs_le.mp (hS t)).2))
  have hSmall := eventual_abs_le_one_of_tendsto_zero hE
  have hL : IsCoboundedUnder (fun a b : Real => a <= b) atTop E :=
    IsCoboundedUnder.of_frequently_ge (hSmall.mono (fun t ht => (abs_le.mp ht).1)).frequently
  have hU : IsBoundedUnder (fun a b : Real => a <= b) atTop E :=
    isBoundedUnder_of_eventually_le (hSmall.mono (fun t ht => (abs_le.mp ht).2))
  have hSE := limsup_add_le hLower hUpper hL hU
  rw [hE.limsup_eq, add_zero] at hSE
  refine le_antisymm hSE ?_
  have hNeg : Tendsto (-E) atTop (nhds 0) := by
    change Tendsto (fun t : Real => -E t) atTop (nhds 0)
    simpa only [neg_zero] using hE.neg
  have hN := eventual_abs_le_one_of_tendsto_zero hNeg
  have hNLower : IsCoboundedUnder (fun a b : Real => a <= b) atTop (-E) :=
    IsCoboundedUnder.of_frequently_ge (hN.mono (fun t ht => (abs_le.mp ht).1)).frequently
  have hNUpper : IsBoundedUnder (fun a b : Real => a <= b) atTop (-E) :=
    isBoundedUnder_of_eventually_le (hN.mono (fun t ht => (abs_le.mp ht).2))
  have hB : Filter.Eventually (fun t : Real => abs ((S + E) t) <= M + 1) atTop :=
    hSmall.mono (fun t ht => (abs_add_le (S t) (E t)).trans (add_le_add (hS t) ht))
  have hBL := isBoundedUnder_of_eventually_ge (hB.mono (fun t ht => (abs_le.mp ht).1))
  have hBU := isBoundedUnder_of_eventually_le (hB.mono (fun t ht => (abs_le.mp ht).2))
  have hAdd := limsup_add_le hBL hBU hNLower hNUpper
  have hEq : (S + E) + -E = S := by rw [add_assoc, add_neg_cancel, add_zero]
  rwa [hEq, hNeg.limsup_eq, add_zero] at hAdd

/-- The upper Cesaro mean of squared absolute value. -/
def spectralSquareEnergy (H : Real -> Complex) : Real :=
  Filter.limsup (fun T : Real => (fourierCesaro
    (fun t => ((norm (H t) ^ 2 : Real) : Complex)) T).re) atTop

private theorem intervalIntegrable_of_measurable_bounded
    {f : Real -> Complex} (hf : Measurable f) {B : Real} (hB : forall t, norm (f t) <= B)
    (a b : Real) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  exact IntegrableOn.of_bound (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top)
    hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)

private theorem norm_fourierCesaro_le_of_bounded {f : Real -> Complex} {B : Real}
    (hB : forall t, norm (f t) <= B) (T : Real) : norm (fourierCesaro f T) <= B := by
  by_cases hT : T = 0
  case pos =>
    simpa only [fourierCesaro, hT, Complex.ofReal_zero, inv_zero, zero_mul, norm_zero]
      using (norm_nonneg (f 0)).trans (hB 0)
  case neg =>
    have hT' : Not (abs T = 0) := fun h => hT (abs_eq_zero.mp h)
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := f) (a := 0) (b := T) (fun t _ => hB t)
    rw [sub_zero] at hI
    unfold fourierCesaro
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ <= Inv.inv (abs T) * (B * abs T) :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr (abs_nonneg _))
      _ = B := by
        rw [mul_left_comm, mul_comm (Inv.inv (abs T)) (abs T), <- div_eq_mul_inv, div_self hT', mul_one]

/-- An additive error tending to zero leaves the global squared time
average unchanged for bounded measurable signals. -/
theorem spectralSquareEnergy_eq_of_tendsto_sub_zero {H S : Real -> Complex}
    (hH : Measurable H) (hS : Measurable S) {M N : Real}
    (hMBound : forall t, norm (H t) <= M) (hNBound : forall t, norm (S t) <= N)
    (hDiff : Tendsto (fun t => H t - S t) atTop (nhds 0)) :
    spectralSquareEnergy H = spectralSquareEnergy S := by
  let HH (t : Real) : Complex := ((norm (H t) ^ 2 : Real) : Complex)
  let SS (t : Real) : Complex := ((norm (S t) ^ 2 : Real) : Complex)
  let E (t : Real) : Complex := HH t - SS t
  have hHH : Measurable HH := Complex.continuous_ofReal.measurable.comp (hH.norm.pow_const 2)
  have hSS : Measurable SS := Complex.continuous_ofReal.measurable.comp (hS.norm.pow_const 2)
  have hNormSq {z : Complex} {C : Real} (hC : norm z <= C) :
      norm ((norm z ^ 2 : Real) : Complex) <= C ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two, pow_two]
    exact mul_le_mul hC hC (norm_nonneg _) ((norm_nonneg _).trans hC)
  have hHBound (t : Real) : norm (HH t) <= M ^ 2 := hNormSq (hMBound t)
  have hSBound (t : Real) : norm (SS t) <= N ^ 2 := hNormSq (hNBound t)
  have hPointwise (t : Real) : norm (E t) <= (M + N) * norm (H t - S t) := by
    have hDiffNorm : abs (norm (H t) - norm (S t)) <= norm (H t - S t) := by
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le (H t) (S t)
    have hp : norm (H t) ^ 2 - norm (S t) ^ 2 =
        (norm (H t) + norm (S t)) * (norm (H t) - norm (S t)) := by ring
    rw [show E t = (((norm (H t) ^ 2 - norm (S t) ^ 2 : Real) : Complex)) by
      simp only [E, HH, SS, Complex.ofReal_sub], Complex.norm_real, Real.norm_eq_abs,
      hp, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul (add_le_add (hMBound t) (hNBound t)) hDiffNorm
      (abs_nonneg _) (add_nonneg ((norm_nonneg _).trans (hMBound t)) ((norm_nonneg _).trans (hNBound t)))
  have hE0 : Tendsto E atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have h := (tendsto_zero_iff_norm_tendsto_zero.mp hDiff).const_mul (M + N)
    exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (Filter.Eventually.of_forall hPointwise) (by simpa only [mul_zero] using h)
  have hIntH := intervalIntegrable_of_measurable_bounded hHH hHBound
  have hIntS := intervalIntegrable_of_measurable_bounded hSS hSBound
  have hEAvg := fourierCesaro_tendsto_zero_of_tendsto_zero
    (fun a b => (hIntH a b).sub (hIntS a b)) hE0
  have hER : Tendsto (fun T : Real => (fourierCesaro E T).re) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hEAvg
  have hDecomp : (fun T : Real => (fourierCesaro HH T).re) =
      (fun T : Real => (fourierCesaro SS T).re) + (fun T : Real => (fourierCesaro E T).re) := by
    funext T
    have hPair : fourierCesaro E T = fourierCesaro HH T - fourierCesaro SS T := by
      unfold fourierCesaro E
      rw [intervalIntegral.integral_sub (hIntH 0 T) (hIntS 0 T), mul_sub]
    rw [Pi.add_apply, hPair, Complex.sub_re]
    ring
  unfold spectralSquareEnergy
  change Filter.limsup (fun T : Real => (fourierCesaro HH T).re) atTop =
    Filter.limsup (fun T : Real => (fourierCesaro SS T).re) atTop
  rw [hDecomp]
  exact limsup_add_tendsto_zero
    (fun T => (Complex.abs_re_le_norm _).trans (norm_fourierCesaro_le_of_bounded hSBound T)) hER

/-- An error tending to zero leaves the upper limit of the real part
unchanged when the comparison signal is bounded. -/
theorem limsup_re_eq_of_tendsto_sub_zero {H S : Real -> Complex} {N : Real}
    (hBound : forall t, norm (S t) <= N) (hDiff : Tendsto (fun t => H t - S t) atTop (nhds 0)) :
    Filter.limsup (fun t : Real => (H t).re) atTop =
      Filter.limsup (fun t : Real => (S t).re) atTop := by
  let E (t : Real) : Real := (H t - S t).re
  have hE : Tendsto E atTop (nhds 0) := by
    simpa only [E, Function.comp_def, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hDiff
  have hEq : (fun t : Real => (H t).re) = (fun t : Real => (S t).re) + E := by
    funext t
    simp only [E, Pi.add_apply, Complex.sub_re]
    ring
  rw [hEq]
  exact limsup_add_tendsto_zero (fun t => (Complex.abs_re_le_norm _).trans (hBound t)) hE

/-- A convolution of measurable functions has a measurable parameter integral. -/
theorem measurable_spectralConvolution {k H : Real -> Complex}
    (hk : Measurable k) (hH : Measurable H) : Measurable (spectralConvolution k H) := by
  have h : Measurable (fun p : Prod Real Real => k p.2 * H (p.1 - p.2)) :=
    (hk.comp measurable_snd).mul (hH.comp (measurable_fst.sub measurable_snd))
  exact (h.stronglyMeasurable.integral_prod_right').measurable

/-- A bounded signal convolved with an integrable kernel remains bounded. -/
theorem norm_spectralConvolution_le {k H : Real -> Complex}
    {M : Real} (hk : Integrable k) (hB : forall t, norm (H t) <= M)
    (t : Real) : norm (spectralConvolution k H t) <= (integral volume (fun v => norm (k v))) * M := by
  unfold spectralConvolution
  calc
    _ <= integral volume (fun v => norm (k v * H (t - v))) := norm_integral_le_integral_norm _
    _ <= integral volume (fun v => norm (k v) * M) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (hk.norm.mul_const _)
      exact Filter.Eventually.of_forall (fun v => by
        change norm (k v * H (t - v)) <= norm (k v) * M
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _))
    _ = _ := integral_mul_const _ _

end Robin1984.GRH
