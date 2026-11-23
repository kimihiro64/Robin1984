import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Robin1984.GRH.DedekindPrimitiveExpansion
import Robin1984.GRH.DedekindRobinForward
import Robin1984.GRH.DedekindSpectralMellin

/-!
# The Dedekind forward Robin implication

The divided difference of the regularized logarithmic derivative is the
Mellin transform of the spectral model. Mellin uniqueness identifies it
with the actual Chebyshev primitive tail. The completed zeros determine
the square-root coefficient, and the origin and Gamma terms are smaller.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The integrated explicit formula for the primitive Chebyshev error and the corrected number-field Robin bound.
- Formalization note: Identify the actual tail with its spectral model by Mellin uniqueness and apply the exact ideal supporting line.
- Content basis: Completed zero mass, gamma lattices, the field's primitive limit, and the forward Mertens estimate.
- Dependency status: Dirichlet GRH and Dedekind ERH proof with the pinned analytic dependencies.
-/

open DedekindZeta Filter MeasureTheory NumberField NumberField.InfinitePlace Set

namespace Robin1984.GRH

private noncomputable def spectralResidues {I : Type*} (rho : I -> Complex) (s : Complex) : Complex :=
  tsum (fun i => primitiveZeroWeight (rho i) / (s - rho i))

private theorem spectralResidues_dividedDifference {I : Type*} (rho : I -> Complex)
    {s : Complex} (hs : 1 < s.re) (hRho : forall i, (rho i).re < 1)
    (h0 : forall i, Not (rho i = 0))
    (hAtS : Summable (fun i => 1 / (rho i * (s - rho i))))
    (hAtOne : Summable (fun i => 1 / (rho i * (1 - rho i)))) :
    ((tsum (fun i => 1 / (rho i * (s - rho i)))) -
      (tsum (fun i => 1 / (rho i * (1 - rho i))))) / (1 - s) = spectralResidues rho s := by
  have hs0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs1 : Not (s = 1) := by
    intro h
    rw [h, Complex.one_re] at hs
    exact (lt_irrefl _) hs
  have h1 (i : I) : Not (rho i = 1) := by
    intro h
    have hi := hRho i
    rw [h, Complex.one_re] at hi
    exact (lt_irrefl _) hi
  have hS (i : I) : Not (s = rho i) := by
    intro h
    rw [h] at hs
    exact (not_lt_of_ge (hRho i).le) hs
  have h := primitiveTailKernel_eq_hadamardZeroSeries rho 0 0 s hs0 hs1 h0 h1 hS hAtS hAtOne
  simp only [zero_div, zero_add] at h
  refine h.trans (tsum_congr (fun i => ?_))
  rw [primitiveZeroWeight, div_div]

private theorem gammaZero_re_of_one_le {q : Real} (hq : 1 <= q) (n : Nat) :
    (gammaZero q n).re < 0 := by
  have hqp := zero_lt_one.trans_le hq
  rw [gammaZero, Complex.neg_re, Complex.ofReal_re, neg_lt_zero]
  positivity

private theorem gammaZero_ne_zero_of_one_le {q : Real} (hq : 1 <= q) (n : Nat) :
    Not (gammaZero q n = 0) := by
  intro h
  have hr := gammaZero_re_of_one_le hq n
  rw [h, Complex.zero_re] at hr
  exact (lt_irrefl _) hr

variable (K : Type*) [Field K] [NumberField K]

private theorem summable_completedZeroKernel {s : Complex} (hs : 0 < s.re)
    (hn : Not (completedDedekindPoleCleared K s = 0)) :
    Summable (fun i : DedekindCompletedZeroIndex K =>
      1 / (completedDedekindZero K i * (s - completedDedekindZero K i))) := by
  let z := completedDedekindZero K
  have hs0 := Complex.ne_zero_of_re_pos hs
  refine ((summable_completedDedekindZero_logDerivTerm K hn).div_const s).congr ?_
  intro i
  change (1 / (s - z i) + 1 / z i) / s = 1 / (z i * (s - z i))
  have hzi : Not (z i = 0) := i.property
  have hN : Not (s - z i = 0) := sub_ne_zero.mpr (fun e => by
    apply hn
    rw [e]
    exact completedDedekindZero_is_zero K i)
  field_simp [hs0, hzi, hN]
  ring

private noncomputable def dedekindOriginMultiplicity : Complex :=
  (nrRealPlaces K : Complex) + (nrComplexPlaces K : Complex) - 1

/-- The primitive-tail divided difference is the sum of its origin and spectral terms. -/
private theorem exists_dedekind_primitiveLogDeriv_dividedDifference :
    exists a : Complex, forall s : Complex, 1 < s.re ->
      let F := entirePoleFreeDedekindZeta K
      let m := dedekindOriginMultiplicity K
      ((logDeriv F s + 1) / s - (logDeriv F 1 + 1)) / (1 - s) =
        (a + m) / s + m / s ^ (2 : Nat) +
          spectralResidues (completedDedekindZero K) s +
          (nrRealPlaces K : Complex) * spectralResidues (gammaZero 2) s +
          (nrComplexPlaces K : Complex) * spectralResidues (gammaZero 1) s := by
  choose a hA using exists_dedekind_primitiveLogDeriv_expansion K
  refine Exists.intro a ?_
  intro s hs
  let F := entirePoleFreeDedekindZeta K
  let m := dedekindOriginMultiplicity K
  let r := (nrRealPlaces K : Complex)
  let c := (nrComplexPlaces K : Complex)
  let z := completedDedekindZero K
  let A {I : Type} (rho : I -> Complex) (w : Complex) := tsum (fun i => 1 / (rho i * (w - rho i)))
  have hs0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs1 : Not (1 - s = 0) := by
    intro h
    have he := congrArg Complex.re (sub_eq_zero.mp h)
    rw [Complex.one_re] at he
    exact (ne_of_lt hs) he
  have hns := completedDedekindPoleCleared_ne_zero_of_one_le_re K hs.le
  have hn1 := completedDedekindPoleCleared_ne_zero_of_one_le_re K (s := 1) (by norm_num)
  have hst := hA s (zero_lt_one.trans hs) hns
  have h1 := hA 1 (by norm_num) hn1
  simp only [one_pow, div_one] at h1
  have hAll (i : DedekindCompletedZeroIndex K) : (z i).re < 1 :=
    (completedDedekindPoleCleared_zero_in_strip K (completedDedekindZero_is_zero K i)).2
  have hZ := spectralResidues_dividedDifference z hs hAll (fun i => i.property)
    (summable_completedZeroKernel K (zero_lt_one.trans hs) hns)
    (summable_completedZeroKernel K (s := 1) (by norm_num) hn1)
  have hGamma (q : Real) (hq : 1 <= q) :
      ((A (gammaZero q) s) - A (gammaZero q) 1) / (1 - s) =
        spectralResidues (gammaZero q) s := by
    refine spectralResidues_dividedDifference (gammaZero q) hs
      (fun n => (gammaZero_re_of_one_le hq n).trans zero_lt_one)
      (gammaZero_ne_zero_of_one_le hq) ?_ ?_
    case refine_1 =>
      exact (hasSum_gammaZeroLogDeriv_div (zero_lt_one.trans_le hq) (zero_lt_one.trans hs)).summable
    case refine_2 =>
      exact (hasSum_gammaZeroLogDeriv_div (zero_lt_one.trans_le hq) (s := 1) (by norm_num)).summable
  change ((logDeriv F s + 1) / s - (logDeriv F 1 + 1)) / (1 - s) = _
  rw [hst, h1, <- hZ, <- hGamma 2 (by norm_num), <- hGamma 1 (by norm_num)]
  dsimp only [m, r, c, dedekindOriginMultiplicity, A, z]
  field_simp [hs0, hs1]
  ring

private noncomputable def spectralTailSeries {I : Type*} (rho : I -> Complex) (x : Real) : Complex :=
  tsum (fun i => primitiveZeroWeight (rho i) * (x : Complex) ^ (rho i - 1))

private noncomputable def dedekindSpectralTail (a : Complex) (x : Real) : Complex :=
  -((a + dedekindOriginMultiplicity K) * (x : Complex) ^ (-(1 : Complex)) +
    dedekindOriginMultiplicity K * ((x : Complex) ^ (-(1 : Complex)) * (Real.log x : Complex)) +
    spectralTailSeries (completedDedekindZero K) x +
    (nrRealPlaces K : Complex) * spectralTailSeries (gammaZero 2) x +
    (nrComplexPlaces K : Complex) * spectralTailSeries (gammaZero 1) x)

private theorem integral_dedekindSpectralTail_cpow (hRH : DedekindRH K) (a : Complex)
    {s : Complex} (hs : 1 < s.re) :
    let mu := volume.restrict (Ioi (1 : Real))
    let m := dedekindOriginMultiplicity K
    let G := fun x : Real => (x : Complex) ^ (-s) * dedekindSpectralTail K a x
    And (Integrable G mu)
      (integral mu G =
        -((a + m) / s + m / s ^ (2 : Nat) +
          spectralResidues (completedDedekindZero K) s +
          (nrRealPlaces K : Complex) * spectralResidues (gammaZero 2) s +
          (nrComplexPlaces K : Complex) * spectralResidues (gammaZero 1) s)) := by
  let mu := volume.restrict (Ioi (1 : Real))
  let m := dedekindOriginMultiplicity K
  let A := a + m
  let r := (nrRealPlaces K : Complex)
  let c := (nrComplexPlaces K : Complex)
  let P (x : Real) := (x : Complex) ^ (-s)
  let Q (x : Real) := (x : Complex) ^ (-(1 : Complex))
  let W (x : Real) := (x : Complex) ^ (-s - 1)
  let L (x : Real) := (Real.log x : Complex)
  let Z := spectralTailSeries (completedDedekindZero K)
  let R := spectralTailSeries (gammaZero 2)
  let C := spectralTailSeries (gammaZero 1)
  let _ : Countable (DedekindCompletedZeroIndex K) := countable_dedekindCompletedZeroIndex K
  have hZ := integrable_integral_tsum_spectralMellin (completedDedekindZero K)
    (fun i => primitiveZeroWeight (completedDedekindZero K i)) hs
    (fun i => (completedDedekindPoleCleared_zero_re_of_dedekindRH K hRH
      (completedDedekindZero_is_zero K i)).le) (summable_norm_primitiveZeroWeight K hRH)
  have hR := integrable_integral_tsum_spectralMellin (gammaZero 2)
    (fun i => primitiveZeroWeight (gammaZero 2 i)) hs
    (fun i => (gammaZero_re_of_one_le (q := 2) (by norm_num) i).le.trans (by norm_num))
    (summable_norm_gammaZeroWeight (q := 2) (by norm_num))
  have hC := integrable_integral_tsum_spectralMellin (gammaZero 1)
    (fun i => primitiveZeroWeight (gammaZero 1 i)) hs
    (fun i => (gammaZero_re_of_one_le (q := 1) (by norm_num) i).le.trans (by norm_num))
    (summable_norm_gammaZeroWeight (q := 1) (by norm_num))
  have hE : (-s - 1).re < -1 := by
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hW : Integrable W mu := integrableOn_Ioi_cpow_of_lt hE zero_lt_one
  have hWInt : integral mu W = 1 / s := by
    change integral mu (fun x : Real => (x : Complex) ^ (-s - 1)) = _
    rw [integral_Ioi_cpow_of_lt hE zero_lt_one, Complex.ofReal_one, Complex.one_cpow,
      show -s - 1 + 1 = -s by ring, neg_div_neg_eq]
  have hL := integral_cpow_log_from_one hs
  have hP : Filter.EventuallyEq (ae mu)
      (fun x : Real => P x * dedekindSpectralTail K a x)
      (fun x : Real => -(A * W x + m * (W x * L x) + P x * Z x +
        r * (P x * R x) + c * (P x * C x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
    have h : P x * Q x = W x := by
      dsimp [P, Q, W]
      rw [<- Complex.cpow_add _ _ hx0]
      congr 1
    change P x * -(A * Q x + m * (Q x * L x) + Z x + r * R x + c * C x) = _
    rw [<- h]
    ring
  have hA : Integrable (fun x => A * W x) mu := hW.const_mul A
  have hLm : Integrable (fun x => m * (W x * L x)) mu := hL.1.const_mul m
  have hZp : Integrable (fun x => P x * Z x) mu := hZ.1
  have hRr : Integrable (fun x => r * (P x * R x)) mu := hR.1.const_mul r
  have hCc : Integrable (fun x => c * (P x * C x)) mu := hC.1.const_mul c
  have hTotal := ((((hA.add hLm).add hZp).add hRr).add hCc).neg
  refine And.intro (hTotal.congr hP.symm) ?_
  change integral mu (fun x => P x * dedekindSpectralTail K a x) = _
  have e4 := integral_add (((hA.add hLm).add hZp).add hRr) hCc
  have e3 := integral_add ((hA.add hLm).add hZp) hRr
  have e2 := integral_add (hA.add hLm) hZp
  have e1 := integral_add hA hLm
  simp only [Pi.add_apply] at e4 e3 e2 e1
  have eZ : integral mu (fun x => P x * Z x) = spectralResidues (completedDedekindZero K) s :=
    hZ.2
  have eR : integral mu (fun x => P x * R x) = spectralResidues (gammaZero 2) s := hR.2
  have eC : integral mu (fun x => P x * C x) = spectralResidues (gammaZero 1) s := hC.2
  have eL : integral mu (fun x => W x * L x) = 1 / s ^ (2 : Nat) := hL.2
  rw [integral_congr_ae hP, integral_neg, e4, e3, e2, e1]
  simp only [integral_const_mul, hWInt, eL, eZ, eR, eC, mul_one_div, A, m, r, c]


private theorem ae_dedekindPrimitiveTail_eq_re_spectralTail (hRH : DedekindRH K)
    {a0 : Real} (ha0 : (a0 : Complex) = -(logDeriv (entirePoleFreeDedekindZeta K) 1 + 1)) :
    exists a : Complex, Filter.EventuallyEq (ae (volume.restrict (Ioi (1 : Real))))
      (primitiveTail (dedekindChebyshevErrorRatio K) a0) (fun x => (dedekindSpectralTail K a x).re) := by
  choose a ha using exists_dedekind_primitiveLogDeriv_dividedDifference K
  refine Exists.intro a ?_
  let mu := volume.restrict (Ioi (1 : Real))
  let T := primitiveTail (dedekindChebyshevErrorRatio K) a0
  let S := dedekindSpectralTail K a
  let d := fun x : Real => (T x : Complex) - S x
  let W (t x : Real) := (x : Complex) ^ (-(2 : Complex) + (t : Complex) * Complex.I)
  have h (t : Real) : And (Integrable (fun x => W t x * d x) mu)
      (integral mu (fun x => W t x * d x) = 0) := by
    let s : Complex := 2 - (t : Complex) * Complex.I
    have hs : 1 < s.re := by
      simp [s, Complex.sub_re, Complex.mul_re]
    have hA := integral_dedekindPrimitiveTail_cpow K ha0 hs
    have hS := integral_dedekindSpectralTail_cpow K hRH a hs
    have he : (fun x => W t x * d x) =
        fun x : Real => (x : Complex) ^ (-s) * (T x : Complex) - (x : Complex) ^ (-s) * S x := by
      funext x
      have hn : -(2 : Complex) + (t : Complex) * Complex.I = -s := by dsimp [s]; ring
      simp only [W, hn, d, mul_sub]
    rw [he]
    refine And.intro (hA.1.sub hS.1) ?_
    rw [integral_sub hA.1 hS.1, hA.2, hS.2, neg_div, ha s hs, sub_self]
  have hd : AEMeasurable d mu := by
    let G := fun x : Real => (x : Complex) ^ (2 : Nat) * (W 0 x * d x)
    have hm : AEMeasurable G mu :=
      ((Complex.continuous_ofReal.pow (2 : Nat)).measurable.aemeasurable).mul (h 0).1.aemeasurable
    refine hm.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hne := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
    have hh : W 0 x = Inv.inv ((x : Complex) ^ (2 : Nat)) := by
      simp only [W, Complex.ofReal_zero, zero_mul, add_zero, Complex.cpow_neg,
        show (2 : Complex) = ((2 : Nat) : Complex) by norm_num, Complex.cpow_natCast]
    change (x : Complex) ^ (2 : Nat) * (W 0 x * d x) = d x
    rw [hh, <- mul_assoc, <- div_eq_mul_inv, div_self (pow_ne_zero _ hne), one_mul]
  let d0 := hd.mk d
  have h0 : Filter.EventuallyEq (ae mu) d d0 := hd.ae_eq_mk
  have hRep (t : Real) : And (Integrable (fun x => W t x * d0 x) mu)
      (integral mu (fun x => W t x * d0 x) = 0) := by
    have ht := h0.mono (fun x hx => congrArg (fun z : Complex => W t x * z) hx)
    exact And.intro ((h t).1.congr ht) ((integral_congr_ae ht).symm.trans (h t).2)
  have hRe := ae_zero_re_of_verticalMellin_eq_zero hd.measurable_mk hRep
  filter_upwards [hRe, h0] with x hR hx
  change (d0 x).re = 0 at hR
  rw [<- hx, show (d x).re = T x - (S x).re by simp only [d, Complex.sub_re, Complex.ofReal_re]] at hR
  exact sub_eq_zero.mp hR


private theorem norm_spectralTailSeries_le {I : Type*} (rho : I -> Complex)
    (h : Summable (fun i => norm (primitiveZeroWeight (rho i))))
    {u x : Real} (hx : 1 < x) (hu : forall i, (rho i).re <= u) :
    norm (spectralTailSeries rho x) <=
      (tsum (fun i => norm (primitiveZeroWeight (rho i)))) * x ^ (u - 1) := by
  have hx0 := zero_lt_one.trans hx
  let b (i : I) := primitiveZeroWeight (rho i)
  have hterm (i : I) :
      norm (b i * (x : Complex) ^ (rho i - 1)) <= norm (b i) * x ^ (u - 1) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx.le (sub_le_sub_right (hu i) 1)) (norm_nonneg _)
  have hs : Summable (fun i => norm (b i) * x ^ (u - 1)) := h.mul_right _
  have htermSum : Summable (fun i => norm (b i * (x : Complex) ^ (rho i - 1))) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hs
  exact (norm_tsum_le_tsum_norm htermSum).trans
    (by rw [<- tsum_mul_right]; exact htermSum.tsum_le_tsum hterm hs)

private theorem norm_dedekindSpectralTail_eventually_le (hRH : DedekindRH K) (a : Complex) :
    Filter.Eventually (fun x : Real => norm (dedekindSpectralTail K a x) <=
      (tsum (fun i : DedekindCompletedZeroIndex K =>
        (Inv.inv (norm (completedDedekindZero K i))) ^ (2 : Nat)) + 1) / Real.sqrt x) atTop := by
  let Z := completedDedekindZero K
  let M := tsum (fun i : DedekindCompletedZeroIndex K => (Inv.inv (norm (Z i))) ^ (2 : Nat))
  let m := dedekindOriginMultiplicity K
  let r := (nrRealPlaces K : Complex)
  let c := (nrComplexPlaces K : Complex)
  let A : Real := norm (a + m) +
    norm r * tsum (fun n => norm (primitiveZeroWeight (gammaZero 2 n))) +
    norm c * tsum (fun n => norm (primitiveZeroWeight (gammaZero 1 n)))
  have hm : 0 <= norm m := norm_nonneg _
  have hZ (i : DedekindCompletedZeroIndex K) : (Z i).re = 1 / 2 :=
    completedDedekindPoleCleared_zero_re_of_dedekindRH K hRH (completedDedekindZero_is_zero K i)
  have halpha : Filter.Eventually (fun x : Real => 2 * A <= Real.sqrt x) atTop :=
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop _)
  have hLog : Asymptotics.IsLittleO atTop (fun x : Real => norm m * Real.log x) Real.sqrt := by
    change Asymptotics.IsLittleO atTop (fun x : Real => norm m * Real.log x)
      (fun x : Real => Real.sqrt x)
    simp_rw [Real.sqrt_eq_rpow]
    exact (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : Real))).const_mul_left (norm m)
  have hbeta := (Asymptotics.isLittleO_iff.mp hLog) (by norm_num : 0 < (1 / 2 : Real))
  filter_upwards [eventually_gt_atTop (1 : Real), halpha, hbeta] with x hx hAx hLx
  have hx0 := zero_lt_one.trans hx
  have hxS := Real.sqrt_pos.mpr hx0
  have hQ : norm ((x : Complex) ^ (-(1 : Complex))) = 1 / x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.neg_re, Complex.one_re,
      Real.rpow_neg hx0.le, Real.rpow_one, one_div]
  have hLogPos := Real.log_nonneg hx.le
  have hZb := norm_spectralTailSeries_le Z (summable_norm_primitiveZeroWeight K hRH)
    hx (u := 1 / 2) (fun i => (hZ i).le)
  have hw : (tsum (fun i => norm (primitiveZeroWeight (Z i)))) = M := by
    exact tsum_congr (fun i => norm_primitiveZeroWeight_of_re_eq_half (hZ i))
  rw [hw, show (1 / 2 : Real) - 1 = -(1 / 2) by norm_num, Real.rpow_neg hx0.le,
    <- Real.sqrt_eq_rpow, <- div_eq_mul_inv] at hZb
  have hGb (q : Real) (hq : 1 <= q) :
      norm (spectralTailSeries (gammaZero q) x) <=
        (tsum (fun n => norm (primitiveZeroWeight (gammaZero q n)))) / x := by
    have h := norm_spectralTailSeries_le (gammaZero q) (summable_norm_gammaZeroWeight hq)
      hx (u := 0) (fun n => (gammaZero_re_of_one_le hq n).le)
    rwa [zero_sub, Real.rpow_neg hx0.le, Real.rpow_one, <- div_eq_mul_inv] at h
  have hRb := mul_le_mul_of_nonneg_left (hGb 2 (by norm_num)) (norm_nonneg r)
  have hCb := mul_le_mul_of_nonneg_left (hGb 1 (by norm_num)) (norm_nonneg c)
  have hTri : norm (dedekindSpectralTail K a x) <= M / Real.sqrt x + (A + norm m * Real.log x) / x := by
    unfold dedekindSpectralTail
    rw [norm_neg]
    calc
      _ <= norm (a + m) * (1 / x) + norm m * (1 / x * Real.log x) +
          M / Real.sqrt x +
          norm r * ((tsum (fun n => norm (primitiveZeroWeight (gammaZero 2 n)))) / x) +
          norm c * ((tsum (fun n => norm (primitiveZeroWeight (gammaZero 1 n)))) / x) := by
        repeat apply norm_add_le_of_le
        all_goals first
          | exact hZb
          | exact (by rw [norm_mul]; exact hRb)
          | exact (by rw [norm_mul]; exact hCb)
          | exact (by rw [norm_mul, hQ])
          | exact (by rw [norm_mul, norm_mul, hQ, Complex.norm_real, Real.norm_of_nonneg hLogPos])
      _ = _ := by dsimp [A]; ring
  have hLogI : norm m * Real.log x <= (1 / 2 : Real) * Real.sqrt x := by
    simpa only [Real.norm_of_nonneg (mul_nonneg hm hLogPos), Real.norm_of_nonneg hxS.le] using hLx
  have hSmall : A + norm m * Real.log x <= Real.sqrt x := by linarith
  have hEq : Real.sqrt x / x = 1 / Real.sqrt x := by
    field_simp [hxS.ne', hx0.ne']
    exact Real.sq_sqrt hx0.le
  calc
    _ <= M / Real.sqrt x + (A + norm m * Real.log x) / x := hTri
    _ <= M / Real.sqrt x + Real.sqrt x / x :=
      add_le_add (le_refl _) (div_le_div_of_nonneg_right hSmall hx0.le)
    _ = _ := by rw [hEq]; ring

private theorem continuousAt_realPrimitiveFromOne {g : Real -> Real}
    (hI : forall b : Real, 1 < b -> IntegrableOn g (Ioo 1 b))
    {x : Real} (hx : 1 < x) :
    ContinuousAt (realPrimitiveFromOne g) x := by
  let b := x + 1
  have hb : x < b := by dsimp [b]; linarith
  let G := (Ioo (1 : Real) b).indicator g
  have hG : Integrable G volume := (hI b (hx.trans hb)).integrable_indicator measurableSet_Ioo
  have hE : Filter.EventuallyEq (nhds x)
      (fun y : Real => intervalIntegral G 1 y volume) (realPrimitiveFromOne g) := by
    filter_upwards [isOpen_Ioo.mem_nhds (And.intro hx hb)] with y hy
    rw [intervalIntegral.integral_of_le hy.1.le, integral_Ioc_eq_integral_Ioo, realPrimitiveFromOne]
    exact setIntegral_congr_fun measurableSet_Ioo (fun z hz =>
      indicator_of_mem (show Membership.mem (Ioo (1 : Real) b) z from
        And.intro hz.1 (hz.2.trans hy.2)) g)
  exact (hG.continuous_primitive 1).continuousAt.congr hE

private theorem le_everywhere_of_ae_le_tail {u v : Real -> Real} {X : Real}
    (hu : forall x : Real, X < x -> ContinuousAt u x)
    (hv : forall x : Real, X < x -> ContinuousAt v x)
    (h : Filter.Eventually (fun y : Real => X < y -> u y <= v y) (ae volume))
    {x : Real} (hx : X < x) :
    u x <= v x := by
  by_contra hn
  have hU := (hv x hx).tendsto.eventually_lt (hu x hx).tendsto (lt_of_not_ge hn)
  have hX : Filter.Eventually (fun y : Real => X < y) (nhds x) := Ioi_mem_nhds hx
  have he : Membership.mem (nhds x) { y : Real | v y < u y /\ X < y } := hU.and hX
  choose O hO using mem_nhds_iff.mp he
  have hNull := ae_iff.mp h
  have hSub : Set.Subset O {y : Real | Not (X < y -> u y <= v y)} := by
    intro y hy
    have hy' := hO.1 hy
    exact fun p => (not_le.mpr hy'.1) (p hy'.2)
  exact (hO.2.1.measure_ne_zero volume (Exists.intro x hO.2.2)) (measure_mono_null hSub hNull)


/-- Under Dedekind RH the integrated relative Chebyshev error has a
primitive tail bounded in absolute value by a constant times x^(-1/2). -/
theorem exists_dedekindChebyshevPrimitiveTailBound (hRH : DedekindRH K) :
    exists c B X : Real, 1 < X /\ 0 <= B /\ B < 12 + 3 * Real.log ((discr K).natAbs : Real) /\
      Tendsto (realPrimitiveFromOne (dedekindChebyshevErrorRatio K)) atTop (nhds c) /\
      forall t : Real, X <= t ->
        abs (primitiveTail (dedekindChebyshevErrorRatio K) c t) <= B / Real.sqrt t := by
  choose c hc using exists_dedekindChebyshevPrimitiveLimit K
  choose a ha using ae_dedekindPrimitiveTail_eq_re_spectralTail K hRH hc.2
  let T := primitiveTail (dedekindChebyshevErrorRatio K) c
  let S := dedekindSpectralTail K a
  let M := tsum (fun i : DedekindCompletedZeroIndex K =>
    (Inv.inv (norm (completedDedekindZero K i))) ^ (2 : Nat))
  let B := M + 1
  have hMass : M <= 9 + 3 * Real.log ((discr K).natAbs : Real) :=
    completedDedekindZeroMass_le K hRH
  have hB : 0 <= B := by
    have hM : 0 <= M := tsum_nonneg (fun _ => sq_nonneg _)
    dsimp [B]
    linarith
  have hGap : B < 12 + 3 * Real.log ((discr K).natAbs : Real) := by
    dsimp [B]
    linarith
  choose X hX using eventually_atTop.mp (norm_dedekindSpectralTail_eventually_le K hRH a)
  let Y := max 1 X
  have hA : Filter.Eventually (fun x : Real => Y < x -> abs (T x) <= B / Real.sqrt x)
      (ae volume) := by
    have hA : Filter.Eventually (fun x : Real => Y < x -> abs (T x) <= B / Real.sqrt x)
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      refine ha.mono ?_
      intro x he hx
      change T x = (S x).re at he
      rw [he]
      exact (Complex.abs_re_le_norm (S x)).trans
        (hX x ((le_max_right 1 X).trans hx.le))
    exact ((ae_restrict_iff' measurableSet_Ioi).mp hA).mono (fun x h hx =>
      h ((le_max_left 1 X).trans_lt hx) hx)
  have hContinuousT (x : Real) (hx : Y < x) : ContinuousAt (fun x => abs (T x)) x := by
    have h1 : 1 < x := (le_max_left 1 X).trans_lt hx
    exact (continuousAt_const.sub (continuousAt_realPrimitiveFromOne
      (fun b _ => dedekindChebyshevErrorRatio_integrableOn_Ioo K b) h1)).abs
  have hContinuousB (x : Real) (hx : Y < x) : ContinuousAt (fun x => B / Real.sqrt x) x := by
    have h1 : 1 < x := (le_max_left 1 X).trans_lt hx
    exact continuousAt_const.div Real.continuous_sqrt.continuousAt
      (Real.sqrt_pos.mpr (zero_lt_one.trans h1)).ne'
  have hAll (t : Real) (ht : Y < t) : abs (T t) <= B / Real.sqrt t :=
    le_everywhere_of_ae_le_tail hContinuousT hContinuousB hA ht
  have hY : 1 < Y + 1 := (le_max_left 1 X).trans_lt (lt_add_one Y)
  exact Exists.intro c (Exists.intro B (Exists.intro (Y + 1)
    (And.intro hY (And.intro hB (And.intro hGap (And.intro hc.1
      (fun t ht => hAll t ((lt_add_one Y).trans_le ht))))))))

/-- Dedekind RH implies the corrected ideal Robin inequality for this field. -/
theorem correctedIdealRobin_of_dedekindRH (hRH : DedekindRH K) :
    CorrectedIdealRobin K := by
  choose c B X h using exists_dedekindChebyshevPrimitiveTailBound K hRH
  exact correctedIdealRobin_of_abs_primitiveTail K (X := X)
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

end Robin1984.GRH
