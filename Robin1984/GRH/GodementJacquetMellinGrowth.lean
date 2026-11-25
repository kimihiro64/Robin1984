import Robin1984.GRH.GodementJacquetThetaMellin

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and absolute bounds for Mellin transforms on vertical strips.
- Formalization note: Derives a uniform vertical-strip bound from the two-sided exponential moments and uses it in the order-one proof for a paired standard completion.
- PROVENANCE-END
-/

/-!
# Vertical-strip bounds and growth of the theta Mellin transform

The two-sided exponential moment bounds the transform uniformly in the
imaginary part. This bound supplies the middle strip in the order-one
estimate when the paired completion has the required Euler identity
on the right and the norm reflection on the left.
For an individual completion, the contragredient Euler product controls
the reflected half-plane.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open MeasureTheory

/-- A two-sided exponential moment bounds the logarithmic Mellin transform
by a constant independent of the imaginary part of the argument. -/
theorem norm_godementJacquetLogMellin_le_of_exponentialMoment
    (n : Nat) (F : Real -> Complex) (R : Real)
    (hMoment : Integrable (fun t : Real => norm (F t) * (Real.exp (abs t)) ^ R)
      (volume : Measure Real))
    (s : Complex) (hs : abs (s + ((n : Complex) - 1) / 2).re <= R) :
    norm (godementJacquetLogMellin n F s) <= integral (volume : Measure Real)
      (fun t : Real => norm (F t) * (Real.exp (abs t)) ^ R) := by
  unfold godementJacquetLogMellin
  refine norm_integral_le_of_norm_le hMoment (Filter.Eventually.of_forall fun t => ?_)
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  refine Real.exp_le_exp.mpr ?_
  calc
    _ <= abs (t * (s + ((n : Complex) - 1) / 2).re) := le_abs_self _
    _ = abs t * abs (s + ((n : Complex) - 1) / 2).re := abs_mul _ _
    _ <= _ := mul_le_mul_of_nonneg_left hs (abs_nonneg t)

/-- Two-sided exponential moments give a uniform bound on the vertical
strip used in the order-one argument. -/
theorem exists_godementJacquetLogMellin_verticalStrip_bound_of_exponentialMoments
    (n : Nat) (F : Real -> Complex)
    (hMoment : forall a : Real,
      Integrable (fun t : Real => norm (F t) * (Real.exp (abs t)) ^ a) (volume : Measure Real)) :
    Exists (fun M : Real => And (0 < M)
      (forall s : Complex, -2 <= s.re -> s.re <= 3 ->
        norm (godementJacquetLogMellin n F s) <= M)) := by
  let c : Complex := ((n : Complex) - 1) / 2
  let R := 3 + abs c.re
  let B := integral (volume : Measure Real) (fun t : Real => norm (F t) * (Real.exp (abs t)) ^ R)
  refine Exists.intro (max 1 B) (And.intro (zero_lt_one.trans_le (le_max_left _ _)) ?_)
  intro s ha hb
  have hS : abs s.re <= 3 := abs_le.mpr (And.intro (by linarith) hb)
  have hR : abs (s + c).re <= R := by
    rw [Complex.add_re]
    exact (abs_add_le _ _).trans (add_le_add hS (le_refl (abs c.re)))
  exact (norm_godementJacquetLogMellin_le_of_exponentialMoment n F R (hMoment R) s hR).trans
    (le_max_right _ _)

/-- Poisson reflection and rapid decay of the two positive tails give a
uniform bound on the vertical strip used in the order-one argument. -/
theorem exists_godementJacquetLogMellin_verticalStrip_bound_of_decay
    (n : Nat) (F G : Real -> Complex) (hF : Measurable F) (hG : Measurable G)
    (hReflect : forall t : Real,
      F t = ((Real.exp (-((n : Real) * t)) : Real) : Complex) * G (-t))
    (hDecayF : forall b : Real, 0 < b -> Exists (fun C : Real =>
      forall t : Real, 0 <= t -> norm (F t) <= C * Real.exp (-b * t)))
    (hDecayG : forall b : Real, 0 < b -> Exists (fun C : Real =>
      forall t : Real, 0 <= t -> norm (G t) <= C * Real.exp (-b * t))) :
    Exists (fun M : Real => And (0 < M)
      (forall s : Complex, -2 <= s.re -> s.re <= 3 ->
        norm (godementJacquetLogMellin n F s) <= M)) := by
  apply exists_godementJacquetLogMellin_verticalStrip_bound_of_exponentialMoments n F
  exact integrable_godementJacquet_exponentialMoment_of_reflection n F G hReflect
    (integrableOn_godementJacquet_exponentialMoment_of_decay F hF hDecayF)
    (integrableOn_godementJacquet_exponentialMoment_of_decay G hG hDecayG)

/-- Once a paired completion is identified with two theta Mellin
transforms, exponential moments provide the missing vertical-strip
estimate for the order-one proof. The right-half-plane Euler identity
and the norm reflection are the standard paired identities. -/
theorem entireOrderOne_of_standardPairedEulerProduct_and_godementJacquetLogMellin
    {powers realPlaces complexPlaces : Type*} [Fintype realPlaces] [Fintype complexPlaces]
    (d : GrandRobinEulerData powers) (hTwo : forall i, 2 <= d.normPower i)
    (hSummable : Summable (fun i => norm (d.coefficient i) * d.normPower i ^ (-(2 : Real))))
    {conductor : Real} (hConductor : 0 < conductor) (m : Nat)
    (mu : realPlaces -> Complex) (nu : complexPlaces -> Complex)
    (hMu : forall i, -(1 : Real) / 2 < (mu i).re)
    (hNu : forall i, -(1 : Real) / 2 < (nu i).re)
    (n : Nat) (F G : Real -> Complex) (hF : Measurable F) (hG : Measurable G)
    (hFM : forall a : Real,
      Integrable (fun t : Real => norm (F t) * (Real.exp (abs t)) ^ a) (volume : Measure Real))
    (hGM : forall a : Real,
      Integrable (fun t : Real => norm (G t) * (Real.exp (abs t)) ^ a) (volume : Measure Real))
    (Lambda : Complex -> Complex)
    (hMellin : forall s, Lambda s =
      godementJacquetLogMellin n F s * godementJacquetLogMellin n G s)
    (hCompletion : forall s : Complex, 3 <= s.re ->
      Lambda s = standardCompletionFactor conductor m mu nu s *
        ((s - 1) ^ m * Complex.exp (grandEulerLog d s)))
    (hReflect : forall s : Complex, norm (Lambda (1 - s)) = norm (Lambda s)) :
    Complex.Hadamard.EntireOfOrderAtMost 1 Lambda := by
  have hEntire : Differentiable Complex Lambda := by
    rw [funext hMellin]
    exact (differentiable_godementJacquetLogMellin_of_exponentialMoments n F hF hFM).mul
      (differentiable_godementJacquetLogMellin_of_exponentialMoments n G hG hGM)
  refine entireOrderOne_of_standardPairedEulerProduct_and_stripBound d hTwo hSummable
    hConductor m mu nu hMu hNu hEntire hCompletion hReflect ?_
  choose M hM using exists_godementJacquetLogMellin_verticalStrip_bound_of_exponentialMoments n F hFM
  choose N hN using exists_godementJacquetLogMellin_verticalStrip_bound_of_exponentialMoments n G hGM
  let C := M * N + 1
  have hC : 0 < C := add_pos (mul_pos hM.1 hN.1) zero_lt_one
  intro eps hEps
  refine Exists.intro C (And.intro hC ?_)
  intro s hs1 hs2
  have hPow : 1 <= (1 + norm s) ^ (1 + eps) :=
    Real.one_le_rpow (le_add_of_nonneg_right (norm_nonneg _)) (by linarith)
  calc
    _ = norm (godementJacquetLogMellin n F s) * norm (godementJacquetLogMellin n G s) := by
      rw [hMellin s, norm_mul]
    _ <= M * N := mul_le_mul (hM.2 s hs1 hs2) (hN.2 s hs1 hs2) (norm_nonneg _) (le_of_lt hM.1)
    _ <= Real.exp C := by
      have h := Real.add_one_le_exp C
      dsimp only [C] at h
      linarith
    _ <= _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (le_of_lt hC) hPow)

private theorem hasOrderOneBoundOn_standardIndividualEulerCompletion_on_right
    {powers realPlaces complexPlaces : Type*}
    [Fintype realPlaces] [Fintype complexPlaces]
    (q : powers -> Real) (b : powers -> Complex) (hTwo : forall i, 2 <= q i)
    (hSum : Summable (fun i => norm (b i) * q i ^ (-(2 : Real))))
    {conductor : Real} (hConductor : 0 < conductor) (m : Nat)
    (mu : realPlaces -> Complex) (nu : complexPlaces -> Complex)
    (hMu : forall i, -(1 : Real) / 2 < (mu i).re)
    (hNu : forall i, -(1 : Real) / 2 < (nu i).re)
    {Lambda : Complex -> Complex}
    (hEuler : forall s : Complex, 3 <= s.re ->
      Lambda s = standardCompletionFactor conductor m mu nu s *
        ((s - 1) ^ m * Complex.exp (complexPrimePowerEulerLog q b s))) :
    forall eps : Real, 0 < eps -> Exists (fun C : Real => And (0 < C)
      (forall s : Complex, 3 <= s.re ->
        norm (Lambda s) <= Real.exp (C * (1 + norm s) ^ (1 + eps)))) := by
  let C := tsum (fun i => (Real.log 2) ^ (-1 : Int) * (norm (b i) * q i ^ (-(2 : Real))))
  refine standardCompletion_orderOneBound_on_right hConductor m mu nu hMu hNu C ?_ hEuler
  intro s hs
  have h2 : (2 : Real) <= s.re := (by norm_num : (2 : Real) <= 3).trans hs
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr
    ((Complex.re_le_norm _).trans (norm_complexPrimePowerEulerLog_le q b hTwo hSum h2))

/-- The primal Mellin is entire of order at most one. The original Euler
product bounds it on the right, the contragredient Euler product bounds
it on the left through reflection, and the Mellin moment bounds the
middle strip. -/
theorem entireOrderOne_of_individualGodementJacquetMellin
    {powers dualPowers realPlaces complexPlaces dualRealPlaces dualComplexPlaces : Type*}
    [Fintype realPlaces] [Fintype complexPlaces]
    [Fintype dualRealPlaces] [Fintype dualComplexPlaces]
    (n : Nat) (F G : Real -> Complex) (hF : Measurable F)
    (hMoment : forall a : Real, Integrable (fun t : Real =>
      norm (F t) * (Real.exp (abs t)) ^ a) (volume : Measure Real))
    (q : powers -> Real) (b : powers -> Complex) (hTwo : forall i, 2 <= q i)
    (hSum : Summable (fun i => norm (b i) * q i ^ (-(2 : Real))))
    (qD : dualPowers -> Real) (bD : dualPowers -> Complex) (hTwoD : forall i, 2 <= qD i)
    (hSumD : Summable (fun i => norm (bD i) * qD i ^ (-(2 : Real))))
    {conductor conductorD : Real} (hConductor : 0 < conductor) (hConductorD : 0 < conductorD)
    (m mD : Nat) (mu : realPlaces -> Complex) (nu : complexPlaces -> Complex)
    (muD : dualRealPlaces -> Complex) (nuD : dualComplexPlaces -> Complex)
    (hMu : forall i, -(1 : Real) / 2 < (mu i).re)
    (hNu : forall i, -(1 : Real) / 2 < (nu i).re)
    (hMuD : forall i, -(1 : Real) / 2 < (muD i).re)
    (hNuD : forall i, -(1 : Real) / 2 < (nuD i).re)
    (hEuler : forall s : Complex, 3 <= s.re ->
      godementJacquetLogMellin n F s = standardCompletionFactor conductor m mu nu s *
        ((s - 1) ^ m * Complex.exp (complexPrimePowerEulerLog q b s)))
    (hEulerD : forall s : Complex, 3 <= s.re ->
      godementJacquetLogMellin n G s = standardCompletionFactor conductorD mD muD nuD s *
        ((s - 1) ^ mD * Complex.exp (complexPrimePowerEulerLog qD bD s)))
    (hReflect : forall s : Complex,
      norm (godementJacquetLogMellin n G (1 - s)) = norm (godementJacquetLogMellin n F s)) :
    Complex.Hadamard.EntireOfOrderAtMost 1 (godementJacquetLogMellin n F) := by
  have hRight := hasOrderOneBoundOn_standardIndividualEulerCompletion_on_right
    q b hTwo hSum hConductor m mu nu hMu hNu hEuler
  have hRightD := hasOrderOneBoundOn_standardIndividualEulerCompletion_on_right
    qD bD hTwoD hSumD hConductorD mD muD nuD hMuD hNuD hEulerD
  refine entireOrderOne_of_dualRightBounds_and_stripBound
    (differentiable_godementJacquetLogMellin_of_exponentialMoments n F hF hMoment)
    hRight hRightD hReflect ?_
  choose M hM using exists_godementJacquetLogMellin_verticalStrip_bound_of_exponentialMoments n F hMoment
  let C := M + 1
  have hC : 0 < C := add_pos hM.1 zero_lt_one
  intro eps hEps
  refine Exists.intro C (And.intro hC ?_)
  intro s hs1 hs2
  have hPow : 1 <= (1 + norm s) ^ (1 + eps) :=
    Real.one_le_rpow (le_add_of_nonneg_right (norm_nonneg _)) (by linarith)
  calc
    _ <= M := hM.2 s hs1 hs2
    _ <= Real.exp C := by
      have h := Real.add_one_le_exp C
      dsimp only [C] at h
      linarith
    _ <= _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (le_of_lt hC) hPow)

end Robin1984.GRH
