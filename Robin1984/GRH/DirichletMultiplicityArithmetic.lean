import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Ring
import Robin1984.GRH.RiemannMultiplicityArithmetic

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Hurwitz theta functional equations and the explicit Euler series for ordinary Dirichlet L-functions.
- Formalization note: The split Hurwitz Mellin tails give order one for the actual pole-cleared functions, including imprimitive characters.
- PROVENANCE-END
-/

/-!
# Arithmetic and order-one bounds for Dirichlet L-functions

The continuation used here is Mathlib's actual Dirichlet L-function.
The theta tail bounds and Euler logarithmic derivative apply to all
characters of a positive modulus.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Complex.Hadamard DedekindZeta.MellinPrinciple Filter Set
open scoped Classical Topology

local macro "weakFEfZero" : term => do
  pure (Lean.mkIdent (Lean.Name.str `WeakFEPair (String.ofList ['f', Char.ofNat 8320])))

local macro "weakFEgZero" : term => do
  pure (Lean.mkIdent (Lean.Name.str `WeakFEPair (String.ofList ['g', Char.ofNat 8320])))

local macro "weakFEEpsilon" : term => do
  pure (Lean.mkIdent (Lean.Name.str `WeakFEPair (String.ofList [Char.ofNat 949])))

local macro "weakFELambda" : term => do
  pure (Lean.mkIdent (Lean.Name.str `WeakFEPair (String.ofList [Char.ofNat 923])))

local macro "weakFELambdaZero" : term => do
  pure (Lean.mkIdent (Lean.Name.str `WeakFEPair (String.ofList [Char.ofNat 923, Char.ofNat 8320])))

local macro "weakFELambdaZeroDifferentiable" : term => do
  pure (Lean.mkIdent (Lean.Name.str `WeakFEPair
    ("differentiable_" ++ String.ofList [Char.ofNat 923, Char.ofNat 8320])))

local macro "weakFELambdaZeroEq" : term => do
  pure (Lean.mkIdent (Lean.Name.str `WeakFEPair
    (String.ofList [Char.ofNat 923, Char.ofNat 8320] ++ "_eq")))

/-- The pole-free weak functional equation Mellin transform is the sum
of the two positive-half-line Mellin tails with the same normalization. -/
theorem weakFELambdaZero_eq_mellinTail (P : WeakFEPair Complex) {c p : Real}
    (hPair : IsMellinPair P.f P.g (weakFEfZero P) (weakFEgZero P) (weakFEEpsilon P) P.k c p) :
    weakFELambdaZero P = mellinTail P.f P.g (weakFEfZero P) (weakFEgZero P) (weakFEEpsilon P) P.k := by
  have hAn : AnalyticOnNhd Complex (weakFELambdaZero P) (univ : Set Complex) := fun s _ =>
    (weakFELambdaZeroDifferentiable P).analyticAt s
  let z : Complex := ((P.k + 1 : Real) : Complex)
  have hz : P.k < z.re := by
    change P.k < (((P.k + 1 : Real) : Complex)).re
    rw [Complex.ofReal_re]
    exact lt_add_of_pos_right _ zero_lt_one
  have hNear : Filter.EventuallyEq (nhds z) (weakFELambdaZero P)
      (mellinTail P.f P.g (weakFEfZero P) (weakFEgZero P) (weakFEEpsilon P) P.k) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with s hs
    have hM := (P.hasMellin hs).2
    change reducedMellin P.f (weakFEfZero P) s = weakFELambda P s at hM
    rw [weakFELambdaZeroEq P s, <- hM, <- mellinContinuation_eq hPair hs]
    unfold mellinContinuation
    rw [show (P.k : Complex) - s = -(s - (P.k : Complex)) by ring, div_neg]
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  exact hAn.eq_of_eventuallyEq (mellinTail_analyticOn hPair) hNear

/-- The weak functional-equation proof of order one, with the two tail
exponents in the original Hurwitz or automorphic normalization. -/
theorem entireOfOrderAtMost_one_weakFELambdaZero_comp (P : WeakFEPair Complex) {c p : Real}
    (hPair : IsMellinPair P.f P.g (weakFEfZero P) (weakFEgZero P) (weakFEEpsilon P) P.k c p)
    {z : Complex -> Complex} (hZ : Differentiable Complex z)
    (hLeft : forall s, (z s).re - 1 <= norm s)
    (hRight : forall s, ((P.k : Complex) - z s).re - 1 <= norm s) :
    EntireOfOrderAtMost 1 (fun s => weakFELambdaZero P (z s)) := by
  rw [weakFELambdaZero_eq_mellinTail P hPair]
  exact entireOfOrderAtMost_one_mellinTail_comp hPair hZ hLeft hRight

local macro "weakFEEpsilon_ne_zero" : term => do
  pure (Lean.mkIdent (Lean.Name.str `WeakFEPair (String.ofList ['h', Char.ofNat 949])))

local macro "completedEvenPoleFree" : term => do
  pure (Lean.mkIdent (Lean.Name.str `HurwitzZeta
    ("completedHurwitzZetaEven" ++ String.ofList [Char.ofNat 8320])))

local macro "oddPair_fZero" : term => do
  pure (Lean.mkIdent (Lean.Name.str `HurwitzZeta
    ("hurwitzOddFEPair_f" ++ String.ofList [Char.ofNat 8320])))

local macro "oddPair_gZero" : term => do
  pure (Lean.mkIdent (Lean.Name.str `HurwitzZeta
    ("hurwitzOddFEPair_g" ++ String.ofList [Char.ofNat 8320])))

private theorem isBigO_ofReal_atTop {f g : Real -> Real} (h : Asymptotics.IsBigO atTop f g) :
    Asymptotics.IsBigO atTop (fun x => (f x : Complex)) g := by
  choose C hC using h.bound
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with x hx
  simpa only [Complex.norm_real] using hx

private theorem isBigO_exp_rate_le {a c : Real} (h : c <= a) :
    Asymptotics.IsBigO atTop (fun x : Real => Real.exp (-a * x))
      (fun x => Real.exp (-c * x ^ (1 : Real))) := by
  apply Asymptotics.IsBigO.of_bound'
  filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_one]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg h) hx)

private theorem exists_weakFEMellinPair_of_exponentialTails (P : WeakFEPair Complex)
    (hF : ContinuousOn P.f (Ioi (0 : Real))) (hG : ContinuousOn P.g (Ioi (0 : Real)))
    (hFDecay : exists c : Real, 0 < c /\
      Asymptotics.IsBigO atTop (fun x => P.f x - weakFEfZero P) (fun x => Real.exp (-c * x)))
    (hGDecay : exists c : Real, 0 < c /\
      Asymptotics.IsBigO atTop (fun x => P.g x - weakFEgZero P) (fun x => Real.exp (-c * x))) :
    exists c : Real,
      IsMellinPair P.f P.g (weakFEfZero P) (weakFEgZero P) (weakFEEpsilon P) P.k c 1 := by
  choose cF hCf using hFDecay
  choose cG hCg using hGDecay
  refine Exists.intro (min cF cG) (IsMellinPair.mk hF hG P.hk
    (lt_min hCf.1 hCg.1) zero_lt_one (weakFEEpsilon_ne_zero P)
    (hCf.2.trans (isBigO_exp_rate_le (min_le_left _ _)))
    (hCg.2.trans (isBigO_exp_rate_le (min_le_right _ _))) ?_)
  intro x hx
  simpa only [smul_eq_mul] using P.h_feq x hx

private theorem exists_hurwitzEven_mellinPair (a : UnitAddCircle) :
    let P := HurwitzZeta.hurwitzEvenFEPair a
    exists c : Real,
      IsMellinPair P.f P.g (weakFEfZero P) (weakFEgZero P) (weakFEEpsilon P) P.k c 1 := by
  let P := HurwitzZeta.hurwitzEvenFEPair a
  apply exists_weakFEMellinPair_of_exponentialTails P
  case hF =>
    exact Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel a)
  case hG =>
    exact Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel a)
  case hFDecay =>
    choose c hc using HurwitzZeta.isBigO_atTop_evenKernel_sub a
    refine Exists.intro c (And.intro hc.1 ?_)
    have h := isBigO_ofReal_atTop hc.2
    by_cases ha : a = 0
    case pos =>
      simpa [P, HurwitzZeta.hurwitzEvenFEPair, ha, Complex.ofReal_sub] using h
    case neg =>
      simpa [P, HurwitzZeta.hurwitzEvenFEPair, ha, Complex.ofReal_sub] using h
  case hGDecay =>
    choose c hc using HurwitzZeta.isBigO_atTop_cosKernel_sub a
    refine Exists.intro c (And.intro hc.1 ?_)
    have h := isBigO_ofReal_atTop hc.2
    simpa [P, HurwitzZeta.hurwitzEvenFEPair, Complex.ofReal_sub] using h

private theorem exists_hurwitzOdd_mellinPair (a : UnitAddCircle) :
    let P := HurwitzZeta.hurwitzOddFEPair a
    exists c : Real,
      IsMellinPair P.f P.g (weakFEfZero P) (weakFEgZero P) (weakFEEpsilon P) P.k c 1 := by
  let P := HurwitzZeta.hurwitzOddFEPair a
  apply exists_weakFEMellinPair_of_exponentialTails P
  case hF =>
    rw [show P.f = (fun x => (HurwitzZeta.oddKernel a x : Complex)) from
      funext (HurwitzZeta.hurwitzOddFEPair_f a)]
    exact Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_oddKernel a)
  case hG =>
    rw [show P.g = (fun x => (HurwitzZeta.sinKernel a x : Complex)) from
      funext (HurwitzZeta.hurwitzOddFEPair_g a)]
    exact Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_sinKernel a)
  case hFDecay =>
    choose c hc using HurwitzZeta.isBigO_atTop_oddKernel a
    refine Exists.intro c (And.intro hc.1 ?_)
    simpa [P, oddPair_fZero, HurwitzZeta.hurwitzOddFEPair_f, Function.comp_def] using
      isBigO_ofReal_atTop hc.2
  case hGDecay =>
    choose c hc using HurwitzZeta.isBigO_atTop_sinKernel a
    refine Exists.intro c (And.intro hc.1 ?_)
    simpa [P, oddPair_gZero, HurwitzZeta.hurwitzOddFEPair_g, Function.comp_def] using
      isBigO_ofReal_atTop hc.2

private theorem complex_half_re (s : Complex) : (s / 2).re = s.re / 2 := by
  norm_num [Complex.div_re, Complex.normSq_apply]

private theorem entireOrderOne_div_two {f : Complex -> Complex} (hf : EntireOfOrderAtMost 1 f) :
    EntireOfOrderAtMost 1 (fun z => f z / 2) := by
  refine And.intro (hf.differentiable.div_const 2) ?_
  intro e he
  choose A hA using hf.2 e he
  refine Exists.intro A (And.intro hA.1 (fun z => ?_))
  refine (show norm (f z / 2) <= norm (f z) from ?_).trans (hA.2 z)
  rw [norm_div, show norm (2 : Complex) = 2 by norm_num]
  linarith only [norm_nonneg (f z)]

/-- The entire part of the completed even Hurwitz zeta has order at most one. -/
theorem completedHurwitzEven_poleFree_entireOrderOne (a : UnitAddCircle) :
    EntireOfOrderAtMost 1 (completedEvenPoleFree a) := by
  choose c hPair using exists_hurwitzEven_mellinPair a
  have h := entireOfOrderAtMost_one_weakFELambdaZero_comp (HurwitzZeta.hurwitzEvenFEPair a)
    hPair (z := fun s => s / 2) (differentiable_id.div_const 2)
    (fun s => by
      rw [complex_half_re]
      linarith only [Complex.re_le_norm s, norm_nonneg s])
    (fun s => by
      change (((1 / 2 : Real) : Complex) - s / 2).re - 1 <= norm s
      rw [Complex.sub_re, Complex.ofReal_re, complex_half_re]
      have hNeg := Complex.re_le_norm (-s)
      rw [Complex.neg_re, norm_neg] at hNeg
      linarith only [hNeg, norm_nonneg s])
  exact entireOrderOne_div_two h

/-- The completed odd Hurwitz zeta has order at most one. -/
theorem completedHurwitzOdd_entireOrderOne (a : UnitAddCircle) :
    EntireOfOrderAtMost 1 (HurwitzZeta.completedHurwitzZetaOdd a) := by
  let P := HurwitzZeta.hurwitzOddFEPair a
  choose c hPair using exists_hurwitzOdd_mellinPair a
  have h := entireOfOrderAtMost_one_weakFELambdaZero_comp P hPair
    (z := fun s => (s + 1) / 2) ((differentiable_id.add_const 1).div_const 2)
    (fun s => by
      rw [complex_half_re, Complex.add_re, Complex.one_re]
      linarith only [Complex.re_le_norm s, norm_nonneg s])
    (fun s => by
      change (((P.k : Real) : Complex) - (s + 1) / 2).re - 1 <= norm s
      rw [Complex.sub_re, Complex.ofReal_re, complex_half_re, Complex.add_re, Complex.one_re]
      change (HurwitzZeta.hurwitzOddFEPair a).k - (s.re + 1) / 2 - 1 <= norm s
      rw [HurwitzZeta.hurwitzOddFEPair_k]
      have hNeg := Complex.re_le_norm (-s)
      rw [Complex.neg_re, norm_neg] at hNeg
      linarith only [hNeg, norm_nonneg s])
  have hEq (s : Complex) : weakFELambdaZero P s = weakFELambda P s := by
    rw [weakFELambdaZeroEq P s]
    simp [P, oddPair_fZero, oddPair_gZero]
  have hFun : (fun s => weakFELambdaZero P ((s + 1) / 2) / 2) =
      HurwitzZeta.completedHurwitzZetaOdd a := by
    funext s
    exact congrArg (fun z : Complex => z / 2) (hEq ((s + 1) / 2))
  rw [<- hFun]
  exact entireOrderOne_div_two h

/-- The Euler coefficients for the signed triangular remainder of a Dirichlet character. -/
def dirichletPrimePowerCoefficient {N : Nat} (chi : DirichletCharacter Complex N)
    (n : Nat) : Complex :=
  chi (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : Complex)

/-- The principal pole contributes one, and nonprincipal characters contribute zero. -/
def dirichletMultiplicityPoleOrder {N : Nat} (chi : DirichletCharacter Complex N) : Real :=
  if chi = 1 then 1 else 0

private theorem riemannPrimePowerNorm_eq_natCast_of_ne_zero {n : Nat}
    (h : Not (n = 0)) : riemannPrimePowerNorm n = (n : Real) := by
  unfold riemannPrimePowerNorm
  rw [max_eq_right (Nat.pos_of_ne_zero h)]

/-- The twisted von Mangoldt series equals the complex prime-power series. -/
theorem LSeries_twist_vonMangoldt_eq_tsum_primePowerNorm {N : Nat}
    (chi : DirichletCharacter Complex N) (s : Complex) :
    LSeries (dirichletPrimePowerCoefficient chi) s =
      tsum (fun n => dirichletPrimePowerCoefficient chi n *
        (riemannPrimePowerNorm n : Complex) ^ (-s)) := by
  unfold LSeries
  refine tsum_congr ?_
  intro n
  by_cases hn : n = 0
  case pos => simp [hn, LSeries.term_zero, dirichletPrimePowerCoefficient]
  case neg =>
    rw [LSeries.term_of_ne_zero hn, riemannPrimePowerNorm_eq_natCast_of_ne_zero hn,
      Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]

/-- The complex arithmetic coefficients satisfy the absolute Mellin condition. -/
theorem summable_norm_dirichletPrimePowerCoefficient {N : Nat}
    (chi : DirichletCharacter Complex N) {r : Real} (hr : 1 < r) :
    Summable (fun n => norm (dirichletPrimePowerCoefficient chi n) *
      (riemannPrimePowerNorm n) ^ (-r)) := by
  have h := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi
    (s := (r : Complex)) (by simpa only [Complex.ofReal_re] using hr)).norm
  change Summable (fun n => norm (LSeries.term (dirichletPrimePowerCoefficient chi)
    (r : Complex) n)) at h
  refine h.congr ?_
  intro n
  by_cases hn : n = 0
  case pos => simp [hn, LSeries.term_zero, dirichletPrimePowerCoefficient]
  case neg =>
    rw [LSeries.norm_term_eq, if_neg hn, riemannPrimePowerNorm_eq_natCast_of_ne_zero hn,
      Real.rpow_neg (Nat.cast_nonneg n)]
    simp only [Complex.ofReal_re, div_eq_mul_inv]

/-- The actual Dirichlet L-function has logarithmic derivative given by its
twisted von Mangoldt series on the half-plane of absolute convergence. -/
theorem logDeriv_dirichletLFunction_eq_primePowerSeries {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction chi) s =
      -tsum (fun n => dirichletPrimePowerCoefficient chi n *
        (riemannPrimePowerNorm n : Complex) ^ (-s)) := by
  have hEq : Filter.EventuallyEq (nhds s) (DirichletCharacter.LFunction chi)
      (LSeries (fun n : Nat => chi (n : ZMod N))) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries chi hz
  rw [(logDeriv_congr_nhds hEq).self_of_nhds, <- LSeries_twist_vonMangoldt_eq_tsum_primePowerNorm]
  have hMangoldt := DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs
  change LSeries (dirichletPrimePowerCoefficient chi) s = _ at hMangoldt
  rw [hMangoldt, logDeriv_apply, neg_div, neg_neg]

/-- Removing the principal pole adds exactly its rational logarithmic derivative.
The local factor identity suffices for the arithmetic Mellin transform. -/
theorem logDeriv_dirichletPoleCleared_eq_primePowerSeries {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (F : Complex -> Complex)
    (hF : forall z : Complex, 1 < z.re ->
      F z = (if chi = 1 then z - 1 else 1) * DirichletCharacter.LFunction chi z)
    {s : Complex} (hs : 1 < s.re) :
    logDeriv F s = (dirichletMultiplicityPoleOrder chi : Complex) / (s - 1) -
      tsum (fun n => dirichletPrimePowerCoefficient chi n *
        (riemannPrimePowerNorm n : Complex) ^ (-s)) := by
  let P (z : Complex) := if chi = 1 then z - 1 else 1
  have hs1 : Not (s = 1) := by
    intro he
    rw [he, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hL0 : Not (DirichletCharacter.LFunction chi s = 0) := by
    rw [DirichletCharacter.LFunction_eq_LSeries chi hs]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re chi hs
  have hL := DirichletCharacter.differentiableAt_LFunction chi s (Or.inl hs1)
  have hEq : Filter.EventuallyEq (nhds s) F (fun z => P z * DirichletCharacter.LFunction chi z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact hF z hz
  have hP : HasDerivAt P (dirichletMultiplicityPoleOrder chi : Complex) s := by
    by_cases hp : chi = 1
    case pos =>
      have hid : HasDerivAt (fun z : Complex => z) 1 s := hasDerivAt_id s
      simpa [P, dirichletMultiplicityPoleOrder, hp] using hid.sub_const (1 : Complex)
    case neg =>
      simpa [P, dirichletMultiplicityPoleOrder, hp] using hasDerivAt_const s (1 : Complex)
  have hP0 : Not (P s = 0) := by
    by_cases hp : chi = 1
    case pos => simpa [P, hp] using sub_ne_zero.mpr hs1
    case neg => simp [P, hp]
  have hquot : logDeriv P s = (dirichletMultiplicityPoleOrder chi : Complex) / (s - 1) := by
    rw [logDeriv_apply, hP.deriv]
    by_cases hp : chi = 1 <;> simp [P, dirichletMultiplicityPoleOrder, hp]
  rw [(logDeriv_congr_nhds hEq).self_of_nhds, logDeriv_mul s hP0 hL0 hP.differentiableAt hL,
    hquot, logDeriv_dirichletLFunction_eq_primePowerSeries chi hs]
  simp only [sub_eq_add_neg]

local macro "dirichletPrincipalPoleCleared" : term => do
  pure (Lean.mkIdent (Lean.Name.str `DirichletCharacter
    ("LFunctionTrivChar" ++ String.ofList [Char.ofNat 8321])))

local macro "dirichletPrincipalPoleCleared_differentiable" : term => do
  pure (Lean.mkIdent (Lean.Name.str `DirichletCharacter
    ("differentiable_LFunctionTrivChar" ++ String.ofList [Char.ofNat 8321])))

local macro "dirichletPrincipalPoleCleared_ne_zero_at_one" : term => do
  pure (Lean.mkIdent (Lean.Name.str `DirichletCharacter
    ("LFunctionTrivChar" ++ String.ofList [Char.ofNat 8321] ++ "_apply_one_ne_zero")))

/-- The actual Dirichlet L-function, with the principal pole removed. -/
def dirichletPoleClearedFactor {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    Complex -> Complex :=
  if chi = 1 then dirichletPrincipalPoleCleared N else DirichletCharacter.LFunction chi

theorem differentiable_dirichletPoleClearedFactor {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) :
    Differentiable Complex (dirichletPoleClearedFactor chi) := by
  by_cases hc : chi = 1
  case pos =>
    simpa only [dirichletPoleClearedFactor, if_pos hc] using
      dirichletPrincipalPoleCleared_differentiable N
  case neg =>
    simpa only [dirichletPoleClearedFactor, if_neg hc] using
      DirichletCharacter.differentiable_LFunction hc

theorem dirichletPoleClearedFactor_eq_off_pole {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) {s : Complex} (hs : Not (s = 1)) :
    dirichletPoleClearedFactor chi s =
      (if chi = 1 then s - 1 else 1) * DirichletCharacter.LFunction chi s := by
  by_cases hc : chi = 1
  case pos =>
    subst chi
    simp only [dirichletPoleClearedFactor, if_true]
    exact Function.update_of_ne hs _ _
  case neg =>
    simp [dirichletPoleClearedFactor, hc]

theorem dirichletPoleClearedFactor_ne_zero_of_one_le_re {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) {s : Complex} (hs : 1 <= s.re) :
    Not (dirichletPoleClearedFactor chi s = 0) := by
  by_cases hs1 : s = 1
  case pos =>
    subst s
    by_cases hc : chi = 1
    case pos =>
      simpa only [dirichletPoleClearedFactor, if_pos hc] using
        dirichletPrincipalPoleCleared_ne_zero_at_one N
    case neg =>
      simpa only [dirichletPoleClearedFactor, if_neg hc] using
        DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hc) hs
  case neg =>
    rw [dirichletPoleClearedFactor_eq_off_pole chi hs1]
    apply mul_ne_zero
    case ha =>
      by_cases hc : chi = 1
      case pos => simpa only [if_pos hc] using sub_ne_zero.mpr hs1
      case neg => simp [hc]
    case hb =>
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inr hs1) hs

/-- Dirichlet GRH for a character places every zero of its entire
pole-cleared factor to the left of or on the critical line. -/
theorem dirichletPoleClearedFactor_zero_re_le_half {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N)
    (hRH : forall s : Complex, 0 < s.re -> s.re < 1 ->
      DirichletCharacter.LFunction chi s = 0 -> s.re = 1 / 2)
    {s : Complex} (hZero : dirichletPoleClearedFactor chi s = 0) : s.re <= 1 / 2 := by
  by_contra h
  have hhalf : 1 / 2 < s.re := lt_of_not_ge h
  have hs : s.re < 1 := lt_of_not_ge
    (fun hs => dirichletPoleClearedFactor_ne_zero_of_one_le_re chi hs hZero)
  have hs1 : Not (s = 1) := by
    intro e
    rw [e, Complex.one_re] at hs
    exact lt_irrefl _ hs
  rw [dirichletPoleClearedFactor_eq_off_pole chi hs1] at hZero
  have hP : Not ((if chi = 1 then s - 1 else 1) = 0) := by
    by_cases hc : chi = 1
    case pos => simpa only [if_pos hc] using sub_ne_zero.mpr hs1
    case neg => simp only [if_neg hc, one_ne_zero, not_false_eq_true]
  have hL := (mul_eq_zero.mp hZero).resolve_left hP
  have hLine := hRH s (by linarith only [hhalf]) hs hL
  rw [hLine] at hhalf
  exact (lt_irrefl _) hhalf

/-- Removing the principal pole preserves ordinary zero orders in the strip. -/
theorem analyticOrderNatAt_dirichletPoleClearedFactor_eq {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) {s : Complex} (hs : Not (s = 1)) :
    analyticOrderNatAt (dirichletPoleClearedFactor chi) s =
      analyticOrderNatAt (DirichletCharacter.LFunction chi) s := by
  let P (w : Complex) := if chi = 1 then w - 1 else 1
  have hOpen : IsOpen {w : Complex | Not (w = 1)} := isOpen_compl_singleton
  have hEq : Filter.EventuallyEq (nhds s) (dirichletPoleClearedFactor chi)
      (P * DirichletCharacter.LFunction chi) := by
    filter_upwards [hOpen.mem_nhds hs] with w hw
    exact dirichletPoleClearedFactor_eq_off_pole chi hw
  have hP : AnalyticAt Complex P s := by
    by_cases hc : chi = 1
    case pos =>
      have hD : Differentiable Complex (fun w : Complex => w - 1) :=
        differentiable_id.sub_const 1
      simpa only [P, if_pos hc] using hD.analyticAt s
    case neg =>
      simp only [P, if_neg hc]
      exact analyticAt_const
  have hP0 : Not (P s = 0) := by
    by_cases hc : chi = 1
    case pos => simpa only [P, if_pos hc] using sub_ne_zero.mpr hs
    case neg => simp [P, hc]
  have hD : DifferentiableOn Complex (DirichletCharacter.LFunction chi) {w : Complex | Not (w = 1)} :=
    fun w hw => (DirichletCharacter.differentiableAt_LFunction chi w (Or.inl hw)).differentiableWithinAt
  have hL : AnalyticAt Complex (DirichletCharacter.LFunction chi) s :=
    ((Complex.analyticOnNhd_iff_differentiableOn hOpen).2 hD) s hs
  have hOrd : analyticOrderAt P s = 0 := hP.analyticOrderAt_eq_zero.mpr hP0
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hEq, analyticOrderAt_mul hP hL, hOrd, zero_add]

theorem dirichletPoleClearedFactor_logDeriv {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re) :
    logDeriv (dirichletPoleClearedFactor chi) s =
      (dirichletMultiplicityPoleOrder chi : Complex) / (s - 1) -
      tsum (fun n => dirichletPrimePowerCoefficient chi n *
        (riemannPrimePowerNorm n : Complex) ^ (-s)) := by
  apply logDeriv_dirichletPoleCleared_eq_primePowerSeries chi _ ?_ hs
  intro z hz
  apply dirichletPoleClearedFactor_eq_off_pole chi
  intro h
  rw [h, Complex.one_re] at hz
  exact lt_irrefl _ hz

local macro "realArchGamma" : term => do
  pure (Lean.mkIdent (Lean.Name.str `Complex ("Gamma" ++ String.ofList [Char.ofNat 8477])))

private def hurwitzEvenClearedNumerator (a : UnitAddCircle) (s : Complex) : Complex :=
  s * (s - 1) * completedEvenPoleFree a s -
    (s - 1) * (if a = 0 then 1 else 0) + s

private def hurwitzDoubleCleared (a : UnitAddCircle) (s : Complex) : Complex :=
  hurwitzEvenClearedNumerator a s * Inv.inv (realArchGamma s) +
    s * (s - 1) * HurwitzZeta.completedHurwitzZetaOdd a s * Inv.inv (realArchGamma (s + 1))

private theorem hurwitzDoubleCleared_entireOrderOne (a : UnitAddCircle) :
    EntireOfOrderAtMost 1 (hurwitzDoubleCleared a) := by
  let d : Complex := if a = 0 then 1 else 0
  have hA : EntireOfOrderAtMost 1 (fun s : Complex => s - 1) :=
    entireOrderOne_sub entireOrderOne_id (entireOrderOne_const 1)
  have hP : EntireOfOrderAtMost 1 (fun s : Complex => s * (s - 1)) :=
    entireOrderOne_mul entireOrderOne_id hA
  have hEven : EntireOfOrderAtMost 1 (hurwitzEvenClearedNumerator a) :=
    entireOrderOne_add (entireOrderOne_sub
      (entireOrderOne_mul hP (completedHurwitzEven_poleFree_entireOrderOne a))
      (entireOrderOne_mul hA (entireOrderOne_const d))) entireOrderOne_id
  have hGamma : EntireOfOrderAtMost 1 (fun s : Complex => Inv.inv (realArchGamma s)) :=
    entireOrderOne_inv_LReal
  have hShiftedGamma : EntireOfOrderAtMost 1 (fun s : Complex => Inv.inv (realArchGamma (s + 1))) := by
    simpa only [one_mul] using entireOrderOne_affine hGamma 1 1
  exact entireOrderOne_add (entireOrderOne_mul hEven hGamma)
    (entireOrderOne_mul (entireOrderOne_mul hP (completedHurwitzOdd_entireOrderOne a)) hShiftedGamma)

private theorem hurwitzDoubleCleared_eq (a : UnitAddCircle) {s : Complex} (hs : 1 < s.re) :
    hurwitzDoubleCleared a s = s * (s - 1) * HurwitzZeta.hurwitzZeta a s := by
  have hs0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs1 : Not (s = 1) := by
    intro e
    rw [e, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hExpansion : hurwitzEvenClearedNumerator a s =
      s * (s - 1) * HurwitzZeta.completedHurwitzZetaEven a s := by
    rw [hurwitzEvenClearedNumerator, HurwitzZeta.completedHurwitzZetaEven_eq]
    field_simp [hs0, sub_ne_zero.mpr hs1, sub_ne_zero.mpr (Ne.symm hs1)]
    ring
  rw [hurwitzDoubleCleared, hExpansion, HurwitzZeta.hurwitzZeta,
    HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs0), HurwitzZeta.hurwitzZetaOdd]
  simp only [div_eq_mul_inv]
  ring

private def dirichletDoubleCleared {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (s : Complex) : Complex :=
  (N : Complex) ^ (-s) * Finset.univ.sum
    (fun j : ZMod N => chi j * hurwitzDoubleCleared (ZMod.toAddCircle j) s)

private theorem dirichletDoubleCleared_entireOrderOne {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) :
    EntireOfOrderAtMost 1 (dirichletDoubleCleared chi) := by
  have hN : 0 < (N : Real) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hCpow : EntireOfOrderAtMost 1 (fun s : Complex => (N : Complex) ^ (-s)) := by
    simpa only [Complex.ofReal_natCast, neg_one_mul] using entireOrderOne_const_cpow hN (-1)
  exact entireOrderOne_mul hCpow (entireOrderOne_finsetSum Finset.univ
    (fun j : ZMod N => fun s => chi j * hurwitzDoubleCleared (ZMod.toAddCircle j) s)
    (fun j _ => entireOrderOne_mul (entireOrderOne_const (chi j)) (hurwitzDoubleCleared_entireOrderOne _)))

private theorem dirichletDoubleCleared_eq {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re) :
    dirichletDoubleCleared chi s = s * (s - 1) * DirichletCharacter.LFunction chi s := by
  let A := Finset.univ.sum
    (fun j : ZMod N => chi j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s)
  have hSum : Finset.univ.sum
      (fun j : ZMod N => chi j * hurwitzDoubleCleared (ZMod.toAddCircle j) s) =
      s * (s - 1) * A := by
    unfold A
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hurwitzDoubleCleared_eq (ZMod.toAddCircle j) hs]
    ring
  unfold dirichletDoubleCleared
  rw [hSum]
  change (N : Complex) ^ (-s) * (s * (s - 1) * A) = s * (s - 1) * ((N : Complex) ^ (-s) * A)
  ring

/-- Every Dirichlet L-function, including imprimitive characters, has
order at most one after clearing its principal pole. -/
theorem dirichletPoleClearedFactor_entireOrderOne {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) :
    EntireOfOrderAtMost 1 (dirichletPoleClearedFactor chi) := by
  let m : Nat := if chi = 1 then 0 else 1
  let F := dirichletPoleClearedFactor chi
  let H (s : Complex) := (s - 1) ^ m * F s
  have hF : Differentiable Complex F := differentiable_dirichletPoleClearedFactor chi
  have hSub : Differentiable Complex (fun s : Complex => s - 1) :=
    differentiable_id.sub_const 1
  have hH : Differentiable Complex H := (hSub.pow m).mul hF
  have hProd : Differentiable Complex (fun s : Complex => s ^ (1 : Nat) * H s) :=
    (differentiable_id.pow 1).mul hH
  have hDbl := dirichletDoubleCleared_entireOrderOne chi
  have hNear : Filter.EventuallyEq (nhds (2 : Complex)) (fun s : Complex => s ^ (1 : Nat) * H s)
      (dirichletDoubleCleared chi) := by
    have hTwo : 1 < (2 : Complex).re := by norm_num
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hTwo] with s hs
    have hs1 : Not (s = 1) := by
      intro e
      rw [e, Complex.one_re] at hs
      exact lt_irrefl _ hs
    have hEq : H s = (s - 1) * DirichletCharacter.LFunction chi s := by
      change (s - 1) ^ m * dirichletPoleClearedFactor chi s = _
      rw [dirichletPoleClearedFactor_eq_off_pole chi hs1]
      by_cases hc : chi = 1 <;> simp [m, hc]
    rw [pow_one, hEq, dirichletDoubleCleared_eq chi hs, mul_assoc]
  have hEqual : AnalyticOnNhd Complex (fun s : Complex => s ^ (1 : Nat) * H s)
      (univ : Set Complex) := fun s _ => hProd.analyticAt s
  have hDblAn : AnalyticOnNhd Complex (dirichletDoubleCleared chi)
      (univ : Set Complex) := fun s _ => hDbl.differentiable.analyticAt s
  have hAll := hEqual.eq_of_eventuallyEq hDblAn hNear
  have hHOrder : EntireOfOrderAtMost 1 H :=
    entireOrderOne_of_mul_pow hH hDbl 1 (fun s => congrFun hAll s)
  have hHShift : EntireOfOrderAtMost 1 (fun s => H (s + 1)) := by
    simpa only [one_mul] using entireOrderOne_affine hHOrder 1 1
  have hPlus : Differentiable Complex (fun s : Complex => s + 1) :=
    differentiable_id.add_const 1
  have hFShift : EntireOfOrderAtMost 1 (fun s => F (s + 1)) := by
    apply entireOrderOne_of_mul_pow (hF.comp hPlus) hHShift m
    intro s
    simp only [H, add_sub_cancel_right, Function.comp_def]
  simpa [F, sub_eq_add_neg] using entireOrderOne_affine hFShift 1 (-1)

end Robin1984.GRH
