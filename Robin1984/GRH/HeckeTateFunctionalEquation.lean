import Robin1984.GRH.HeckeTateMellinReflection

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's thesis on Hecke L-functions and the Dedekind zeta specialization.
- Formalization note: Constructs the standard rank-one completions and proves their familywise triangular criterion, including all imaginary norm twists.
- PROVENANCE-END
-/

/-!
# The standard Hecke functional equation and triangular criterion

The full Tate Mellin integral gives the conductor-normalized completion.
Its reflected conjugate identity has a unit scalar, and the two positive
tails bound the completion on the middle strip. The triangular criterion
applies to the paired completion. Characters trivial on norm-one classes
are norm twists, whose pole-cleared completions are translated Dedekind
completions.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open MeasureTheory

/-- The conductor-centered logarithmic Mellin integral, weighted by the
character on the logarithmic norm section. -/
def heckeTateLogCharacterMellin
    (G W : Real -> Complex) (beta : Real) (s : Complex) : Complex :=
  Complex.exp (-s * (beta : Complex) / 2) *
    integral volume (fun t : Real => Complex.exp (s * (t : Complex)) * W t * G t)

private theorem tateLogCharacter_weight
    (W : Real -> Complex) (tau : Real)
    (hW : forall t, W t = Complex.exp (((tau * t : Real) : Complex) * Complex.I))
    (s : Complex) (t : Real) :
    Complex.exp (s * (t : Complex)) * W t =
      Complex.exp ((s + (tau : Complex) * Complex.I) * (t : Complex)) := by
  rw [hW, <- Complex.exp_add, Complex.ofReal_mul]
  congr 1
  ring

/-- The character on the norm section shifts the Mellin argument by its
purely imaginary frequency, with the conductor factor kept at s. -/
theorem heckeTateLogCharacterMellin_eq_centered
    (G W : Real -> Complex) (beta tau : Real)
    (hW : forall t, W t = Complex.exp (((tau * t : Real) : Complex) * Complex.I))
    (s : Complex) :
    heckeTateLogCharacterMellin G W beta s =
      Complex.exp ((tau : Complex) * Complex.I * (beta : Complex) / 2) *
        heckeTateCenteredMellin G beta (s + (tau : Complex) * Complex.I) := by
  unfold heckeTateLogCharacterMellin heckeTateCenteredMellin
  simp only [tateLogCharacter_weight W tau hW]
  have hExp : Complex.exp (-s * (beta : Complex) / 2) =
      Complex.exp ((tau : Complex) * Complex.I * (beta : Complex) / 2) *
      Complex.exp (-(s + (tau : Complex) * Complex.I) * (beta : Complex) / 2) := by
    rw [<- Complex.exp_add]
    congr 1
    ring
  rw [hExp, mul_assoc]

/-- Norm-section frequencies of opposite sign reflect the Mellin argument
and introduce the explicit conductor phase in the scalar. -/
theorem heckeTateLogCharacterMellin_reflect
    (A B W V : Real -> Complex) (beta tau : Real) (k : Complex)
    (hA : forall t, A t = k * (Real.exp (-t) : Complex) * B (beta - t))
    (hW : forall t, W t = Complex.exp (((tau * t : Real) : Complex) * Complex.I))
    (hV : forall t, V t = Complex.exp (((-tau * t : Real) : Complex) * Complex.I))
    (s : Complex) :
    heckeTateLogCharacterMellin A W beta s =
      (k * Complex.exp (-(beta : Complex) / 2 + (tau : Complex) * Complex.I * (beta : Complex))) *
        heckeTateLogCharacterMellin B V beta (1 - s) := by
  let a := (tau : Complex) * Complex.I * (beta : Complex) / 2
  let b := -(beta : Complex) / 2
  let u := s + (tau : Complex) * Complex.I
  let M := heckeTateCenteredMellin B beta (1 - u)
  have hUV : 1 - s + ((-tau : Real) : Complex) * Complex.I = 1 - u := by
    rw [Complex.ofReal_neg]
    unfold u
    ring
  have hPh : ((-tau : Real) : Complex) * Complex.I * (beta : Complex) / 2 = -a := by
    rw [Complex.ofReal_neg]
    unfold a
    ring
  rw [heckeTateLogCharacterMellin_eq_centered A W beta tau hW,
    heckeTateCenteredMellin_reflect A B beta k hA,
    heckeTateLogCharacterMellin_eq_centered B V beta (-tau) hV, hUV, hPh]
  change Complex.exp a * ((k * Complex.exp b) * M) =
    (k * Complex.exp (b + (tau : Complex) * Complex.I * (beta : Complex))) *
      (Complex.exp (-a) * M)
  have hPhase : b + (tau : Complex) * Complex.I * (beta : Complex) = b + 2 * a := by
    unfold a
    ring
  rw [hPhase]
  calc
    _ = (k * (Complex.exp a * Complex.exp b)) * M := by ring
    _ = (k * Complex.exp (a + b)) * M := by rw [Complex.exp_add]
    _ = (k * (Complex.exp (b + 2 * a) * Complex.exp (-a))) * M := by
      rw [<- Complex.exp_add, show b + 2 * a + -a = a + b by ring]
    _ = _ := by ring

/-- Conjugating both weights conjugates the shifted Mellin completion. -/
theorem heckeTateLogCharacterMellin_conj
    (A B W V : Real -> Complex) (beta : Real)
    (hB : forall t, B t = starRingEnd Complex (A t))
    (hV : forall t, V t = starRingEnd Complex (W t))
    (s : Complex) :
    heckeTateLogCharacterMellin B V beta (starRingEnd Complex s) =
      starRingEnd Complex (heckeTateLogCharacterMellin A W beta s) := by
  let C := starRingEnd Complex
  let F (t : Real) := Complex.exp (s * (t : Complex)) * W t * A t
  have hI : integral volume (fun t : Real => C (F t)) = C (integral volume F) :=
    integral_conj
  have hP : C (-s * (beta : Complex) / 2) = -(C s) * (beta : Complex) / 2 := by
    have hTwo : starRingEnd Complex (2 : Complex) = 2 := map_ofNat _ _
    simp [C, div_eq_mul_inv, map_neg, map_mul, Complex.conj_ofReal, hTwo]
  unfold heckeTateLogCharacterMellin
  change _ = C (Complex.exp (-s * (beta : Complex) / 2) * integral volume F)
  rw [map_mul, <- hI]
  have hE : C (Complex.exp (-s * (beta : Complex) / 2)) =
      Complex.exp (-(C s) * (beta : Complex) / 2) := by
    rw [<- Complex.exp_conj, hP]
  rw [hE]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [hB, hV, show F t = _ from rfl, map_mul, map_mul, <- Complex.exp_conj,
    map_mul, Complex.conj_ofReal]

/-- A reflected conjugate pair with one nonzero value has a functional
equation scalar of absolute value one. -/
theorem norm_eq_one_of_conjugate_mellin_reflection
    (F G : Complex -> Complex) (k : Complex)
    (hConj : forall s, G (starRingEnd Complex s) = starRingEnd Complex (F s))
    (hFE : forall s, F s = k * G (1 - s)) (s0 : Complex) (hs0 : Not (F s0 = 0)) :
    norm k = 1 := by
  let j (s : Complex) := 1 - starRingEnd Complex s
  have hj (s : Complex) : starRingEnd Complex (j s) = 1 - s := by
    rw [show j s = _ from rfl, map_sub, map_one, starRingEnd_apply, starRingEnd_apply, star_star]
  have hJJ (s : Complex) : j (j s) = s := by
    change 1 - starRingEnd Complex (j s) = s
    rw [hj, sub_sub_cancel]
  have hNorm (s : Complex) : norm (F s) = norm k * norm (F (j s)) := by
    have h := congrArg norm (hFE s)
    have hG : G (1 - s) = starRingEnd Complex (F (j s)) := by
      have hg := hConj (j s)
      rw [hj] at hg
      exact hg
    rw [hG, norm_mul, starRingEnd_apply, norm_star] at h
    exact h
  have h0 := hNorm s0
  have h1 := hNorm (j s0)
  rw [hJJ] at h1
  have hProd : norm k ^ 2 * norm (F s0) = norm (F s0) := by
    rw [pow_two, mul_assoc, <- h1, <- h0]
  have hPos : 0 < norm (F s0) := norm_pos_iff.mpr hs0
  have hSq := (eq_div_iff hPos.ne').mpr hProd
  rw [div_self hPos.ne'] at hSq
  have hFact : (norm k - 1) * (norm k + 1) = 0 := by nlinarith only [hSq]
  have hPos1 : Not (norm k + 1 = 0) := (add_pos_of_nonneg_of_pos (norm_nonneg k) zero_lt_one).ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hFact).resolve_right hPos1)

open IsDedekindDomain NumberField
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev C (K : Type*) [Field K] [NumberField K] := heckeNormOneIdeleClass K

private abbrev F (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev Mix (K : Type*) [Field K] := mixedEmbedding.mixedSpace K

/-- The standard conductor and Gamma factors times the Hecke Euler product
on its half-plane of absolute convergence. -/
def heckeTateStandardCompletedEulerValue (chi : UnitaryHeckeCharacter K) (s : Complex) : Complex :=
  standardCompletionFactor (heckeArithmeticConductor chi) 0
    (fun v : {w : InfinitePlace K // w.IsReal} => realInfiniteHeckeShift chi v.property)
    (fun v : {w : InfinitePlace K // w.IsComplex} => complexInfiniteHeckeShift chi v.property) s *
      heckeEulerL K chi s

theorem heckeTateStandardCompletedEulerValue_ne_zero
    (chi : UnitaryHeckeCharacter K) (s : Complex) (hs : 1 < s.re) :
    Not (heckeTateStandardCompletedEulerValue chi s = 0) := by
  have h := standardCompletionFactor_ne_zero (heckeArithmeticConductor_pos chi) 0
    (fun v : {w : InfinitePlace K // w.IsReal} => realInfiniteHeckeShift chi v.property)
    (fun v : {w : InfinitePlace K // w.IsComplex} => complexInfiniteHeckeShift chi v.property)
    (fun v => (by norm_num : -(1 : Real) / 2 < 0).trans_le (realInfiniteHeckeShift_re_nonneg chi v.property))
    (fun v => (by norm_num : -(1 : Real) / 2 < 0).trans_le (complexInfiniteHeckeShift_re_nonneg chi v.property))
    ((by norm_num : (1 : Real) / 2 < 1).trans hs)
  exact mul_ne_zero h (Complex.exp_ne_zero _)

private theorem heckeTateLogCharacterMellin_eq_two_tails
    [MeasurableSpace (C K)] [BorelSpace (C K)]
    [MeasurableSpace (F K)] [BorelSpace (F K)]
    (mu : Measure (C K)) [IsFiniteMeasure mu] [mu.IsMulLeftInvariant]
    (hInv : MeasurePreserving Inv.inv mu mu)
    (chi : UnitaryHeckeCharacter K) (z : C K)
    (hz : Not (heckeNormOneClassCharacter chi z = 1)) (f : SchwartzMap (Mix K) Complex)
    (beta tau : Real)
    (hTau : forall t : Real, (chi.val (heckeIdelicExpSection K t) : Complex) =
      Complex.exp (((tau * t : Real) : Complex) * Complex.I))
    (s : Complex) :
    heckeTateLogCharacterMellin
      (heckeTateCharacterThetaAverage mu chi f (heckeFiniteAdditiveTateTest chi))
      (fun t => (chi.val (heckeIdelicExpSection K t) : Complex)) beta s =
      Complex.exp (-s * (beta : Complex) / 2) *
        (heckeTateThetaMellinTail mu f (heckeFiniteAdditiveTateTest chi) chi
            (s + (tau : Complex) * Complex.I) +
          heckeTateThetaMellinTail mu (heckeTateDualInfiniteTest f) (heckeTateDualFiniteTest chi)
            (unitaryHeckeInverse chi) (1 - (s + (tau : Complex) * Complex.I))) := by
  unfold heckeTateLogCharacterMellin
  have hWeight := tateLogCharacter_weight
    (fun t : Real => (chi.val (heckeIdelicExpSection K t) : Complex)) tau hTau s
  simp only [hWeight]
  rw [integral_heckeTateCharacterThetaAverage_eq_two_mellinTails mu hInv chi z hz f]

/-- The absolute theta moment at the right endpoint controls the whole
left half-plane of the positive Mellin tail. -/
theorem norm_heckeTateThetaMellinTail_le_moment
    [MeasurableSpace (C K)] [BorelSpace (C K)]
    (mu : Measure (C K)) [IsFiniteMeasure mu]
    (f : SchwartzMap (Mix K) Complex)
    (T : F K -> Complex) (hT : Continuous T)
    (S : Set (F K)) (hS : IsCompact S)
    (hST : forall z, Not (Membership.mem S z) -> T z = 0)
    (B : Real) (hB : 0 <= B) (hBT : forall z, norm (T z) <= B)
    (chi : UnitaryHeckeCharacter K) (a : Real) (s : Complex) (hs : s.re <= a) :
    norm (heckeTateThetaMellinTail mu f T chi s) <=
      integral (heckePositiveThetaMeasure mu) (fun p : Prod Real (C K) =>
        norm (heckeTateThetaNormOneClass f T p.1 p.2) * (Real.exp p.1) ^ a) := by
  let M := heckePositiveThetaMeasure mu
  let q := heckeNormOneClassCharacter chi
  let D (p : Prod Real (C K)) := (q p.2 : Complex) * heckeTateThetaNormOneClass f T p.1 p.2
  let r (p : Prod Real (C K)) := Real.exp p.1
  have hr : Continuous r := Real.continuous_exp.comp continuous_fst
  have hq : Continuous (fun p : Prod Real (C K) => (q p.2 : Complex)) :=
    continuous_subtype_val.comp (q.continuous.comp continuous_snd)
  have hD : Continuous D := hq.mul (continuous_heckeTateThetaNormOneClass_joint f T hT S hS hST B hB hBT)
  have hPos : Filter.Eventually (fun t : Real => 0 < t)
      (ae (volume.restrict (Set.Ioi (0 : Real)))) := ae_restrict_mem measurableSet_Ioi
  have hP : Filter.Eventually (fun p : Prod Real (C K) => 0 < p.1) (ae M) := by
    change Filter.Eventually (fun p : Prod Real (C K) => 0 < p.1)
      (ae ((volume.restrict (Set.Ioi (0 : Real))).prod mu))
    have hSet : MeasurableSet (Set.ofPred (fun p : Prod Real (C K) => 0 < p.1)) :=
      measurableSet_Ioi.preimage measurable_fst
    exact (Measure.ae_prod_iff_ae_ae hSet).mpr
      (hPos.mono (fun _ ht => Filter.Eventually.of_forall (fun _ => ht)))
  have hRadius : Filter.Eventually (fun p => 1 <= r p) (ae M) :=
    hP.mono (fun p hp => Real.one_le_exp_iff.mpr hp.le)
  have hEq : (fun p => norm (D p) * r p ^ a) =
      (fun p : Prod Real (C K) => norm (heckeTateThetaNormOneClass f T p.1 p.2) * (Real.exp p.1) ^ a) := by
    funext p
    unfold D r
    rw [norm_mul, Circle.norm_coe, one_mul]
  have hWeight : Integrable (fun p => norm (D p) * r p ^ a) M := by
    rw [hEq]
    exact integrable_heckeTateThetaNormOneClass_expMoment mu f T hT S hS hST B hB hBT a
  have h := norm_heckeMellinTail_le M D r hD.aestronglyMeasurable hr.measurable.aemeasurable
    hRadius hWeight hs
  rw [hEq] at h
  exact h

/-- On the middle strip, a positive conductor contributes a uniformly
bounded complex exponential in the logarithmic coordinate. -/
theorem norm_tateConductorExp_le_of_strip
    (beta : Real) (s : Complex) (hL : -2 <= s.re) (hR : s.re <= 3) :
    norm (Complex.exp (-s * (beta : Complex) / 2)) <= Real.exp (3 * abs beta / 2) := by
  have hDiv (w : Complex) : (w / 2).re = w.re / 2 := by
    simp [div_eq_mul_inv, Complex.mul_re, Complex.inv_re]
  have hReal : (-s * (beta : Complex) / 2).re = -s.re * beta / 2 := by
    rw [hDiv, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hS : abs s.re <= 3 := abs_le.mpr (And.intro (by linarith only [hL]) hR)
  rw [Complex.norm_exp, hReal]
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    -s.re * beta <= abs (-s.re * beta) := le_abs_self _
    _ = abs s.re * abs beta := by rw [abs_mul, abs_neg]
    _ <= _ := mul_le_mul_of_nonneg_right hS (abs_nonneg _)

private theorem differentiable_and_stripBound_heckeTateLogCharacterMellin
    [MeasurableSpace (C K)] [BorelSpace (C K)]
    [MeasurableSpace (F K)] [BorelSpace (F K)]
    (mu : Measure (C K)) [IsFiniteMeasure mu] [mu.IsMulLeftInvariant]
    (hInv : MeasurePreserving Inv.inv mu mu)
    (chi : UnitaryHeckeCharacter K) (z : C K)
    (hz : Not (heckeNormOneClassCharacter chi z = 1)) (f : SchwartzMap (Mix K) Complex)
    (beta tau : Real)
    (hTau : forall t : Real, (chi.val (heckeIdelicExpSection K t) : Complex) =
      Complex.exp (((tau * t : Real) : Complex) * Complex.I)) :
    let L := heckeTateLogCharacterMellin
      (heckeTateCharacterThetaAverage mu chi f (heckeFiniteAdditiveTateTest chi))
      (fun t => (chi.val (heckeIdelicExpSection K t) : Complex)) beta
    And (Differentiable Complex L)
      (exists B : Real, forall s, -2 <= s.re -> s.re <= 3 -> norm (L s) <= B) := by
  let T := heckeFiniteAdditiveTateTest chi
  let TD := heckeTateDualFiniteTest chi
  let U := heckeIntegralFiniteAdeles (K := K)
  have hTzero (y : F K) (hy : Not (Membership.mem (U : Set (F K)) y)) : T y = 0 := by
    change Not (Membership.mem U y) at hy
    rw [show T = heckeFiniteAdditiveTateTest chi from rfl, heckeFiniteAdditiveTateTest, if_neg hy]
  have hPrim := differentiable_heckeTateThetaMellinTail mu f T
    (continuous_heckeFiniteAdditiveTateTest chi) (U : Set (F K))
    isCompact_integralFiniteAdeles hTzero 1 zero_le_one (norm_heckeFiniteAdditiveTateTest_le_one chi) chi
  choose V B hVB using heckeTateDualFiniteTest_support_and_bound chi
  have hTDC : Continuous TD := by
    change Continuous (fun y : F K =>
      Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
        heckeFiniteFourierIntegral heckeFiniteAdeleHaar (heckeFiniteAdditiveTateTest chi) (-y))
    exact continuous_const.mul
      ((continuous_heckeFiniteFourierIntegral_TateTest heckeFiniteAdeleHaar chi).comp continuous_neg)
  have hDual := differentiable_heckeTateThetaMellinTail mu (heckeTateDualInfiniteTest f)
    TD hTDC V hVB.1 hVB.2.2.1 B hVB.2.1 hVB.2.2.2 (unitaryHeckeInverse chi)
  let u (s : Complex) := s + (tau : Complex) * Complex.I
  let v (s : Complex) := 1 - u s
  have hU : Differentiable Complex u := differentiable_id.add (differentiable_const _)
  have hV : Differentiable Complex v := (differentiable_const (1 : Complex)).sub hU
  have hPref : Differentiable Complex (fun s : Complex => Complex.exp (-s * (beta : Complex) / 2)) :=
    Complex.differentiable_exp.comp ((differentiable_id.neg.mul (differentiable_const _)).div_const _)
  have hTails := heckeTateLogCharacterMellin_eq_two_tails mu hInv chi z hz f beta tau hTau
  refine And.intro ?_ ?_
  . rw [funext hTails]
    exact hPref.mul ((hPrim.comp hU).add (hDual.comp hV))
  . let M := heckePositiveThetaMeasure mu
    let B1 := integral M (fun p : Prod Real (C K) =>
      norm (heckeTateThetaNormOneClass f T p.1 p.2) * (Real.exp p.1) ^ (3 : Real))
    let B2 := integral M (fun p : Prod Real (C K) =>
      norm (heckeTateThetaNormOneClass (heckeTateDualInfiniteTest f) TD p.1 p.2) *
        (Real.exp p.1) ^ (3 : Real))
    refine Exists.intro (Real.exp (3 * abs beta / 2) * (B1 + B2)) ?_
    intro s hsL hsR
    have hRe : (u s).re = s.re := by simp [u, Complex.add_re, Complex.mul_re]
    have hReU : (u s).re <= 3 := hRe.trans_le hsR
    have hReV : (v s).re <= 3 := by
      change (1 - u s).re <= 3
      rw [Complex.sub_re, Complex.one_re, hRe]
      linarith only [hsL]
    have hA : norm (heckeTateThetaMellinTail mu f T chi (u s)) <= B1 :=
      norm_heckeTateThetaMellinTail_le_moment mu f T (continuous_heckeFiniteAdditiveTateTest chi)
        (U : Set (F K)) isCompact_integralFiniteAdeles hTzero 1 zero_le_one
        (norm_heckeFiniteAdditiveTateTest_le_one chi) chi 3 (u s) hReU
    have hB : norm (heckeTateThetaMellinTail mu (heckeTateDualInfiniteTest f) TD
        (unitaryHeckeInverse chi) (v s)) <= B2 :=
      norm_heckeTateThetaMellinTail_le_moment mu (heckeTateDualInfiniteTest f) TD hTDC
        V hVB.1 hVB.2.2.1 B hVB.2.1 hVB.2.2.2 (unitaryHeckeInverse chi) 3 (v s) hReV
    rw [hTails s, norm_mul]
    apply mul_le_mul (norm_tateConductorExp_le_of_strip beta s hsL hsR)
    . exact (norm_add_le _ _).trans (add_le_add hA hB)
    . exact norm_nonneg _
    . exact (Real.exp_pos _).le

set_option maxHeartbeats 1400000 in
/-- The standard conductor-normalized completion of each unitary Hecke
character nontrivial on norm-one classes is entire and satisfies its
functional equation with the inverse character and a unit root factor. -/
theorem exists_heckeCompletedEulerFamily_functionalEquation
    (K : Type*) [Field K] [NumberField K] :
    exists L : UnitaryHeckeCharacter K -> Complex -> Complex,
      forall (chi : UnitaryHeckeCharacter K) (z : C K),
        Not (heckeNormOneClassCharacter chi z = 1) ->
        And (Differentiable Complex (L chi))
          (And (forall s : Complex, 1 < s.re -> L chi s = heckeTateStandardCompletedEulerValue chi s)
            (And (exists B : Real, forall s : Complex, -2 <= s.re -> s.re <= 3 -> norm (L chi s) <= B)
              (exists w : Complex, And (norm w = 1)
                (forall s : Complex, L (unitaryHeckeInverse chi) (1 - s) = w * L chi s)))) := by
  let : MeasurableSpace (Units (Mix K)) := borel _
  let : BorelSpace (Units (Mix K)) := BorelSpace.mk rfl
  let : MeasurableSpace (F K) := borel _
  let : BorelSpace (F K) := BorelSpace.mk rfl
  let : MeasurableSpace (Units (F K)) := borel _
  let : BorelSpace (Units (F K)) := BorelSpace.mk rfl
  let : MeasurableSpace (Units (AdeleRing (RingOfIntegers K) K)) := borel _
  let : BorelSpace (Units (AdeleRing (RingOfIntegers K) K)) := BorelSpace.mk rfl
  let : MeasurableSpace (heckeNormOneIdeles K) := borel _
  let : BorelSpace (heckeNormOneIdeles K) := BorelSpace.mk rfl
  let : MeasurableSpace (heckeIdeleClass K) := borel _
  let : BorelSpace (heckeIdeleClass K) := BorelSpace.mk rfl
  let : MeasurableSpace (C K) := borel _
  let : BorelSpace (C K) := BorelSpace.mk rfl
  let I := FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K
  let : MeasurableSpace (Units I) := Top.top
  let : MeasurableSingletonClass (Units I) := MeasurableSingletonClass.mk (fun _ => trivial)
  choose mu hMu using exists_heckeTateClassThetaEulerMeasure (K := K)
  let : IsFiniteMeasure mu := hMu.1
  let : mu.IsMulLeftInvariant := hMu.2.1
  have hInv := hMu.2.2.1
  choose f hf using hMu.2.2.2
  let A (xi : UnitaryHeckeCharacter K) :=
    heckeTateCharacterThetaAverage mu xi (f xi) (heckeFiniteAdditiveTateTest xi)
  let W (xi : UnitaryHeckeCharacter K) (t : Real) : Complex :=
    xi.val (heckeIdelicExpSection K t)
  let beta (xi : UnitaryHeckeCharacter K) := -(Real.log (heckeArithmeticConductor xi))
  let L (xi : UnitaryHeckeCharacter K) : Complex -> Complex :=
    heckeTateLogCharacterMellin (A xi) (W xi) (beta xi)
  refine Exists.intro L ?_
  intro chi z hz
  let opp := unitaryHeckeInverse chi
  choose tau hTau using exists_heckeTateClassZeta_mellinTail_shift chi
  have hW (t : Real) : W chi t = Complex.exp (((tau * t : Real) : Complex) * Complex.I) := hTau.1 t
  have hV (t : Real) : W opp t = Complex.exp (((-tau * t : Real) : Complex) * Complex.I) := by
    have hWI : W opp t = Inv.inv (W chi t) := Circle.coe_inv _
    rw [hWI, hW, <- Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hBeta : beta opp = beta chi := by
    change -(Real.log (heckeArithmeticConductor (unitaryHeckeInverse chi))) = _
    rw [heckeArithmeticConductor_inverse]
  have hEval (s : Complex) (hs : 1 < s.re) : L chi s = heckeTateStandardCompletedEulerValue chi s := by
    have hE := heckeTateLogCharacterMellin_eq_two_tails mu hInv chi z hz (f chi) (beta chi) tau hW s
    have hZ := integral_heckeTateClassZeta_eq_two_mellinTails_of_logCharacter
      mu hInv chi z hz (f chi) tau hW s hs
    have hP : (heckeArithmeticConductor chi : Complex) ^ (s / 2) =
        Complex.exp (-s * (beta chi : Complex) / 2) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr
        (heckeArithmeticConductor_pos chi).ne'), <- Complex.ofReal_log (heckeArithmeticConductor_pos chi).le]
      change Complex.exp ((Real.log (heckeArithmeticConductor chi) : Complex) * (s / 2)) =
        Complex.exp (-s * ((-(Real.log (heckeArithmeticConductor chi)) : Real) : Complex) / 2)
      rw [Complex.ofReal_neg]
      congr 1
      ring
    change heckeTateLogCharacterMellin (A chi) (W chi) (beta chi) s = _
    rw [hE, <- hZ, (hf chi).2 s hs]
    unfold heckeTateStandardCompletedEulerValue standardCompletionFactor
    rw [pow_zero, one_mul, hP]
    ring
  have hAnalytic :=
    differentiable_and_stripBound_heckeTateLogCharacterMellin mu hInv chi z hz (f chi) (beta chi) tau hW
  refine And.intro hAnalytic.1 (And.intro hEval (And.intro hAnalytic.2 ?_))
  have hd0 : Not (DedekindZeta.Theta.differentFractionalIdeal K = 0) := by
    change Not (((differentIdeal Int (RingOfIntegers K)) : I) = 0)
    exact FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  choose d hD using surjective_heckeFiniteIdeleIdealHom (K := K)
    (Units.mk0 (DedekindZeta.Theta.differentFractionalIdeal K) hd0)
  have hd : heckeFiniteIdeleFractionalIdeal d = DedekindZeta.Theta.differentFractionalIdeal K :=
    congrArg Units.val hD
  choose c hc using exists_heckeFiniteIdele_conductor chi
  choose k hR using heckeTateCharacterThetaAverage_canonical_reflect mu hInv chi z hz
    (f chi) (f opp) (hf chi).1 (hf opp).1 d c hd hc.1 hc.2
  rw [heckeFiniteIdeleNorm_different_mul_conductor chi d c hd hc.1, Real.log_inv] at hR
  let root := k * Complex.exp (-(beta chi : Complex) / 2 + (tau : Complex) * Complex.I * (beta chi : Complex))
  have hFE (s : Complex) : L chi s = root * L opp (1 - s) := by
    change heckeTateLogCharacterMellin (A chi) (W chi) (beta chi) s =
      root * heckeTateLogCharacterMellin (A opp) (W opp) (beta opp) (1 - s)
    rw [hBeta]
    exact heckeTateLogCharacterMellin_reflect (A chi) (A opp) (W chi) (W opp) (beta chi)
      tau k hR hW hV s
  have hConj (s : Complex) : L opp (starRingEnd Complex s) = starRingEnd Complex (L chi s) := by
    have hA (t : Real) : A opp t = starRingEnd Complex (A chi t) :=
      heckeTateCharacterThetaAverage_inverse_conj mu chi (f chi) (f opp) (hf chi).1 (hf opp).1 t
    have hWC (t : Real) : W opp t = starRingEnd Complex (W chi t) := Circle.coe_inv_eq_conj _
    change heckeTateLogCharacterMellin (A opp) (W opp) (beta opp) (starRingEnd Complex s) = _
    rw [hBeta]
    exact heckeTateLogCharacterMellin_conj (A chi) (A opp) (W chi) (W opp) (beta chi) hA hWC s
  have h2 : 1 < (2 : Complex).re := by norm_num
  have hNZ : Not (L chi (2 : Complex) = 0) := by
    rw [hEval 2 h2]
    exact heckeTateStandardCompletedEulerValue_ne_zero chi 2 h2
  have hUnit := norm_eq_one_of_conjugate_mellin_reflection (L chi) (L opp) root
    hConj hFE (2 : Complex) hNZ
  have hRoot : Not (root = 0) := by
    intro h
    rw [h, norm_zero] at hUnit
    exact zero_ne_one hUnit
  refine Exists.intro (Inv.inv root) (And.intro (by rw [norm_inv, hUnit, inv_one]) ?_)
  intro s
  change L opp (1 - s) = Inv.inv root * L chi s
  rw [hFE s, <- mul_assoc]
  simp [hRoot]

/-- The product of the standard conductor and Gamma completed Euler values
equals the paired completion factor times the two Euler products. -/
theorem heckeTateStandardCompletedEulerValue_mul_inverse
    (chi : UnitaryHeckeCharacter K) (s : Complex) :
    heckeTateStandardCompletedEulerValue chi s *
        heckeTateStandardCompletedEulerValue (unitaryHeckeInverse chi) s =
      heckePairedCompletionFactor chi 0 s *
        (heckeEulerL K chi s * heckeEulerL K (unitaryHeckeInverse chi) s) := by
  let Q := heckeArithmeticConductor chi
  have hQ : 0 < Q := heckeArithmeticConductor_pos chi
  have hQ2 : (0 : Real) < Q ^ 2 := pow_pos hQ _
  have hPower : ((Q ^ (2 : Nat) : Real) : Complex) ^ (s / 2) =
      (Q : Complex) ^ (s / 2) * (Q : Complex) ^ (s / 2) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hQ2.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hQ.ne'), <- Complex.exp_add,
      <- Complex.ofReal_log hQ2.le, <- Complex.ofReal_log hQ.le,
      Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
    congr 1
    push_cast
    ring
  have hR : (Finset.univ.prod (fun i : PairedRealHeckePlaces K =>
      DedekindZeta.LReal (s + heckePairedRealShift chi i))) =
      (Finset.univ.prod (fun i : {v : InfinitePlace K // v.IsReal} =>
        DedekindZeta.LReal (s + realInfiniteHeckeShift chi i.property))) *
      (Finset.univ.prod (fun i : {v : InfinitePlace K // v.IsReal} =>
        DedekindZeta.LReal (s + realInfiniteHeckeShift (unitaryHeckeInverse chi) i.property))) := by
    rw [Fintype.prod_prod_type, Fintype.prod_bool]
    rfl
  have hC : (Finset.univ.prod (fun i : PairedComplexHeckePlaces K =>
      DedekindZeta.LComplex (s + heckePairedComplexShift chi i))) =
      (Finset.univ.prod (fun i : {v : InfinitePlace K // v.IsComplex} =>
        DedekindZeta.LComplex (s + complexInfiniteHeckeShift chi i.property))) *
      (Finset.univ.prod (fun i : {v : InfinitePlace K // v.IsComplex} =>
        DedekindZeta.LComplex (s + complexInfiniteHeckeShift (unitaryHeckeInverse chi) i.property))) := by
    rw [Fintype.prod_prod_type, Fintype.prod_bool]
    rfl
  unfold heckeTateStandardCompletedEulerValue heckePairedCompletionFactor standardCompletionFactor
  simp only [pow_zero, one_mul, heckeArithmeticConductor_inverse]
  rw [hR, hC, hPower]
  ring

/-- The unitary Hecke characters whose restriction to norm-one idele
classes is nontrivial. Their standard completed L-functions are entire. -/
def HeckePoleFreeCharacter (K : Type*) [Field K] [NumberField K] :=
  {chi : UnitaryHeckeCharacter K // exists z : C K, Not (heckeNormOneClassCharacter chi z = 1)}

private def heckePoleFreeCharacterDual (i : HeckePoleFreeCharacter K) : HeckePoleFreeCharacter K :=
  Subtype.mk (unitaryHeckeInverse i.val) (by
    choose z hz using i.property
    refine Exists.intro z ?_
    have hQ : heckeNormOneClassCharacter (unitaryHeckeInverse i.val) z =
        Inv.inv (heckeNormOneClassCharacter i.val z) := by
      choose a ha using QuotientGroup.mk'_surjective (heckePrincipalNormOneIdele K).range z
      rw [<- ha, heckeNormOneClassCharacter_mk, heckeNormOneClassCharacter_mk]
      rfl
    rw [hQ, inv_eq_one]
    exact hz)

set_option maxHeartbeats 1000000 in
/-- The actual pole-free standard Hecke family satisfies the critical-line
hypothesis exactly when every character satisfies its paired triangular
prime-power bound. The completed functions agree with the arithmetic
conductor, Gamma factors and Euler product on the convergence half-plane. -/
theorem exists_heckePoleFreeCompletedFamily_triangularCriterion
    (K : Type*) [Field K] [NumberField K] :
    exists L : HeckePoleFreeCharacter K -> Complex -> Complex,
      And (forall i, Differentiable Complex (L i))
        (And (forall i s, 1 < s.re -> L i s = heckeTateStandardCompletedEulerValue i.val s)
          (CompletedFamilyRH L <-> forall i : HeckePoleFreeCharacter K, HeckeTriangularBound i.val 0)) := by
  choose H hH using exists_heckeCompletedEulerFamily_functionalEquation K
  let L (i : HeckePoleFreeCharacter K) := H i.val
  let dual := heckePoleFreeCharacterDual (K := K)
  have hDual (i : HeckePoleFreeCharacter K) : dual (dual i) = i :=
    Subtype.ext (unitaryHeckeInverse_involutive i.val)
  choose z hz using fun i : HeckePoleFreeCharacter K => i.property
  have hData (i : HeckePoleFreeCharacter K) := hH i.val (z i) (hz i)
  have hEuler (i : HeckePoleFreeCharacter K) (s : Complex) (hs : 1 < s.re) :
      L i s = heckeTateStandardCompletedEulerValue i.val s := (hData i).2.1 s hs
  choose root hRoot using fun i : HeckePoleFreeCharacter K => (hData i).2.2.2
  have hPairEuler (i : HeckePoleFreeCharacter K) (s : Complex) (hs : 1 < s.re) :
      L i s * L (dual i) s = heckePairedCompletionFactor i.val 0 s *
        (heckeEulerL K i.val s * heckeEulerL K (unitaryHeckeInverse i.val) s) := by
    rw [hEuler i s hs, hEuler (dual i) s hs]
    exact heckeTateStandardCompletedEulerValue_mul_inverse i.val s
  have hStrip (i : HeckePoleFreeCharacter K) :
      exists B : Real, forall s : Complex, -2 <= s.re -> s.re <= 3 ->
        norm (L i s * L (dual i) s) <= B := by
    choose B hB using (hData i).2.2.1
    choose C hC using (hData (dual i)).2.2.1
    refine Exists.intro (B * C) ?_
    intro s hL hR
    rw [norm_mul]
    exact mul_le_mul (hB s hL hR) (hC s hL hR) (norm_nonneg _)
      ((norm_nonneg _).trans (hB s hL hR))
  have hEntire (i : HeckePoleFreeCharacter K) :
      Differentiable Complex (fun s => L i s * L (dual i) s) :=
    (hData i).1.mul (hData (dual i)).1
  have hEquation (i : HeckePoleFreeCharacter K) (s : Complex) :
      L (dual i) (1 - s) = root i * L i s := (hRoot i).2 s
  refine Exists.intro L (And.intro (fun i => (hData i).1) (And.intro hEuler ?_))
  exact heckePoleFreeCompletedCriterion_of_stripBound (K := K) (index := HeckePoleFreeCharacter K)
    (fun i => i.val) dual L (fun i _ => root i) hDual (fun i _ => (hRoot i).1)
    hEntire hPairEuler hStrip hEquation

/-- The unitary Hecke characters trivial on the norm-one classes are
exactly the purely imaginary powers of the idelic norm. -/
theorem heckeNormOneClassCharacter_trivial_iff_normCharacter
    (chi : UnitaryHeckeCharacter K) :
    (forall z : heckeNormOneIdeleClass K, heckeNormOneClassCharacter chi z = 1) <->
      exists t : Real, chi = heckeNormCharacter t := by
  let : MeasurableSpace (heckeNormOneIdeleClass K) := borel _
  constructor
  . intro h
    choose t ht using exists_heckeTateClassZeta_mellinTail_shift chi
    refine Exists.intro t ?_
    apply Subtype.ext
    ext a
    let r := Real.log (heckeIdelicNorm a)
    have hNorm : Membership.mem (heckeNormOneIdeles K) (heckeIdelicExpSection K (-r) * a) := by
      apply (mem_heckeNormOneIdeles K _).mpr
      rw [map_mul, heckeIdelicNorm_expSection, Real.exp_neg]
      change Inv.inv (Real.exp (Real.log (heckeIdelicNorm a))) * heckeIdelicNorm a = 1
      rw [Real.exp_log (heckeIdelicNorm_pos a)]
      simp [(heckeIdelicNorm_pos a).ne']
    let b : heckeNormOneIdeles K := Subtype.mk (heckeIdelicExpSection K (-r) * a) hNorm
    have hB : chi.val b.val = 1 := by
      rw [<- heckeNormOneClassCharacter_mk chi b]
      exact h _
    have hFactor : a = heckeIdelicExpSection K r * b.val := by
      change a = heckeIdelicExpSection K r * (heckeIdelicExpSection K (-r) * a)
      rw [<- mul_assoc, <- heckeIdelicExpSection_add, add_neg_cancel,
        heckeIdelicExpSection_zero, one_mul]
    change (chi.val a : Complex) = ((heckeNormCharacter t).val a : Complex)
    calc
      _ = (chi.val (heckeIdelicExpSection K r * b.val) : Complex) :=
        congrArg (fun v => (chi.val v : Complex)) hFactor
      _ = (chi.val (heckeIdelicExpSection K r) : Complex) := by rw [map_mul, hB, mul_one]
      _ = (Complex.exp (((t * r : Real) : Complex) * Complex.I)) := ht.1 r
      _ = _ := (Circle.coe_exp (t * r)).symm
  . intro h z
    choose t ht using h
    rw [ht]
    choose a ha using QuotientGroup.mk'_surjective (heckePrincipalNormOneIdele K).range z
    rw [<- ha, heckeNormOneClassCharacter_mk]
    change Circle.exp (t * Real.log (heckeIdelicNorm a.val)) = 1
    rw [(mem_heckeNormOneIdeles K a.val).mp a.property, Real.log_one, mul_zero, Circle.exp_zero]

/-- Every unitary Hecke character is either a norm twist or is nontrivial
on the norm-one classes. -/
theorem heckeCharacter_normTwist_or_nontrivialNormOne (chi : UnitaryHeckeCharacter K) :
    Or (exists t : Real, chi = heckeNormCharacter t)
      (exists z : heckeNormOneIdeleClass K, Not (heckeNormOneClassCharacter chi z = 1)) := by
  by_cases h : exists z : heckeNormOneIdeleClass K, Not (heckeNormOneClassCharacter chi z = 1)
  . exact Or.inr h
  . apply Or.inl
    apply (heckeNormOneClassCharacter_trivial_iff_normCharacter chi).mp
    intro z
    by_contra hz
    exact h (Exists.intro z hz)

private theorem completedDedekindPoleCleared_RH_iff (K : Type*) [Field K] [NumberField K] :
    (forall s : Complex, DedekindZeta.completedDedekindPoleCleared K s = 0 -> s.re = 1 / 2) <->
      DedekindRH K := by
  constructor
  . intro h
    apply (dedekindRH_iff_zeros_of_continuation (DedekindZeta.isDedekindZetaContinuation_actual K)).mpr
    intro s hs0 hs1 hz
    have hs : Not (s = 1) := by
      intro e
      rw [e, Complex.one_re] at hs1
      exact (lt_irrefl _) hs1
    have hZ : DedekindZeta.entirePoleFreeDedekindZeta K s = 0 := by
      unfold DedekindZeta.dedekindZetaContinuation at hz
      exact (div_eq_zero_iff.mp hz).resolve_right (sub_ne_zero.mpr hs)
    apply h s
    rw [DedekindZeta.completedDedekindPoleCleared_eq_archimedean K hs0, hZ, mul_zero]
  . intro h s hs
    exact DedekindZeta.completedDedekindPoleCleared_zero_re_of_dedekindRH K h hs

/-- A norm twist translates the zeros of the pole-cleared Dedekind
completion vertically, preserving its triangular criterion. -/
theorem completedDedekindNormTwist_RH_iff_triangular
    (K : Type*) [Field K] [NumberField K] (t : Real) :
    (forall s : Complex, DedekindZeta.completedDedekindPoleCleared K
      (s + (t : Complex) * Complex.I) = 0 -> s.re = 1 / 2) <->
        DedekindTriangularRobin K := by
  have hRe (s : Complex) : (s + (t : Complex) * Complex.I).re = s.re := by
    simp [Complex.add_re, Complex.mul_re]
  have h :
      (forall s : Complex, DedekindZeta.completedDedekindPoleCleared K
        (s + (t : Complex) * Complex.I) = 0 -> s.re = 1 / 2) <->
      (forall s : Complex, DedekindZeta.completedDedekindPoleCleared K s = 0 -> s.re = 1 / 2) := by
    constructor
    . intro h s hz
      let u := s - (t : Complex) * Complex.I
      have hu : u + (t : Complex) * Complex.I = s := sub_add_cancel _ _
      have hLine := h u (by rw [hu]; exact hz)
      rw [<- hRe u, hu] at hLine
      exact hLine
    . intro h s hz
      have hLine := h (s + (t : Complex) * Complex.I) hz
      rwa [hRe] at hLine
  exact h.trans ((completedDedekindPoleCleared_RH_iff K).trans
    (dedekindRH_iff_dedekindTriangularRobin K))

set_option maxHeartbeats 1200000 in
/-- The rank-one standard automorphic family over a number field has all
zeros of its pole-cleared completions on the critical line exactly when
the Dedekind triangular bound and the paired bounds for its pole-free
Hecke characters hold. The completions are identified with the standard
Euler products or with the translated Dedekind completion. -/
theorem exists_heckeStandardCompletedFamily_triangularCriterion
    (K : Type*) [Field K] [NumberField K] :
    exists L : UnitaryHeckeCharacter K -> Complex -> Complex,
      And (forall chi, Differentiable Complex (L chi))
        (And (forall (i : HeckePoleFreeCharacter K) s, 1 < s.re ->
          L i.val s = heckeTateStandardCompletedEulerValue i.val s)
          (And (forall (chi : UnitaryHeckeCharacter K),
            (forall z : C K, heckeNormOneClassCharacter chi z = 1) ->
              exists t : Real, And (chi = heckeNormCharacter t)
                (forall s : Complex, L chi s =
                  DedekindZeta.completedDedekindPoleCleared K (s + (t : Complex) * Complex.I)))
            (CompletedFamilyRH L <-> And (DedekindTriangularRobin K)
              (forall i : HeckePoleFreeCharacter K, HeckeTriangularBound i.val 0)))) := by
  choose P hP using exists_heckePoleFreeCompletedFamily_triangularCriterion K
  let N (chi : UnitaryHeckeCharacter K) := exists z : C K, Not (heckeNormOneClassCharacter chi z = 1)
  have hTw (chi : UnitaryHeckeCharacter K) (h : Not (N chi)) :
      exists t : Real, chi = heckeNormCharacter t := by
    apply (heckeNormOneClassCharacter_trivial_iff_normCharacter chi).mp
    intro z
    by_contra hz
    exact h (Exists.intro z hz)
  let t (chi : UnitaryHeckeCharacter K) (h : Not (N chi)) := Classical.choose (hTw chi h)
  let L (chi : UnitaryHeckeCharacter K) (s : Complex) :=
    if h : N chi then P (Subtype.mk chi h) s
    else DedekindZeta.completedDedekindPoleCleared K (s + (t chi h : Complex) * Complex.I)
  have hLfree (i : HeckePoleFreeCharacter K) (s : Complex) : L i.val s = P i s := by
    change (if h : N i.val then P (Subtype.mk i.val h) s
      else DedekindZeta.completedDedekindPoleCleared K
        (s + (t i.val h : Complex) * Complex.I)) = P i s
    rw [dif_pos i.property]
    rfl
  have hLtw (chi : UnitaryHeckeCharacter K) (h : Not (N chi)) (s : Complex) :
      L chi s = DedekindZeta.completedDedekindPoleCleared K
        (s + (t chi h : Complex) * Complex.I) := by
    change (if h' : N chi then P (Subtype.mk chi h') s
      else DedekindZeta.completedDedekindPoleCleared K
        (s + (t chi h' : Complex) * Complex.I)) = _
    rw [dif_neg h]
  have hDir (chi : UnitaryHeckeCharacter K) : Differentiable Complex (L chi) := by
    by_cases h : N chi
    . have he : L chi = P (Subtype.mk chi h) := funext (hLfree (Subtype.mk chi h))
      rw [he]
      exact hP.1 (Subtype.mk chi h)
    . rw [funext (hLtw chi h)]
      have hC : Differentiable Complex (DedekindZeta.completedDedekindPoleCleared K) :=
        fun s => (DedekindZeta.analyticAt_completedDedekindPoleCleared K s).differentiableAt
      exact hC.comp (differentiable_id.add (differentiable_const _))
  refine Exists.intro L (And.intro hDir (And.intro ?_ (And.intro ?_ ?_)))
  . intro i s hs
    exact (hLfree i s).trans (hP.2.1 i s hs)
  . intro chi h
    have hNot : Not (N chi) := by
      intro a
      choose z hz using a
      exact hz (h z)
    exact Exists.intro (t chi hNot) (And.intro (Classical.choose_spec (hTw chi hNot)) (hLtw chi hNot))
  . constructor
    . intro h
      have hFree : CompletedFamilyRH P := by
        intro i s hs
        exact h i.val s ((hLfree i s).trans hs)
      let chi : UnitaryHeckeCharacter K := heckeNormCharacter 0
      have hT : forall z : C K, heckeNormOneClassCharacter chi z = 1 :=
        (heckeNormOneClassCharacter_trivial_iff_normCharacter chi).mpr (Exists.intro 0 rfl)
      have hNot : Not (N chi) := by
        intro a
        choose z hz using a
        exact hz (hT z)
      have hTwist (s : Complex) (hz : DedekindZeta.completedDedekindPoleCleared K
          (s + (t chi hNot : Complex) * Complex.I) = 0) : s.re = 1 / 2 :=
        h chi s ((hLtw chi hNot s).trans hz)
      exact And.intro ((completedDedekindNormTwist_RH_iff_triangular K (t chi hNot)).mp hTwist)
        (hP.2.2.mp hFree)
    . intro h chi s hz
      by_cases hN : N chi
      . exact (hP.2.2.mpr h.2) (Subtype.mk chi hN) s
          ((hLfree (Subtype.mk chi hN) s).symm.trans hz)
      . exact (completedDedekindNormTwist_RH_iff_triangular K (t chi hN)).mpr h.1 s
          ((hLtw chi hN s).symm.trans hz)

end Robin1984.GRH
