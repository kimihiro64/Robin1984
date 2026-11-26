import Robin1984.GRH.HeckeTateContinuation
import Robin1984.GRH.HeckeTateFiniteFourier
import Robin1984.GRH.HeckeTateInfiniteFourier

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's thesis, the Mellin transform of the adelic Poisson formula.
- Formalization note: Constructs the conductor-shifted reflection and conjugation of the canonical norm-one theta averages and identifies their full Mellin integrals with the two tails.
- PROVENANCE-END
-/

/-!
# Mellin reflection for canonical Hecke Tate tests

A finite dilation translates the logarithmic norm and moves the norm-one
idele class by multiplication. Averaging against a nontrivial character
removes the two constants in Poisson summation. For the canonical tests
the two Fourier identities give a conductor-shifted reflection. The
entire Mellin tails agree with integration over the full logarithmic line,
and conjugation takes the tests for a character to the tests for its inverse.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open IsDedekindDomain NumberField MeasureTheory
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev Mix (K : Type*) [Field K] := mixedEmbedding.mixedSpace K

private abbrev F (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

/-- The norm-one representative of a finite idele after compensating
for its norm by an archimedean scale. -/
def heckeTateFiniteNormOneLift (b : Units (F K)) : heckeNormOneIdeles K :=
  Subtype.mk (heckeIdelicExpSection K (-(Real.log (heckeFiniteIdeleNorm b))) *
    heckeFiniteIdeleInclusion b) (by
      apply (mem_heckeNormOneIdeles K _).mpr
      rw [map_mul, heckeIdelicNorm_expSection]
      have hFinite : heckeIdelicNorm (heckeFiniteIdeleInclusion b) = heckeFiniteIdeleNorm b := by
        change heckeInfiniteIdeleNorm (1 : Units (InfiniteAdeleRing K)) *
          heckeFiniteIdeleNorm b = heckeFiniteIdeleNorm b
        rw [map_one, one_mul]
      rw [hFinite, Real.exp_neg, Real.exp_log (heckeFiniteIdeleNorm_pos b)]
      simp [(heckeFiniteIdeleNorm_pos b).ne'])

private theorem heckeTateThetaNormOneTerm_eq_full_of_ne_zero
    (f : SchwartzMap (Mix K) Complex) (T : F K -> Complex)
    (a : heckeNormOneIdeles K) (t : Real) (x : K) (hx : Not (x = 0)) :
    heckeTateThetaNormOneTerm f T a t x =
      heckeTateFullThetaTerm f T (heckeIdelicExpSection K t * a.val) x := by
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let c := Real.exp (t / (Module.finrank Rat K : Real))
  have hScale : (heckeIdelicExpSection K t).val =
      Prod.mk (E.symm (algebraMap Real (Mix K) c)) (1 : F K) := rfl
  rw [heckeTateThetaNormOneTerm, if_neg hx]
  symm
  change heckeTateFullThetaTerm f T (heckeIdelicExpSection K t * a.val) x =
    f (HSMul.hSMul c (E a.val.val.1 * mixedEmbedding K x)) *
      T (a.val.val.2 * algebraMap K (F K) x)
  unfold heckeTateFullThetaTerm
  rw [Units.val_mul, hScale]
  change f (E (E.symm (algebraMap Real (Mix K) c) * a.val.val.1) * mixedEmbedding K x) *
    T (algebraMap K (F K) x * (1 * a.val.val.2)) = _
  rw [E.map_mul, E.apply_symm_apply, Algebra.algebraMap_eq_smul_one]
  simp only [smul_mul_assoc, one_mul, mul_comm (algebraMap K (F K) x)]

/-- Scaling the finite test by an idele translates its logarithmic radius
and multiplies its norm-one class by the compensated idele. -/
theorem heckeTateThetaNormOneClass_finite_translate
    (f : SchwartzMap (Mix K) Complex) (T : F K -> Complex)
    (b : Units (F K)) (t : Real) (z : heckeNormOneIdeleClass K) :
    heckeTateThetaNormOneClass f (fun x => T (b.val * x)) t z =
      heckeTateThetaNormOneClass f T (t + Real.log (heckeFiniteIdeleNorm b))
        ((QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
          (heckeTateFiniteNormOneLift b)) * z) := by
  let q := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
  choose a ha using QuotientGroup.mk'_surjective (heckePrincipalNormOneIdele K).range z
  let v := heckeTateFiniteNormOneLift b
  let r := Real.log (heckeFiniteIdeleNorm b)
  change heckeTateThetaNormOneClass f (fun x => T (b.val * x)) t z =
    heckeTateThetaNormOneClass f T (t + r) (q v * z)
  rw [<- ha, <- map_mul q, heckeTateThetaNormOneClass_mk, heckeTateThetaNormOneClass_mk]
  have hId : heckeIdelicExpSection K (t + r) * (v * a).val =
      heckeFiniteIdeleInclusion b * (heckeIdelicExpSection K t * a.val) := by
    change heckeIdelicExpSection K (t + r) *
      ((heckeIdelicExpSection K (-r) * heckeFiniteIdeleInclusion b) * a.val) = _
    calc
      _ = heckeFiniteIdeleInclusion b *
          ((heckeIdelicExpSection K (t + r) * heckeIdelicExpSection K (-r)) * a.val) :=
        by ac_rfl
      _ = _ := by rw [<- heckeIdelicExpSection_add, add_neg_cancel_right]
  unfold heckeTateThetaNormOne
  apply tsum_congr
  intro x
  by_cases hx : x = 0
  . rw [heckeTateThetaNormOneTerm, if_pos hx, heckeTateThetaNormOneTerm, if_pos hx]
  . rw [heckeTateThetaNormOneTerm_eq_full_of_ne_zero _ _ _ _ _ hx,
      heckeTateThetaNormOneTerm_eq_full_of_ne_zero _ _ _ _ _ hx, hId]
    let A := heckeIdelicExpSection K t * a.val
    change heckeTateFullThetaTerm f (fun y => T (b.val * y)) A x =
      heckeTateFullThetaTerm f T (heckeFiniteIdeleInclusion b * A) x
    unfold heckeTateFullThetaTerm
    change f (InfiniteAdeleRing.ringEquiv_mixedSpace K A.val.1 * mixedEmbedding K x) *
      T (b.val * (algebraMap K (F K) x * A.val.2)) =
      f (InfiniteAdeleRing.ringEquiv_mixedSpace K ((1 : InfiniteAdeleRing K) * A.val.1) *
        mixedEmbedding K x) * T (algebraMap K (F K) x * (b.val * A.val.2))
    rw [one_mul, mul_left_comm b.val]

private abbrev C (K : Type*) [Field K] [NumberField K] := heckeNormOneIdeleClass K

/-- Integrating the translated finite test against a character introduces
the inverse character value of the compensating norm-one idele. -/
theorem integral_heckeTateThetaNormOneClass_finite_translate
    [MeasurableSpace (C K)] [BorelSpace (C K)]
    (mu : Measure (C K)) [mu.IsMulLeftInvariant]
    (q : ContinuousMonoidHom (C K) Circle)
    (f : SchwartzMap (Mix K) Complex) (T : F K -> Complex)
    (b : Units (F K)) (t : Real) :
    integral mu (fun z : C K => (q z : Complex) *
      heckeTateThetaNormOneClass f (fun x => T (b.val * x)) t z) =
      (q (Inv.inv (QuotientGroup.mk' (heckePrincipalNormOneIdele K).range
        (heckeTateFiniteNormOneLift b))) : Complex) *
        integral mu (fun z : C K => (q z : Complex) *
          heckeTateThetaNormOneClass f T (t + Real.log (heckeFiniteIdeleNorm b)) z) := by
  let u := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range (heckeTateFiniteNormOneLift b)
  let H (z : C K) := (q z : Complex) *
    heckeTateThetaNormOneClass f T (t + Real.log (heckeFiniteIdeleNorm b)) z
  change _ = (q (Inv.inv u) : Complex) * integral mu H
  calc
    _ = integral mu (fun z : C K => (q (Inv.inv u) : Complex) * H (u * z)) := by
      apply integral_congr_ae
      filter_upwards with z
      have hQ : (q z : Complex) = (q (Inv.inv u) : Complex) * (q (u * z) : Complex) := by
        have hVal : q z = q (Inv.inv u) * q (u * z) := by
          rw [<- map_mul, <- mul_assoc, inv_mul_cancel, one_mul]
        exact congrArg (fun a : Circle => (a : Complex)) hVal
      rw [heckeTateThetaNormOneClass_finite_translate f T b t z]
      change (q z : Complex) *
        heckeTateThetaNormOneClass f T (t + Real.log (heckeFiniteIdeleNorm b)) (u * z) =
        (q (Inv.inv u) : Complex) * H (u * z)
      rw [hQ, mul_assoc]
    _ = _ := by rw [integral_const_mul, integral_mul_left_eq_self H u]

/-- Scaling the two factors of a Tate theta sum multiplies the sum by
the product of their scalars. -/
theorem heckeTateThetaNormOneClass_scale
    (f g : SchwartzMap (Mix K) Complex) (T U : F K -> Complex) (w k : Complex)
    (hf : forall x, f x = w * g x) (hT : forall x, T x = k * U x)
    (t : Real) (z : C K) :
    heckeTateThetaNormOneClass f T t z = (w * k) * heckeTateThetaNormOneClass g U t z := by
  choose a ha using QuotientGroup.mk'_surjective (heckePrincipalNormOneIdele K).range z
  rw [<- ha, heckeTateThetaNormOneClass_mk, heckeTateThetaNormOneClass_mk]
  unfold heckeTateThetaNormOne
  rw [<- tsum_mul_left]
  apply tsum_congr
  intro x
  by_cases hx : x = 0
  . simp only [heckeTateThetaNormOneTerm, if_pos hx, mul_zero]
  . rw [heckeTateThetaNormOneTerm, if_neg hx, heckeTateThetaNormOneTerm, if_neg hx, hf, hT]
    ring

/-- The full logarithmic Mellin integral centered at the conductor. -/
def heckeTateCenteredMellin (G : Real -> Complex) (beta : Real) (s : Complex) : Complex :=
  Complex.exp (-s * (beta : Complex) / 2) *
    integral volume (fun t : Real => Complex.exp (s * (t : Complex)) * G t)

/-- A theta reflection at logarithmic shift beta reflects the centered
Mellin integral, with scalar multiplied by exp(-beta / 2). -/
theorem heckeTateCenteredMellin_reflect
    (G H : Real -> Complex) (beta : Real) (k : Complex)
    (h : forall t, G t = k * (Real.exp (-t) : Complex) * H (beta - t))
    (s : Complex) :
    heckeTateCenteredMellin G beta s =
      (k * Complex.exp (-(beta : Complex) / 2)) * heckeTateCenteredMellin H beta (1 - s) := by
  let F (u : Real) := Complex.exp ((1 - s) * (u : Complex)) * H u
  let k' := k * Complex.exp ((s - 1) * (beta : Complex))
  have hF : integral volume (fun t : Real => F (beta - t)) = integral volume F := by
    change integral volume (fun t : Real => F (beta + (-t))) = integral volume F
    rw [integral_neg_eq_self (fun t : Real => F (beta + t)), integral_add_left_eq_self F beta]
  have hLine (t : Real) : Complex.exp (s * (t : Complex)) * G t = k' * F (beta - t) := by
    rw [h]
    simp only [k', F, Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_neg]
    have hArg : s * (t : Complex) + (-(t : Complex)) =
        (s - 1) * (beta : Complex) + (1 - s) * ((beta : Complex) - (t : Complex)) := by ring
    calc
      _ = k * (Complex.exp (s * (t : Complex)) * Complex.exp (-(t : Complex))) *
          H (beta - t) := by ring
      _ = _ := by rw [<- Complex.exp_add, hArg, Complex.exp_add]; ring
  have hInt : integral volume (fun t : Real => Complex.exp (s * (t : Complex)) * G t) =
      k' * integral volume F := by
    simp only [hLine, integral_const_mul, hF]
  unfold heckeTateCenteredMellin
  rw [hInt]
  change Complex.exp (-s * (beta : Complex) / 2) *
      ((k * Complex.exp ((s - 1) * (beta : Complex))) * integral volume F) =
    (k * Complex.exp (-(beta : Complex) / 2)) *
      (Complex.exp (-(1 - s) * (beta : Complex) / 2) * integral volume F)
  have hExp : -s * (beta : Complex) / 2 + (s - 1) * (beta : Complex) =
      -(beta : Complex) / 2 + (-(1 - s) * (beta : Complex) / 2) := by ring
  calc
    _ = k * (Complex.exp (-s * (beta : Complex) / 2) *
        Complex.exp ((s - 1) * (beta : Complex))) * integral volume F := by ring
    _ = _ := by rw [<- Complex.exp_add, hExp, Complex.exp_add]; ring

/-- The theta sum averaged against a unitary character on the compact
norm-one idele class group. -/
def heckeTateCharacterThetaAverage
    [MeasurableSpace (C K)] (mu : Measure (C K))
    (chi : UnitaryHeckeCharacter K) (f : SchwartzMap (Mix K) Complex)
    (T : F K -> Complex) (t : Real) : Complex :=
  integral mu (fun z : C K => (heckeNormOneClassCharacter chi z : Complex) *
    heckeTateThetaNormOneClass f T t z)

private theorem heckeNormOneClassCharacter_on_inv (chi : UnitaryHeckeCharacter K) (z : C K) :
    heckeNormOneClassCharacter chi (Inv.inv z) =
      heckeNormOneClassCharacter (unitaryHeckeInverse chi) z := by
  choose a ha using QuotientGroup.mk'_surjective (heckePrincipalNormOneIdele K).range z
  rw [<- ha, map_inv, heckeNormOneClassCharacter_mk, heckeNormOneClassCharacter_mk]
  rfl

/-- Nontriviality on norm-one classes removes both constant terms of
Poisson summation before the integration in the logarithmic radius. -/
theorem heckeTateCharacterThetaAverage_poisson
    [MeasurableSpace (C K)] [BorelSpace (C K)]
    [MeasurableSpace (F K)] [BorelSpace (F K)]
    (mu : Measure (C K)) [IsFiniteMeasure mu] [mu.IsMulLeftInvariant]
    (hInv : MeasurePreserving Inv.inv mu mu)
    (chi : UnitaryHeckeCharacter K) (z0 : C K)
    (hz : Not (heckeNormOneClassCharacter chi z0 = 1))
    (f : SchwartzMap (Mix K) Complex) (t : Real)
    (hP : Continuous (heckeTateThetaNormOneClass f (heckeFiniteAdditiveTateTest chi) t))
    (hD : Continuous (heckeTateThetaNormOneClass (heckeTateDualInfiniteTest f)
      (heckeTateDualFiniteTest chi) (-t))) :
    heckeTateCharacterThetaAverage mu chi f (heckeFiniteAdditiveTateTest chi) t =
      (Real.exp (-t) : Complex) *
        heckeTateCharacterThetaAverage mu (unitaryHeckeInverse chi) (heckeTateDualInfiniteTest f)
          (heckeTateDualFiniteTest chi) (-t) := by
  let : CompactSpace (C K) := compactSpace_heckeNormOneIdeleClass K
  let opp := unitaryHeckeInverse chi
  let q := heckeNormOneClassCharacter opp
  let fD := heckeTateDualInfiniteTest f
  let T := heckeFiniteAdditiveTateTest chi
  let TD := heckeTateDualFiniteTest chi
  let P (z : C K) := (heckeNormOneClassCharacter chi z : Complex) *
    heckeTateThetaNormOneClass f T t z
  let D (z : C K) := (q z : Complex) * heckeTateThetaNormOneClass fD TD (-t) z
  let E (a : Complex) (z : C K) := (q z : Complex) * a
  let r := (Real.exp (-t) : Complex)
  let j : Complex := f 0 * T 0
  let jD : Complex := fD 0 * TD 0
  let e := MeasurableEquiv.inv (C K)
  have hMP : MeasurePreserving e mu mu := hInv
  have hzOpp : Not (q (Inv.inv z0) = 1) := by
    intro hz'
    apply hz
    rw [show q (Inv.inv z0) = Inv.inv (heckeNormOneClassCharacter chi (Inv.inv z0)) from
      (heckeNormOneClassCharacter_on_inv chi _).symm.trans (map_inv _ _)]
      at hz'
    rw [map_inv, inv_inv] at hz'
    exact hz'
  have hQc : Continuous (fun z : C K => (q z : Complex)) :=
    continuous_subtype_val.comp q.continuous
  have hPc : Continuous P :=
    (continuous_subtype_val.comp (heckeNormOneClassCharacter chi).continuous).mul hP
  have hDc : Continuous D := hQc.mul hD
  have hEc (a : Complex) : Continuous (E a) := hQc.mul continuous_const
  have hPi : Integrable P mu := hPc.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hDi : Integrable D mu := hDc.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hEi (a : Complex) : Integrable (E a) mu :=
    (hEc a).integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hE0 (a : Complex) : integral mu (E a) = 0 := by
    unfold E
    rw [integral_mul_const, integral_continuousCircleCharacter_eq_zero mu q (Inv.inv z0) hzOpp,
      zero_mul]
  have hPI : Integrable (Function.comp P e) mu :=
    (hMP.integrable_comp_emb e.measurableEmbedding).mpr hPi
  have hEq (z : C K) : P (e z) + E j z = r * (D z + E jD z) := by
    have hTheta := heckeTateThetaNormOneClass_poisson chi f t (Inv.inv z)
    have hII : Inv.inv (Inv.inv z) = z := inv_inv z
    rw [hII] at hTheta
    change heckeTateThetaNormOneClass f T t (Inv.inv z) + j =
      r * (heckeTateThetaNormOneClass fD TD (-t) z + jD) at hTheta
    have h := congrArg (fun w : Complex => (q z : Complex) * w) hTheta
    change (heckeNormOneClassCharacter chi (Inv.inv z) : Complex) *
      heckeTateThetaNormOneClass f T t (Inv.inv z) + (q z : Complex) * j =
      r * ((q z : Complex) * heckeTateThetaNormOneClass fD TD (-t) z + (q z : Complex) * jD)
    rw [heckeNormOneClassCharacter_on_inv]
    linear_combination h
  have hI := congrArg (integral mu) (funext hEq)
  change integral mu (fun z => Function.comp P e z + E j z) =
    integral mu (fun z => r * (D z + E jD z)) at hI
  rw [integral_add hPI (hEi j), integral_const_mul, integral_add hDi (hEi jD),
    hE0, hE0, add_zero, add_zero] at hI
  exact (hMP.integral_comp' P).symm.trans hI

set_option maxHeartbeats 1000000 in
/-- The canonical averaged Tate theta functions satisfy the shifted
Poisson identity, with both the archimedean phase and the finite scalar. -/
theorem heckeTateCharacterThetaAverage_canonical_reflect
    [MeasurableSpace (C K)] [BorelSpace (C K)]
    [MeasurableSpace (F K)] [BorelSpace (F K)]
    (mu : Measure (C K)) [IsFiniteMeasure mu] [mu.IsMulLeftInvariant]
    (hInv : MeasurePreserving Inv.inv mu mu)
    (chi : UnitaryHeckeCharacter K) (z0 : C K)
    (hz : Not (heckeNormOneClassCharacter chi z0 = 1))
    (f g : SchwartzMap (Mix K) Complex)
    (hf : forall x, f x = heckeTateInfiniteTest chi x)
    (hg : forall x, g x = heckeTateInfiniteTest (unitaryHeckeInverse chi) x)
    (d c : Units (F K))
    (hd : heckeFiniteIdeleFractionalIdeal d = DedekindZeta.Theta.differentFractionalIdeal K)
    (hc : heckeFiniteIdeleFractionalIdeal c = (heckeConductorIdeal chi :
      FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K))
    (hcVal : forall p : HeightOneSpectrum (RingOfIntegers K),
      (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) (c.val p) =
        ((Multiplicative.ofAdd (-(heckeConductorExponent chi p : Int)) : Multiplicative Int) :
          WithZero (Multiplicative Int))) :
    exists k : Complex, forall t : Real,
      heckeTateCharacterThetaAverage mu chi f (heckeFiniteAdditiveTateTest chi) t =
        k * (Real.exp (-t) : Complex) *
          heckeTateCharacterThetaAverage mu (unitaryHeckeInverse chi) g
            (heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi))
            (Real.log (heckeFiniteIdeleNorm (d * c)) - t) := by
  let b := d * c
  let opp := unitaryHeckeInverse chi
  let q := heckeNormOneClassCharacter opp
  let u := QuotientGroup.mk' (heckePrincipalNormOneIdele K).range (heckeTateFiniteNormOneLift b)
  let p := heckeTateArchimedeanFourierPhase chi
  let k := heckeTateDualFiniteTest chi b.inv
  let T := heckeFiniteAdditiveTateTest opp
  let U (x : F K) := T (b.val * x)
  let T0 := heckeFiniteAdditiveTateTest chi
  let TD := heckeTateDualFiniteTest chi
  let fD := heckeTateDualInfiniteTest f
  let O := heckeIntegralFiniteAdeles (K := K)
  have hZero (x : F K) (h : Not (Membership.mem (O : Set (F K)) x)) : T0 x = 0 := by
    change Not (Membership.mem O x) at h
    rw [show T0 = heckeFiniteAdditiveTateTest chi from rfl, heckeFiniteAdditiveTateTest, if_neg h]
  have hP := continuous_heckeTateThetaNormOneClass_joint f T0
    (continuous_heckeFiniteAdditiveTateTest chi) (O : Set (F K)) isCompact_integralFiniteAdeles
    hZero 1 zero_le_one (norm_heckeFiniteAdditiveTateTest_le_one chi)
  have hTDC : Continuous TD := by
    change Continuous (fun y : F K =>
      Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
        heckeFiniteFourierIntegral heckeFiniteAdeleHaar (heckeFiniteAdditiveTateTest chi) (-y))
    exact continuous_const.mul
      ((continuous_heckeFiniteFourierIntegral_TateTest heckeFiniteAdeleHaar chi).comp continuous_neg)
  choose S B hS using heckeTateDualFiniteTest_support_and_bound chi
  have hD := continuous_heckeTateThetaNormOneClass_joint fD TD hTDC S hS.1
    hS.2.2.1 B hS.2.1 hS.2.2.2
  refine Exists.intro ((p * k) * (q (Inv.inv u) : Complex)) ?_
  intro t
  have hPrim : Continuous (heckeTateThetaNormOneClass f T0 t) := by
    have hArg : Continuous (fun z : C K => Prod.mk t z) := continuous_const.prodMk continuous_id
    have h := hP.comp hArg
    simpa only [Function.comp_def] using h
  have hDual : Continuous (heckeTateThetaNormOneClass fD TD (-t)) := by
    have hArg : Continuous (fun z : C K => Prod.mk (-t) z) := continuous_const.prodMk continuous_id
    have h := hD.comp hArg
    simpa only [Function.comp_def] using h
  have hPoisson := heckeTateCharacterThetaAverage_poisson mu hInv chi z0 hz f t hPrim hDual
  have hArch (x : Mix K) : fD x = p * g x :=
    (heckeTateDualInfiniteTest_eq_phase_mul_inverse chi f hf x).trans
      (congrArg (fun y => p * y) (hg x).symm)
  have hFin (x : F K) : TD x = k * U x :=
    heckeTateDualFiniteTest_eq_mul_inverse chi d c hd hc hcVal x
  have hDualAvg : heckeTateCharacterThetaAverage mu opp fD TD (-t) =
      ((p * k) * (q (Inv.inv u) : Complex)) *
        heckeTateCharacterThetaAverage mu opp g T (Real.log (heckeFiniteIdeleNorm b) - t) := by
    let A (z : C K) := (q z : Complex) * heckeTateThetaNormOneClass g U (-t) z
    let r := Real.log (heckeFiniteIdeleNorm b)
    have hTrans : integral mu A = (q (Inv.inv u) : Complex) *
        heckeTateCharacterThetaAverage mu opp g T (r - t) := by
      have h := integral_heckeTateThetaNormOneClass_finite_translate mu q g T b (-t)
      have hLog : -t + Real.log (heckeFiniteIdeleNorm b) = r - t := by
        dsimp only [r]
        ring
      rw [hLog] at h
      exact h
    calc
      _ = integral mu (fun z : C K => (p * k) * A z) := by
        apply integral_congr_ae
        filter_upwards with z
        have hTheta := heckeTateThetaNormOneClass_scale fD g TD U p k hArch hFin (-t) z
        change (q z : Complex) * heckeTateThetaNormOneClass fD TD (-t) z =
          (p * k) * ((q z : Complex) * heckeTateThetaNormOneClass g U (-t) z)
        rw [hTheta, mul_left_comm (q z : Complex) (p * k)]
      _ = _ := by
        rw [integral_const_mul, hTrans]
        simp only [mul_assoc]
        rfl
  calc
    _ = (Real.exp (-t) : Complex) * heckeTateCharacterThetaAverage mu opp fD TD (-t) := hPoisson
    _ = _ := by
      rw [hDualAvg, mul_left_comm]
      simp only [mul_assoc]
      rfl

/-- A logarithmic reflection identifies the full Mellin integral with
the sum of its two positive tails. -/
theorem integral_tateLogWeight_eq_two_positive
    (A B : Real -> Complex) (a : Complex)
    (hReflection : forall t, A t = (Real.exp (-t) : Complex) * B (-t))
    (hA : Integrable (fun t : Real => Complex.exp (a * (t : Complex)) * A t)
      (volume.restrict (Set.Ioi (0 : Real))))
    (hB : Integrable (fun t : Real => Complex.exp ((1 - a) * (t : Complex)) * B t)
      (volume.restrict (Set.Ioi (0 : Real)))) :
    And (Integrable (fun t : Real => Complex.exp (a * (t : Complex)) * A t) volume)
      (integral volume (fun t : Real => Complex.exp (a * (t : Complex)) * A t) =
        integral (volume.restrict (Set.Ioi (0 : Real)))
          (fun t : Real => Complex.exp (a * (t : Complex)) * A t) +
        integral (volume.restrict (Set.Ioi (0 : Real)))
          (fun t : Real => Complex.exp ((1 - a) * (t : Complex)) * B t)) := by
  let P := (volume : Measure Real).restrict (Set.Ioi 0)
  let N := (volume : Measure Real).restrict (Set.Iio 0)
  let e := MeasurableEquiv.neg Real
  let f (t : Real) := Complex.exp (a * (t : Complex)) * A t
  let g (t : Real) := Complex.exp ((1 - a) * (t : Complex)) * B t
  have hMP : MeasurePreserving e P N := by
    have h := (Measure.measurePreserving_neg (volume : Measure Real)).restrict_preimage
      (s := Set.Iio (0 : Real)) measurableSet_Iio
    have hPre : Set.preimage (fun t : Real => -t) (Set.Iio (0 : Real)) = Set.Ioi 0 := by
      ext t
      change -t < 0 <-> 0 < t
      exact neg_neg_iff_pos
    rw [hPre] at h
    exact h
  have hComp : Function.comp f e = g := by
    funext t
    change Complex.exp (a * ((-t : Real) : Complex)) * A (-t) = _
    rw [hReflection (-t), neg_neg, Complex.ofReal_neg, mul_left_comm, mul_neg, Complex.ofReal_exp]
    change Complex.exp (t : Complex) * (Complex.exp (-(a * (t : Complex))) * B t) = _
    rw [<- mul_assoc, <- Complex.exp_add, show (t : Complex) + -(a * (t : Complex)) =
      (1 - a) * (t : Complex) by ring]
  have hNeg : Integrable f N := by
    apply (hMP.integrable_comp_emb e.measurableEmbedding).mp
    rw [hComp]
    exact hB
  have hVol : (volume : Measure Real) = P + N := by
    have hDis : Disjoint (Set.Ioi (0 : Real)) (Set.Iic 0) := by
      apply Set.disjoint_left.mpr
      intro t htP htN
      exact (not_lt_of_ge (show t <= 0 from htN)) (show 0 < t from htP)
    have hUn : Union.union (Set.Ioi (0 : Real)) (Set.Iic 0) = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro t
      exact lt_or_ge 0 t
    change (volume : Measure Real) =
      volume.restrict (Set.Ioi (0 : Real)) + volume.restrict (Set.Iio (0 : Real))
    rw [restrict_Iio_eq_restrict_Iic, <- Measure.restrict_union hDis measurableSet_Iic,
      hUn, Measure.restrict_univ]
  have hI : integral N f = integral P g := by
    calc
      _ = integral P (Function.comp f e) := (hMP.integral_comp' f).symm
      _ = _ := by rw [hComp]
  change And (Integrable f volume) (integral volume f = integral P f + integral P g)
  refine And.intro ?_ ?_
  . rw [hVol]
    exact hA.add_measure hNeg
  . rw [hVol, integral_add_measure hA hNeg, hI]

/-- Fubini identifies the positive Mellin tail with the Mellin integral of
the theta function averaged over the norm-one classes. -/
theorem integrable_and_integral_heckeTateThetaAverage_log_positive
    [MeasurableSpace (C K)] [BorelSpace (C K)] (mu : Measure (C K)) [IsFiniteMeasure mu]
    (f : SchwartzMap (Mix K) Complex) (T : F K -> Complex)
    (chi : UnitaryHeckeCharacter K) (a : Complex)
    (hC : Continuous (fun p : Prod Real (C K) => heckeTateThetaNormOneClass f T p.1 p.2))
    (hWeight : Integrable (fun p : Prod Real (C K) =>
      norm (heckeTateThetaNormOneClass f T p.1 p.2) * Real.exp p.1 ^ a.re)
      (heckePositiveThetaMeasure mu)) :
    let R (t : Real) := Complex.exp (a * (t : Complex)) * integral mu (fun z : C K =>
      (heckeNormOneClassCharacter chi z : Complex) * heckeTateThetaNormOneClass f T t z)
    And (Integrable R (volume.restrict (Set.Ioi (0 : Real))))
      (integral (volume.restrict (Set.Ioi (0 : Real))) R =
        heckeTateThetaMellinTail mu f T chi a) := by
  let R (t : Real) := Complex.exp (a * (t : Complex)) * integral mu (fun z : C K =>
    (heckeNormOneClassCharacter chi z : Complex) * heckeTateThetaNormOneClass f T t z)
  let D (p : Prod Real (C K)) := Complex.exp (a * (p.1 : Complex)) *
    ((heckeNormOneClassCharacter chi p.2 : Complex) * heckeTateThetaNormOneClass f T p.1 p.2)
  let q := heckeNormOneClassCharacter chi
  have hq : Continuous (fun p : Prod Real (C K) => (q p.2 : Complex)) :=
    continuous_subtype_val.comp (q.continuous.comp continuous_snd)
  have hExp : Continuous (fun p : Prod Real (C K) => Complex.exp (a * (p.1 : Complex))) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))
  have hD : Continuous D := hExp.mul (hq.mul hC)
  have hIntegrable : Integrable D (heckePositiveThetaMeasure mu) := by
    refine hWeight.mono' hD.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => ?_))
    have hRe : (a * (p.1 : Complex)).re = a.re * p.1 := by simp [Complex.mul_re]
    rw [show D p = _ from rfl, norm_mul, norm_mul, Complex.norm_exp, Circle.norm_coe, one_mul, hRe,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm p.1 a.re, mul_comm]
  have hCalc (t : Real) : integral mu (fun z : C K => D (Prod.mk t z)) = R t := by
    unfold D R
    exact integral_const_mul (Complex.exp (a * (t : Complex))) (fun z : C K =>
      (heckeNormOneClassCharacter chi z : Complex) * heckeTateThetaNormOneClass f T t z)
  have hTail : integral (heckePositiveThetaMeasure mu) D = heckeTateThetaMellinTail mu f T chi a := by
    rw [heckeTateThetaMellinTail, heckeMellinTail]
    congr 1
    funext p
    rw [Real.log_exp]
    change Complex.exp (a * (p.1 : Complex)) * ((q p.2 : Complex) *
      heckeTateThetaNormOneClass f T p.1 p.2) = _
    ring
  change And (Integrable R _) (integral _ R = _)
  refine And.intro ?_ ?_
  . simpa only [hCalc] using hIntegrable.integral_prod_left
  . have hFubini := integral_prod D hIntegrable
    simp only [hCalc] at hFubini
    exact hFubini.symm.trans hTail

/-- Taking the contragredient twice recovers the unitary Hecke character. -/
theorem unitaryHeckeInverse_involutive (chi : UnitaryHeckeCharacter K) :
    unitaryHeckeInverse (unitaryHeckeInverse chi) = chi := by
  apply Subtype.ext
  ext a
  exact congrArg (fun z : Circle => (z : Complex)) (inv_inv (chi.val a))

private theorem heckeLocalAdditiveTateTest_inverse_conj
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K))
    (x : p.adicCompletion K) :
    heckeLocalAdditiveTateTest p (unitaryHeckeInverse chi) x =
      starRingEnd Complex (heckeLocalAdditiveTateTest p chi x) := by
  let opp := unitaryHeckeInverse chi
  let v := (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
  have hUnram : Iff (HeckeUnramifiedAt opp p) (HeckeUnramifiedAt chi p) := by
    rw [<- heckeConductorExponent_eq_zero_iff, <- heckeConductorExponent_eq_zero_iff,
      show heckeConductorExponent opp p = _ from heckeConductorExponent_inverse chi p]
  unfold heckeLocalAdditiveTateTest
  by_cases h : HeckeUnramifiedAt chi p
  . rw [if_pos (hUnram.mpr h), if_pos h]
    by_cases hx : v x <= 1
    . rw [if_pos hx, map_one]
    . rw [if_neg hx, map_zero]
  . rw [if_neg (fun hh => h (hUnram.mp hh)), if_neg h]
    by_cases hv : v x = 1
    . rw [dif_pos hv, dif_pos hv]
      change ((Inv.inv (chi.val (localIdeleHom K p (Inv.inv (Units.mk0 x _))))) : Circle) =
        starRingEnd Complex _
      exact Circle.coe_inv_eq_conj _
    . rw [dif_neg hv, dif_neg hv, map_zero]

/-- The inverse Hecke character's finite Tate test is the complex conjugate
of the original finite test at every finite adele. -/
theorem heckeFiniteAdditiveTateTest_inverse_conj
    (chi : UnitaryHeckeCharacter K) (x : F K) :
    heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi) x =
      starRingEnd Complex (heckeFiniteAdditiveTateTest chi x) := by
  unfold heckeFiniteAdditiveTateTest
  by_cases hx : Membership.mem (heckeIntegralFiniteAdeles (K := K)) x
  . rw [if_pos hx, if_pos hx, heckeRamifiedFinset_inverse, map_prod]
    apply Finset.prod_congr rfl
    intro p _
    exact heckeLocalAdditiveTateTest_inverse_conj chi p (x p)
  . rw [if_neg hx, if_neg hx, map_zero]

private theorem tate_int_toNat_eq_natAbs (m : Int) (hm : 0 <= m) :
    m.toNat = m.natAbs := by
  cases m with
  | ofNat n => rfl
  | negSucc n => exact ((Int.negSucc_lt_zero n).not_ge hm).elim

private def tateComplexMonomial (m : Int) (z : Complex) : Complex :=
  if 0 <= m then (starRingEnd Complex z) ^ m.toNat else z ^ m.natAbs

private theorem tateComplexMonomial_neg (m : Int) (z : Complex) :
    tateComplexMonomial (-m) z = starRingEnd Complex (tateComplexMonomial m z) := by
  unfold tateComplexMonomial
  by_cases hZero : m = 0
  . subst m
    simp only [neg_zero, if_pos (le_refl (0 : Int)), Int.toNat_zero, pow_zero, map_one]
  . by_cases hPos : 0 <= m
    . have hNeg : Not (0 <= -m) := by omega
      rw [if_neg hNeg, if_pos hPos, Int.natAbs_neg, tate_int_toNat_eq_natAbs m hPos,
        map_pow, starRingEnd_apply, starRingEnd_apply, star_star]
    . have hPosNeg : 0 <= -m := by omega
      rw [if_pos hPosNeg, if_neg hPos, tate_int_toNat_eq_natAbs (-m) hPosNeg,
        Int.natAbs_neg, map_pow]

/-- The inverse Hecke character's canonical archimedean test is obtained by
conjugating its polynomial Gaussian at every infinite adele. -/
theorem heckeTateInfiniteTest_inverse_conj
    (chi : UnitaryHeckeCharacter K) (x : Mix K) :
    heckeTateInfiniteTest (unitaryHeckeInverse chi) x =
      starRingEnd Complex (heckeTateInfiniteTest chi x) := by
  let opp := unitaryHeckeInverse chi
  let R := {v : InfinitePlace K // v.IsReal}
  let C := {v : InfinitePlace K // v.IsComplex}
  let f (xi : UnitaryHeckeCharacter K) (v : R) : Complex :=
    (x.1 v : Complex) ^ (realInfiniteHeckeParameters xi v.property).1 *
      (Real.exp (-Real.pi * (x.1 v) ^ 2) : Complex)
  let g (xi : UnitaryHeckeCharacter K) (v : C) : Complex :=
    tateComplexMonomial (complexInfiniteHeckeParameters xi v.property).1 (x.2 v) *
      (Real.exp (-2 * Real.pi * norm (x.2 v) ^ 2) : Complex)
  change Finset.univ.prod (f opp) * Finset.univ.prod (g opp) =
    starRingEnd Complex (Finset.univ.prod (f chi) * Finset.univ.prod (g chi))
  rw [map_mul, map_prod, map_prod]
  congr 1
  . apply Finset.prod_congr rfl
    intro v _
    unfold f
    rw [realInfiniteHeckeParameters_inverse_parity, map_mul, map_pow]
    rw [Complex.conj_ofReal, Complex.conj_ofReal]
  . apply Finset.prod_congr rfl
    intro v _
    unfold g
    rw [complexInfiniteHeckeParameters_inverse_weight, tateComplexMonomial_neg, map_mul]
    rw [Complex.conj_ofReal]

/-- The canonical theta sum for the inverse character is the conjugate of
the theta sum for the original character. -/
theorem heckeTateThetaNormOneClass_inverse_conj
    (chi : UnitaryHeckeCharacter K) (f g : SchwartzMap (Mix K) Complex)
    (hf : forall x, f x = heckeTateInfiniteTest chi x)
    (hg : forall x, g x = heckeTateInfiniteTest (unitaryHeckeInverse chi) x)
    (t : Real) (z : C K) :
    heckeTateThetaNormOneClass g
      (heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi)) t z =
      starRingEnd Complex (heckeTateThetaNormOneClass f (heckeFiniteAdditiveTateTest chi) t z) := by
  choose b hb using QuotientGroup.mk'_surjective (heckePrincipalNormOneIdele K).range z
  rw [<- hb, heckeTateThetaNormOneClass_mk, heckeTateThetaNormOneClass_mk]
  unfold heckeTateThetaNormOne
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro x
  by_cases hx : x = 0
  . simp only [heckeTateThetaNormOneTerm, if_pos hx, map_zero]
  . have hG (y : Mix K) : g y = starRingEnd Complex (f y) :=
      (hg y).trans ((heckeTateInfiniteTest_inverse_conj chi y).trans
        (congrArg (starRingEnd Complex) (hf y).symm))
    rw [heckeTateThetaNormOneTerm, if_neg hx, heckeTateThetaNormOneTerm, if_neg hx,
      hG, heckeFiniteAdditiveTateTest_inverse_conj, map_mul]

/-- Character averaging preserves the conjugation identity of the
canonical inverse tests. -/
theorem heckeTateCharacterThetaAverage_inverse_conj
    [MeasurableSpace (C K)] (mu : Measure (C K))
    (chi : UnitaryHeckeCharacter K) (f g : SchwartzMap (Mix K) Complex)
    (hf : forall x, f x = heckeTateInfiniteTest chi x)
    (hg : forall x, g x = heckeTateInfiniteTest (unitaryHeckeInverse chi) x)
    (t : Real) :
    heckeTateCharacterThetaAverage mu (unitaryHeckeInverse chi) g
      (heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi)) t =
      starRingEnd Complex
        (heckeTateCharacterThetaAverage mu chi f (heckeFiniteAdditiveTateTest chi) t) := by
  let q := heckeNormOneClassCharacter chi
  let Q := heckeNormOneClassCharacter (unitaryHeckeInverse chi)
  let f0 (z : C K) := (q z : Complex) *
    heckeTateThetaNormOneClass f (heckeFiniteAdditiveTateTest chi) t z
  have hI : integral mu (fun z : C K => starRingEnd Complex (f0 z)) =
      starRingEnd Complex (integral mu f0) := integral_conj
  change _ = starRingEnd Complex (integral mu f0)
  rw [<- hI]
  apply integral_congr_ae
  filter_upwards with z
  have hQ : (Q z : Complex) = starRingEnd Complex (q z : Complex) := by
    rw [show Q z = q (Inv.inv z) from (heckeNormOneClassCharacter_on_inv chi z).symm,
      map_inv, Circle.coe_inv_eq_conj]
  change (Q z : Complex) * heckeTateThetaNormOneClass g
    (heckeFiniteAdditiveTateTest (unitaryHeckeInverse chi)) t z = _
  rw [hQ, heckeTateThetaNormOneClass_inverse_conj chi f g hf hg]
  exact (map_mul (starRingEnd Complex) _ _).symm

/-- The untruncated radial Mellin integral coincides with the two entire
Mellin tails of the primary and Fourier-dual tests. -/
theorem integral_heckeTateCharacterThetaAverage_eq_two_mellinTails
    [MeasurableSpace (C K)] [BorelSpace (C K)]
    [MeasurableSpace (F K)] [BorelSpace (F K)]
    (mu : Measure (C K)) [IsFiniteMeasure mu] [mu.IsMulLeftInvariant]
    (hInv : MeasurePreserving Inv.inv mu mu)
    (chi : UnitaryHeckeCharacter K) (z : C K)
    (hz : Not (heckeNormOneClassCharacter chi z = 1))
    (f : SchwartzMap (Mix K) Complex) (a : Complex) :
    integral volume (fun t : Real => Complex.exp (a * (t : Complex)) *
      heckeTateCharacterThetaAverage mu chi f (heckeFiniteAdditiveTateTest chi) t) =
      heckeTateThetaMellinTail mu f (heckeFiniteAdditiveTateTest chi) chi a +
      heckeTateThetaMellinTail mu (heckeTateDualInfiniteTest f) (heckeTateDualFiniteTest chi)
        (unitaryHeckeInverse chi) (1 - a) := by
  let T := heckeFiniteAdditiveTateTest chi
  let TD := heckeTateDualFiniteTest chi
  let fD := heckeTateDualInfiniteTest f
  let opp := unitaryHeckeInverse chi
  let U := heckeIntegralFiniteAdeles (K := K)
  have hTzero (y : F K) (hy : Not (Membership.mem (U : Set (F K)) y)) : T y = 0 := by
    change Not (Membership.mem U y) at hy
    rw [show T = heckeFiniteAdditiveTateTest chi from rfl, heckeFiniteAdditiveTateTest, if_neg hy]
  have hTC := continuous_heckeFiniteAdditiveTateTest chi
  have hPC := continuous_heckeTateThetaNormOneClass_joint f T hTC
    (U : Set (F K)) isCompact_integralFiniteAdeles hTzero 1 zero_le_one
    (norm_heckeFiniteAdditiveTateTest_le_one chi)
  choose V B hV using heckeTateDualFiniteTest_support_and_bound chi
  have hTDC : Continuous TD := by
    change Continuous (fun y : F K =>
      Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
        heckeFiniteFourierIntegral heckeFiniteAdeleHaar (heckeFiniteAdditiveTateTest chi) (-y))
    exact continuous_const.mul
      ((continuous_heckeFiniteFourierIntegral_TateTest heckeFiniteAdeleHaar chi).comp continuous_neg)
  have hDC := continuous_heckeTateThetaNormOneClass_joint fD TD hTDC V hV.1
    hV.2.2.1 B hV.2.1 hV.2.2.2
  have hP := integrable_and_integral_heckeTateThetaAverage_log_positive mu f T chi a hPC
    (integrable_heckeTateThetaNormOneClass_character_expMoment mu f chi a.re)
  have hD := integrable_and_integral_heckeTateThetaAverage_log_positive mu fD TD opp (1 - a) hDC
    (integrable_heckeTateThetaNormOneClass_expMoment mu fD TD hTDC V hV.1
      hV.2.2.1 B hV.2.1 hV.2.2.2 (1 - a).re)
  let A := heckeTateCharacterThetaAverage mu chi f T
  let G := heckeTateCharacterThetaAverage mu opp fD TD
  have hPoint (t : Real) : A t = (Real.exp (-t) : Complex) * G (-t) := by
    have hArg (w : Real) : Continuous (fun y : C K => Prod.mk w y) :=
      continuous_const.prodMk continuous_id
    have hFP : Continuous (heckeTateThetaNormOneClass f T t) := by
      have h := hPC.comp (hArg t)
      simpa only [Function.comp_def] using h
    have hFD : Continuous (heckeTateThetaNormOneClass fD TD (-t)) := by
      have h := hDC.comp (hArg (-t))
      simpa only [Function.comp_def] using h
    exact heckeTateCharacterThetaAverage_poisson mu hInv chi z hz f t hFP hFD
  have hBoth := integral_tateLogWeight_eq_two_positive A G a hPoint hP.1 hD.1
  rw [hBoth.2]
  exact congrArg (fun v : Complex => v + _) hP.2 |>.trans
    (congrArg (fun v : Complex => _ + v) hD.2)

end Robin1984.GRH
