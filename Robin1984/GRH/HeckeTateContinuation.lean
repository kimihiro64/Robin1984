import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Robin1984.GRH.HeckeTateClassPoisson

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's analytic continuation of completed Hecke L-functions.
- Formalization note: Splits the class theta integral by logarithmic norm and constructs the entire completion for characters nontrivial on the norm-one idele classes.
- PROVENANCE-END
-/

/-!
# Entire continuation of Hecke L-functions from Tate's integral

For a unitary Hecke character that is nontrivial on the norm-one idele classes,
the two zero terms cancel after integration. The two remaining integrals are
entire positive Mellin tails. Their sum agrees with the actual Gamma-completed
Euler product on the half-plane of absolute convergence.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open MeasureTheory

private theorem measurePreserving_neg_restrict_log_positive :
    MeasurePreserving (fun t : Real => -t)
      (volume.restrict (Set.Ioi (0 : Real))) (volume.restrict (Set.Iio (0 : Real))) := by
  have h := (Measure.measurePreserving_neg (volume : Measure Real)).restrict_preimage
    (s := Set.Iio (0 : Real)) measurableSet_Iio
  have hPre : Set.preimage (fun t : Real => -t) (Set.Iio (0 : Real)) = Set.Ioi 0 := by
    ext t
    change -t < 0 <-> 0 < t
    exact neg_neg_iff_pos
  rw [hPre] at h
  exact h

private theorem integral_log_pos_add_log_neg
    {G : Type*} [MeasurableSpace G] (mu : Measure G) [SFinite mu]
    (F : Prod Real G -> Complex)
    (hPos : Integrable F ((volume.restrict (Set.Ioi (0 : Real))).prod mu))
    (hNeg : Integrable F ((volume.restrict (Set.Iio (0 : Real))).prod mu)) :
    integral (volume.prod mu) F =
      integral ((volume.restrict (Set.Ioi (0 : Real))).prod mu) F +
        integral ((volume.restrict (Set.Iio (0 : Real))).prod mu) F := by
  have hDis : Disjoint (Set.Ioi (0 : Real)) (Set.Iic 0) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge (show x <= 0 from hy)) (show 0 < x from hx)
  have hUn : Union.union (Set.Ioi (0 : Real)) (Set.Iic 0) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    exact (lt_or_ge 0 x)
  have hVol : (volume : Measure Real) =
      volume.restrict (Set.Ioi (0 : Real)) + volume.restrict (Set.Iio (0 : Real)) := by
    rw [restrict_Iio_eq_restrict_Iic]
    rw [<- Measure.restrict_union hDis measurableSet_Iic, hUn, Measure.restrict_univ]
  have hProd : (volume : Measure Real).prod mu =
      (volume.restrict (Set.Ioi (0 : Real))).prod mu +
        (volume.restrict (Set.Iio (0 : Real))).prod mu := by
    calc
      (volume : Measure Real).prod mu = _ := congrArg (fun m : Measure Real => m.prod mu) hVol
      _ = _ := Measure.add_prod _
  rw [hProd, integral_add_measure hPos hNeg]

private theorem integrable_exp_weight_log_positive
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [IsFiniteMeasure mu] (q : ContinuousMonoidHom G Circle)
    (a : Complex) (ha : a.re < 0) :
    Integrable (fun p : Prod Real G => Complex.exp (a * (p.1 : Complex)) * (q p.2 : Complex))
      ((volume.restrict (Set.Ioi (0 : Real))).prod mu) := by
  have hRad : Integrable (fun t : Real => Complex.exp (a * (t : Complex)))
      (volume.restrict (Set.Ioi (0 : Real))) := integrableOn_exp_mul_complex_Ioi ha 0
  have hChar : Integrable (fun z : G => (q z : Complex)) mu := by
    have hC : Continuous (fun z : G => (q z : Complex)) :=
      continuous_subtype_val.comp q.continuous
    have hOne : Integrable (fun _ : G => (1 : Real)) mu := integrable_const 1
    refine hOne.mono' hC.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun z => (Circle.norm_coe (q z)).le)
  exact hRad.mul_prod hChar

private theorem integral_exp_weight_log_positive_eq_zero
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalGroup G]
    (mu : Measure G) [IsFiniteMeasure mu] [mu.IsMulLeftInvariant]
    (q : ContinuousMonoidHom G Circle) (z : G) (hz : Not (q z = 1))
    (a : Complex) :
    integral ((volume.restrict (Set.Ioi (0 : Real))).prod mu)
      (fun p : Prod Real G => Complex.exp (a * (p.1 : Complex)) * (q p.2 : Complex)) = 0 := by
  let F (t : Real) := Complex.exp (a * (t : Complex))
  let H (y : G) : Complex := q y
  have hProd : integral ((volume.restrict (Set.Ioi (0 : Real))).prod mu)
      (fun p : Prod Real G => F p.1 * H p.2) =
      integral (volume.restrict (Set.Ioi (0 : Real))) F * integral mu H :=
    integral_prod_mul F H
  change integral ((volume.restrict (Set.Ioi (0 : Real))).prod mu)
    (fun p : Prod Real G => F p.1 * H p.2) = 0
  rw [hProd, show integral mu H = 0 from integral_continuousCircleCharacter_eq_zero mu q z hz,
    mul_zero]

private theorem integral_tate_reflection_split
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    (mu : Measure G) [SFinite mu] (hInv : MeasurePreserving Inv.inv mu mu)
    (F D E0 E1 : Prod Real G -> Complex)
    (hF : Integrable F ((volume.restrict (Set.Ioi (0 : Real))).prod mu))
    (hD : Integrable D ((volume.restrict (Set.Ioi (0 : Real))).prod mu))
    (hE0 : Integrable E0 ((volume.restrict (Set.Ioi (0 : Real))).prod mu))
    (hE1 : Integrable E1 ((volume.restrict (Set.Ioi (0 : Real))).prod mu))
    (hE0Zero : integral ((volume.restrict (Set.Ioi (0 : Real))).prod mu) E0 = 0)
    (hE1Zero : integral ((volume.restrict (Set.Ioi (0 : Real))).prod mu) E1 = 0)
    (hEq : forall p, F (Prod.mk (-p.1) (Inv.inv p.2)) = D p + E0 p - E1 p) :
    integral (volume.prod mu) F =
      integral ((volume.restrict (Set.Ioi (0 : Real))).prod mu) F +
        integral ((volume.restrict (Set.Ioi (0 : Real))).prod mu) D := by
  let P : Measure (Prod Real G) := (volume.restrict (Set.Ioi (0 : Real))).prod mu
  let N : Measure (Prod Real G) := (volume.restrict (Set.Iio (0 : Real))).prod mu
  let e := MeasurableEquiv.prodCongr (MeasurableEquiv.neg Real) (MeasurableEquiv.inv G)
  have hMP : MeasurePreserving e P N :=
    MeasurePreserving.prod measurePreserving_neg_restrict_log_positive hInv
  have hR : Function.comp F e = (fun p => D p + E0 p - E1 p) := funext hEq
  have hReflected : Integrable (Function.comp F e) P := by
    rw [hR]
    exact (hD.add hE0).sub hE1
  have hNeg : Integrable F N := (hMP.integrable_comp_emb e.measurableEmbedding).mp hReflected
  have hReflectIntegral : integral N F = integral P (Function.comp F e) :=
    (hMP.integral_comp' F).symm
  change integral (volume.prod mu) F = integral P F + integral P D
  rw [integral_log_pos_add_log_neg mu F hF hNeg]
  change integral P F + integral N F = _
  have hSub : integral P (fun p => D p + E0 p - E1 p) =
      integral P (fun p => D p + E0 p) - integral P E1 :=
    integral_sub (hD.add hE0) hE1
  have hAdd : integral P (fun p => D p + E0 p) = integral P D + integral P E0 :=
    integral_add hD hE0
  change integral P E0 = 0 at hE0Zero
  change integral P E1 = 0 at hE1Zero
  rw [hReflectIntegral, hR, hSub, hAdd, hE0Zero, hE1Zero, add_zero, sub_zero]

open IsDedekindDomain NumberField
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev TClass (K : Type*) [Field K] [NumberField K] := heckeNormOneIdeleClass K
private abbrev TFinite (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K
private abbrev TMixed (K : Type*) [Field K] := mixedEmbedding.mixedSpace K
private abbrev TCoordinates (K : Type*) [Field K] [NumberField K] := Prod Real (TClass K)

/-- The character on the exponential section contributes a purely imaginary
shift to the positive Tate Mellin integral. -/
theorem exists_heckeTateClassZeta_mellinTail_shift
    [MeasurableSpace (heckeNormOneIdeleClass K)] (chi : UnitaryHeckeCharacter K) :
    exists tau : Real,
      And (forall t : Real, (chi.val (heckeIdelicExpSection K t) : Complex) =
          Complex.exp (((tau * t : Real) : Complex) * Complex.I))
        (forall (mu : Measure (heckeNormOneIdeleClass K))
          (f : SchwartzMap (mixedEmbedding.mixedSpace K) Complex)
          (T : FiniteAdeleRing (RingOfIntegers K) K -> Complex) (s : Complex),
          integral (heckePositiveThetaMeasure mu) (heckeTateClassZetaIntegrand chi s f T) =
            heckeTateThetaMellinTail mu f T chi (s + (tau : Complex) * Complex.I)) := by
  let g (t : Real) := (chi.val (heckeIdelicExpSection K t) : Complex)
  have hg : Continuous g :=
    continuous_subtype_val.comp (chi.val.continuous.comp (continuous_heckeIdelicExpSection K))
  have h0 : g 0 = 1 := by simp [g]
  have hMul (x y : Real) : g (x + y) = g x * g y := by
    simp only [g, heckeIdelicExpSection_add, map_mul, Circle.coe_mul]
  choose tau htau using exists_frequency_of_continuous_unitary_character g hg h0 hMul
    (fun t => Circle.norm_coe (chi.val (heckeIdelicExpSection K t)))
  refine Exists.intro tau (And.intro htau ?_)
  intro mu f T s
  rw [heckeTateThetaMellinTail, heckeMellinTail]
  congr 1
  funext p
  rw [heckeTateClassZetaIntegrand, show (chi.val (heckeIdelicExpSection K p.1) : Complex) = _
    from htau p.1, Real.log_exp, add_mul, Complex.exp_add]
  have hExp : (((tau * p.1 : Real) : Complex) * Complex.I) =
      (tau : Complex) * Complex.I * (p.1 : Complex) := by push_cast; ring
  rw [hExp]
  ring

private theorem heckeNormOneClassCharacter_inverse_apply (chi : UnitaryHeckeCharacter K)
    (z : TClass K) :
    heckeNormOneClassCharacter (unitaryHeckeInverse chi) z =
      Inv.inv (heckeNormOneClassCharacter chi z) := by
  choose a ha using QuotientGroup.mk'_surjective (heckePrincipalNormOneIdele K).range z
  rw [<- ha, heckeNormOneClassCharacter_mk, heckeNormOneClassCharacter_mk]
  rfl

private def radialWeightedTheta
    (f : SchwartzMap (TMixed K) Complex) (T : TFinite K -> Complex)
    (chi : UnitaryHeckeCharacter K) (a : Complex) (p : TCoordinates K) : Complex :=
  (Complex.exp (a * (p.1 : Complex)) *
    (heckeNormOneClassCharacter chi p.2 : Complex)) * heckeTateThetaNormOneClass f T p.1 p.2

private theorem integral_radialWeightedTheta_eq_tail
    [MeasurableSpace (TClass K)] (mu : Measure (TClass K))
    (f : SchwartzMap (TMixed K) Complex) (T : TFinite K -> Complex)
    (chi : UnitaryHeckeCharacter K) (a : Complex) :
    integral (heckePositiveThetaMeasure mu) (radialWeightedTheta f T chi a) =
      heckeTateThetaMellinTail mu f T chi a := by
  rw [heckeTateThetaMellinTail, heckeMellinTail]
  congr 1
  funext p
  rw [radialWeightedTheta, Real.log_exp]
  ring

private theorem integrable_radialWeightedTheta_of_moment
    [MeasurableSpace (TClass K)] [BorelSpace (TClass K)]
    (mu : Measure (TClass K)) (f : SchwartzMap (TMixed K) Complex)
    (T : TFinite K -> Complex) (chi : UnitaryHeckeCharacter K) (a : Complex)
    (hC : Continuous (fun p : TCoordinates K => heckeTateThetaNormOneClass f T p.1 p.2))
    (hI : Integrable (fun p : TCoordinates K =>
      norm (heckeTateThetaNormOneClass f T p.1 p.2) * (Real.exp p.1) ^ a.re)
      (heckePositiveThetaMeasure mu)) :
    Integrable (radialWeightedTheta f T chi a) (heckePositiveThetaMeasure mu) := by
  let q := heckeNormOneClassCharacter chi
  have hq : Continuous (fun p : TCoordinates K => (q p.2 : Complex)) :=
    continuous_subtype_val.comp (q.continuous.comp continuous_snd)
  have hExp : Continuous (fun p : TCoordinates K => Complex.exp (a * (p.1 : Complex))) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))
  have hF : Continuous (radialWeightedTheta f T chi a) := (hExp.mul hq).mul hC
  refine hI.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => ?_))
  have hRe : (a * (p.1 : Complex)).re = a.re * p.1 := by simp [Complex.mul_re]
  rw [radialWeightedTheta, norm_mul, norm_mul, Complex.norm_exp, Circle.norm_coe, mul_one, hRe,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm p.1 a.re, mul_comm]

private theorem radialWeightedTheta_reflect
    [MeasurableSpace (TFinite K)] [BorelSpace (TFinite K)]
    (chi : UnitaryHeckeCharacter K) (f : SchwartzMap (TMixed K) Complex)
    (a : Complex) (p : TCoordinates K) :
    radialWeightedTheta f (heckeFiniteAdditiveTateTest chi) chi a (Prod.mk (-p.1) (Inv.inv p.2)) =
      radialWeightedTheta (heckeTateDualInfiniteTest f) (heckeTateDualFiniteTest chi)
        (unitaryHeckeInverse chi) (1 - a) p +
      (Complex.exp ((1 - a) * (p.1 : Complex)) *
        (heckeNormOneClassCharacter (unitaryHeckeInverse chi) p.2 : Complex)) *
          (heckeTateDualInfiniteTest f 0 * heckeTateDualFiniteTest chi 0) -
      (Complex.exp (-a * (p.1 : Complex)) *
        (heckeNormOneClassCharacter (unitaryHeckeInverse chi) p.2 : Complex)) *
          (f 0 * heckeFiniteAdditiveTateTest chi 0) := by
  have hP := heckeTateThetaNormOneClass_poisson chi f (-p.1) (Inv.inv p.2)
  have hII : Inv.inv (Inv.inv p.2) = p.2 := inv_inv p.2
  rw [neg_neg, hII] at hP
  have hT := eq_sub_of_add_eq hP
  have hQ : (heckeNormOneClassCharacter chi (Inv.inv p.2) : Complex) =
      (heckeNormOneClassCharacter (unitaryHeckeInverse chi) p.2 : Complex) := by
    rw [map_inv, heckeNormOneClassCharacter_inverse_apply]
  have hNeg : Complex.exp (a * ((-p.1 : Real) : Complex)) =
      Complex.exp (-a * (p.1 : Complex)) := by
    rw [Complex.ofReal_neg, mul_neg, neg_mul]
  have hExp : Complex.exp (-a * (p.1 : Complex)) * (Real.exp p.1 : Complex) =
      Complex.exp ((1 - a) * (p.1 : Complex)) := by
    rw [Complex.ofReal_exp, <- Complex.exp_add]
    congr 1
    ring
  simp only [radialWeightedTheta, hQ, hNeg, hT]
  rw [<- hExp]
  ring

/-- For a Hecke character nontrivial on the norm-one classes, the adelic
zeta integral is the sum of two positive Mellin tails. The two correction
terms from the Poisson formula have zero Haar integral. -/
theorem integral_heckeTateClassZeta_eq_two_mellinTails
    [MeasurableSpace (TClass K)] [BorelSpace (TClass K)]
    [MeasurableSpace (TFinite K)] [BorelSpace (TFinite K)]
    (mu : Measure (TClass K)) [IsFiniteMeasure mu] [mu.IsMulLeftInvariant]
    (hInv : MeasurePreserving Inv.inv mu mu)
    (chi : UnitaryHeckeCharacter K) (z : TClass K)
    (hz : Not (heckeNormOneClassCharacter chi z = 1))
    (f : SchwartzMap (TMixed K) Complex) :
    exists tau : Real, forall s : Complex, 1 < s.re ->
      integral (volume.prod mu)
        (heckeTateClassZetaIntegrand chi s f (heckeFiniteAdditiveTateTest chi)) =
        heckeTateThetaMellinTail mu f (heckeFiniteAdditiveTateTest chi) chi
          (s + (tau : Complex) * Complex.I) +
        heckeTateThetaMellinTail mu (heckeTateDualInfiniteTest f) (heckeTateDualFiniteTest chi)
          (unitaryHeckeInverse chi) (1 - (s + (tau : Complex) * Complex.I)) := by
  let opp := unitaryHeckeInverse chi
  have hzOpp : Not (heckeNormOneClassCharacter opp z = 1) := by
    intro h
    apply hz
    change heckeNormOneClassCharacter (unitaryHeckeInverse chi) z = 1 at h
    rw [heckeNormOneClassCharacter_inverse_apply] at h
    simpa only [inv_inv, inv_one] using congrArg Inv.inv h
  choose tau hTau using exists_heckeTateClassZeta_mellinTail_shift chi
  refine Exists.intro tau ?_
  intro s hs
  let a := s + (tau : Complex) * Complex.I
  let P := heckePositiveThetaMeasure mu
  let fD := heckeTateDualInfiniteTest f
  let T := heckeFiniteAdditiveTateTest chi
  let TD := heckeTateDualFiniteTest chi
  let F := radialWeightedTheta f T chi a
  let D := radialWeightedTheta fD TD opp (1 - a)
  let W (b : Complex) (p : TCoordinates K) :=
    Complex.exp (b * (p.1 : Complex)) * (heckeNormOneClassCharacter opp p.2 : Complex)
  let E0 (p : TCoordinates K) := W (1 - a) p * (fD 0 * TD 0)
  let E1 (p : TCoordinates K) := W (-a) p * (f 0 * T 0)
  have hEq : heckeTateClassZetaIntegrand chi s f T = F := by
    funext p
    rw [heckeTateClassZetaIntegrand, hTau.1 p.1]
    have hExp : (s * (p.1 : Complex)) + ((tau * p.1 : Real) : Complex) * Complex.I =
        a * (p.1 : Complex) := by dsimp only [a]; push_cast; ring
    rw [<- Complex.exp_add, hExp]
    rfl
  let U := heckeIntegralFiniteAdeles (K := K)
  have hTzero (y : TFinite K) (hy : Not (Membership.mem (U : Set (TFinite K)) y)) :
      T y = 0 := by
    have hy' : Not (Membership.mem U y) := hy
    rw [show T = heckeFiniteAdditiveTateTest chi from rfl, heckeFiniteAdditiveTateTest, if_neg hy']
  have hTnorm : forall y, norm (T y) <= 1 := norm_heckeFiniteAdditiveTateTest_le_one chi
  have hTC : Continuous T := continuous_heckeFiniteAdditiveTateTest chi
  have hFC := continuous_heckeTateThetaNormOneClass_joint f T hTC
    (U : Set (TFinite K)) isCompact_integralFiniteAdeles hTzero 1 zero_le_one hTnorm
  have hFi : Integrable F P := integrable_radialWeightedTheta_of_moment mu f T chi a hFC
    (integrable_heckeTateThetaNormOneClass_character_expMoment mu f chi a.re)
  choose V B hVB using heckeTateDualFiniteTest_support_and_bound chi
  have hTDC : Continuous TD := by
    change Continuous (fun y : TFinite K =>
      Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
        heckeFiniteFourierIntegral heckeFiniteAdeleHaar (heckeFiniteAdditiveTateTest chi) (-y))
    exact continuous_const.mul
      ((continuous_heckeFiniteFourierIntegral_TateTest heckeFiniteAdeleHaar chi).comp continuous_neg)
  have hDC := continuous_heckeTateThetaNormOneClass_joint fD TD hTDC
    V hVB.1 hVB.2.2.1 B hVB.2.1 hVB.2.2.2
  have hDi : Integrable D P := integrable_radialWeightedTheta_of_moment mu fD TD opp (1 - a) hDC
    (integrable_heckeTateThetaNormOneClass_expMoment mu fD TD hTDC
      V hVB.1 hVB.2.2.1 B hVB.2.1 hVB.2.2.2 (1 - a).re)
  have haRe : a.re = s.re := by simp only [a, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_self, add_zero]
  have hCorr0 : (1 - a).re < 0 := by rw [Complex.sub_re, Complex.one_re, haRe]; exact sub_neg.mpr hs
  have hCorr1 : (-a).re < 0 := by rw [Complex.neg_re, haRe, neg_neg_iff_pos]; exact zero_lt_one.trans hs
  have hE0 : Integrable E0 P :=
    (integrable_exp_weight_log_positive mu (heckeNormOneClassCharacter opp) (1 - a) hCorr0).mul_const _
  have hE1 : Integrable E1 P :=
    (integrable_exp_weight_log_positive mu (heckeNormOneClassCharacter opp) (-a) hCorr1).mul_const _
  have hW0 (b : Complex) : integral P (W b) = 0 :=
    integral_exp_weight_log_positive_eq_zero mu (heckeNormOneClassCharacter opp) z hzOpp b
  have hZ0 : integral P E0 = 0 := by rw [show E0 = _ from rfl, integral_mul_const, hW0, zero_mul]
  have hZ1 : integral P E1 = 0 := by rw [show E1 = _ from rfl, integral_mul_const, hW0, zero_mul]
  have hSplit := integral_tate_reflection_split mu hInv F D E0 E1
    hFi hDi hE0 hE1 hZ0 hZ1 (radialWeightedTheta_reflect chi f a)
  rw [hEq, hSplit]
  have hL := integral_radialWeightedTheta_eq_tail mu f T chi a
  have hR := integral_radialWeightedTheta_eq_tail mu fD TD opp (1 - a)
  change integral P F = _ at hL
  change integral P D = _ at hR
  change integral P F + integral P D = _
  rw [hL, hR]

/-- The actual Gamma-completed Hecke Euler product has an entire continuation
when the character is nontrivial on the norm-one idele classes. -/
theorem exists_entire_heckeCompletedEulerL_of_nontrivial_normOne
    (chi : UnitaryHeckeCharacter K) (z : TClass K)
    (hz : Not (heckeNormOneClassCharacter chi z = 1)) :
    exists L : Complex -> Complex,
      And (Differentiable Complex L)
        (forall s : Complex, 1 < s.re ->
          L s =
            ((Finset.univ.prod (fun v : {w : InfinitePlace K // w.IsReal} =>
              DedekindZeta.LReal (s + realInfiniteHeckeShift chi v.property))) *
             (Finset.univ.prod (fun v : {w : InfinitePlace K // w.IsComplex} =>
              DedekindZeta.LComplex (s + complexInfiniteHeckeShift chi v.property)))) *
              heckeEulerL K chi s) := by
  let : MeasurableSpace (Units (TMixed K)) := borel _
  let : BorelSpace (Units (TMixed K)) := BorelSpace.mk rfl
  let : MeasurableSpace (TFinite K) := borel _
  let : BorelSpace (TFinite K) := BorelSpace.mk rfl
  let : MeasurableSpace (Units (TFinite K)) := borel _
  let : BorelSpace (Units (TFinite K)) := BorelSpace.mk rfl
  let : MeasurableSpace (Units (AdeleRing (RingOfIntegers K) K)) := borel _
  let : BorelSpace (Units (AdeleRing (RingOfIntegers K) K)) := BorelSpace.mk rfl
  let : MeasurableSpace (heckeNormOneIdeles K) := borel _
  let : BorelSpace (heckeNormOneIdeles K) := BorelSpace.mk rfl
  let : MeasurableSpace (heckeIdeleClass K) := borel _
  let : BorelSpace (heckeIdeleClass K) := BorelSpace.mk rfl
  let : MeasurableSpace (TClass K) := borel _
  let : BorelSpace (TClass K) := BorelSpace.mk rfl
  let F := Units (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)
  let : MeasurableSpace F := Top.top
  let : MeasurableSingletonClass F := MeasurableSingletonClass.mk (fun _ => trivial)
  choose mu hMu using exists_heckeTateClassThetaEulerMeasure (K := K)
  let : IsFiniteMeasure mu := hMu.1
  let : mu.IsMulLeftInvariant := hMu.2.1
  choose f hEuler using hMu.2.2.2 chi
  choose tau hS using integral_heckeTateClassZeta_eq_two_mellinTails mu hMu.2.2.1 chi z hz f
  let fD := heckeTateDualInfiniteTest f
  let T := heckeFiniteAdditiveTateTest chi
  let TD := heckeTateDualFiniteTest chi
  let U := heckeIntegralFiniteAdeles (K := K)
  have hTzero (y : TFinite K) (hy : Not (Membership.mem (U : Set (TFinite K)) y)) :
      T y = 0 := by
    have hy' : Not (Membership.mem U y) := hy
    rw [show T = heckeFiniteAdditiveTateTest chi from rfl, heckeFiniteAdditiveTateTest, if_neg hy']
  have hTnorm : forall y, norm (T y) <= 1 := norm_heckeFiniteAdditiveTateTest_le_one chi
  have hTC : Continuous T := continuous_heckeFiniteAdditiveTateTest chi
  have hPrim := differentiable_heckeTateThetaMellinTail mu f T hTC
    (U : Set (TFinite K)) isCompact_integralFiniteAdeles hTzero 1 zero_le_one hTnorm chi
  choose V B hVB using heckeTateDualFiniteTest_support_and_bound chi
  have hTDC : Continuous TD := by
    change Continuous (fun y : TFinite K =>
      Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
        heckeFiniteFourierIntegral heckeFiniteAdeleHaar (heckeFiniteAdditiveTateTest chi) (-y))
    exact continuous_const.mul
      ((continuous_heckeFiniteFourierIntegral_TateTest heckeFiniteAdeleHaar chi).comp continuous_neg)
  have hDual := differentiable_heckeTateThetaMellinTail mu fD TD hTDC
    V hVB.1 hVB.2.2.1 B hVB.2.1 hVB.2.2.2 (unitaryHeckeInverse chi)
  let u (s : Complex) := s + (tau : Complex) * Complex.I
  let v (s : Complex) := 1 - u s
  have hU : Differentiable Complex u := differentiable_id.add (differentiable_const _)
  have hV : Differentiable Complex v := (differentiable_const (1 : Complex)).sub hU
  let L (s : Complex) := heckeTateThetaMellinTail mu f T chi (u s) +
    heckeTateThetaMellinTail mu fD TD (unitaryHeckeInverse chi) (v s)
  have hL : Differentiable Complex L := (hPrim.comp hU).add (hDual.comp hV)
  refine Exists.intro L (And.intro hL ?_)
  intro s hs
  exact (hS s hs).symm.trans (hEuler.2 s hs)

end Robin1984.GRH
