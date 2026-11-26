import Robin1984.GRH.GodementJacquetMellinAbsolute

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Godement-Jacquet unfolding and square integrability of the matrix-coefficient vectors on the norm-one quotient.
- Formalization note: Uses quotient right-translation invariance to supply the absolute double integrability required by the theta Mellin identity.
- PROVENANCE-END
-/

/-!
# Absolute Godement-Jacquet unfolding from square integrability

The right-invariance of the norm-one quotient integral gives a uniform
bound for the absolute matrix-coefficient integrand. If the weighted
matrix test is integrable over the full adelic group, Tonelli then
verifies the absolute convergence used in the theta Mellin identity.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField

namespace Robin1984.GRH

private theorem integrable_mul_of_uniformLIntegral
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (nu : Measure Y) [SFinite nu]
    (w : X -> Complex) (k : X -> Y -> Complex)
    (hw : Measurable w) (hk : Measurable (fun p : Prod X Y => k p.1 p.2))
    (hW : Integrable w mu) (C : ENNReal) (hC : C < Top.top)
    (hK : forall x : X, lintegral nu (fun y => enorm (k x y)) <= C) :
    Integrable (fun p : Prod X Y => w p.1 * k p.1 p.2) (mu.prod nu) := by
  have hF : Measurable (fun p : Prod X Y => w p.1 * k p.1 p.2) :=
    (hw.comp measurable_fst).mul hk
  refine And.intro hF.aestronglyMeasurable ?_
  change lintegral (mu.prod nu) (fun p : Prod X Y => enorm (w p.1 * k p.1 p.2)) < Top.top
  rw [lintegral_prod _ hF.enorm.aemeasurable]
  have hBound (x : X) :
      lintegral nu (fun y => enorm (w x * k x y)) <= enorm (w x) * C := by
    have hm : Measurable (fun y => k x y) := hk.comp (measurable_const.prodMk measurable_id)
    have hEq : (fun y : Y => enorm (w x * k x y)) =
        (fun y : Y => enorm (w x) * enorm (k x y)) :=
      funext (fun y => enorm_mul (w x) (k x y))
    rw [hEq, lintegral_const_mul _ hm.enorm]
    exact mul_le_mul_right (hK x) _
  refine (lintegral_mono hBound).trans_lt ?_
  have hWC : (fun x : X => enorm (w x) * C) = (fun x : X => C * enorm (w x)) :=
    funext (fun x => mul_comm _ _)
  rw [hWC, lintegral_const_mul _ hw.enorm]
  exact ENNReal.mul_lt_top hC hW.2

section

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "G" => AdelicGeneralLinearGroup K n
local notation "N" => MonoidHom.ker (adelicDeterminantLogNorm K n)
local notation "Gamma" => MonoidHom.range (adelicPrincipalDeterminantOne K n)

set_option maxHeartbeats 600000 in
/-- Two square-integrable quotient vectors give an absolutely integrable
double zeta kernel whenever the determinant-weighted test is integrable. -/
theorem integrable_adelicGodementJacquetKernel_of_squareIntegrable
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace N] [BorelSpace N] [MeasurableMul N]
    (hn : 0 < n) (mu : Measure N) [SFinite mu] [mu.IsHaarMeasure] [mu.IsMulRightInvariant]
    (D : Set N) (hD : MeasurableSet D)
    (hMul : Measurable (fun p : Prod G G => p.1 * p.2))
    (hUnique : forall x : N, ExistsUnique (fun gamma : Gamma => Membership.mem D (gamma.val * x)))
    (w f : G -> Complex) (c : N -> Complex)
    (hw : Measurable w) (hf : Measurable f) (hc : Measurable c)
    (hPrincipal : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      f (adelicPrincipalGeneralLinear K n a * g) = f g)
    (hCentral : forall t : Real, forall a : N,
      f (adelicDeterminantSection K n (Multiplicative.ofAdd t) * a.val) = f a.val)
    (hW : Integrable w (adelicDeterminantProductMeasure K n hn mu))
    (hcI : lintegral (mu.restrict D) (fun a => ENNReal.ofReal (norm (c a) ^ 2)) < Top.top)
    (hfI : lintegral (mu.restrict D) (fun a => ENNReal.ofReal (norm (f a.val) ^ 2)) < Top.top) :
    Integrable (fun p : Prod G N => w p.1 * (f (p.2.val * p.1) * c p.2))
      ((adelicDeterminantProductMeasure K n hn mu).prod (mu.restrict D)) := by
  let : Countable Gamma := countable_adelicPrincipalDeterminantOne K n
  let nu := mu.restrict D
  let M := adelicDeterminantProductMeasure K n hn mu
  let A (a : N) := ENNReal.ofReal (norm (c a) ^ 2)
  let B (a : N) := ENNReal.ofReal (norm (f a.val) ^ 2)
  let C := lintegral nu A + lintegral nu B
  have hC : C < Top.top := ENNReal.add_lt_top.mpr (And.intro hcI hfI)
  have hA : Measurable A := (hc.norm.pow_const 2).ennreal_ofReal
  have hv : Measurable (Subtype.val : N -> G) := continuous_subtype_val.measurable
  have hBInvariance (gamma : Gamma) (a : N) : B (gamma.val * a) = B a := by
    choose P hP using gamma.property
    have he : adelicPrincipalGeneralLinear K n P = gamma.val.val := congrArg Subtype.val hP
    change ENNReal.ofReal (norm (f (gamma.val.val * a.val)) ^ 2) = _
    rw [<- he, hPrincipal]
  have hRight (g : N) : lintegral nu (fun a => B (a * g)) = lintegral nu B :=
    lintegral_rightTranslate_eq_of_leftFundamentalDomain Gamma mu D hD hUnique B hBInvariance g
  have hF (g : G) (a : N) : f (a.val * g) = f (a * adelicDeterminantNormOnePart K n hn g).val := by
    let h := adelicDeterminantNormOnePart K n hn g
    let t := adelicDeterminantLogNorm K n g
    let z := adelicDeterminantSection K n t
    have e : z * h.val = g := (adelicDeterminantCoordinates K n hn).apply_symm_apply g
    calc
      _ = f (a.val * (z * h.val)) := congrArg (fun u => f (a.val * u)) e.symm
      _ = f (z * (a * h).val) := by
        change f (a.val * (z * h.val)) = f (z * (a.val * h.val))
        rw [<- mul_assoc, <-(adelicDeterminantSection_commute K n t a.val).eq, mul_assoc]
      _ = _ := hCentral (Multiplicative.toAdd t) (a * h)
  have hInner (g : G) :
      lintegral nu (fun a : N => enorm (f (a.val * g) * c a)) <= C := by
    let h := adelicDeterminantNormOnePart K n hn g
    calc
      _ <= lintegral nu (fun a => A a + B (a * h)) := by
        apply lintegral_mono
        intro a
        change enorm (f (a.val * g) * c a) <= A a + B (a * h)
        rw [hF g a, <- ofReal_norm, norm_mul]
        change ENNReal.ofReal (norm (f (a * h).val) * norm (c a)) <=
          ENNReal.ofReal (norm (c a) ^ 2) + ENNReal.ofReal (norm (f (a * h).val) ^ 2)
        rw [<- ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (norm (c a) - norm (f (a * h).val))])
      _ = C := by rw [lintegral_add_left hA, hRight h]
  have hk : Measurable (fun p : Prod G N => f (p.2.val * p.1) * c p.2) :=
    (hf.comp (hMul.comp ((hv.comp measurable_snd).prodMk measurable_fst))).mul
      (hc.comp measurable_snd)
  exact integrable_mul_of_uniformLIntegral M nu w (fun g a => f (a.val * g) * c a)
    hw hk hW C hC hInner


set_option maxHeartbeats 600000 in
/-- Square integrability on the norm-one quotient and integrability of
the weighted test justify the Mellin unfolding of the matrix coefficient. -/
theorem integral_adelicGodementJacquetMatrixCoeff_eq_logMellin_of_squareIntegrable
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace N] [BorelSpace N] [MeasurableMul N]
    [MeasurableSpace (Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K))]
    [BorelSpace (Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K))]
    (hn : 0 < n) (mu : Measure N) [SFinite mu] [mu.IsHaarMeasure] [mu.IsMulRightInvariant]
    (D : Set N) (hD : MeasurableSet D)
    (hMul : Measurable (fun p : Prod G G => p.1 * p.2))
    (hUnique : forall x : N, ExistsUnique (fun gamma : Gamma => Membership.mem D (gamma.val * x)))
    (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (f : G -> Complex) (c : N -> Complex) (s : Complex)
    (hPhi : Measurable Phi) (hf : Measurable f) (hc : Measurable c)
    (hSum : forall (t : Real) (A B : N),
      Summable (fun P : Matrix.GeneralLinearGroup (Fin n) K =>
        godementJacquetDoubleThetaTerm K n Phi t A B P.val))
    (hPrincipal : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      f (adelicPrincipalGeneralLinear K n a * g) = f g)
    (hCentral : forall t : Real, forall a : N,
      f (adelicDeterminantSection K n (Multiplicative.ofAdd t) * a.val) = f a.val)
    (hW : Integrable (fun g : G => Phi g.val *
      (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2))
      (adelicDeterminantProductMeasure K n hn mu))
    (hcI : lintegral (mu.restrict D) (fun a => ENNReal.ofReal (norm (c a) ^ 2)) < Top.top)
    (hfI : lintegral (mu.restrict D) (fun a => ENNReal.ofReal (norm (f a.val) ^ 2)) < Top.top) :
    integral (adelicDeterminantProductMeasure K n hn mu)
      (fun g => (Phi g.val * integral (mu.restrict D) (fun h => f (h.val * g) * c h)) *
        (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)) =
      godementJacquetLogMellin n
        (fun t => godementJacquetInvertibleDoubleThetaIntegral K n (mu.restrict D) Phi c
          (fun B => f B.val) t) s := by
  let : Countable Gamma := countable_adelicPrincipalDeterminantOne K n
  have hFund : IsFundamentalDomain Gamma D mu := IsFundamentalDomain.mk' hD.nullMeasurableSet hUnique
  let z := s + ((n : Complex) - 1) / 2
  let w (g : G) := (adelicDeterminantNorm K n g : Complex) ^ z
  have hWExp (g : G) : w g = Complex.exp ((Real.log (adelicDeterminantNorm K n g) : Complex) * z) := by
    have h := adelicDeterminantNorm_pos K n g
    unfold w
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt h)), Complex.ofReal_log h.le]
  have hWM : Measurable w := by
    rw [show w = (fun g => Complex.exp ((Real.log (adelicDeterminantNorm K n g) : Complex) * z))
      from funext hWExp]
    exact Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp
        (Real.measurable_log.comp (continuous_adelicDeterminantNorm K n).measurable)).mul_const z)
  let test (g : G) := Phi g.val * w g
  have hTest : Measurable test := (hPhi.comp Units.continuous_val.measurable).mul hWM
  have hAbs := integrable_adelicGodementJacquetKernel_of_squareIntegrable K n hn mu D hD
    hMul hUnique test f c hTest hf hc hPrincipal hCentral hW hcI hfI
  refine integral_adelicGodementJacquetMatrixCoeff_eq_logMellin_of_measurable K n hn mu D
    hFund Phi f c s hPhi hf hc hSum hPrincipal hCentral ?_
  have he : (fun p : Prod G N => (Phi p.1.val * (f (p.2.val * p.1) * c p.2)) * w p.1) =
      (fun p : Prod G N => test p.1 * (f (p.2.val * p.1) * c p.2)) := by
    funext p
    unfold test
    ac_rfl
  change Integrable (fun p : Prod G N => (Phi p.1.val * (f (p.2.val * p.1) * c p.2)) * w p.1) _
  rwa [he]

end

end Robin1984.GRH
