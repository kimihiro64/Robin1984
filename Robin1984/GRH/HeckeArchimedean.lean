import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.Gamma
import Robin1984.GRH.HeckeConductor

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The unitary characters of the real and complex local multiplicative groups and their archimedean Gamma factors in Tate's thesis.
- Formalization note: Proves both local character formulas, obtains the archimedean shifts from the actual ideles, evaluates the radial Gaussian Mellin integrals, and applies the completed Hecke criterion with these shifts and the conductor.
- PROVENANCE-END
-/

/-!
# Archimedean factors of unitary Hecke characters

A continuous additive real character has a real frequency. This
gives the parity and frequency of the real local characters and
the angular weight and radial frequency of the complex characters.
The local parameters determine the Gamma shifts, which are also
identified with the radial Gaussian Mellin integrals.
-/

set_option autoImplicit false

open Complex IsDedekindDomain MeasureTheory Metric NumberField Set

namespace Robin1984.GRH

/-- A continuous unitary character of the additive real line has a real frequency. -/
theorem exists_frequency_of_continuous_unitary_character
    (f : Real -> Complex) (hc : Continuous f)
    (h0 : f 0 = 1) (hmul : forall x y : Real, f (x + y) = f x * f y)
    (hunit : forall x : Real, norm (f x) = 1) :
    exists tau : Real, forall x : Real, f x = Complex.exp (((tau * x : Real) : Complex) * Complex.I) := by
  have hRe : Continuous (fun x : Real => (f x).re) := Complex.continuous_re.comp hc
  have hOpen : IsOpen {x : Real | 1 / 2 < (f x).re} :=
    isOpen_lt continuous_const hRe
  have hNear : Membership.mem (nhds (0 : Real)) {x : Real | 1 / 2 < (f x).re} := by
    apply hOpen.mem_nhds
    change (1 : Real) / 2 < (f 0).re
    rw [h0]
    norm_num
  choose eps hEps hBall using Metric.mem_nhds_iff.mp hNear
  let a : Real := eps / 2
  have ha : 0 < a := half_pos hEps
  have hHalf (t : Real) (ht : Membership.mem (Icc 0 a) t) : 1 / 2 < (f t).re := by
    apply hBall
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt (half_lt_self hEps)
  let A : Complex := intervalIntegral f 0 a volume
  have hReA : intervalIntegral (fun x => (f x).re) 0 a volume = A.re :=
    Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable 0 a)
  have hAc : Not (A = 0) := by
    have hConstInt : IntervalIntegrable (fun _ : Real => (1 : Real) / 2) volume 0 a :=
      continuous_const.intervalIntegrable 0 a
    have hLower := intervalIntegral.integral_mono_on ha.le
      hConstInt (hRe.intervalIntegrable 0 a)
      (fun t ht => (hHalf t ht).le)
    have hConst : intervalIntegral (fun _ : Real => (1 : Real) / 2) 0 a volume = a / 2 := by
      simp [intervalIntegral.integral_const, div_eq_mul_inv]
    rw [hConst, hReA] at hLower
    intro hAz
    rw [hAz, Complex.zero_re] at hLower
    exact (not_le_of_gt (half_pos ha)) hLower
  let F : Real -> Complex := fun x => intervalIntegral f 0 x volume
  have hFftc (x : Real) : HasDerivAt F (f x) x := by
    exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hTranslate (x : Real) : F (x + a) - F x = f x * A := by
    calc
      _ = intervalIntegral f x (x + a) volume := by
        have hh : F x + intervalIntegral f x (x + a) volume = F (x + a) :=
          intervalIntegral.integral_add_adjacent_intervals
            (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x (x + a))
        rw [<- hh]
        abel
      _ = intervalIntegral (fun t => f (t + x)) 0 a volume := by
        simpa only [zero_add, add_comm a x] using
          (intervalIntegral.integral_comp_add_right (f := f) (a := 0) (b := a) x).symm
      _ = _ := by
        have hEq : (fun t : Real => f (t + x)) = (fun t : Real => f x * f t) := by
          funext t
          rw [add_comm t x, hmul]
        rw [hEq, intervalIntegral.integral_const_mul]
  let lambda : Complex := (f a - 1) / A
  have hDeriv (x : Real) : HasDerivAt f (lambda * f x) x := by
    have hMove : HasDerivAt (fun y : Real => F (y + a)) (f (x + a)) x := by
      exact HasDerivAt.comp_add_const x a (hFftc (x + a))
    have h : HasDerivAt (fun y : Real => (F (y + a) - F y) / A) ((f (x + a) - f x) / A) x :=
      (hMove.sub (hFftc x)).div_const A
    have hf : (fun y : Real => (F (y + a) - F y) / A) = f := by
      funext y
      rw [hTranslate y]
      field_simp [hAc]
    rw [hf, hmul] at h
    convert h using 1
    dsimp [lambda]
    ring
  have hOfReal (x : Real) : HasDerivAt (fun t : Real => (t : Complex)) 1 x := by
    exact Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  let G : Real -> Complex := fun x => f x * Complex.exp (-(lambda * (x : Complex)))
  have hGDeriv (x : Real) : HasDerivAt G 0 x := by
    have hArg : HasDerivAt (fun y : Real => -(lambda * (y : Complex))) (-lambda) x := by
      simpa only [mul_one] using ((hOfReal x).const_mul lambda).fun_neg
    have h := (hDeriv x).fun_mul hArg.cexp
    have hZero : lambda * f x * Complex.exp (-(lambda * (x : Complex))) +
        f x * (Complex.exp (-(lambda * (x : Complex))) * (-lambda)) = 0 := by
      ring
    rw [hZero] at h
    exact h
  have hG (x : Real) : G x = 1 := by
    have h := is_const_of_deriv_eq_zero (fun y => (hGDeriv y).differentiableAt)
      (fun y => (hGDeriv y).deriv) x 0
    simpa [G, h0] using h
  have hExp (x : Real) : f x = Complex.exp (lambda * (x : Complex)) := by
    calc
      _ = G x * Complex.exp (lambda * (x : Complex)) := by
        simp only [G, mul_assoc, <- Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = _ := by rw [hG, one_mul]
  have hReZero : lambda.re = 0 := by
    have h := congrArg norm (hExp 1)
    rw [hunit, Complex.ofReal_one, mul_one, Complex.norm_exp] at h
    exact Real.exp_injective (by simpa only [Real.exp_zero] using h.symm)
  let tau := lambda.im
  have hLambda : lambda = (tau : Complex) * Complex.I :=
    Complex.ext (by simp [hReZero, Complex.mul_re]) (by simp [tau, Complex.mul_im])
  refine Exists.intro tau ?_
  intro x
  rw [hExp x, hLambda, Complex.ofReal_mul]
  congr 1
  ring

/-- A continuous character of the unit circle is an integral power. -/
theorem exists_integer_power_of_continuous_circle_character
    (chi : ContinuousMonoidHom Circle Circle) :
    exists m : Int, forall z : Circle, chi z = z ^ m := by
  let f (x : Real) : Complex := (chi (Circle.exp x) : Complex)
  have hExpCont : Continuous Circle.exp := by
    apply continuous_induced_rng.mpr
    change Continuous (fun x : Real => Complex.exp ((x : Complex) * Complex.I))
    exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hF : Continuous f := continuous_subtype_val.comp (chi.continuous.comp hExpCont)
  have hZero : f 0 = 1 := by simp [f]
  have hMul (x y : Real) : f (x + y) = f x * f y := by
    simp [f, Circle.exp_add, map_mul]
  choose tau hTau using exists_frequency_of_continuous_unitary_character f hF hZero hMul
    (fun x => Circle.norm_coe (chi (Circle.exp x)))
  have hPeriod : Complex.exp (((tau * (2 * Real.pi) : Real) : Complex) * Complex.I) = 1 := by
    rw [<- hTau]
    simp [f]
  choose m hm using Complex.exp_eq_one_iff.mp hPeriod
  have hMulEq : tau * (2 * Real.pi) = (m : Real) * (2 * Real.pi) := by
    have h := congrArg Complex.im hm
    simpa [Complex.mul_im, Complex.mul_re, mul_comm, mul_left_comm] using h
  have hDiff : (tau - (m : Real)) * (2 * Real.pi) = 0 := by
    rw [sub_mul, hMulEq, sub_self]
  have hTauInt : tau = (m : Real) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hDiff).resolve_right (mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos)))
  refine Exists.intro m ?_
  intro z
  apply Subtype.ext
  have hValue := hTau (Complex.arg (z : Complex))
  change (chi (Circle.exp (Complex.arg (z : Complex))) : Complex) = _ at hValue
  rw [Circle.exp_arg, hTauInt, <- Circle.coe_exp] at hValue
  have hPower : Circle.exp ((m : Real) * Complex.arg (z : Complex)) = z ^ m := by
    simpa only [zsmul_eq_mul, Circle.exp_arg] using Circle.exp_zsmul (Complex.arg (z : Complex)) m
  exact hValue.trans (congrArg (fun w : Circle => (w : Complex)) hPower)

private noncomputable def realExpUnit (x : Real) : Units Real :=
  Units.mk0 (Real.exp x) (Real.exp_ne_zero x)

private theorem continuous_realExpUnit : Continuous realExpUnit := by
  apply Units.continuous_iff.mpr
  constructor
  case left =>
    exact Real.continuous_exp
  case right =>
    have h : (fun x : Real => ((Inv.inv (realExpUnit x) : Units Real) : Real)) =
        (fun x : Real => Real.exp (-x)) := by
      funext x
      rw [Units.val_inv_eq_inv_val, Real.exp_neg]
      rfl
    rw [h]
    exact Real.continuous_exp.comp continuous_neg

private theorem realExpUnit_add (x y : Real) :
    realExpUnit (x + y) = realExpUnit x * realExpUnit y :=
  Units.ext (Real.exp_add x y)

private theorem realExpUnit_zero : realExpUnit 0 = 1 :=
  Units.ext Real.exp_zero

/-- Real local characters have a parity and a real frequency on positive units. -/
theorem exists_realUnitaryCharacter_parameters
    (chi : ContinuousMonoidHom (Units Real) Circle) :
    exists epsilon : Nat, exists tau : Real, epsilon <= 1 /\
      forall a : Units Real, (chi a : Complex) =
        (if 0 < (a : Real) then 1 else (-1 : Complex) ^ epsilon) *
          Complex.exp (((tau * Real.log (abs (a : Real)) : Real) : Complex) * Complex.I) := by
  let f (x : Real) : Complex := (chi (realExpUnit x) : Complex)
  have hF : Continuous f := continuous_subtype_val.comp (chi.continuous.comp continuous_realExpUnit)
  have hF0 : f 0 = 1 := by simp [f, realExpUnit_zero]
  have hFmul (x y : Real) : f (x + y) = f x * f y := by
    simp [f, realExpUnit_add, map_mul]
  choose tau htau using exists_frequency_of_continuous_unitary_character f hF hF0 hFmul
    (fun x => Circle.norm_coe (chi (realExpUnit x)))
  let negUnit : Units Real := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  have hnegSq : negUnit ^ 2 = 1 := by
    apply Units.ext
    change (-1 : Real) ^ 2 = 1
    norm_num
  have hChiSq : (chi negUnit : Complex) ^ 2 = 1 := by
    rw [<- Circle.coe_pow, <- map_pow, hnegSq, map_one]
    rfl
  have hParity : exists n : Nat, n <= 1 /\ (chi negUnit : Complex) = (-1 : Complex) ^ n := by
    by_cases hp : (chi negUnit : Complex) = 1
    case pos =>
      exact Exists.intro 0 (And.intro (Nat.zero_le _) (by simpa only [pow_zero] using hp))
    case neg =>
      have hFactor : ((chi negUnit : Complex) - 1) * ((chi negUnit : Complex) + 1) = 0 := by
        linear_combination hChiSq
      have hEq := (mul_eq_zero.mp hFactor).resolve_left (sub_ne_zero.mpr hp)
      exact Exists.intro 1 (And.intro le_rfl (by
        simpa only [pow_one] using eq_neg_of_add_eq_zero_left hEq))
  choose epsilon hEps hEpsValue using hParity
  refine Exists.intro epsilon (Exists.intro tau (And.intro hEps ?_))
  intro u
  let y := Real.log (abs (u : Real))
  have hy : ((realExpUnit y : Units Real) : Real) = abs (u : Real) :=
    Real.exp_log (abs_pos.mpr u.ne_zero)
  have hVal : (chi (realExpUnit y) : Complex) =
      Complex.exp (((tau * y : Real) : Complex) * Complex.I) := htau y
  by_cases hu : 0 < (u : Real)
  case pos =>
    have he : u = realExpUnit y := Units.ext (hy.trans (abs_of_pos hu)).symm
    rw [if_pos hu, one_mul]
    exact (congrArg (fun z : Units Real => (chi z : Complex)) he).trans hVal
  case neg =>
    have huNeg : (u : Real) < 0 := lt_of_le_of_ne (le_of_not_gt hu) u.ne_zero
    have he : u = negUnit * realExpUnit y := by
      apply Units.ext
      change (u : Real) = (-1 : Real) * (realExpUnit y : Real)
      rw [hy, abs_of_neg huNeg, neg_one_mul, neg_neg]
    calc
      (chi u : Complex) = (chi negUnit : Complex) * (chi (realExpUnit y) : Complex) := by
        rw [<- Circle.coe_mul, <- map_mul, <- he]
      _ = _ := by rw [hEpsValue, if_neg hu, hVal]

private noncomputable def complexExpUnit (x : Real) : Units Complex :=
  Units.map Complex.ofRealHom.toMonoidHom (realExpUnit x)

private theorem continuous_complexExpUnit : Continuous complexExpUnit :=
  (Units.continuous_map Complex.continuous_ofReal).comp continuous_realExpUnit

private theorem complexExpUnit_add (x y : Real) :
    complexExpUnit (x + y) = complexExpUnit x * complexExpUnit y := by
  simp only [complexExpUnit, realExpUnit_add, map_mul]

private theorem complexExpUnit_zero : complexExpUnit 0 = 1 := by
  simp only [complexExpUnit, realExpUnit_zero, map_one]

private theorem continuous_circleToUnits : Continuous Circle.toUnits := by
  apply Units.continuous_iff.mpr
  constructor
  case left =>
    exact continuous_subtype_val
  case right =>
    have h : (fun z : Circle => ((Inv.inv (Circle.toUnits z) : Units Complex) : Complex)) =
        (fun z : Circle => ((Inv.inv z : Circle) : Complex)) := by
      funext z
      rw [<- map_inv]
      rfl
    rw [h]
    exact continuous_subtype_val.comp continuous_inv

/-- The unit-circle component of a nonzero complex number. -/
noncomputable def complexUnitPhase (u : Units Complex) : Circle :=
  Subtype.mk ((u : Complex) / (norm (u : Complex) : Complex)) (by
    apply mem_sphere_zero_iff_norm.mpr
    have hp : 0 < norm (u : Complex) := norm_pos_iff.mpr u.ne_zero
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, div_self hp.ne'])

/-- Complex local characters have an integral angular weight and a real radial frequency. -/
theorem exists_complexUnitaryCharacter_parameters
    (chi : ContinuousMonoidHom (Units Complex) Circle) :
    exists m : Int, exists tau : Real,
      forall u : Units Complex, (chi u : Complex) =
        ((complexUnitPhase u ^ m : Circle) : Complex) *
          Complex.exp (((tau * Real.log (norm (u : Complex)) : Real) : Complex) * Complex.I) := by
  let f (x : Real) : Complex := (chi (complexExpUnit x) : Complex)
  have hF : Continuous f := continuous_subtype_val.comp (chi.continuous.comp continuous_complexExpUnit)
  have hF0 : f 0 = 1 := by simp [f, complexExpUnit_zero]
  have hFmul (x y : Real) : f (x + y) = f x * f y := by
    simp [f, complexExpUnit_add, map_mul]
  choose tau htau using exists_frequency_of_continuous_unitary_character f hF hF0 hFmul
    (fun x => Circle.norm_coe (chi (complexExpUnit x)))
  let angular : ContinuousMonoidHom Circle Circle :=
    { toMonoidHom := chi.toMonoidHom.comp Circle.toUnits
      continuous_toFun := chi.continuous.comp continuous_circleToUnits }
  choose m hm using exists_integer_power_of_continuous_circle_character angular
  refine Exists.intro m (Exists.intro tau ?_)
  intro u
  let t := Real.log (norm (u : Complex))
  have hr : Real.exp t = norm (u : Complex) :=
    Real.exp_log (norm_pos_iff.mpr u.ne_zero)
  have hRadial : (chi (complexExpUnit t) : Complex) =
      Complex.exp (((tau * t : Real) : Complex) * Complex.I) := htau t
  have hAngular : chi (Circle.toUnits (complexUnitPhase u)) = complexUnitPhase u ^ m :=
    hm (complexUnitPhase u)
  have hDecompose : u = Circle.toUnits (complexUnitPhase u) * complexExpUnit t := by
    apply Units.ext
    change (u : Complex) = ((u : Complex) / (norm (u : Complex) : Complex)) *
      (Real.exp t : Complex)
    rw [hr]
    field_simp
  calc
    (chi u : Complex) =
        (chi (Circle.toUnits (complexUnitPhase u)) : Complex) * (chi (complexExpUnit t) : Complex) := by
      rw [<- Circle.coe_mul, <- map_mul, <- hDecompose]
    _ = _ := by rw [hAngular, hRadial]

/-! ## The parameters at infinite places -/

private noncomputable def infiniteLocalAdeleHom (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) : MonoidHom v.Completion (AdeleRing (RingOfIntegers K) K) := by
  classical
  exact (MonoidHom.mulSingle (fun w : InfinitePlace K => w.Completion) v).prod 1

private theorem continuous_infiniteLocalAdeleHom (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) : Continuous (infiniteLocalAdeleHom K v) := by
  classical
  have h : Continuous (fun a : v.Completion => (Pi.mulSingle v a : InfiniteAdeleRing K)) := by
    apply continuous_pi
    intro w
    by_cases hw : w = v
    case pos =>
      subst w
      simp only [Pi.mulSingle_eq_same]
      exact continuous_id
    case neg =>
      simpa only [Pi.mulSingle_eq_of_ne hw] using
        (continuous_const : Continuous (fun _ : v.Completion => (1 : w.Completion)))
  change Continuous (fun a : v.Completion =>
    ((Pi.mulSingle v a : InfiniteAdeleRing K), (1 : FiniteAdeleRing (RingOfIntegers K) K)))
  exact h.prodMk continuous_const

/-- Restrict a unitary Hecke character to the completion at an infinite place. -/
noncomputable def infiniteLocalHeckeCharacter {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (v : InfinitePlace K) :
    ContinuousMonoidHom (Units v.Completion) Circle where
  toMonoidHom := chi.val.toMonoidHom.comp (Units.map (infiniteLocalAdeleHom K v))
  continuous_toFun := chi.val.continuous.comp (Units.continuous_map (continuous_infiniteLocalAdeleHom K v))

/-- The local Hecke character at a real place, in the real completion. -/
noncomputable def realInfiniteHeckeCharacter {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsReal) :
    ContinuousMonoidHom (Units Real) Circle :=
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  { toMonoidHom := (infiniteLocalHeckeCharacter chi v).toMonoidHom.comp
      (Units.map e.symm.toMonoidHom)
    continuous_toFun := (infiniteLocalHeckeCharacter chi v).continuous.comp
      (Units.continuous_map (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous) }

/-- The local Hecke character at a complex place, in the complex completion. -/
noncomputable def complexInfiniteHeckeCharacter {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsComplex) :
    ContinuousMonoidHom (Units Complex) Circle :=
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
  { toMonoidHom := (infiniteLocalHeckeCharacter chi v).toMonoidHom.comp
      (Units.map e.symm.toMonoidHom)
    continuous_toFun := (infiniteLocalHeckeCharacter chi v).continuous.comp
      (Units.continuous_map (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous) }

/-- The parity and frequency of the local Hecke character at a real place. -/
noncomputable def realInfiniteHeckeParameters {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsReal) : Prod Nat Real :=
  let h := exists_realUnitaryCharacter_parameters (realInfiniteHeckeCharacter chi hv)
  (h.choose, h.choose_spec.choose)

theorem realInfiniteHeckeParameters_spec {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsReal) :
    let params := realInfiniteHeckeParameters chi hv
    params.1 <= 1 /\ forall a : Units Real, (realInfiniteHeckeCharacter chi hv a : Complex) =
      (if 0 < (a : Real) then 1 else (-1 : Complex) ^ params.1) *
        Complex.exp (((params.2 * Real.log (abs (a : Real)) : Real) : Complex) * Complex.I) :=
  (exists_realUnitaryCharacter_parameters (realInfiniteHeckeCharacter chi hv)).choose_spec.choose_spec

/-- The angular weight and radial frequency of the local Hecke character at a complex place. -/
noncomputable def complexInfiniteHeckeParameters {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsComplex) : Prod Int Real :=
  let h := exists_complexUnitaryCharacter_parameters (complexInfiniteHeckeCharacter chi hv)
  (h.choose, h.choose_spec.choose)

theorem complexInfiniteHeckeParameters_spec {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsComplex) :
    let params := complexInfiniteHeckeParameters chi hv
    forall u : Units Complex, (complexInfiniteHeckeCharacter chi hv u : Complex) =
      ((complexUnitPhase u ^ params.1 : Circle) : Complex) *
        Complex.exp (((params.2 * Real.log (norm (u : Complex)) : Real) : Complex) * Complex.I) :=
  (exists_complexUnitaryCharacter_parameters (complexInfiniteHeckeCharacter chi hv)).choose_spec.choose_spec

/-- The shift in the standard real Gamma factor for this local character. -/
noncomputable def realInfiniteHeckeShift {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsReal) : Complex :=
  let params := realInfiniteHeckeParameters chi hv
  (params.1 : Complex) + (params.2 : Complex) * Complex.I

/-- The shift in the standard complex Gamma factor for this local character. -/
noncomputable def complexInfiniteHeckeShift {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsComplex) : Complex :=
  let params := complexInfiniteHeckeParameters chi hv
  (((params.1.natAbs : Real) / 2 : Real) : Complex) + ((params.2 / 2 : Real) : Complex) * Complex.I

theorem realInfiniteHeckeShift_re_nonneg {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsReal) :
    0 <= (realInfiniteHeckeShift chi hv).re := by
  simp [realInfiniteHeckeShift, Complex.add_re, Complex.mul_re]

theorem complexInfiniteHeckeShift_re_nonneg {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsComplex) :
    0 <= (complexInfiniteHeckeShift chi hv).re := by
  simp [complexInfiniteHeckeShift, Complex.add_re, Complex.mul_re]
  positivity

/-! ## The paired completion -/

abbrev PairedRealHeckePlaces (K : Type*) [Field K] :=
  Prod Bool {v : InfinitePlace K // v.IsReal}

abbrev PairedComplexHeckePlaces (K : Type*) [Field K] :=
  Prod Bool {v : InfinitePlace K // v.IsComplex}

/-- The real shifts for the product of a character and its inverse. -/
noncomputable def heckePairedRealShift {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : PairedRealHeckePlaces K) : Complex :=
  realInfiniteHeckeShift (if p.1 then chi else unitaryHeckeInverse chi) p.2.property

/-- The complex shifts for the product of a character and its inverse. -/
noncomputable def heckePairedComplexShift {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : PairedComplexHeckePlaces K) : Complex :=
  complexInfiniteHeckeShift (if p.1 then chi else unitaryHeckeInverse chi) p.2.property

theorem heckePairedRealShift_re_nonneg {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : PairedRealHeckePlaces K) :
    0 <= (heckePairedRealShift chi p).re :=
  realInfiniteHeckeShift_re_nonneg _ _

theorem heckePairedComplexShift_re_nonneg {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : PairedComplexHeckePlaces K) :
    0 <= (heckePairedComplexShift chi p).re :=
  complexInfiniteHeckeShift_re_nonneg _ _

/-- The conductor and Gamma factors for the paired Hecke completion. -/
noncomputable def heckePairedCompletionFactor {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (m : Nat) (s : Complex) : Complex := by
  classical
  exact standardCompletionFactor (heckeArithmeticConductor chi ^ 2) m
    (heckePairedRealShift chi) (heckePairedComplexShift chi) s

/-- The Hecke criterion with the conductor and archimedean shifts constructed
from the characters. The analytic continuation and functional equation
are inputs. The pole order and completion use the normalized functions. -/
theorem heckeCompletedCriterion_of_characterParameters
    {K : Type*} [Field K] [NumberField K] {index : Type*}
    (character : index -> UnitaryHeckeCharacter K)
    (dual : index -> index)
    (completedL poleRemoved equationFactor : index -> Complex -> Complex)
    (poleOrder : index -> Nat)
    (hEntire : forall i, Differentiable Complex (poleRemoved i))
    (hOrder : forall i, Complex.Hadamard.EntireOfOrderAtMost 1 (completedL i))
    (hEuler : forall i s, 1 < s.re ->
      poleRemoved i s = (s - 1) ^ (poleOrder i) *
        (heckeEulerL K (character i) s * heckeEulerL K (unitaryHeckeInverse (character i)) s))
    (hCompletion : forall i s, (1 : Real) / 2 < s.re ->
      completedL i s * completedL (dual i) s =
        heckePairedCompletionFactor (character i) (poleOrder i) s * poleRemoved i s)
    (hEquation : forall i s, completedL (dual i) (1 - s) =
      equationFactor i s * completedL i s) :
    CompletedFamilyRH completedL <->
      forall i, GrandRobinTriangularBound (heckePairedEulerData K (character i) (poleOrder i) (poleRemoved i)) := by
  classical
  refine heckeCompletedCriterion K character dual completedL poleRemoved equationFactor
    (fun i => heckeArithmeticConductor (character i) ^ 2) poleOrder
    (fun i => heckePairedRealShift (character i)) (fun i => heckePairedComplexShift (character i))
    (fun i => pow_pos (heckeArithmeticConductor_pos (character i)) _) ?_ ?_
    hEntire hOrder hEuler hCompletion hEquation
  case refine_1 =>
    intro i p
    exact (show -(1 : Real) / 2 < 0 by norm_num).trans_le (heckePairedRealShift_re_nonneg (character i) p)
  case refine_2 =>
    intro i p
    exact (show -(1 : Real) / 2 < 0 by norm_num).trans_le (heckePairedComplexShift_re_nonneg (character i) p)

/-! ## Radial Gaussian transforms -/

/-- The radial Gaussian Mellin transform for a complex exponent. -/
theorem radial_gaussian_mellin (a : Real) (ha : 0 < a) (z : Complex) (hz : 0 < z.re) :
    integral (volume.restrict (Ioi (0 : Real)))
      (fun x : Real => (x : Complex) ^ (2 * z - 1) *
        Complex.exp (-((a : Complex) * ((x ^ 2 : Real) : Complex)))) =
      (1 / 2 : Complex) * ((a : Complex) ^ (-z) * Complex.Gamma z) := by
  let f (x : Real) : Complex := (x : Complex) ^ (z - 1) *
    Complex.exp (-((a : Complex) * (x : Complex)))
  let g (x : Real) : Complex := (x : Complex) ^ (2 * z - 1) *
    Complex.exp (-((a : Complex) * ((x ^ 2 : Real) : Complex)))
  have hSub : integral (volume.restrict (Ioi (0 : Real)))
      (fun x : Real => ((2 * x : Real) : Complex) * f (x ^ 2)) =
      integral (volume.restrict (Ioi (0 : Real))) f := by
    simpa only [abs_of_nonneg (show (0 : Real) <= 2 by norm_num),
      show (2 : Real) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, Complex.real_smul] using
      (integral_comp_rpow_Ioi (p := 2) f (show Not ((2 : Real) = 0) by norm_num))
  have hPoint (x : Real) (hx : Membership.mem (Ioi (0 : Real)) x) :
      (2 : Complex) * g x = ((2 * x : Real) : Complex) * f (x ^ 2) := by
    have hx0 : 0 < x := hx
    have hxc : Not ((x : Complex) = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt hx0)
    have hSquare :
        ((x ^ 2 : Real) : Complex) ^ (z - 1) =
          (x : Complex) ^ (z - 1) * (x : Complex) ^ (z - 1) := by
      rw [Complex.ofReal_pow, pow_two]
      exact Complex.mul_cpow_ofReal_nonneg hx0.le hx0.le _
    have hWeight : (x : Complex) *
        ((x : Complex) ^ (z - 1) * (x : Complex) ^ (z - 1)) =
        (x : Complex) ^ (2 * z - 1) := by
      calc
        _ = (x : Complex) ^ (1 : Complex) *
            ((x : Complex) ^ (z - 1) * (x : Complex) ^ (z - 1)) := by rw [Complex.cpow_one]
        _ = (x : Complex) ^ ((1 : Complex) + ((z - 1) + (z - 1))) := by
          rw [Complex.cpow_add _ _ hxc, Complex.cpow_add _ _ hxc]
        _ = _ := by congr 1; ring
    dsimp only [g, f]
    rw [hSquare, Complex.ofReal_mul, Complex.ofReal_ofNat, <- hWeight]
    ring
  have hScale : (1 / (a : Complex)) ^ z = (a : Complex) ^ (-z) := by
    have haArg : Not ((a : Complex).arg = Real.pi) := by
      rw [Complex.arg_ofReal_of_nonneg ha.le]
      exact (ne_of_gt Real.pi_pos).symm
    rw [one_div, Complex.inv_cpow _ _ haArg, Complex.cpow_neg]
  have hTotal : (2 : Complex) * integral (volume.restrict (Ioi (0 : Real))) g =
      (a : Complex) ^ (-z) * Complex.Gamma z := by
    calc
      _ = integral (volume.restrict (Ioi (0 : Real))) (fun x => (2 : Complex) * g x) :=
        (integral_const_mul _ _).symm
      _ = integral (volume.restrict (Ioi (0 : Real))) (fun x : Real => ((2 * x : Real) : Complex) * f (x ^ 2)) :=
        setIntegral_congr_fun measurableSet_Ioi hPoint
      _ = integral (volume.restrict (Ioi (0 : Real))) f := hSub
      _ = _ := by
        rw [show integral (volume.restrict (Ioi (0 : Real))) f =
          (1 / (a : Complex)) ^ z * Complex.Gamma z from
            Complex.integral_cpow_mul_exp_neg_mul_Ioi hz ha, hScale]
  change integral (volume.restrict (Ioi (0 : Real))) g = _
  calc
    _ = (1 / 2 : Complex) * ((2 : Complex) * integral (volume.restrict (Ioi (0 : Real))) g) := by ring
    _ = _ := by rw [hTotal]

/-- The real archimedean factor as a radial Gaussian Mellin integral. -/
theorem realInfiniteHeckeGamma_eq_radial_mellin {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsReal)
    (s : Complex) (hs : 0 < s.re) :
    let w := s + realInfiniteHeckeShift chi hv
    (2 : Complex) * integral (volume.restrict (Ioi (0 : Real)))
      (fun x : Real => (x : Complex) ^ (w - 1) *
        Complex.exp (-((Real.pi : Complex) * ((x ^ 2 : Real) : Complex)))) =
      (Real.pi : Complex) ^ (-(w / 2)) * Complex.Gamma (w / 2) := by
  let w := s + realInfiniteHeckeShift chi hv
  let z := w / 2
  have hTwo : (2 : Complex) * z = w := by
    dsimp [z]
    ring
  have hz : 0 < z.re := by
    have h := congrArg Complex.re hTwo
    norm_num [Complex.mul_re, Complex.add_re, w] at h
    linarith [realInfiniteHeckeShift_re_nonneg chi hv]
  change (2 : Complex) * integral (volume.restrict (Ioi (0 : Real)))
    (fun x : Real => (x : Complex) ^ (w - 1) *
      Complex.exp (-((Real.pi : Complex) * ((x ^ 2 : Real) : Complex)))) =
    (Real.pi : Complex) ^ (-z) * Complex.Gamma z
  have hM := radial_gaussian_mellin Real.pi Real.pi_pos z hz
  rw [hTwo] at hM
  rw [hM]
  ring

/-- The complex archimedean factor as a radial Gaussian Mellin integral. -/
theorem complexInfiniteHeckeGamma_eq_radial_mellin {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) {v : InfinitePlace K} (hv : v.IsComplex)
    (s : Complex) (hs : 0 < s.re) :
    let w := s + complexInfiniteHeckeShift chi hv
    (4 : Complex) * integral (volume.restrict (Ioi (0 : Real)))
      (fun x : Real => (x : Complex) ^ (2 * w - 1) *
        Complex.exp (-(((2 * Real.pi : Real) : Complex) * ((x ^ 2 : Real) : Complex)))) =
      2 * (((2 * Real.pi : Real) : Complex) ^ (-w) * Complex.Gamma w) := by
  let w := s + complexInfiniteHeckeShift chi hv
  have hw : 0 < w.re := by
    rw [show w.re = s.re + (complexInfiniteHeckeShift chi hv).re from Complex.add_re _ _]
    exact add_pos_of_pos_of_nonneg hs (complexInfiniteHeckeShift_re_nonneg chi hv)
  have hPi : 0 < (2 : Real) * Real.pi := mul_pos (by norm_num) Real.pi_pos
  change (4 : Complex) * integral (volume.restrict (Ioi (0 : Real)))
    (fun x : Real => (x : Complex) ^ (2 * w - 1) *
      Complex.exp (-(((2 * Real.pi : Real) : Complex) * ((x ^ 2 : Real) : Complex)))) =
    2 * (((2 * Real.pi : Real) : Complex) ^ (-w) * Complex.Gamma w)
  rw [radial_gaussian_mellin (2 * Real.pi) hPi w hw]
  ring

end Robin1984.GRH
