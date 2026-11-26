import Robin1984.GRH.HeckeTateClassPoisson

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The real and complex local Fourier transforms in Tate's thesis.
- Formalization note: Identifies the canonical archimedean trace Fourier test with the test for the inverse character and an explicit unit phase.
- PROVENANCE-END
-/

/-!
# Archimedean Fourier transform of the canonical Tate test

The trace Fourier transform factors by infinite place. At real places it
preserves the test parity, and at complex places it reverses the angular
exponent. The square-root-of-two change of coordinates accounts for the
complex trace normalization. The resulting phase has absolute value one.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace Real U] [FiniteDimensional Real U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V]

/-- Fourier transform separates over a two-factor Euclidean product. -/
theorem fourier_tate_withLp_prod (f : U -> Complex) (g : V -> Complex)
    (w : WithLp 2 (Prod U V)) :
    fourier (fun z : WithLp 2 (Prod U V) => f (WithLp.ofLp z).1 * g (WithLp.ofLp z).2) w =
      fourier f (WithLp.ofLp w).1 * fourier g (WithLp.ofLp w).2 := by
  let A (x : U) :=
    Complex.exp (((-2 * Real.pi * inner Real x (WithLp.ofLp w).1 : Real) : Complex) * Complex.I) * f x
  let B (x : V) :=
    Complex.exp (((-2 * Real.pi * inner Real x (WithLp.ofLp w).2 : Real) : Complex) * Complex.I) * g x
  have hA : fourier f (WithLp.ofLp w).1 = integral volume A := by
    simp only [Real.fourier_eq', smul_eq_mul, A]
  have hB : fourier g (WithLp.ofLp w).2 = integral volume B := by
    simp only [Real.fourier_eq', smul_eq_mul, B]
  rw [hA, hB, <- integral_prod_mul A B, <- Measure.volume_eq_prod]
  have hP := (WithLp.volume_preserving_ofLp U V).integral_comp
    (MeasurableEquiv.toLp 2 (Prod U V)).symm.measurableEmbedding
    (fun z : Prod U V => A z.1 * B z.2)
  rw [<- hP, Real.fourier_eq']
  congr 1
  funext z
  change
    Complex.exp (((-2 * Real.pi * (inner Real (WithLp.ofLp z).1 (WithLp.ofLp w).1 +
      inner Real (WithLp.ofLp z).2 (WithLp.ofLp w).2) : Real) : Complex) * Complex.I) *
      (f (WithLp.ofLp z).1 * g (WithLp.ofLp z).2) =
    A (WithLp.ofLp z).1 * B (WithLp.ofLp z).2
  dsimp only [A, B]
  rw [<- mul_mul_mul_comm, <- Complex.exp_add]
  congr 2
  push_cast
  ring

universe u

private def piLpOptionSplit
    (J : Type*) [Fintype J]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace Real E] :
    LinearIsometryEquiv (RingHom.id Real) (PiLp 2 (fun _ : Option J => E))
      (WithLp 2 (Prod E (PiLp 2 (fun _ : J => E)))) := by
  let P := PiLp 2 (fun _ : J => E)
  let A : LinearEquiv (RingHom.id Real) (Option J -> E) (Prod E (J -> E)) :=
    LinearEquiv.piOptionEquivProd Real
  let B : LinearEquiv (RingHom.id Real) (Prod E (J -> E)) (Prod E P) :=
    (LinearEquiv.refl Real E).prodCongr (WithLp.linearEquiv 2 Real (J -> E)).symm
  let C := (A.trans B).withLpCongr 2
  refine { toLinearEquiv := C, norm_map' := fun x => ?_ }
  have hSq : norm (C x) ^ 2 = norm x ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2 (fun _ : Option J => E) x]
    change norm (x none) ^ 2 + norm (WithLp.toLp 2 (fun j : J => x (some j))) ^ 2 =
      Finset.univ.sum (fun j : Option J => norm (x j) ^ 2)
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : J => E), Fintype.sum_option]
  calc
    norm (C x) = Real.sqrt (norm (C x) ^ 2) := (Real.sqrt_sq (norm_nonneg (C x))).symm
    _ = Real.sqrt (norm x ^ 2) := congrArg Real.sqrt hSq
    _ = norm x := Real.sqrt_sq (norm_nonneg x)

private theorem piLpOptionSplit_fst
    (J : Type*) [Fintype J] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace Real E]
    (x : PiLp 2 (fun _ : Option J => E)) :
    (WithLp.ofLp (piLpOptionSplit J E x)).1 = x none := rfl

private theorem piLpOptionSplit_snd
    (J : Type*) [Fintype J] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace Real E]
    (x : PiLp 2 (fun _ : Option J => E)) (j : J) :
    (WithLp.ofLp (piLpOptionSplit J E x)).2 j = x (some j) := rfl

/-- Fourier transform separates over any finite collection of copies of a
real Euclidean space. -/
theorem fourier_tate_piLp_prod
    {J : Type u} [Fintype J] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E]
    (f : J -> E -> Complex) (w : PiLp 2 (fun _ : J => E)) :
    fourier (fun z : PiLp 2 (fun _ : J => E) => Finset.univ.prod (fun j => f j (z j))) w =
      Finset.univ.prod (fun j => fourier (f j) (w j)) := by
  classical
  let P (I : Type u) [Fintype I] : Prop :=
    forall (F : I -> E -> Complex) (x : PiLp 2 (fun _ : I => E)),
      fourier (fun z : PiLp 2 (fun _ : I => E) => Finset.univ.prod (fun i => F i (z i))) x =
        Finset.univ.prod (fun i => fourier (F i) (x i))
  have hAll (I : Type u) [Fintype I] : P I := by
    apply Fintype.induction_empty_option (P := P)
    . intro I L instF e h
      let : Fintype I := Fintype.ofEquiv L e.symm
      intro F x
      let A := LinearIsometryEquiv.piLpCongrLeft 2 Real E e.symm
      let G (i : I) := F (e i)
      let H (z : PiLp 2 (fun _ : I => E)) := Finset.univ.prod (fun i => G i (z i))
      have hA (z : PiLp 2 (fun _ : L => E)) (i : I) : A z i = z (e i) := rfl
      have hEq : (fun z : PiLp 2 (fun _ : L => E) => Finset.univ.prod (fun i => F i (z i))) =
          Function.comp H A := by
        funext z
        exact (Fintype.prod_equiv e (fun i => G i (A z i)) (fun i => F i (z i))
          (fun i => by rw [hA])).symm
      rw [hEq, Real.fourier_comp_linearIsometry]
      change fourier (fun z : PiLp 2 (fun _ : I => E) => Finset.univ.prod (fun i => G i (z i))) (A x) = _
      rw [h G (A x)]
      exact Fintype.prod_equiv e _ _ (fun i => by rw [hA])
    . intro F x
      let W := EuclideanSpace Real (PEmpty : Type u)
      let Y := PiLp 2 (fun _ : (PEmpty : Type u) => E)
      let A : LinearIsometryEquiv (RingHom.id Real) W Y :=
        { toLinearEquiv := LinearEquiv.ofSubsingleton (R := Real) W Y
          norm_map' := fun z => by
            rw [Subsingleton.elim z (0 : W)]
            simp }
      let H (z : Y) := Finset.univ.prod (fun i => F i (z i))
      change fourier H x = _
      rw [<- A.apply_symm_apply x, <- Real.fourier_comp_linearIsometry]
      rw [Real.fourier_eq', volume_euclideanSpace_eq_dirac]
      simp [H]
    . intro I instF h F x
      let E' := PiLp 2 (fun _ : I => E)
      let A := piLpOptionSplit I E
      let H (z : E') := Finset.univ.prod (fun i : I => F (some i) (z i))
      let F' (z : WithLp 2 (Prod E E')) := F none (WithLp.ofLp z).1 * H (WithLp.ofLp z).2
      have hEq : (fun z : PiLp 2 (fun _ : Option I => E) =>
          Finset.univ.prod (fun i => F i (z i))) = Function.comp F' A := by
        funext z
        simp only [Function.comp_apply, F', H, A, piLpOptionSplit_fst, piLpOptionSplit_snd]
        exact Fintype.prod_option (fun i => F i (z i))
      rw [hEq, Real.fourier_comp_linearIsometry]
      change fourier (fun p : WithLp 2 (Prod E E') =>
        F none (WithLp.ofLp p).1 * H (WithLp.ofLp p).2) (A x) = _
      rw [fourier_tate_withLp_prod, Fintype.prod_option]
      have hLast := h (fun i : I => F (some i)) (WithLp.ofLp (A x)).2
      change fourier H (WithLp.ofLp (A x)).2 = _ at hLast
      rw [hLast, piLpOptionSplit_fst]
      simp only [A, piLpOptionSplit_snd]
  exact hAll J f w

open NumberField NumberField.InfinitePlace
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev RealPlaces (K : Type*) [Field K] [NumberField K] :=
  {v : InfinitePlace K // v.IsReal}

private abbrev ComplexPlaces (K : Type*) [Field K] [NumberField K] :=
  {v : InfinitePlace K // v.IsComplex}

private abbrev RVec (K : Type*) [Field K] [NumberField K] := EuclideanSpace Real (RealPlaces K)
private abbrev CVec (K : Type*) [Field K] [NumberField K] := EuclideanSpace Complex (ComplexPlaces K)
private abbrev Mix (K : Type*) [Field K] := mixedEmbedding.mixedSpace K
private abbrev Mink (K : Type*) [Field K] [NumberField K] := DedekindZeta.Theta.minkowskiSpace K

private theorem mixedCoordinates_of_minkowski (x : Mink K) :
    (DedekindZeta.Theta.toMinkowski K).symm x =
      Prod.mk (fun v : RealPlaces K => (WithLp.ofLp x).1 v)
        (fun v : ComplexPlaces K => HSMul.hSMul (Inv.inv (Real.sqrt 2)) ((WithLp.ofLp x).2 v)) := by
  change (DedekindZeta.Theta.scaleMixed K).symm (mixedEmbedding.euclidean.toMixed K x) = _
  rw [DedekindZeta.Theta.scaleMixed_symm_apply]
  rfl

private theorem minkowskiCoordinates_real (x : Mix K) (v : RealPlaces K) :
    (WithLp.ofLp (DedekindZeta.Theta.toMinkowski K x)).1 v = x.1 v := rfl

private theorem minkowskiCoordinates_complex (x : Mix K) (v : ComplexPlaces K) :
    (WithLp.ofLp (DedekindZeta.Theta.toMinkowski K x)).2 v =
      HSMul.hSMul (Real.sqrt 2) (x.2 v) := rfl

/-- The mixed trace Fourier test separates by infinite place. Each complex
coordinate has the reciprocal dilation on its test function and the direct
dilation at the conjugate trace frequency. -/
theorem heckeTateDualInfiniteTest_placewise
    (f : SchwartzMap (Mix K) Complex)
    (gR : RealPlaces K -> Real -> Complex) (gC : ComplexPlaces K -> Complex -> Complex)
    (hf : forall z : Mix K, f z =
      Finset.univ.prod (fun v => gR v (z.1 v)) *
        Finset.univ.prod (fun v => gC v (z.2 v)))
    (x : Mix K) :
    heckeTateDualInfiniteTest f x =
      Finset.univ.prod (fun v => fourier (gR v) (x.1 v)) *
        Finset.univ.prod (fun v =>
          fourier (fun z : Complex => gC v (HSMul.hSMul (Inv.inv (Real.sqrt 2)) z))
            (HSMul.hSMul (Real.sqrt 2) (starRingEnd Complex (x.2 v)))) := by
  let FR (q : RVec K) := Finset.univ.prod (fun v => gR v (q v))
  let GC (v : ComplexPlaces K) (z : Complex) := gC v (HSMul.hSMul (Inv.inv (Real.sqrt 2)) z)
  let FC (q : CVec K) := Finset.univ.prod (fun v => GC v (q v))
  let w := DedekindZeta.Theta.toMinkowski K (DedekindZeta.Theta.conjMixed K x)
  have hTest : (fun q : Mink K => f ((DedekindZeta.Theta.toMinkowski K).symm q)) =
      (fun q : WithLp 2 (Prod (RVec K) (CVec K)) => FR (WithLp.ofLp q).1 * FC (WithLp.ofLp q).2) := by
    funext q
    rw [hf ((DedekindZeta.Theta.toMinkowski K).symm q),
      mixedCoordinates_of_minkowski (K := K) q]
  rw [heckeTateDualInfiniteTest_apply]
  change fourier (fun q : Mink K => f ((DedekindZeta.Theta.toMinkowski K).symm q)) w = _
  rw [hTest, fourier_tate_withLp_prod]
  have hR : fourier FR (WithLp.ofLp w).1 =
      Finset.univ.prod (fun v => fourier (gR v) ((WithLp.ofLp w).1 v)) :=
    fourier_tate_piLp_prod gR _
  have hC : fourier FC (WithLp.ofLp w).2 =
      Finset.univ.prod (fun v => fourier (GC v) ((WithLp.ofLp w).2 v)) :=
    fourier_tate_piLp_prod GC _
  rw [hR, hC]
  simp only [w, minkowskiCoordinates_real, minkowskiCoordinates_complex,
    DedekindZeta.Theta.conjMixed_fst, DedekindZeta.Theta.conjMixed_snd, GC]

private theorem circle_angularWeight_ext (m n : Int)
    (h : forall z : Circle, z ^ m = z ^ n) : m = n := by
  by_contra hNe
  let d : Real := (m - n : Int)
  have hd : Not (d = 0) := by
    change Not (((m - n : Int) : Real) = 0)
    exact_mod_cast sub_ne_zero.mpr hNe
  let t := Real.pi / d
  have hPow : Circle.exp t ^ (m - n) = 1 := by
    rw [zpow_sub, h]
    exact div_self' _
  have ht : HSMul.hSMul (m - n) t = Real.pi := by
    rw [zsmul_eq_mul]
    change d * (Real.pi / d) = Real.pi
    field_simp
  rw [<- Circle.exp_zsmul, ht] at hPow
  have hC := congrArg (fun z : Circle => (z : Complex)) hPow
  rw [Circle.coe_exp, Complex.exp_pi_mul_I] at hC
  norm_num at hC

/-- Inverting a Hecke character negates its angular exponent at each
complex place. -/
theorem complexInfiniteHeckeParameters_inverse_weight
    {K : Type*} [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    {v : InfinitePlace K} (hv : v.IsComplex) :
    (complexInfiniteHeckeParameters (unitaryHeckeInverse chi) hv).1 =
      -(complexInfiniteHeckeParameters chi hv).1 := by
  apply circle_angularWeight_ext
  intro z
  let a := Circle.toUnits z
  have hNorm : norm (a : Complex) = 1 := Circle.norm_coe z
  have hPhase : complexUnitPhase a = z := by
    apply Subtype.ext
    change (a : Complex) / (norm (a : Complex) : Complex) = (z : Complex)
    rw [hNorm, Complex.ofReal_one, div_one]
    rfl
  have h := complexInfiniteHeckeParameters_spec chi hv a
  have hi := complexInfiniteHeckeParameters_spec (unitaryHeckeInverse chi) hv a
  simp only [hNorm, hPhase, Real.log_one, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one] at h hi
  have hLocal : (complexInfiniteHeckeCharacter (unitaryHeckeInverse chi) hv a : Complex) =
      Inv.inv (complexInfiniteHeckeCharacter chi hv a : Complex) := by
    exact Circle.coe_inv _
  apply Subtype.ext
  calc
    _ = (complexInfiniteHeckeCharacter (unitaryHeckeInverse chi) hv a : Complex) := hi.symm
    _ = _ := hLocal
    _ = _ := by rw [h, zpow_neg, Circle.coe_inv]

/-- Inverting a real Hecke character preserves its parity. -/
theorem realInfiniteHeckeParameters_inverse_parity
    {K : Type*} [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    {v : InfinitePlace K} (hv : v.IsReal) :
    (realInfiniteHeckeParameters (unitaryHeckeInverse chi) hv).1 =
      (realInfiniteHeckeParameters chi hv).1 := by
  let a : Units Real := -1
  have ha : (a : Real) = -1 := rfl
  have haNeg : Not (0 < (a : Real)) := by rw [ha]; norm_num
  have haAbs : abs (a : Real) = 1 := by rw [ha]; norm_num
  let m := (realInfiniteHeckeParameters chi hv).1
  let n := (realInfiniteHeckeParameters (unitaryHeckeInverse chi) hv).1
  have hM := realInfiniteHeckeParameters_spec chi hv
  have hN := realInfiniteHeckeParameters_spec (unitaryHeckeInverse chi) hv
  have hm : (realInfiniteHeckeCharacter chi hv a : Complex) = (-1 : Complex) ^ m := by
    have h := hM.2 a
    simpa only [if_neg haNeg, haAbs, Real.log_one, mul_zero, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, mul_one, m] using h
  have hn : (realInfiniteHeckeCharacter (unitaryHeckeInverse chi) hv a : Complex) = (-1 : Complex) ^ n := by
    have h := hN.2 a
    simpa only [if_neg haNeg, haAbs, Real.log_one, mul_zero, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, mul_one, n] using h
  have hInv : (realInfiniteHeckeCharacter (unitaryHeckeInverse chi) hv a : Complex) =
      Inv.inv (realInfiniteHeckeCharacter chi hv a : Complex) := Circle.coe_inv _
  have hPow : (-1 : Complex) ^ n = (-1 : Complex) ^ m := by
    rw [<- hn, hInv, hm, <- inv_pow, inv_neg, inv_one]
  have hmCases : Or (m = 0) (m = 1) := by have hmBound : m <= 1 := hM.1; omega
  have hnCases : Or (n = 0) (n = 1) := by have hnBound : n <= 1 := hN.1; omega
  change n = m
  obtain hmZero | hmOne := hmCases
  . obtain hnZero | hnOne := hnCases
    . exact hnZero.trans hmZero.symm
    . rw [hnOne, hmZero, pow_one, pow_zero] at hPow
      norm_num at hPow
  . obtain hnZero | hnOne := hnCases
    . rw [hnZero, hmOne, pow_zero, pow_one] at hPow
      norm_num at hPow
    . exact hnOne.trans hmOne.symm

/-- The Euclidean complex coordinate in the mixed Tate model carries the
square-root-of-two dilation. Accounting for its Fourier Jacobian gives the
complex trace normalization. -/
theorem fourier_complex_sqrtTwo_inverse_dilation
    (f : Complex -> Complex) (w : Complex) :
    fourier (fun z : Complex => f (HSMul.hSMul (Inv.inv (Real.sqrt 2)) z))
        (HSMul.hSMul (Real.sqrt 2) w) =
      (2 : Complex) * fourier f (HSMul.hSMul (2 : Real) w) := by
  let c := Real.sqrt (2 : Real)
  have hC : 0 < c := Real.sqrt_pos.2 (by norm_num)
  have hC2 : c ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let H (z : Complex) :=
    Complex.exp (((-2 * Real.pi * inner Real z (HSMul.hSMul (2 : Real) w) : Real) : Complex) * Complex.I) * f z
  have hInner (z : Complex) : inner Real (HSMul.hSMul (Inv.inv c) z) (HSMul.hSMul (2 : Real) w) =
      inner Real z (HSMul.hSMul c w) := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_right]
    have hCmul : Inv.inv c * 2 = c := by
      rw [<- hC2, pow_two]
      field_simp
    rw [<- mul_assoc, hCmul]
  have hComp := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Complex) H hC.le
  rw [Complex.finrank_real_complex, hC2, Complex.real_smul, Complex.ofReal_ofNat] at hComp
  have hFL : fourier (fun z : Complex => f (HSMul.hSMul (Inv.inv c) z)) (HSMul.hSMul c w) =
      integral volume (fun z : Complex => H (HSMul.hSMul (Inv.inv c) z)) := by
    rw [Real.fourier_eq']
    congr 1
    funext z
    simp only [H, hInner, smul_eq_mul]
  have hFR : fourier f (HSMul.hSMul (2 : Real) w) = integral volume H := by
    simp only [Real.fourier_eq', smul_eq_mul, H]
  exact hFL.trans (hComp.trans (congrArg (fun z : Complex => 2 * z) hFR.symm))

/-- In the trace pairing, the Fourier transform of the antiholomorphic
monomial Gaussian is the corresponding holomorphic Gaussian with its phase. -/
theorem fourier_complexTateConjugatePolynomialGaussian_trace (n : Nat) (w : Complex) :
    (2 : Complex) *
      fourier (fun z : Complex => (starRingEnd Complex z) ^ n *
        (Real.exp (-2 * Real.pi * norm z ^ 2) : Complex)) (2 * starRingEnd Complex w) =
      (-Complex.I) ^ n * w ^ n * (Real.exp (-2 * Real.pi * norm w ^ 2) : Complex) := by
  let g (z : Complex) := z ^ n * (Real.exp (-2 * Real.pi * norm z ^ 2) : Complex)
  have hG : (fun z : Complex => (starRingEnd Complex z) ^ n *
        (Real.exp (-2 * Real.pi * norm z ^ 2) : Complex)) = Function.comp g Complex.conjLIE := by
    funext z
    change _ = g (Complex.conjLIE z)
    dsimp only [g]
    rw [Complex.conjLIE_apply]
    simp
  have hFreq : Complex.conjLIE (2 * starRingEnd Complex w) = 2 * w := by
    rw [Complex.conjLIE_apply]
    have hTwo : starRingEnd Complex (2 : Complex) = 2 := map_ofNat _ _
    rw [map_mul, hTwo, starRingEnd_apply, starRingEnd_apply, star_star]
  have hTrace := fourier_complexTatePolynomialGaussian_trace n (starRingEnd Complex w)
  rw [hG, Real.fourier_comp_linearIsometry, hFreq]
  simpa only [g, starRingEnd_apply, star_star, norm_star] using hTrace

private def tateComplexCoordinateGaussian (m : Int) (z : Complex) : Complex :=
  (if 0 <= m then (starRingEnd Complex z) ^ m.toNat else z ^ m.natAbs) *
    (Real.exp (-2 * Real.pi * norm z ^ 2) : Complex)

private theorem int_toNat_eq_natAbs_of_nonnegative (m : Int) (hm : 0 <= m) :
    m.toNat = m.natAbs := by
  cases m with
  | ofNat n => rfl
  | negSucc n => exact ((Int.negSucc_lt_zero n).not_ge hm).elim

private theorem fourier_tateComplexCoordinateGaussian_trace (m : Int) (w : Complex) :
    (2 : Complex) * fourier (tateComplexCoordinateGaussian m) (2 * starRingEnd Complex w) =
      (-Complex.I) ^ m.natAbs * tateComplexCoordinateGaussian (-m) w := by
  unfold tateComplexCoordinateGaussian
  by_cases hZero : m = 0
  . subst m
    simpa only [neg_zero, if_pos (le_refl (0 : Int)),
      Int.toNat_zero, Int.natAbs_zero, pow_zero, one_mul] using
        fourier_complexTatePolynomialGaussian_trace 0 w
  . by_cases hPos : 0 <= m
    . have hNeg : Not (0 <= -m) := by omega
      simpa only [if_pos hPos, if_neg hNeg,
        int_toNat_eq_natAbs_of_nonnegative m hPos, Int.natAbs_neg, mul_assoc] using
        fourier_complexTateConjugatePolynomialGaussian_trace m.natAbs w
    . have hPosNeg : 0 <= -m := by omega
      simpa only [if_neg hPos, if_pos hPosNeg,
        int_toNat_eq_natAbs_of_nonnegative (-m) hPosNeg, Int.natAbs_neg, mul_assoc] using
        fourier_complexTatePolynomialGaussian_trace m.natAbs w

/-- Fourier transform of a complex Tate polynomial Gaussian in its
scaled Euclidean coordinate, at the conjugate trace frequency. -/
theorem fourier_tateComplexCoordinateGaussian_dual (m : Int) (w : Complex) :
    fourier (fun z : Complex =>
      tateComplexCoordinateGaussian m (HSMul.hSMul (Inv.inv (Real.sqrt 2)) z))
      (HSMul.hSMul (Real.sqrt 2) (starRingEnd Complex w)) =
      (-Complex.I) ^ m.natAbs * tateComplexCoordinateGaussian (-m) w := by
  rw [fourier_complex_sqrtTwo_inverse_dilation, Complex.real_smul, Complex.ofReal_ofNat]
  exact fourier_tateComplexCoordinateGaussian_trace m w

private def tateRealPlaceGaussian
    (chi : UnitaryHeckeCharacter K) (v : RealPlaces K) (x : Real) : Complex :=
  (x : Complex) ^ (realInfiniteHeckeParameters chi v.property).1 *
    (Real.exp (-Real.pi * x ^ 2) : Complex)

private def tateComplexPlaceGaussian
    (chi : UnitaryHeckeCharacter K) (v : ComplexPlaces K) (z : Complex) : Complex :=
  tateComplexCoordinateGaussian (complexInfiniteHeckeParameters chi v.property).1 z

private theorem heckeTateInfiniteTest_placewise_eq (chi : UnitaryHeckeCharacter K) (x : Mix K) :
    heckeTateInfiniteTest chi x =
      (Finset.univ.prod (fun v => tateRealPlaceGaussian chi v (x.1 v))) *
        (Finset.univ.prod (fun v => tateComplexPlaceGaussian chi v (x.2 v))) := rfl

/-- The archimedean Fourier phase of the canonical Tate polynomial Gaussian. -/
def heckeTateArchimedeanFourierPhase (chi : UnitaryHeckeCharacter K) : Complex :=
  (-Complex.I) ^
    (Finset.univ.sum (fun v : RealPlaces K => (realInfiniteHeckeParameters chi v.property).1) +
      Finset.univ.sum (fun v : ComplexPlaces K => (complexInfiniteHeckeParameters chi v.property).1.natAbs))

/-- The Fourier phase is of absolute value one. -/
theorem norm_heckeTateArchimedeanFourierPhase (chi : UnitaryHeckeCharacter K) :
    norm (heckeTateArchimedeanFourierPhase chi) = 1 := by
  simp only [heckeTateArchimedeanFourierPhase, norm_pow, norm_neg, Complex.norm_I, one_pow]

/-- The adelic trace Fourier transform of the canonical archimedean test
is the canonical test of the inverse character times its unit phase. -/
theorem heckeTateDualInfiniteTest_eq_phase_mul_inverse
    (chi : UnitaryHeckeCharacter K) (f : SchwartzMap (Mix K) Complex)
    (hf : forall x : Mix K, f x = heckeTateInfiniteTest chi x) (x : Mix K) :
    heckeTateDualInfiniteTest f x =
      heckeTateArchimedeanFourierPhase chi * heckeTateInfiniteTest (unitaryHeckeInverse chi) x := by
  let opp := unitaryHeckeInverse chi
  let n (v : RealPlaces K) := (realInfiniteHeckeParameters chi v.property).1
  let m (v : ComplexPlaces K) := (complexInfiniteHeckeParameters chi v.property).1.natAbs
  let PR (v : RealPlaces K) := fourier (tateRealPlaceGaussian chi v) (x.1 v)
  let PC (v : ComplexPlaces K) :=
    fourier (fun z : Complex => tateComplexPlaceGaussian chi v (HSMul.hSMul (Inv.inv (Real.sqrt 2)) z))
      (HSMul.hSMul (Real.sqrt 2) (starRingEnd Complex (x.2 v)))
  have hR (v : RealPlaces K) : PR v = (-Complex.I) ^ n v * tateRealPlaceGaussian opp v (x.1 v) := by
    have hN : n v <= 1 := (realInfiniteHeckeParameters_spec chi v.property).1
    have hN01 : Or (n v = 0) (n v = 1) := by omega
    unfold PR tateRealPlaceGaussian
    rw [show (realInfiniteHeckeParameters opp v.property).1 = n v from
      realInfiniteHeckeParameters_inverse_parity chi v.property]
    simpa only [realTateGaussian, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow, mul_assoc] using fourier_realTatePolynomialGaussian (n v) hN01 (x.1 v)
  have hC (v : ComplexPlaces K) : PC v =
      (-Complex.I) ^ m v * tateComplexPlaceGaussian opp v (x.2 v) := by
    unfold PC tateComplexPlaceGaussian
    rw [show (complexInfiniteHeckeParameters opp v.property).1 =
        -(complexInfiniteHeckeParameters chi v.property).1 from
      complexInfiniteHeckeParameters_inverse_weight chi v.property]
    exact fourier_tateComplexCoordinateGaussian_dual
      (complexInfiniteHeckeParameters chi v.property).1 (x.2 v)
  have hRProd : Finset.univ.prod PR =
      (-Complex.I) ^ Finset.univ.sum n *
        Finset.univ.prod (fun v => tateRealPlaceGaussian opp v (x.1 v)) := by
    calc
      _ = Finset.univ.prod (fun v => (-Complex.I) ^ n v * tateRealPlaceGaussian opp v (x.1 v)) :=
        Finset.prod_congr rfl (fun v _ => hR v)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hCProd : Finset.univ.prod PC =
      (-Complex.I) ^ Finset.univ.sum m *
        Finset.univ.prod (fun v => tateComplexPlaceGaussian opp v (x.2 v)) := by
    calc
      _ = Finset.univ.prod (fun v => (-Complex.I) ^ m v * tateComplexPlaceGaussian opp v (x.2 v)) :=
        Finset.prod_congr rfl (fun v _ => hC v)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hFactor : heckeTateDualInfiniteTest f x = Finset.univ.prod PR * Finset.univ.prod PC :=
    heckeTateDualInfiniteTest_placewise f (tateRealPlaceGaussian chi) (tateComplexPlaceGaussian chi)
      (fun y => (hf y).trans (heckeTateInfiniteTest_placewise_eq chi y)) x
  rw [hFactor, hRProd, hCProd, heckeTateInfiniteTest_placewise_eq, heckeTateArchimedeanFourierPhase,
    pow_add]
  change _ = ((-Complex.I) ^ Finset.univ.sum n * (-Complex.I) ^ Finset.univ.sum m) *
    (Finset.univ.prod (fun v => tateRealPlaceGaussian opp v (x.1 v)) *
      Finset.univ.prod (fun v => tateComplexPlaceGaussian opp v (x.2 v)))
  ring

end Robin1984.GRH
