import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Pi
import Robin1984.GRH.GodementJacquetArchimedeanIwasawaProduct


/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Archimedean spherical Gaussian zeta integrals, exponential substitution, and the Gamma integral.
- Formalization note: Splits the original matrix Gaussian into diagonal and upper-entry factors and computes the weighted Gaussian integral in logarithmic coordinates.
- PROVENANCE-END
-/

/-!
# Gaussian integrals in archimedean Iwasawa coordinates

The matrix Gaussian and determinant reduce to the logarithmic diagonal
and the strict upper entries. Integrating the upper entries cancels
the additional diagonal powers. The remaining one-variable integrals
are absolutely convergent Gamma integrals.
-/

set_option autoImplicit false

open MeasureTheory

namespace Robin1984.GRH

section

variable {F : Type*} [RCLike F] {n : Nat}

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "N" => valuationUpperUnitriangularSubgroup F n

/-- The sum of squares of the norms of the entries of an archimedean matrix. -/
def archFrobeniusSq (R : M) : Real :=
  Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n => norm (R i j) ^ 2))

private theorem trace_mul_star_eq_archFrobeniusSq (R : M) :
    Matrix.trace (R * star R) = (archFrobeniusSq R : F) := by
  unfold archFrobeniusSq
  change Finset.univ.sum (fun i : Fin n => (R * star R) i i) = _
  rw [RCLike.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply, RCLike.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.star_apply, RCLike.star_def, RCLike.mul_conj, RCLike.ofReal_pow]

/-- The matrix norm square is invariant under right unitary multiplication. -/
theorem archFrobeniusSq_mul_unitary (R : M) (Q : Matrix.unitaryGroup (Fin n) F) :
    archFrobeniusSq (R * Q.val) = archFrobeniusSq R := by
  have h : (R * Q.val) * star (R * Q.val) = R * star R := by
    calc
      _ = R * ((Q.val * star Q.val) * star R) := by
        rw [star_mul]
        simp only [mul_assoc]
      _ = _ := by rw [Matrix.mem_unitaryGroup_iff.mp Q.property, one_mul]
  have hTrace := congrArg (fun a : M => Matrix.trace a) h
  change Matrix.trace ((R * Q.val) * star (R * Q.val)) = Matrix.trace (R * star R) at hTrace
  rw [trace_mul_star_eq_archFrobeniusSq, trace_mul_star_eq_archFrobeniusSq] at hTrace
  simpa only [RCLike.ofReal_re] using congrArg (fun x : F => RCLike.re x) hTrace

private def archStrictUpperScaledSq (a : Fin n -> Real) (u : N) : Real :=
  Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : Fin n =>
    if i < j then norm (HSMul.hSMul (a i) (u.val.val.val i j)) ^ 2 else 0))

private theorem archFrobeniusSq_diagonal_unitriangular (a : Fin n -> Real) (u : N) :
    archFrobeniusSq (Matrix.diagonal (fun i => (a i : F)) * u.val.val.val) =
      Finset.univ.sum (fun i : Fin n => (a i) ^ 2) + archStrictUpperScaledSq a u := by
  have hD (i : Fin n) : u.val.val.val i i = 1 := by
    have h : valuationTriangularDiagonalHom F n u.val = 1 := u.property
    exact congrArg (fun g : Units (Fin n -> F) => g.val i) h
  have hEntry (i j : Fin n) :
      (Matrix.diagonal (fun k => (a k : F)) * u.val.val.val) i j =
        HSMul.hSMul (a i) (u.val.val.val i j) := by
    rw [Matrix.diagonal_mul, RCLike.real_smul_eq_coe_mul]
  have hSplit (i j : Fin n) : norm (HSMul.hSMul (a i) (u.val.val.val i j)) ^ 2 =
      (if j = i then (a i) ^ 2 else 0) +
        (if i < j then norm (HSMul.hSMul (a i) (u.val.val.val i j)) ^ 2 else 0) := by
    by_cases h : j = i
    . subst j
      rw [if_pos rfl, if_neg (lt_irrefl i), add_zero, hD i, norm_smul,
        norm_one, mul_one, Real.norm_eq_abs, sq_abs]
    . rw [if_neg h, zero_add]
      by_cases hu : i < j
      . rw [if_pos hu]
      . rw [if_neg hu]
        have hlt : j < i := lt_of_le_of_ne (le_of_not_gt hu) h
        rw [u.val.property hlt, smul_zero, norm_zero, zero_pow two_ne_zero]
  have hRows (i : Fin n) :
      Finset.univ.sum (fun j : Fin n =>
        norm ((Matrix.diagonal (fun k => (a k : F)) * u.val.val.val) i j) ^ 2) =
      (a i) ^ 2 + Finset.univ.sum (fun j : Fin n =>
        if i < j then norm (HSMul.hSMul (a i) (u.val.val.val i j)) ^ 2 else 0) := by
    have hPoint : (fun j : Fin n =>
        norm ((Matrix.diagonal (fun k => (a k : F)) * u.val.val.val) i j) ^ 2) =
        (fun j : Fin n => (if j = i then (a i) ^ 2 else 0) +
          (if i < j then norm (HSMul.hSMul (a i) (u.val.val.val i j)) ^ 2 else 0)) := by
      funext j
      rw [hEntry]
      exact hSplit i j
    rw [hPoint, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [archFrobeniusSq, archStrictUpperScaledSq, hRows, Finset.sum_add_distrib]

private theorem archUnipotentScaledKernel_gaussian (b : Real) (a : Fin n -> Real) (u : N) :
    archUnipotentScaledKernel F (fun x => Real.exp (-b * norm x ^ 2)) n a u =
      Real.exp (-b * archStrictUpperScaledSq a u) := by
  induction n with
  | zero => simp [archUnipotentScaledKernel, archStrictUpperScaledSq]
  | succ n ih =>
    let p := valuationUnitriangularFirstRowHomeomorph F n u
    let aTail : Fin n -> Real := fun i => a i.succ
    let tail := archStrictUpperScaledSq aTail p.2
    let row := Finset.univ.sum (fun j : Fin n => norm (HSMul.hSMul (a 0) (p.1 j)) ^ 2)
    have hSplit : archStrictUpperScaledSq a u = tail + row := by
      change Finset.univ.sum (fun i : Fin (n + 1) =>
          Finset.univ.sum (fun j : Fin (n + 1) =>
            if i < j then norm (HSMul.hSMul (a i) (u.val.val.val i j)) ^ 2 else 0)) =
        tail + row
      rw [Fin.sum_univ_succ]
      have hTop : Finset.univ.sum (fun j : Fin (n + 1) =>
          if 0 < j then norm (HSMul.hSMul (a 0) (u.val.val.val 0 j)) ^ 2 else 0) = row := by
        rw [Fin.sum_univ_succ]
        simp only [lt_irrefl, if_false, zero_add, Fin.succ_pos, if_true]
        rfl
      have hTail : Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : Fin (n + 1) =>
            if i.succ < j then norm (HSMul.hSMul (a i.succ) (u.val.val.val i.succ j)) ^ 2 else 0)) =
        tail := by
        unfold tail archStrictUpperScaledSq
        apply Finset.sum_congr rfl
        intro i _
        rw [Fin.sum_univ_succ]
        have hz : Not (i.succ < (0 : Fin (n + 1))) := not_lt_of_ge (Fin.zero_le _)
        simp only [hz, if_false, zero_add, Fin.succ_lt_succ_iff]
        rfl
      rw [hTop, hTail, add_comm]
    have hRow : Finset.univ.prod (fun j : Fin n =>
        Real.exp (-b * norm (HSMul.hSMul (a 0) (p.1 j)) ^ 2)) = Real.exp (-b * row) := by
      rw [<- Real.exp_sum]
      unfold row
      rw [Finset.mul_sum]
    change archUnipotentScaledKernel F (fun x => Real.exp (-b * norm x ^ 2)) n aTail p.2 *
      Finset.univ.prod (fun j : Fin n =>
        Real.exp (-b * norm (HSMul.hSMul (a 0) (p.1 j)) ^ 2)) = _
    rw [ih aTail p.2, hRow, hSplit, <- Real.exp_add]
    change Real.exp (-b * tail + -b * row) = Real.exp (-b * (tail + row))
    rw [mul_add]

/-- The matrix Gaussian splits into the diagonal and strict upper entry kernels. -/
theorem archMatrixGaussian_diagonal_unitriangular_unitary
    (b : Real) (a : Fin n -> Real) (u : N) (Q : Matrix.unitaryGroup (Fin n) F) :
    Real.exp (-b * archFrobeniusSq
      ((Matrix.diagonal (fun i => (a i : F)) * u.val.val.val) * Q.val)) =
      Finset.univ.prod (fun i : Fin n => Real.exp (-b * (a i) ^ 2)) *
        archUnipotentScaledKernel F (fun x => Real.exp (-b * norm x ^ 2)) n a u := by
  rw [archFrobeniusSq_mul_unitary, archFrobeniusSq_diagonal_unitriangular,
    archUnipotentScaledKernel_gaussian, <- Real.exp_sum, mul_add, Real.exp_add,
    Finset.mul_sum]

/-- The determinant of a unitary matrix has norm one. -/
theorem norm_det_archUnitary (Q : Matrix.unitaryGroup (Fin n) F) :
    norm Q.val.det = 1 := by
  have h := congrArg (fun A : M => A.det) (Matrix.mem_unitaryGroup_iff.mp Q.property)
  change (Q.val * star Q.val).det = (1 : M).det at h
  rw [Matrix.det_mul, Matrix.det_one] at h
  change Q.val.det * (Matrix.conjTranspose Q.val).det = 1 at h
  rw [Matrix.det_conjTranspose, RCLike.star_def, RCLike.mul_conj] at h
  have hCast : ((norm Q.val.det ^ (2 : Nat) : Real) : F) = 1 := by
    rw [RCLike.ofReal_pow]
    exact h
  have hSq : norm Q.val.det ^ (2 : Nat) = 1 := by
    simpa only [RCLike.ofReal_re, RCLike.one_re] using congrArg (fun z : F => RCLike.re z) hCast
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] using congrArg Real.sqrt hSq

private theorem det_archUnitriangular (u : N) : (u.val.val.val : M).det = 1 := by
  have hd (i : Fin n) : u.val.val.val i i = 1 := by
    have h : valuationTriangularDiagonalHom F n u.val = 1 := u.property
    exact congrArg (fun g : Units (Fin n -> F) => g.val i) h
  rw [Matrix.det_of_isUpperTriangular u.val.property]
  simp only [hd, Finset.prod_const_one]

/-- The determinant norm is the product of the positive diagonal entries. -/
theorem norm_det_diagonal_unitriangular_unitary
    (a : Fin n -> Real) (ha : forall i, 0 < a i)
    (u : N) (Q : Matrix.unitaryGroup (Fin n) F) :
    norm (((Matrix.diagonal (fun i => (a i : F)) * u.val.val.val) * Q.val).det) =
      Finset.univ.prod a := by
  rw [Matrix.det_mul, Matrix.det_mul, det_archUnitriangular, mul_one, norm_mul,
    norm_det_archUnitary, mul_one, Matrix.det_diagonal, <- RCLike.ofReal_prod]
  rw [RCLike.norm_ofReal, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (ha i).le))]

end

open scoped Real

private theorem radialGaussianMellin (b : Real) (hb : 0 < b)
    (w : Complex) (hw : 0 < w.re) :
    let g : Real -> Complex := fun t => (Real.exp (-b * t ^ 2) : Complex)
    And (MellinConvergent g w)
      (mellin g w = HSMul.hSMul (Inv.inv (2 : Real))
        ((1 / (b : Complex)) ^ (w / 2) * Complex.Gamma (w / 2))) := by
  let f : Real -> Complex := fun t => (Real.exp (-t) : Complex)
  let q : Real -> Complex := fun t => f (b * t)
  let g : Real -> Complex := fun t => (Real.exp (-b * t ^ 2) : Complex)
  have hCast : ((2 : Real) : Complex) = 2 := Complex.ofReal_ofNat 2
  have hHalf : 0 < (w / 2).re := by
    rw [<- hCast, Complex.div_ofReal_re]
    exact div_pos hw two_pos
  have hG : g = fun t => q (t ^ (2 : Real)) := by
    funext t
    change (Real.exp (-b * t ^ (2 : Nat)) : Complex) =
      (Real.exp (-(b * t ^ (2 : Real))) : Complex)
    rw [Real.rpow_two, neg_mul]
  have hF : MellinConvergent f (w / 2) := by
    change IntegrableOn (fun t : Real =>
      HSMul.hSMul ((t : Complex) ^ (w / 2 - 1)) (f t)) (Set.Ioi 0)
    simpa only [f, smul_eq_mul, mul_comm] using Complex.GammaIntegral_convergent hHalf
  have hQ : MellinConvergent q (w / 2) :=
    (MellinConvergent.comp_mul_left hb).mpr hF
  have hConv : MellinConvergent g w := by
    rw [hG]
    apply (MellinConvergent.comp_rpow (ne_of_gt (two_pos : (0 : Real) < 2))).mpr
    rw [hCast]
    exact hQ
  refine And.intro hConv ?_
  have hInt : mellin q (w / 2) =
      (1 / (b : Complex)) ^ (w / 2) * Complex.Gamma (w / 2) := by
    unfold mellin
    rw [<- Complex.integral_cpow_mul_exp_neg_mul_Ioi hHalf hb]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [q, f, smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
  change mellin g w = _
  rw [hG, mellin_comp_rpow, abs_of_pos (two_pos : (0 : Real) < 2), hCast, hInt]

private theorem cpow_cancel_positive_nat_shift (r : Real) (hr : 0 < r)
    (z : Complex) (k : Nat) :
    ((r : Complex) ^ (z + (k : Complex))) * ((Inv.inv (r ^ k) : Real) : Complex) =
      (r : Complex) ^ z := by
  have hR : Not ((r : Complex) = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  rw [Complex.cpow_add _ _ hR, Complex.cpow_natCast, Complex.ofReal_inv, Complex.ofReal_pow,
    mul_assoc]
  have hk : Not (((r : Complex) ^ k) = 0) := pow_ne_zero k hR
  rw [<- div_eq_mul_inv, div_self hk, mul_one]

private theorem logRadialGaussianIntegral
    (b : Real) (hb : 0 < b) (w : Complex) (hw : 0 < w.re) :
    let H (x : Real) := ((Real.exp x : Real) : Complex) ^ w *
      (Real.exp (-b * Real.exp x ^ (2 : Nat)) : Complex)
    And (Integrable H)
      (integral volume H = HSMul.hSMul (Inv.inv (2 : Real))
        ((1 / (b : Complex)) ^ (w / 2) * Complex.Gamma (w / 2))) := by
  let f (t : Real) := (t : Complex) ^ (w - 1) * (Real.exp (-b * t ^ (2 : Nat)) : Complex)
  let H (x : Real) := ((Real.exp x : Real) : Complex) ^ w *
    (Real.exp (-b * Real.exp x ^ (2 : Nat)) : Complex)
  have hRad := radialGaussianMellin b hb w hw
  have hf : IntegrableOn f (Set.Ioi 0) := by
    simpa only [f, MellinConvergent, smul_eq_mul] using hRad.1
  have hi : integral ((volume : Measure Real).restrict (Set.Ioi 0)) f =
      HSMul.hSMul (Inv.inv (2 : Real))
        ((1 / (b : Complex)) ^ (w / 2) * Complex.Gamma (w / 2)) := by
    simpa only [f, mellin, smul_eq_mul] using hRad.2
  have hImage : Real.exp '' (Set.univ : Set Real) = Set.Ioi 0 := by
    ext t
    constructor
    . intro ht
      choose x hx using ht
      rw [<- hx.2]
      exact Real.exp_pos x
    . intro ht
      exact Exists.intro (Real.log t) (And.intro (Set.mem_univ _) (Real.exp_log ht))
  have hDeriv (x : Real) (_ : Membership.mem (Set.univ : Set Real) x) :
      HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hKernel (x : Real) : HSMul.hSMul (abs (Real.exp x)) (f (Real.exp x)) = H x := by
    let r : Complex := (Real.exp x : Real)
    have hr : Not (r = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos x))
    have hPow : r * r ^ (w - 1) = r ^ w := by
      calc
        _ = r ^ (1 : Complex) * r ^ (w - 1) :=
          congrArg (fun z => z * r ^ (w - 1)) (Complex.cpow_one r).symm
        _ = r ^ ((1 : Complex) + (w - 1)) := (Complex.cpow_add _ _ hr).symm
        _ = _ := by rw [add_comm 1 (w - 1), sub_add_cancel]
    rw [abs_of_pos (Real.exp_pos x), Complex.real_smul]
    change r * (r ^ (w - 1) * _) = r ^ w * _
    rw [<- mul_assoc, hPow]
  have hConv := integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ hDeriv Real.exp_injective.injOn f
  have hI := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ hDeriv Real.exp_injective.injOn f
  simp only [hImage, hKernel, integrableOn_univ, Measure.restrict_univ] at hConv hI
  exact And.intro (hConv.mp hf) (hI.symm.trans hi)

private theorem logRadialGaussianProduct
    (b : Real) (hb : 0 < b) (n : Nat) (w : Fin n -> Complex) (hw : forall i, 0 < (w i).re) :
    let H (i : Fin n) (x : Real) := ((Real.exp x : Real) : Complex) ^ (w i) *
      (Real.exp (-b * Real.exp x ^ (2 : Nat)) : Complex)
    let M := Measure.pi (fun _ : Fin n => (volume : Measure Real))
    And (Integrable (fun x : Fin n -> Real => Finset.univ.prod (fun i => H i (x i))) M)
      (integral M (fun x : Fin n -> Real => Finset.univ.prod (fun i => H i (x i))) =
        Finset.univ.prod (fun i : Fin n => HSMul.hSMul (Inv.inv (2 : Real))
          ((1 / (b : Complex)) ^ (w i / 2) * Complex.Gamma (w i / 2)))) := by
  let H (i : Fin n) (x : Real) := ((Real.exp x : Real) : Complex) ^ (w i) *
    (Real.exp (-b * Real.exp x ^ (2 : Nat)) : Complex)
  have h (i : Fin n) := logRadialGaussianIntegral b hb (w i) (hw i)
  refine And.intro (Integrable.fintype_prod (fun i => (h i).1)) ?_
  change integral (Measure.pi (fun _ : Fin n => (volume : Measure Real)))
    (fun x : Fin n -> Real => Finset.univ.prod (fun i => H i (x i))) = _
  rw [integral_fin_nat_prod_eq_prod H]
  exact Finset.prod_congr rfl (fun i _ => (h i).2)

private theorem integral_nonnegative_real_fibers
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (nu : Measure Y) [SFinite mu] [SFinite nu]
    (c : X -> Complex) (f : X -> Y -> Real)
    (hMeas : AEStronglyMeasurable (fun p : Prod X Y => c p.1 * (f p.1 p.2 : Complex))
      (mu.prod nu))
    (hF : forall x, Integrable (f x) nu)
    (hPos : forall x y, 0 <= f x y)
    (hOuter : Integrable (fun x => c x * ((integral nu (f x) : Real) : Complex)) mu) :
    And (Integrable (fun p : Prod X Y => c p.1 * (f p.1 p.2 : Complex)) (mu.prod nu))
      (integral (mu.prod nu) (fun p : Prod X Y => c p.1 * (f p.1 p.2 : Complex)) =
        integral mu (fun x => c x * ((integral nu (f x) : Real) : Complex))) := by
  have hNorm (x : X) :
      integral nu (fun y => norm (c x * (f x y : Complex))) =
        norm (c x * ((integral nu (f x) : Real) : Complex)) := by
    have hSummand (y : Y) : norm (c x * (f x y : Complex)) = norm (c x) * f x y := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hPos x y)]
    have hNonneg : 0 <= integral nu (f x) := integral_nonneg (hPos x)
    simp_rw [hSummand]
    rw [integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hNonneg]
  have hJoint : Integrable (fun p : Prod X Y => c p.1 * (f p.1 p.2 : Complex)) (mu.prod nu) := by
    apply (integrable_prod_iff hMeas).mpr
    constructor
    . exact Filter.Eventually.of_forall (fun x => (hF x).ofReal.const_mul (c x))
    . simp_rw [hNorm]
      exact hOuter.norm
  refine And.intro hJoint ?_
  rw [integral_prod _ hJoint]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change integral nu (fun y : Y => c x * (f x y : Complex)) =
      c x * ((integral nu (f x) : Real) : Complex)
    rw [integral_const_mul, integral_complex_ofReal])

private theorem cancel_scaledGaussian_row_weights
    (b c : Real) (n d : Nat) (w : Fin n -> Complex) (a : Fin n -> Real)
    (ha : forall i, 0 < a i) :
    let m (i : Fin n) := n - (i.val + 1)
    let G (i : Fin n) : Complex := (Real.exp (-b * a i ^ (2 : Nat)) : Complex)
    (Finset.univ.prod (fun i : Fin n => (a i : Complex) ^ (w i + ((d * m i : Nat) : Complex)) * G i)) *
      ((Finset.univ.prod (fun i : Fin n => ((Inv.inv (a i ^ d)) * c) ^ (m i)) : Real) : Complex) =
      Finset.univ.prod (fun i : Fin n => (c : Complex) ^ (m i)) *
        Finset.univ.prod (fun i : Fin n => (a i : Complex) ^ (w i) * G i) := by
  let m (i : Fin n) := n - (i.val + 1)
  let T (i : Fin n) := ((Inv.inv (a i ^ d)) * c) ^ (m i)
  let G (i : Fin n) : Complex := (Real.exp (-b * a i ^ (2 : Nat)) : Complex)
  let h (i : Fin n) := (a i : Complex) ^ (w i + ((d * m i : Nat) : Complex)) * G i
  change Finset.univ.prod h * ((Finset.univ.prod T : Real) : Complex) = _
  rw [Complex.ofReal_prod]
  rw [<- Finset.prod_mul_distrib, <- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hScale : ((T i : Real) : Complex) =
      ((Inv.inv (a i ^ (d * m i)) : Real) : Complex) * (c : Complex) ^ (m i) := by
    unfold T
    rw [mul_pow, inv_pow, <- pow_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [hScale]
  calc
    _ = ((a i : Complex) ^ (w i + ((d * m i : Nat) : Complex)) *
        ((Inv.inv (a i ^ (d * m i)) : Real) : Complex)) * ((c : Complex) ^ (m i) * G i) := by
      ac_rfl
    _ = _ := by
      rw [cpow_cancel_positive_nat_shift _ (ha i)]
      change (a i : Complex) ^ (w i) * ((c : Complex) ^ (m i) * G i) =
        (c : Complex) ^ (m i) * ((a i : Complex) ^ (w i) * G i)
      ac_rfl

section SphericalGaussian

variable (F : Type*) [NormedField F] [InnerProductSpace Real F] [FiniteDimensional Real F]
  [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
  [SigmaFinite (volume : Measure F)]

local notation "Y" n => (Fin n -> Real)
local notation "N" n => valuationUpperUnitriangularSubgroup F n

local instance gaussianUnipotentMeasurableSpace (n : Nat) : MeasurableSpace (N n) := borel (N n)
local instance gaussianUnipotentBorelSpace (n : Nat) : BorelSpace (N n) := BorelSpace.mk rfl

omit [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
  [SigmaFinite (volume : Measure F)] [SecondCountableTopology F] in
private theorem continuous_archUnipotentScaledKernel
    (f : F -> Real) (hf : Continuous f) (n : Nat) :
    Continuous (fun p : Prod (Y n) (N n) => archUnipotentScaledKernel F f n p.1 p.2) := by
  induction n with
  | zero =>
    change Continuous (fun _ : Prod (Y 0) (N 0) => (1 : Real))
    exact continuous_const
  | succ n ih =>
    let J := valuationUnitriangularFirstRowHomeomorph F n
    let A (p : Prod (Y (n + 1)) (N (n + 1))) : Y n := fun i => p.1 i.succ
    have hA : Continuous A := continuous_pi (fun i => (continuous_apply i.succ).comp continuous_fst)
    have hv : Continuous (fun p : Prod (Y (n + 1)) (N (n + 1)) => J p.2) :=
      J.continuous.comp continuous_snd
    have hTail : Continuous (fun p : Prod (Y (n + 1)) (N (n + 1)) =>
        archUnipotentScaledKernel F f n (A p) (J p.2).2) := ih.comp (hA.prodMk hv.snd)
    have hRow : Continuous (fun p : Prod (Y (n + 1)) (N (n + 1)) =>
        Finset.univ.prod (fun j : Fin n => f (HSMul.hSMul (p.1 0) ((J p.2).1 j)))) := by
      apply continuous_finsetProd
      intro j _
      exact hf.comp (((continuous_apply 0).comp continuous_fst).smul ((continuous_apply j).comp hv.fst))
    exact hTail.mul hRow

omit [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
  [SigmaFinite (volume : Measure F)] [SecondCountableTopology F] in
private theorem nonneg_archUnipotentScaledKernel
    (f : F -> Real) (hf : forall x, 0 <= f x) (n : Nat) (a : Y n) (u : N n) :
    0 <= archUnipotentScaledKernel F f n a u := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih =>
    let p := valuationUnitriangularFirstRowHomeomorph F n u
    change 0 <= archUnipotentScaledKernel F f n (fun i => a i.succ) p.2 *
      Finset.univ.prod (fun j : Fin n => f (HSMul.hSMul (a 0) (p.1 j)))
    exact mul_nonneg (ih (fun i => a i.succ) p.2) (Finset.prod_nonneg (fun j _ => hf _))

/-- The weighted Gaussian in diagonal logarithms and unitriangular entries is
absolutely integrable and evaluates to the stated product of Gamma factors. -/
theorem integrable_integral_archSphericalGaussian
    (b : Real) (hb : 0 < b) (n : Nat) (w : Fin n -> Complex) (hw : forall i, 0 < (w i).re) :
    let d := Module.finrank Real F
    let m (i : Fin n) := n - (i.val + 1)
    let C := Real.rpow (Real.pi / b) ((d : Real) / 2)
    let a (x : Y n) (i : Fin n) := Real.exp (x i)
    let g (x : F) := Real.exp (-b * norm x ^ (2 : Nat))
    let K (p : Prod (Y n) (N n)) :=
      Finset.univ.prod (fun i : Fin n => (a p.1 i : Complex) ^ (w i + ((d * m i : Nat) : Complex)) *
        (Real.exp (-b * (a p.1 i) ^ (2 : Nat)) : Complex)) *
        (archUnipotentScaledKernel F g n (a p.1) p.2 : Complex)
    let mu := Measure.pi (fun _ : Fin n => (volume : Measure Real))
    let nu := valuationUnitriangularProductMeasure F volume n
    And (Integrable K (mu.prod nu))
      (integral (mu.prod nu) K =
        Finset.univ.prod (fun i : Fin n => (C : Complex) ^ (m i)) *
          Finset.univ.prod (fun i : Fin n => HSMul.hSMul (Inv.inv (2 : Real))
            ((1 / (b : Complex)) ^ (w i / 2) * Complex.Gamma (w i / 2)))) := by
  let d := Module.finrank Real F
  let m (i : Fin n) := n - (i.val + 1)
  let C := Real.rpow (Real.pi / b) ((d : Real) / 2)
  let a (x : Y n) (i : Fin n) := Real.exp (x i)
  let g (x : F) := Real.exp (-b * norm x ^ (2 : Nat))
  let c (x : Y n) :=
    Finset.univ.prod (fun i : Fin n => (a x i : Complex) ^ (w i + ((d * m i : Nat) : Complex)) *
      (Real.exp (-b * (a x i) ^ (2 : Nat)) : Complex))
  let u (x : Y n) (v : N n) := archUnipotentScaledKernel F g n (a x) v
  let mu := Measure.pi (fun _ : Fin n => (volume : Measure Real))
  let nu := valuationUnitriangularProductMeasure F volume n
  let R (x : Y n) := Finset.univ.prod (fun i : Fin n => (a x i : Complex) ^ (w i) *
    (Real.exp (-b * (a x i) ^ (2 : Nat)) : Complex))
  let CF := Finset.univ.prod (fun i : Fin n => (C : Complex) ^ (m i))
  let _ : SecondCountableTopology (N n) := archUnipotent_secondCountable F n
  let _ : SigmaFinite nu := sigmaFinite_valuationUnitriangularProductMeasure F volume n
  have ha (x : Y n) (i : Fin n) : 0 < a x i := Real.exp_pos _
  have hG (x : Y n) := integrable_integral_archUnipotentGaussian F b hb n (a x) (ha x)
  have hReal : Continuous a :=
    continuous_pi (fun i => Real.continuous_exp.comp (continuous_apply i))
  have hg : Continuous g := Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))
  have hU : Continuous (fun p : Prod (Y n) (N n) => u p.1 p.2) :=
    (continuous_archUnipotentScaledKernel F g hg n).comp
      ((hReal.comp continuous_fst).prodMk continuous_snd)
  have hC : Continuous c := by
    apply continuous_finsetProd
    intro i _
    have hA : Continuous (fun x : Y n => a x i) := (continuous_apply i).comp hReal
    have hBase : Continuous (fun x : Y n => (a x i : Complex)) := Complex.continuous_ofReal.comp hA
    have hPow : Continuous (fun x : Y n => (a x i : Complex) ^ (w i + ((d * m i : Nat) : Complex))) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      have hx : Membership.mem Complex.slitPlane (a x i : Complex) :=
        Complex.ofReal_mem_slitPlane.mpr (ha x i)
      exact ContinuousAt.comp (g := fun z : Complex => z ^ (w i + ((d * m i : Nat) : Complex)))
        (continuousAt_cpow_const hx) hBase.continuousAt
    exact hPow.mul (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (hA.pow 2))))
  have hMeas : AEStronglyMeasurable (fun p : Prod (Y n) (N n) => c p.1 * (u p.1 p.2 : Complex))
      (mu.prod nu) :=
    ((hC.comp continuous_fst).mul (Complex.continuous_ofReal.comp hU)).measurable.aestronglyMeasurable
  have hPos (x : Y n) (v : N n) : 0 <= u x v :=
    nonneg_archUnipotentScaledKernel F g (fun y => (Real.exp_pos _).le) n (a x) v
  have hCancel (x : Y n) : c x * ((integral nu (u x) : Real) : Complex) = CF * R x := by
    change c x * ((integral nu (archUnipotentScaledKernel F g n (a x)) : Real) : Complex) = _
    rw [(hG x).2]
    exact cancel_scaledGaussian_row_weights b C n d w (a x) (ha x)
  have hRad := logRadialGaussianProduct b hb n w hw
  have hOuter : Integrable (fun x : Y n => c x * ((integral nu (u x) : Real) : Complex)) mu := by
    simp_rw [hCancel]
    exact hRad.1.const_mul CF
  have hInt := integral_nonnegative_real_fibers mu nu c u hMeas (fun x => (hG x).1) hPos hOuter
  refine And.intro hInt.1 ?_
  change integral (mu.prod nu) (fun p : Prod (Y n) (N n) => c p.1 * (u p.1 p.2 : Complex)) = _
  rw [hInt.2]
  simp_rw [hCancel]
  rw [integral_const_mul]
  congr 1
  exact hRad.2

end SphericalGaussian

end Robin1984.GRH
