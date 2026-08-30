import Robin1984.NicolasLandau.RobinWeightedIntegral
import Robin1984.NicolasLandau.WeightedMellin
import Robin1984.NicolasLandau.WeightedZeroPairing
import Robin1984.NicolasLandau.XiDivisorCriticalLine
import PrimeNumberTheoremAnd.IEANTN.RobinXiZeroSummability

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# Absolute integration of the complete xi divisor series

Fractional inverse moments are used only for the interchange.  Robin's final
zero estimate continues to use the exact inverse-square sum.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set

theorem inv_rpow_three_halves_eq {r : Real} (hr : 0 < r) :
    (Inv.inv r) ^ (3 / 2 : Real) = 1 / (r * Real.sqrt r) := by
  rw [<- Real.rpow_neg_eq_inv_rpow, Real.rpow_neg hr.le]
  rw [show (3 / 2 : Real) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hr, Real.rpow_one, <- Real.sqrt_eq_rpow, one_div]

/-- A scalar triangle inequality turns a two-resolvent product into two
integrable three-halves weights with a summable external factor. -/
theorem inv_triple_product_le_three_halves
    {R a b : Real} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hTriangle : R <= a + b) :
    1 / (R * a * b) <=
      2 * (Inv.inv R) ^ (3 / 2 : Real) *
        ((Inv.inv a) ^ (3 / 2 : Real) + (Inv.inv b) ^ (3 / 2 : Real)) := by
  rw [inv_rpow_three_halves_eq hR, inv_rpow_three_halves_eq ha,
    inv_rpow_three_halves_eq hb]
  have hRSqrt : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have haSqrt : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hbSqrt : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hOrdered : forall u v : Real, 0 < u -> 0 < v -> u <= v ->
      R <= u + v ->
      1 / (R * u * v) <= 2 * (1 / (R * Real.sqrt R)) * (1 / (u * Real.sqrt u)) := by
    intro u v hu hv huv hRuv
    have hUSqrt : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
    have hProductSq : (Real.sqrt R * Real.sqrt u)^2 <= (2 * v)^2 := by
      rw [mul_pow, Real.sq_sqrt hR.le, Real.sq_sqrt hu.le]
      have hRu : R * u <= (u + v) * u := mul_le_mul_of_nonneg_right hRuv hu.le
      have huSq : u * u <= v * v := mul_self_le_mul_self hu.le huv
      have hvu : v * u <= v * v := mul_le_mul_of_nonneg_left huv hv.le
      nlinarith [sq_nonneg v]
    have hProduct : Real.sqrt R * Real.sqrt u <= 2 * v := by
      nlinarith [sq_nonneg (Real.sqrt R * Real.sqrt u - 2 * v)]
    have hDen : R * Real.sqrt R * (u * Real.sqrt u) / 2 <= R * u * v := by
      nlinarith [mul_le_mul_of_nonneg_left hProduct (by positivity : 0 <= R * u)]
    calc
      1 / (R * u * v) <= 1 / (R * Real.sqrt R * (u * Real.sqrt u) / 2) :=
        one_div_le_one_div_of_le (by positivity) hDen
      _ = 2 * (1 / (R * Real.sqrt R)) * (1 / (u * Real.sqrt u)) := by
        field_simp
  rcases le_total a b with hab | hba
  . have h := hOrdered a b ha hb hab hTriangle
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_right (by positivity)
  . have h := hOrdered b a hb ha hba (by linarith)
    have hSwap : R * a * b = R * b * a := by ring
    rw [hSwap]
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_left (by positivity)

/-- The fractional weight is integrable on each vertical line used in the
safe-line interchange. -/
theorem integrable_three_halves_verticalLine
    {a : Real} (ha : 1 <= a) :
    Integrable (fun t : Real =>
      (Inv.inv (norm ((a : Complex) + (t : Complex) * Complex.I))) ^ (3 / 2 : Real)) := by
  have hBase : Integrable (fun t : Real => (1 + norm t) ^ (-(3 / 2 : Real))) :=
    integrable_one_add_norm (by norm_num)
  have hMajor := hBase.const_mul ((2 : Real) ^ (3 / 2 : Real))
  have hMeas : Measurable (fun t : Real =>
      (Inv.inv (norm ((a : Complex) + (t : Complex) * Complex.I))) ^ (3 / 2 : Real)) := by
    fun_prop
  apply hMajor.mono' hMeas.aestronglyMeasurable
  filter_upwards with t
  let s : Complex := (a : Complex) + (t : Complex) * Complex.I
  have hRe : a <= norm s := by
    calc
      a <= abs a := le_abs_self a
      _ <= norm s := by simpa [s] using Complex.abs_re_le_norm s
  have hIm : norm t <= norm s := by
    simpa [s, Real.norm_eq_abs] using Complex.abs_im_le_norm s
  have hNormPos : 0 < norm s := by linarith
  have hOnePos : 0 < 1 + norm t := by positivity
  have hLower : (1 + norm t) / 2 <= norm s := by linarith
  have hInv : Inv.inv (norm s) <= 2 * Inv.inv (1 + norm t) := by
    have h := one_div_le_one_div_of_le (by positivity : 0 < (1 + norm t) / 2) hLower
    simpa only [one_div, inv_div, div_eq_mul_inv, mul_inv, inv_inv,
      one_mul, mul_one, mul_comm] using h
  have hNonneg : 0 <= (Inv.inv (norm s)) ^ (3 / 2 : Real) :=
    Real.rpow_nonneg (inv_nonneg.mpr hNormPos.le) _
  change norm ((Inv.inv (norm s)) ^ (3 / 2 : Real)) <= _
  rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
  calc
    (Inv.inv (norm s)) ^ (3 / 2 : Real) <=
        (2 * Inv.inv (1 + norm t)) ^ (3 / 2 : Real) :=
      Real.rpow_le_rpow (inv_nonneg.mpr hNormPos.le) hInv (by norm_num)
    _ = (2 : Real) ^ (3 / 2 : Real) * (1 + norm t) ^ (-(3 / 2 : Real)) := by
      rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr hOnePos.le),
        <- Real.rpow_neg_eq_inv_rpow]

/-- A single inverse-square majorant on the safe line Re(s)=3/2.  Its constant
is used only to justify absolute integration, not in Robin's sharp bound. -/
theorem exists_robinCutoffMellin_safeLine_majorant
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    Exists fun C : Real => And (0 <= C) (forall t : Real,
      norm (mellin (robinCutoffMellinTest n x)
        ((3 / 2 : Complex) + (t : Complex) * Complex.I)) <=
        C * (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) := by
  let A : Real := ((n : Real) / 2) * x ^ ((3 / 2 : Real) - n) * Inv.inv (Real.log x)
  let B : Real := x ^ ((3 / 2 : Real) - n) * Inv.inv ((Real.log x)^2) +
    2 * ((-x ^ ((3 / 2 : Real) - n) / ((3 / 2 : Real) - n)) *
      Inv.inv ((Real.log x)^3))
  refine Exists.intro (10 * abs A + 9 * abs B) (And.intro (by positivity) ?_)
  intro t
  let s : Complex := (3 / 2 : Complex) + (t : Complex) * Complex.I
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hsRe : s.re = (3 / 2 : Real) := by simp [s]
  have hsPos : 0 < s.re := by rw [hsRe]; norm_num
  have hsLt : s.re < (n : Real) := by rw [hsRe]; linarith
  have hsZero : Not (s = 0) := by
    intro h
    rw [h] at hsPos
    norm_num at hsPos
  have hnZero : Not (s - (n : Complex) = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.natCast_re, Complex.zero_re, hsRe] at hRe
    linarith
  have hsNorm : 0 < norm s := norm_pos_iff.mpr hsZero
  have hnNorm : 0 < norm (s - (n : Complex)) := norm_pos_iff.mpr hnZero
  have hSq : norm s ^ (2 : Nat) <= 9 * norm (s - (n : Complex)) ^ (2 : Nat) := by
    have hSqS : norm s ^ (2 : Nat) = (9 / 4 : Real) + t^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [s]
      ring
    have hSqN : norm (s - (n : Complex)) ^ (2 : Nat) =
        ((3 / 2 : Real) - n)^2 + t^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [s]
      ring
    rw [hSqS, hSqN]
    have hProduct : 0 <= ((n : Real) - 1) * ((n : Real) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg t]
  have hInv : (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat) <=
      9 * (Inv.inv (norm s)) ^ (2 : Nat) := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < norm s ^ (2 : Nat) / 9)
      (by linarith : norm s ^ (2 : Nat) / 9 <= norm (s - (n : Complex)) ^ (2 : Nat))
    simpa only [inv_pow, one_div, inv_div, div_eq_mul_inv, mul_inv, inv_inv,
      one_mul, mul_one, mul_comm] using h
  have hRaw : norm (mellin (robinCutoffMellinTest n x) s) <=
      A * ((Inv.inv (norm s)) ^ (2 : Nat) +
        (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat)) +
      B * (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat) := by
    rw [mellin_robinCutoffMellinTest_eq_zeroKernel_div hx hsPos hsLt]
    simpa only [hsRe, A, B] using
      norm_robinZeroKernel_div_le_inverseSquares (by omega : 1 <= n) hsZero hx hsLt
  apply hRaw.trans
  have hAbs := add_le_add
    (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity :
      0 <= (Inv.inv (norm s)) ^ (2 : Nat) +
        (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat)))
    (mul_le_mul_of_nonneg_right (le_abs_self B)
      (sq_nonneg (Inv.inv (norm (s - (n : Complex))))))
  have hTransport := mul_le_mul_of_nonneg_left hInv
    (add_nonneg (abs_nonneg A) (abs_nonneg B))
  change _ <= (10 * abs A + 9 * abs B) * (Inv.inv (norm s)) ^ (2 : Nat)
  nlinarith

theorem norm_paired_hadamard_atom_mul_le
    {C : Real} (hC : 0 <= C) {z rho : Complex} {t : Real}
    (hRho : rho.re = (1 / 2 : Real))
    (hz : norm z <= C *
      (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    norm (z * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho)) <=
      2 * C * (Inv.inv (norm rho)) ^ (3 / 2 : Real) *
        ((Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (3 / 2 : Real) +
         (Inv.inv (norm ((1 : Complex) + ((t - rho.im : Real) : Complex) * Complex.I))) ^
           (3 / 2 : Real)) := by
  let s : Complex := (3 / 2 : Complex) + (t : Complex) * Complex.I
  have hsRe : s.re = (3 / 2 : Real) := by simp [s]
  have hShift : s - rho =
      (1 : Complex) + ((t - rho.im : Real) : Complex) * Complex.I := by
    apply Complex.ext
    . simp [s, hRho]
      ring
    . simp [s]
  have hRhoZero : Not (rho = 0) := by
    intro h
    rw [h] at hRho
    norm_num at hRho
  have hsZero : Not (s = 0) := by
    intro h
    rw [h] at hsRe
    norm_num at hsRe
  have hSubZero : Not (s - rho = 0) := by
    intro h
    have hReal := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, hsRe, hRho] at hReal
    norm_num at hReal
  have hR : 0 < norm rho := norm_pos_iff.mpr hRhoZero
  have ha : 0 < norm s := norm_pos_iff.mpr hsZero
  have hb : 0 < norm (s - rho) := norm_pos_iff.mpr hSubZero
  have hTriangle : norm rho <= norm s + norm (s - rho) := by
    calc
      norm rho = norm (s - (s - rho)) := by congr 1; ring
      _ <= norm s + norm (s - rho) := norm_sub_le _ _
  have hAtom : 1 / (s - rho) + 1 / rho = s / (rho * (s - rho)) := by
    field_simp
    ring
  change norm (z * (1 / (s - rho) + 1 / rho)) <= _
  change norm z <= C * (Inv.inv (norm s)) ^ (2 : Nat) at hz
  rw [norm_mul, hAtom, norm_div, norm_mul]
  calc
    norm z * (norm s / (norm rho * norm (s - rho))) <=
        (C * (Inv.inv (norm s)) ^ (2 : Nat)) *
          (norm s / (norm rho * norm (s - rho))) :=
      mul_le_mul_of_nonneg_right hz (by positivity)
    _ = C * (1 / (norm rho * norm s * norm (s - rho))) := by
      field_simp
    _ <= C * (2 * (Inv.inv (norm rho)) ^ (3 / 2 : Real) *
        ((Inv.inv (norm s)) ^ (3 / 2 : Real) +
          (Inv.inv (norm (s - rho))) ^ (3 / 2 : Real))) :=
      mul_le_mul_of_nonneg_left (inv_triple_product_le_three_halves hR ha hb hTriangle) hC
    _ = _ := by
      rw [hShift]
      ring

theorem integrable_paired_xi_atom
    {H : Real -> Complex} (hH : Integrable H) {rho : Complex}
    (hRho : rho.re = (1 / 2 : Real)) :
    Integrable (fun t : Real => H t *
      (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho)) := by
  have hR : Integrable (fun t : Real =>
      H t / ((3 / 2 : Complex) + (t : Complex) * Complex.I - rho)) := by
    simpa using! integrable_vertical_resolvent hH
      (c := (3 / 2 : Real)) (by rw [hRho]; norm_num)
  apply (hR.add (hH.div_const rho)).congr
  filter_upwards with t
  simp only [Pi.add_apply]
  ring

/-- The complete Hadamard series has summable integrated norms against every
inverse-square safe-line test.  This is the absolute-interchange obligation. -/
theorem summable_integral_norm_paired_xi_atoms
    (hRH : RiemannHypothesis) {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      integral volume (fun t : Real => norm (H t *
        (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)))) := by
  let K : Real -> Real -> Real := fun a t =>
    (Inv.inv (norm ((a : Complex) + (t : Complex) * Complex.I))) ^ (3 / 2 : Real)
  let F : RiemannXiDivisorZeroIndex -> Real -> Complex := fun p t => H t *
    (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
      1 / riemannXiDivisorZeroValue p)
  have hKLeft : Integrable (K (3 / 2)) :=
    integrable_three_halves_verticalLine (by norm_num)
  have hKRight : Integrable (K 1) :=
    integrable_three_halves_verticalLine le_rfl
  have hF : forall p : RiemannXiDivisorZeroIndex, Integrable (F p) := by
    intro p
    exact integrable_paired_xi_atom hH
      (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p)
  have hMajorIntegral : forall p : RiemannXiDivisorZeroIndex,
      integral volume (fun t : Real => norm (F p t)) <=
        (2 * C * (integral volume (K (3 / 2)) + integral volume (K 1))) *
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (3 / 2 : Real) := by
    intro p
    let rho : Complex := riemannXiDivisorZeroValue p
    let W : Real := (Inv.inv (norm rho)) ^ (3 / 2 : Real)
    have hShiftInt : Integrable (fun t : Real => K 1 (t - rho.im)) :=
      hKRight.comp_sub_right rho.im
    have hMajorInt : Integrable (fun t : Real =>
        2 * C * W * (K (3 / 2) t + K 1 (t - rho.im))) :=
      (hKLeft.add hShiftInt).const_mul _
    calc
      integral volume (fun t : Real => norm (F p t)) <=
          integral volume (fun t : Real =>
            2 * C * W * (K (3 / 2) t + K 1 (t - rho.im))) := by
        apply integral_mono_ae (hF p).norm hMajorInt
        filter_upwards with t
        simpa [F, K, W, rho] using norm_paired_hadamard_atom_mul_le hC
          (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p) (hBound t)
      _ = _ := by
        rw [integral_const_mul, integral_add hKLeft hShiftInt,
          integral_sub_right_eq_self]
        dsimp [W, rho]
        ring
  have hSum : Summable (fun p : RiemannXiDivisorZeroIndex =>
      (2 * C * (integral volume (K (3 / 2)) + integral volume (K 1))) *
        (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (3 / 2 : Real)) :=
    (summable_riemannXiDivisorZero_norm_inv_rpow (by norm_num : (1 : Real) < 3 / 2)).mul_left _
  exact Summable.of_nonneg_of_le
    (fun p => integral_nonneg (fun t => norm_nonneg (F p t))) hMajorIntegral hSum

/-- Fubini for the whole multiplicity-counted xi series, with absolute
integrated norms proved above. -/
theorem integral_tsum_paired_xi_atoms
    (hRH : RiemannHypothesis) {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    tsum (fun p : RiemannXiDivisorZeroIndex => integral volume (fun t : Real =>
        H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))) =
      integral volume (fun t : Real => tsum (fun p : RiemannXiDivisorZeroIndex =>
        H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))) := by
  have hSupport : Function.support (fun p : RiemannXiDivisorZeroIndex =>
      (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) = Set.univ := by
    ext p
    simp only [Function.mem_support, mem_univ, iff_true]
    exact pow_ne_zero _ (inv_ne_zero (norm_ne_zero_iff.mpr
      (riemannXiDivisorZeroValue_ne_zero p)))
  have hCount := summable_riemannXiDivisorZero_norm_inv_sq.countable_support
  rw [hSupport] at hCount
  letI : Countable RiemannXiDivisorZeroIndex := Set.countable_univ_iff.mp hCount
  exact integral_tsum_of_summable_integral_norm
    (fun p => integrable_paired_xi_atom hH
      (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p))
    (summable_integral_norm_paired_xi_atoms hRH hH hC hBound)

/-- The integrated complete zero contribution is exactly Robin's absolutely
convergent kernel sum. -/
theorem robinCutoffMellin_complete_zero_pairing
    (hRH : RiemannHypothesis) {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (robinCutoffMellinTest n x) ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
            tsum (fun p : RiemannXiDivisorZeroIndex =>
              1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
                1 / riemannXiDivisorZeroValue p)) =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) := by
  choose C hC hBound using exists_robinCutoffMellin_safeLine_majorant hn hx
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcLt : (3 / 2 : Real) < n := by linarith
  let H : Real -> Complex := fun t =>
    mellin (robinCutoffMellinTest n x) ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using! verticalIntegrable_mellin_robinCutoffMellinTest hnOne hx
      (by norm_num : (0 : Real) < 3 / 2) hcLt
  have hSwap := integral_tsum_paired_xi_atoms hRH hH hC hBound
  have hIntegral : integral volume (fun t : Real => H t *
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) =
      tsum (fun p : RiemannXiDivisorZeroIndex => integral volume (fun t : Real =>
        H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))) := by
    rw [hSwap]
    apply integral_congr_ae
    filter_upwards with t
    rw [tsum_mul_left]
  change (((1 / (2 * Real.pi) : Real) : Complex)) *
    integral volume (fun t : Real => H t *
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) = _
  rw [hIntegral, <- tsum_mul_left]
  apply tsum_congr
  intro p
  have hRe := riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
  simpa [H] using! robinCutoffMellin_paired_zero_atom hnOne hx
    (by norm_num : (0 : Real) < 3 / 2) hcLt (riemannXiDivisorZeroValue_ne_zero p)
    (by rw [hRe]; norm_num : (riemannXiDivisorZeroValue p).re < (3 / 2 : Real))

end

end Robin1984
