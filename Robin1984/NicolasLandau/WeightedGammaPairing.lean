import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Robin1984.NicolasLandau.WeightedZeroInterchange

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin (1984), especially the weighted explicit formula and Lemmas 1 and 2.
- Formalization note: The mathematical identity or bound is source-based; the multiplicity-aware indexing, interchange proofs, and Lean decomposition are formalization work.
- PROVENANCE-END
-/

/-!
# The archimedean contribution in Robin's weighted formula

The digamma series is paired with the same cutoff test used for the xi zeros.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set

theorem half_digamma_eq_trivial_zero_series
    {s : Complex} (hs : 1 < s.re) :
    (1 / 2 : Complex) * Complex.digamma (s / 2 + 1) =
      -(Real.eulerMascheroniConstant : Complex) / 2 +
        tsum (fun k : Nat =>
          1 / (2 * ((k : Complex) + 1)) - 1 / (s + 2 * ((k : Complex) + 1))) := by
  have hPole : forall k : Nat, Not (s / 2 + 1 = -(k : Complex)) := by
    intro k h
    have hRe := congrArg Complex.re h
    simp at hRe
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  rw [Complex.digamma_eq_tsum hPole, mul_add]
  have hConstant : (1 / 2 : Complex) * -(Real.eulerMascheroniConstant : Complex) =
      -(Real.eulerMascheroniConstant : Complex) / 2 := by ring
  rw [hConstant, <- tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  have hk : Not ((k : Complex) + 1 = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hRe
    have hkNonneg : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hDen : Not (s + 2 * ((k : Complex) + 1) = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    have hkNonneg : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  rw [show (k : Complex) + (s / 2 + 1) =
    (s + 2 * ((k : Complex) + 1)) / 2 by ring]
  field_simp [hk, hDen]

/-- Absolute resolvent majorant before restricting the pole to a vertical
line or to the negative even integers. -/
theorem norm_regularized_resolvent_mul_le
    {s rho z : Complex} (hs : Not (s = 0)) (hRho : Not (rho = 0))
    (hSub : Not (s - rho = 0)) {C : Real} (hC : 0 <= C)
    (hz : norm z <= C * (Inv.inv (norm s)) ^ (2 : Nat)) :
    norm (z * (1 / (s - rho) + 1 / rho)) <=
      2 * C * (Inv.inv (norm rho)) ^ (3 / 2 : Real) *
        ((Inv.inv (norm s)) ^ (3 / 2 : Real) +
          (Inv.inv (norm (s - rho))) ^ (3 / 2 : Real)) := by
  have hR : 0 < norm rho := norm_pos_iff.mpr hRho
  have ha : 0 < norm s := norm_pos_iff.mpr hs
  have hb : 0 < norm (s - rho) := norm_pos_iff.mpr hSub
  have hTriangle : norm rho <= norm s + norm (s - rho) := by
    calc
      norm rho = norm (s - (s - rho)) := by congr 1; ring
      _ <= norm s + norm (s - rho) := norm_sub_le _ _
  have hAtom : 1 / (s - rho) + 1 / rho = s / (rho * (s - rho)) := by
    field_simp [hRho, hSub] <;> ring
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
    _ = _ := by ring

/-- The gamma atoms have a summable uniform majorant; the constant is used
only for exchanging the integral and the series. -/
theorem norm_gamma_atom_mul_le
    {C : Real} (hC : 0 <= C) {z : Complex} {t : Real} (k : Nat)
    (hz : norm z <= C *
      (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    norm (z * (1 / (2 * ((k : Complex) + 1)) -
      1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1)))) <=
      4 * C * (Inv.inv ((k : Real) + 1)) ^ (3 / 2 : Real) *
        (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (3 / 2 : Real) := by
  let s : Complex := (3 / 2 : Complex) + (t : Complex) * Complex.I
  let u : Real := 2 * ((k : Real) + 1)
  let rho : Complex := -(u : Complex)
  have hk : 0 < (k : Real) + 1 := by positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have huCast : (u : Complex) = 2 * ((k : Complex) + 1) := by
    dsimp [u]
    push_cast
    ring
  have hsRe : s.re = (3 / 2 : Real) := by simp [s]
  have hRhoRe : rho.re = -u := by simp [rho]
  have hsZero : Not (s = 0) := by
    intro h
    rw [h] at hsRe
    norm_num at hsRe
  have hRhoZero : Not (rho = 0) := by
    intro h
    rw [h] at hRhoRe
    simp at hRhoRe
    linarith
  have hSubZero : Not (s - rho = 0) := by
    intro h
    have hReal := congrArg Complex.re h
    simp only [Complex.sub_re, hsRe, hRhoRe, Complex.zero_re] at hReal
    linarith
  have hsNorm : 0 < norm s := norm_pos_iff.mpr hsZero
  have hRhoNorm : norm rho = u := by
    simp [rho, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have hNormLe : norm s <= norm (s - rho) := by
    have hSquare : norm s ^ (2 : Nat) <= norm (s - rho) ^ (2 : Nat) := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, hsRe, hRhoRe]
      have hRhoIm : rho.im = 0 := by simp [rho]
      rw [hRhoIm]
      nlinarith
    nlinarith [norm_nonneg s, norm_nonneg (s - rho)]
  have hInvB : Inv.inv (norm (s - rho)) <= Inv.inv (norm s) := by
    simpa only [one_div] using one_div_le_one_div_of_le hsNorm hNormLe
  have hWeightB : (Inv.inv (norm (s - rho))) ^ (3 / 2 : Real) <=
      (Inv.inv (norm s)) ^ (3 / 2 : Real) :=
    Real.rpow_le_rpow (by positivity) hInvB (by norm_num)
  have hInvU : Inv.inv u <= Inv.inv ((k : Real) + 1) := by
    have hku : (k : Real) + 1 <= u := by dsimp [u]; linarith
    simpa only [one_div] using one_div_le_one_div_of_le hk hku
  have hWeightU : (Inv.inv u) ^ (3 / 2 : Real) <=
      (Inv.inv ((k : Real) + 1)) ^ (3 / 2 : Real) :=
    Real.rpow_le_rpow (by positivity) hInvU (by norm_num)
  have hAtom : z * (1 / (u : Complex) - 1 / (s + (u : Complex))) =
      -(z * (1 / (s - rho) + 1 / rho)) := by
    dsimp [rho]
    simp only [sub_neg_eq_add, div_neg]
    ring
  rw [<- huCast]
  change norm (z * (1 / (u : Complex) - 1 / (s + (u : Complex)))) <= _
  rw [hAtom, norm_neg]
  have hGeneric := norm_regularized_resolvent_mul_le hsZero hRhoZero hSubZero hC hz
  rw [hRhoNorm] at hGeneric
  apply hGeneric.trans
  calc
    2 * C * (Inv.inv u) ^ (3 / 2 : Real) *
        ((Inv.inv (norm s)) ^ (3 / 2 : Real) +
          (Inv.inv (norm (s - rho))) ^ (3 / 2 : Real)) <=
      2 * C * (Inv.inv ((k : Real) + 1)) ^ (3 / 2 : Real) *
        ((Inv.inv (norm s)) ^ (3 / 2 : Real) +
          (Inv.inv (norm s)) ^ (3 / 2 : Real)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hWeightU (by positivity))
        (add_le_add le_rfl hWeightB) (by positivity) (by positivity)
    _ = _ := by ring

theorem integrable_gamma_atom
    {H : Real -> Complex} (hH : Integrable H) (k : Nat) :
    Integrable (fun t : Real => H t *
      (1 / (2 * ((k : Complex) + 1)) -
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1)))) := by
  have hRho : (-(2 * ((k : Complex) + 1))).re < (3 / 2 : Real) := by
    simp
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hR : Integrable (fun t : Real =>
      H t / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1))) := by
    simpa using! integrable_vertical_resolvent hH (c := (3 / 2 : Real)) hRho
  apply ((hH.div_const (2 * ((k : Complex) + 1))).sub hR).congr
  filter_upwards with t
  simp only [Pi.sub_apply]
  ring

theorem summable_integral_norm_gamma_atoms
    {H : Real -> Complex} (hH : Integrable H) {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    Summable (fun k : Nat => integral volume (fun t : Real => norm (H t *
      (1 / (2 * ((k : Complex) + 1)) -
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1)))))) := by
  let K : Real -> Real := fun t =>
    (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (3 / 2 : Real)
  let W : Nat -> Real := fun k => (Inv.inv ((k : Real) + 1)) ^ (3 / 2 : Real)
  let F : Nat -> Real -> Complex := fun k t => H t *
    (1 / (2 * ((k : Complex) + 1)) -
      1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1)))
  have hK : Integrable K := by
    simpa [K] using! integrable_three_halves_verticalLine (by norm_num : (1 : Real) <= 3 / 2)
  have hW : Summable W := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).mpr (by norm_num)
    apply h.congr
    intro k
    dsimp [W]
    rw [abs_of_pos (by positivity : (0 : Real) < k + 1), one_div,
      Real.inv_rpow (by positivity)]
  have hMajor : forall k : Nat, integral volume (fun t : Real => norm (F k t)) <=
      (4 * C * integral volume K) * W k := by
    intro k
    have hF : Integrable (F k) := integrable_gamma_atom hH k
    have hM : Integrable (fun t : Real => 4 * C * W k * K t) := hK.const_mul _
    calc
      integral volume (fun t : Real => norm (F k t)) <=
          integral volume (fun t : Real => 4 * C * W k * K t) := by
        apply integral_mono_ae hF.norm hM
        filter_upwards with t
        exact norm_gamma_atom_mul_le hC k (hBound t)
      _ = _ := by rw [integral_const_mul]; ring
  exact Summable.of_nonneg_of_le
    (fun k => integral_nonneg (fun t => norm_nonneg (F k t))) hMajor (hW.mul_left _)

theorem integral_tsum_gamma_atoms
    {H : Real -> Complex} (hH : Integrable H) {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    tsum (fun k : Nat => integral volume (fun t : Real => H t *
        (1 / (2 * ((k : Complex) + 1)) -
          1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1))))) =
      integral volume (fun t : Real => tsum (fun k : Nat => H t *
        (1 / (2 * ((k : Complex) + 1)) -
          1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1))))) :=
  integral_tsum_of_summable_integral_norm (integrable_gamma_atom hH)
    (summable_integral_norm_gamma_atoms hH hC hBound)

/-- Summable integrated norms also establish integrability of the sum itself,
which is needed when splitting the complete zeta identity into its terms. -/
theorem integrable_complex_series_of_integral_norm
    {Iota : Type*} [Countable Iota] {mu : Measure Real} {F : Iota -> Real -> Complex}
    (hF : forall i : Iota, Integrable (F i) mu)
    (hSum : Summable (fun i : Iota => integral mu (fun t : Real => norm (F i t)))) :
    Integrable (fun t : Real => tsum (fun i : Iota => F i t)) mu := by
  have hMeas : AEStronglyMeasurable (fun t : Real => tsum (fun i : Iota => F i t)) mu :=
    (AEMeasurable.tsum (fun i => (hF i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  refine And.intro hMeas ?_
  rw [hasFiniteIntegral_iff_enorm]
  calc
    lintegral mu (fun t : Real => enorm (tsum (fun i : Iota => F i t))) <=
        lintegral mu (fun t : Real => tsum (fun i : Iota => enorm (F i t))) :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = tsum (fun i : Iota => lintegral mu (fun t : Real => enorm (F i t))) :=
      lintegral_tsum (fun i => (hF i).aestronglyMeasurable.enorm)
    _ = tsum (fun i : Iota => ENNReal.ofReal (integral mu (fun t : Real => norm (F i t)))) := by
      apply tsum_congr
      intro i
      exact (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
    _ < Top.top := hSum.tsum_ofReal_lt_top

theorem robinCutoffMellin_gamma_atom_pairing
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    {c : Real} (hcPos : 0 < c) (hcLt : c < n) (k : Nat) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (robinCutoffMellinTest n x) ((c : Complex) + (t : Complex) * Complex.I) *
            (1 / (2 * ((k : Complex) + 1)) -
              1 / ((c : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1)))) =
      robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1)) := by
  let rho : Complex := -(2 * ((k : Complex) + 1))
  have hRhoZero : Not (rho = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp [rho] at hRe
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hRho : rho.re < c := by
    simp [rho]
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hPair := robinCutoffMellin_paired_zero_atom hn hx hcPos hcLt hRhoZero hRho
  have hFunction : (fun t : Real =>
      mellin (robinCutoffMellinTest n x) ((c : Complex) + (t : Complex) * Complex.I) *
        (1 / (2 * ((k : Complex) + 1)) -
          1 / ((c : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1)))) =
      (fun t : Real => -(mellin (robinCutoffMellinTest n x)
        ((c : Complex) + (t : Complex) * Complex.I) *
          (1 / ((c : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho))) := by
    funext t
    dsimp [rho]
    simp only [sub_neg_eq_add, div_neg]
    ring
  rw [hFunction, integral_neg, mul_neg, hPair]
  simp only [rho, div_neg, neg_neg]

theorem integrable_shifted_gamma_test
    {H : Real -> Complex} (hH : Integrable H) {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    Integrable (fun t : Real => H t *
      ((1 / 2 : Complex) * Complex.digamma
        (((3 / 2 : Complex) + (t : Complex) * Complex.I) / 2 + 1) +
          (Real.eulerMascheroniConstant : Complex) / 2)) := by
  have hInt := integrable_complex_series_of_integral_norm
    (integrable_gamma_atom hH) (summable_integral_norm_gamma_atoms hH hC hBound)
  apply hInt.congr
  filter_upwards with t
  rw [tsum_mul_left, half_digamma_eq_trivial_zero_series (by simp; norm_num)]
  ring

/-- Evaluation of the complete archimedean series against the cutoff test.
The Euler constant is retained explicitly until the pole and xi constants
are combined in the complete weighted formula. -/
theorem robinCutoffMellin_complete_gamma_pairing
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (robinCutoffMellinTest n x) ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
            ((1 / 2 : Complex) * Complex.digamma
              (((3 / 2 : Complex) + (t : Complex) * Complex.I) / 2 + 1) +
                (Real.eulerMascheroniConstant : Complex) / 2)) =
      tsum (fun k : Nat =>
        robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1))) := by
  choose C hC hBound using exists_robinCutoffMellin_safeLine_majorant hn hx
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcLt : (3 / 2 : Real) < n := by linarith
  let H : Real -> Complex := fun t =>
    mellin (robinCutoffMellinTest n x) ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using! verticalIntegrable_mellin_robinCutoffMellinTest
      hnOne hx (by norm_num : (0 : Real) < 3 / 2) hcLt
  have hSwap := integral_tsum_gamma_atoms hH hC hBound
  have hIntegral : integral volume (fun t : Real => H t *
      ((1 / 2 : Complex) * Complex.digamma
        (((3 / 2 : Complex) + (t : Complex) * Complex.I) / 2 + 1) +
          (Real.eulerMascheroniConstant : Complex) / 2)) =
      tsum (fun k : Nat => integral volume (fun t : Real => H t *
        (1 / (2 * ((k : Complex) + 1)) -
          1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1))))) := by
    rw [hSwap]
    apply integral_congr_ae
    filter_upwards with t
    rw [tsum_mul_left, half_digamma_eq_trivial_zero_series (by simp; norm_num)]
    ring
  change (((1 / (2 * Real.pi) : Real) : Complex)) *
    integral volume (fun t : Real => H t *
      ((1 / 2 : Complex) * Complex.digamma
        (((3 / 2 : Complex) + (t : Complex) * Complex.I) / 2 + 1) +
          (Real.eulerMascheroniConstant : Complex) / 2)) = _
  rw [hIntegral, <- tsum_mul_left]
  apply tsum_congr
  intro k
  simpa [H] using! robinCutoffMellin_gamma_atom_pairing hnOne hx
    (by norm_num : (0 : Real) < 3 / 2) hcLt k

end

end Robin1984
