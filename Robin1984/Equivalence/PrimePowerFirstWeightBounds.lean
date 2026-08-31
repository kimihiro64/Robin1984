import Robin1984.Equivalence.WeightedKernelBounds
import Robin1984.NicolasLandau.WeightedPrimePowerTail
import Robin1984.NicolasLandau.ZeroConstantBound
/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann (1984).
- Formalization note: The retained statement or source-level argument is Robin's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Scalar estimates for the complete first-weight prime-power tail

The real-power zero-kernel bounds control the root-scale error contributed by
all higher prime powers at the first Robin weight. Explicit comparisons valid
from `x >= 20000` reduce the complete tail to a normalized scalar coefficient,
which is then used in the large-height proof.
-/

namespace Robin1984

noncomputable section

theorem robinZeroKernel_third_one_lower {x : Real} (hx : 1 < x) :
    (3 / 2 : Real) * x^(-(2 / 3 : Real)) * Inv.inv (Real.log x) -
      (3 / 4 : Real) * x^(-(2 / 3 : Real)) * Inv.inv ((Real.log x)^2) <=
        (robinZeroKernel 1 (1 / 3 : Complex) x).re := by
  have hF := robinZeroKernel_ofReal_eq_main_add_signed_tail 1
    (r := (1 / 3 : Real)) (by norm_num) hx
  have hBound := robinCpowLogTail_ofReal_re_le (a := -(2 / 3 : Real)) (by norm_num) 2 hx
  norm_num at hF hBound
  linarith

theorem robinZeroKernel_fifth_one_upper {x : Real} (hx : 1 < x) :
    (robinZeroKernel 1 (1 / 5 : Complex) x).re <=
      (5 / 4 : Real) * x^(-(4 / 5 : Real)) * Inv.inv (Real.log x) := by
  have hF := robinZeroKernel_ofReal_eq_main_add_signed_tail 1
    (r := (1 / 5 : Real)) (by norm_num) hx
  have hNonneg := robinCpowLogTail_ofReal_re_nonneg (-(4 / 5 : Real)) 2 hx
  norm_num at hF hNonneg
  linarith

/-- Normalize every root error in the same original-x units before estimating. -/
theorem robin_root_error_scalar_eq
    {n k : Nat} (hn : 1 <= n) (hk : 2 <= k) {x : Real} (hx : 1 < x) :
    Inv.inv (k : Real) * robinPsiWeightedErrorScalar (k * n) (x^(Inv.inv (k : Real))) =
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        x^((1 / 2 : Real) * Inv.inv (k : Real) - n) * Inv.inv (Real.log x) *
          (((k * n : Nat) : Real) + (k : Real) * Inv.inv (Real.log x) +
            4 * (k : Real)^2 * Inv.inv (((2 * (k * n) - 1 : Nat) : Real) * (Real.log x)^2)) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hkn : 1 <= k * n := by nlinarith
  have hOddNat : 0 < 2 * (k * n) - 1 := by omega
  have hOdd : Not (((2 * (k * n) - 1 : Nat) : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hOddNat)
  have hExp : Inv.inv (k : Real) * ((1 / 2 : Real) - ((k * n : Nat) : Real)) =
      (1 / 2 : Real) * Inv.inv (k : Real) - n := by
    rw [Nat.cast_mul]
    field_simp [hkPos.ne'] <;> ring
  unfold robinPsiWeightedErrorScalar
  rw [<- Real.rpow_mul hxPos.le, Real.log_rpow hxPos, hExp]
  field_simp [hkPos.ne', (Real.log_pos hx).ne', hOdd] <;> ring

theorem robin_log_ge_nine {x : Real} (hx : 20000 <= x) :
    9 <= Real.log x := by
  have h : Real.log ((2 : Real)^14) <= Real.log x :=
    Real.log_le_log (by positivity) (by norm_num; linarith)
  rw [Real.log_pow] at h
  have hTwo := robin_log_two_lower
  norm_num at h
  linarith

/-- Exact rational-power certification, before any rounded coefficient is used. -/
theorem robin_rpow_neg_div_le_of_pow
    {x b : Real} {a d : Nat} (hx : 0 < x) (hb : 0 <= b) (hd : 0 < d)
    (h : 1 <= b^d * x^a) : x^(-((a : Real) / (d : Real))) <= b := by
  have hdPos : (0 : Real) < d := by exact_mod_cast hd
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hx.le _) hb hdPos).mp
  rw [<- Real.rpow_mul hx.le]
  have hExp : (-((a : Real) / (d : Real))) * (d : Real) = -(a : Real) := by
    field_simp
  rw [hExp, Real.rpow_neg hx.le, Real.rpow_natCast, Real.rpow_natCast]
  have hPos := pow_pos hx a
  have hCancel : Inv.inv (x^a) * x^a = 1 := by field_simp
  nlinarith

theorem robin_root_power_ratios {x : Real} (hx : 20000 <= x) :
    And (x^(-(2 / 15 : Real)) <= 27 / 100)
      (And (x^(-(1 / 12 : Real)) <= 11 / 25)
        (And (x^(-(1 / 6 : Real)) <= 1 / 5)
          (x^(-(7 / 30 : Real)) <= 1 / 10))) := by
  have hxPos : 0 < x := by linarith
  have hTwo : x^(-(2 / 15 : Real)) <= 27 / 100 := by
    apply robin_rpow_neg_div_le_of_pow (a := 2) (d := 15) hxPos (by norm_num) (by omega)
    have hPow : (20000 : Real)^2 <= x^2 := by gcongr
    norm_num at hPow
    norm_num
    nlinarith
  have hTwelve : x^(-(1 / 12 : Real)) <= 11 / 25 := by
    have h := robin_rpow_neg_div_le_of_pow (a := 1) (d := 12) (b := (11 / 25 : Real))
      hxPos (by norm_num) (by omega) (by norm_num; linarith)
    norm_num at h
    exact h
  have hSix : x^(-(1 / 6 : Real)) <= 1 / 5 := by
    have h := robin_rpow_neg_div_le_of_pow (a := 1) (d := 6) (b := (1 / 5 : Real))
      hxPos (by norm_num) (by omega) (by norm_num; linarith)
    norm_num at h
    exact h
  have hThirty : x^(-(7 / 30 : Real)) <= 1 / 10 := by
    apply robin_rpow_neg_div_le_of_pow (a := 7) (d := 30) hxPos (by norm_num) (by omega)
    have hPow : (20000 : Real)^7 <= x^7 := by gcongr
    norm_num at hPow
    norm_num
    linarith
  exact And.intro hTwo (And.intro hTwelve (And.intro hSix hThirty))

theorem robin_root_error_one_upper
    {k : Nat} (hk : 2 <= k) {x : Real} (hx : 20000 <= x) :
    Inv.inv (k : Real) * robinPsiWeightedErrorScalar k (x^(Inv.inv (k : Real))) <=
      (1 / 20 : Real) * x^((1 / 2 : Real) * Inv.inv (k : Real) - 1) *
        Inv.inv (Real.log x) *
          ((k : Real) + (k : Real) / 9 + 4 * (k : Real)^2 /
            (((2 * k - 1 : Nat) : Real) * 81)) := by
  have hxOne : 1 < x := by linarith
  have hLog := robin_log_ge_nine hx
  have hLogPos := Real.log_pos hxOne
  have hq : Inv.inv (Real.log x) <= (1 / 9 : Real) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 9) hLog
  have hqNonneg : 0 <= Inv.inv (Real.log x) := inv_nonneg.mpr hLogPos.le
  have hOddNat : 0 < 2 * k - 1 := by omega
  have hOdd : (0 : Real) < ((2 * k - 1 : Nat) : Real) := by exact_mod_cast hOddNat
  have hBracket : (k : Real) + (k : Real) * Inv.inv (Real.log x) +
      4 * (k : Real)^2 * Inv.inv (((2 * k - 1 : Nat) : Real) * (Real.log x)^2) <=
      (k : Real) + (k : Real) / 9 + 4 * (k : Real)^2 /
        (((2 * k - 1 : Nat) : Real) * 81) := by
    rw [mul_inv, <- inv_pow]
    have hqSq : (Inv.inv (Real.log x))^2 <= (1 / 9 : Real)^2 := by gcongr
    calc
      _ <= (k : Real) + (k : Real) * (1 / 9 : Real) +
          4 * (k : Real)^2 * (Inv.inv (((2 * k - 1 : Nat) : Real)) * (1 / 9 : Real)^2) := by
        gcongr
      _ = _ := by field_simp; ring
  have hBracketNonneg : 0 <= (k : Real) + (k : Real) * Inv.inv (Real.log x) +
      4 * (k : Real)^2 * Inv.inv (((2 * k - 1 : Nat) : Real) * (Real.log x)^2) := by positivity
  have hEq := robin_root_error_scalar_eq (n := 1) (by omega) hk hxOne
  simp only [Nat.mul_one, Nat.cast_one] at hEq
  rw [hEq]
  calc
    _ <= (1 / 20 : Real) * x^((1 / 2 : Real) * Inv.inv (k : Real) - 1) *
        Inv.inv (Real.log x) *
        ((k : Real) + (k : Real) * Inv.inv (Real.log x) +
          4 * (k : Real)^2 * Inv.inv (((2 * k - 1 : Nat) : Real) * (Real.log x)^2)) := by
      gcongr
      exact robin_zero_constant_le_one_twentieth
    _ <= _ := by gcongr

theorem robin_scaled_rpow_log_le
    {x r s a b : Real} (hx : 1 < x) (ha : 0 <= a) (h : x^s <= b) :
    a * x^(r + s) * Inv.inv (Real.log x) <=
      a * b * (x^r * Inv.inv (Real.log x)) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogPos := Real.log_pos hx
  have hScale : 0 <= x^r * Inv.inv (Real.log x) := by positivity
  rw [Real.rpow_add hxPos]
  calc
    _ = a * x^s * (x^r * Inv.inv (Real.log x)) := by ring
    _ <= _ := by gcongr

theorem robin_root_error_one_normalized
    {k : Nat} (hk : 2 <= k) {x b : Real} (hx : 20000 <= x)
    (hPower : x^((1 / 2 : Real) * Inv.inv (k : Real) - 1 / 3) <= b) :
    Inv.inv (k : Real) * robinPsiWeightedErrorScalar k (x^(Inv.inv (k : Real))) <=
      ((1 / 20 : Real) *
        ((k : Real) + (k : Real) / 9 + 4 * (k : Real)^2 /
          (((2 * k - 1 : Nat) : Real) * 81)) * b) *
            (x^(-(2 / 3 : Real)) * Inv.inv (Real.log x)) := by
  have hxOne : 1 < x := by linarith
  have hOddNat : 0 < 2 * k - 1 := by omega
  have hOdd : (0 : Real) < ((2 * k - 1 : Nat) : Real) := by exact_mod_cast hOddNat
  have hCoef : 0 <= (1 / 20 : Real) *
      ((k : Real) + (k : Real) / 9 + 4 * (k : Real)^2 /
        (((2 * k - 1 : Nat) : Real) * 81)) := by positivity
  have h := robin_scaled_rpow_log_le (r := -(2 / 3 : Real)) hxOne hCoef hPower
  have hExp : -(2 / 3 : Real) + ((1 / 2 : Real) * Inv.inv (k : Real) - 1 / 3) =
      (1 / 2 : Real) * Inv.inv (k : Real) - 1 := by ring
  rw [hExp] at h
  have hUpper := robin_root_error_one_upper hk hx
  nlinarith

/-- The complete prime-power upper tail used by Robin's Mertens estimate.
All three root errors are bounded before their common scale is compared. -/
theorem robinPrimePowerWeightedTail_one_upper
    (hRH : RiemannHypothesis) {x : Real} (hx : 20000 <= x) :
    robinPrimePowerWeightedTail 1 x <=
      (robinZeroKernel 1 (1 / 2 : Complex) x).re +
        (4 / 3 : Real) * (robinZeroKernel 1 (1 / 3 : Complex) x).re := by
  have hxOne : 1 < x := by linarith
  have hLogPos := Real.log_pos hxOne
  have hScale : 0 <= x^(-(2 / 3 : Real)) * Inv.inv (Real.log x) := by positivity
  have hRatios := robin_root_power_ratios hx
  have hTwo := robin_root_error_one_normalized (k := 2) (by omega) hx
    (b := (11 / 25 : Real)) (by norm_num; exact hRatios.2.1)
  have hThree := robin_root_error_one_normalized (k := 3) (by omega) hx
    (b := (1 / 5 : Real)) (by norm_num; exact hRatios.2.2.1)
  have hFive := robin_root_error_one_normalized (k := 5) (by omega) hx
    (b := (1 / 10 : Real)) (by norm_num; exact hRatios.2.2.2)
  norm_num at hTwo hThree hFive
  have hTwoBound : (1 / 2 : Real) * robinPsiWeightedErrorScalar 2 (x^(1 / 2 : Real)) <=
      (51 / 1000 : Real) * (x^(-(2 / 3 : Real)) * Inv.inv (Real.log x)) := by nlinarith
  have hThreeBound : (1 / 3 : Real) * robinPsiWeightedErrorScalar 3 (x^(1 / 3 : Real)) <=
      (35 / 1000 : Real) * (x^(-(2 / 3 : Real)) * Inv.inv (Real.log x)) := by nlinarith
  have hFiveBound : (1 / 5 : Real) * robinPsiWeightedErrorScalar 5 (x^(1 / 5 : Real)) <=
      (29 / 1000 : Real) * (x^(-(2 / 3 : Real)) * Inv.inv (Real.log x)) := by nlinarith
  have hFifthPower := robin_scaled_rpow_log_le (r := -(2 / 3 : Real)) hxOne
    (by norm_num : (0 : Real) <= 5 / 4) hRatios.1
  norm_num at hFifthPower
  have hFifth := robinZeroKernel_fifth_one_upper hxOne
  have hFifthBound : (robinZeroKernel 1 (1 / 5 : Complex) x).re <=
      (27 / 80 : Real) * (x^(-(2 / 3 : Real)) * Inv.inv (Real.log x)) := by nlinarith
  have hq : Inv.inv (Real.log x) <= (1 / 9 : Real) := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : Real) < 9) (robin_log_ge_nine hx)
  have hCorrection : (3 / 4 : Real) * x^(-(2 / 3 : Real)) * Inv.inv ((Real.log x)^2) <=
      (1 / 12 : Real) * (x^(-(2 / 3 : Real)) * Inv.inv (Real.log x)) := by
    rw [<- inv_pow]
    have h := mul_le_mul_of_nonneg_right hq hScale
    nlinarith
  have hThirdLower := robinZeroKernel_third_one_lower hxOne
  have hThirdBound : (17 / 12 : Real) * (x^(-(2 / 3 : Real)) * Inv.inv (Real.log x)) <=
      (robinZeroKernel 1 (1 / 3 : Complex) x).re := by nlinarith
  have hRoot := (robinPrimePowerWeightedTail_root_bounds hRH (n := 1) (by omega)
    (by linarith : 128 <= x)).2
  unfold robinRootPsiTailUpper at hRoot
  norm_num at hRoot
  linarith

end

end Robin1984
