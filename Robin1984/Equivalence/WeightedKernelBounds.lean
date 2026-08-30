import Robin1984.NicolasLandau.RobinWeightedIntegral

/-!
## Provenance

- Classification: **Direct source formalization**.
- Mathematical source: Guy Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann (1984).
- Formalization note: The retained statement or source-level argument is Robin's; the Lean encoding, exact constants, and proof decomposition are the formalization authors' work.
- PROVENANCE-END
-/

/-!
# Real-power kernel estimates used in Robin 1984 Section 3

The complex logarithmic tail is specialized to nonnegative real exponents and
related by a recurrence to Robin's zero kernel. Explicit upper and lower
bounds at exponents `1 / 2` and `1 / 3`, for weights one and two, supply the
kernel estimates used in the prime-power error analysis.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

theorem robinCpowLogTail_ofReal_eq
    (a : Real) (k : Nat) {x : Real} (hx : 1 < x) :
    robinCpowLogTail (a : Complex) k x =
      ((integral (volume.restrict (Ioi x)) (fun t : Real =>
        t^(a - 1) * Inv.inv ((Real.log t)^k)) : Real) : Complex) := by
  unfold robinCpowLogTail
  rw [<- integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have htPos : 0 < t := lt_trans Real.zero_lt_one (lt_trans hx ht)
  rw [Complex.ofReal_mul, Complex.ofReal_cpow htPos.le]
  push_cast
  rfl

theorem robinCpowLogTail_ofReal_re_nonneg
    (a : Real) (k : Nat) {x : Real} (hx : 1 < x) :
    0 <= (robinCpowLogTail (a : Complex) k x).re := by
  rw [robinCpowLogTail_ofReal_eq a k hx, Complex.ofReal_re]
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have htOne : 1 < t := lt_trans hx ht
  have htPos : 0 < t := lt_trans Real.zero_lt_one htOne
  exact mul_nonneg (Real.rpow_nonneg htPos.le _)
    (inv_nonneg.mpr (pow_nonneg (Real.log_pos htOne).le k))

theorem robinCpowLogTail_ofReal_re_le
    {a : Real} (ha : a < 0) (k : Nat) {x : Real} (hx : 1 < x) :
    (robinCpowLogTail (a : Complex) k x).re <=
      (-x^a / a) * Inv.inv ((Real.log x)^k) := by
  exact (Complex.re_le_norm _).trans
    (norm_robinCpowLogTail_le hx (show (a : Complex).re < 0 from ha) k)

theorem robinCpowLogTail_ofReal_recurrence
    {a : Real} (ha : a < 0) (k : Nat) {x : Real} (hx : 1 < x) :
    (robinCpowLogTail (a : Complex) k x).re =
      -Inv.inv a * x^a * Inv.inv ((Real.log x)^k) +
        ((k : Real) * Inv.inv a) * (robinCpowLogTail (a : Complex) (k + 1) x).re := by
  have hRaw := robinCpowLogTail_recurrence hx (show (a : Complex).re < 0 from ha) k
  have hPow : (x : Complex)^(a : Complex) = ((x^a : Real) : Complex) :=
    (Complex.ofReal_cpow (lt_trans Real.zero_lt_one hx).le a).symm
  rw [hPow, <- Complex.ofReal_inv] at hRaw
  have hRe := congrArg Complex.re hRaw
  simpa only [Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero, neg_zero,
    zero_add, add_zero] using hRe

/-- The signed next logarithmic tail is retained before taking any bound. -/
theorem robinZeroKernel_ofReal_eq_main_add_signed_tail
    (n : Nat) {r : Real} (hr : r < n) {x : Real} (hx : 1 < x) :
    (robinZeroKernel n (r : Complex) x).re =
      -(n : Real) * Inv.inv (r - n) * x^(r - n) * Inv.inv (Real.log x) +
        ((n : Real) * Inv.inv (r - n) + 1) *
          (robinCpowLogTail ((r - n : Real) : Complex) 2 x).re := by
  have hKernel := robinZeroKernel_eq_nat_mul_tail_one_add_tail_two
    (n := n) (rho := (r : Complex)) hx (show (r : Complex).re < n from hr)
  have hCast : (r : Complex) - (n : Complex) = ((r - n : Real) : Complex) := by push_cast; rfl
  rw [hCast] at hKernel
  have hKernelRe := congrArg Complex.re hKernel
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at hKernelRe
  have hRec := robinCpowLogTail_ofReal_recurrence (show r - n < 0 by linarith) 1 hx
  simp only [Nat.cast_one, pow_one, one_mul] at hRec
  rw [hKernelRe, hRec]
  ring

/-- The square-layer kernel keeps its negative second-order term. -/
theorem robinZeroKernel_half_one_upper {x : Real} (hx : 1 < x) :
    (robinZeroKernel 1 (1 / 2 : Complex) x).re <=
      2 * x^(-(1 / 2 : Real)) * Inv.inv (Real.log x) -
        2 * x^(-(1 / 2 : Real)) * Inv.inv ((Real.log x)^2) +
        8 * x^(-(1 / 2 : Real)) * Inv.inv ((Real.log x)^3) := by
  have hF := robinZeroKernel_ofReal_eq_main_add_signed_tail 1
    (r := (1 / 2 : Real)) (by norm_num) hx
  have hRec := robinCpowLogTail_ofReal_recurrence (a := -(1 / 2 : Real)) (by norm_num) 2 hx
  have hBound := robinCpowLogTail_ofReal_re_le (a := -(1 / 2 : Real)) (by norm_num) 3 hx
  norm_num at hF hRec hBound
  linarith

theorem robinZeroKernel_third_one_upper {x : Real} (hx : 1 < x) :
    (robinZeroKernel 1 (1 / 3 : Complex) x).re <=
      (3 / 2 : Real) * x^(-(2 / 3 : Real)) * Inv.inv (Real.log x) := by
  have hF := robinZeroKernel_ofReal_eq_main_add_signed_tail 1
    (r := (1 / 3 : Real)) (by norm_num) hx
  have hNonneg := robinCpowLogTail_ofReal_re_nonneg (-(2 / 3 : Real)) 2 hx
  norm_num at hF hNonneg
  linarith

/-- Both estimates retain the complete infinite square-layer tail. -/
theorem robinZeroKernel_half_two_bounds {x : Real} (hx : 1 < x) :
    And ((4 / 3 : Real) * x^(-(3 / 2 : Real)) * Inv.inv (Real.log x) -
        (2 / 9 : Real) * x^(-(3 / 2 : Real)) * Inv.inv ((Real.log x)^2) <=
          (robinZeroKernel 2 (1 / 2 : Complex) x).re)
      ((robinZeroKernel 2 (1 / 2 : Complex) x).re <=
        (4 / 3 : Real) * x^(-(3 / 2 : Real)) * Inv.inv (Real.log x)) := by
  have hF := robinZeroKernel_ofReal_eq_main_add_signed_tail 2
    (r := (1 / 2 : Real)) (by norm_num) hx
  have hNonneg := robinCpowLogTail_ofReal_re_nonneg (-(3 / 2 : Real)) 2 hx
  have hBound := robinCpowLogTail_ofReal_re_le (a := -(3 / 2 : Real)) (by norm_num) 2 hx
  norm_num at hF hNonneg hBound
  constructor <;> linarith

theorem robinZeroKernel_third_two_upper {x : Real} (hx : 1 < x) :
    (robinZeroKernel 2 (1 / 3 : Complex) x).re <=
      (6 / 5 : Real) * x^(-(5 / 3 : Real)) * Inv.inv (Real.log x) := by
  have hF := robinZeroKernel_ofReal_eq_main_add_signed_tail 2
    (r := (1 / 3 : Real)) (by norm_num) hx
  have hNonneg := robinCpowLogTail_ofReal_re_nonneg (-(5 / 3 : Real)) 2 hx
  norm_num at hF hNonneg
  linarith

end

end Robin1984
