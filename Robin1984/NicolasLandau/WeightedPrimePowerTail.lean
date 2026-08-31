import Robin1984.Equivalence.RobinLemmaTwo
/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: N. Costa Pereira, Estimates for the Chebyshev Function psi(x)-theta(x), Mathematics of Computation 44 (1985), 211--221, and the 1987 corrigendum.
- Formalization note: The prime-power inequalities are source-based; their weighted integral form and composition with Robin's kernels are formalization-specific.
- PROVENANCE-END
-/

/-!
# Complete root-scale prime-power tails

The substitution t=u^k carries the actual Robin weight to w_(kn)/k.
Together with the proved Costa-Pereira inequalities this estimates the
complete prime-power tail directly using Robin's proved J bounds.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

theorem robinRealWeight_rpow_pullback
    (n k : Nat) (hk : 0 < k) {u : Real} (hu : 1 < u) :
    (k : Real) * u^((k : Real) - 1) * robinRealWeight n (u^(k : Real)) =
      Inv.inv (k : Real) * robinRealWeight (k * n) u := by
  have huPos : 0 < u := lt_trans Real.zero_lt_one hu
  have hkPos : (0 : Real) < k := by exact_mod_cast hk
  have hPowers : u^((k : Real) - 1) * (u^(k : Real))^(-(n : Real) - 1) =
      u^(-((k : Real) * n) - 1) := by
    rw [<- Real.rpow_mul huPos.le, <- Real.rpow_add huPos]
    congr 1
    ring
  unfold robinRealWeight
  rw [Real.log_rpow huPos]
  simp only [Nat.cast_mul]
  calc
    _ = (k : Real) * (u^((k : Real) - 1) * (u^(k : Real))^(-(n : Real) - 1)) *
        (((n : Real) * ((k : Real) * Real.log u) + 1) / ((k : Real) * Real.log u)^2) := by ring
    _ = _ := by
      rw [hPowers]
      field_simp [hkPos.ne', (Real.log_pos hu).ne'] <;> ring

/-- Exact change of variable for an arbitrary root-scale integrand. -/
theorem integral_root_mul_robinRealWeight
    (g : Real -> Real) (n k : Nat) (hk : 0 < k) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real =>
        g (t^(Inv.inv (k : Real))) * robinRealWeight n t) =
      Inv.inv (k : Real) * integral (volume.restrict (Ioi (x^(Inv.inv (k : Real)))))
        (fun u : Real => g u * robinRealWeight (k * n) u) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast hk
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hRoot : 1 < x^(Inv.inv (k : Real)) := Real.one_lt_rpow hx (inv_pos.mpr hkPos)
  have hChange := integral_comp_rpow_Ioi_of_pos'
    (g := fun t : Real => g (t^(Inv.inv (k : Real))) * robinRealWeight n t)
    hkPos hxPos.le
  rw [<- hChange, <- integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  have huOne : 1 < u := lt_trans hRoot hu
  have huPos : 0 < u := lt_trans Real.zero_lt_one huOne
  have hRootBack : (u^(k : Real))^(Inv.inv (k : Real)) = u := by
    rw [<- Real.rpow_mul huPos.le]
    have hCancel : (k : Real) * Inv.inv (k : Real) = 1 := by field_simp
    rw [hCancel, Real.rpow_one]
  rw [smul_eq_mul, hRootBack]
  calc
    _ = g u * ((k : Real) * u^((k : Real) - 1) * robinRealWeight n (u^(k : Real))) := by ring
    _ = _ := by rw [robinRealWeight_rpow_pullback n k hk huOne]; ring

theorem integrableOn_rpow_mul_robinRealWeight
    {n : Nat} {r x : Real} (hx : 1 < x) (hr : r < n) :
    IntegrableOn (fun t : Real => t^r * robinRealWeight n t) (Ioi x) := by
  have hRaw := (integrableOn_cpow_mul_robinRealWeight (rho := (r : Complex)) hx hr).norm
  apply IntegrableOn.congr_fun hRaw _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans Real.zero_lt_one (lt_trans hx ht)),
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (robinRealWeight_nonneg (lt_trans hx ht))]
  rfl

theorem integral_rpow_mul_robinRealWeight
    (n : Nat) (r : Real) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real => t^r * robinRealWeight n t) =
      (robinZeroKernel n (r : Complex) x).re := by
  have hEq : robinZeroKernel n (r : Complex) x =
      ((integral (volume.restrict (Ioi x)) (fun t : Real => t^r * robinRealWeight n t) : Real) : Complex) := by
    rw [robinZeroKernel_eq_integral_cpow_weight n (r : Complex) hx, <- integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (lt_trans Real.zero_lt_one (lt_trans hx ht)).le]
  rw [hEq, Complex.ofReal_re]

theorem inv_nat_lt_nat_of_two_le
    {n k : Nat} (hn : 1 <= n) (hk : 2 <= k) : Inv.inv (k : Real) < n := by
  have hkGt : (1 : Real) < k := by exact_mod_cast (show 1 < k by omega)
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn
  have hInv : Inv.inv (k : Real) < 1 := by
    simpa only [one_div, inv_one] using one_div_lt_one_div_of_lt Real.zero_lt_one hkGt
  exact lt_of_lt_of_le hInv hnReal

theorem integrableOn_psi_root_mul_robinRealWeight
    {n k : Nat} (hn : 1 <= n) (hk : 2 <= k) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real =>
      Chebyshev.psi (t^(Inv.inv (k : Real))) * robinRealWeight n t) (Ioi x) := by
  have hMain := integrableOn_rpow_mul_robinRealWeight hx (inv_nat_lt_nat_of_two_le hn hk)
  have hPsiMeas : Measurable (fun t : Real => Chebyshev.psi (t^(Inv.inv (k : Real)))) :=
    Chebyshev.psi_mono.measurable.comp (by fun_prop)
  have hWeightMeas : Measurable (robinRealWeight n) := by unfold robinRealWeight; fun_prop
  apply Integrable.mono' (hMain.const_mul (Real.log 4 + 4))
    (hPsiMeas.mul hWeightMeas).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htOne : 1 < t := lt_trans hx ht
  have htNonneg : 0 <= t := le_of_lt (lt_trans Real.zero_lt_one htOne)
  have hWeight := robinRealWeight_nonneg (n := n) htOne
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Chebyshev.psi_nonneg _) hWeight)]
  calc
    _ <= ((Real.log 4 + 4) * t^(Inv.inv (k : Real))) * robinRealWeight n t :=
      mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg htNonneg _)) hWeight
    _ = _ := by ring

/-- Each complete root-scale prime-power tail is an elementary real-power
kernel plus a weighted psi error whose bound is already proved. -/
theorem integral_psi_root_mul_robinRealWeight_eq
    {n k : Nat} (hn : 1 <= n) (hk : 2 <= k) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real =>
        Chebyshev.psi (t^(Inv.inv (k : Real))) * robinRealWeight n t) =
      (robinZeroKernel n ((Inv.inv (k : Real)) : Complex) x).re +
        Inv.inv (k : Real) * robinPsiWeightedErrorIntegral (k * n) (x^(Inv.inv (k : Real))) := by
  have hPsi := integrableOn_psi_root_mul_robinRealWeight hn hk hx
  have hMain := integrableOn_rpow_mul_robinRealWeight hx (inv_nat_lt_nat_of_two_le hn hk)
  have hError : IntegrableOn (fun t : Real =>
      (Chebyshev.psi (t^(Inv.inv (k : Real))) - t^(Inv.inv (k : Real))) * robinRealWeight n t) (Ioi x) := by
    apply IntegrableOn.congr_fun (hPsi.sub hMain) _ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.sub_apply]
    ring
  calc
    _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
        t^(Inv.inv (k : Real)) * robinRealWeight n t) +
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Chebyshev.psi (t^(Inv.inv (k : Real))) - t^(Inv.inv (k : Real))) * robinRealWeight n t) := by
      rw [<- integral_add hMain hError]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      ring
    _ = _ := by
      rw [integral_rpow_mul_robinRealWeight n _ hx,
        integral_root_mul_robinRealWeight (fun u : Real => Chebyshev.psi u - u) n k (by omega) hx]
      simp only [Complex.ofReal_inv, robinPsiWeightedErrorIntegral]

def robinPrimePowerWeightedTail (n : Nat) (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    (Chebyshev.psi t - Chebyshev.theta t) * robinRealWeight n t)

theorem integrableOn_robinPrimePowerWeightedTail
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real =>
      (Chebyshev.psi t - Chebyshev.theta t) * robinRealWeight n t) (Ioi x) := by
  have hTwo := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (2 : Nat)) hx
  have hThree := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (3 : Nat)) hx
  have hFive := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (5 : Nat)) hx
  have hWeightMeas : Measurable (robinRealWeight n) := by unfold robinRealWeight; fun_prop
  apply Integrable.mono' ((hTwo.add hThree).add hFive)
    (((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).mul hWeightMeas).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hWeight := robinRealWeight_nonneg (n := n) (lt_trans hx ht)
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t)) hWeight)]
  simpa only [add_mul, Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t) hWeight

theorem robinPrimePowerWeightedTail_le_three_root_integrals
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    robinPrimePowerWeightedTail n x <=
      integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.psi (t^(Inv.inv (2 : Real))) * robinRealWeight n t) +
      integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.psi (t^(Inv.inv (3 : Real))) * robinRealWeight n t) +
      integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.psi (t^(Inv.inv (5 : Real))) * robinRealWeight n t) := by
  have hTwo := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (2 : Nat)) hx
  have hThree := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (3 : Nat)) hx
  have hFive := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (5 : Nat)) hx
  have hAdd := integral_add (hTwo.add hThree) hFive
  simp only [Pi.add_apply] at hAdd
  rw [integral_add hTwo hThree] at hAdd
  norm_num at hAdd
  norm_num
  have hMono : robinPrimePowerWeightedTail n x <= integral (volume.restrict (Ioi x))
      (fun t : Real =>
        Chebyshev.psi (t^(Inv.inv (2 : Real))) * robinRealWeight n t +
        Chebyshev.psi (t^(Inv.inv (3 : Real))) * robinRealWeight n t +
        Chebyshev.psi (t^(Inv.inv (5 : Real))) * robinRealWeight n t) := by
    unfold robinPrimePowerWeightedTail
    apply integral_mono_ae (integrableOn_robinPrimePowerWeightedTail hn hx) ((hTwo.add hThree).add hFive)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [Pi.add_apply]
    simpa only [add_mul, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t)
        (robinRealWeight_nonneg (n := n) (lt_trans hx ht))
  norm_num at hMono
  exact hMono.trans_eq hAdd

theorem three_root_integrals_le_robinPrimePowerWeightedTail
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.psi (t^(Inv.inv (2 : Real))) * robinRealWeight n t) +
      integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.psi (t^(Inv.inv (3 : Real))) * robinRealWeight n t) +
      integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.psi (t^(Inv.inv (7 : Real))) * robinRealWeight n t) <=
        robinPrimePowerWeightedTail n x := by
  have hTwo := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (2 : Nat)) hx
  have hThree := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (3 : Nat)) hx
  have hSeven := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (7 : Nat)) hx
  have hAdd := integral_add (hTwo.add hThree) hSeven
  simp only [Pi.add_apply] at hAdd
  rw [integral_add hTwo hThree] at hAdd
  norm_num at hAdd
  norm_num
  have hMono : integral (volume.restrict (Ioi x)) (fun t : Real =>
      Chebyshev.psi (t^(Inv.inv (2 : Real))) * robinRealWeight n t +
      Chebyshev.psi (t^(Inv.inv (3 : Real))) * robinRealWeight n t +
      Chebyshev.psi (t^(Inv.inv (7 : Real))) * robinRealWeight n t) <=
      robinPrimePowerWeightedTail n x := by
    unfold robinPrimePowerWeightedTail
    apply integral_mono_ae ((hTwo.add hThree).add hSeven) (integrableOn_robinPrimePowerWeightedTail hn hx)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [Pi.add_apply]
    have htNonneg : 0 <= t := le_of_lt (lt_trans Real.zero_lt_one (lt_trans hx ht))
    simpa only [add_mul, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi htNonneg)
        (robinRealWeight_nonneg (n := n) (lt_trans hx ht))
  norm_num at hMono
  exact hAdd.symm.trans_le hMono

def robinRootPsiTailUpper (n k : Nat) (x : Real) : Real :=
  (robinZeroKernel n ((Inv.inv (k : Real)) : Complex) x).re +
    Inv.inv (k : Real) * robinPsiWeightedErrorScalar (k * n) (x^(Inv.inv (k : Real)))

def robinRootPsiTailLower (n k : Nat) (x : Real) : Real :=
  (robinZeroKernel n ((Inv.inv (k : Real)) : Complex) x).re +
    Inv.inv (k : Real) * (-robinPsiWeightedErrorScalar (k * n) (x^(Inv.inv (k : Real))) -
      Real.log (2 * Real.pi) * (x^(Inv.inv (k : Real)))^(-((k * n : Nat) : Real)) *
        Inv.inv (Real.log (x^(Inv.inv (k : Real)))))

theorem integral_psi_root_mul_robinRealWeight_bounds
    (hRH : RiemannHypothesis) {n k : Nat} (hn : 1 <= n) (hk : 2 <= k)
    {x : Real} (hx : 1 < x) (hRoot : 2 <= x^(Inv.inv (k : Real))) :
    And (robinRootPsiTailLower n k x <=
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          Chebyshev.psi (t^(Inv.inv (k : Real))) * robinRealWeight n t))
      (integral (volume.restrict (Ioi x)) (fun t : Real =>
          Chebyshev.psi (t^(Inv.inv (k : Real))) * robinRealWeight n t) <=
        robinRootPsiTailUpper n k x) := by
  have hkn : 1 <= k * n := by nlinarith
  have hBounds := robinPsiWeightedErrorIntegral_bounds_all hRH hkn hRoot
  have hkNonneg : 0 <= Inv.inv (k : Real) := inv_nonneg.mpr (Nat.cast_nonneg k)
  rw [integral_psi_root_mul_robinRealWeight_eq hn hk hx]
  constructor
  . exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hBounds.1 hkNonneg)
  . exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hBounds.2 hkNonneg)

theorem two_le_root_of_pow_le
    {k : Nat} (hk : 0 < k) {x : Real} (hx : (2 : Real)^k <= x) :
    2 <= x^(Inv.inv (k : Real)) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast hk
  have hPower : ((2 : Real)^k)^(Inv.inv (k : Real)) = 2 := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
    have hCancel : (k : Real) * Inv.inv (k : Real) = 1 := by field_simp
    rw [hCancel, Real.rpow_one]
  have hCompare := Real.rpow_le_rpow (by positivity : (0 : Real) <= 2^k) hx (inv_nonneg.mpr hkPos.le)
  rw [hPower] at hCompare
  exact hCompare

/-- Explicit cumulative prime-power bounds. They depend only on the already
proved Robin zero scalar at four root scales, not an assumed pointwise
prime-power envelope. -/
theorem robinPrimePowerWeightedTail_root_bounds
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) {x : Real} (hx : 128 <= x) :
    And (robinRootPsiTailLower n 2 x + robinRootPsiTailLower n 3 x + robinRootPsiTailLower n 7 x <=
        robinPrimePowerWeightedTail n x)
      (robinPrimePowerWeightedTail n x <=
        robinRootPsiTailUpper n 2 x + robinRootPsiTailUpper n 3 x + robinRootPsiTailUpper n 5 x) := by
  have hxOne : 1 < x := by linarith
  have hRootTwo : 2 <= x^(Inv.inv ((2 : Nat) : Real)) :=
    two_le_root_of_pow_le (by norm_num : 0 < (2 : Nat)) (by norm_num; linarith)
  have hRootThree : 2 <= x^(Inv.inv ((3 : Nat) : Real)) :=
    two_le_root_of_pow_le (by norm_num : 0 < (3 : Nat)) (by norm_num; linarith)
  have hRootFive : 2 <= x^(Inv.inv ((5 : Nat) : Real)) :=
    two_le_root_of_pow_le (by norm_num : 0 < (5 : Nat)) (by norm_num; linarith)
  have hRootSeven : 2 <= x^(Inv.inv ((7 : Nat) : Real)) :=
    two_le_root_of_pow_le (by norm_num : 0 < (7 : Nat)) (by norm_num; linarith)
  have hTwo := integral_psi_root_mul_robinRealWeight_bounds hRH hn (by norm_num : 2 <= (2 : Nat)) hxOne hRootTwo
  have hThree := integral_psi_root_mul_robinRealWeight_bounds hRH hn (by norm_num : 2 <= (3 : Nat)) hxOne hRootThree
  have hFive := integral_psi_root_mul_robinRealWeight_bounds hRH hn (by norm_num : 2 <= (5 : Nat)) hxOne hRootFive
  have hSeven := integral_psi_root_mul_robinRealWeight_bounds hRH hn (by norm_num : 2 <= (7 : Nat)) hxOne hRootSeven
  have hUpper := robinPrimePowerWeightedTail_le_three_root_integrals hn hxOne
  have hLower := three_root_integrals_le_robinPrimePowerWeightedTail hn hxOne
  constructor
  . exact (add_le_add (add_le_add hTwo.1 hThree.1) hSeven.1).trans hLower
  . exact hUpper.trans (add_le_add (add_le_add hTwo.2 hThree.2) hFive.2)

end

end Robin1984
