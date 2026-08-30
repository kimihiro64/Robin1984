import Robin1984.Arithmetic.Definitions

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: No external theorem is directly formalized; published inputs retain their attribution in the imported modules and project bibliography.
- Formalization note: The retained definitions, interfaces, reductions, or proof assembly are primarily original to this formalization.
- PROVENANCE-END
-/

/-!
# Divisor ratios and Robin's comparison bound

This module collects the elementary arithmetic and logarithmic comparisons
used throughout the finite, colossally abundant, and analytic parts of the
formalization.
-/

namespace Robin1984

/-- The abundancy ratio `sigma(n) / n`, regarded as a real number. -/
noncomputable def abundancy (n : Nat) : Real :=
  (Core.sigmaOneNat n : Real) / (n : Real)

/-- The right-hand side of Robin's inequality after division by `n`. -/
noncomputable def robinBoundRatio (n : Nat) : Real :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : Real))

/-- The reciprocal logarithmic scale attached to the Robin bound. -/
noncomputable def robinFrontierCutoff (n : Nat) : Real :=
  (Real.log (n : Real) * Real.log (Real.log (n : Real)))⁻¹

/-- The Robin comparison ratio is positive above the exceptional cutoff. -/
theorem robinBoundRatio_pos_of_cutoff
    {n : Nat} (hnCut : 5040 < n) :
    0 < robinBoundRatio n := by
  unfold robinBoundRatio
  have hnPos : (0 : Real) < (n : Real) := by
    exact_mod_cast (Nat.zero_lt_of_lt hnCut)
  have hlogGtOne : (1 : Real) < Real.log (n : Real) := by
    rw [Real.lt_log_iff_exp_lt hnPos]
    exact lt_trans Real.exp_one_lt_three
      (by exact_mod_cast (by omega : 3 < n))
  have hloglogPos : 0 < Real.log (Real.log (n : Real)) :=
    Real.log_pos hlogGtOne
  positivity

/-- Logarithmic form of the Robin comparison ratio above the cutoff. -/
theorem log_robinBoundRatio_eq_of_cutoff
    {n : Nat} (hnCut : 5040 < n) :
    Real.log (robinBoundRatio n) =
      Real.eulerMascheroniConstant +
        Real.log (Real.log (Real.log (n : Real))) := by
  unfold robinBoundRatio
  have hnPos : (0 : Real) < (n : Real) := by
    exact_mod_cast (Nat.zero_lt_of_lt hnCut)
  have hlogGtOne : (1 : Real) < Real.log (n : Real) := by
    rw [Real.lt_log_iff_exp_lt hnPos]
    exact lt_trans Real.exp_one_lt_three
      (by exact_mod_cast (by omega : 3 < n))
  have hloglogPos : 0 < Real.log (Real.log (n : Real)) :=
    Real.log_pos hlogGtOne
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hloglogPos), Real.log_exp]

/-- The Robin frontier cutoff is positive above the exceptional cutoff. -/
theorem robinFrontierCutoff_pos_of_cutoff
    {n : Nat} (hnCut : 5040 < n) :
    0 < robinFrontierCutoff n := by
  have hnPos : (0 : Real) < (n : Real) := by
    exact_mod_cast (Nat.zero_lt_of_lt hnCut)
  have hlogPos : 0 < Real.log (n : Real) := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogGtOne : (1 : Real) < Real.log (n : Real) := by
    rw [Real.lt_log_iff_exp_lt hnPos]
    exact lt_trans Real.exp_one_lt_three
      (by exact_mod_cast (by omega : 3 < n))
  have hloglogPos : 0 < Real.log (Real.log (n : Real)) :=
    Real.log_pos hlogGtOne
  unfold robinFrontierCutoff
  exact inv_pos.mpr (mul_pos hlogPos hloglogPos)

/-- Robin's inequality rewritten after division by the positive integer `n`. -/
theorem nativeRobinInequality_iff_abundancy_lt_bound
    {n : Nat} (hn : 0 < n) :
    Core.NativeRobinInequality n <-> abundancy n < robinBoundRatio n := by
  unfold Core.NativeRobinInequality abundancy robinBoundRatio
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  constructor
  . intro h
    have hdiv := div_lt_div_of_pos_right h hnReal
    have hright :
        (Real.exp Real.eulerMascheroniConstant * (n : Real) *
            Real.log (Real.log (n : Real))) / (n : Real) =
          Real.exp Real.eulerMascheroniConstant *
            Real.log (Real.log (n : Real)) := by
      field_simp [hnReal.ne']
    simpa [abundancy, robinBoundRatio, hright] using hdiv
  . intro h
    have hmul := mul_lt_mul_of_pos_right h hnReal
    have hleft :
        ((Core.sigmaOneNat n : Real) / (n : Real)) * (n : Real) =
          (Core.sigmaOneNat n : Real) := by
      field_simp [hnReal.ne']
    have hright :
        (Real.exp Real.eulerMascheroniConstant *
            Real.log (Real.log (n : Real))) * (n : Real) =
          Real.exp Real.eulerMascheroniConstant * (n : Real) *
            Real.log (Real.log (n : Real)) := by
      ring
    simpa [abundancy, robinBoundRatio, hleft, hright] using hmul

/-- The Robin frontier cutoff is antitone above the exceptional cutoff. -/
theorem robinFrontierCutoff_antitone_above_cutoff
    {n m : Nat} (hnCut : 5040 < n) (hnm : n <= m) :
    robinFrontierCutoff m <= robinFrontierCutoff n := by
  have hnPosNat : 0 < n := Nat.zero_lt_of_lt hnCut
  have hmPosNat : 0 < m := lt_of_lt_of_le hnPosNat hnm
  have hnRealPos : (0 : Real) < (n : Real) := by exact_mod_cast hnPosNat
  have hmRealPos : (0 : Real) < (m : Real) := by exact_mod_cast hmPosNat
  have hnmReal : (n : Real) <= (m : Real) := by exact_mod_cast hnm
  have hlognPos : 0 < Real.log (n : Real) := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hloglognPos : 0 < Real.log (Real.log (n : Real)) := by
    have hlognGtOne : (1 : Real) < Real.log (n : Real) := by
      rw [Real.lt_log_iff_exp_lt hnRealPos]
      exact lt_trans Real.exp_one_lt_three
        (by exact_mod_cast (by omega : 3 < n))
    exact Real.log_pos hlognGtOne
  have hlogLe : Real.log (n : Real) <= Real.log (m : Real) :=
    Real.log_le_log hnRealPos hnmReal
  have hloglogLe :
      Real.log (Real.log (n : Real)) <= Real.log (Real.log (m : Real)) :=
    Real.log_le_log hlognPos hlogLe
  have hlogmPos : 0 < Real.log (m : Real) := lt_of_lt_of_le hlognPos hlogLe
  have hloglogmPos : 0 < Real.log (Real.log (m : Real)) :=
    lt_of_lt_of_le hloglognPos hloglogLe
  have hProd :
      Real.log (n : Real) * Real.log (Real.log (n : Real)) <=
        Real.log (m : Real) * Real.log (Real.log (m : Real)) := by
    exact mul_le_mul hlogLe hloglogLe
      (le_of_lt hloglognPos) (le_of_lt hlogmPos)
  have hnProdPos :
      0 < Real.log (n : Real) * Real.log (Real.log (n : Real)) :=
    mul_pos hlognPos hloglognPos
  have hmProdPos :
      0 < Real.log (m : Real) * Real.log (Real.log (m : Real)) :=
    mul_pos hlogmPos hloglogmPos
  unfold robinFrontierCutoff
  exact (inv_le_inv₀ hmProdPos hnProdPos).2 hProd

/-- The divisor sum is positive for every positive integer. -/
theorem sigmaOneNat_pos {n : Nat} (hn : 0 < n) :
    0 < Core.sigmaOneNat n := by
  unfold Core.sigmaOneNat
  exact ArithmeticFunction.sigma_pos 1 n (Nat.ne_of_gt hn)

/-- The abundancy ratio is positive for every positive integer. -/
theorem abundancy_pos {n : Nat} (hn : 0 < n) :
    0 < abundancy n := by
  unfold abundancy
  exact div_pos
    (by exact_mod_cast sigmaOneNat_pos hn)
    (by exact_mod_cast hn)

end Robin1984
