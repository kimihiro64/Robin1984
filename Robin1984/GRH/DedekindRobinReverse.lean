import Robin1984.GRH.DedekindCutoffLoss
import Robin1984.GRH.DedekindMertensNormalization
import Robin1984.GRH.DedekindMertensTailConverse
import Robin1984.GRH.DedekindRobinLogBound

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The reverse implication of the corrected ideal Robin criterion.
- Formalization note: The corrected ideal Robin inequality implies Dedekind RH.
- PROVENANCE-END
-/

/-!
# The corrected ideal Robin inequality implies Dedekind RH

The prime ideal theorem controls the cutoff logarithmic norm. The
geometric losses and the log-log tangent leave precisely the signed
weighted Mertens tail needed by the zero-free converse.
-/

open Filter NumberField Set Topology

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

private theorem eventual_dedekindChebyshev_comparable :
    exists b : Real, forall x : Real, b <= x -> 1 <= x ->
      And (x / 2 <= dedekindChebyshev K x) (dedekindChebyshev K x <= 2 * x) := by
  have hWindow : Membership.mem (nhds (1 : Real)) (Ioo (1 / 2 : Real) 2) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hP := (DedekindZeta.dedekindChebyshev_div_tendsto_one K).eventually hWindow
  choose b hb using eventually_atTop.mp hP
  refine Exists.intro b (fun x hbx hx => ?_)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hRange : Membership.mem (Ioo (1 / 2 : Real) 2) (dedekindChebyshev K x / x) := hb x hbx
  have hLo := mul_lt_mul_of_pos_right hRange.1 hx0
  have hHi := mul_lt_mul_of_pos_right hRange.2 hx0
  have hId : (dedekindChebyshev K x / x) * x = dedekindChebyshev K x := by
    field_simp [hx0.ne']
  rw [hId] at hLo hHi
  exact And.intro (by linarith only [hLo]) hHi.le

private theorem absNorm_le_idealDivisorNormSum (a : Ideal (RingOfIntegers K))
    (ha : Not (a = 0)) : Ideal.absNorm a <= idealDivisorNormSum a ha := by
  classical
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
  let d : {d : Ideal (RingOfIntegers K) // Dvd.dvd d a} := Subtype.mk a (dvd_refl a)
  unfold idealDivisorNormSum
  change Ideal.absNorm d.val <= Finset.univ.sum
    (fun p : {p : Ideal (RingOfIntegers K) // Dvd.dvd p a} => Ideal.absNorm p.val)
  exact Finset.single_le_sum
    (f := fun p : {p : Ideal (RingOfIntegers K) // Dvd.dvd p a} => Ideal.absNorm p.val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)

/-- The actual corrected ideal inequality forces Dedekind RH in the same field. -/
theorem dedekindRH_of_correctedIdealRobin (h : CorrectedIdealRobin K) : DedekindRH K := by
  classical
  choose cutoff hCutoff using h
  choose b hb using eventual_dedekindChebyshev_comparable K
  let B := max 1 b
  let A := 2 + dedekindChebyshev K B
  have hNonneg := dedekindChebyshev_nonneg K B
  have hA : 0 <= A := by dsimp only [A]; linarith only [hNonneg]
  have hPsi (x : Real) (hx : 1 <= x) : dedekindChebyshev K x <= A * x := by
    by_cases hBx : B <= x
    case pos =>
      have hVal := (hb x ((le_max_right 1 b).trans hBx) hx).2
      have hTwo : 2 <= A := by dsimp only [A]; linarith only [hNonneg]
      exact hVal.trans (mul_le_mul_of_nonneg_right hTwo (zero_le_one.trans hx))
    case neg =>
      have hVal := monotone_dedekindChebyshev K (le_of_lt (lt_of_not_ge hBx))
      have hNorm : dedekindChebyshev K B <= A := by dsimp only [A]; linarith
      exact hVal.trans (hNorm.trans (le_mul_of_one_le_right hA hx))
  choose c hc using DedekindZeta.exists_dedekindChebyshevPrimitiveLimit K
  let D : Real := (NumberField.discr K).natAbs
  let C : Real := max 0 (12 + 3 * Real.log D)
  let gamma := Real.eulerMascheroniConstant
  let kap := NumberField.dedekindZeta_residue K
  let R := Real.exp gamma * kap
  have hC : 0 <= C := le_max_left _ _
  have hRConst : 12 + 3 * Real.log D <= C := le_max_right _ _
  have hKap : 0 < kap := NumberField.dedekindZeta_residue_pos K
  have hRpos : 0 < R := mul_pos (Real.exp_pos gamma) hKap
  have hLogR : Real.log R = gamma + Real.log kap := by
    unfold R
    rw [Real.log_mul (Real.exp_pos gamma).ne' hKap.ne', Real.log_exp]
  apply DedekindZeta.dedekindRH_of_eventual_weightedMertensTailBound K hc.1
    (C := 32 * A + 4 * C) (add_nonneg (mul_nonneg (by norm_num) hA) (mul_nonneg (by norm_num) hC))
  filter_upwards [eventually_ge_atTop (4 : Real), eventually_ge_atTop b,
    eventually_ge_atTop (2 * (cutoff : Real))] with x hx hbx hcx
  have hx1 : 1 < x := by linarith only [hx]
  have hx0 := zero_lt_one.trans hx1
  have htHalf := (hb x hbx hx1.le).1
  let n := Nat.floor x
  let I := primePowerCutoffIdeal K n
  let N := Ideal.absNorm I
  let t := dedekindChebyshev K x
  let Q := (idealDivisorNormSum I (primePowerCutoffIdeal_ne_zero K n) : Real) / (N : Real)
  have hnPos : 1 <= n := (Nat.le_floor_iff hx0.le).mpr (by simpa only [Nat.cast_one] using hx1.le)
  have hn : Not (n = 0) := Nat.ne_of_gt hnPos
  have hLogN : Real.log (N : Real) = t := log_absNorm_primePowerCutoffIdeal K x
  have ht1 : 1 < t := by
    change x / 2 <= t at htHalf
    linarith only [hx, htHalf]
  have hN0 : 0 < (N : Real) := by
    by_contra hz
    have hNZero : (N : Real) = 0 :=
      le_antisymm (le_of_not_gt hz) (Nat.cast_nonneg N)
    rw [hNZero, Real.log_zero] at hLogN
    linarith only [hLogN, ht1]
  have hNcut : cutoff <= N := by
    have hNlinear := Real.log_le_sub_one_of_pos hN0
    rw [hLogN] at hNlinear
    change x / 2 <= t at htHalf
    exact_mod_cast (show (cutoff : Real) <= (N : Real) from by
      linarith only [hNlinear, hcx, htHalf])
  have hQpos : 0 < Q := by
    have hLe := absNorm_le_idealDivisorNormSum K I (primePowerCutoffIdeal_ne_zero K n)
    have hLeReal : (N : Real) <= (idealDivisorNormSum I (primePowerCutoffIdeal_ne_zero K n) : Real) := by
      exact_mod_cast hLe
    exact div_pos (hN0.trans_le hLeReal) hN0
  have hOrig := hCutoff I (primePowerCutoffIdeal_ne_zero K n) hNcut
  have hOrig' : Q <= R * (Real.log t + (12 + 3 * Real.log D) / Real.sqrt t) := by
    change Q <= R * (Real.log (Real.log (N : Real)) +
      (12 + 3 * Real.log D) / Real.sqrt (Real.log (N : Real))) at hOrig
    rwa [hLogN] at hOrig
  have hSPos := Real.sqrt_pos.mpr (zero_lt_one.trans ht1)
  have hInnerPos : 0 < Real.log t + C / Real.sqrt t :=
    add_pos_of_pos_of_nonneg (Real.log_pos ht1) (div_nonneg hC hSPos.le)
  have hQub : Q <= R * (Real.log t + C / Real.sqrt t) :=
    hOrig'.trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl _) (div_le_div_of_nonneg_right hRConst hSPos.le)) hRpos.le)
  have hLogQ := Real.log_le_log hQpos hQub
  rw [Real.log_mul hRpos.ne' hInnerPos.ne', hLogR] at hLogQ
  have hLogBound := log_correctedIdealThreshold_le hx htHalf hC
  have hCut := dedekindMertensPrimePowerSum_le_log_cutoffIdeal_add K hn
  have hFloorM : dedekindMertensPrimePowerSum K (n : Real) = dedekindMertensPrimePowerSum K x := by
    simp only [dedekindMertensPrimePowerSum, Nat.floor_natCast, n]
  rw [hFloorM] at hCut
  have hLoss := sum_cutoffIdealLoss_le K hA hx1 hPsi
  have hM := DedekindZeta.dedekindMertensPrimePowerSum_eq_residue_weightedTail K
    (a := 3 / 2) (x := x) (by norm_num) (by norm_num) (by linarith only [hx]) hc.1
  have hBoundary : mertensPrimePowerWeight x * (t - x) = (t - x) / (x * Real.log x) := by
    rw [mertensPrimePowerWeight, div_eq_mul_inv, mul_comm]
  rw [show dedekindChebyshev K x = t by rfl, hBoundary] at hM
  have hW : (32 * A + 4 * C) / (Real.sqrt x * Real.log x) =
    32 * A / (Real.sqrt x * Real.log x) + 4 * C / (Real.sqrt x * Real.log x) := add_div _ _ _
  rw [hW]
  linarith only [hCut, hLoss, hLogQ, hLogBound, hM]

end Robin1984.GRH
