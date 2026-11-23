import Robin1984.GRH.DedekindCutoffMertens
import Robin1984.GRH.SupportingLine

/-!
# Prime-power comparison for the corrected ideal Robin criterion

Each local divisor factor is bounded by its truncated logarithmic series.
Applying the prime-power supporting line at the logarithmic norm of the ideal
then leaves the weighted Mertens sum and its boundary term.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The finite supporting-line inequality for weighted Euler factors.
- Formalization note: The occupied prime powers carry logarithmic norm cost.
- Content basis: Finite norm factorization and the local truncated series bound.
- Dependency status: Optional GRH extension and existing Mathlib APIs.
-/

open IsDedekindDomain NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "PP" => Prod P Nat

/-- The logarithm of the divisor ratio is bounded by the Mertens prime-power
sum and the supporting-line boundary term at the log norm of the ideal. -/
theorem log_idealDivisorRatio_le_mertensSupportingLine
    (a : Ideal (RingOfIntegers K)) (ha : Not (a = 0))
    (hx : 1 < Real.log (Ideal.absNorm a : Real)) :
    let x := Real.log (Ideal.absNorm a : Real)
    Real.log ((idealDivisorNormSum a ha : Real) / (Ideal.absNorm a : Real)) <=
      dedekindMertensPrimePowerSum K x +
        (x - dedekindChebyshev K x) / (x * Real.log x) := by
  classical
  let m := primeMultisetIdealEquiv.symm (Subtype.mk a ha)
  let q (p : P) : Real := dedekindPrimeNorm K p
  let r (p : P) : Real := Inv.inv (q p)
  let x := Real.log (Ideal.absNorm a : Real)
  let piece (p : P) : Finset PP :=
    (Finset.range (m.count p)).image (fun j => (p, j))
  let occupied := m.toFinset.biUnion piece
  let frontier := primePowersUpTo K (Nat.floor x)
  let N (i : PP) : Real := dedekindPrimePowerNorm K i
  let cost (i : PP) : Real := Real.log (q i.1)
  let w (i : PP) : Real := cost i / (N i * Real.log (N i))
  let geom (p : P) := (Finset.range (m.count p + 1)).sum (fun j => r p ^ j)
  have hq2 (p : P) : 2 <= q p := by
    change (2 : Real) <= (dedekindPrimeNorm K p : Real)
    exact_mod_cast Nat.succ_le_iff.mpr (one_lt_dedekindPrimeNorm K p)
  have hq (p : P) : 1 < q p := (by norm_num : (1 : Real) < 2).trans_le (hq2 p)
  have hr (p : P) : 0 < r p := inv_pos.mpr (zero_lt_one.trans (hq p))
  have hrHalf (p : P) : r p <= 1 / 2 := by
    rw [show r p = 1 / q p from (one_div _).symm]
    exact one_div_le_one_div_of_le (by norm_num) (hq2 p)
  have hr1 (p : P) : r p < 1 := (hrHalf p).trans_lt (by norm_num)
  have hGeo (p : P) : geom p = (1 - r p ^ (m.count p + 1)) / (1 - r p) := by
    unfold geom
    rw [geom_sum_eq (hr1 p).ne]
    field_simp [(sub_ne_zero.mpr (hr1 p).ne'), (sub_ne_zero.mpr (hr1 p).ne)] <;> ring
  have hGeoPos (p : P) : 0 < geom p := by
    rw [hGeo p]
    apply div_pos _ (sub_pos.mpr (hr1 p))
    exact sub_pos.mpr
      ((pow_lt_one_iff_of_nonneg (hr p).le (Nat.succ_ne_zero _)).mpr (hr1 p))
  have hPieces (f : PP -> Real) :
      occupied.sum f = m.toFinset.sum (fun p =>
        (Finset.range (m.count p)).sum fun j => f (p, j)) := by
    have hDisjoint : (m.toFinset : Set P).PairwiseDisjoint piece := by
      intro p _ t _ hpt
      change Disjoint (piece p) (piece t)
      rw [Finset.disjoint_left]
      intro i hi hj
      have hp := Finset.mem_image.mp hi
      have ht := Finset.mem_image.mp hj
      exact hpt ((congrArg Prod.fst (Classical.choose_spec hp).2).trans
        (congrArg Prod.fst (Classical.choose_spec ht).2).symm)
    unfold occupied
    rw [Finset.sum_biUnion hDisjoint]
    apply Finset.sum_congr rfl
    intro p _
    unfold piece
    rw [Finset.sum_image]
    intro j _ k _ h
    exact congrArg Prod.snd h
  have hIdeal : primeMultisetIdealEquiv m = Subtype.mk a ha :=
    primeMultisetIdealEquiv.apply_symm_apply _
  have hNorm : (Ideal.absNorm a : Real) =
      m.toFinset.prod (fun p => q p ^ m.count p) := by
    have hn := absNorm_primeMultiset_eq_prod_count K m m.toFinset Finset.Subset.rfl
    rw [hIdeal] at hn
    change (Ideal.absNorm a : Real) = m.toFinset.prod
      (fun p => (dedekindPrimeNorm K p : Real) ^ m.count p)
    exact_mod_cast hn
  have hOccCost : occupied.sum cost = x := by
    rw [hPieces, show x = Real.log (Ideal.absNorm a : Real) from rfl, hNorm]
    rw [Real.log_prod (fun p _ => (pow_pos (zero_lt_one.trans (hq p)) _).ne')]
    simp only [cost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.log_pow]
  have hInv (i : PP) : w i = Inv.inv (N i * ((i.2 + 1 : Nat) : Real)) := by
    have hN : N i = q i.1 ^ (i.2 + 1) := Nat.cast_pow _ _
    have hN0 : 0 < N i := by
      rw [hN]
      exact pow_pos (zero_lt_one.trans (hq i.1)) _
    have hCount : 0 < ((i.2 + 1 : Nat) : Real) := by exact_mod_cast Nat.succ_pos i.2
    have hLog : 0 < Real.log (q i.1) := Real.log_pos (hq i.1)
    have hLp : Real.log (N i) = ((i.2 + 1 : Nat) : Real) * Real.log (q i.1) := by
      rw [hN, Real.log_pow]
    unfold w cost
    rw [hLp, <- one_div]
    field_simp [hN0.ne', hCount.ne', hLog.ne']
  have hOccValue :
      Real.log ((idealDivisorNormSum a ha : Real) / (Ideal.absNorm a : Real)) <=
        occupied.sum w := by
    have hProduct := idealDivisorNormSum_div_primeMultiset K m
    rw [hIdeal] at hProduct
    change (idealDivisorNormSum a ha : Real) / (Ideal.absNorm a : Real) =
      m.toFinset.prod geom at hProduct
    rw [hPieces, hProduct, Real.log_prod (fun p _ => (hGeoPos p).ne')]
    apply Finset.sum_le_sum
    intro p _
    rw [hGeo p]
    have hValue (j : Nat) : w (p, j) = r p ^ (j + 1) / ((j + 1 : Nat) : Real) := by
      rw [hInv]
      simp [N, r, q, dedekindPrimePowerNorm, Nat.cast_pow, inv_pow, div_eq_mul_inv, mul_comm]
    simp_rw [hValue]
    exact logGeomFactor_le_primePowerLogSeries (hr p) (hrHalf p) (m.count p)
  have hFrontCost : frontier.sum cost = dedekindChebyshev K x := rfl
  have hFrontValue : frontier.sum w = dedekindMertensPrimePowerSum K x := by
    rw [dedekindMertensPrimePowerSum_eq_sum_primePowersUpTo]
    exact Finset.sum_congr rfl (fun i _ => hInv i)
  have hN1 (i : PP) : 1 < N i := by
    have hni := one_lt_dedekindPrimeNorm K i.1
    have hpow : dedekindPrimeNorm K i.1 <= dedekindPrimePowerNorm K i := by
      change dedekindPrimeNorm K i.1 <= dedekindPrimeNorm K i.1 ^ (i.2 + 1)
      simpa only [pow_one] using Nat.pow_le_pow_right hni.le (Nat.succ_pos i.2)
    change (1 : Real) < (dedekindPrimePowerNorm K i : Real)
    exact_mod_cast hni.trans_le hpow
  have hx0 : 0 <= x := (zero_lt_one.trans hx).le
  have hFront (i : PP) : Membership.mem frontier i <-> N i <= x :=
    (mem_primePowersUpTo K).trans (Nat.le_floor_iff hx0)
  have hLine := weightedPrimePowerSupportingLine occupied frontier N cost x hx
    (fun i _ => hN1 i) (fun i _ => (Real.log_pos (hq i.1)).le)
    (fun i hi => (hFront i).mp hi)
    (fun i _ hi => (lt_of_not_ge (fun h => hi ((hFront i).mpr h))).le)
  change occupied.sum w <= frontier.sum w +
    (occupied.sum cost - frontier.sum cost) / (x * Real.log x) at hLine
  rw [hOccCost, hFrontCost, hFrontValue] at hLine
  exact hOccValue.trans hLine

end Robin1984.GRH
