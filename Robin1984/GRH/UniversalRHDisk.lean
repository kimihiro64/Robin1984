import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.DiscreteSubset
import Robin1984.GRH.UniversalRH

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The support of a finite exponential sum is determined by its exponential growth under real translations.
- Formalization note: Shows that compact pieces of an admissible zero set are finite and proves the whole-disk triangular equivalence for Universal RH.
- PROVENANCE-END
-/

/-!
# Whole-disk triangular criterion for Universal RH

Admissibility gives finitely many zeros in every compact region. The
triangular bound can test all zeros in each closed disk at once. A finite
linear combination of real translations isolates any chosen exponential
term, so cancellations cannot hide an off-line zero.
-/

set_option autoImplicit false

namespace Robin1984.GRH

private noncomputable def spectralTerm (a : Complex -> Complex) (t : Real) (z : Complex) : Complex :=
  a z * Complex.exp ((t : Complex) * z)

private theorem exists_positive_exp_shift_ne {z r : Complex} (hNe : Not (z = r)) :
    exists h : Real, 0 < h /\
      Not (Complex.exp ((h : Complex) * z) = Complex.exp ((h : Complex) * r)) := by
  let d := 1 + abs z.im + abs r.im
  let h := Real.pi / d
  have hd : 0 < d := by dsimp [d]; linarith [abs_nonneg z.im, abs_nonneg r.im]
  have hh : 0 < h := div_pos Real.pi_pos hd
  have hProduct : h * d = Real.pi :=
    ((div_eq_iff (ne_of_gt hd)).mp (show Real.pi / d = h from rfl)).symm
  have him (w : Complex) (hw : abs w.im < d) :
      abs (((h : Complex) * w).im) < Real.pi := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [abs_mul, abs_of_pos hh]
    exact (mul_lt_mul_of_pos_left hw hh).trans_eq hProduct
  have hz := abs_lt.mp (him z (by dsimp [d]; linarith [abs_nonneg r.im]))
  have hr := abs_lt.mp (him r (by dsimp [d]; linarith [abs_nonneg z.im]))
  refine Exists.intro h (And.intro hh ?_)
  intro he
  have hEq := Complex.exp_inj_of_neg_pi_lt_of_le_pi hz.1 hz.2.le hr.1 hr.2.le he
  have hProd : (h : Complex) * (z - r) = 0 := by rw [mul_sub, hEq, sub_self]
  exact hNe (sub_eq_zero.mp ((mul_eq_zero.mp hProd).resolve_left
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hh))))

private theorem re_le_of_spectralTerm_bound
    (r : Complex) (a : Complex -> Complex) (ha : Not (a r = 0))
    (w M : Real)
    (hb : forall t : Real, 0 <= t ->
      norm (spectralTerm a t r) <= M * Real.exp (w * t)) :
    r.re <= w := by
  apply le_of_not_gt
  intro hTooLarge
  let A := norm (a r)
  let B := M / A
  let d := r.re - w
  have hA : 0 < A := norm_pos_iff.mpr ha
  have hd : 0 < d := sub_pos.mpr hTooLarge
  have hAtZero : A <= M := by
    simpa [spectralTerm, A] using hb 0 le_rfl
  have hB : 1 <= B := by
    calc
      1 = A / A := (div_self (ne_of_gt hA)).symm
      _ <= M / A := div_le_div_of_nonneg_right hAtZero hA.le
  let t := (Real.log B + 1) / d
  have ht : 0 <= t := div_nonneg (by linarith [Real.log_nonneg hB]) hd.le
  have hExponent : Real.exp (t * r.re) = Real.exp (d * t) * Real.exp (w * t) := by
    rw [<- Real.exp_add]
    congr 1
    dsimp [d]
    ring
  have h := hb t ht
  simp only [spectralTerm, Complex.norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  change A * Real.exp (t * r.re) <= _ at h
  rw [hExponent, <- mul_assoc] at h
  have hMul : A * Real.exp (d * t) <= M := le_of_mul_le_mul_right h (Real.exp_pos _)
  have hCancel : A * B = M := by
    rw [mul_comm]
    exact ((div_eq_iff (ne_of_gt hA)).mp (show M / A = B from rfl)).symm
  have hUpper : Real.exp (d * t) <= B := by
    apply le_of_mul_le_mul_left _ hA
    rw [hCancel]
    exact hMul
  have hdt : d * t = Real.log B + 1 := by
    rw [mul_comm]
    exact ((div_eq_iff (ne_of_gt hd)).mp (show (Real.log B + 1) / d = t from rfl)).symm
  have hLower : B < Real.exp (d * t) := by
    rw [hdt]
    calc
      B = Real.exp (Real.log B) := (Real.exp_log (zero_lt_one.trans_le hB)).symm
      _ < _ := Real.exp_lt_exp.mpr (lt_add_of_pos_right _ zero_lt_one)
  exact (not_lt_of_ge hUpper) hLower

/-- A nonzero exponential term cannot be hidden by finitely many other
frequencies in a bound along the positive real ray. -/
private theorem re_le_of_groupedFiniteSpectrum_bound
    (S : Finset Complex) (r : Complex) (hr : Not (Membership.mem S r))
    (a : Complex -> Complex) (ha : Not (a r = 0))
    (w M : Real) (hM : 0 <= M)
    (hBound : forall t : Real, 0 <= t ->
      norm (spectralTerm a t r + S.sum (spectralTerm a t)) <= M * Real.exp (w * t)) :
    r.re <= w := by
  classical
  induction S using Finset.induction_on generalizing a M with
  | empty =>
    apply re_le_of_spectralTerm_bound r a ha w M
    intro t ht
    simpa only [Finset.sum_empty, add_zero] using hBound t ht
  | @insert z S hz ih =>
    have hrz : Not (r = z) := fun h => hr (Finset.mem_insert.mpr (Or.inl h))
    have hrS : Not (Membership.mem S r) :=
      fun h => hr (Finset.mem_insert.mpr (Or.inr h))
    choose h hh using exists_positive_exp_shift_ne hrz
    let D := Complex.exp ((h : Complex) * z)
    let b (u : Complex) := a u * (Complex.exp ((h : Complex) * u) - D)
    let N := M * Real.exp (w * h) + norm D * M
    have hb : Not (b r = 0) := mul_ne_zero ha (sub_ne_zero.mpr hh.2)
    have hN : 0 <= N := add_nonneg (mul_nonneg hM (Real.exp_pos _).le)
      (mul_nonneg (norm_nonneg D) hM)
    apply ih hrS b hb N hN
    intro t ht
    have hTerm (u : Complex) :
        spectralTerm b t u = spectralTerm a (t + h) u - D * spectralTerm a t u := by
      dsimp [spectralTerm, b]
      rw [Complex.ofReal_add, add_mul, Complex.exp_add]
      ring
    have hAtZ : spectralTerm a (t + h) z = D * spectralTerm a t z := by
      have htZ := hTerm z
      change a z * (D - D) * Complex.exp ((t : Complex) * z) = _ at htZ
      simp only [sub_self, mul_zero, zero_mul] at htZ
      exact sub_eq_zero.mp htZ.symm
    let P (v : Real) : Complex := spectralTerm a v r + (insert z S).sum (spectralTerm a v)
    have hCombine : spectralTerm b t r + S.sum (spectralTerm b t) =
        P (t + h) - D * P t := by
      simp only [hTerm, P, Finset.sum_insert hz, Finset.sum_sub_distrib, <- Finset.mul_sum]
      rw [hAtZ]
      ring
    have htH : 0 <= t + h := add_nonneg ht hh.1.le
    calc
      _ = norm (P (t + h) - D * P t) := congrArg norm hCombine
      _ <= norm (P (t + h)) + norm (D * P t) := norm_sub_le _ _
      _ <= M * Real.exp (w * (t + h)) + norm D * (M * Real.exp (w * t)) := by
        rw [Complex.norm_mul]
        exact add_le_add (hBound (t + h) htH)
          (mul_le_mul_of_nonneg_left (hBound t ht) (norm_nonneg D))
      _ = N * Real.exp (w * t) := by
        rw [show w * (t + h) = w * t + w * h by ring, Real.exp_add]
        dsimp [N]
        ring

private theorem re_le_of_finiteSpectrum_bound
    (S : Finset Complex) (r : Complex) (hr : Membership.mem S r)
    (a : Complex -> Complex) (ha : Not (a r = 0))
    (w M : Real) (hM : 0 <= M)
    (hBound : forall t : Real, 0 <= t ->
      norm (S.sum (spectralTerm a t)) <= M * Real.exp (w * t)) :
    r.re <= w := by
  classical
  have hEr : Not (Membership.mem (S.erase r) r) := Finset.notMem_erase r S
  apply re_le_of_groupedFiniteSpectrum_bound (S.erase r) r hEr a ha w M hM
  intro t ht
  rw [<- Finset.sum_insert hEr, Finset.insert_erase hr]
  exact hBound t ht

/-- The zeros of an admissible function in a compact set form a finite set. -/
theorem URHAdmissible.finite_zerosOnCompact
    {F : Complex -> Complex} (h : URHAdmissible F)
    {K : Set Complex} (hK : IsCompact K) :
    Set.Finite {z : Complex | Membership.mem K z /\ F z = 0} := by
  let Z : Set Complex := {z : Complex | Membership.mem K z /\ F z = 0}
  have hClosed : IsClosed {z : Complex | F z = 0} :=
    isClosed_eq h.continuous continuous_const
  have hCompact : IsCompact Z := hK.inter_right hClosed
  apply hCompact.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro z hz
  have hz0 : F z = 0 := hz.2
  choose r hr using h.isolated_zeros z hz0
  refine Exists.intro (Metric.ball z r) (And.intro Metric.isOpen_ball ?_)
  ext y
  constructor
  next =>
    intro hy
    exact Set.mem_singleton_iff.mpr (hr.2 y (Metric.mem_ball.mp hy.1) hy.2.2)
  next =>
    intro hy
    have he := Set.mem_singleton_iff.mp hy
    subst y
    exact And.intro (Metric.mem_ball_self hr.1) hz

/-- Distinct zeros in the closed disk of radius `R` centered at zero. -/
noncomputable def URHAdmissible.zerosInDisk
    {F : Complex -> Complex} (h : URHAdmissible F) (R : Real) : Finset Complex :=
  (h.finite_zerosOnCompact (isCompact_closedBall (0 : Complex) R)).toFinset

private theorem mem_zerosInDisk
    {F : Complex -> Complex} (h : URHAdmissible F) {R : Real} {z : Complex} :
    Membership.mem (h.zerosInDisk R) z <-> dist z 0 <= R /\ F z = 0 := by
  classical
  simp only [URHAdmissible.zerosInDisk, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    Metric.mem_closedBall]

/-- The whole-disk triangular test, expressed with the factor
`exp (c * t)` moved to the right of the inequality. -/
def DiskTriangularZeroBound
    {F : Complex -> Complex} (h : URHAdmissible F) (c : Real) : Prop :=
  Not (F ((c + 1 : Real) : Complex) = 0) /\
    Not (F ((c + 2 : Real) : Complex) = 0) /\
    (forall R t : Real, norm ((h.zerosInDisk R).sum
        (fun z => triangularZeroWeight c 0 z * Complex.exp ((t : Complex) * z))) <=
      (h.zerosInDisk R).sum (fun z => norm (triangularZeroWeight c 0 z)) * Real.exp (c * t))

/-- On the full URH domain it is enough to test the grouped series in
each closed disk. Cancellations among zeros in a disk cannot hide an
off-line zero. -/
theorem universalRiemannHypothesisAt_iff_diskTriangularZeroBound
    {F : Complex -> Complex} (h : URHAdmissible F) (c : Real) :
    UniversalRiemannHypothesisAt F c <-> DiskTriangularZeroBound h c := by
  classical
  let a := triangularZeroWeight c 0
  constructor
  next =>
    intro hLine
    have hFinite := (universalRiemannHypothesisAt_iff_finiteTriangularZeroBound F c).mp hLine
    refine And.intro (by simpa only [add_zero] using hFinite.2.1)
      (And.intro (by simpa only [add_zero] using hFinite.2.2.1) ?_)
    intro R t
    let Z := h.zerosInDisk R
    change norm (Z.sum (spectralTerm a t)) <= (Z.sum fun z => norm (a z)) * Real.exp (c * t)
    calc
      _ <= Z.sum (fun z => norm (spectralTerm a t z)) := norm_sum_le Z _
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro z hz
        have hz0 := (mem_zerosInDisk h).mp hz
        simp only [spectralTerm, Complex.norm_mul, Complex.norm_exp, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hLine.2 z hz0.2, mul_comm t c]
  next =>
    intro hDisk
    refine And.intro h ?_
    intro z hz
    let R := dist z 0
    let Z := h.zerosInDisk R
    have hMem : Membership.mem Z z := (mem_zerosInDisk h).mpr (And.intro le_rfl hz)
    let M := Z.sum (fun y => norm (a y))
    have hM : 0 <= M := Finset.sum_nonneg (fun y _ => norm_nonneg (a y))
    have hBound (t : Real) : norm (Z.sum (spectralTerm a t)) <= M * Real.exp (c * t) :=
      hDisk.2.2 R t
    have hAnchor1 : Not (z - ((c + 0 + 1 : Real) : Complex) = 0) := by
      intro he
      apply hDisk.1
      rw [<- add_zero c, <- sub_eq_zero.mp he]
      exact hz
    have hAnchor2 : Not (z - ((c + 0 + 2 : Real) : Complex) = 0) := by
      intro he
      apply hDisk.2.1
      rw [<- add_zero c, <- sub_eq_zero.mp he]
      exact hz
    have ha : Not (a z = 0) := inv_ne_zero (mul_ne_zero hAnchor1 hAnchor2)
    have hRight : z.re <= c :=
      re_le_of_finiteSpectrum_bound Z z hMem a ha c M hM (fun t _ => hBound t)
    let e : Function.Embedding Complex Complex := { toFun := Neg.neg, inj' := neg_injective }
    let Zneg := Z.map e
    let aneg (y : Complex) := a (-y)
    have hMemNeg : Membership.mem Zneg (-z) :=
      Finset.mem_map.mpr (Exists.intro z (And.intro hMem rfl))
    have hNe : Not (aneg (-z) = 0) := by simpa only [aneg, neg_neg] using ha
    have hBoundNeg (t : Real) : norm (Zneg.sum (spectralTerm aneg t)) <= M * Real.exp ((-c) * t) := by
      have hSumEq : Zneg.sum (spectralTerm aneg t) = Z.sum (spectralTerm a (-t)) := by
        change (Z.map e).sum (spectralTerm aneg t) = _
        rw [Finset.sum_map]
        apply Finset.sum_congr rfl
        intro y _
        change a (-(-y)) * Complex.exp ((t : Complex) * (-y)) =
          a y * Complex.exp (((-t : Real) : Complex) * y)
        rw [neg_neg, Complex.ofReal_neg, mul_neg, neg_mul]
      rw [hSumEq, show (-c) * t = c * (-t) by ring]
      exact hBound (-t)
    have hLeft : (-z).re <= -c :=
      re_le_of_finiteSpectrum_bound Zneg (-z) hMemNeg aneg hNe (-c) M hM (fun t _ => hBoundNeg t)
    rw [Complex.neg_re] at hLeft
    linarith

end Robin1984.GRH
