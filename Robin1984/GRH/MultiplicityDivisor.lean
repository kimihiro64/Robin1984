import Robin1984.GRH.MultiplicityExpansion
import Robin1984.GRH.TriangularHadamard

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Repeated Hadamard divisors and restriction of the zero series to the critical line.
- Formalization note: The occurrence index retains analytic orders, so injectivity of its ordinate map detects simple zeros.
- PROVENANCE-END
-/

/-!
# Critical-line zero occurrences

The repeated Hadamard divisor records one occurrence for each unit of
analytic order. Its restriction to the critical line supplies the
frequencies and weights in the global multiplicity criterion.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Complex.Hadamard Set
open scoped Classical

/-- The divisor index retains one occurrence per order at each critical-line zero. -/
abbrev criticalHadamardOccurrence (F : Complex -> Complex) :=
  Subtype (fun i : regularHadamardZeroIndex F => (regularHadamardZero i).re = 1 / 2)

/-- The ordinate of an occurrence in the critical-line divisor. -/
def criticalHadamardOrdinate {F : Complex -> Complex}
    (i : criticalHadamardOccurrence F) : Real :=
  (regularHadamardZero i.val).im

private theorem divisorOrder_toNat_eq_analyticOrderNatAt
    {F : Complex -> Complex} (hF : Differentiable Complex F) (z : Complex) :
    Int.toNat (MeromorphicOn.divisor F (univ : Set Complex) z) = analyticOrderNatAt F z := by
  have hAn : AnalyticOnNhd Complex F univ := fun w _ => hF.analyticAt w
  rw [MeromorphicOn.divisor_apply hAn.meromorphicOn (mem_univ z),
    (hF.analyticAt z).meromorphicOrderAt_eq]
  unfold analyticOrderNatAt
  cases h : analyticOrderAt F z <;> simp

private def criticalOccurrenceFromFin {F : Complex -> Complex} {z : Complex}
    (hz : z.re = 1 / 2) (j : Fin (Int.toNat (MeromorphicOn.divisor F (univ : Set Complex) z))) :
    criticalHadamardOccurrence F := by
  have hz0 : Not (z = 0) := Complex.ne_zero_of_re_pos (by rw [hz]; norm_num)
  have hz1 : Not (z + 1 = 0) := Complex.ne_zero_of_re_pos (by
    rw [Complex.add_re, Complex.one_re, hz]
    norm_num)
  let s : divisorZeroIndex F univ := Sigma.mk z j
  let t : entireNonzeroZeroIndex F := Subtype.mk s hz0
  let u : regularHadamardZeroIndex F := Subtype.mk t hz1
  exact Subtype.mk u hz

/-- The repeated divisor uses a single occurrence per ordinate exactly
when every critical-line zero has analytic order at most one. -/
theorem injective_criticalHadamardOrdinate_iff {F : Complex -> Complex}
    (hF : Differentiable Complex F) :
    Function.Injective (criticalHadamardOrdinate (F := F)) <->
      forall z : Complex, z.re = 1 / 2 -> F z = 0 -> analyticOrderNatAt F z <= 1 := by
  constructor
  case mp =>
    intro h z hRe hZ
    by_contra hOrd
    have hBound : 1 < Int.toNat (MeromorphicOn.divisor F univ z) := by
      rw [divisorOrder_toNat_eq_analyticOrderNatAt hF z]
      exact lt_of_not_ge hOrd
    let a : Fin (Int.toNat (MeromorphicOn.divisor F univ z)) :=
      Fin.mk 0 (Nat.lt_of_succ_lt hBound)
    let b : Fin (Int.toNat (MeromorphicOn.divisor F univ z)) := Fin.mk 1 hBound
    have hEq : criticalOccurrenceFromFin hRe a = criticalOccurrenceFromFin hRe b :=
      h (show criticalHadamardOrdinate (criticalOccurrenceFromFin hRe a) =
        criticalHadamardOrdinate (criticalOccurrenceFromFin hRe b) from rfl)
    have hNat : (0 : Nat) = 1 :=
      congrArg (fun i : criticalHadamardOccurrence F => i.val.val.val.2.val) hEq
    exact Nat.zero_ne_one hNat
  case mpr =>
    intro h i j hIm
    have hEqualZero : regularHadamardZero i.val = regularHadamardZero j.val :=
      Complex.ext (i.property.trans j.property.symm) hIm
    have hFiber {p q : divisorZeroIndex F univ} (hPQ : p.1 = q.1)
        (hRe : p.1.re = 1 / 2) (hZero : F p.1 = 0) : p = q := by
      cases p with
      | mk z k =>
        cases q with
        | mk w l =>
          change z = w at hPQ
          subst w
          have hCap : Int.toNat (MeromorphicOn.divisor F univ z) <= 1 := by
            rw [divisorOrder_toNat_eq_analyticOrderNatAt hF z]
            exact h z hRe hZero
          have hkl : k = l := Fin.ext (by
            have hk := k.isLt
            have hl := l.isLt
            omega)
          rw [hkl]
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hFiber hEqualZero i.property (entireNonzeroZero_is_zero hF i.val.val)

private theorem regularHadamardZero_eq_on_criticalLine {F : Complex -> Complex}
    (i : criticalHadamardOccurrence F) :
    regularHadamardZero i.val = (1 / 2 : Complex) +
      (criticalHadamardOrdinate i : Complex) * Complex.I := by
  exact Complex.ext
    (by simpa [Complex.add_re, Complex.mul_re, Complex.div_re] using i.property)
    (by simp [criticalHadamardOrdinate, Complex.add_im, Complex.mul_im])

/-- Restricting the surviving terms to the critical-line divisor turns
the normalized triangular series into its pure frequency expansion. -/
theorem tsum_triangularCriticalSpectrumTerm_eq_occurrenceSeries {F : Complex -> Complex}
    (t : Real) :
    tsum (fun i : regularHadamardZeroIndex F => triangularCriticalSpectrumTerm
      (regularHadamardZero i) t) =
      tsum (fun i : criticalHadamardOccurrence F =>
        Inv.inv (((1 / 2 : Complex) + (criticalHadamardOrdinate i : Complex) * Complex.I) *
          ((3 / 2 : Complex) + (criticalHadamardOrdinate i : Complex) * Complex.I)) *
          Complex.exp ((criticalHadamardOrdinate i : Complex) * Complex.I * (t : Complex))) := by
  let S : Set (regularHadamardZeroIndex F) := {i | (regularHadamardZero i).re = 1 / 2}
  let W (i : regularHadamardZeroIndex F) : Complex :=
    Complex.exp ((regularHadamardZero i - 1 / 2) * (t : Complex)) /
      (regularHadamardZero i * (regularHadamardZero i + 1))
  have hInd : (fun i : regularHadamardZeroIndex F =>
      triangularCriticalSpectrumTerm (regularHadamardZero i) t) = S.indicator W := by
    funext i
    unfold triangularCriticalSpectrumTerm
    simp only [Set.indicator_apply, S, Set.mem_ofPred_eq, W]
  rw [hInd, <- tsum_subtype]
  refine tsum_congr ?_
  intro i
  unfold W
  let c : Complex := (criticalHadamardOrdinate i : Complex) * Complex.I
  have hz := regularHadamardZero_eq_on_criticalLine i
  change regularHadamardZero i.val = (1 / 2 : Complex) + c at hz
  rw [hz, show (1 / 2 : Complex) + c - 1 / 2 = c by ring,
    show (1 / 2 : Complex) + c + 1 = 3 / 2 + c by ring]
  rw [div_eq_mul_inv, mul_comm]

/-- Restrict the summable Hadamard denominators to the critical line. -/
theorem summable_criticalHadamardOccurrence_denominator {F : Complex -> Complex}
    (hOrder : EntireOfOrderAtMost 1 F) (hNontrivial : exists z, Not (F z = 0)) :
    Summable (fun i : criticalHadamardOccurrence F => Inv.inv (norm
      (((1 / 2 : Complex) + (criticalHadamardOrdinate i : Complex) * Complex.I) *
        ((3 / 2 : Complex) + (criticalHadamardOrdinate i : Complex) * Complex.I)))) := by
  have h := (summable_regularHadamardZeroWeight hOrder hNontrivial).subtype
    (fun i => (regularHadamardZero i).re = 1 / 2)
  refine h.congr ?_
  intro i
  change (norm (regularHadamardZero i.val * (regularHadamardZero i.val + 1))) ^ (-1 : Int) = _
  simp only [zpow_neg_one]
  rw [regularHadamardZero_eq_on_criticalLine i,
    show (1 / 2 : Complex) + (criticalHadamardOrdinate i : Complex) * Complex.I + 1 =
      (3 / 2 : Complex) + (criticalHadamardOrdinate i : Complex) * Complex.I by ring]

/-- The Gaussian weights are summable whenever the corresponding canonical
triangular denominators are summable. -/
theorem summable_gaussian_criticalWeights {i : Type*} (gamma : i -> Real)
    (hWeight : Summable (fun j => Inv.inv (norm
      (((1 / 2 : Complex) + (gamma j : Complex) * Complex.I) *
        ((3 / 2 : Complex) + (gamma j : Complex) * Complex.I))))) :
    Summable (fun j => Real.exp (-(gamma j ^ 2))) := by
  refine Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le) ?_
    (hWeight.mul_left 5)
  intro j
  let g := gamma j
  let c : Complex := (g : Complex) * Complex.I
  let q : Complex := ((1 / 2 : Complex) + c) * ((3 / 2 : Complex) + c)
  have hc : 0 = c.re := by simp [c, Complex.mul_re]
  have hq : 0 < norm q := norm_pos_iff.mpr (mul_ne_zero
    (Complex.ne_zero_of_re_pos (by norm_num [Complex.add_re, Complex.div_re, <- hc]))
    (Complex.ne_zero_of_re_pos (by norm_num [Complex.add_re, Complex.div_re, <- hc])))
  have hNorm : norm c = abs g := by
    simp [c, Complex.norm_real, Real.norm_eq_abs]
  have hOne : norm ((1 / 2 : Complex) + c) <= (3 / 2 : Real) + abs g := by
    have h := norm_add_le (1 / 2 : Complex) c
    rw [hNorm] at h
    have hHalf : norm (1 / 2 : Complex) = (1 / 2 : Real) := by norm_num [norm_div]
    rw [hHalf] at h
    linarith only [h]
  have hTwo : norm ((3 / 2 : Complex) + c) <= (3 / 2 : Real) + abs g := by
    have h := norm_add_le (3 / 2 : Complex) c
    rw [hNorm] at h
    have hThree : norm (3 / 2 : Complex) = (3 / 2 : Real) := by norm_num [norm_div]
    rwa [hThree] at h
  have hQ : norm q <= 5 * (1 + g ^ 2) := by
    unfold q
    rw [norm_mul]
    have h := mul_le_mul hOne hTwo (norm_nonneg _) (by positivity : 0 <= (3 / 2 : Real) + abs g)
    have hs : (abs g) ^ 2 = g ^ 2 := sq_abs g
    have ht := sq_nonneg (abs g - 3 / 2)
    nlinarith only [h, hs, ht, sq_nonneg g]
  have hExp : (1 + g ^ 2) * Real.exp (-g ^ 2) <= 1 := by
    have he : 1 + g ^ 2 <= Real.exp (g ^ 2) := by
      simpa only [add_comm] using Real.add_one_le_exp (g ^ 2)
    have h := mul_le_mul_of_nonneg_right he (Real.exp_pos (-g ^ 2)).le
    rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    exact h
  have hMul : Real.exp (-g ^ 2) * norm q <= 5 := by
    calc
      _ <= Real.exp (-g ^ 2) * (5 * (1 + g ^ 2)) :=
        mul_le_mul_of_nonneg_left hQ (Real.exp_pos _).le
      _ = 5 * ((1 + g ^ 2) * Real.exp (-g ^ 2)) := by ring
      _ <= _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp (by norm_num : (0 : Real) <= 5)
  change Real.exp (-(g ^ 2)) <= 5 * Inv.inv (norm q)
  calc
    _ = (Real.exp (-g ^ 2) * norm q) * Inv.inv (norm q) := by
      rw [mul_assoc, <- div_eq_mul_inv, div_self hq.ne', mul_one]
    _ <= _ := mul_le_mul_of_nonneg_right hMul (inv_nonneg.mpr hq.le)

/-- The point on the critical line of a specified ordinate. -/
def multiplicityCriticalPoint (delta : Real) : Complex :=
  Complex.mk (1 / 2) delta

private def criticalOccurrencesAtEquiv {F : Complex -> Complex} (delta : Real) :
    Equiv (Fin (Int.toNat (MeromorphicOn.divisor F univ (multiplicityCriticalPoint delta))))
      {i : criticalHadamardOccurrence F // criticalHadamardOrdinate i = delta} := by
  let z := multiplicityCriticalPoint delta
  let n := Int.toNat (MeromorphicOn.divisor F univ z)
  have hz : z.re = 1 / 2 := rfl
  let f (j : Fin n) :
      {i : criticalHadamardOccurrence F // criticalHadamardOrdinate i = delta} :=
    Subtype.mk (criticalOccurrenceFromFin hz j) rfl
  apply Equiv.ofBijective f
  refine And.intro ?_ ?_
  case refine_1 =>
    intro j k hjk
    exact Fin.ext (congrArg (fun i : {i : criticalHadamardOccurrence F //
      criticalHadamardOrdinate i = delta} => i.val.val.val.val.2.val) hjk)
  case refine_2 =>
    intro p
    have hp : regularHadamardZero p.val.val = z := Complex.ext p.val.property p.property
    change p.val.val.val.val.1 = z at hp
    generalize hQ : p.val.val.val.val = q at hp
    cases q with
    | mk w j =>
      change w = z at hp
      subst w
      refine Exists.intro j ?_
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hQ.symm

/-- The complete contribution at an ordinate counts the order of that zero. -/
theorem criticalOccurrenceFiberSum_eq_order {F : Complex -> Complex}
    (hF : Differentiable Complex F) (delta : Real) (coeff : Real -> Complex) :
    tsum (fun i : criticalHadamardOccurrence F =>
      if criticalHadamardOrdinate i = delta then coeff (criticalHadamardOrdinate i) else 0) =
    (analyticOrderNatAt F (multiplicityCriticalPoint delta) : Complex) * coeff delta := by
  let S : Set (criticalHadamardOccurrence F) := {i | criticalHadamardOrdinate i = delta}
  have hIndicator : (fun i : criticalHadamardOccurrence F =>
      if criticalHadamardOrdinate i = delta then coeff (criticalHadamardOrdinate i) else 0) =
      S.indicator (fun i => coeff (criticalHadamardOrdinate i)) := by
    funext i
    rw [Set.indicator_apply]
    rfl
  rw [hIndicator, <- tsum_subtype]
  let e := criticalOccurrencesAtEquiv (F := F) delta
  let n := Int.toNat (MeromorphicOn.divisor F univ (multiplicityCriticalPoint delta))
  change tsum (fun i : {i : criticalHadamardOccurrence F // criticalHadamardOrdinate i = delta} =>
    coeff (criticalHadamardOrdinate i.val)) = _
  rw [<- e.tsum_eq]
  have hFun : (fun j : Fin n => coeff (criticalHadamardOrdinate (e j).val)) =
      fun _ => coeff delta := by
    funext j
    rw [(e j).property]
  rw [hFun, tsum_fintype, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [divisorOrder_toNat_eq_analyticOrderNatAt hF]

/-- Away from omitted ordinates, distinct zero occurrences have distinct
frequencies exactly when the corresponding analytic orders are at most one. -/
theorem injective_criticalHadamardOrdinate_outside_iff {F : Complex -> Complex}
    (hF : Differentiable Complex F) (E : Finset Real) :
    Function.Injective
      (fun i : {i : criticalHadamardOccurrence F // Not (Membership.mem E (criticalHadamardOrdinate i))} =>
        criticalHadamardOrdinate i.val) <->
      forall delta, Not (Membership.mem E delta) ->
        analyticOrderNatAt F (multiplicityCriticalPoint delta) <= 1 := by
  constructor
  case mp =>
    intro h delta hDelta
    by_contra hOrd
    let n := Int.toNat (MeromorphicOn.divisor F univ (multiplicityCriticalPoint delta))
    have hn : 1 < n := by
      unfold n
      rw [divisorOrder_toNat_eq_analyticOrderNatAt hF]
      exact lt_of_not_ge hOrd
    let e := criticalOccurrencesAtEquiv (F := F) delta
    let a : Fin n := Fin.mk 0 (Nat.lt_of_succ_lt hn)
    let b : Fin n := Fin.mk 1 hn
    have hOff (j : Fin n) : Not (Membership.mem E (criticalHadamardOrdinate (e j).val)) := by
      rw [(e j).property]
      exact hDelta
    have hSame := @h (Subtype.mk (e a).val (hOff a)) (Subtype.mk (e b).val (hOff b))
      ((e a).property.trans (e b).property.symm)
    have hVal : (e a).val = (e b).val := congrArg
      (fun p : {i : criticalHadamardOccurrence F //
        Not (Membership.mem E (criticalHadamardOrdinate i))} => p.val) hSame
    have hEq := e.injective (Subtype.ext hVal)
    exact Nat.zero_ne_one (congrArg Fin.val hEq)
  case mpr =>
    intro h i j hIj
    let delta := criticalHadamardOrdinate i.val
    let e := criticalOccurrencesAtEquiv (F := F) delta
    let a : {k : criticalHadamardOccurrence F // criticalHadamardOrdinate k = delta} :=
      Subtype.mk i.val rfl
    let b : {k : criticalHadamardOccurrence F // criticalHadamardOrdinate k = delta} :=
      Subtype.mk j.val hIj.symm
    have hN : Int.toNat (MeromorphicOn.divisor F univ (multiplicityCriticalPoint delta)) <= 1 := by
      rw [divisorOrder_toNat_eq_analyticOrderNatAt hF]
      exact h delta i.property
    have hFin : e.symm a = e.symm b := Fin.ext (by
      have ha := (e.symm a).isLt
      have hb := (e.symm b).isLt
      omega)
    have hFib := e.symm.injective hFin
    have hVal : a.val = b.val := congrArg Subtype.val hFib
    exact Subtype.ext hVal

end Robin1984.GRH
