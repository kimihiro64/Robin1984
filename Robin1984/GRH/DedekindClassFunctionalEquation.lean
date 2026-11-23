import Robin1984.GRH.DedekindClassNormalization
import Robin1984.GRH.DedekindClassSeries

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The classical classwise theta proof of the Dedekind functional equation.
- Formalization note: The functional equation for the completed Dedekind zeta function.
- PROVENANCE-END
-/

/-!
# The functional equation for the completed Dedekind zeta function

The per-class continuation is independent of the integral ideal chosen
to represent a class. The trace dual then permutes the classes in the
completed sum.
-/

open Filter NumberField Set Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

local notation "R" => RingOfIntegers K
local notation "F" => FractionalIdeal (nonZeroDivisors R) K
local notation "NZI" => (nonZeroDivisors (Ideal R))

omit [NumberField K] in
private theorem nonzeroIdeal_ne_zero (A : NZI) : Not (A.val = 0) :=
  mem_nonZeroDivisors_iff_ne_zero.mp A.property

/-- A completed partial zeta continuation depends only on the ideal class. -/
theorem completedIdealContinuation_eq_of_sameClass (A B : NZI)
    (hClass : ClassGroup.mk0 A = ClassGroup.mk0 B)
    {s : Complex} (hs0 : Not (s = 0)) (hs1 : Not (s = 1)) :
    completedIdealContinuation K A.val s = completedIdealContinuation K B.val s := by
  have ha := nonzeroIdeal_ne_zero K A
  have hb := nonzeroIdeal_ne_zero K B
  let L := completedIdealPoleCleared K A.val
  let T := completedIdealPoleCleared K B.val
  have hL : AnalyticOnNhd Complex L Set.univ :=
    fun z _ => analyticAt_completedIdealPoleCleared K A.val ha z
  have hT : AnalyticOnNhd Complex T Set.univ :=
    fun z _ => analyticAt_completedIdealPoleCleared K B.val hb z
  have hOpen : IsOpen {z : Complex | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hAtTwo : Membership.mem {z : Complex | 1 < z.re} (2 : Complex) := by
    change 1 < (2 : Complex).re
    norm_num
  have hNear : Filter.EventuallyEq (nhds (2 : Complex)) L T := by
    filter_upwards [hOpen.mem_nhds hAtTwo] with w hw
    change 1 < w.re at hw
    have hw0 : Not (w = 0) := by
      intro h
      rw [h, Complex.zero_re] at hw
      exact (not_lt_of_ge zero_le_one) hw
    have hw1 : Not (w = 1) := by
      intro h
      rw [h, Complex.one_re] at hw
      exact (lt_irrefl (1 : Real)) hw
    change completedIdealPoleCleared K A.val w = completedIdealPoleCleared K B.val w
    rw [completedIdealPoleCleared_eq K _ hw0 hw1, completedIdealPoleCleared_eq K _ hw0 hw1,
      completedIdealContinuation_eq_completedPartialZeta K A.val ha hw,
      completedIdealContinuation_eq_completedPartialZeta K B.val hb hw,
      completedPartialZeta_integralIdeal_eq K A hw, completedPartialZeta_integralIdeal_eq K B hw,
      hClass]
  have hGlobal : Set.EqOn L T Set.univ :=
    hL.eqOn_of_preconnected_of_eventuallyEq hT isPreconnected_univ
      (mem_univ (2 : Complex)) hNear
  have hAt : completedIdealPoleCleared K A.val s = completedIdealPoleCleared K B.val s :=
    hGlobal (mem_univ s)
  rw [completedIdealPoleCleared_eq K _ hs0 hs1, completedIdealPoleCleared_eq K _ hs0 hs1] at hAt
  have hCoef : Not (s * (s - 1) = 0) := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  have hDiff : s * (s - 1) * (completedIdealContinuation K A.val s -
      completedIdealContinuation K B.val s) = 0 := by
    rw [mul_sub, hAt, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hDiff).resolve_left hCoef)

private noncomputable def classIdeal (c : ClassGroup R) : NZI :=
  Function.surjInv ClassGroup.mk0_surjective c

private theorem mk0_classIdeal (c : ClassGroup R) : ClassGroup.mk0 (classIdeal K c) = c :=
  Function.surjInv_eq ClassGroup.mk0_surjective c

private noncomputable def differentNonzeroIdeal : NZI :=
  Subtype.mk (differentIdeal Int R) (mem_nonZeroDivisors_iff_ne_zero.mpr (by
    rw [Ideal.zero_eq_bot]
    exact differentIdeal_ne_bot))

private noncomputable def dualClassEquiv : Equiv (ClassGroup R) (ClassGroup R) where
  toFun c := Inv.inv (c * ClassGroup.mk0 (differentNonzeroIdeal K))
  invFun c := Inv.inv c * Inv.inv (ClassGroup.mk0 (differentNonzeroIdeal K))
  left_inv c := by simp [mul_assoc]
  right_inv c := by simp [mul_assoc]

private theorem reflect_class (c : ClassGroup R) {s : Complex}
    (hs0 : Not (s = 0)) (hs1 : Not (s = 1)) :
    completedIdealContinuation K (classIdeal K c).val s =
      completedIdealContinuation K (classIdeal K (dualClassEquiv K c)).val (1 - s) := by
  let A := classIdeal K c
  let D := differentNonzeroIdeal K
  have ha := nonzeroIdeal_ne_zero K A
  have hAF : Not ((A.val : F) = 0) := (FractionalIdeal.coeIdeal_ne_zero'
    (P := K) (S := nonZeroDivisors R) le_rfl).mpr (by simpa only [Ideal.zero_eq_bot] using ha)
  have hAD : Not (Theta.dualIdeal K A.val = 0) := by
    rw [<- Theta.dualIdeal_eq_dual]
    exact FractionalIdeal.dual_ne_zero Int Rat hAF
  choose m hm b hb hScaled using exists_integral_natural_multiple K (Theta.dualIdeal K A.val) hAD
  let B : NZI := Subtype.mk b (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
  have hProd : Submodule.IsPrincipal (B * (A * D)).val := by
    change Submodule.IsPrincipal (b * (A.val * differentIdeal Int R))
    rw [integral_dual_representative_mul K A.val b ha m hScaled]
    exact Submodule.IsPrincipal.mk (Exists.intro (m : R) rfl)
  have hClassProd : ClassGroup.mk0 (B * (A * D)) = 1 :=
    (ClassGroup.mk0_eq_one_iff (B * (A * D)).property).mpr hProd
  rw [map_mul, map_mul, show ClassGroup.mk0 A = c from mk0_classIdeal K c] at hClassProd
  have hClassB : ClassGroup.mk0 B = ClassGroup.mk0 (classIdeal K (dualClassEquiv K c)) := by
    rw [mk0_classIdeal]
    change ClassGroup.mk0 B = Inv.inv (c * ClassGroup.mk0 D)
    exact (eq_inv_iff_mul_eq_one).mpr hClassProd
  have h1s0 : Not ((1 : Complex) - s = 0) := sub_ne_zero.mpr (Ne.symm hs1)
  have h1s1 : Not ((1 : Complex) - s = 1) := by
    intro h
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 0 := by rw [h, sub_self]
  calc
    completedIdealContinuation K A.val s = completedIdealContinuation K B.val (1 - s) :=
      completedIdealContinuation_eq_dual K A.val b ha hb hm hScaled hs0 hs1
    _ = _ := completedIdealContinuation_eq_of_sameClass K B
      (classIdeal K (dualClassEquiv K c)) hClassB h1s0 h1s1

/-- The completed Dedekind zeta continuation as the sum over ideal classes. -/
noncomputable def completedDedekindContinuation (s : Complex) : Complex :=
  Finset.sum Finset.univ (fun c : ClassGroup R => completedIdealContinuation K (classIdeal K c).val s)

/-- The global functional equation results from reindexing by trace dual. -/
theorem completedDedekindContinuation_functionalEquation {s : Complex}
    (hs0 : Not (s = 0)) (hs1 : Not (s = 1)) :
    completedDedekindContinuation K s = completedDedekindContinuation K (1 - s) := by
  unfold completedDedekindContinuation
  calc
    _ = Finset.sum Finset.univ (fun c : ClassGroup R =>
        completedIdealContinuation K (classIdeal K (dualClassEquiv K c)).val (1 - s)) := by
      apply Finset.sum_congr rfl
      intro c _
      exact reflect_class K c hs0 hs1
    _ = _ := Equiv.sum_comp (dualClassEquiv K)
      (fun c : ClassGroup R => completedIdealContinuation K (classIdeal K c).val (1 - s))

/-- The continuation specializes to the original completed Dedekind
zeta on its half-plane of convergence. -/
theorem completedDedekindContinuation_eq_initial {s : Complex} (hs : 1 < s.re) :
    completedDedekindContinuation K s = ZInfty K s * dedekindZeta K s := by
  rw [<- completedDedekindZeta_eq K hs]
  unfold completedDedekindContinuation completedDedekindZeta
  apply Finset.sum_congr rfl
  intro c _
  exact completedIdealContinuation_eq_completedPartialZeta K (classIdeal K c).val
    (nonzeroIdeal_ne_zero K (classIdeal K c)) hs

end DedekindZeta
