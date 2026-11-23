import DedekindZeta.ConeMellinBridge
import DedekindZeta.PerClass
import Mathlib.Analysis.Complex.RemovableSingularity
import Robin1984.GRH.AnalyticAssembly

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Theta-Mellin continuation of the Dedekind zeta function from its Dirichlet series.
- Formalization note: The pole-removed Dedekind zeta function on the positive half-plane.
- PROVENANCE-END
-/

/-!
# The pole-removed Dedekind zeta function on the positive half-plane

The per-class theta continuation gives the pole-removed function directly.
The finite class sum agrees with Mathlib's ideal Dirichlet series on its
absolute-convergence half-plane. The value at one is the class number
formula's positive residue.
-/

open Filter Set NumberField

namespace DedekindZeta

open ConeMellinBridge ConeRadialReduction MellinPrinciple

universe u

variable (K : Type u) [Field K] [NumberField K]

private theorem analyticAt_cpow_base_ne_zero {b s : Complex} {g : Complex -> Complex}
    (hb : Not (b = 0)) (hg : AnalyticAt Complex g s) :
    AnalyticAt Complex (fun z => b ^ (g z)) s := by
  have hLog : AnalyticAt Complex (fun z => Complex.log b * g z) s :=
    analyticAt_const.mul hg
  have hExp : AnalyticAt Complex (fun z => Complex.exp (Complex.log b * g z)) s :=
    analyticAt_cexp.comp (f := fun z => Complex.log b * g z) hLog
  exact hExp.congr (Filter.Eventually.of_forall (fun z =>
    (Complex.cpow_def_of_ne_zero hb (g z)).symm))

private noncomputable def classTail (a : Ideal (RingOfIntegers K)) (s : Complex) : Complex :=
  mellinTail (radialTheta K a) (radialThetaDual K a)
    (surfaceVolume K) (surfaceVolume K) (Inv.inv (Theta.covolume K a : Complex)) 1 s

private noncomputable def classPrefactor (a : Ideal (RingOfIntegers K)) (s : Complex) : Complex :=
  (1 / (Units.torsionOrder K : Complex)) * (Ideal.absNorm a : Complex) ^ s *
    ((abs (NumberField.discr K) : Int) : Complex) ^ (s / 2)

private noncomputable def poleFreeCompletedClass (a : Ideal (RingOfIntegers K))
    (s : Complex) : Complex :=
  classPrefactor K a s *
    ((s - 1) * (-(surfaceVolume K : Complex) / s + classTail K a s) +
      Inv.inv (Theta.covolume K a : Complex) * (surfaceVolume K : Complex))

/-- The class sum with the pole at one removed, divided by its completion factor. -/
noncomputable def poleFreeDedekindZeta (s : Complex) : Complex :=
  (Finset.univ.sum (fun c : ClassGroup (RingOfIntegers K) =>
    poleFreeCompletedClass K (idealClassRep K c) s)) / ZInfty K s

private theorem classRep_nonzero (c : ClassGroup (RingOfIntegers K)) :
    Not (idealClassRep K c = 0) :=
  mem_nonZeroDivisors_iff_ne_zero.mp (Function.surjInv ClassGroup.mk0_surjective c).property

private theorem analyticAt_classPrefactor (c : ClassGroup (RingOfIntegers K)) (s : Complex) :
    AnalyticAt Complex (classPrefactor K (idealClassRep K c)) s := by
  let a := idealClassRep K c
  have haNormNat : Not (Ideal.absNorm a = 0) :=
    Ideal.absNorm_ne_zero_of_nonZeroDivisors (Function.surjInv ClassGroup.mk0_surjective c)
  have haNorm : Not ((Ideal.absNorm a : Complex) = 0) := by exact_mod_cast haNormNat
  have hDisc : Not (((abs (NumberField.discr K) : Int) : Complex) = 0) := by
    exact_mod_cast abs_ne_zero.mpr (NumberField.discr_ne_zero K)
  have hPowD : AnalyticAt Complex (fun z : Complex =>
      ((abs (NumberField.discr K) : Int) : Complex) ^ (z / 2)) s :=
    analyticAt_cpow_base_ne_zero hDisc
      (analyticAt_id.div analyticAt_const (by norm_num : Not ((2 : Complex) = 0)))
  exact (analyticAt_const.mul (analyticAt_cpow_base_ne_zero haNorm analyticAt_id)).mul hPowD

private theorem analyticAt_classTail (c : ClassGroup (RingOfIntegers K)) (s : Complex) :
    AnalyticAt Complex (classTail K (idealClassRep K c)) s := by
  choose d alpha hPair using
    exists_isMellinPair_radialTheta (K := K) (idealClassRep K c) (classRep_nonzero K c)
  unfold classTail
  exact mellinTail_analyticOn hPair s (mem_univ s)

private theorem analyticAt_poleFreeCompletedClass (c : ClassGroup (RingOfIntegers K))
    {s : Complex} (hs : 0 < s.re) :
    AnalyticAt Complex (poleFreeCompletedClass K (idealClassRep K c)) s := by
  have hRegular : AnalyticAt Complex (fun z : Complex =>
      -(surfaceVolume K : Complex) / z + classTail K (idealClassRep K c) z) s :=
    (analyticAt_const.div analyticAt_id (Complex.ne_zero_of_re_pos hs)).add
      (analyticAt_classTail K c s)
  exact (analyticAt_classPrefactor K c s).mul
    (((analyticAt_id.sub analyticAt_const).mul hRegular).add analyticAt_const)

/-- The pole-removed Dedekind function is analytic throughout the positive half-plane. -/
theorem analyticAt_poleFreeDedekindZeta {s : Complex} (hs : 0 < s.re) :
    AnalyticAt Complex (poleFreeDedekindZeta K) s := by
  have hSum : AnalyticAt Complex (fun z : Complex =>
      Finset.univ.sum (fun c : ClassGroup (RingOfIntegers K) =>
        poleFreeCompletedClass K (idealClassRep K c) z)) s :=
    Finset.analyticAt_fun_sum Finset.univ (fun c _ => analyticAt_poleFreeCompletedClass K c hs)
  exact hSum.div (analyticAt_ZInfty_of_re_pos K hs) (ZInfty_ne_zero_of_re_pos K hs)

private theorem poleFreeCompletedClass_eq (c : ClassGroup (RingOfIntegers K))
    {s : Complex} (hs : 1 < s.re) :
    poleFreeCompletedClass K (idealClassRep K c) s =
      (s - 1) * completedPartialZeta K (idealClassRep K c) s := by
  have hOne : Not (s - 1 = 0) := Complex.ne_zero_of_re_pos (by
    rw [Complex.sub_re, Complex.one_re]
    exact sub_pos.mpr hs)
  unfold poleFreeCompletedClass classPrefactor classTail
  rw [completedPartialZeta_eq_conePolarCorrection_add_tail (K := K) _ (classRep_nonzero K c) hs]
  simp only [conePolarCorrection]
  field_simp [hOne]
  ring

/-- Agreement with Mathlib's ideal Dirichlet series on its convergence half-plane. -/
theorem poleFreeDedekindZeta_eq {s : Complex} (hs : 1 < s.re) :
    poleFreeDedekindZeta K s = (s - 1) * NumberField.dedekindZeta K s := by
  unfold poleFreeDedekindZeta
  simp_rw [poleFreeCompletedClass_eq K _ hs]
  rw [<- Finset.mul_sum]
  change ((s - 1) * completedDedekindZeta K s) / ZInfty K s = _
  rw [completedDedekindZeta_eq K hs]
  field_simp [ZInfty_ne_zero_of_re_pos K (zero_lt_one.trans hs)]

/-- The value at one is the positive residue in Mathlib's class number formula. -/
theorem poleFreeDedekindZeta_one :
    poleFreeDedekindZeta K 1 = (NumberField.dedekindZeta_residue K : Complex) := by
  let l := nhdsWithin (1 : Real) (Ioi 1)
  have hFilter : l <= nhds (1 : Real) := nhdsWithin_le_nhds
  have hCont := (analyticAt_poleFreeDedekindZeta K (by norm_num : 0 < (1 : Complex).re)).continuousAt
  have hCastCont : ContinuousAt (poleFreeDedekindZeta K) ((1 : Real) : Complex) := by
    simpa only [Complex.ofReal_one] using hCont
  have hCast : ContinuousAt (fun x : Real => (x : Complex)) 1 :=
    Complex.continuous_ofReal.continuousAt
  have hLeft : Tendsto (fun x : Real => poleFreeDedekindZeta K (x : Complex)) l
      (nhds (poleFreeDedekindZeta K 1)) := by
    simpa only [Complex.ofReal_one, Function.comp_def] using
      (hCastCont.comp hCast).tendsto.mono_left hFilter
  have hRight : Filter.Eventually (fun x : Real => 1 < x) l := self_mem_nhdsWithin
  have hAgreement : Filter.EventuallyEq l (fun x : Real => (x - 1) *
      NumberField.dedekindZeta K (x : Complex)) (fun x : Real => poleFreeDedekindZeta K (x : Complex)) :=
    hRight.mono (fun x hx => (poleFreeDedekindZeta_eq K
      (by simpa only [Complex.ofReal_re] using hx)).symm)
  exact tendsto_nhds_unique hLeft
    ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' hAgreement)

private noncomputable def reciprocalCompletion (s : Complex) : Complex :=
  Inv.inv (ZInfty K s)

private theorem analyticAt_reciprocalCompletion_slope (s : Complex) :
    AnalyticAt Complex (dslope (reciprocalCompletion K) 0) s := by
  have hDiff : DifferentiableOn Complex (reciprocalCompletion K) (Set.univ : Set Complex) :=
    fun z _ => (analyticAt_invZInfty K z).differentiableAt.differentiableWithinAt
  have hSlopeDiff : DifferentiableOn Complex (dslope (reciprocalCompletion K) 0)
      (Set.univ : Set Complex) :=
    (Complex.differentiableOn_dslope
      (Filter.univ_mem : Membership.mem (nhds (0 : Complex)) Set.univ)).mpr hDiff
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Filter.Eventually.of_forall
    (fun z => (hSlopeDiff z (mem_univ z)).differentiableAt Filter.univ_mem)

private noncomputable def entireClassContribution (a : Ideal (RingOfIntegers K)) (s : Complex) :
    Complex :=
  classPrefactor K a s *
    ((s - 1) * (-(surfaceVolume K : Complex) * dslope (reciprocalCompletion K) 0 s +
      reciprocalCompletion K s * classTail K a s) +
      Inv.inv (Theta.covolume K a : Complex) * (surfaceVolume K : Complex) *
        reciprocalCompletion K s)

/-- The entire pole-removed Dedekind function includes the removable point at zero. -/
noncomputable def entirePoleFreeDedekindZeta (s : Complex) : Complex :=
  Finset.univ.sum (fun c : ClassGroup (RingOfIntegers K) =>
    entireClassContribution K (idealClassRep K c) s)

/-- Analyticity holds at every complex point, including zero. -/
theorem analyticAt_entirePoleFreeDedekindZeta (s : Complex) :
    AnalyticAt Complex (entirePoleFreeDedekindZeta K) s := by
  apply Finset.analyticAt_fun_sum
  intro c _
  let a := idealClassRep K c
  have hInverse : AnalyticAt Complex (reciprocalCompletion K) s := analyticAt_invZInfty K s
  have hRegular : AnalyticAt Complex (fun z : Complex =>
      -(surfaceVolume K : Complex) * dslope (reciprocalCompletion K) 0 z +
        reciprocalCompletion K z * classTail K a z) s :=
    (analyticAt_const.mul (analyticAt_reciprocalCompletion_slope K s)).add
      (hInverse.mul (analyticAt_classTail K c s))
  have hResidue : AnalyticAt Complex (fun z : Complex =>
      Inv.inv (Theta.covolume K a : Complex) * (surfaceVolume K : Complex) *
        reciprocalCompletion K z) s :=
    analyticAt_const.mul hInverse
  exact (analyticAt_classPrefactor K c s).mul
    (((analyticAt_id.sub analyticAt_const).mul hRegular).add hResidue)

/-- The positive-half-plane formula agrees with the entire definition. -/
theorem entirePoleFreeDedekindZeta_eq_poleFree {s : Complex} (hs : 0 < s.re) :
    entirePoleFreeDedekindZeta K s = poleFreeDedekindZeta K s := by
  have hSlope : dslope (reciprocalCompletion K) 0 s = reciprocalCompletion K s / s := by
    rw [dslope_of_ne _ (Complex.ne_zero_of_re_pos hs), slope_def_field, sub_zero]
    rw [show reciprocalCompletion K 0 = 0 from invZInfty_zero K, sub_zero]
  unfold entirePoleFreeDedekindZeta poleFreeDedekindZeta
  rw [div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  unfold entireClassContribution poleFreeCompletedClass
  rw [hSlope]
  change _ = classPrefactor K (idealClassRep K c) s *
    ((s - 1) * (-(surfaceVolume K : Complex) / s + classTail K (idealClassRep K c) s) +
      Inv.inv (Theta.covolume K (idealClassRep K c) : Complex) * (surfaceVolume K : Complex)) *
      reciprocalCompletion K s
  ring

/-- The analytic continuation of Mathlib's Dedekind zeta series away from one. -/
noncomputable def dedekindZetaContinuation (s : Complex) : Complex :=
  entirePoleFreeDedekindZeta K s / (s - 1)

theorem analyticAt_dedekindZetaContinuation {s : Complex} (hs : Not (s = 1)) :
    AnalyticAt Complex (dedekindZetaContinuation K) s :=
  (analyticAt_entirePoleFreeDedekindZeta K s).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)

theorem dedekindZetaContinuation_eq_series {s : Complex} (hs : 1 < s.re) :
    dedekindZetaContinuation K s = NumberField.dedekindZeta K s := by
  have hsOne : Not (s - 1 = 0) := Complex.ne_zero_of_re_pos (by
    rw [Complex.sub_re, Complex.one_re]
    exact sub_pos.mpr hs)
  unfold dedekindZetaContinuation
  rw [entirePoleFreeDedekindZeta_eq_poleFree K (zero_lt_one.trans hs),
    poleFreeDedekindZeta_eq K hs]
  field_simp [hsOne]

end DedekindZeta
