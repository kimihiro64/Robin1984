import DedekindZeta.MellinPrinciple

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Mellin reflection identity for a theta function and its dual.
- Formalization note: Reflection for Mellin continuations of a dual pair.
- PROVENANCE-END
-/

/-!
# Reflection for Mellin continuations of a dual pair

This is the analytic reflection identity. In the Dedekind application
the dual radial theta function is then identified with the radial theta
function of an integral representative of the dual ideal class.
-/

open Filter MeasureTheory Set

namespace DedekindZeta.MellinPrinciple

private theorem mellinTail_eq_mul_swap (f g : Real -> Complex) (a b C : Complex)
    (k : Real) (s : Complex) (hC : Not (C = 0)) :
    mellinTail f g a b C k s =
      C * mellinTail g f b a (Inv.inv C) k ((k : Complex) - s) := by
  unfold mellinTail
  rw [<- integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  have hExp : (k : Complex) - ((k : Complex) - s) - 1 = s - 1 := by ring
  rw [hExp]
  field_simp [hC]
  ring

/-- Reflection exchanges the two Mellin transforms of a dual pair. -/
theorem mellinContinuation_eq_mul_swap (f g : Real -> Complex) (a b C : Complex)
    (k : Real) (s : Complex) (hC : Not (C = 0))
    (hs : Not (s = 0)) (hsk : Not (s = (k : Complex))) :
    mellinContinuation f g a b C k s =
      C * mellinContinuation g f b a (Inv.inv C) k ((k : Complex) - s) := by
  unfold mellinContinuation
  rw [mellinTail_eq_mul_swap f g a b C k s hC]
  have hExp : (k : Complex) - s - (k : Complex) = -s := by ring
  rw [hExp]
  have hsk' : Not (s - (k : Complex) = 0) := sub_ne_zero.mpr hsk
  have hks : Not ((k : Complex) - s = 0) := sub_ne_zero.mpr (Ne.symm hsk)
  field_simp [hC, hs, hsk', hks]
  ring

/-- The radial Mellin continuation with its two simple poles cleared. -/
noncomputable def poleClearedMellin (f g : Real -> Complex) (a C : Complex)
    (s : Complex) : Complex :=
  -a * (s - 1) + C * a * s + s * (s - 1) * mellinTail f g a a C 1 s

theorem analyticAt_poleClearedMellin {f g : Real -> Complex} {a C : Complex}
    {c alpha : Real} (h : IsMellinPair f g a a C 1 c alpha) (s : Complex) :
    AnalyticAt Complex (poleClearedMellin f g a C) s := by
  have hSub : AnalyticAt Complex (fun w : Complex => w - 1) s :=
    analyticAt_id.sub analyticAt_const
  have hTail := mellinTail_analyticOn h s (mem_univ s)
  have hRational : AnalyticAt Complex (fun w : Complex => -a * (w - 1) + C * a * w) s :=
    (analyticAt_const.mul hSub).add (analyticAt_const.mul analyticAt_id)
  exact hRational.add ((analyticAt_id.mul hSub).mul hTail)

theorem poleClearedMellin_eq {f g : Real -> Complex} {a C s : Complex}
    (hs0 : Not (s = 0)) (hs1 : Not (s - 1 = 0)) :
    poleClearedMellin f g a C s = s * (s - 1) * mellinContinuation f g a a C 1 s := by
  unfold poleClearedMellin mellinContinuation
  rw [Complex.ofReal_one]
  field_simp [hs0, hs1]

private theorem analyticAt_mellinDilation {d : Real} (hd : 0 < d) (s : Complex) :
    AnalyticAt Complex (fun w : Complex => (d : Complex) ^ (-w)) s := by
  have hExp : AnalyticAt Complex (fun w : Complex => Complex.exp (Complex.log (d : Complex) * -w)) s :=
    analyticAt_cexp.comp (f := fun w : Complex => Complex.log (d : Complex) * -w)
      (analyticAt_const.mul analyticAt_id.neg)
  have hd0 : Not ((d : Complex) = 0) := Complex.ofReal_ne_zero.mpr hd.ne'
  exact hExp.congr (Filter.Eventually.of_forall (fun w =>
    (Complex.cpow_def_of_ne_zero hd0 (-w)).symm))

/-- A dilation of the positive radial argument gives the corresponding
power factor throughout the common domain of the continuations. -/
theorem mellinContinuation_dilation {f g F G : Real -> Complex} {a C D : Complex}
    {c alpha c' alpha' d : Real}
    (hFirst : IsMellinPair f g a a C 1 c alpha)
    (hSecond : IsMellinPair F G a a D 1 c' alpha') (hd : 0 < d)
    (hScale : forall y : Real, 0 < y -> f y = F (y * d))
    {s : Complex} (hs0 : Not (s = 0)) (hs1 : Not (s - 1 = 0)) :
    mellinContinuation f g a a C 1 s =
      (d : Complex) ^ (-s) * mellinContinuation F G a a D 1 s := by
  let L := poleClearedMellin f g a C
  let R := fun w : Complex => (d : Complex) ^ (-w) * poleClearedMellin F G a D w
  have hL : AnalyticOnNhd Complex L Set.univ :=
    fun w _ => analyticAt_poleClearedMellin hFirst w
  have hR : AnalyticOnNhd Complex R Set.univ :=
    fun w _ => (analyticAt_mellinDilation hd w).mul (analyticAt_poleClearedMellin hSecond w)
  have hMellin (w : Complex) : reducedMellin f a w =
      (d : Complex) ^ (-w) * reducedMellin F a w := by
    have hChange : reducedMellin f a w = mellin (fun y : Real => F (y * d) - a) w := by
      unfold reducedMellin mellin
      exact setIntegral_congr_fun measurableSet_Ioi (fun y hy => by simp only [hScale y hy])
    rw [hChange]
    simpa only [smul_eq_mul, reducedMellin] using
      mellin_comp_mul_right (fun y : Real => F y - a) w hd
  have hNear : Filter.Eventually (fun w : Complex => 1 < w.re) (nhds (2 : Complex)) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hInitial : Filter.EventuallyEq (nhds (2 : Complex)) L R := by
    filter_upwards [hNear] with w hw
    have hw0 : Not (w = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hw)
    have hw1 : Not (w - 1 = 0) := Complex.ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re]
      exact sub_pos.mpr hw)
    change poleClearedMellin f g a C w =
      (d : Complex) ^ (-w) * poleClearedMellin F G a D w
    rw [poleClearedMellin_eq hw0 hw1, poleClearedMellin_eq hw0 hw1,
      mellinContinuation_eq hFirst hw, mellinContinuation_eq hSecond hw, hMellin]
    ring
  have hGlobal : EqOn L R Set.univ :=
    hL.eqOn_of_preconnected_of_eventuallyEq hR isPreconnected_univ (mem_univ (2 : Complex)) hInitial
  have hAt := hGlobal (mem_univ s)
  change poleClearedMellin f g a C s =
    (d : Complex) ^ (-s) * poleClearedMellin F G a D s at hAt
  rw [poleClearedMellin_eq hs0 hs1, poleClearedMellin_eq hs0 hs1] at hAt
  have hDen := mul_ne_zero hs0 hs1
  calc
    _ = (s * (s - 1) * mellinContinuation f g a a C 1 s) / (s * (s - 1)) := by
      field_simp [hDen]
    _ = ((d : Complex) ^ (-s) * (s * (s - 1) * mellinContinuation F G a a D 1 s)) /
        (s * (s - 1)) := by rw [hAt]
    _ = _ := by field_simp [hDen]

end DedekindZeta.MellinPrinciple
