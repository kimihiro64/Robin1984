import Mathlib.Tactic.Linarith
import Robin1984.GRH.DedekindDeLaValleePoussin
import Robin1984.GRH.LogDerivativeResidue

/-!
# Nonvanishing on the line of convergence

An analytic pole-cleared continuation of the Dedekind zeta series with
nonzero residue at one cannot vanish at any other point on the line.
The three-point inequality excludes the local orders that a zero would
force along horizontal approaches from the initial half-plane.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The de la Vallee Poussin proof of nonvanishing on the line of absolute convergence.
- Formalization note: Extract the integer order by a horizontal limit of the scaled logarithmic derivative and use the exact signed residues in the three-point inequality.
- PROVENANCE-END
-/

open Filter NumberField Set

namespace Robin1984.GRH

private abbrev rightAtOne : Filter Real := nhdsWithin 1 (Ioi 1)

private theorem tendsto_horizontal (t : Real) :
    Tendsto (fun x : Real => Complex.mk x t) rightAtOne (nhds (Complex.mk 1 t)) := by
  have hCont : Continuous (fun x : Real => Complex.mk x t) := by
    simp only [Complex.mk_eq_add_mul_I]
    exact Complex.continuous_ofReal.add continuous_const
  exact hCont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private theorem tendsto_horizontal_scale :
    Tendsto (fun x : Real => x - 1) rightAtOne (nhds (0 : Real)) := by
  have h : Tendsto (fun x : Real => x) rightAtOne (nhds 1) := nhdsWithin_le_nhds
  have hConst : Tendsto (fun _ : Real => 1) rightAtOne (nhds (1 : Real)) := tendsto_const_nhds
  have hSub : Tendsto (fun x : Real => x - 1) rightAtOne (nhds (1 - 1 : Real)) := h.sub hConst
  simpa only [sub_self] using hSub

private theorem horizontal_sub (x t : Real) :
    Complex.mk x t - Complex.mk 1 t = ((x - 1 : Real) : Complex) := by
  refine Complex.ext ?real ?imaginary
  case real => rw [Complex.sub_re, Complex.ofReal_re]
  case imaginary =>
    rw [Complex.sub_im, Complex.ofReal_im]
    exact sub_self t

private theorem horizontal_tendsto_logDeriv_order (f : Complex -> Complex) (t : Real)
    (hf : AnalyticAt Complex f (Complex.mk 1 t))
    (hNZ : forall x : Real, 1 < x -> Not (f (Complex.mk x t) = 0)) :
    exists n : Nat, And (f (Complex.mk 1 t) = 0 -> 0 < n)
      (Tendsto (fun x : Real => (x - 1) * (logDeriv f (Complex.mk x t)).re)
        rightAtOne (nhds (n : Real))) := by
  have hRight : Filter.Eventually (fun x : Real => 1 < x) rightAtOne := self_mem_nhdsWithin
  have h := tendsto_horizontal t
  let z := Complex.mk 1 t
  by_cases hz : f z = 0
  case pos =>
    have hNonzeroGerm : Not (Filter.Eventually (fun w => f w = 0) (nhds z)) := by
      intro hZero
      choose x hx using ((h.eventually hZero).and hRight).exists
      exact hNZ x hx.2 hx.1
    choose n hn using tendsto_scaled_logDeriv_at_zero hf hz hNonzeroGerm
    have hPunctured : Tendsto (fun x : Real => Complex.mk x t) rightAtOne
        (nhdsWithin z {w : Complex | Not (w = z)}) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h
        (hRight.mono (fun x hx hEq => (ne_of_gt hx) (congrArg Complex.re hEq)))
    have hLimit :
        Tendsto (fun x : Real => ((Complex.mk x t - z) * logDeriv f (Complex.mk x t)).re)
          rightAtOne (nhds (n : Complex).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp (hn.2.comp hPunctured)
    refine Exists.intro n (And.intro (fun _ => hn.1) ?_)
    simpa only [z, horizontal_sub, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.natCast_re] using hLimit
  case neg =>
    have hLogCont : ContinuousAt (logDeriv f) z :=
      hf.deriv.continuousAt.div hf.continuousAt hz
    have hLimit := tendsto_horizontal_scale.mul
      (Complex.continuous_re.continuousAt.tendsto.comp (hLogCont.tendsto.comp h))
    refine Exists.intro 0 (And.intro (fun hZero => (hz hZero).elim) ?_)
    simpa only [Nat.cast_zero, zero_mul, Function.comp_apply] using hLimit

private theorem horizontal_poleLimit (t : Real) (ht : Not (t = 0)) :
    Tendsto (fun x : Real => (((x - 1 : Real) : Complex)) / (Complex.mk x t - 1))
      rightAtOne (nhds (0 : Complex)) := by
  have hNZ : Not (Complex.mk 1 t - 1 = 0) := fun h => ht
    (congrArg Complex.im (sub_eq_zero.mp h))
  have hNumerator : Tendsto (fun x : Real => ((x - 1 : Real) : Complex))
      rightAtOne (nhds (0 : Complex)) := by
    have h : Tendsto (fun x : Real => ((x - 1 : Real) : Complex))
        rightAtOne (nhds ((0 : Real) : Complex)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_horizontal_scale
    simpa only [Complex.ofReal_zero] using h
  have hDenominator :
      Tendsto (fun x : Real => Complex.mk x t - 1) rightAtOne (nhds (Complex.mk 1 t - 1)) :=
    (tendsto_horizontal t).sub tendsto_const_nhds
  have hQuotient : Tendsto (fun x : Real => ((x - 1 : Real) : Complex) / (Complex.mk x t - 1))
      rightAtOne (nhds (0 / (Complex.mk 1 t - 1))) := hNumerator.div hDenominator hNZ
  simpa only [zero_div] using hQuotient

variable (K : Type*) [Field K] [NumberField K]

private theorem negativeLogDeriv_eq_pole_sub {f : Complex -> Complex}
    (hf : forall z : Complex, AnalyticAt Complex f z)
    (hMatch : forall z : Complex, 1 < z.re -> f z = (z - 1) * dedekindZeta K z)
    {s : Complex} (hs : 1 < s.re) :
    -deriv (dedekindZeta K) s / dedekindZeta K s = 1 / (s - 1) - logDeriv f s := by
  let U : Set Complex := {z | 1 < z.re}
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hNear : Filter.Eventually (fun z => 1 < z.re) (nhds s) := hOpen.mem_nhds hs
  have hNotOne {z : Complex} (hz : 1 < z.re) : Not (z - 1 = 0) := by
    intro hz0
    rw [sub_eq_zero.mp hz0, Complex.one_re] at hz
    exact (lt_irrefl (1 : Real)) hz
  have hNearF : Filter.EventuallyEq (nhds s) f (fun z => (z - 1) * dedekindZeta K z) :=
    hNear.mono hMatch
  have hNearZ : Filter.EventuallyEq (nhds s) (dedekindZeta K) (fun z => f z / (z - 1)) :=
    hNear.mono (fun z hz => (eq_div_iff (hNotOne hz)).mpr (by rw [hMatch z hz, mul_comm]))
  have hId := (hasDerivAt_id s).sub_const (1 : Complex)
  have hZD := ((hf s).differentiableAt.hasDerivAt.div hId (hNotOne hs)).congr_of_eventuallyEq hNearZ
  have hFD := (hId.mul hZD).congr_of_eventuallyEq hNearF
  have hD : deriv f s = dedekindZeta K s + (s - 1) * deriv (dedekindZeta K) s := by
    rw [hFD.deriv, <- hZD.deriv, one_mul, id_eq]
  rw [logDeriv_apply, hD, hMatch s hs]
  field_simp [hNotOne hs, dedekindZeta_ne_zero_of_one_lt_re K hs]
  ring

private theorem scaled_negativeLogDeriv_eq {f : Complex -> Complex}
    (hf : forall z : Complex, AnalyticAt Complex f z)
    (hMatch : forall z : Complex, 1 < z.re -> f z = (z - 1) * dedekindZeta K z)
    {x : Real} (hx : 1 < x) (t : Real) :
    (x - 1) * (-deriv (dedekindZeta K) (Complex.mk x t) / dedekindZeta K (Complex.mk x t)).re =
      (((x - 1 : Real) : Complex) / (Complex.mk x t - 1)).re -
        (x - 1) * (logDeriv f (Complex.mk x t)).re := by
  rw [negativeLogDeriv_eq_pole_sub K hf hMatch (s := Complex.mk x t) hx, Complex.sub_re, mul_sub]
  have h := congrArg Complex.re (mul_one_div ((x - 1 : Real) : Complex) (Complex.mk x t - 1))
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
    congrArg (fun a : Real => a - (x - 1) * (logDeriv f (Complex.mk x t)).re) h

/-- If an entire function agrees initially with the pole-cleared
Dedekind zeta series and is nonzero at the pole, it is nonzero everywhere
on the boundary of absolute convergence. -/
theorem dedekindPoleCleared_ne_zero_re_eq_one {f : Complex -> Complex}
    (hf : forall z : Complex, AnalyticAt Complex f z)
    (hMatch : forall z : Complex, 1 < z.re -> f z = (z - 1) * dedekindZeta K z)
    (hOne : Not (f 1 = 0)) {s : Complex} (hs : s.re = 1) : Not (f s = 0) := by
  let t := s.im
  have hsEq : s = Complex.mk 1 t := Complex.ext hs rfl
  have hAt {y : Real} {x : Real} (hx : 1 < x) : Not (f (Complex.mk x y) = 0) := by
    have hN : Not (Complex.mk x y - 1 = 0) := fun h =>
      (ne_of_gt hx) (congrArg Complex.re (sub_eq_zero.mp h))
    rw [hMatch (Complex.mk x y) hx]
    exact mul_ne_zero hN (dedekindZeta_ne_zero_of_one_lt_re K hx)
  let F (y x : Real) := (-deriv (dedekindZeta K) (Complex.mk x y) /
    dedekindZeta K (Complex.mk x y)).re
  have hRight : Filter.Eventually (fun x : Real => 1 < x) rightAtOne := self_mem_nhdsWithin
  have hLogAtOne : ContinuousAt (logDeriv f) 1 :=
    (hf 1).deriv.continuousAt.div (hf 1).continuousAt hOne
  have hZeroIm (x : Real) : Complex.mk x 0 = (x : Complex) := Complex.ext rfl rfl
  have hLim0 : Tendsto (fun x : Real => (x - 1) * F 0 x) rightAtOne (nhds (1 : Real)) := by
    have hRegular := tendsto_horizontal_scale.mul (Complex.continuous_re.continuousAt.tendsto.comp
      (hLogAtOne.tendsto.comp
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)))
    have hLimit := (tendsto_const_nhds.sub hRegular :
      Tendsto (fun x : Real => 1 - (x - 1) * (logDeriv f (x : Complex)).re) rightAtOne
        (nhds (1 - 0 * (logDeriv f 1).re)))
    apply (show Tendsto _ rightAtOne (nhds (1 : Real)) from by simpa only [zero_mul, sub_zero] using hLimit).congr'
    refine hRight.mono (fun x hx => ?_)
    have hSub : Not ((x : Complex) - 1 = 0) := fun h =>
      (ne_of_gt hx) (congrArg Complex.re (sub_eq_zero.mp h))
    simpa only [F, hZeroIm, Complex.ofReal_sub, Complex.ofReal_one, div_self hSub, Complex.one_re] using
      (scaled_negativeLogDeriv_eq K hf hMatch hx 0).symm
  have hLim (y : Real) (hy : Not (y = 0)) :
      exists n : Nat, And (f (Complex.mk 1 y) = 0 -> 0 < n)
        (Tendsto (fun x : Real => (x - 1) * F y x) rightAtOne (nhds (-(n : Real)))) := by
    choose n hn using horizontal_tendsto_logDeriv_order f y (hf (Complex.mk 1 y)) (fun _ => hAt)
    have hPole := Complex.continuous_re.continuousAt.tendsto.comp (horizontal_poleLimit y hy)
    have hLimit := hPole.sub hn.2
    refine Exists.intro n (And.intro hn.1 ?_)
    apply (show Tendsto _ rightAtOne (nhds (-(n : Real))) from by
      simpa only [Complex.zero_re, zero_sub, Function.comp_apply] using hLimit).congr'
    exact hRight.mono (fun x hx => (scaled_negativeLogDeriv_eq K hf hMatch hx y).symm)
  by_cases ht : t = 0
  case pos => simpa only [hsEq, ht, hZeroIm, Complex.ofReal_one] using hOne
  case neg =>
    choose n hn using hLim t ht
    choose m hm using hLim (2 * t) (mul_ne_zero (by norm_num) ht)
    have hBoth := ((hLim0.const_mul (3 : Real)).add (hn.2.const_mul (4 : Real))).add hm.2
    have hNonneg : 0 <= 3 * (1 : Real) + 4 * (-(n : Real)) + (-(m : Real)) :=
      ge_of_tendsto hBoth (hRight.mono (fun x hx => by
        change 0 <= 3 * ((x - 1) * F 0 x) + 4 * ((x - 1) * F t x) + (x - 1) * F (2 * t) x
        have hCast := dedekindLogDerivative_trigonometric_nonneg K hx t
        have hProduct := mul_nonneg (sub_nonneg.mpr hx.le) hCast
        change 0 <= (x - 1) * (3 * F 0 x + 4 * F t x + F (2 * t) x) at hProduct
        calc
          0 <= (x - 1) * (3 * F 0 x + 4 * F t x + F (2 * t) x) := hProduct
          _ = _ := by ring))
    intro hZero
    have hN : (1 : Real) <= n := by
      exact_mod_cast (Nat.succ_le_of_lt (hn.1 (show f (Complex.mk 1 t) = 0 by rwa [<- hsEq])))
    have hM : (0 : Real) <= m := Nat.cast_nonneg _
    linarith

end Robin1984.GRH
