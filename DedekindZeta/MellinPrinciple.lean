/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Abstract Mellin principle

This module formalises the part of the abstract analytic engine behind
Hecke/Dedekind zeta functions that is retained in this pruned repository: the
Mellin-principle framework from Neukirch, *Algebraic Number Theory*, Chapter VII
§1. The full analytic statement also contains continuation and functional-equation
conclusions; `SumProduct` only consumes the explicit continuation formula and its
agreement with the reduced Mellin transform on the convergence strip.

For a continuous function `f : ℝ_+^* → ℂ` with a limit `f(∞) = a₀` at infinity,
we use the **(reduced) Mellin transform**

    L(f, s) = ∫_0^∞ (f(y) − f(∞)) · y^s · dy/y

(the *reduced* improper integral — the constant term `a₀ = f(∞)` is subtracted
*before* integrating, which is exactly what makes the integral converge near
`y = ∞` and what produces the simple poles via the `(0,1]` part). In Mathlib's
spelling this is `mellin (fun y => f y − a₀) s` because
`y^s · dy/y = y^{s-1} dy`.

The Mellin principle says: if

    f(y) = a₀ + O(e^{-c y^α}),   g(y) = b₀ + O(e^{-c y^α})   (y → ∞)

with `c, α > 0`, and the two functions are tied by the inversion law

    f(1/y) = C · y^k · g(y)

for some `k > 0`, `C ≠ 0`, then:

* **(i)** `L(f,s)`, `L(g,s)` converge for `Re s > k`, are holomorphic there, and
  continue holomorphically to `ℂ ∖ {0, k}`;
* **(ii)** the continuations have simple poles at `s = 0` and `s = k` with
  residues `−a₀, C·b₀` (resp. `−b₀, C⁻¹·a₀` for `g`); equivalently, near the
  poles `L(f,s) = −a₀/s + C·b₀/(s−k) + (holomorphic)`;
* **(iii)** they satisfy the functional equation `L(f,s) = C · L(g, k−s)`.

The point for the Dedekind-zeta development is that the constant terms `a₀`, `b₀` are
*not* discarded: they are precisely the source of the simple poles and of the
`+1`/`−1` lattice-zero correction, so the correction integral `𝒞` must be read
as the explicit polar term `−a₀/s + C·b₀/(s−k)`, never faked to `0` by a
non-integrability artefact.

The statements here are abstract (functions `ℝ → ℂ`) and provide the portion of
the Mellin principle needed by the cone/theta-specific reduction in this repository.
-/

open MeasureTheory Set Filter Asymptotics Topology Complex

namespace DedekindZeta.MellinPrinciple

/-- The **reduced Mellin transform** `L(f, s) = ∫_0^∞ (f y − a₀) y^s dy/y` of
the Mellin principle: the constant term `a₀ = f(∞)` is subtracted before
integrating. In Mathlib's `mellin` spelling `y^s dy/y = y^{s-1} dy`, so this is
`mellin (fun y => f y − a₀) s`.

-- definition used by the Mellin principle -/
noncomputable def reducedMellin (f : ℝ → ℂ) (a₀ : ℂ) (s : ℂ) : ℂ :=
  mellin (fun y => f y - a₀) s

/-- The hypotheses of the **Mellin principle**:
two continuous functions `f, g : ℝ_+^* → ℂ` with exponential decay to their
constant terms `a₀, b₀` at `∞`, tied by the inversion law
`f(1/y) = C · y^k · g(y)` for some `k > 0`, `C ≠ 0`.

-- the Mellin principle hypotheses -/
structure IsMellinPair (f g : ℝ → ℂ) (a₀ b₀ C : ℂ) (k c α : ℝ) : Prop where
  /-- `f` is continuous on `ℝ_+^*`. The integrals only ever use `f` on `Ioi 0`,
  so this records exactly the part of the domain used by the integrals. -/
  hf_cont : ContinuousOn f (Set.Ioi (0 : ℝ))
  /-- `g` is continuous on `ℝ_+^*`. -/
  hg_cont : ContinuousOn g (Set.Ioi (0 : ℝ))
  /-- `k > 0` is the weight in the inversion law. -/
  hk : 0 < k
  /-- decay rate `c > 0`. -/
  hc : 0 < c
  /-- decay exponent `α > 0`. -/
  hα : 0 < α
  /-- `C ≠ 0` is the inversion constant. -/
  hC : C ≠ 0
  /-- `f(y) = a₀ + O(e^{-c y^α})` as `y → ∞`. -/
  hf_decay : (fun y : ℝ => f y - a₀) =O[atTop] (fun y : ℝ => Real.exp (-c * y ^ α))
  /-- `g(y) = b₀ + O(e^{-c y^α})` as `y → ∞`. -/
  hg_decay : (fun y : ℝ => g y - b₀) =O[atTop] (fun y : ℝ => Real.exp (-c * y ^ α))
  /-- the inversion law `f(1/y) = C · y^k · g(y)` for `y > 0`. -/
  hfe : ∀ y : ℝ, 0 < y → f (1 / y) = C * ((y ^ k : ℝ) : ℂ) * g y

variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}

/-- **Super-polynomial decay of the reduced function at `∞`.** The exponential
decay `f y = a₀ + O(e^{-c y^α})` (`c, α > 0`) implies `f y − a₀ = O(y^{-a})` for
*every* exponent `a` as `y → ∞`. This is the top-end half of the convergence
majorant in the standard proof (the integrand is bounded by `B'/y²` on `[1,∞)`).

-- the Mellin principle proof -/
theorem reducedMellin_isBigO_atTop (h : IsMellinPair f g a₀ b₀ C k c α) (a : ℝ) :
    (fun y : ℝ => f y - a₀) =O[atTop] (fun y : ℝ => y ^ (-a)) := by
  -- `e^{-c y^α} =o[atTop] y^{-a}` (exponential decay beats every polynomial), via
  -- `isLittleO_exp_neg_mul_rpow_atTop` composed with `y ↦ y^α → ∞`.
  have hlo : (fun y : ℝ => Real.exp (-c * y ^ α)) =o[atTop] (fun y : ℝ => y ^ (-a)) := by
    have h0 := (isLittleO_exp_neg_mul_rpow_atTop h.hc ((-a) / α)).comp_tendsto
      (tendsto_rpow_atTop h.hα)
    refine h0.congr' (Filter.EventuallyEq.rfl) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hy, mul_comm, div_mul_cancel₀ _ (ne_of_gt h.hα)]
  exact h.hf_decay.trans hlo.isBigO

/-- **Near-zero growth of the reduced function `f`.** Substituting `y ↦ 1/y`
in the inversion law `f(1/y) = C y^k g(y)` (with `g` bounded near `∞`) shows
`f y − a₀ = O(y^{-k})` as `y → 0⁺`; this is the bottom-end half of the
convergence analysis and the source of the pole at `s = k`.

-- the Mellin principle proof -/
theorem reducedMellin_isBigO_zero (h : IsMellinPair f g a₀ b₀ C k c α) :
    (fun y : ℝ => f y - a₀) =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-k)) := by
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  -- `g(y) → b₀` at `+∞` (exponential decay to its constant term).
  have hatbot : Tendsto (fun y : ℝ => -c * y ^ α) atTop atBot :=
    (tendsto_rpow_atTop h.hα).const_mul_atTop_of_neg (by linarith [h.hc])
  have hexp0 : Tendsto (fun y : ℝ => Real.exp (-c * y ^ α)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hatbot
  have hgz : Tendsto (fun y : ℝ => g y - b₀) atTop (𝓝 0) :=
    h.hg_decay.trans_tendsto hexp0
  have hg_top : Tendsto g atTop (𝓝 b₀) := by
    rwa [tendsto_sub_nhds_zero_iff] at hgz
  -- hence `g(1/y) → b₀` as `y → 0⁺`, so `C·g(1/y)` is bounded there.
  have hg_inv : Tendsto (fun y : ℝ => g (1 / y)) l (𝓝 b₀) := by
    simp only [one_div]; exact hg_top.comp tendsto_inv_nhdsGT_zero
  have hbdd : (fun y : ℝ => C * g (1 / y)) =O[l] (fun _ : ℝ => (1 : ℝ)) :=
    (hg_inv.const_mul C).isBigO_one ℝ
  -- `↑(y^{-k}) =O y^{-k}` (norms agree under the real-to-complex coercion).
  have hcast : (fun y : ℝ => ((y ^ (-k) : ℝ) : ℂ)) =O[l] (fun y : ℝ => y ^ (-k)) :=
    Asymptotics.isBigO_of_le _ (fun y => by simp [Complex.norm_real])
  -- the bounded factor times `y^{-k}` is `O(y^{-k})`.
  have hA : (fun y : ℝ => C * ((y ^ (-k) : ℝ) : ℂ) * g (1 / y)) =O[l]
      (fun y : ℝ => y ^ (-k)) := by
    have hmul := hcast.mul hbdd
    refine hmul.congr' ?_ ?_
    · filter_upwards with y; ring
    · filter_upwards with y; ring
  -- the constant `a₀` is `O(y^{-k})` since `y^{-k} → +∞` as `y → 0⁺`.
  have ha0 : (fun _ : ℝ => a₀) =O[l] (fun y : ℝ => y ^ (-k)) := by
    have h1 : (fun _ : ℝ => (1 : ℝ)) =o[l] (fun y : ℝ => y ^ (-k)) := by
      rw [isLittleO_one_left_iff]
      simp only [Real.norm_eq_abs]
      exact tendsto_abs_atTop_atTop.comp (tendsto_rpow_neg_nhdsGT_zero (by linarith [h.hk]))
    exact (isBigO_const_const a₀ one_ne_zero _).trans h1.isBigO
  -- on `𝓝[>] 0`, `f y - a₀ = C·↑(y^{-k})·g(1/y) - a₀` by the inversion law.
  have hev : (fun y : ℝ => f y - a₀) =ᶠ[l]
      (fun y : ℝ => C * ((y ^ (-k) : ℝ) : ℂ) * g (1 / y) - a₀) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    have hfe := h.hfe (1 / y) (by positivity)
    rw [one_div_one_div] at hfe
    have heq : ((1 / y) ^ k : ℝ) = y ^ (-k) := by
      rw [one_div, Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le]
    rw [hfe, heq]
  exact (hA.sub ha0).congr' hev.symm (Filter.EventuallyEq.rfl)

/-- **Mellin principle, the Mellin principle (i), convergence.** For `Re s > k` the
reduced Mellin integral `L(f,s) = ∫_0^∞ (f y − a₀) y^s dy/y` converges
absolutely.

The proof combines the `s`-uniform majorant `B'/y²` near `∞`
(`reducedMellin_isBigO_atTop`) with the near-zero bound `O(y^{-k})`
(`reducedMellin_isBigO_zero`), feeding Mathlib's
`mellinConvergent_of_isBigO_rpow`.

-- the Mellin principle -/
theorem reducedMellin_convergent (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) : MellinConvergent (fun y : ℝ => f y - a₀) s :=
  mellinConvergent_of_isBigO_rpow
    ((h.hf_cont.sub continuousOn_const).locallyIntegrableOn measurableSet_Ioi)
    (reducedMellin_isBigO_atTop h (s.re + 1)) (by linarith)
    (reducedMellin_isBigO_zero h) hs

/-- **The entire correction integral** `F(s)` of the standard treatment's proof:
`F(s) = ∫_1^∞ [(f y − a₀) y^s + C (g y − b₀) y^{k-s}] dy/y`. Written in
Mathlib's `y^{•-1}` form (`y^s · dy/y = y^{s-1} dy`). It converges absolutely
and locally uniformly on all of `ℂ` (the integrand is `O(y^{-2})` on `[1,∞)`
for both summands), hence is entire.

-- the Mellin principle proof, def of `F(s)` -/
noncomputable def mellinTail (f g : ℝ → ℂ) (a₀ b₀ C : ℂ) (k : ℝ) (s : ℂ) : ℂ :=
  ∫ y in Ioi (1 : ℝ),
    ((f y - a₀) * (y : ℂ) ^ (s - 1)
      + C * (g y - b₀) * (y : ℂ) ^ ((k : ℂ) - s - 1))

/-- **The holomorphic continuation** `Lf(s) = −a₀/s + C b₀/(s−k) + F(s)` of
`L(f, s)` to `ℂ ∖ {0, k}` (the standard explicit formula). The first two terms are
the simple poles at `s = 0` (residue `−a₀`) and `s = k` (residue `C b₀`); `F` is
the entire tail `mellinTail`.

-- the Mellin principle proof -/
noncomputable def mellinContinuation (f g : ℝ → ℂ) (a₀ b₀ C : ℂ) (k : ℝ) (s : ℂ) :
    ℂ :=
  -a₀ / s + C * b₀ / (s - (k : ℂ)) + mellinTail f g a₀ b₀ C k s

/-- **The pair swap.** From `f(1/y) = C y^k g(y)` one gets
`g(1/y) = C⁻¹ y^k f(y)`, so `(g, f, b₀, a₀, C⁻¹)` is again a Mellin pair. This
is what produces the `g`-statements from the `f`-statements.

-- the Mellin principle proof (the f↔g symmetry of the construction) -/
theorem IsMellinPair.swap (h : IsMellinPair f g a₀ b₀ C k c α) :
    IsMellinPair g f b₀ a₀ C⁻¹ k c α where
  hf_cont := h.hg_cont
  hg_cont := h.hf_cont
  hk := h.hk
  hc := h.hc
  hα := h.hα
  hC := inv_ne_zero h.hC
  hf_decay := h.hg_decay
  hg_decay := h.hf_decay
  hfe := by
    intro y hy
    have hy' : (0 : ℝ) < 1 / y := by positivity
    have h1 := h.hfe (1 / y) hy'
    rw [one_div_one_div] at h1
    -- h1 : f y = C * (((1/y) ^ k : ℝ) : ℂ) * g (1/y)
    have hr : ((1 : ℝ) / y) ^ k = (y ^ k)⁻¹ := by
      rw [one_div, Real.inv_rpow hy.le]
    rw [hr, Complex.ofReal_inv] at h1
    -- h1 : f y = C * ((y ^ k : ℝ) : ℂ)⁻¹ * g (1/y)
    have hyk : (0 : ℝ) < y ^ k := Real.rpow_pos_of_pos hy k
    have hA : ((y ^ k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hyk
    rw [h1]
    field_simp
    rw [mul_div_assoc, div_self h.hC, mul_one]

/-- **Auxiliary lemma for a single tail summand.** For a continuous `φ` with
super-polynomial decay at `∞` (`φ =O(y^{-a})` for every `a`), the function
`(Ioi 1).indicator φ` (which is `0` near `0` and `φ` past `1`) has a Mellin
transform that, for every `s`:

* is complex-differentiable at `s` (entire), via
  `mellin_differentiableAt_of_isBigO_rpow` (decay at `∞`; vanishing near `0`);
* its restricted integrand `φ · y^{s-1}` is integrable on `Ioi 1`;
* equals `∫_1^∞ φ y · y^{s-1} dy`.

This isolates the structure shared by the `f`- and `g`-summands of
`mellinTail`. -/
private theorem mellinTail_summand_aux (φ : ℝ → ℂ)
    (hcont : ContinuousOn φ (Set.Ioi (0 : ℝ)))
    (hdecay : ∀ a : ℝ, φ =O[atTop] fun y : ℝ => y ^ (-a)) (s : ℂ) :
    DifferentiableAt ℂ (mellin ((Ioi 1).indicator φ)) s ∧
      IntegrableOn (fun y : ℝ => φ y * (y : ℂ) ^ (s - 1)) (Ioi 1) ∧
      mellin ((Ioi 1).indicator φ) s = ∫ y in Ioi 1, φ y * (y : ℂ) ^ (s - 1) := by
  set ψ : ℝ → ℂ := (Ioi 1).indicator φ with hψ
  -- `φ` is `LocallyIntegrableOn (Ioi 0)`; its restriction to `Ioi 1` (an `Ioi 0`
  -- measurable subset) keeps local integrability, computed compact-subset-wise.
  have hloc : LocallyIntegrableOn ψ (Ioi 0) := by
    rw [hψ, locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro K hKsub hKcomp
    exact ((hcont.locallyIntegrableOn measurableSet_Ioi).integrableOn_compact_subset
      hKsub hKcomp).indicator measurableSet_Ioi
  -- `ψ = φ` eventually at `∞`, so it inherits the super-polynomial decay.
  have heqtop : φ =ᶠ[atTop] ψ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    have : y ∈ Ioi (1 : ℝ) := hy
    simp [hψ, Set.indicator_of_mem this]
  have htop : ψ =O[atTop] fun y : ℝ => y ^ (-(s.re + 1)) :=
    (hdecay (s.re + 1)).congr' heqtop (EventuallyEq.refl _ _)
  -- `ψ = 0` near `0`, so it is `O(y^{-b})` for every `b`.
  have h01 : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds (by norm_num [Set.mem_Iio]))
  have heqbot : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)] ψ := by
    filter_upwards [h01] with y hy
    have hy' : y ∉ Ioi (1 : ℝ) := by
      simp only [Set.mem_Ioi, not_lt]; exact le_of_lt hy
    simp [hψ, Set.indicator_of_notMem hy']
  have hbot : ψ =O[𝓝[>] (0 : ℝ)] fun y : ℝ => y ^ (-(s.re - 1)) :=
    (isBigO_zero _ _).congr' heqbot (EventuallyEq.refl _ _)
  have hdiff : DifferentiableAt ℂ (mellin ψ) s :=
    mellin_differentiableAt_of_isBigO_rpow hloc htop (by linarith) hbot (by linarith)
  have hconv' : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) • ψ y) (Ioi 0) :=
    mellinConvergent_of_isBigO_rpow hloc htop (by linarith) hbot (by linarith)
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hEq : EqOn (fun y : ℝ => (y : ℂ) ^ (s - 1) • ψ y)
      (fun y => φ y * (y : ℂ) ^ (s - 1)) (Ioi 1) := by
    intro y hy
    simp only [hψ, Set.indicator_of_mem hy, smul_eq_mul]
    ring
  have hinteg : IntegrableOn (fun y : ℝ => φ y * (y : ℂ) ^ (s - 1)) (Ioi 1) :=
    (IntegrableOn.mono_set hconv' hsub).congr_fun hEq measurableSet_Ioi
  have hval : mellin ψ s = ∫ y in Ioi 1, φ y * (y : ℂ) ^ (s - 1) := by
    have hpt : ∀ y : ℝ, (y : ℂ) ^ (s - 1) • ψ y
        = (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) • φ t) y := by
      intro y
      by_cases hy : y ∈ Ioi (1 : ℝ)
      · rw [hψ, Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      · rw [hψ, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]
    unfold mellin
    simp_rw [hpt]
    rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr hsub]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    rw [smul_eq_mul, mul_comm]
  exact ⟨hdiff, hinteg, hval⟩

/-- **The tail `F(s)` is entire.** -/
theorem mellinTail_analyticOn (h : IsMellinPair f g a₀ b₀ C k c α) :
    AnalyticOnNhd ℂ (mellinTail f g a₀ b₀ C k) Set.univ := by
  have Pf := fun s : ℂ => mellinTail_summand_aux (fun y : ℝ => f y - a₀)
    (h.hf_cont.sub continuousOn_const) (fun a => reducedMellin_isBigO_atTop h a) s
  have Pg := fun s : ℂ => mellinTail_summand_aux (fun y : ℝ => g y - b₀)
    (h.hg_cont.sub continuousOn_const) (fun a => reducedMellin_isBigO_atTop h.swap a) s
  -- `mellinTail` is, pointwise, the sum of two entire (translated) Mellin tails.
  have hfun : mellinTail f g a₀ b₀ C k
      = fun s => mellin ((Ioi 1).indicator (fun y : ℝ => f y - a₀)) s
          + C * mellin ((Ioi 1).indicator (fun y : ℝ => g y - b₀)) ((k : ℂ) - s) := by
    funext s
    have iA' := (Pf s).2.1
    have iB' := ((Pg ((k : ℂ) - s)).2.1).const_mul C
    unfold mellinTail
    rw [(Pf s).2.2, (Pg ((k : ℂ) - s)).2.2, ← integral_const_mul C,
      ← integral_add iA' iB']
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    beta_reduce
    ring
  rw [hfun, analyticOnNhd_univ_iff_differentiable]
  intro s
  have d1 : DifferentiableAt ℂ
      (fun s : ℂ => mellin ((Ioi 1).indicator (fun y : ℝ => f y - a₀)) s) s := (Pf s).1
  have hinner : DifferentiableAt ℂ (fun s : ℂ => (k : ℂ) - s) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have d2 : DifferentiableAt ℂ
      (fun s : ℂ => mellin ((Ioi 1).indicator (fun y : ℝ => g y - b₀)) ((k : ℂ) - s)) s :=
    ((Pg ((k : ℂ) - s)).1).comp s hinner
  exact d1.add (d2.const_mul C)


/-- **Splitting the reduced Mellin integral at `y = 1`.** For `Re s > k` the
integrand `(f y − a₀) y^{s−1}` is integrable on `Ioi 0`, hence the integral over
`Ioi 0` is the sum of the integrals over `Ioc 0 1` and `Ioi 1`.

-- the Mellin principle proof -/
theorem reducedMellin_split (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) :
    reducedMellin f a₀ s
      = (∫ y in Ioc (0 : ℝ) 1, (f y - a₀) * (y : ℂ) ^ (s - 1))
        + (∫ y in Ioi (1 : ℝ), (f y - a₀) * (y : ℂ) ^ (s - 1)) := by
  -- Rewrite Mathlib's `smul` integrand into the `mul` form used in the goal.
  have key : ∀ y : ℝ,
      (y : ℂ) ^ (s - 1) • (f y - a₀) = (f y - a₀) * (y : ℂ) ^ (s - 1) := by
    intro y; rw [smul_eq_mul, mul_comm]
  -- Integrability on `Ioi 0` from `MellinConvergent`.
  have hconv : IntegrableOn
      (fun y : ℝ => (f y - a₀) * (y : ℂ) ^ (s - 1)) (Ioi 0) := by
    have hc := reducedMellin_convergent h hs
    unfold MellinConvergent at hc
    simpa only [key] using hc
  have hsub₁ : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hsub₂ : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  unfold reducedMellin mellin
  simp_rw [key]
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hconv.mono_set hsub₁) (hconv.mono_set hsub₂)]

/-- **Integrability of the `f`-summand of the tail on `Ioi 1`.** The integrand
is `O(y^{−2})` near `∞` (super-polynomial decay of `f y − a₀`).

-- the Mellin principle proof -/
theorem mellinTail_integrable_left (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ} :
    IntegrableOn (fun y : ℝ => (f y - a₀) * (y : ℂ) ^ (s - 1)) (Ioi (1 : ℝ)) :=
  (mellinTail_summand_aux (fun y : ℝ => f y - a₀) (h.hf_cont.sub continuousOn_const)
    (fun a => reducedMellin_isBigO_atTop h a) s).2.1

/-- **Integrability of the `g`-summand of the tail on `Ioi 1`.** The integrand
is `O(y^{−2})` near `∞` (super-polynomial decay of `g y − b₀`).

-- the Mellin principle proof -/
theorem mellinTail_integrable_right (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ} :
    IntegrableOn
      (fun y : ℝ => C * (g y - b₀) * (y : ℂ) ^ ((k : ℂ) - s - 1)) (Ioi (1 : ℝ)) := by
  -- The `g`-summand at exponent `k - s` is `(g y - b₀) * y^{(k-s)-1}`, integrable by
  -- the shared auxiliary lemma applied to the swapped pair (super-polynomial decay
  -- of `g y - b₀` via `h.swap`). Scaling by the constant `C` preserves integrability.
  have hg : IntegrableOn
      (fun y : ℝ => (g y - b₀) * (y : ℂ) ^ (((k : ℂ) - s) - 1)) (Ioi (1 : ℝ)) :=
    (mellinTail_summand_aux (fun y : ℝ => g y - b₀)
      (h.hg_cont.sub continuousOn_const)
      (fun a => reducedMellin_isBigO_atTop h.swap a) ((k : ℂ) - s)).2.1
  refine IntegrableOn.congr_fun (hg.const_mul C) (fun y _ => ?_) measurableSet_Ioi
  ring

/-- **The lower-range integral via the inversion law.** Substituting `y ↦ 1/y`
in `∫_{Ioc 0 1} (f y − a₀) y^{s−1} dy` and applying `f(1/y) = C y^k g(y)`
produces the constant-term boundary integral `−a₀/s`, the pole term
`C b₀/(s−k)`, and the `g`-part of the tail.

-- the Mellin principle proof -/
theorem reducedMellin_lower (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) :
    (∫ y in Ioc (0 : ℝ) 1, (f y - a₀) * (y : ℂ) ^ (s - 1))
      = -a₀ / s + C * b₀ / (s - (k : ℂ))
        + ∫ y in Ioi (1 : ℝ), C * (g y - b₀) * (y : ℂ) ^ ((k : ℂ) - s - 1) := by
  have hkpos := h.hk
  have hspos : 0 < s.re := lt_trans hkpos hs
  have hsne : s ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hspos; exact lt_irrefl _ hspos
  have hsk : s - (k : ℂ) ≠ 0 := by
    intro h0
    have : s = (k : ℂ) := by linear_combination h0
    rw [this, Complex.ofReal_re] at hs; exact lt_irrefl _ hs
  -- The substituted/tail cpow exponent has real part `< -1` since `k < s.re`.
  have hexp : ((k : ℂ) - s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]; linarith
  -- (1) `y ↦ y^(s-1)` is integrable on `Ioc 0 1` (`Re (s-1) > -1`).
  have hcpow_ioc : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    apply intervalIntegral.intervalIntegrable_cpow'
    simp only [Complex.sub_re, Complex.one_re]; linarith
  -- `(f - a₀)·y^(s-1)` is integrable on `Ioi 0` (Mellin convergence), hence on `Ioc 0 1`.
  have hconv := reducedMellin_convergent h hs
  have hfa_ioi : IntegrableOn (fun y : ℝ => (f y - a₀) * (y : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
    refine hconv.congr_fun ?_ measurableSet_Ioi
    intro y _; simp [smul_eq_mul, mul_comm]
  have hfa_ioc : IntegrableOn (fun y : ℝ => (f y - a₀) * (y : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) :=
    hfa_ioi.mono_set Ioc_subset_Ioi_self
  have ha0_ioc : IntegrableOn (fun y : ℝ => a₀ * (y : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) :=
    hcpow_ioc.const_mul a₀
  have hf_ioc : IntegrableOn (fun y : ℝ => f y * (y : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
    refine (hfa_ioc.add ha0_ioc).congr_fun ?_ measurableSet_Ioc
    intro y _; simp only [Pi.add_apply]; ring
  -- (2) The constant-term boundary integral `∫_{Ioc 0 1} a₀ y^(s-1) = a₀/s`.
  have hconst : (∫ y in Ioc (0 : ℝ) 1, a₀ * (y : ℂ) ^ (s - 1)) = a₀ / s := by
    rw [integral_const_mul]
    have hcpow : (∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 1)) = 1 / s := by
      rw [← intervalIntegral.integral_of_le zero_le_one,
        integral_cpow (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith))]
      rw [sub_add_cancel, Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero,
        Complex.zero_cpow hsne, sub_zero]
    rw [hcpow, mul_one_div]
  -- (3) The `y ↦ 1/y` substitution turns `∫_{Ioc 0 1} f y·y^(s-1)` into the `g`-integral.
  have hsubst : (∫ y in Ioc (0 : ℝ) 1, f y * (y : ℂ) ^ (s - 1))
      = ∫ u in Ioi (1 : ℝ), C * g u * (u : ℂ) ^ ((k : ℂ) - s - 1) := by
    have himg : (fun y : ℝ => y⁻¹) '' (Ioc (0 : ℝ) 1) = Ici 1 := by
      ext z
      simp only [mem_image, mem_Ioc, mem_Ici]
      constructor
      · rintro ⟨y, ⟨hy0, hy1⟩, rfl⟩
        exact (one_le_inv₀ hy0).mpr hy1
      · intro hz
        have hz0 : (0 : ℝ) < z := lt_of_lt_of_le zero_lt_one hz
        exact ⟨z⁻¹, ⟨inv_pos.mpr hz0, (inv_le_one₀ hz0).mpr hz⟩, inv_inv z⟩
    have hderiv : ∀ x ∈ Ioc (0 : ℝ) 1,
        HasDerivWithinAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) (Ioc (0 : ℝ) 1) x :=
      fun x hx => (hasDerivAt_inv (ne_of_gt hx.1)).hasDerivWithinAt
    have hinj : InjOn (fun y : ℝ => y⁻¹) (Ioc (0 : ℝ) 1) :=
      fun a _ b _ hab => inv_inj.mp hab
    have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hderiv hinj
      (fun u : ℝ => C * g u * (u : ℂ) ^ ((k : ℂ) - s - 1))
    rw [himg, integral_Ici_eq_integral_Ioi] at key
    rw [key]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    obtain ⟨hx0, _⟩ := hx
    set X : ℂ := (x : ℂ) with hX
    have hXne : X ≠ 0 := by rw [hX]; exact_mod_cast ne_of_gt hx0
    have harg : X.arg ≠ Real.pi := by
      rw [hX, Complex.arg_ofReal_of_nonneg hx0.le]; exact (Real.pi_ne_zero).symm
    have hfe := h.hfe x⁻¹ (inv_pos.mpr hx0)
    rw [one_div, inv_inv] at hfe
    have hbase : ((x⁻¹ ^ k : ℝ) : ℂ) = (X⁻¹) ^ (k : ℂ) := by
      rw [Complex.ofReal_cpow (inv_nonneg.mpr hx0.le), Complex.ofReal_inv, hX]
    have hxsq : (((x ^ 2)⁻¹ : ℝ) : ℂ) = (X ^ 2)⁻¹ := by rw [hX]; push_cast; ring
    have hinvcast : ((x⁻¹ : ℝ) : ℂ) = X⁻¹ := by rw [hX]; exact Complex.ofReal_inv x
    have hX2 : (X ^ 2)⁻¹ = X ^ (-(2 : ℂ)) := by
      rw [Complex.cpow_neg]
      norm_num [Complex.cpow_natCast X 2]
    have cpid : (X⁻¹) ^ (k : ℂ) * X ^ (s - 1)
        = (X ^ 2)⁻¹ * (X⁻¹) ^ ((k : ℂ) - s - 1) := by
      rw [Complex.inv_cpow X _ harg, Complex.inv_cpow X _ harg,
        ← Complex.cpow_neg, ← Complex.cpow_neg, hX2,
        ← Complex.cpow_add _ _ hXne, ← Complex.cpow_add _ _ hXne]
      congr 1; ring
    rw [Complex.real_smul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x ^ 2)⁻¹), hfe,
      hbase, hxsq, hinvcast]
    linear_combination (C * g x⁻¹) * cpid
  -- (4) Split `g u = (g u - b₀) + b₀`; the `b₀` part is the pole `C b₀/(s-k)`.
  have htail := mellinTail_integrable_right (h := h) (s := s)
  have hconstg : IntegrableOn
      (fun u : ℝ => C * b₀ * (u : ℂ) ^ ((k : ℂ) - s - 1)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_cpow_of_lt hexp one_pos).const_mul (C * b₀)
  have hsplit_g : (∫ u in Ioi (1 : ℝ), C * g u * (u : ℂ) ^ ((k : ℂ) - s - 1))
      = (∫ u in Ioi (1 : ℝ), C * (g u - b₀) * (u : ℂ) ^ ((k : ℂ) - s - 1))
        + C * b₀ / (s - (k : ℂ)) := by
    have hpole : (∫ u in Ioi (1 : ℝ), C * b₀ * (u : ℂ) ^ ((k : ℂ) - s - 1))
        = C * b₀ / (s - (k : ℂ)) := by
      rw [integral_const_mul, integral_Ioi_cpow_of_lt hexp one_pos]
      rw [sub_add_cancel, Complex.ofReal_one, Complex.one_cpow]
      have hks : (k : ℂ) - s ≠ 0 := sub_ne_zero.mpr (fun e => hsk (by linear_combination -e))
      field_simp
      ring
    rw [← hpole, ← integral_add htail hconstg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    ring
  -- Assemble.
  have step1 : (∫ y in Ioc (0 : ℝ) 1, (f y - a₀) * (y : ℂ) ^ (s - 1))
      = (∫ y in Ioc (0 : ℝ) 1, f y * (y : ℂ) ^ (s - 1))
        - (∫ y in Ioc (0 : ℝ) 1, a₀ * (y : ℂ) ^ (s - 1)) := by
    rw [← integral_sub hf_ioc ha0_ioc]
    refine setIntegral_congr_fun measurableSet_Ioc (fun y _ => ?_)
    ring
  rw [step1, hsubst, hconst, hsplit_g]
  ring

/-- **The continuation agrees with the reduced Mellin transform on `Re s > k`**
(the identity `L(f,s) = −a₀/s + C b₀/(s−k) + F(s)`, obtained by cutting
`(0,∞)` at `1` and substituting `y ↦ 1/y` on `(0,1]`).

Assembled from `reducedMellin_split` (cut at `1`), `reducedMellin_lower` (the
`y ↦ 1/y` substitution producing the polar terms and `g`-tail), and the
integrability of the two tail summands (`integral_add` splits `mellinTail`).

-- the Mellin principle proof -/
theorem mellinContinuation_eq (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) :
    mellinContinuation f g a₀ b₀ C k s = reducedMellin f a₀ s := by
  rw [reducedMellin_split h hs, reducedMellin_lower h hs]
  unfold mellinContinuation mellinTail
  rw [integral_add (mellinTail_integrable_left h) (mellinTail_integrable_right h)]
  ring





end DedekindZeta.MellinPrinciple

/-!
## Provenance

- Classification: **Other published source formalization**.
- Mathematical source: mathlib-initiative/sum_product at 80e4127a67742659d521466204c6d2d7e0ca2b3f.
- Formalization note: Lean 4.33.1 compatibility port with narrow imports for DedekindZeta.MellinPrinciple.
- PROVENANCE-END
-/
