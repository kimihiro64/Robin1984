import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Robin1984.GRH
import Robin1984.GRH.CyclotomicNormCoefficients
import Robin1984.GRH.DedekindContinuation

/-!
# Cyclotomic Dedekind zeta factorization

The logarithmic derivatives agree because the coefficients agree at each natural index. The limit along the real axis fixes the multiplicative constant, and analytic continuation gives the identity away from the pole.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The cyclotomic factorization into primitive Dirichlet L-functions.
- Formalization note: Compare logarithmic Dirichlet series, normalize at real infinity, and use uniqueness of continuation.
- Content basis: Cyclotomic prime decomposition, primitive character orthogonality, and analytic continuation.
- Dependency status: Optional Dirichlet GRH extension and Mathlib.
-/

open Filter NumberField Set

namespace Robin1984.GRH

private noncomputable def primitiveFactor {m : Nat} [NeZero m]
    (chi : DirichletCharacter Complex m) : Complex -> Complex :=
  @DirichletCharacter.LFunction chi.conductor (NeZero.mk chi.conductor_ne_zero)
    chi.primitiveCharacter

/-- The finite product of the primitive L-functions induced by characters modulo m. -/
noncomputable def cyclotomicPrimitiveProduct (m : Nat) [NeZero m] (s : Complex) : Complex :=
  Finset.univ.prod (fun chi : DirichletCharacter Complex m => primitiveFactor chi s)

private theorem primitiveFactor_ne_zero {m : Nat} [NeZero m]
    (chi : DirichletCharacter Complex m) {s : Complex} (hs : 1 < s.re) :
    Not (primitiveFactor chi s = 0) := by
  let _ : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  have hs1 : Not (s = 1) := by
    intro h
    simp [h] at hs
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi.primitiveCharacter
    (Or.inr hs1) hs.le

private theorem differentiableAt_primitiveFactor {m : Nat} [NeZero m]
    (chi : DirichletCharacter Complex m) {s : Complex} (hs : Not (s = 1)) :
    DifferentiableAt Complex (primitiveFactor chi) s := by
  let _ : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  exact DirichletCharacter.differentiableAt_LFunction chi.primitiveCharacter s (Or.inl hs)

private theorem cyclotomic_logDeriv_eq_primitiveProduct (m : Nat) [NeZero m]
    {s : Complex} (hs : 1 < s.re) :
    logDeriv (NumberField.dedekindZeta (CyclotomicField m Rat)) s =
      logDeriv (cyclotomicPrimitiveProduct m) s := by
  classical
  have hs1 : Not (s = 1) := by
    intro h
    simp [h] at hs
  let a (chi : DirichletCharacter Complex m) : Nat -> Complex :=
    (fun n : Nat => chi.primitiveCharacter (n : ZMod chi.conductor)) *
      (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
  have hsum (chi : DirichletCharacter Complex m) : LSeriesSummable (a chi) s := by
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi.primitiveCharacter hs
  have ha (chi : DirichletCharacter Complex m) : LSeries (a chi) s =
      -logDeriv (primitiveFactor chi) s := by
    let _ : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
    have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq chi.primitiveCharacter hs
    rw [<- DirichletCharacter.LFunction_eq_LSeries chi.primitiveCharacter hs,
      <- DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi.primitiveCharacter hs] at h
    change LSeries (a chi) s = -(deriv (primitiveFactor chi) s / primitiveFactor chi s)
    rw [<- neg_div]
    exact h
  have hcoeff : (fun n => (dedekindNormCoeff (CyclotomicField m Rat) n : Complex)) =
      Finset.univ.sum a := by
    funext n
    rw [Finset.sum_apply, cyclotomicNormCoeff_eq_sum_primitiveCharacter_vonMangoldt,
      Finset.sum_mul]
    simp only [Pi.mul_apply, Int.cast_natCast]
  have hDed :
      LSeries (fun n => (dedekindNormCoeff (CyclotomicField m Rat) n : Complex)) s =
        -logDeriv (NumberField.dedekindZeta (CyclotomicField m Rat)) s := by
    change tsum (LSeries.term (fun n => (dedekindNormCoeff (CyclotomicField m Rat) n : Complex)) s) =
      -(deriv (NumberField.dedekindZeta (CyclotomicField m Rat)) s /
        NumberField.dedekindZeta (CyclotomicField m Rat) s)
    rw [<- neg_div]
    exact (hasSum_dedekindNormCoeff (CyclotomicField m Rat) hs).tsum_eq
  rw [hcoeff, LSeries_sum (fun chi _ => hsum chi)] at hDed
  simp only [ha, Finset.sum_neg_distrib] at hDed
  unfold cyclotomicPrimitiveProduct
  rw [logDeriv_prod (fun chi _ => primitiveFactor_ne_zero chi hs)
    (fun chi _ => differentiableAt_primitiveFactor chi hs1)]
  exact (neg_inj.mp hDed).symm

private theorem idealNormCount_one (K : Type*) [Field K] [NumberField K] :
    idealNormCount K 1 = 1 := by
  unfold idealNormCount
  apply Nat.card_eq_one_iff_unique.mpr
  refine And.intro ?_ (Nonempty.intro (Subtype.mk Top.top (Ideal.absNorm_eq_one_iff.mpr rfl)))
  refine Subsingleton.intro (fun a b => Subtype.ext ?_)
  exact (Ideal.absNorm_eq_one_iff.mp a.property).trans
    (Ideal.absNorm_eq_one_iff.mp b.property).symm

private theorem tendsto_dedekindZeta_real_atTop
    (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun x : Real => NumberField.dedekindZeta K (x : Complex)) atTop (nhds 1) := by
  have hTwo : 1 < (2 : Complex).re := by norm_num
  have hs := (dedekindZeta_series_summable K hTwo).abscissaOfAbsConv_le
  have hb := hs.trans_lt (EReal.coe_lt_top _)
  change Tendsto (fun x : Real => LSeries (fun n => (idealNormCount K n : Complex)) x) atTop (nhds 1)
  simpa only [idealNormCount_one, Nat.cast_one] using LSeries.tendsto_atTop hb

private theorem tendsto_primitiveFactor_real_atTop {m : Nat} [NeZero m]
    (chi : DirichletCharacter Complex m) :
    Tendsto (fun x : Real => primitiveFactor chi (x : Complex)) atTop (nhds 1) := by
  let _ : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  let psi := chi.primitiveCharacter
  have hTwo : 1 < (2 : Complex).re := by norm_num
  have hs := (DirichletCharacter.LSeriesSummable_of_one_lt_re psi hTwo).abscissaOfAbsConv_le
  have hb := hs.trans_lt (EReal.coe_lt_top _)
  have ht := LSeries.tendsto_atTop hb
  have hone : psi ((1 : Nat) : ZMod chi.conductor) = 1 := by simp
  rw [hone] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
  exact (DirichletCharacter.LFunction_eq_LSeries psi (by simpa only [Complex.ofReal_re] using hx)).symm

private theorem tendsto_cyclotomicPrimitiveProduct_real_atTop (m : Nat) [NeZero m] :
    Tendsto (fun x : Real => cyclotomicPrimitiveProduct m (x : Complex)) atTop (nhds 1) := by
  classical
  unfold cyclotomicPrimitiveProduct
  generalize (Finset.univ : Finset (DirichletCharacter Complex m)) = F
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (tendsto_const_nhds (x := (1 : Complex)))
  | insert chi F hchi ih =>
    simp only [Finset.prod_insert hchi]
    simpa only [one_mul] using (tendsto_primitiveFactor_real_atTop chi).mul ih

private theorem cyclotomicPrimitiveProduct_eq_series (m : Nat) [NeZero m]
    {s : Complex} (hs : 1 < s.re) :
    cyclotomicPrimitiveProduct m s = NumberField.dedekindZeta (CyclotomicField m Rat) s := by
  classical
  let K := CyclotomicField m Rat
  let U : Set Complex := {z : Complex | 1 < z.re}
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hConnected : IsPreconnected U := (convex_halfSpace_re_gt 1).isPreconnected
  have hf : DifferentiableOn Complex (NumberField.dedekindZeta K) U := by
    intro z hz
    have ha : LSeries.abscissaOfAbsConv (fun n => (idealNormCount K n : Complex)) <= 1 := by
      refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable ?_
      intro x hx
      exact dedekindZeta_series_summable K (by simpa only [Complex.ofReal_re] using hx)
    exact (LSeries_hasDerivAt (ha.trans_lt (EReal.coe_lt_coe_iff.mpr hz))).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn Complex (cyclotomicPrimitiveProduct m) U := by
    intro z hz
    have hz1 : Not (z = 1) := by
      intro h
      change 1 < z.re at hz
      simp [h] at hz
    exact (DifferentiableAt.fun_finsetProd (fun chi _ =>
      differentiableAt_primitiveFactor chi hz1)).differentiableWithinAt
  have hfn (z : Complex) (hz : Membership.mem U z) :
      Not (NumberField.dedekindZeta K z = 0) := dedekindZeta_ne_zero_of_one_lt_re K hz
  have hgn (z : Complex) (hz : Membership.mem U z) :
      Not (cyclotomicPrimitiveProduct m z = 0) :=
    Finset.prod_ne_zero_iff.mpr (fun chi _ => primitiveFactor_ne_zero chi hz)
  have heq : Set.EqOn (logDeriv (NumberField.dedekindZeta K))
      (logDeriv (cyclotomicPrimitiveProduct m)) U :=
    fun _ hz => cyclotomic_logDeriv_eq_primitiveProduct m hz
  choose c hc using (logDeriv_eqOn_iff hf hg hOpen hConnected hgn hfn).mp heq
  have ht := (tendsto_cyclotomicPrimitiveProduct_real_atTop m).const_mul c
  have he : EventuallyEq atTop
      (fun x : Real => c * cyclotomicPrimitiveProduct m (x : Complex))
      (fun x : Real => NumberField.dedekindZeta K (x : Complex)) := by
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    exact (hc.2 (show Membership.mem U (x : Complex) by
      change 1 < (x : Complex).re
      simpa only [Complex.ofReal_re] using hx)).symm
  have hc1 : c = 1 := by
    simpa only [mul_one] using tendsto_nhds_unique (ht.congr' he) (tendsto_dedekindZeta_real_atTop K)
  have h := hc.2 (show Membership.mem U s from hs)
  simpa only [hc1, one_smul] using h.symm

/-- Away from the pole, cyclotomic Dedekind zeta is the product of its primitive Dirichlet factors. -/
theorem cyclotomicDedekindZeta_eq_primitiveProduct (m : Nat) [NeZero m]
    {s : Complex} (hs : Not (s = 1)) :
    DedekindZeta.dedekindZetaContinuation (CyclotomicField m Rat) s =
      cyclotomicPrimitiveProduct m s := by
  have hf : IsDedekindZetaContinuation (CyclotomicField m Rat)
      (DedekindZeta.dedekindZetaContinuation (CyclotomicField m Rat)) :=
    And.intro (fun _ hz => (DedekindZeta.analyticAt_dedekindZetaContinuation _ hz).differentiableAt.differentiableWithinAt)
      (fun _ hz => DedekindZeta.dedekindZetaContinuation_eq_series _ hz)
  have hg : IsDedekindZetaContinuation (CyclotomicField m Rat) (cyclotomicPrimitiveProduct m) :=
    And.intro (fun _ hz => (DifferentiableAt.fun_finsetProd (fun chi _ =>
      differentiableAt_primitiveFactor chi hz)).differentiableWithinAt)
      (fun _ hz => cyclotomicPrimitiveProduct_eq_series m hz)
  exact eqOn_of_dedekindZetaContinuations hf hg hs

/-- GRH for every Dirichlet L-function is equivalent to RH for all cyclotomic Dedekind zeta functions. -/
theorem dirichletGRH_iff_cyclotomicDedekindRH :
    DirichletGRH <-> forall (m : Nat) [NeZero m], DedekindRH (CyclotomicField m Rat) := by
  refine dirichletGRH_iff_cyclotomicDedekindRH_of_primitive_factorization
    (fun m _ => DedekindZeta.dedekindZetaContinuation (CyclotomicField m Rat)) ?_ ?_
  case refine_1 =>
    intro m hm
    exact And.intro
      (fun _ hz => (DedekindZeta.analyticAt_dedekindZetaContinuation _ hz).differentiableAt.differentiableWithinAt)
      (fun _ hz => DedekindZeta.dedekindZetaContinuation_eq_series _ hz)
  case refine_2 =>
    intro m hm s _ hs
    have hs1 : Not (s = 1) := by
      intro h
      simp [h] at hs
    exact cyclotomicDedekindZeta_eq_primitiveProduct m hs1

end Robin1984.GRH
