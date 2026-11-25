import Robin1984.GRH.GodementJacquetLocalZetaCoefficientOrbit

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The logarithmic derivative of a local Euler factor and the geometric series for its reciprocal linear factors.
- Formalization note: Recovers the multiplicity-preserving prime-power coefficients of a normalized local denominator and obtains a common right half-plane for the finite collection of roots.
- PROVENANCE-END
-/

/-!
# Prime-power coefficients of canonical Godement-Jacquet factors

A polynomial normalized to one at zero gives a reciprocal Euler factor.
After the usual real shift, the inverse roots give the linear local factors,
with multiplicities. On a common right half-plane their geometric series
express the negative logarithmic derivative as a prime-power series.
-/

set_option autoImplicit false

namespace Robin1984.GRH

private theorem prod_sub_of_nonzero_roots (z : Complex) (R : Multiset Complex)
    (h : forall r, Membership.mem R r -> Not (r = 0)) :
    (R.map (fun r => z - r)).prod =
      (R.map (fun r => 0 - r)).prod * (R.map (fun r => 1 - Inv.inv r * z)).prod := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons r R ih =>
    have hr := h r (Multiset.mem_cons_self _ _)
    have hR : forall x, Membership.mem R x -> Not (x = 0) :=
      fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have hf : z - r = (0 - r) * (1 - Inv.inv r * z) := by
      field_simp [hr]
      ring
    simp only [Multiset.map_cons, Multiset.prod_cons, ih hR]
    rw [hf, mul_mul_mul_comm]

/-- A polynomial normalized at zero is the product of the linear factors
from its roots, with multiplicities. -/
theorem eval_eq_prod_inverse_roots (D : Polynomial Complex) (hD : D.eval 0 = 1)
    (z : Complex) : D.eval z = (D.roots.map (fun r => 1 - Inv.inv r * z)).prod := by
  have hNonzero : Not (D = 0) := by
    intro h
    simp [h] at hD
  have hRoots : forall r, Membership.mem D.roots r -> Not (r = 0) := by
    intro r hr h
    subst r
    exact one_ne_zero (hD.symm.trans ((Polynomial.mem_roots hNonzero).mp hr))
  have hSplit : D.Splits := IsAlgClosed.splits D
  rw [hSplit.eval_eq_prod_roots, prod_sub_of_nonzero_roots z D.roots hRoots]
  rw [Eq.symm (mul_assoc _ _ _), Eq.symm (hSplit.eval_eq_prod_roots 0), hD, one_mul]

/-- Express the shifted local denominator using the inverse roots multiplied
by the shift factor. -/
theorem eval_shifted_primeNorm_eq_prod_inverse_roots
    (D : Polynomial Complex) (hD : D.eval 0 = 1) (q delta : Real) (hq : 0 < q)
    (s : Complex) :
    D.eval ((q : Complex) ^ (-(s + (delta : Complex)))) =
      ((D.roots.map (fun r => Inv.inv r * (q : Complex) ^ (-(delta : Complex)))).map
        (fun a => 1 - a * (q : Complex) ^ (-s))).prod := by
  have hShift : (q : Complex) ^ (-(s + (delta : Complex))) =
      (q : Complex) ^ (-(delta : Complex)) * (q : Complex) ^ (-s) := by
    rw [neg_add, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hq.ne'), mul_comm]
  rw [hShift, eval_eq_prod_inverse_roots D hD, Multiset.map_map]
  simp only [Function.comp_apply, mul_assoc]

private theorem logDeriv_localEulerDenominator (q : Real) (hq : 0 < q)
    (A : Multiset Complex) (s : Complex)
    (hSize : forall a, Membership.mem A a -> norm (a * (q : Complex) ^ (-s)) < 1) :
    let P (t : Complex) := (A.map (fun a => 1 - a * (q : Complex) ^ (-t))).prod
    And (Not (P s = 0)) (And (DifferentiableAt Complex P s)
      (logDeriv P s = (A.map (fun a =>
        (Real.log q : Complex) * (a * (q : Complex) ^ (-s)) /
          (1 - a * (q : Complex) ^ (-s)))).sum)) := by
  dsimp only
  induction A using Multiset.induction_on with
  | empty =>
    simp [logDeriv_apply]
  | cons a A ih =>
    have hTail : forall b, Membership.mem A b -> norm (b * (q : Complex) ^ (-s)) < 1 :=
      fun b hb => hSize b (Multiset.mem_cons_of_mem hb)
    have hRest := ih hTail
    have hAtomNonzero : Not (1 - a * (q : Complex) ^ (-s) = 0) := by
      intro he
      have hOne := (sub_eq_zero.mp he).symm
      have hSmall := hSize a (Multiset.mem_cons_self _ _)
      rw [hOne, norm_one] at hSmall
      exact (lt_irrefl _) hSmall
    have hAtom : HasDerivAt (fun t : Complex => 1 - a * (q : Complex) ^ (-t))
        ((Real.log q : Complex) * (a * (q : Complex) ^ (-s))) s := by
      have h := (hasDerivAt_const s (1 : Complex)).sub
        (((hasDerivAt_neg' s).const_cpow
          (c := (q : Complex)) (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne'))).const_mul a)
      have hValue : (0 : Complex) -
          a * ((q : Complex) ^ (-s) * Complex.log (q : Complex) * (-1)) =
          (Real.log q : Complex) * (a * (q : Complex) ^ (-s)) := by
        rw [<- Complex.ofReal_log hq.le]
        ring
      rw [hValue] at h
      exact h
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    refine And.intro (mul_ne_zero hAtomNonzero hRest.1)
      (And.intro (hAtom.differentiableAt.mul hRest.2.1) ?_)
    rw [logDeriv_mul s hAtomNonzero hRest.1 hAtom.differentiableAt hRest.2.1, hRest.2.2]
    rw [logDeriv_apply, hAtom.deriv]

private theorem hasSum_localEulerGeometric (q : Real) (A : Multiset Complex)
    (s : Complex) (hSize : forall a, Membership.mem A a -> norm (a * (q : Complex) ^ (-s)) < 1) :
    HasSum (fun k : Nat => (A.map (fun a =>
        (Real.log q : Complex) * (a * (q : Complex) ^ (-s)) ^ (k + 1))).sum)
      (A.map (fun a =>
        (Real.log q : Complex) * (a * (q : Complex) ^ (-s)) /
          (1 - a * (q : Complex) ^ (-s)))).sum := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    let w := a * (q : Complex) ^ (-s)
    have hw : norm w < 1 := hSize a (Multiset.mem_cons_self _ _)
    have hAtom : HasSum (fun k : Nat => (Real.log q : Complex) * w ^ (k + 1))
        ((Real.log q : Complex) * w / (1 - w)) := by
      have h := (hasSum_geometric_of_norm_lt_one hw).mul_left ((Real.log q : Complex) * w)
      rw [div_eq_mul_inv]
      have hTerms : (fun k : Nat => (Real.log q : Complex) * w ^ (k + 1)) =
          (fun k : Nat => (Real.log q : Complex) * w * w ^ k) := by
        funext k
        rw [pow_succ]
        ring
      rw [hTerms]
      exact h
    have hTail : forall b, Membership.mem A b -> norm (b * (q : Complex) ^ (-s)) < 1 :=
      fun b hb => hSize b (Multiset.mem_cons_of_mem hb)
    simpa only [Multiset.map_cons, Multiset.sum_cons, w] using hAtom.add (ih hTail)

private theorem hasSum_primePower_canonicalFactor (D : Polynomial Complex) (hD : D.eval 0 = 1)
    (q delta : Real) (hq : 0 < q) (s : Complex)
    (hSize : forall r, Membership.mem D.roots r ->
      norm ((Inv.inv r * (q : Complex) ^ (-(delta : Complex))) * (q : Complex) ^ (-s)) < 1) :
    let A := D.roots.map (fun r => Inv.inv r * (q : Complex) ^ (-(delta : Complex)))
    HasSum (fun k : Nat => (A.map (fun a =>
      (Real.log q : Complex) * (a * (q : Complex) ^ (-s)) ^ (k + 1))).sum)
      (-logDeriv (fun t : Complex => Inv.inv (D.eval ((q : Complex) ^ (-(t + (delta : Complex)))))) s) := by
  intro A
  have h : forall a, Membership.mem A a -> norm (a * (q : Complex) ^ (-s)) < 1 := by
    intro a ha
    choose r hr he using Multiset.mem_map.mp ha
    rw [<- he]
    exact hSize r hr
  let P (t : Complex) := (A.map (fun a => 1 - a * (q : Complex) ^ (-t))).prod
  have hP := logDeriv_localEulerDenominator q hq A s h
  have hEq : (fun t : Complex => Inv.inv (D.eval ((q : Complex) ^ (-(t + (delta : Complex)))))) =
      (fun t : Complex => 1 / P t) := by
    funext t
    rw [eval_shifted_primeNorm_eq_prod_inverse_roots D hD q delta hq t, one_div]
  have hZ : logDeriv (fun _ : Complex => (1 : Complex)) s = 0 := by simp [logDeriv_apply]
  rw [hEq, logDeriv_div s one_ne_zero hP.1 (differentiableAt_const _) hP.2.1, hZ,
    zero_sub, neg_neg, hP.2.2]
  exact hasSum_localEulerGeometric q A s h

private theorem exists_rightHalfPlane_localEulerNorm (q : Real) (hq : 1 < q)
    (A : Multiset Complex) :
    exists T : Real, forall s : Complex, T < s.re ->
      forall a, Membership.mem A a -> norm (a * (q : Complex) ^ (-s)) < 1 := by
  classical
  let B : Real := 1 + A.toFinset.sum norm
  have hB : 0 < B := by
    have hSum : 0 <= A.toFinset.sum norm := Finset.sum_nonneg (fun a _ => norm_nonneg a)
    dsimp only [B]
    linarith
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hLogQ : 0 < Real.log q := Real.log_pos hq
  refine Exists.intro (Real.log B / Real.log q) ?_
  intro s hs a ha
  have hCancel : (Real.log B / Real.log q) * Real.log q = Real.log B := by
    field_simp [hLogQ.ne']
  have hExp : Real.log B < s.re * Real.log q := by
    simpa only [hCancel] using mul_lt_mul_of_pos_right hs hLogQ
  have hScale : q ^ (-s.re) < Inv.inv B := by
    calc
      _ = Real.exp (Real.log q * (-s.re)) := by rw [Real.rpow_def_of_pos hq0]
      _ < Real.exp (-(Real.log B)) := Real.exp_lt_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log hB]
  have haB : norm a <= B := by
    have hA : norm a <= A.toFinset.sum norm :=
      Finset.single_le_sum (fun b _ => norm_nonneg b) (Multiset.mem_toFinset.mpr ha)
    dsimp only [B]
    linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
  calc
    _ <= B * q ^ (-s.re) := mul_le_mul_of_nonneg_right haB (Real.rpow_nonneg hq0.le _)
    _ < B * Inv.inv B := mul_lt_mul_of_pos_left hScale hB
    _ = 1 := by field_simp [hB.ne']

private theorem exists_hasSum_primePower_canonicalFactor_rightHalfPlane
    (D : Polynomial Complex) (hD : D.eval 0 = 1)
    (q delta : Real) (hq : 1 < q) :
    let A := D.roots.map (fun r => Inv.inv r * (q : Complex) ^ (-(delta : Complex)))
    let L (s : Complex) := Inv.inv (D.eval ((q : Complex) ^ (-(s + (delta : Complex)))))
    exists T : Real, forall s : Complex, T < s.re ->
      HasSum (fun k : Nat => (A.map (fun a =>
        (Real.log q : Complex) * (a * (q : Complex) ^ (-s)) ^ (k + 1))).sum)
        (-logDeriv L s) := by
  intro A L
  choose T hT using exists_rightHalfPlane_localEulerNorm q hq A
  refine Exists.intro T (fun s hs => ?_)
  apply hasSum_primePower_canonicalFactor D hD q delta (zero_lt_one.trans hq) s
  intro r hr
  exact hT s hs _ (Multiset.mem_map.mpr (Exists.intro r (And.intro hr rfl)))

private theorem cpow_primeNorm_natPower (q : Real) (hq : 0 < q)
    (m : Nat) (s : Complex) :
    ((q ^ m : Real) : Complex) ^ s = ((q : Complex) ^ s) ^ m := by
  have hArg : Complex.arg (q : Complex) = 0 := Complex.arg_ofReal_of_nonneg hq.le
  have hLeft : -Real.pi < (m : Real) * Complex.arg (q : Complex) := by
    rw [hArg, mul_zero]
    exact neg_lt_zero.mpr Real.pi_pos
  have hRight : (m : Real) * Complex.arg (q : Complex) <= Real.pi := by
    rw [hArg, mul_zero]
    exact Real.pi_pos.le
  rw [Complex.ofReal_pow, <- Complex.cpow_nat_mul' hLeft hRight, Complex.cpow_nat_mul]

private theorem sum_localEulerPowers (A : Multiset Complex) (z c : Complex) (m : Nat) :
    (A.map (fun a => c * (a * z) ^ m)).sum = c * (A.map (fun a => a ^ m)).sum * z ^ m := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih, mul_pow]
    ring

/-- The Euler coefficients of the shifted reciprocal polynomial are the
powers of its shifted inverse roots, summed with multiplicities and
weighted by the logarithm of the prime norm. -/
theorem hasSum_canonicalLocalPrimePowerCoefficients_rightHalfPlane
    (D : Polynomial Complex) (hD : D.eval 0 = 1) (q delta : Real) (hq : 1 < q) :
    let A := D.roots.map (fun r => Inv.inv r * (q : Complex) ^ (-(delta : Complex)))
    let L (s : Complex) := Inv.inv (D.eval ((q : Complex) ^ (-(s + (delta : Complex)))))
    exists T : Real, forall s : Complex, T < s.re ->
      HasSum (fun k : Nat => (Real.log q : Complex) * (A.map (fun a => a ^ (k + 1))).sum *
          ((q ^ (k + 1) : Real) : Complex) ^ (-s))
        (-logDeriv L s) := by
  intro A L
  choose T hT using exists_hasSum_primePower_canonicalFactor_rightHalfPlane D hD q delta hq
  refine Exists.intro T (fun s hs => ?_)
  have hTerms (k : Nat) :
      (A.map (fun a => (Real.log q : Complex) * (a * (q : Complex) ^ (-s)) ^ (k + 1))).sum =
      (Real.log q : Complex) * (A.map (fun a => a ^ (k + 1))).sum *
        ((q ^ (k + 1) : Real) : Complex) ^ (-s) := by
    rw [cpow_primeNorm_natPower q (zero_lt_one.trans hq)]
    exact sum_localEulerPowers A _ _ _
  rw [<- funext hTerms]
  exact hT s hs

open IsDedekindDomain NumberField in
/-- Apply the prime-power identity to the canonical local variable from a
finite-place uniformizer. -/
theorem hasSum_canonicalRamifiedPrimePowerCoefficients_rightHalfPlane
    {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K))
    (u : Units (p.adicCompletion K))
    (hu : Valued.v u.val = finiteUniformizerValue)
    (D : Polynomial Complex) (hD : D.eval 0 = 1) (delta : Real) :
    let q : Real := dedekindPrimeNorm K p
    let A := D.roots.map (fun r => Inv.inv r * (q : Complex) ^ (-(delta : Complex)))
    let L (s : Complex) := Inv.inv (D.eval ((norm u.val : Complex) ^ (s + (delta : Complex))))
    exists T : Real, forall s : Complex, T < s.re ->
      HasSum (fun k : Nat => (Real.log q : Complex) * (A.map (fun a => a ^ (k + 1))).sum *
          ((q ^ (k + 1) : Real) : Complex) ^ (-s))
        (-logDeriv L s) := by
  intro q A L
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast one_lt_dedekindPrimeNorm K p
  have hNorm : norm u.val = Inv.inv q := norm_eq_inv_of_valuation_finiteUniformizer p u.val hu
  have hL : (fun s : Complex => Inv.inv (D.eval ((q : Complex) ^ (-(s + (delta : Complex)))))) =
      L := by
    funext s
    dsimp only [L]
    rw [hNorm, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (zero_lt_one.trans hq).le,
      <- Complex.cpow_neg]
  rw [<- hL]
  exact hasSum_canonicalLocalPrimePowerCoefficients_rightHalfPlane D hD q delta hq

end Robin1984.GRH
