import Robin1984.GRH.DedekindTriangular

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Rankin--Selberg logarithmic coefficients and absolute convergence of the Dedekind zeta logarithmic derivative.
- Formalization note: Derives individual and paired logarithmic-derivative summability from the unramified Rankin--Selberg bound and a local parameter bound at finitely many ramified primes.
- PROVENANCE-END
-/

/-!
# Absolute convergence of standard prime-power coefficients

The individual and paired prime-power coefficients are dominated by the
Dedekind and Rankin--Selberg coefficients. At the finitely many ramified
places, a geometric series supplies the required summability directly.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open IsDedekindDomain NumberField
open scoped Classical

private abbrev RankinSelbergPrimePower (K : Type*) [Field K] [NumberField K] :=
  Prod (HeightOneSpectrum (RingOfIntegers K)) Nat

private theorem summable_dedekindPrimePowerLogWeight
    (K : Type*) [Field K] [NumberField K] (r : Real) (hr : 1 < r) :
    Summable (fun p : RankinSelbergPrimePower K =>
      Real.log (dedekindPrimeNorm K p.1 : Real) * (dedekindPrimePowerNorm K p : Real) ^ (-r)) := by
  have hs : 1 < (r : Complex).re := by simpa only [Complex.ofReal_re] using hr
  refine (summable_norm_dedekindPrimePowerTerm K hs).congr ?_
  intro p
  have hp : 1 < (dedekindPrimeNorm K p.1 : Real) := by
    exact_mod_cast one_lt_dedekindPrimeNorm K p.1
  have hq : 0 < (dedekindPrimePowerNorm K p : Real) := by
    unfold dedekindPrimePowerNorm
    rw [Nat.cast_pow]
    exact pow_pos (zero_lt_one.trans hp) _
  change norm (Complex.log (dedekindPrimeNorm K p.1 : Complex) *
    (dedekindPrimePowerNorm K p : Complex) ^ (-(r : Complex))) = _
  simp only [<- Complex.ofReal_natCast]
  rw [<- Complex.ofReal_log (zero_lt_one.trans hp).le, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_nonneg hp.le), Complex.norm_cpow_eq_rpow_re_of_pos hq,
    Complex.neg_re, Complex.ofReal_re]

/-- The positive Rankin--Selberg coefficient bound gives absolute
convergence for both the individual and paired standard logarithmic
derivatives. The input is the power trace at each prime ideal power. -/
theorem summable_standardPrimePowerCoefficients_of_rankinSelberg
    (K : Type*) [Field K] [NumberField K] (A : RankinSelbergPrimePower K -> Complex)
    (r : Real) (hr : 1 < r)
    (hRankin : Summable (fun p : RankinSelbergPrimePower K =>
      norm (A p) ^ 2 * (Real.log (dedekindPrimeNorm K p.1 : Real) *
        (dedekindPrimePowerNorm K p : Real) ^ (-r)))) :
    And
      (Summable (fun p : RankinSelbergPrimePower K =>
        norm (A p * (Real.log (dedekindPrimeNorm K p.1 : Real) : Complex)) *
          (dedekindPrimePowerNorm K p : Real) ^ (-r)))
      (Summable (fun p : RankinSelbergPrimePower K =>
        norm (2 * (A p).re * Real.log (dedekindPrimeNorm K p.1 : Real)) *
          (dedekindPrimePowerNorm K p : Real) ^ (-r))) := by
  let P := RankinSelbergPrimePower K
  let ell (p : P) := Real.log (dedekindPrimeNorm K p.1 : Real)
  let q (p : P) : Real := dedekindPrimePowerNorm K p
  let w (p : P) := ell p * (q p) ^ (-r)
  let rankinWeight (p : P) := norm (A p) ^ 2 * w p
  have hEll (p : P) : 0 <= ell p := by
    have h : 1 <= (dedekindPrimeNorm K p.1 : Real) := by
      exact_mod_cast (one_lt_dedekindPrimeNorm K p.1).le
    exact Real.log_nonneg h
  have hq (p : P) : 0 <= (q p) ^ (-r) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hw (p : P) : 0 <= w p := mul_nonneg (hEll p) (hq p)
  have hZeta : Summable w := summable_dedekindPrimePowerLogWeight K r hr
  have hR : Summable rankinWeight := hRankin
  have hBoth : Summable (fun p => w p + rankinWeight p) := hZeta.add hR
  have hHalf : Summable (fun p => (w p + rankinWeight p) / 2) := hBoth.div_const 2
  have hBound (p : P) : norm (A p) <= (1 + norm (A p) ^ 2) / 2 := by
    nlinarith only [sq_nonneg (norm (A p) - 1)]
  constructor
  . refine Summable.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (hq p)) ?_ hHalf
    intro p
    change norm (A p * (ell p : Complex)) * (q p) ^ (-r) <= _
    calc
      _ = norm (A p) * w p := by
        dsimp only [w]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hEll p), mul_assoc]
      _ <= ((1 + norm (A p) ^ 2) / 2) * w p :=
        mul_le_mul_of_nonneg_right (hBound p) (hw p)
      _ = _ := by dsimp only [rankinWeight]; ring
  . refine Summable.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (hq p)) ?_ hBoth
    intro p
    change norm (2 * (A p).re * ell p) * (q p) ^ (-r) <= _
    have hPair : 2 * abs (A p).re <= 1 + norm (A p) ^ 2 := by
      linarith only [Complex.abs_re_le_norm (A p), hBound p]
    calc
      _ = (2 * abs (A p).re) * w p := by
        dsimp only [w]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (zero_le_two : (0 : Real) <= 2),
          abs_of_nonneg (hEll p), mul_assoc]
      _ <= (1 + norm (A p) ^ 2) * w p := mul_le_mul_of_nonneg_right hPair (hw p)
      _ = _ := by dsimp only [rankinWeight]; ring

/-- The finitely many ramified primes give a convergent geometric tail.
The unramified Rankin--Selberg bound then gives the individual and
paired logarithmic-derivative summability for the full prime-power
families. Zero entries may pad the local parameter list. -/
theorem summable_standardSatakeCoefficients_of_unramified_rankinSelberg
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (alpha : HeightOneSpectrum (RingOfIntegers K) -> Fin n -> Complex)
    (R : Finset (HeightOneSpectrum (RingOfIntegers K))) (r : Real) (hr : 1 < r)
    (hRamified : forall p, Membership.mem R p -> forall i,
      norm (alpha p i) <= Real.sqrt (dedekindPrimeNorm K p : Real)) :
    let A (p : RankinSelbergPrimePower K) := Finset.univ.sum (fun i => (alpha p.1 i) ^ (p.2 + 1))
    let Q (p : RankinSelbergPrimePower K) : Real := dedekindPrimePowerNorm K p
    let E (p : RankinSelbergPrimePower K) := Real.log (dedekindPrimeNorm K p.1 : Real)
    Summable (fun p : RankinSelbergPrimePower K =>
      if Membership.mem R p.1 then 0 else norm (A p) ^ 2 * (E p * (Q p) ^ (-r))) ->
    And (Summable (fun p : RankinSelbergPrimePower K =>
        norm (A p * (E p : Complex)) * (Q p) ^ (-r)))
      (Summable (fun p : RankinSelbergPrimePower K =>
        norm (2 * (A p).re * E p) * (Q p) ^ (-r))) := by
  intro A Q E hUnramified
  let P := HeightOneSpectrum (RingOfIntegers K)
  let N (p : P) : Real := dedekindPrimeNorm K p
  let B (p : P) := (N p) ^ (1 - r)
  let W (p : RankinSelbergPrimePower K) := norm (A p) ^ 2 * (E p * (Q p) ^ (-r))
  let C (p : P) := (n : Real) ^ 2 * Real.log (N p)
  let Bad (p : RankinSelbergPrimePower K) := if Membership.mem R p.1 then W p else 0
  let Major (p : RankinSelbergPrimePower K) :=
    if Membership.mem R p.1 then C p.1 * (B p.1) ^ (p.2 + 1) else 0
  have hN (p : P) : 1 < N p := by
    change 1 < (dedekindPrimeNorm K p : Real)
    exact_mod_cast one_lt_dedekindPrimeNorm K p
  have hP (p : P) : 0 < N p := zero_lt_one.trans (hN p)
  have hE (p : RankinSelbergPrimePower K) : 0 <= E p := Real.log_nonneg (hN p.1).le
  have hQ (p : RankinSelbergPrimePower K) : 0 < Q p := by
    dsimp only [Q]
    unfold dedekindPrimePowerNorm
    rw [Nat.cast_pow]
    exact pow_pos (hP p.1) _
  have hB0 (p : P) : 0 <= B p := Real.rpow_nonneg (hP p).le _
  have hB1 (p : P) : B p < 1 := Real.rpow_lt_one_of_one_lt_of_neg (hN p) (by linarith)
  have hC (p : P) : 0 <= C p := mul_nonneg (sq_nonneg _) (Real.log_nonneg (hN p).le)
  have hMajor0 : 0 <= Major := by
    intro p
    unfold Major
    split
    . exact mul_nonneg (hC p.1) (pow_nonneg (hB0 p.1) _)
    . exact le_rfl
  have hMajorSum : Summable Major := by
    apply (summable_prod_of_nonneg hMajor0).mpr
    constructor
    . intro p
      by_cases hp : Membership.mem R p
      . have hg := (summable_geometric_of_lt_one (hB0 p) (hB1 p)).mul_right (B p)
        have h := hg.mul_left (C p)
        simpa only [Major, if_pos hp, pow_succ] using h
      . simp only [Major, if_neg hp]
        exact summable_zero
    . refine summable_of_ne_finset_zero (s := R) ?_
      intro p hp
      simp only [Major, if_neg hp, tsum_zero]
  have hAbs (p : RankinSelbergPrimePower K) (hp : Membership.mem R p.1) :
      norm (A p) ^ 2 <= (n : Real) ^ 2 * Q p := by
    let u := Real.sqrt (N p.1)
    have hu (i : Fin n) : norm ((alpha p.1 i) ^ (p.2 + 1)) <= u ^ (p.2 + 1) := by
      rw [norm_pow]
      have hx : norm (alpha p.1 i) ^ ((p.2 + 1 : Nat) : Real) <=
          u ^ ((p.2 + 1 : Nat) : Real) :=
        Real.rpow_le_rpow (norm_nonneg _) (hRamified p.1 hp i) (Nat.cast_nonneg _)
      simpa only [Real.rpow_natCast] using hx
    have hTrace : norm (A p) <= (n : Real) * u ^ (p.2 + 1) := by
      calc
        _ <= Finset.univ.sum (fun i : Fin n => norm ((alpha p.1 i) ^ (p.2 + 1))) := norm_sum_le _ _
        _ <= Finset.univ.sum (fun _ : Fin n => u ^ (p.2 + 1)) := Finset.sum_le_sum (fun i _ => hu i)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hSq : (u ^ (p.2 + 1)) ^ 2 = Q p := by
      calc
        _ = (u ^ 2) ^ (p.2 + 1) := by
          rw [<- pow_mul, <- pow_mul, Nat.mul_comm (p.2 + 1) 2]
        _ = Q p := by
          dsimp only [u, Q, N, dedekindPrimePowerNorm]
          rw [Real.sq_sqrt (hP p.1).le, Nat.cast_pow]
    calc
      _ <= ((n : Real) * u ^ (p.2 + 1)) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_le_mul hTrace hTrace (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))
      _ = _ := by rw [mul_pow, hSq]
  have hPower (p : RankinSelbergPrimePower K) :
      Q p * (Q p) ^ (-r) = (B p.1) ^ (p.2 + 1) := by
    calc
      _ = (Q p) ^ (1 : Real) * (Q p) ^ (-r) := by rw [Real.rpow_one]
      _ = (Q p) ^ (1 - r) := by
        rw [sub_eq_add_neg]
        exact (Real.rpow_add (hQ p) _ _).symm
      _ = ((N p.1) ^ (p.2 + 1)) ^ (1 - r) := by
        dsimp only [Q, N, dedekindPrimePowerNorm]
        rw [Nat.cast_pow]
      _ = (N p.1) ^ (((p.2 + 1 : Nat) : Real) * (1 - r)) :=
        (Real.rpow_natCast_mul (hP p.1).le _ _).symm
      _ = (B p.1) ^ (p.2 + 1) := by
        rw [mul_comm ((p.2 + 1 : Nat) : Real)]
        exact Real.rpow_mul_natCast (hP p.1).le _ _
  have hW0 (p : RankinSelbergPrimePower K) : 0 <= W p :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (hE p) (Real.rpow_nonneg (hQ p).le _))
  have hBad : Summable Bad := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hMajorSum
    . by_cases hp : Membership.mem R p.1
      . simpa only [Bad, if_pos hp] using hW0 p
      . simp only [Bad, if_neg hp, le_refl]
    . by_cases hp : Membership.mem R p.1
      . simp only [Bad, Major, if_pos hp]
        calc
          W p <= ((n : Real) ^ 2 * Q p) * (E p * (Q p) ^ (-r)) :=
            mul_le_mul_of_nonneg_right (hAbs p hp)
              (mul_nonneg (hE p) (Real.rpow_nonneg (hQ p).le _))
          _ = C p.1 * (Q p * (Q p) ^ (-r)) := by dsimp only [C, E, N]; ring
          _ = _ := by rw [hPower]
      . simp only [Bad, Major, if_neg hp, le_refl]
  have hAll : Summable W := (hUnramified.add hBad).congr (fun p => by
    by_cases hp : Membership.mem R p.1
    . simp only [W, Bad, if_pos hp, zero_add]
    . simp only [W, Bad, if_neg hp, add_zero])
  exact summable_standardPrimePowerCoefficients_of_rankinSelberg K A r hr hAll

end Robin1984.GRH
