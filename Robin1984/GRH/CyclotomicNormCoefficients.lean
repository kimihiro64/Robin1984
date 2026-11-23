import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Robin1984.GRH.CyclotomicCharacterCoefficients
import Robin1984.GRH.CyclotomicPrimeDecomposition
import Robin1984.GRH.DedekindNormCoefficients

/-!
# Cyclotomic prime-power norm coefficients

At a rational prime power the Dedekind coefficient is the sum over primes
above the rational base prime. Each contributes precisely when the inertia
degree divides the exponent, and the degree cancels against the prime count.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The logarithmic derivative of the cyclotomic Euler factors.
- Formalization note: Reindex the finite norm fiber by the primes over its rational base prime.
- Content basis: Norm powers, contraction to the integers, and cyclotomic prime decomposition.
- Dependency status: Optional GRH extension and existing Mathlib APIs.
-/

open Ideal IsDedekindDomain NumberField

namespace Robin1984.GRH

private theorem primeNorm_eq_rationalPrimePower (K : Type*) [Field K] [NumberField K]
    (I : HeightOneSpectrum (RingOfIntegers K)) :
    let q := Ideal.absNorm (I.asIdeal.under Int)
    And q.Prime
      (And (I.asIdeal.under Int = Ideal.span ({(q : Int)} : Set Int))
        (And (dedekindPrimeNorm K I = q ^ I.asIdeal.inertiaDeg Int)
          (0 < I.asIdeal.inertiaDeg Int))) := by
  let q := Ideal.absNorm (I.asIdeal.under Int)
  letI : NeZero I.asIdeal := NeZero.mk I.ne_bot
  have hPrime : q.Prime := Nat.absNorm_under_prime I.asIdeal
  have hSpan : Ideal.span ({(q : Int)} : Set Int) = I.asIdeal.under Int :=
    Int.ideal_span_absNorm_eq_self _
  letI : I.asIdeal.LiesOver (Ideal.span ({(q : Int)} : Set Int)) := by
    rw [hSpan]
    infer_instance
  have hNorm : dedekindPrimeNorm K I = q ^ I.asIdeal.inertiaDeg Int := by
    change Ideal.absNorm I.asIdeal = _
    simpa only [Int.natAbs_natCast] using (Ideal.natAbs_pow_inertiaDeg (q : Int) I.asIdeal).symm
  have hDeg : 0 < I.asIdeal.inertiaDeg Int := by
    apply Nat.pos_of_ne_zero
    intro h
    have hn := one_lt_dedekindPrimeNorm K I
    rw [hNorm, h, pow_zero] at hn
    exact (lt_irrefl _) hn
  exact And.intro hPrime (And.intro hSpan.symm (And.intro hNorm hDeg))

/-- At `p ^ l` with `l > 0`, the cyclotomic logarithmic coefficient is
`totient d * log p` if the inertia degree divides `l`, and zero otherwise. -/
theorem dedekindNormCoeff_cyclotomic_primePower {m d p k l : Nat} [NeZero m] [NeZero d]
    (hp : Nat.Prime p) (hm : m = p ^ k * d) (hpd : Not (Dvd.dvd p d)) (hl : 0 < l) :
    let f := orderOf (p : ZMod d)
    dedekindNormCoeff (CyclotomicField m Rat) (p ^ l) =
      if Dvd.dvd f l then (d.totient : Real) * Real.log (p : Real) else 0 := by
  classical
  let K := CyclotomicField m Rat
  let R := RingOfIntegers K
  let P := HeightOneSpectrum R
  let q : Ideal Int := Ideal.span ({(p : Int)} : Set Int)
  let S := q.primesOver R
  let f := orderOf (p : ZMod d)
  let E := powersOfNorm K (p ^ l)
  have hpZ : Prime (p : Int) := Nat.prime_iff_prime_int.mp hp
  letI : q.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hSplit := cyclotomic_primesOver_norm_and_count hp hm hpd
  have hCount : S.ncard * f = d.totient := hSplit.1
  have hNorm (I : Ideal R) (hI : Membership.mem S I) : Ideal.absNorm I = p ^ f :=
    hSplit.2 I hI
  have hf : 0 < f := by
    apply Nat.pos_of_ne_zero
    intro h
    have hd := Nat.totient_pos.mpr (NeZero.pos d)
    rw [<- hCount, h, Nat.mul_zero] at hd
    exact (lt_irrefl _) hd
  have hAtPrime (i : Prod P Nat) (hi : Membership.mem E i) :
      And (Membership.mem S i.1.asIdeal) (f * (i.2 + 1) = l) := by
    let b := Ideal.absNorm (i.1.asIdeal.under Int)
    have h := primeNorm_eq_rationalPrimePower K i.1
    have hQ : b.Prime := h.1
    have hUnder : i.1.asIdeal.under Int = Ideal.span ({(b : Int)} : Set Int) := h.2.1
    have hPow : dedekindPrimeNorm K i.1 = b ^ i.1.asIdeal.inertiaDeg Int := h.2.2.1
    have he : 0 < i.1.asIdeal.inertiaDeg Int * (i.2 + 1) :=
      Nat.mul_pos h.2.2.2 (Nat.succ_pos _)
    have hPN := (mem_powersOfNorm K).mp hi
    change dedekindPrimeNorm K i.1 ^ (i.2 + 1) = p ^ l at hPN
    have hDiv : Dvd.dvd b (p ^ l) := by
      rw [<- hPN, hPow, <- pow_mul]
      exact dvd_pow_self b he.ne'
    have hBp : b = p := Nat.prime_eq_prime_of_dvd_pow hQ hp hDiv
    have hOver : Membership.mem S i.1.asIdeal := by
      change And i.1.asIdeal.IsPrime (i.1.asIdeal.LiesOver q)
      refine And.intro i.1.isPrime ?_
      have hu : i.1.asIdeal.under Int = q := by rw [hUnder, hBp]
      rw [<- hu]
      infer_instance
    have hN : dedekindPrimeNorm K i.1 = p ^ f := hNorm _ hOver
    rw [hN, <- pow_mul] at hPN
    exact And.intro hOver (Nat.pow_right_injective (Nat.succ_le_of_lt hp.one_lt) hPN)
  change E.sum (fun i => Real.log (dedekindPrimeNorm K i.1 : Real)) =
    if Dvd.dvd f l then (d.totient : Real) * Real.log (p : Real) else 0
  by_cases hDiv : Dvd.dvd f l
  case neg =>
    have hEmpty : E = Finset.empty := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hDiv (Exists.intro (i.2 + 1) (hAtPrime i hi).2.symm)
    rw [hEmpty, if_neg hDiv]
    exact Finset.sum_empty
  case pos =>
    choose b hb using hDiv
    have hb0 : 0 < b := Nat.pos_of_ne_zero (fun h => hl.ne' (by simpa only [h, Nat.mul_zero] using hb))
    have hb1 : b - 1 + 1 = b := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hb0)
    have hFinite : S.Finite := Algebra.QuasiFinite.finite_primesOver q
    let FS := hFinite.toFinset
    have hFS (I : Ideal R) : Iff (Membership.mem FS I) (Membership.mem S I) :=
      Set.Finite.mem_toFinset _
    have hSum :
        E.sum (fun i => Real.log (dedekindPrimeNorm K i.1 : Real)) =
          FS.sum (fun _ => (f : Real) * Real.log (p : Real)) := by
      refine Finset.sum_bij (fun i _ => i.1.asIdeal) ?hi ?i_inj ?i_surj ?h
      case hi =>
        intro i hi
        exact (hFS _).mpr (hAtPrime i hi).1
      case i_inj =>
        intro i hi j hj hij
        have hFirst := HeightOneSpectrum.ext hij
        have hSecond := Nat.eq_of_mul_eq_mul_left hf ((hAtPrime i hi).2.trans (hAtPrime j hj).2.symm)
        exact Prod.ext hFirst (Nat.add_right_cancel hSecond)
      case i_surj =>
        intro I hI
        have hOver := (hFS I).mp hI
        have hNoBot : Not (I = 0) := by
          intro h
          have hNormZero : Ideal.absNorm I = 0 := Ideal.absNorm_eq_zero_iff.mpr h
          exact (pow_ne_zero f hp.ne_zero) ((hNorm I hOver).symm.trans hNormZero)
        let J : P := HeightOneSpectrum.mk I hOver.1 hNoBot
        refine Exists.intro (J, b - 1) (Exists.intro ((mem_powersOfNorm K).mpr ?_) rfl)
        change (Ideal.absNorm I) ^ (b - 1 + 1) = p ^ l
        rw [hNorm I hOver, hb1, <- pow_mul, <- hb]
      case h =>
        intro i hi
        have hN : dedekindPrimeNorm K i.1 = p ^ f := hNorm _ (hAtPrime i hi).1
        rw [hN, Nat.cast_pow, Real.log_pow]
    have hDivisible : Dvd.dvd f l := Exists.intro b hb
    rw [hSum, if_pos hDivisible, Finset.sum_const, nsmul_eq_mul]
    have hCard : (FS.card : Real) * (f : Real) = (d.totient : Real) := by
      have hNat := hCount
      rw [Set.ncard_eq_toFinset_card S hFinite] at hNat
      exact_mod_cast hNat
    rw [<- mul_assoc, hCard]

/-- The Dedekind logarithmic coefficients of the cyclotomic field are the
sum of the logarithmic coefficients of the associated primitive characters. -/
theorem cyclotomicNormCoeff_eq_sum_primitiveCharacter_vonMangoldt
    (m n : Nat) [NeZero m] :
    (dedekindNormCoeff (CyclotomicField m Rat) n : Complex) =
      (Finset.univ.sum (fun chi : DirichletCharacter Complex m =>
        chi.primitiveCharacter (n : Int))) *
      (ArithmeticFunction.vonMangoldt n : Complex) := by
  classical
  by_cases primePower : IsPrimePow n
  case pos =>
    choose p k hp hk hpk using (isPrimePow_nat_iff n).mp primePower
    subst n
    let d := m / p ^ m.factorization p
    let f := orderOf (p : ZMod d)
    letI : NeZero d := NeZero.mk (Nat.ordCompl_pos p (NeZero.ne m)).ne'
    have hm : m = p ^ m.factorization p * d := calc
      _ = d * p ^ m.factorization p := (Nat.div_mul_cancel (Nat.ordProj_dvd m p)).symm
      _ = _ := mul_comm _ _
    have hpd : Not (Dvd.dvd p d) := Nat.not_dvd_ordCompl hp (NeZero.ne m)
    have hR := dedekindNormCoeff_cyclotomic_primePower hp hm hpd hk
    change dedekindNormCoeff (CyclotomicField m Rat) (p ^ k) =
      (if Dvd.dvd f k then (d.totient : Real) * Real.log (p : Real) else 0) at hR
    have hChars :
        (Finset.univ.sum (fun chi : DirichletCharacter Complex m =>
          chi.primitiveCharacter ((p ^ k : Nat) : Int))) =
          if Dvd.dvd f k then (d.totient : Complex) else 0 := calc
      _ = Finset.univ.sum (fun chi : DirichletCharacter Complex m =>
        (chi.primitiveCharacter (p : Int)) ^ k) := by
        apply Finset.sum_congr rfl
        intro chi _
        rw [Nat.cast_pow, Int.cast_pow, map_pow]
      _ = _ := sum_primitiveCharacter_primePower m p k hp hk
    rw [hR, hChars, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    by_cases hfd : Dvd.dvd f k <;> simp [hfd]
  case neg =>
    let K := CyclotomicField m Rat
    have hEmpty : powersOfNorm K n = Finset.empty := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      let p := Ideal.absNorm (i.1.asIdeal.under Int)
      let e := i.1.asIdeal.inertiaDeg Int * (i.2 + 1)
      have hp := primeNorm_eq_rationalPrimePower K i.1
      have hn := (mem_powersOfNorm K).mp hi
      change dedekindPrimeNorm K i.1 ^ (i.2 + 1) = n at hn
      rw [hp.2.2.1, <- pow_mul] at hn
      exact primePower ((isPrimePow_nat_iff n).mpr
        (Exists.intro p (Exists.intro e (And.intro hp.1
          (And.intro (Nat.mul_pos hp.2.2.2 (Nat.succ_pos _)) hn)))))
    have hCoeff : dedekindNormCoeff K n = 0 := by
      unfold dedekindNormCoeff
      rw [hEmpty]
      exact Finset.sum_empty
    rw [hCoeff, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr primePower]
    simp


end Robin1984.GRH
