import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finsupp.Multiset
import Robin1984.GRH.DedekindIdealSeries
import Robin1984.GRH.DedekindPrimeFactorization
import Robin1984.GRH.FinsuppEulerProduct

/-!
# The Dedekind zeta Euler product

The ideal-norm series factors over the height-one prime ideals in its
half-plane of absolute convergence.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The prime-ideal Euler product for Dedekind zeta and the convergent complex logarithm of that product.
- Formalization note: The norm series is reindexed by prime-ideal exponents. Exponentiating the sum of local logarithms proves zero-freeness for real part greater than one.
- PROVENANCE-END
-/

open IsDedekindDomain NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)

/-- The absolute norm of a prime ideal occurring in the Euler product. -/
noncomputable def dedekindPrimeNorm (p : P) : Nat :=
  Ideal.absNorm p.asIdeal

theorem one_lt_dedekindPrimeNorm (p : P) : 1 < dedekindPrimeNorm K p := by
  have h0 : Not (dedekindPrimeNorm K p = 0) :=
    fun h => p.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Not (dedekindPrimeNorm K p = 1) :=
    fun h => p.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr h0) (Ne.symm h1)

private noncomputable def natCpowHom (s : Complex) : MonoidHom Nat Complex where
  toFun n := (n : Complex) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

private noncomputable def primeNormWeight (s : Complex) (p : P) : Complex :=
  (dedekindPrimeNorm K p : Complex) ^ (-s)

private theorem norm_primeNormWeight_lt_one {s : Complex} (hs : 1 < s.re) (p : P) :
    norm (primeNormWeight K s p) < 1 := by
  have hp : (1 : Real) < (dedekindPrimeNorm K p : Real) := by
    exact_mod_cast one_lt_dedekindPrimeNorm K p
  unfold primeNormWeight
  rw [<- Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hp),
    Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (neg_lt_zero.mpr (zero_lt_one.trans hs))

private noncomputable def primeExponentIdealEquiv [DecidableEq P] :
    Equiv (Finsupp P Nat) (NonzeroIntegralIdeal K) :=
  Multiset.toFinsupp.toEquiv.symm.trans primeMultisetIdealEquiv

private theorem primeExponentIdealWeight [DecidableEq P] (s : Complex) (e : Finsupp P Nat) :
    exponentWeight (primeNormWeight K s) e =
      (Ideal.absNorm (primeExponentIdealEquiv K e).val : Complex) ^ (-s) := by
  let f : MonoidHom (Ideal (RingOfIntegers K)) Complex :=
    (natCpowHom s).comp Ideal.absNorm.toMonoidHom
  change exponentWeight (primeNormWeight K s) e =
    f (primeMultisetIdealEquiv e.toMultiset).val
  rw [primeMultisetIdealEquiv_apply_val, map_multiset_prod, Multiset.map_map]
  change exponentWeight (primeNormWeight K s) e = (e.toMultiset.map (primeNormWeight K s)).prod
  rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index pow_zero pow_add]
  rfl

/-- Mathlib's Dedekind zeta series is the convergent product of its prime-ideal
Euler factors at every point with real part greater than one. -/
theorem hasProd_dedekindZeta_eulerFactors {s : Complex} (hs : 1 < s.re) :
    HasProd (fun p : P => Inv.inv (1 - (dedekindPrimeNorm K p : Complex) ^ (-s)))
      (dedekindZeta K s) := by
  classical
  let e := primeExponentIdealEquiv K
  have hNorm := (e.summable_iff).mpr (summable_norm_dedekindIdealTerm K hs)
  have hWeight : Summable (fun a : Finsupp P Nat => norm (exponentWeight (primeNormWeight K s) a)) :=
    hNorm.congr (fun a => congrArg norm (primeExponentIdealWeight K s a).symm)
  have hProd := hasProd_eulerFactors_of_exponentWeight (primeNormWeight K s)
    (norm_primeNormWeight_lt_one K hs) hWeight
  rw [dedekindZeta_eq_tsum_idealNorm K hs, <- e.tsum_eq]
  have hSumEq : (tsum (fun a : Finsupp P Nat => (Ideal.absNorm (e a).val : Complex) ^ (-s))) =
      tsum (exponentWeight (primeNormWeight K s)) :=
    tsum_congr (fun a => (primeExponentIdealWeight K s a).symm)
  rwa [<- hSumEq] at hProd

/-- The prime-ideal terms are absolutely summable in the same half-plane
as the ideal-norm series. -/
theorem summable_dedekindPrimeNormWeight {s : Complex} (hs : 1 < s.re) :
    Summable (fun p : P => norm ((dedekindPrimeNorm K p : Complex) ^ (-s))) := by
  let i : P -> NonzeroIntegralIdeal K := fun p => Subtype.mk p.asIdeal p.ne_bot
  have hInjective : Function.Injective i := by
    intro p q h
    apply HeightOneSpectrum.ext
    exact congrArg (fun a : NonzeroIntegralIdeal K => a.val) h
  let w : NonzeroIntegralIdeal K -> Real :=
    fun a => norm ((Ideal.absNorm a.val : Complex) ^ (-s))
  have hw : Summable w := summable_norm_dedekindIdealTerm K hs
  change Summable (Function.comp w i)
  exact hw.comp_injective hInjective

/-- The exponential representation of the Dedekind zeta Euler product
uses the principal logarithm of each Euler denominator. -/
theorem dedekindZeta_eq_exp_tsum_log_eulerFactors {s : Complex} (hs : 1 < s.re) :
    dedekindZeta K s =
      Complex.exp (tsum (fun p : P => -Complex.log (1 - (dedekindPrimeNorm K p : Complex) ^ (-s)))) := by
  let a := primeNormWeight K s
  have haSum : Summable a := summable_norm_iff.mp (summable_dedekindPrimeNormWeight K hs)
  have hLog : Summable (fun p => Complex.log (1 - a p)) := by
    simpa only [sub_eq_add_neg] using Complex.summable_log_one_add_of_summable haSum.neg
  have hNonzero (p : P) : Not (1 - a p = 0) := by
    intro h
    have hp := norm_primeNormWeight_lt_one K hs p
    have hOne : a p = 1 := (sub_eq_zero.mp h).symm
    change norm (a p) < 1 at hp
    rw [hOne, norm_one] at hp
    exact (lt_irrefl (1 : Real)) hp
  have hProd : HasProd (fun p => Inv.inv (1 - a p))
      (Complex.exp (tsum (fun p => -Complex.log (1 - a p)))) := by
    have hF : (fun p : P => Complex.exp (-Complex.log (1 - a p))) =
        (fun p : P => Inv.inv (1 - a p)) := by
      funext p
      rw [Complex.exp_neg, Complex.exp_log (hNonzero p)]
    have hExp : HasProd (fun p : P => Complex.exp (-Complex.log (1 - a p)))
        (Complex.exp (tsum (fun p => -Complex.log (1 - a p)))) :=
      hLog.neg.hasSum.cexp
    rwa [hF] at hExp
  exact (hasProd_dedekindZeta_eulerFactors K hs).unique hProd

/-- Zero-freeness of Dedekind zeta to the right of the line of convergence. -/
theorem dedekindZeta_ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) :
    Not (dedekindZeta K s = 0) := by
  rw [dedekindZeta_eq_exp_tsum_log_eulerFactors K hs]
  exact Complex.exp_ne_zero _

end Robin1984.GRH
