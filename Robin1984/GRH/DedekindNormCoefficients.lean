import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Robin1984.GRH.DedekindLogDerivative
import Robin1984.GRH.PrimeIdealChebyshev

/-!
# Dedekind coefficients indexed by natural norms

Aggregate the logarithmic derivative's prime-power terms over the
finite fibers of the absolute norm. The nonnegative coefficient
sequence has partial sums exactly equal to the Chebyshev function.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The natural-index Dirichlet series of the negative logarithmic derivative of Dedekind zeta.
- Formalization note: Reindex the absolutely convergent prime-power series by finite norm fibers and use the same reindexing for partial sums.
- PROVENANCE-END
-/

open IsDedekindDomain NumberField

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "PP" => Prod P Nat

/-- Prime ideal powers with the indicated absolute norm. -/
noncomputable def powersOfNorm (n : Nat) : Finset PP :=
  (primePowersUpTo K n).filter (fun pn => dedekindPrimePowerNorm K pn = n)

theorem mem_powersOfNorm {n : Nat} {pn : PP} :
    Iff (Membership.mem (powersOfNorm K n) pn) (dedekindPrimePowerNorm K pn = n) := by
  constructor
  case mp =>
    intro h
    exact (Finset.mem_filter.mp h).2
  case mpr =>
    intro h
    exact Finset.mem_filter.mpr (And.intro ((mem_primePowersUpTo K).mpr h.le) h)

/-- The coefficient at a natural number is the sum of the base-prime
logarithms over prime ideal powers of that norm. -/
noncomputable def dedekindNormCoeff (n : Nat) : Real :=
  (powersOfNorm K n).sum (fun pn => Real.log (dedekindPrimeNorm K pn.1 : Real))

private theorem one_lt_primeNorm_real (p : P) : (1 : Real) < dedekindPrimeNorm K p := by
  exact_mod_cast one_lt_dedekindPrimeNorm K p

theorem dedekindNormCoeff_nonneg (n : Nat) : 0 <= dedekindNormCoeff K n :=
  Finset.sum_nonneg (fun pn _ => Real.log_nonneg (one_lt_primeNorm_real K pn.1).le)

theorem dedekindNormCoeff_eq_zero_of_le_one {n : Nat} (hn : n <= 1) :
    dedekindNormCoeff K n = 0 := by
  unfold dedekindNormCoeff
  apply Finset.sum_eq_zero
  intro pn hpn
  exfalso
  have hq := one_lt_dedekindPrimeNorm K pn.1
  have hPow : dedekindPrimeNorm K pn.1 <= dedekindPrimePowerNorm K pn := by
    unfold dedekindPrimePowerNorm
    simpa only [pow_one] using Nat.pow_le_pow_right hq.le (Nat.succ_pos pn.2)
  have hPos := hq.trans_le hPow
  rw [(mem_powersOfNorm K).mp hpn] at hPos
  exact (not_lt_of_ge hn) hPos

/-- Group a finite prime-power sum using any factor depending only on the norm. -/
theorem sum_primePowersUpTo_weighted_eq_sum_normCoeff (n : Nat) (weight : Nat -> Real) :
    (primePowersUpTo K n).sum
        (fun pn => weight (dedekindPrimePowerNorm K pn) *
          Real.log (dedekindPrimeNorm K pn.1 : Real)) =
      (Finset.range (n + 1)).sum (fun m => weight m * dedekindNormCoeff K m) := by
  classical
  let p := primePowersUpTo K n
  let g := dedekindPrimePowerNorm K
  let v := fun pn : PP => weight (g pn) * Real.log (dedekindPrimeNorm K pn.1 : Real)
  have hMaps : forall pn : PP, Membership.mem p pn -> Membership.mem (Finset.range (n + 1)) (g pn) :=
    fun pn hp => Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ((mem_primePowersUpTo K).mp hp))
  change p.sum v = _
  rw [<- Finset.sum_fiberwise_of_maps_to hMaps v]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hFiber : p.filter (fun pn => g pn = m) = powersOfNorm K m := by
    apply Finset.ext
    intro pn
    rw [Finset.mem_filter, mem_powersOfNorm]
    exact Iff.intro And.right
      (fun h => And.intro ((mem_primePowersUpTo K).mpr (h.le.trans hmn)) h)
  rw [hFiber, dedekindNormCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pn hpn
  change weight (dedekindPrimePowerNorm K pn) * Real.log (dedekindPrimeNorm K pn.1 : Real) = _
  rw [(mem_powersOfNorm K).mp hpn]

theorem dedekindChebyshev_eq_sum_normCoeff (x : Real) :
    dedekindChebyshev K x = (Finset.range (Nat.floor x + 1)).sum (dedekindNormCoeff K) := by
  unfold dedekindChebyshev
  simpa only [one_mul] using sum_primePowersUpTo_weighted_eq_sum_normCoeff K
    (Nat.floor x) (fun _ => 1)

theorem dedekindChebyshev_nonneg (x : Real) : 0 <= dedekindChebyshev K x := by
  rw [dedekindChebyshev_eq_sum_normCoeff]
  exact Finset.sum_nonneg (fun n _ => dedekindNormCoeff_nonneg K n)

theorem monotone_dedekindChebyshev : Monotone (dedekindChebyshev K) := by
  intro x y hxy
  rw [dedekindChebyshev_eq_sum_normCoeff, dedekindChebyshev_eq_sum_normCoeff]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right (Nat.floor_le_floor hxy) 1))
    (fun n _ _ => dedekindNormCoeff_nonneg K n)

private theorem primePowerTerm_log_real (pn : PP) (s : Complex) :
    dedekindPrimePowerTerm K pn.1 pn.2 s =
      (Real.log (dedekindPrimeNorm K pn.1 : Real) : Complex) *
        (dedekindPrimePowerNorm K pn : Complex) ^ (-s) := by
  unfold dedekindPrimePowerTerm dedekindPrimePowerNorm
  have h := Complex.ofReal_log (Nat.cast_nonneg (dedekindPrimeNorm K pn.1) :
    (0 : Real) <= dedekindPrimeNorm K pn.1)
  rw [Complex.ofReal_natCast] at h
  rw [h]

/-- Group an absolutely summable prime-power series by norm when its
factor apart from the base-prime logarithm depends only on that norm. -/
theorem hasSum_dedekindNormCoeff_mul {u : PP -> Complex} {v : Nat -> Complex} {A : Complex}
    (hu : HasSum u A)
    (hTerm : forall pn : PP, u pn = (Real.log (dedekindPrimeNorm K pn.1 : Real) : Complex) *
      v (dedekindPrimePowerNorm K pn)) :
    HasSum (fun n : Nat => (dedekindNormCoeff K n : Complex) * v n) A := by
  classical
  let g := dedekindPrimePowerNorm K
  have hSum := hu.tsum_fiberwise g
  have hEq : (fun n : Nat => tsum (fun pn : {p : PP // g p = n} => u pn.val)) =
      fun n : Nat => (dedekindNormCoeff K n : Complex) * v n := by
    funext n
    let carrier : Set PP := {pn | g pn = n}
    let _ : Fintype carrier :=
      Fintype.ofFinset (powersOfNorm K n) (fun _ => mem_powersOfNorm K)
    let w := fun pn : PP => (Real.log (dedekindPrimeNorm K pn.1 : Real) : Complex)
    have hFib : (fun pn : carrier => u pn.val) =
        fun pn : carrier => w pn.val * v n := by
      funext pn
      have hp : g pn.val = n := pn.property
      rw [hTerm]
      change w pn.val * v (g pn.val) = w pn.val * v n
      rw [hp]
    change tsum (fun pn : carrier => u pn.val) = (dedekindNormCoeff K n : Complex) * v n
    have hFiberSum : (Finset.univ.sum (fun pn : carrier => w pn.val)) = (powersOfNorm K n).sum w :=
      (Finset.sum_subtype (p := carrier) (powersOfNorm K n)
        (fun _ => mem_powersOfNorm K) w).symm
    rw [hFib, tsum_fintype, <- Finset.sum_mul, hFiberSum]
    congr 1
    unfold dedekindNormCoeff
    exact (map_sum Complex.ofRealHom _ _).symm
  rw [<- hEq]
  exact hSum

/-- The norm-indexed coefficient sequence has the actual Dedekind
negative logarithmic derivative as its L-series on the initial
half-plane. -/
theorem hasSum_dedekindNormCoeff {s : Complex} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (dedekindNormCoeff K n : Complex)) s
      (-deriv (dedekindZeta K) s / dedekindZeta K s) := by
  have hS : Not (s = 0) := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  change HasSum (LSeries.term (fun n => (dedekindNormCoeff K n : Complex)) s) _
  have hTerms : LSeries.term (fun n => (dedekindNormCoeff K n : Complex)) s =
      fun n : Nat => (dedekindNormCoeff K n : Complex) * (n : Complex) ^ (-s) := by
    funext n
    rw [LSeries.term_of_ne_zero' hS, div_eq_mul_inv, Complex.cpow_neg]
  rw [hTerms]
  exact hasSum_dedekindNormCoeff_mul K (hasSum_dedekindPrimePowerTerm K hs)
    (fun pn => primePowerTerm_log_real K pn s)

end Robin1984.GRH
