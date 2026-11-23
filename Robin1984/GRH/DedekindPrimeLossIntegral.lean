import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Robin1984.GRH.PrimeIdealChebyshev

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Partial summation for the reciprocal-square tail of the prime-ideal Chebyshev measure.
- Formalization note: Integrate the positive inverse-cube kernel against the finite prime counting sum, then bound that sum by the actual Chebyshev function.
- PROVENANCE-END
-/

/-!
# A reciprocal-square bound for Dedekind prime ideals

The finite prime log sum is bounded by the Chebyshev sum over all prime
powers. An exact improper integral turns this comparison into the
large-prime part of the cutoff ideal's geometric truncation error.
-/

open IsDedekindDomain MeasureTheory NumberField Set

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "PP" => Prod P Nat

theorem sum_primeNormLog_le_dedekindChebyshev (B : Finset P) {t : Real} (ht : 0 <= t)
    (hB : forall p, Membership.mem B p -> (dedekindPrimeNorm K p : Real) <= t) :
    B.sum (fun p => Real.log (dedekindPrimeNorm K p : Real)) <= dedekindChebyshev K t := by
  classical
  let e : Function.Embedding P PP :=
    { toFun := fun p => (p, 0)
      inj' := fun _ _ h => congrArg Prod.fst h }
  have hSub : forall pn : PP, Membership.mem (B.map e) pn ->
      Membership.mem (primePowersUpTo K (Nat.floor t)) pn := by
    intro pn hpn
    have h := Finset.mem_map.mp hpn
    choose p hp using h
    have hNorm : dedekindPrimeNorm K p <= Nat.floor t := (Nat.le_floor_iff ht).mpr (hB p hp.1)
    apply (mem_primePowersUpTo K).mpr
    rw [<- hp.2]
    change dedekindPrimeNorm K p ^ (1 : Nat) <= Nat.floor t
    simpa only [pow_one] using hNorm
  unfold dedekindChebyshev
  let w (pn : PP) : Real := Real.log (dedekindPrimeNorm K pn.1 : Real)
  have hSum : (B.map e).sum w <= (primePowersUpTo K (Nat.floor t)).sum w :=
    Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun pn _ _ => Real.log_nonneg (by exact_mod_cast (one_lt_dedekindPrimeNorm K pn.1).le))
  rw [Finset.sum_map] at hSum
  exact hSum

private theorem integral_two_mul_inverseCube {q : Real} (hq : 0 < q) :
    integral (volume.restrict (Ioi q)) (fun t : Real => 2 * t ^ (-3 : Real)) =
      Inv.inv (q ^ (2 : Nat)) := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-3 : Real) < -1) hq]
  have hExp : (-3 : Real) + 1 = ((-2 : Int) : Real) := by norm_num
  rw [hExp, Real.rpow_intCast, zpow_neg]
  norm_num
  ring

/-- The inverse-square weighted prime log sum is bounded by the integral
of the Chebyshev upper bound from the smallest permitted norm upwards. -/
theorem sum_primeNormLog_div_norm_sq_le {A Y : Real}
    (hY : 1 <= Y) (hPsi : forall t : Real, 1 <= t -> dedekindChebyshev K t <= A * t)
    (B : Finset P) (hB : forall p, Membership.mem B p -> Y <= (dedekindPrimeNorm K p : Real)) :
    B.sum (fun p => Real.log (dedekindPrimeNorm K p : Real) /
        (dedekindPrimeNorm K p : Real) ^ (2 : Nat)) <= 2 * A / Y := by
  classical
  let q (p : P) : Real := dedekindPrimeNorm K p
  let w (t : Real) : Real := 2 * t ^ (-3 : Real)
  let f (p : P) : Real -> Real :=
    (Ioi (q p)).indicator (fun t => Real.log (q p) * w t)
  let mu := volume.restrict (Ioi Y)
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hRestr (p : P) (hp : Membership.mem B p) :
      mu.restrict (Ioi (q p)) = volume.restrict (Ioi (q p)) :=
    Measure.restrict_restrict_of_subset (fun _ ht => (hB p hp).trans_lt ht)
  have hInt (p : P) (hp : Membership.mem B p) : Integrable (f p) mu := by
    apply (integrable_indicator_iff measurableSet_Ioi).mpr
    change Integrable (fun t => Real.log (q p) * w t) (mu.restrict (Ioi (q p)))
    rw [hRestr p hp]
    exact ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : Real) < -1)
      (hYpos.trans_le (hB p hp))).const_mul 2).const_mul (Real.log (q p))
  have hId (p : P) (hp : Membership.mem B p) :
      integral mu (f p) = Real.log (q p) / q p ^ (2 : Nat) := by
    unfold f
    rw [integral_indicator measurableSet_Ioi]
    change integral (mu.restrict (Ioi (q p))) (fun t => Real.log (q p) * w t) = _
    rw [hRestr p hp, integral_const_mul, integral_two_mul_inverseCube (hYpos.trans_le (hB p hp))]
    rw [div_eq_mul_inv]
  have hIntSum : Integrable (fun t => B.sum (fun p => f p t)) mu :=
    integrable_finsetSum B hInt
  have hIntUpper : Integrable (fun t : Real => (2 * A) * t ^ (-2 : Real)) mu :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : Real) < -1) hYpos).const_mul (2 * A)
  have hCmp : forall t, Membership.mem (Ioi Y) t ->
      B.sum (fun p => f p t) <= (2 * A) * t ^ (-2 : Real) := by
    intro t ht
    have htY : Y < t := ht
    have htpos := hYpos.trans htY
    have hw : 0 <= w t := mul_nonneg (by norm_num) (Real.rpow_nonneg htpos.le _)
    let C := B.filter (fun p => q p < t)
    have hSum : B.sum (fun p => f p t) = w t * C.sum (fun p => Real.log (q p)) := by
      rw [Finset.mul_sum]
      unfold C
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : q p < t
      case pos => simp [f, h, mul_comm]
      case neg => simp [f, h]
    rw [hSum]
    have hSub : C.sum (fun p => Real.log (q p)) <= dedekindChebyshev K t :=
      sum_primeNormLog_le_dedekindChebyshev K C htpos.le
        (fun _ hp => (Finset.mem_filter.mp hp).2.le)
    have hPower : t ^ (-3 : Real) * t = t ^ (-2 : Real) := calc
      _ = t ^ (-3 : Real) * t ^ (1 : Real) := by rw [Real.rpow_one]
      _ = _ := by rw [<- Real.rpow_add htpos]; norm_num
    calc
      _ <= w t * dedekindChebyshev K t := mul_le_mul_of_nonneg_left hSub hw
      _ <= w t * (A * t) := mul_le_mul_of_nonneg_left (hPsi t (hY.trans htY.le)) hw
      _ = _ := by unfold w; rw [<- hPower]; ring
  have hExact :
      B.sum (fun p => Real.log (q p) / q p ^ (2 : Nat)) =
        integral mu (fun t => B.sum (fun p => f p t)) := by
    rw [integral_finsetSum B hInt]
    exact Finset.sum_congr rfl (fun p hp => (hId p hp).symm)
  rw [hExact]
  apply (setIntegral_mono_on hIntSum hIntUpper measurableSet_Ioi hCmp).trans
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : Real) < -1) hYpos]
  have hExp : (-2 : Real) + 1 = ((-1 : Int) : Real) := by norm_num
  rw [hExp, Real.rpow_intCast, zpow_neg_one]
  norm_num [div_eq_mul_inv]

end Robin1984.GRH
