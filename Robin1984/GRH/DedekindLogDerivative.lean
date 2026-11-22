import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Robin1984.GRH.DedekindEulerProduct

/-!
# The logarithmic derivative of Dedekind zeta on the right half-plane

The logarithms of the prime-ideal factors converge locally uniformly in
the half-plane of absolute convergence. Their sum differentiates there.
-/

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Termwise differentiation of the Dedekind zeta log Euler product on the half-plane of absolute convergence.
- Formalization note: Local uniform comparison and the geometric expansion give the absolutely convergent logarithmic derivative over prime powers.
- PROVENANCE-END
-/

open Complex Filter IsDedekindDomain NumberField Set Topology

namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)

private noncomputable def primeWeight (p : P) (s : Complex) : Complex :=
  (dedekindPrimeNorm K p : Complex) ^ (-s)

private theorem real_one_lt_primeNorm (p : P) :
    (1 : Real) < (dedekindPrimeNorm K p : Real) := by
  exact_mod_cast one_lt_dedekindPrimeNorm K p

private theorem norm_primeWeight (p : P) (s : Complex) :
    norm (primeWeight K p s) = (dedekindPrimeNorm K p : Real) ^ (-s.re) := by
  have hq := zero_lt_one.trans (real_one_lt_primeNorm K p)
  unfold primeWeight
  rw [<- Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re]

private theorem norm_primeWeight_le (p : P) {s z : Complex} (h : s.re <= z.re) :
    norm (primeWeight K p z) <= norm (primeWeight K p s) := by
  rw [norm_primeWeight, norm_primeWeight]
  exact Real.rpow_le_rpow_of_exponent_le (real_one_lt_primeNorm K p).le (neg_le_neg h)

private theorem norm_primeWeight_le_half (p : P) {s : Complex} (hs : 1 <= s.re) :
    norm (primeWeight K p s) <= 1 / 2 := by
  have hTwo : (2 : Real) <= (dedekindPrimeNorm K p : Real) := by
    exact_mod_cast Nat.succ_le_of_lt (one_lt_dedekindPrimeNorm K p)
  have hS : (1 : Complex).re <= s.re := by simpa using hs
  refine (norm_primeWeight_le K p hS).trans ?_
  rw [norm_primeWeight, Complex.one_re, Real.rpow_neg_one]
  simpa only [one_div] using one_div_le_one_div_of_le (zero_lt_two : (0 : Real) < 2) hTwo

private noncomputable def eulerLog (p : P) (s : Complex) : Complex :=
  -Complex.log (1 - primeWeight K p s)

/-- The prime-ideal contribution to the negative logarithmic derivative
of the Dedekind zeta series. -/
noncomputable def dedekindLogDerivativeTerm (p : P) (s : Complex) : Complex :=
  Complex.log (dedekindPrimeNorm K p : Complex) * primeWeight K p s / (1 - primeWeight K p s)

private theorem hasDerivAt_eulerLog (p : P) {s : Complex} (hs : 1 <= s.re) :
    HasDerivAt (eulerLog K p) (-dedekindLogDerivativeTerm K p s) s := by
  have ha : norm (primeWeight K p s) < 1 :=
    (norm_primeWeight_le_half K p hs).trans_lt (half_lt_self zero_lt_one)
  have hSlit : Membership.mem Complex.slitPlane (1 - primeWeight K p s) := by
    have hn : norm (-primeWeight K p s) < 1 := by rwa [norm_neg]
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hn
  have hq : Not ((dedekindPrimeNorm K p : Complex) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt ((zero_lt_one : 0 < (1 : Nat)).trans
      (one_lt_dedekindPrimeNorm K p)))
  let v := primeWeight K p s * Complex.log (dedekindPrimeNorm K p : Complex) * (-1)
  have hBase : HasDerivAt (primeWeight K p) v s :=
    (hasDerivAt_neg' s).const_cpow (Or.inl hq)
  have hArg := hBase.const_sub 1
  have hScalar : -(Inv.inv (1 - primeWeight K p s) * (-v)) =
      -dedekindLogDerivativeTerm K p s := by
    dsimp [v, dedekindLogDerivativeTerm]
    rw [div_eq_mul_inv]
    ring
  rw [<- hScalar]
  exact ((Complex.hasDerivAt_log hSlit).comp s hArg).neg

/-- The logarithmic derivative of the actual Dedekind zeta series is the
convergent sum of the differentiated local factors for `1 < s.re`. -/
theorem hasSum_dedekindLogDerivativeTerm {s : Complex} (hs : 1 < s.re) :
    HasSum (fun p : P => dedekindLogDerivativeTerm K p s)
      (-deriv (dedekindZeta K) s / dedekindZeta K s) := by
  choose a hA using exists_between hs
  let D : Set Complex := {z | a < z.re}
  have hO : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hsD : Membership.mem D s := hA.2
  have hbase : 1 < (a : Complex).re := by simpa using hA.1
  have hu : Summable (fun p : P => (3 / 2 : Real) * norm (primeWeight K p (a : Complex))) :=
    (summable_dedekindPrimeNormWeight K hbase).mul_left _
  have hDiff (p : P) : DifferentiableOn Complex (eulerLog K p) D := by
    intro z hz
    have h := hasDerivAt_eulerLog K p (hA.1.trans (show a < z.re from hz)).le
    exact h.differentiableAt.differentiableWithinAt
  have hb (p : P) (z : Complex) (hz : Membership.mem D z) :
      norm (eulerLog K p z) <= (3 / 2 : Real) * norm (primeWeight K p (a : Complex)) := by
    have hnorm := norm_primeWeight_le_half K p (hA.1.trans (show a < z.re from hz)).le
    have hbound : norm (-primeWeight K p z) <= 1 / 2 := by rwa [norm_neg]
    calc
      norm (eulerLog K p z) <= (3 / 2 : Real) * norm (primeWeight K p z) := by
        simpa only [eulerLog, norm_neg, sub_eq_add_neg] using
          Complex.norm_log_one_add_half_le_self hbound
      _ <= (3 / 2 : Real) * norm (primeWeight K p (a : Complex)) :=
        mul_le_mul_of_nonneg_left (norm_primeWeight_le K p (by simpa using
          (show a < z.re from hz).le)) (div_nonneg (Nat.cast_nonneg 3) (Nat.cast_nonneg 2))
  let L : Complex -> Complex := fun z => tsum (fun p : P => eulerLog K p z)
  have hSum := hasSum_deriv_of_summable_norm hu hDiff hO hb hsD
  have hL : DifferentiableAt Complex L s :=
    (differentiableOn_tsum_of_summable_norm hu hDiff hO hb).differentiableAt (hO.mem_nhds hsD)
  have hEq : Filter.EventuallyEq (nhds s) (fun z => Complex.exp (L z)) (dedekindZeta K) := by
    filter_upwards [hO.mem_nhds hsD] with z hz
    exact (dedekindZeta_eq_exp_tsum_log_eulerFactors K
      (hA.1.trans (show a < z.re from hz))).symm
  have hDeriv := ((Complex.hasDerivAt_exp (L s)).comp s hL.hasDerivAt).congr_of_eventuallyEq hEq.symm
  have hz := dedekindZeta_ne_zero_of_one_lt_re K hs
  have hExp : Complex.exp (L s) = dedekindZeta K s := hEq.eq_of_nhds
  have hDerivative : -deriv L s = -deriv (dedekindZeta K) s / dedekindZeta K s := by
    rw [hDeriv.deriv, hExp]
    apply (eq_div_iff hz).mpr
    ring
  have hLocal (p : P) : deriv (eulerLog K p) s = -dedekindLogDerivativeTerm K p s :=
    (hasDerivAt_eulerLog K p hs.le).deriv
  change HasSum (fun p : P => deriv (eulerLog K p) s) (deriv L s) at hSum
  simp only [hLocal] at hSum
  simpa only [neg_neg, hDerivative] using hSum.neg

/-- A summand indexed by the power `p^(n+1)` of a prime ideal. -/
noncomputable def dedekindPrimePowerTerm (p : P) (n : Nat) (s : Complex) : Complex :=
  Complex.log (dedekindPrimeNorm K p : Complex) *
    ((dedekindPrimeNorm K p ^ (n + 1) : Nat) : Complex) ^ (-s)

private theorem primePowerTerm_eq (p : P) (n : Nat) (s : Complex) :
    dedekindPrimePowerTerm K p n s =
      Complex.log (dedekindPrimeNorm K p : Complex) * (primeWeight K p s) ^ (n + 1) := by
  unfold dedekindPrimePowerTerm primeWeight
  rw [Nat.cast_pow, <- Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

private theorem primePowerTerm_hasSum (p : P) {s : Complex} (hs : 1 <= s.re) :
    HasSum (fun n => dedekindPrimePowerTerm K p n s) (dedekindLogDerivativeTerm K p s) := by
  have h := (norm_primeWeight_le_half K p hs).trans_lt (half_lt_self zero_lt_one)
  have H := (hasSum_geometric_of_norm_lt_one h).mul_left
    (Complex.log (dedekindPrimeNorm K p : Complex) * primeWeight K p s)
  simpa only [primePowerTerm_eq, pow_succ', <- mul_assoc, dedekindLogDerivativeTerm, div_eq_mul_inv]
    using H

private theorem norm_primePowerTerm (p : P) (n : Nat) (s : Complex) :
    norm (dedekindPrimePowerTerm K p n s) =
      Real.log (dedekindPrimeNorm K p : Real) * norm (primeWeight K p s) ^ (n + 1) := by
  have hp := real_one_lt_primeNorm K p
  have hLog : norm (Complex.log (dedekindPrimeNorm K p : Complex)) =
      Real.log (dedekindPrimeNorm K p : Real) := by
    rw [<- Complex.ofReal_natCast, <- Complex.ofReal_log (zero_lt_one.trans hp).le,
      Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hp.le)]
  rw [primePowerTerm_eq, norm_mul, norm_pow, hLog]

private theorem log_mul_primeWeight_le {a : Real} {s : Complex} (ha : a < s.re) (p : P) :
    Real.log (dedekindPrimeNorm K p : Real) * norm (primeWeight K p s) <=
      (1 / (s.re - a)) * norm (primeWeight K p (a : Complex)) := by
  let q : Real := dedekindPrimeNorm K p
  let d : Real := s.re - a
  have hq : 0 < q := zero_lt_one.trans (real_one_lt_primeNorm K p)
  have hd : 0 < d := sub_pos.mpr ha
  have hLogPower : Real.log (q ^ d) = d * Real.log q := by
    rw [Real.rpow_def_of_pos hq, Real.log_exp, mul_comm]
  have hLog : Real.log q <= (q ^ d) / d := by
    have h := (Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hq d)).trans (sub_le_self _ zero_le_one)
    rw [hLogPower] at h
    calc
      Real.log q = (d * Real.log q) / d := by field_simp
      _ <= (q ^ d) / d := div_le_div_of_nonneg_right h hd.le
  rw [norm_primeWeight, norm_primeWeight, Complex.ofReal_re]
  change Real.log q * q ^ (-s.re) <= (1 / d) * q ^ (-a)
  calc
    _ <= ((q ^ d) / d) * q ^ (-s.re) :=
      mul_le_mul_of_nonneg_right hLog (Real.rpow_nonneg hq.le _)
    _ = (q ^ d * q ^ (-s.re)) / d := by ring
    _ = (1 / d) * q ^ (-a) := by
      rw [<- Real.rpow_add hq, show d + (-s.re) = -a by dsimp [d]; ring]
      ring

/-- The prime-power expansion converges absolutely in the half-plane
`1 < s.re`. -/
theorem summable_norm_dedekindPrimePowerTerm {s : Complex} (hs : 1 < s.re) :
    Summable (fun pn : Prod P Nat => norm (dedekindPrimePowerTerm K pn.1 pn.2 s)) := by
  choose a ha using exists_between hs
  have hBase : 1 < (a : Complex).re := by simpa using ha.1
  have hOuter : Summable (fun p : P => (2 * (1 / (s.re - a))) *
      norm (primeWeight K p (a : Complex))) :=
    (summable_dedekindPrimeNormWeight K hBase).mul_left _
  have hLocal (p : P) :
      HasSum (fun n => norm (dedekindPrimePowerTerm K p n s))
        (Real.log (dedekindPrimeNorm K p : Real) * norm (primeWeight K p s) *
          Inv.inv (1 - norm (primeWeight K p s))) := by
    have h := (norm_primeWeight_le_half K p hs.le).trans_lt (half_lt_self zero_lt_one)
    have H := (hasSum_geometric_of_lt_one (norm_nonneg _) h).mul_left
      (Real.log (dedekindPrimeNorm K p : Real) * norm (primeWeight K p s))
    simpa only [norm_primePowerTerm, pow_succ', <- mul_assoc] using H
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine And.intro (fun p => (hLocal p).summable) ?_
  refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _)) ?_ hOuter
  intro p
  rw [(hLocal p).tsum_eq]
  have hHalf : (1 / 2 : Real) <= 1 - norm (primeWeight K p s) := by
    linarith only [norm_primeWeight_le_half K p hs.le]
  have hInv : Inv.inv (1 - norm (primeWeight K p s)) <= 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1 / 2) hHalf
    norm_num [one_div] at h
    exact h
  have hZ := mul_nonneg (Real.log_nonneg (real_one_lt_primeNorm K p).le) (norm_nonneg (primeWeight K p s))
  calc
    _ <= Real.log (dedekindPrimeNorm K p : Real) * norm (primeWeight K p s) * 2 :=
      mul_le_mul_of_nonneg_left hInv hZ
    _ <= ((1 / (s.re - a)) * norm (primeWeight K p (a : Complex))) * 2 :=
      mul_le_mul_of_nonneg_right (log_mul_primeWeight_le K ha.2 p) zero_le_two
    _ = _ := by ring

/-- The negative logarithmic derivative is the absolutely convergent
prime-power Dirichlet series on `1 < s.re`. -/
theorem hasSum_dedekindPrimePowerTerm {s : Complex} (hs : 1 < s.re) :
    HasSum (fun pn : Prod P Nat => dedekindPrimePowerTerm K pn.1 pn.2 s)
      (-deriv (dedekindZeta K) s / dedekindZeta K s) := by
  have h : Summable (fun pn : Prod P Nat => dedekindPrimePowerTerm K pn.1 pn.2 s) :=
    summable_norm_iff.mp (summable_norm_dedekindPrimePowerTerm K hs)
  have hEq : (tsum (fun pn : Prod P Nat => dedekindPrimePowerTerm K pn.1 pn.2 s)) =
      -deriv (dedekindZeta K) s / dedekindZeta K s := by
    rw [h.tsum_prod]
    simp_rw [(primePowerTerm_hasSum K _ hs.le).tsum_eq]
    exact (hasSum_dedekindLogDerivativeTerm K hs).tsum_eq
  rw [<- hEq]
  exact h.hasSum

end Robin1984.GRH
