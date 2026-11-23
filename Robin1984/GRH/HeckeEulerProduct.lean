import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Robin1984.GRH.AutomorphicEulerLog

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The unitary Hecke character on the idele class group and the Euler product of its finite local factors.
- Formalization note: Constructs the finite factors from pinned Mathlib adeles, proves absolute convergence and the paired logarithmic identity, and applies the triangular criterion when given the analytic completions.
- PROVENANCE-END
-/

/-!
# The finite Euler product of a unitary Hecke character

A unitary character is a continuous circle-valued character of the ideles
that is trivial on the principal ideles. Its factors use evaluations at
uniformizers for unramified primes. Absolute convergence gives the Hecke
Euler series and the paired logarithm used in the triangular criterion.
The criterion takes the analytic continuation and completion as inputs.
-/

set_option autoImplicit false

open Complex Filter IsDedekindDomain NumberField Set

namespace Robin1984.GRH

private noncomputable def eulerLocalLogTerm (n : Nat) (z : Complex) : Complex :=
  z ^ (n + 1) / ((n + 1 : Nat) : Complex)

private theorem hasDerivAt_eulerLocalLogTerm (n : Nat) (z : Complex) :
    HasDerivAt (eulerLocalLogTerm n) (z ^ n) z := by
  have hne : Not ((((n + 1 : Nat) : Complex)) = 0) := by
    exact_mod_cast Nat.succ_ne_zero n
  have hd := ((hasDerivAt_id z).pow (n + 1)).div_const ((n + 1 : Nat) : Complex)
  have hExact : ((n + 1 : Nat) : Complex) * z ^ n / ((n + 1 : Nat) : Complex) = z ^ n :=
    (div_eq_iff hne).mpr (mul_comm _ _)
  have h : HasDerivAt (eulerLocalLogTerm n)
      (((n + 1 : Nat) : Complex) * z ^ n / ((n + 1 : Nat) : Complex)) z := by
    simpa only [eulerLocalLogTerm, Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one] using! hd
  rwa [hExact] at h

private theorem norm_eulerLocalLogTerm_le (n : Nat) (z : Complex) {r : Real} (hz : norm z <= r) :
    norm (eulerLocalLogTerm n z) <= r ^ (n + 1) := by
  have hk : (1 : Real) <= ((n + 1 : Nat) : Real) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  rw [eulerLocalLogTerm, norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ <= norm z ^ (n + 1) / 1 :=
      div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _) zero_lt_one hk
    _ <= _ := by
      rw [div_one]
      gcongr

private theorem hasDerivAt_tsum_eulerLocalLogTerm {z : Complex} (hz : norm z < 1) :
    HasDerivAt (fun w => tsum (fun n => eulerLocalLogTerm n w)) (Inv.inv (1 - z)) z := by
  choose r hr using exists_between hz
  let D : Set Complex := Metric.ball 0 r
  have hOpen : IsOpen D := Metric.isOpen_ball
  have hzD : Membership.mem D z := by
    change dist z 0 < r
    rw [dist_zero_right]
    exact hr.1
  have hSum : Summable (fun n : Nat => r ^ (n + 1)) :=
    ((hasSum_geometric_of_lt_one ((norm_nonneg z).trans hr.1.le) hr.2).mul_left r).summable.congr
      (fun n => (pow_succ' r n).symm)
  have hDiff (n : Nat) : DifferentiableOn Complex (eulerLocalLogTerm n) D := fun w _ =>
    (hasDerivAt_eulerLocalLogTerm n w).differentiableAt.differentiableWithinAt
  have hBound (n : Nat) (w : Complex) (hw : Membership.mem D w) : norm (eulerLocalLogTerm n w) <= r ^ (n + 1) := by
    change dist w 0 < r at hw
    rw [dist_zero_right] at hw
    exact norm_eulerLocalLogTerm_le n w hw.le
  have hd := hasSum_deriv_of_summable_norm hSum hDiff hOpen hBound hzD
  have hD := (differentiableOn_tsum_of_summable_norm hSum hDiff hOpen hBound).differentiableAt
    (hOpen.mem_nhds hzD)
  have hTerm (n : Nat) : deriv (eulerLocalLogTerm n) z = z ^ n := (hasDerivAt_eulerLocalLogTerm n z).deriv
  simp only [hTerm] at hd
  have hDeriv := hd.unique (hasSum_geometric_of_norm_lt_one hz)
  rw [<- hDeriv]
  exact hD.hasDerivAt

private theorem exp_tsum_eulerLocalLogTerm {z : Complex} (hz : norm z < 1) :
    Complex.exp (tsum (fun n => eulerLocalLogTerm n z)) = Inv.inv (1 - z) := by
  let D : Set Complex := Metric.ball 0 1
  let f : Complex -> Complex := fun w => tsum (fun n => eulerLocalLogTerm n w)
  let g : Complex -> Complex := fun w => Complex.exp (f w) * (1 - w)
  have hOpen : IsOpen D := Metric.isOpen_ball
  have hConn : IsPreconnected D := (convex_ball (0 : Complex) 1).isPreconnected
  have hZero (w : Complex) (hw : Membership.mem D w) : HasDerivAt g 0 w := by
    have hwNorm : norm w < 1 := by
      change dist w 0 < 1 at hw
      rwa [dist_zero_right] at hw
    have hNe : Not (1 - w = 0) := fun h => by
      have he := (sub_eq_zero.mp h).symm
      subst w
      simp at hwNorm
    have hF : HasDerivAt f (Inv.inv (1 - w)) w := hasDerivAt_tsum_eulerLocalLogTerm hwNorm
    have hExp : HasDerivAt (fun t => Complex.exp (f t)) (Complex.exp (f w) * Inv.inv (1 - w)) w :=
      (Complex.hasDerivAt_exp (f w)).comp w hF
    have hLin : HasDerivAt (fun t : Complex => 1 - t) (-1) w := (hasDerivAt_id w).const_sub 1
    have hG := hExp.mul hLin
    have hScalar : Complex.exp (f w) * Inv.inv (1 - w) * (1 - w) +
        Complex.exp (f w) * (-1) = 0 := by
      rw [mul_assoc, mul_comm (Inv.inv (1 - w)) (1 - w), <- div_eq_mul_inv, div_self hNe]
      ring
    rwa [hScalar] at hG
  have hDiff : DifferentiableOn Complex g D :=
    fun w hw => (hZero w hw).differentiableAt.differentiableWithinAt
  have hDeriv : Set.EqOn (deriv g) 0 D := fun w hw => (hZero w hw).deriv
  choose c hc using hOpen.exists_is_const_of_deriv_eq_zero hConn hDiff hDeriv
  have h0D : Membership.mem D (0 : Complex) := by
    change dist (0 : Complex) 0 < 1
    simp
  have hzD : Membership.mem D z := by
    change dist z 0 < 1
    rwa [dist_zero_right]
  have h0 : g 0 = 1 := by
    dsimp only [g, f, eulerLocalLogTerm]
    simp
  have hzG := (hc z hzD).trans ((hc 0 h0D).symm.trans h0)
  have hNe : Not (1 - z = 0) := fun h => by
    have he := (sub_eq_zero.mp h).symm
    subst z
    simp at hz
  have hEq : Complex.exp (f z) * (1 - z) = 1 := hzG
  simpa only [one_div] using (eq_div_iff hNe).mpr hEq


/-- A unitary character of the idele class group, realized by its pullback
to the ideles. Units of the adele ring carry the units topology. -/
abbrev UnitaryHeckeCharacter (K : Type*) [Field K] [NumberField K] :=
  {chi : ContinuousMonoidHom (Units (AdeleRing (RingOfIntegers K) K)) Circle //
    forall a : Units K, chi (Units.map (algebraMap K (AdeleRing (RingOfIntegers K) K)).toMonoidHom a) = 1}

private noncomputable def finiteLocalAdele (K : Type*) [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (a : p.adicCompletion K) :
    FiniteAdeleRing (RingOfIntegers K) K := by
  classical
  refine Subtype.mk (Function.update (fun _ => 1) p a) ?_
  filter_upwards [(Set.finite_singleton p).compl_mem_cofinite] with q hq
  rw [Function.update_of_ne (show Not (q = p) from hq)]
  exact (q.adicCompletionIntegers K).one_mem

private theorem finiteLocalAdele_at (K : Type*) [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (a : p.adicCompletion K) :
    finiteLocalAdele K p a p = a := by
  classical
  change Function.update (fun _ : HeightOneSpectrum (RingOfIntegers K) => 1) p a p = a
  exact Function.update_self p a _

private theorem finiteLocalAdele_away (K : Type*) [Field K] [NumberField K]
    (p q : HeightOneSpectrum (RingOfIntegers K)) (a : p.adicCompletion K) (hq : Not (q = p)) :
    finiteLocalAdele K p a q = 1 := by
  classical
  change Function.update (fun _ : HeightOneSpectrum (RingOfIntegers K) => 1) p a q = 1
  exact Function.update_of_ne hq a _

private noncomputable def localAdeleHom (K : Type*) [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    MonoidHom (p.adicCompletion K) (AdeleRing (RingOfIntegers K) K) where
  toFun a := (1, finiteLocalAdele K p a)
  map_one' := by
    change (1, finiteLocalAdele K p 1) = ((1 : InfiniteAdeleRing K), 1)
    refine Prod.ext rfl ?_
    apply DFunLike.ext
    intro q
    by_cases hq : q = p
    case pos => subst q; exact finiteLocalAdele_at K p 1
    case neg => exact finiteLocalAdele_away K p q 1 hq
  map_mul' a b := by
    apply Prod.ext (one_mul _).symm
    apply DFunLike.ext
    intro q
    change finiteLocalAdele K p (a * b) q =
      finiteLocalAdele K p a q * finiteLocalAdele K p b q
    by_cases hq : q = p
    case pos => subst q; simp only [finiteLocalAdele_at]
    case neg => simp only [finiteLocalAdele_away K p q _ hq, one_mul]

/-- A local unit, viewed as an idele with all other components one. -/
noncomputable def localIdeleHom (K : Type*) [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    MonoidHom (Units (p.adicCompletion K)) (Units (AdeleRing (RingOfIntegers K) K)) :=
  Units.map (localAdeleHom K p)

/-- The valuation of a uniformizer for Mathlib's normalized finite valuation. -/
def finiteUniformizerValue : WithZero (Multiplicative Int) :=
  (Multiplicative.ofAdd (-1 : Int) : Multiplicative Int)

private theorem exists_localUniformizer (K : Type*) [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    exists a : Units (p.adicCompletion K), Valued.v (a : p.adicCompletion K) = finiteUniformizerValue := by
  choose a ha using HeightOneSpectrum.valuedAdicCompletion_surjective K p finiteUniformizerValue
  have hNe : Not (a = 0) := by
    intro h
    rw [h, Valuation.map_zero] at ha
    exact WithZero.coe_ne_zero ha.symm
  exact Exists.intro (Units.mk0 a hNe) ha

private noncomputable def localUniformizer (K : Type*) [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) : Units (p.adicCompletion K) :=
  (exists_localUniformizer K p).choose

private theorem valuation_localUniformizer (K : Type*) [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) :
    Valued.v (localUniformizer K p : p.adicCompletion K) = finiteUniformizerValue :=
  (exists_localUniformizer K p).choose_spec

/-- Triviality on the local integral unit group is unramifiedness. -/
def HeckeUnramifiedAt {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K)) : Prop :=
  forall a : Units (p.adicCompletion K),
    (Valued.v (a : p.adicCompletion K) : WithZero (Multiplicative Int)) = 1 ->
      chi.val (localIdeleHom K p a) = 1

/-- The rank-one parameter at a finite prime is zero in the ramified
case and is the unramified character evaluated on a uniformizer otherwise. -/
noncomputable def heckeLocalParameter {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K)) : Complex := by
  classical
  exact if HeckeUnramifiedAt chi p then
    (chi.val (localIdeleHom K p (localUniformizer K p)) : Complex) else 0

theorem norm_heckeLocalParameter_le_one {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K)) :
    norm (heckeLocalParameter chi p) <= 1 := by
  classical
  unfold heckeLocalParameter
  by_cases h : HeckeUnramifiedAt chi p
  case pos => rw [if_pos h, Circle.norm_coe]
  case neg => rw [if_neg h, norm_zero]; exact zero_le_one

/-- At an unramified prime any local uniformizer gives the same
Euler parameter. -/
theorem heckeLocalParameter_eq_of_uniformizer {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K))
    (h : HeckeUnramifiedAt chi p) (a : Units (p.adicCompletion K))
    (ha : Valued.v (a : p.adicCompletion K) = finiteUniformizerValue) :
    heckeLocalParameter chi p = (chi.val (localIdeleHom K p a) : Complex) := by
  classical
  unfold heckeLocalParameter
  rw [if_pos h]
  have hVal : Valued.v ((localUniformizer K p / a : Units (p.adicCompletion K)) :
      p.adicCompletion K) = 1 := by
    rw [Units.val_div_eq_div_val, Valuation.map_div, valuation_localUniformizer K p, ha, div_self]
    exact WithZero.coe_ne_zero
  have hEq := h (localUniformizer K p / a) hVal
  rw [map_div, map_div] at hEq
  exact congrArg (fun z : Circle => (z : Complex)) (div_eq_one.mp hEq)

/-- The inverse of a unitary Hecke character, giving its contragredient. -/
noncomputable def unitaryHeckeInverse {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) : UnitaryHeckeCharacter K :=
  Subtype.mk
    { toFun := fun a => Inv.inv (chi.val a)
      map_one' := by rw [map_one, inv_one]
      map_mul' := by intro a b; rw [map_mul, mul_inv_rev, mul_comm]
      continuous_toFun := chi.val.continuous.inv }
    (fun a => by
      change Inv.inv (chi.val (Units.map (algebraMap K (AdeleRing (RingOfIntegers K) K)).toMonoidHom a)) = 1
      rw [chi.property a, inv_one])

private theorem unitaryHeckeInverse_apply {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (a : Units (AdeleRing (RingOfIntegers K) K)) :
    (unitaryHeckeInverse chi).val a = Inv.inv (chi.val a) := rfl

private theorem heckeUnramifiedAt_inverse_iff {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K)) :
    HeckeUnramifiedAt (unitaryHeckeInverse chi) p <-> HeckeUnramifiedAt chi p := by
  simp only [HeckeUnramifiedAt, unitaryHeckeInverse_apply, inv_eq_one]

/-- The unramified parameter of the inverse character is the conjugate
parameter. Both parameters are zero at a ramified prime. -/
theorem heckeLocalParameter_inverse {K : Type*} [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (p : HeightOneSpectrum (RingOfIntegers K)) :
    heckeLocalParameter (unitaryHeckeInverse chi) p =
      (starRingEnd Complex) (heckeLocalParameter chi p) := by
  classical
  unfold heckeLocalParameter
  by_cases h : HeckeUnramifiedAt chi p
  case pos =>
    rw [if_pos h, if_pos ((heckeUnramifiedAt_inverse_iff chi p).mpr h),
      unitaryHeckeInverse_apply, Circle.coe_inv_eq_conj]
  case neg =>
    have hInv : Not (HeckeUnramifiedAt (unitaryHeckeInverse chi) p) := by
      intro hinv
      exact h ((heckeUnramifiedAt_inverse_iff chi p).mp hinv)
    rw [if_neg h, if_neg hInv, map_zero]

variable (K : Type*) [Field K] [NumberField K]

/-- Prime ideals equipped with a positive power, represented by the
exponent one more than the natural-number component. -/
abbrev HeckePrimePowers :=
  Prod (HeightOneSpectrum (RingOfIntegers K)) Nat

/-- The real logarithmic Euler coefficient of the pair of a unitary
Hecke character and its inverse. -/
noncomputable def heckePairedCoefficient (chi : UnitaryHeckeCharacter K)
    (pn : HeckePrimePowers K) : Real :=
  2 * ((heckeLocalParameter chi pn.1) ^ (pn.2 + 1)).re *
    Real.log (dedekindPrimeNorm K pn.1 : Real)

/-- The triangular remainder for a paired Hecke Euler product. -/
noncomputable def heckePairedEulerData (chi : UnitaryHeckeCharacter K)
    (m : Nat) (F : Complex -> Complex) : GrandRobinEulerData (HeckePrimePowers K) where
  normPower pn := dedekindPrimePowerNorm K pn
  coefficient := heckePairedCoefficient K chi
  poleOrder := m
  poleRemoved := F

private theorem two_le_heckePrimePowerNorm (pn : HeckePrimePowers K) :
    (2 : Real) <= (dedekindPrimePowerNorm K pn : Real) := by
  have h := one_lt_dedekindPrimeNorm K pn.1
  have hTwo : 2 <= dedekindPrimeNorm K pn.1 := Nat.succ_le_of_lt h
  have hTail : 1 <= dedekindPrimeNorm K pn.1 ^ pn.2 :=
    Nat.one_le_pow pn.2 (dedekindPrimeNorm K pn.1) h.le
  have hPow : 2 <= dedekindPrimePowerNorm K pn := by
    unfold dedekindPrimePowerNorm
    rw [pow_succ']
    calc
      _ <= dedekindPrimeNorm K pn.1 := hTwo
      _ = dedekindPrimeNorm K pn.1 * 1 := (Nat.mul_one _).symm
      _ <= _ := Nat.mul_le_mul_left _ hTail
  exact_mod_cast hPow

private theorem finite_heckePrimePowerNorm_lt (T : Real) :
    Set.Finite {pn : HeckePrimePowers K | (dedekindPrimePowerNorm K pn : Real) < T} := by
  apply (finite_primePowerNorm_le K (Nat.ceil T)).subset
  intro pn hp
  have h : ((dedekindPrimePowerNorm K pn : Nat) : Real) <= (Nat.ceil T : Real) :=
    le_trans (show (dedekindPrimePowerNorm K pn : Real) <= T from hp.le) (Nat.le_ceil T)
  exact_mod_cast h

private theorem countable_heckePrimePowers : Countable (HeckePrimePowers K) := by
  refine Set.countable_univ_iff.mp ?_
  have hUnion : (Set.univ : Set (HeckePrimePowers K)) =
      Set.iUnion (fun n : Nat => {pn : HeckePrimePowers K | dedekindPrimePowerNorm K pn <= n}) := by
    ext pn
    constructor
    case mp =>
      intro _
      refine Set.mem_iUnion.mpr (Exists.intro (dedekindPrimePowerNorm K pn) ?_)
      change dedekindPrimePowerNorm K pn <= dedekindPrimePowerNorm K pn
      exact le_rfl
    case mpr =>
      intro _
      exact Set.mem_univ pn
  rw [hUnion]
  exact Set.countable_iUnion (fun n => (finite_primePowerNorm_le K n).countable)

private theorem norm_pow_heckeLocalParameter_le_one (chi : UnitaryHeckeCharacter K)
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat) :
    norm (heckeLocalParameter chi p ^ n) <= 1 := by
  induction n with
  | zero => rw [pow_zero, norm_one]
  | succ n hn =>
    rw [pow_succ, norm_mul]
    calc
      _ <= 1 * 1 := mul_le_mul hn (norm_heckeLocalParameter_le_one chi p) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _

private theorem norm_heckePairedCoefficient_le (chi : UnitaryHeckeCharacter K)
    (pn : HeckePrimePowers K) :
    norm (heckePairedCoefficient K chi pn) <= 2 * norm (Real.log (dedekindPrimeNorm K pn.1 : Real)) := by
  have hRe : norm (((heckeLocalParameter chi pn.1) ^ (pn.2 + 1)).re) <= 1 :=
    (Complex.abs_re_le_norm _).trans (norm_pow_heckeLocalParameter_le_one K chi pn.1 _)
  rw [heckePairedCoefficient, norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : Real) <= 2)]
  calc
    _ <= (2 * 1) * norm (Real.log (dedekindPrimeNorm K pn.1 : Real)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRe (by norm_num)) (norm_nonneg _)
    _ = _ := by rw [mul_one]

/-- Absolute convergence of the paired prime-power logarithmic
derivative in the ordinary right half-plane. -/
theorem summable_heckePairedCoefficient (chi : UnitaryHeckeCharacter K) {r : Real} (hr : 1 < r) :
    Summable (fun pn : HeckePrimePowers K =>
      norm (heckePairedCoefficient K chi pn) * (dedekindPrimePowerNorm K pn : Real) ^ (-r)) := by
  have hs : 1 < (r : Complex).re := by simpa only [Complex.ofReal_re] using hr
  have hSum := (summable_norm_dedekindPrimePowerTerm K hs).mul_left (2 : Real)
  refine Summable.of_nonneg_of_le (fun pn => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))
    ?_ hSum
  intro pn
  have hn : 0 < (dedekindPrimePowerNorm K pn : Real) :=
    (by norm_num : (0 : Real) < 2).trans_le (two_le_heckePrimePowerNorm K pn)
  have hp : 0 <= (dedekindPrimeNorm K pn.1 : Real) := by positivity
  have hEq : dedekindPrimePowerTerm K pn.1 pn.2 (r : Complex) =
      (Real.log (dedekindPrimeNorm K pn.1 : Real) : Complex) *
        ((dedekindPrimePowerNorm K pn : Real) : Complex) ^ (-(r : Complex)) := by
    unfold dedekindPrimePowerTerm dedekindPrimePowerNorm
    rw [Complex.ofReal_log hp, Complex.ofReal_natCast, Complex.ofReal_natCast]
  rw [hEq, norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hn,
    Complex.neg_re, Complex.ofReal_re, <- mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_heckePairedCoefficient_le K chi pn)
    (Real.rpow_nonneg hn.le _)

private noncomputable def heckeEulerLogTerm (chi : UnitaryHeckeCharacter K)
    (pn : HeckePrimePowers K) (s : Complex) : Complex :=
  (heckeLocalParameter chi pn.1 ^ (pn.2 + 1) / ((pn.2 + 1 : Nat) : Complex)) *
    ((dedekindPrimePowerNorm K pn : Real) : Complex) ^ (-s)

/-- The Hecke L-series on the open half-plane of absolute convergence,
expressed as the exponential of its prime-power logarithm. -/
noncomputable def heckeEulerL (chi : UnitaryHeckeCharacter K) (s : Complex) : Complex :=
  Complex.exp (tsum (fun pn => heckeEulerLogTerm K chi pn s))

private theorem norm_heckeEulerLogTerm_le (chi : UnitaryHeckeCharacter K)
    (pn : HeckePrimePowers K) (s : Complex) :
    norm (heckeEulerLogTerm K chi pn s) <=
      Inv.inv (Real.log 2) * norm (dedekindPrimePowerTerm K pn.1 pn.2 s) := by
  have hPrime : (1 : Real) < (dedekindPrimeNorm K pn.1 : Real) := by
    exact_mod_cast one_lt_dedekindPrimeNorm K pn.1
  have hPrimeTwo : (2 : Real) <= (dedekindPrimeNorm K pn.1 : Real) := by
    exact_mod_cast Nat.succ_le_of_lt (one_lt_dedekindPrimeNorm K pn.1)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLog := Real.log_le_log (by norm_num : (0 : Real) < 2) hPrimeTwo
  unfold heckeEulerLogTerm
  rw [norm_mul, norm_div, Complex.norm_natCast]
  have hEq : dedekindPrimePowerTerm K pn.1 pn.2 s =
      (Real.log (dedekindPrimeNorm K pn.1 : Real) : Complex) *
        ((dedekindPrimePowerNorm K pn : Real) : Complex) ^ (-s) := by
    unfold dedekindPrimePowerTerm dedekindPrimePowerNorm
    rw [Complex.ofReal_log (zero_le_one.trans hPrime.le), Complex.ofReal_natCast, Complex.ofReal_natCast]
  rw [hEq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hPrime.le), <- mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ <= 1 / ((pn.2 + 1 : Nat) : Real) :=
      div_le_div_of_nonneg_right (norm_pow_heckeLocalParameter_le_one K chi pn.1 _) (Nat.cast_nonneg _)
    _ <= 1 / 1 := div_le_div_of_nonneg_left zero_le_one zero_lt_one (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le pn.2))
    _ = Inv.inv (Real.log 2) * Real.log 2 := by
      rw [div_one, mul_comm, <- div_eq_mul_inv, div_self hLogTwo.ne']
    _ <= _ := mul_le_mul_of_nonneg_left hLog (inv_nonneg.mpr hLogTwo.le)

private theorem summable_heckeEulerLogTerm (chi : UnitaryHeckeCharacter K) {s : Complex}
    (hs : 1 < s.re) :
    Summable (fun pn => heckeEulerLogTerm K chi pn s) := by
  apply summable_norm_iff.mp
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun pn => norm_heckeEulerLogTerm_le K chi pn s)
    ((summable_norm_dedekindPrimePowerTerm K hs).mul_left (Inv.inv (Real.log 2)))

private theorem ofReal_two_mul_re (z : Complex) :
    ((2 * z.re : Real) : Complex) = z + (starRingEnd Complex) z := by
  apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, two_mul]

private theorem heckePairedEulerLog_eq (chi : UnitaryHeckeCharacter K)
    (m : Nat) (F : Complex -> Complex) {s : Complex} (hs : 1 < s.re) :
    grandEulerLog (heckePairedEulerData K chi m F) s =
      tsum (fun pn => heckeEulerLogTerm K chi pn s) +
        tsum (fun pn => heckeEulerLogTerm K (unitaryHeckeInverse chi) pn s) := by
  rw [<- (summable_heckeEulerLogTerm K chi hs).tsum_add
    (summable_heckeEulerLogTerm K (unitaryHeckeInverse chi) hs)]
  apply tsum_congr
  intro pn
  change ((heckePairedCoefficient K chi pn : Complex) /
      (Real.log (dedekindPrimePowerNorm K pn : Real) : Complex)) *
      ((dedekindPrimePowerNorm K pn : Real) : Complex) ^ (-s) =
    heckeEulerLogTerm K chi pn s + heckeEulerLogTerm K (unitaryHeckeInverse chi) pn s
  have hLog :
      Real.log (dedekindPrimePowerNorm K pn : Real) =
        ((pn.2 + 1 : Nat) : Real) * Real.log (dedekindPrimeNorm K pn.1 : Real) := by
    rw [dedekindPrimePowerNorm, Nat.cast_pow, Real.log_pow]
  have hPrime : (1 : Real) < (dedekindPrimeNorm K pn.1 : Real) := by
    exact_mod_cast one_lt_dedekindPrimeNorm K pn.1
  have hLogNe : Not ((Real.log (dedekindPrimeNorm K pn.1 : Real) : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hPrime).ne'
  simp only [heckeEulerLogTerm, heckeLocalParameter_inverse, <- map_pow]
  rw [<- add_mul, <- add_div, <- ofReal_two_mul_re]
  apply congrArg (fun z : Complex => z * ((dedekindPrimePowerNorm K pn : Real) : Complex) ^ (-s))
  rw [hLog, heckePairedCoefficient]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [hLogNe]

/-- The exponential Euler product in the triangular criterion is the
product of the actual finite Euler series of a Hecke character and its inverse. -/
theorem heckePairedEulerProduct_eq (chi : UnitaryHeckeCharacter K)
    (m : Nat) (F : Complex -> Complex) {s : Complex} (hs : 1 < s.re) :
    Complex.exp (grandEulerLog (heckePairedEulerData K chi m F) s) =
      heckeEulerL K chi s * heckeEulerL K (unitaryHeckeInverse chi) s := by
  rw [heckePairedEulerLog_eq K chi m F hs, Complex.exp_add]
  rfl

private theorem heckeEulerLogTerm_eq_localLogTerm (chi : UnitaryHeckeCharacter K)
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat) (s : Complex) :
    heckeEulerLogTerm K chi (p, n) s =
      eulerLocalLogTerm n (heckeLocalParameter chi p * (dedekindPrimeNorm K p : Complex) ^ (-s)) := by
  unfold heckeEulerLogTerm eulerLocalLogTerm dedekindPrimePowerNorm
  rw [Complex.ofReal_natCast, Nat.cast_pow, <- Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, mul_pow]
  simp only [div_eq_mul_inv]
  ac_rfl

private theorem norm_heckeLocalWeight_lt_one (chi : UnitaryHeckeCharacter K)
    (p : HeightOneSpectrum (RingOfIntegers K)) {s : Complex} (hs : 1 < s.re) :
    norm (heckeLocalParameter chi p * (dedekindPrimeNorm K p : Complex) ^ (-s)) < 1 := by
  have hPrime : (1 : Real) < (dedekindPrimeNorm K p : Real) := by
    exact_mod_cast one_lt_dedekindPrimeNorm K p
  have hPow := Real.rpow_lt_rpow_of_exponent_lt hPrime
    (neg_lt_zero.mpr (zero_lt_one.trans hs))
  rw [Real.rpow_zero] at hPow
  rw [norm_mul, <- Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hPrime), Complex.neg_re]
  calc
    _ <= 1 * (dedekindPrimeNorm K p : Real) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (norm_heckeLocalParameter_le_one chi p)
        (Real.rpow_nonneg (zero_le_one.trans hPrime.le) _)
    _ < _ := by simpa only [one_mul] using hPow

/-- The Hecke series agrees with the ordinary prime-ideal Euler product
throughout the half-plane of absolute convergence. -/
theorem hasProd_heckeEulerL (chi : UnitaryHeckeCharacter K) {s : Complex} (hs : 1 < s.re) :
    HasProd (fun p : HeightOneSpectrum (RingOfIntegers K) =>
      Inv.inv (1 - heckeLocalParameter chi p * (dedekindPrimeNorm K p : Complex) ^ (-s)))
      (heckeEulerL K chi s) := by
  have hSum := summable_heckeEulerLogTerm K chi hs
  have hIterated := hSum.hasSum.prod_fiberwise (fun p => (hSum.prod_factor p).hasSum)
  refine HasProd.congr_fun hIterated.cexp ?_
  intro p
  simp only [heckeEulerLogTerm_eq_localLogTerm]
  exact (exp_tsum_eulerLocalLogTerm (norm_heckeLocalWeight_lt_one K chi p hs)).symm

/-- The triangular criterion for Hecke characters with the stated
analytic continuation and completion data. The Euler series and their
absolute convergence come from the character and its inverse. -/
theorem heckeCompletedCriterion
    {index : Type*} {realPlaces complexPlaces : index -> Type*}
    [forall i, Fintype (realPlaces i)] [forall i, Fintype (complexPlaces i)]
    (character : index -> UnitaryHeckeCharacter K)
    (dual : index -> index)
    (completedL poleRemoved equationFactor : index -> Complex -> Complex)
    (conductor : index -> Real) (poleOrder : index -> Nat)
    (mu : forall i, realPlaces i -> Complex) (nu : forall i, complexPlaces i -> Complex)
    (hConductor : forall i, 0 < conductor i)
    (hMu : forall i j, -(1 : Real) / 2 < (mu i j).re)
    (hNu : forall i j, -(1 : Real) / 2 < (nu i j).re)
    (hEntire : forall i, Differentiable Complex (poleRemoved i))
    (hOrder : forall i, Complex.Hadamard.EntireOfOrderAtMost 1 (completedL i))
    (hEuler : forall i s, 1 < s.re ->
      poleRemoved i s = (s - 1) ^ (poleOrder i) *
        (heckeEulerL K (character i) s * heckeEulerL K (unitaryHeckeInverse (character i)) s))
    (hCompletion : forall i s, (1 : Real) / 2 < s.re ->
      completedL i s * completedL (dual i) s =
        standardCompletionFactor (conductor i) (poleOrder i) (mu i) (nu i) s * poleRemoved i s)
    (hEquation : forall i s, completedL (dual i) (1 - s) =
      equationFactor i s * completedL i s) :
    CompletedFamilyRH completedL <->
      forall i, GrandRobinTriangularBound (heckePairedEulerData K (character i) (poleOrder i) (poleRemoved i)) := by
  haveI : Countable (HeckePrimePowers K) := countable_heckePrimePowers K
  let data (i : index) := heckePairedEulerData K (character i) (poleOrder i) (poleRemoved i)
  refine grandRobinCompletedCriterion_of_eulerProduct completedL equationFactor dual
    data conductor poleOrder mu nu hConductor hMu hNu (fun _ => rfl)
    (fun _ pn => two_le_heckePrimePowerNorm K pn) (fun _ T => finite_heckePrimePowerNorm_lt K T)
    (fun i _ hr => summable_heckePairedCoefficient K (character i) hr)
    hEntire hOrder ?_ hCompletion hEquation
  intro i s hs
  change poleRemoved i s = (s - 1) ^ (poleOrder i) * Complex.exp (grandEulerLog (data i) s)
  rw [heckePairedEulerProduct_eq K (character i) (poleOrder i) (poleRemoved i) hs]
  exact hEuler i s hs

end Robin1984.GRH
