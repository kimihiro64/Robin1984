import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Valued.LocallyCompact
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
The local integral uses the multiplicative Haar measure normalized by the
compact valuation-one subgroup, whose compactness follows from the finite
residue field of the completion.
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


/-- The actual Hecke prime-power coefficients give the growth bound for
a pole-free paired completion when it is bounded on the middle strip. -/
theorem entireOrderOne_heckePair_of_stripBound
    {realPlaces complexPlaces : Type*} [Fintype realPlaces] [Fintype complexPlaces]
    (chi : UnitaryHeckeCharacter K) {conductor : Real} (hConductor : 0 < conductor)
    (mu : realPlaces -> Complex) (nu : complexPlaces -> Complex)
    (hMu : forall i, -(1 : Real) / 2 < (mu i).re)
    (hNu : forall i, -(1 : Real) / 2 < (nu i).re)
    {Lambda : Complex -> Complex}
    (hEntire : Differentiable Complex Lambda)
    (hCompletion : forall s : Complex, 1 < s.re ->
      Lambda s = standardCompletionFactor conductor 0 mu nu s *
        (heckeEulerL K chi s * heckeEulerL K (unitaryHeckeInverse chi) s))
    (hReflect : forall s : Complex, norm (Lambda (1 - s)) = norm (Lambda s))
    (hStrip : forall eps : Real, 0 < eps -> exists C : Real, 0 < C /\
      forall s : Complex, -2 <= s.re -> s.re <= 3 ->
        norm (Lambda s) <= Real.exp (C * (1 + norm s) ^ (1 + eps))) :
    Complex.Hadamard.EntireOfOrderAtMost 1 Lambda := by
  let F : Complex -> Complex := fun _ => 0
  let d := heckePairedEulerData K chi 0 F
  refine entireOrderOne_of_standardPairedEulerProduct_and_stripBound d
    (two_le_heckePrimePowerNorm K) (summable_heckePairedCoefficient K chi (by norm_num))
    hConductor 0 mu nu hMu hNu hEntire ?_ hReflect hStrip
  intro s hs
  have hs1 : 1 < s.re := (by norm_num : (1 : Real) < 3).trans_le hs
  rw [pow_zero, one_mul, heckePairedEulerProduct_eq K chi 0 F hs1]
  exact hCompletion s hs1

/-- The pole-free Hecke criterion needs the growth bound for each paired
completion. The ordinary functions are obtained from the standard factors. -/
theorem heckePoleFreeCompletedCriterion_of_pairOrder
    {index : Type*} {realPlaces complexPlaces : index -> Type*}
    [forall i, Fintype (realPlaces i)] [forall i, Fintype (complexPlaces i)]
    (character : index -> UnitaryHeckeCharacter K) (dual : index -> index)
    (completedL equationFactor : index -> Complex -> Complex)
    (conductor : index -> Real)
    (mu : forall i, realPlaces i -> Complex) (nu : forall i, complexPlaces i -> Complex)
    (hConductor : forall i, 0 < conductor i)
    (hMu : forall i j, -(1 : Real) / 2 < (mu i j).re)
    (hNu : forall i j, -(1 : Real) / 2 < (nu i j).re)
    (hPairedOrder : forall i, Complex.Hadamard.EntireOfOrderAtMost 1 (fun s => completedL i s * completedL (dual i) s))
    (hCompletedEuler : forall i s, 1 < s.re ->
      completedL i s * completedL (dual i) s =
        standardCompletionFactor (conductor i) 0 (mu i) (nu i) s *
          (heckeEulerL K (character i) s * heckeEulerL K (unitaryHeckeInverse (character i)) s))
    (hEquation : forall i s, completedL (dual i) (1 - s) =
      equationFactor i s * completedL i s) :
    CompletedFamilyRH completedL <-> forall i,
      GrandRobinTriangularBound (heckePairedEulerData K (character i) 0 (fun _ => 0)) := by
  haveI : Countable (HeckePrimePowers K) := countable_heckePrimePowers K
  have hOrdinary (i : index) := exists_entireOrderOne_of_standardCompletion_noPole
    (hConductor i) (mu i) (nu i) (hMu i) (hNu i) (hPairedOrder i)
  choose F hOrder hFCompletion using hOrdinary
  let factor (i : index) := standardCompletionFactor (conductor i) 0 (mu i) (nu i)
  let data (i : index) := heckePairedEulerData K (character i) 0 (F i)
  have hFactor (i : index) (s : Complex) (hs : (1 : Real) / 2 < s.re) :
      Not (factor i s = 0) :=
    standardCompletionFactor_ne_zero (hConductor i) 0 (mu i) (nu i) (hMu i) (hNu i) hs
  have hSummable (i : index) (r : Real) (hr : 1 < r) :=
    summable_heckePairedCoefficient K (character i) hr
  have hEuler (i : index) (s : Complex) (hs : 1 < s.re) :
      (data i).poleRemoved s = (s - 1) ^ (0 : Nat) * Complex.exp (grandEulerLog (data i) s) := by
    have hsHalf : (1 : Real) / 2 < s.re := (by norm_num : (1 : Real) / 2 < 1).trans hs
    change F i s = (s - 1) ^ (0 : Nat) * Complex.exp (grandEulerLog (data i) s)
    rw [pow_zero, one_mul, heckePairedEulerProduct_eq K (character i) 0 (F i) hs]
    have h := (hFCompletion i s hsHalf).symm.trans (hCompletedEuler i s hs)
    change factor i s * F i s = factor i s *
      (heckeEulerL K (character i) s * heckeEulerL K (unitaryHeckeInverse (character i)) s) at h
    have hZero : factor i s * (F i s -
        heckeEulerL K (character i) s * heckeEulerL K (unitaryHeckeInverse (character i)) s) = 0 := by
      rw [mul_sub, h, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hZero).resolve_left (hFactor i s hsHalf))
  have hLocal (i : index) (s : Complex) (hs : 1 < s.re) :=
    grandEulerAnalytic_of_eulerLog (data i) 0 rfl (two_le_heckePrimePowerNorm K)
      (hSummable i) (hEuler i) hs
  change CompletedFamilyRH completedL <-> forall i, GrandRobinTriangularBound (data i)
  exact grandRobinCompletedCriterion_of_entireOrder completedL factor equationFactor dual data
    (fun _ pn => one_le_two.trans (two_le_heckePrimePowerNorm K pn))
    (fun _ T => finite_heckePrimePowerNorm_lt K T) hSummable hOrder
    (fun i s hs => (hLocal i s hs).1) (fun i s hs => (hLocal i s hs).2)
    hFCompletion hFactor hEquation


/-! ## Finite local Tate integrals -/

section TateFactors

open MeasureTheory MeasureTheory.Measure

/-- The integral of a geometric series supported on measurable shells of
unit measure is its usual Euler factor. -/
private theorem integral_geometric_shells {X : Type*} [MeasurableSpace X]
    (M : Measure X) (shell : Nat -> Set X)
    (hMeas : forall n, MeasurableSet (shell n))
    (hMass : forall n, M (shell n) = 1) {z : Complex} (hz : norm z < 1) :
    integral M (fun x => tsum (fun n => Set.indicator (shell n) (fun _ => z ^ n) x)) =
      Inv.inv (1 - z) := by
  let F (n : Nat) := Set.indicator (shell n) (fun _ : X => z ^ n)
  have hInt (n : Nat) : Integrable (F n) M :=
    (integrable_indicator_iff (hMeas n)).mpr (integrableOn_const (C := z ^ n) (by simp [hMass n]))
  have hReal (n : Nat) : M.real (shell n) = 1 := by
    simp only [Measure.real, hMass n, ENNReal.toReal_one]
  have hTerm (n : Nat) : integral M (F n) = z ^ n := by
    rw [integral_indicator_const (z ^ n) (hMeas n), hReal n, one_smul]
  have hNormTerm (n : Nat) : integral M (fun x => norm (F n x)) = norm z ^ n := by
    have hEq (x : X) : norm (F n x) = Set.indicator (shell n) (fun _ : X => norm z ^ n) x := by
      classical
      by_cases hx : Membership.mem (shell n) x
      case pos => simp [F, hx, norm_pow]
      case neg => simp [F, hx]
    simp only [hEq, integral_indicator_const _ (hMeas n), hReal n, one_smul]
  have hSum : Summable (fun n => integral M (fun x => norm (F n x))) := by
    simpa only [hNormTerm] using summable_geometric_of_lt_one (norm_nonneg z) hz
  change integral M (fun x => tsum (fun n => F n x)) = _
  rw [<- integral_tsum_of_summable_integral_norm hInt hSum]
  simp only [hTerm]
  exact tsum_geometric_of_norm_lt_one hz

/-- When the shells are disjoint and the integrand has a constant geometric
value on each shell, its integral over their union is the local Euler factor. -/
private theorem integral_on_geometric_shells {X : Type*} [MeasurableSpace X]
    (M : Measure X) (shell : Nat -> Set X) (weight : X -> Complex)
    (hMeas : forall n, MeasurableSet (shell n))
    (hMass : forall n, M (shell n) = 1)
    (hDisjoint : Pairwise (fun n m => Disjoint (shell n) (shell m)))
    {z : Complex} (hz : norm z < 1)
    (hWeight : forall n x, Membership.mem (shell n) x -> weight x = z ^ n) :
    integral M (Set.indicator (iUnion shell) weight) = Inv.inv (1 - z) := by
  classical
  have hEq (x : X) : Set.indicator (iUnion shell) weight x =
      tsum (fun n => Set.indicator (shell n) (fun _ => z ^ n) x) := by
    by_cases hx : Membership.mem (iUnion shell) x
    case pos =>
      choose n hn using Set.mem_iUnion.mp hx
      have hSingle (j : Nat) (hj : Not (j = n)) :
          Set.indicator (shell j) (fun _ => z ^ j) x = 0 := by
        have hjx : Not (Membership.mem (shell j) x) :=
          fun hjx => (Set.disjoint_left.mp (hDisjoint hj)) hjx hn
        exact Set.indicator_of_notMem hjx _
      have hTsum : tsum (fun j => Set.indicator (shell j) (fun _ => z ^ j) x) =
          Set.indicator (shell n) (fun _ => z ^ n) x := tsum_eq_single n hSingle
      rw [Set.indicator_of_mem hx, hWeight n x hn, hTsum, Set.indicator_of_mem hn]
    case neg =>
      rw [Set.indicator_of_notMem hx]
      have hZero (n : Nat) : Set.indicator (shell n) (fun _ => z ^ n) x = 0 :=
        Set.indicator_of_notMem (fun hn => hx (Set.mem_iUnion.mpr (Exists.intro n hn))) _
      simp only [hZero, tsum_zero]
  rw [funext hEq]
  exact integral_geometric_shells M shell hMeas hMass hz

/-- A multiplicative local weight trivial on the unit shell integrates to
its Euler factor over the union of the uniformizer shells. -/
private theorem integral_unramified_uniformizerShells
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (M : Measure G) [Measure.IsMulLeftInvariant M] (unitShell : Set G)
    (hMeas : MeasurableSet unitShell) (hMass : M unitShell = 1)
    (uniformizer : G) (weight : MonoidHom G Complex)
    (hUnit : forall x, Membership.mem unitShell x -> weight x = 1)
    (hDisjoint : Pairwise (fun n m : Nat => Disjoint
      (Set.preimage (fun x : G => Inv.inv (uniformizer ^ n) * x) unitShell)
      (Set.preimage (fun x : G => Inv.inv (uniformizer ^ m) * x) unitShell)))
    (hNorm : norm (weight uniformizer) < 1) :
    integral M (Set.indicator
      (iUnion (fun n : Nat => Set.preimage (fun x : G => Inv.inv (uniformizer ^ n) * x) unitShell))
      weight) = Inv.inv (1 - weight uniformizer) := by
  let shell (n : Nat) := Set.preimage (fun g : G => Inv.inv (uniformizer ^ n) * g) unitShell
  have hPres (n : Nat) := measurePreserving_mul_left M (Inv.inv (uniformizer ^ n))
  have hMeasShell (n : Nat) : MeasurableSet (shell n) := (hPres n).measurable hMeas
  have hMassShell (n : Nat) : M (shell n) = 1 :=
    ((hPres n).measure_preimage hMeas.nullMeasurableSet).trans hMass
  refine integral_on_geometric_shells M shell weight hMeasShell hMassShell hDisjoint hNorm ?_
  intro n x hx
  have hx' : x = uniformizer ^ n * (Inv.inv (uniformizer ^ n) * x) := by
    rw [<- mul_assoc, mul_inv_cancel, one_mul]
  calc
    _ = weight (uniformizer ^ n * (Inv.inv (uniformizer ^ n) * x)) := congrArg weight hx'
    _ = _ := by rw [map_mul, hUnit _ hx, map_pow, mul_one]

section FinitePlace

variable {L : Type*} [Field L] [NumberField L]
variable (p : HeightOneSpectrum (RingOfIntegers L))

/-- The nonzero local valuation takes values in the multiplicative
integers when restricted to units of the local field. -/
noncomputable def heckeLocalValueIndex :
    MonoidHom (Units (p.adicCompletion L)) (Multiplicative Int) :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (Valued.v : Valuation (p.adicCompletion L) (WithZero (Multiplicative Int))).toMonoidHom)

theorem coe_heckeLocalValueIndex (a : Units (p.adicCompletion L)) :
    (heckeLocalValueIndex p a : WithZero (Multiplicative Int)) =
      Valued.v (a : p.adicCompletion L) :=
  WithZero.coe_unitsWithZeroEquiv_eq_units_val _

/-- The unit shell of the local field consists of the valuation-one elements. -/
def heckeLocalUnitShell : Set (Units (p.adicCompletion L)) :=
  Set.ofPred (fun a => Valued.v (a : p.adicCompletion L) = (1 : WithZero (Multiplicative Int)))

/-- The complex unramified weight combines the finite character and the
power of the normalized finite absolute value. -/
noncomputable def heckeLocalTateWeight (chi : UnitaryHeckeCharacter L) (s : Complex) :
    MonoidHom (Units (p.adicCompletion L)) Complex where
  toFun a :=
    (chi.val (localIdeleHom L p a) : Complex) *
      Complex.exp (((Multiplicative.toAdd (heckeLocalValueIndex p a) : Int) : Complex) *
        (Real.log (dedekindPrimeNorm L p : Real) : Complex) * s)
  map_one' := by
    simp [map_one, Complex.exp_zero]
  map_mul' a b := by
    have hAdd (x y : Multiplicative Int) :
        Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + Multiplicative.toAdd y := rfl
    simp only [map_mul, Circle.coe_mul, hAdd, Int.cast_add, add_mul, Complex.exp_add]
    ac_rfl

/-- A valuation-one element contributes multiplicative weight one in the
unramified case. -/
theorem heckeLocalTateWeight_eq_one (chi : UnitaryHeckeCharacter L)
    (hUnramified : HeckeUnramifiedAt chi p) (s : Complex)
    (a : Units (p.adicCompletion L)) (ha : Membership.mem (heckeLocalUnitShell p) a) :
    heckeLocalTateWeight p chi s a = 1 := by
  have hA : Valued.v (a : p.adicCompletion L) = (1 : WithZero (Multiplicative Int)) := ha
  have hIndex : heckeLocalValueIndex p a = 1 := by
    apply WithZero.coe_inj.mp
    rw [coe_heckeLocalValueIndex p a, hA]
    rfl
  change (chi.val (localIdeleHom L p a) : Complex) *
    Complex.exp (((Multiplicative.toAdd (heckeLocalValueIndex p a) : Int) : Complex) *
      (Real.log (dedekindPrimeNorm L p : Real) : Complex) * s) = 1
  simp [hUnramified a hA, hIndex]

private theorem heckeLocalValueIndex_uniformizer (a : Units (p.adicCompletion L))
    (ha : Valued.v (a : p.adicCompletion L) = finiteUniformizerValue) :
    heckeLocalValueIndex p a = Multiplicative.ofAdd (-1 : Int) := by
  apply WithZero.coe_inj.mp
  rw [coe_heckeLocalValueIndex p a, ha]
  rfl

/-- At a uniformizer the weight is the Hecke Euler parameter times the
prime norm to the negative complex exponent. -/
theorem heckeLocalTateWeight_uniformizer (chi : UnitaryHeckeCharacter L)
    (hUnramified : HeckeUnramifiedAt chi p) (s : Complex)
    (a : Units (p.adicCompletion L)) (ha : Valued.v (a : p.adicCompletion L) = finiteUniformizerValue) :
    heckeLocalTateWeight p chi s a =
      heckeLocalParameter chi p * (dedekindPrimeNorm L p : Complex) ^ (-s) := by
  have hN : (1 : Real) < (dedekindPrimeNorm L p : Real) := by
    exact_mod_cast one_lt_dedekindPrimeNorm L p
  have hArg : 0 < (dedekindPrimeNorm L p : Real) := zero_lt_one.trans hN
  change (chi.val (localIdeleHom L p a) : Complex) *
    Complex.exp (((Multiplicative.toAdd (heckeLocalValueIndex p a) : Int) : Complex) *
      (Real.log (dedekindPrimeNorm L p : Real) : Complex) * s) = _
  rw [<- heckeLocalParameter_eq_of_uniformizer chi p hUnramified a ha,
    heckeLocalValueIndex_uniformizer p a ha, <- Complex.ofReal_natCast,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hArg.ne')]
  have hCast :
      ((Multiplicative.toAdd (Multiplicative.ofAdd (-1 : Int)) : Int) : Complex) = -1 := by
    change ((-1 : Int) : Complex) = -1
    norm_num
  rw [hCast, <- Complex.ofReal_log hArg.le]
  congr 2
  ring

private theorem heckeLocalUnitShell_iff_index_one (x : Units (p.adicCompletion L)) :
    Membership.mem (heckeLocalUnitShell p) x <-> heckeLocalValueIndex p x = 1 := by
  change Valued.v (x : p.adicCompletion L) = ((1 : Multiplicative Int) : WithZero (Multiplicative Int))
    <-> heckeLocalValueIndex p x = 1
  rw [<- coe_heckeLocalValueIndex p x]
  exact WithZero.coe_inj

private theorem toAdd_uniformizerValue_pow (n : Nat) :
    Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : Int)) ^ n) = -(n : Int) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    change Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : Int)) ^ k) + (-1 : Int) =
      -(Nat.succ k : Int)
    rw [ih, Nat.cast_succ]
    ring

private theorem mem_heckeLocalUniformizerShell_iff
    (a : Units (p.adicCompletion L)) (ha : Valued.v (a : p.adicCompletion L) = finiteUniformizerValue)
    (n : Nat) (x : Units (p.adicCompletion L)) :
    Membership.mem (Set.preimage (fun u => Inv.inv (a ^ n) * u) (heckeLocalUnitShell p)) x <->
      Multiplicative.toAdd (heckeLocalValueIndex p x) = -(n : Int) := by
  change Membership.mem (heckeLocalUnitShell p) (Inv.inv (a ^ n) * x) <-> _
  rw [heckeLocalUnitShell_iff_index_one, map_mul, map_inv, map_pow,
    heckeLocalValueIndex_uniformizer p a ha]
  change -(Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : Int)) ^ n)) +
      Multiplicative.toAdd (heckeLocalValueIndex p x) = 0 <-> _
  rw [toAdd_uniformizerValue_pow]
  constructor
  case mp =>
    intro h
    linarith only [h]
  case mpr =>
    intro h
    rw [h, neg_neg, add_neg_cancel]

/-- Distinct nonnegative powers of a uniformizer index disjoint shells. -/
theorem heckeLocalUniformizerShells_pairwiseDisjoint
    (a : Units (p.adicCompletion L)) (ha : Valued.v (a : p.adicCompletion L) = finiteUniformizerValue) :
    Pairwise (fun n m : Nat => Disjoint
      (Set.preimage (fun x => Inv.inv (a ^ n) * x) (heckeLocalUnitShell p))
      (Set.preimage (fun x => Inv.inv (a ^ m) * x) (heckeLocalUnitShell p))) := by
  intro n m hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hn := (mem_heckeLocalUniformizerShell_iff p a ha n x).mp hx
  have hm := (mem_heckeLocalUniformizerShell_iff p a ha m x).mp hy
  exact hne (by exact_mod_cast neg_injective (hn.symm.trans hm))

/-- The nonzero integral local elements have nonpositive logarithmic
valuation, with the uniformizer normalized to minus one. -/
def heckeLocalIntegralUnits : Set (Units (p.adicCompletion L)) :=
  Set.ofPred (fun x => Multiplicative.toAdd (heckeLocalValueIndex p x) <= 0)

theorem heckeLocalUniformizerShells_eq_integralUnits
    (a : Units (p.adicCompletion L)) (ha : Valued.v (a : p.adicCompletion L) = finiteUniformizerValue) :
    iUnion (fun n : Nat => Set.preimage (fun x => Inv.inv (a ^ n) * x) (heckeLocalUnitShell p)) =
      heckeLocalIntegralUnits p := by
  ext x
  constructor
  case mp =>
    intro hx
    choose n hn using Set.mem_iUnion.mp hx
    have h := (mem_heckeLocalUniformizerShell_iff p a ha n x).mp hn
    change Multiplicative.toAdd (heckeLocalValueIndex p x) <= 0
    rw [h]
    exact neg_nonpos.mpr (by positivity)
  case mpr =>
    intro hx
    change Multiplicative.toAdd (heckeLocalValueIndex p x) <= 0 at hx
    let n := Int.toNat (-(Multiplicative.toAdd (heckeLocalValueIndex p x)))
    have hN : (n : Int) = -(Multiplicative.toAdd (heckeLocalValueIndex p x)) :=
      Int.toNat_of_nonneg (neg_nonneg.mpr hx)
    refine Set.mem_iUnion.mpr (Exists.intro n ((mem_heckeLocalUniformizerShell_iff p a ha n x).mpr ?_))
    linarith only [hN]

/-- With the local Haar normalization, the unramified test function
integrates to the Euler factor for every parameter with positive real part. -/
theorem integral_unramifiedHeckeLocalFactor
    [MeasurableSpace (Units (p.adicCompletion L))]
    [MeasurableMul (Units (p.adicCompletion L))]
    (M : Measure (Units (p.adicCompletion L))) [Measure.IsMulLeftInvariant M]
    (hMeas : MeasurableSet (heckeLocalUnitShell p)) (hMass : M (heckeLocalUnitShell p) = 1)
    (chi : UnitaryHeckeCharacter L) (hUnramified : HeckeUnramifiedAt chi p)
    (a : Units (p.adicCompletion L)) (ha : Valued.v (a : p.adicCompletion L) = finiteUniformizerValue)
    {s : Complex} (hs : 0 < s.re) :
    integral M (Set.indicator (heckeLocalIntegralUnits p) (heckeLocalTateWeight p chi s)) =
        Inv.inv (1 - heckeLocalParameter chi p * (dedekindPrimeNorm L p : Complex) ^ (-s)) := by
  have hN : (1 : Real) < (dedekindPrimeNorm L p : Real) := by
    exact_mod_cast one_lt_dedekindPrimeNorm L p
  have hNorm : norm (heckeLocalParameter chi p * (dedekindPrimeNorm L p : Complex) ^ (-s)) < 1 := by
    have hPow := Real.rpow_lt_rpow_of_exponent_lt hN (neg_lt_zero.mpr hs)
    rw [Real.rpow_zero] at hPow
    rw [norm_mul, <- Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hN), Complex.neg_re]
    exact (mul_le_mul_of_nonneg_right (norm_heckeLocalParameter_le_one chi p)
      (Real.rpow_nonneg (zero_le_one.trans hN.le) _)).trans_lt (by simpa only [one_mul] using hPow)
  rw [<- heckeLocalTateWeight_uniformizer p chi hUnramified s a ha] at hNorm
  rw [<- heckeLocalTateWeight_uniformizer p chi hUnramified s a ha,
    <- heckeLocalUniformizerShells_eq_integralUnits p a ha]
  exact integral_unramified_uniformizerShells M (heckeLocalUnitShell p) hMeas hMass a
    (heckeLocalTateWeight p chi s) (heckeLocalTateWeight_eq_one p chi hUnramified s)
    (heckeLocalUniformizerShells_pairwiseDisjoint p a ha) hNorm


/-- The ramified test density is the inverse character on the local unit
shell and vanishes outside that shell. -/
noncomputable def heckeLocalRamifiedTest (chi : UnitaryHeckeCharacter L) :
    Units (p.adicCompletion L) -> Complex :=
  Set.indicator (heckeLocalUnitShell p)
    (fun x => (chi.val (localIdeleHom L p (Inv.inv x)) : Complex))

/-- With the local Haar normalization, the ramified test function
integrates to the Euler factor one for every complex parameter. -/
theorem integral_ramifiedHeckeLocalFactor
    [MeasurableSpace (Units (p.adicCompletion L))]
    (M : Measure (Units (p.adicCompletion L)))
    (hMeas : MeasurableSet (heckeLocalUnitShell p)) (hMass : M (heckeLocalUnitShell p) = 1)
    (chi : UnitaryHeckeCharacter L) (hRamified : Not (HeckeUnramifiedAt chi p)) (s : Complex) :
    integral M (fun x => heckeLocalRamifiedTest p chi x * heckeLocalTateWeight p chi s x) =
      Inv.inv (1 - heckeLocalParameter chi p * (dedekindPrimeNorm L p : Complex) ^ (-s)) := by
  classical
  have hZero : heckeLocalParameter chi p = 0 := by
    unfold heckeLocalParameter
    rw [if_neg hRamified]
  rw [hZero, zero_mul, sub_zero, inv_one]
  have hPoint (x : Units (p.adicCompletion L)) :
      heckeLocalRamifiedTest p chi x * heckeLocalTateWeight p chi s x =
        Set.indicator (heckeLocalUnitShell p) (fun _ => (1 : Complex)) x := by
    by_cases hx : Membership.mem (heckeLocalUnitShell p) x
    case pos =>
      have hIdx := (heckeLocalUnitShell_iff_index_one p x).mp hx
      have hc : chi.val (localIdeleHom L p (Inv.inv x)) *
          chi.val (localIdeleHom L p x) = 1 := by
        rw [<- map_mul, <- map_mul, inv_mul_cancel, map_one, map_one]
      have hWeight :
          heckeLocalTateWeight p chi s x = (chi.val (localIdeleHom L p x) : Complex) := by
        change (chi.val (localIdeleHom L p x) : Complex) *
          Complex.exp (((Multiplicative.toAdd (heckeLocalValueIndex p x) : Int) : Complex) *
            (Real.log (dedekindPrimeNorm L p : Real) : Complex) * s) = _
        simp [hIdx]
      rw [heckeLocalRamifiedTest, Set.indicator_of_mem hx, Set.indicator_of_mem hx, hWeight]
      simpa only [Circle.coe_mul, Circle.coe_one] using congrArg (fun z : Circle => (z : Complex)) hc
    case neg =>
      simp [heckeLocalRamifiedTest, hx]
  rw [funext hPoint, integral_indicator_const (1 : Complex) hMeas]
  simp [Measure.real, hMass]


/-- The local test density for the Euler factor uses the integral elements
in the unramified case and the inverse character on units in the ramified case. -/
noncomputable def heckeLocalTateTest (chi : UnitaryHeckeCharacter L) :
    Units (p.adicCompletion L) -> Complex := by
  classical
  exact if HeckeUnramifiedAt chi p then
    Set.indicator (heckeLocalIntegralUnits p) (fun _ => 1)
    else heckeLocalRamifiedTest p chi

/-- With unit-shell measure one, the canonical finite test gives the
standard Hecke Euler factor on the local right half-plane. -/
theorem integral_heckeLocalTateFactor
    [MeasurableSpace (Units (p.adicCompletion L))]
    [MeasurableMul (Units (p.adicCompletion L))]
    (M : Measure (Units (p.adicCompletion L))) [Measure.IsMulLeftInvariant M]
    (hMeas : MeasurableSet (heckeLocalUnitShell p)) (hMass : M (heckeLocalUnitShell p) = 1)
    (chi : UnitaryHeckeCharacter L)
    {s : Complex} (hs : 0 < s.re) :
    integral M (fun x => heckeLocalTateTest p chi x * heckeLocalTateWeight p chi s x) =
      Inv.inv (1 - heckeLocalParameter chi p * (dedekindPrimeNorm L p : Complex) ^ (-s)) := by
  classical
  by_cases h : HeckeUnramifiedAt chi p
  case pos =>
    rw [heckeLocalTateTest, if_pos h]
    have hPoint (x : Units (p.adicCompletion L)) :
        Set.indicator (heckeLocalIntegralUnits p) (fun _ => (1 : Complex)) x *
            heckeLocalTateWeight p chi s x =
          Set.indicator (heckeLocalIntegralUnits p) (heckeLocalTateWeight p chi s) x := by
      by_cases hx : Membership.mem (heckeLocalIntegralUnits p) x
      case pos => simp [hx]
      case neg => simp [hx]
    rw [funext hPoint]
    exact integral_unramifiedHeckeLocalFactor p M hMeas hMass chi h
      (localUniformizer L p) (valuation_localUniformizer L p) hs
  case neg =>
    rw [heckeLocalTateTest, if_neg h]
    exact integral_ramifiedHeckeLocalFactor p M hMeas hMass chi h s

end FinitePlace

end TateFactors


section LocalHaar

open MeasureTheory Topology

variable {K : Type*} [Field K] [NumberField K]
variable (p : HeightOneSpectrum (RingOfIntegers K))

private theorem exists_lt_one_adicCompletionIntegers_sub
    (b : p.adicCompletionIntegers K) :
    Exists (fun a : RingOfIntegers K =>
      (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
        ((algebraMap (RingOfIntegers K) (p.adicCompletion K) a) -
          (b : p.adicCompletion K)) < 1) := by
  let V := (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
  have hnear : Filter.Eventually (fun x : p.adicCompletion K =>
      V (x - (b : p.adicCompletion K)) < 1) (nhds (b : p.adicCompletion K)) := by
    apply Valued.mem_nhds.mpr
    refine Exists.intro 1 ?_
    intro x hx
    change V.restrict (x - (b : p.adicCompletion K)) < 1 at hx
    change V (x - (b : p.adicCompletion K)) < 1
    exact V.restrict_lt_one_iff.mp hx
  have hK := (HeightOneSpectrum.denseRange_algebraMap (K := K) p).mem_nhds hnear
  choose k hk using hK
  let x := algebraMap K (p.adicCompletion K) k
  have hx : V (x - (b : p.adicCompletion K)) < 1 := hk
  have hb : V (b : p.adicCompletion K) <= 1 := b.property
  have hX : V x <= 1 := by
    calc
      V x = V ((x - (b : p.adicCompletion K)) + (b : p.adicCompletion K)) := by
        rw [sub_add_cancel]
      _ <= max (V (x - (b : p.adicCompletion K))) (V (b : p.adicCompletion K)) :=
        V.map_add _ _
      _ <= 1 := max_le (le_of_lt hx) hb
  have hvK : p.valuation K k <= 1 := by
    rw [<- HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := p)]
    exact hX
  have hO := p.exists_valuation_sub_lt_of_integer hvK 1
  choose a ha using hO
  refine Exists.intro a ?_
  have ha' : V (algebraMap (RingOfIntegers K) (p.adicCompletion K) a - x) < 1 := by
    rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K (p.adicCompletion K)]
    dsimp [x]
    rw [<- map_sub]
    let z := algebraMap (RingOfIntegers K) K a - k
    change Valued.v (z : p.adicCompletion K) < (1 : WithZero (Multiplicative Int))
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := p)]
    exact ha
  let A := algebraMap (RingOfIntegers K) (p.adicCompletion K) a
  calc
    V (A - (b : p.adicCompletion K)) =
        V ((A - x) + (x - (b : p.adicCompletion K))) := by
      rw [sub_add_sub_cancel]
    _ <= max (V (A - x)) (V (x - (b : p.adicCompletion K))) := V.map_add _ _
    _ < 1 := max_lt ha' hx




/-- Every residue class of the completed valuation ring is represented by a
global algebraic integer. -/
theorem surjective_heckeLocalResidueMap :
    Function.Surjective
      ((IsLocalRing.residue (p.adicCompletionIntegers K)).comp
        (algebraMap (RingOfIntegers K) (p.adicCompletionIntegers K))) := by
  let D := p.adicCompletionIntegers K
  let V := (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
  intro c
  have hc := IsLocalRing.residue_surjective c
  choose b hb using hc
  have haExists := exists_lt_one_adicCompletionIntegers_sub p b
  choose a ha using haExists
  refine Exists.intro a ?_
  change IsLocalRing.residue D (algebraMap (RingOfIntegers K) D a) = c
  rw [<- hb, <- sub_eq_zero, <- map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (Valuation.mem_maximalIdeal_iff (p.adicCompletion K) V).mpr ha




/-- Completion induces the residue field isomorphism at the same prime. -/
noncomputable def heckeLocalResidueEquiv :
    RingEquiv (HasQuotient.Quotient (RingOfIntegers K) p.asIdeal)
      (IsLocalRing.ResidueField (p.adicCompletionIntegers K)) := by
  let D := p.adicCompletionIntegers K
  let rho := (IsLocalRing.residue D).comp (algebraMap (RingOfIntegers K) D)
  have hKer : forall a : RingOfIntegers K, rho a = 0 <-> Membership.mem p.asIdeal a := by
    intro a
    change IsLocalRing.residue D (algebraMap (RingOfIntegers K) D a) = 0 <-> _
    rw [IsLocalRing.residue_eq_zero_iff]
    let V := (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
    have hMax : Membership.mem (IsLocalRing.maximalIdeal D)
        (algebraMap (RingOfIntegers K) D a) <->
        Valued.v (a : p.adicCompletion K) < (1 : WithZero (Multiplicative Int)) :=
      Valuation.mem_maximalIdeal_iff (p.adicCompletion K) V
    have hv := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) (v := p) a
    have hPrime := HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) p a
    exact hMax.trans (Iff.intro
      (fun h => hPrime.mp (hv.symm.trans_lt h))
      (fun h => hv.trans_lt (hPrime.mpr h)))
  let rhoBar := Ideal.Quotient.lift p.asIdeal rho (fun a ha => (hKer a).mpr ha)
  have hInj : Function.Injective rhoBar := by
    intro x y h
    have hx := Ideal.Quotient.mk_surjective x
    choose a ha using hx
    have hy := Ideal.Quotient.mk_surjective y
    choose b hb using hy
    rw [<- ha, <- hb] at h
    rw [<- ha, <- hb]
    change rho a = rho b at h
    apply sub_eq_zero.mp
    rw [<- map_sub, Ideal.Quotient.eq_zero_iff_mem]
    apply (hKer (a - b)).mp
    rw [map_sub, h, sub_self]
  have hSurj : Function.Surjective rhoBar := by
    intro c
    have h := surjective_heckeLocalResidueMap p c
    choose a ha using h
    exact Exists.intro (Ideal.Quotient.mk p.asIdeal a) ha
  exact RingEquiv.ofBijective rhoBar (And.intro hInj hSurj)

/-- The residue field of the finite completion is finite. -/
theorem finite_heckeLocalResidueField :
    Finite (IsLocalRing.ResidueField (p.adicCompletionIntegers K)) := by
  have hFinite : Finite (HasQuotient.Quotient (RingOfIntegers K) p.asIdeal) :=
    p.asIdeal.finiteQuotientOfFreeOfNeBot p.ne_bot
  exact @Finite.of_surjective _ _ hFinite _ (heckeLocalResidueEquiv p).surjective

/-- The ring of integers of a finite completion is compact. -/
theorem compactSpace_heckeLocalIntegers :
    CompactSpace (p.adicCompletionIntegers K) := by
  change CompactSpace (Valued.integer (p.adicCompletion K))
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    (And.intro
      (@IsClosed.completeSpace_coe (p.adicCompletion K) _ _ _
        (Valued.isClosed_valuationSubring _))
      (And.intro (inferInstance : IsDiscreteValuationRing (p.adicCompletionIntegers K))
        (finite_heckeLocalResidueField p)))




/-- The nonzero valuation of units is locally constant on every finite
completion. -/
theorem eventually_heckeLocalValueIndex_eq (a : Units (p.adicCompletion K)) :
    Filter.Eventually (fun b : Units (p.adicCompletion K) =>
      heckeLocalValueIndex p b = heckeLocalValueIndex p a) (nhds a) := by
  let V := (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
  have ha : Not (V (a : p.adicCompletion K) = 0) :=
    (Valuation.ne_zero_iff V).mpr a.ne_zero
  have hV : Filter.Eventually (fun b : p.adicCompletion K => V b = V a)
      (nhds (a : p.adicCompletion K)) := Valued.locally_const ha
  have hc : Continuous (fun b : Units (p.adicCompletion K) => (b : p.adicCompletion K)) :=
    Units.continuous_val
  refine (hc.continuousAt.eventually hV).mono ?_
  intro b hb
  apply WithZero.coe_inj.mp
  rw [coe_heckeLocalValueIndex, coe_heckeLocalValueIndex]
  exact hb

/-- The valuation-one subgroup of the local multiplicative group is open. -/
theorem isOpen_heckeLocalUnitShell : IsOpen (heckeLocalUnitShell p) := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  refine (eventually_heckeLocalValueIndex_eq p a).mono ?_
  intro b hb
  have hA : Valued.v (a : p.adicCompletion K) = (1 : WithZero (Multiplicative Int)) := ha
  change Valued.v (b : p.adicCompletion K) = (1 : WithZero (Multiplicative Int))
  rw [<- coe_heckeLocalValueIndex p b, hb, coe_heckeLocalValueIndex]
  exact hA

/-- The finite absolute value on local units is continuous. -/
theorem continuous_heckeFiniteAbsoluteValue :
    Continuous (fun a : Units (p.adicCompletion K) =>
      Real.exp (((Multiplicative.toAdd (heckeLocalValueIndex p a) : Int) : Real) *
        Real.log (dedekindPrimeNorm K p : Real))) := by
  rw [continuous_iff_continuousAt]
  intro a
  let F (x : Units (p.adicCompletion K)) :=
    Real.exp (((Multiplicative.toAdd (heckeLocalValueIndex p x) : Int) : Real) *
      Real.log (dedekindPrimeNorm K p : Real))
  have hEq : Filter.Eventually (fun x => F x = F a) (nhds a) := by
    refine (eventually_heckeLocalValueIndex_eq p a).mono ?_
    intro x hx
    show Real.exp (((Multiplicative.toAdd (heckeLocalValueIndex p x) : Int) : Real) * _) =
      Real.exp (((Multiplicative.toAdd (heckeLocalValueIndex p a) : Int) : Real) * _)
    rw [hx]
  change Tendsto F (nhds a) (nhds (F a))
  exact (Filter.tendsto_congr' hEq).mpr tendsto_const_nhds

/-- The open unit shell of a finite completion is compact. -/
theorem isCompact_heckeLocalUnitShell : IsCompact (heckeLocalUnitShell p) := by
  have h := compactSpace_heckeLocalIntegers p
  have hRing : IsCompact (p.adicCompletionIntegers K : Set (p.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr h
  have hUnits := (Submonoid.units_isCompact
    (S := (p.adicCompletionIntegers K).toSubring.toSubmonoid)) hRing
  convert hUnits using 1
  ext a
  exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
    (K := K) (v := p) (a := a)).symm

/-- The unit shell is a compact set with nonempty interior. -/
def heckeLocalUnitPositiveCompact :
    TopologicalSpace.PositiveCompacts (Units (p.adicCompletion K)) :=
  { toCompacts := { carrier := heckeLocalUnitShell p, isCompact' := isCompact_heckeLocalUnitShell p }
    interior_nonempty' := by
      rw [(isOpen_heckeLocalUnitShell p).interior_eq]
      exact Exists.intro 1 (by change Valued.v (1 : p.adicCompletion K) = _; exact map_one _) }

section Haar

variable [MeasurableSpace (Units (p.adicCompletion K))]
  [BorelSpace (Units (p.adicCompletion K))]

/-- Haar measure on the local multiplicative group, normalized by the units. -/
noncomputable def heckeLocalHaar : Measure (Units (p.adicCompletion K)) :=
  Measure.haarMeasure (heckeLocalUnitPositiveCompact p)

instance heckeLocalHaar_isMulLeftInvariant : Measure.IsMulLeftInvariant (heckeLocalHaar p) :=
  Measure.isMulLeftInvariant_haarMeasure _

theorem heckeLocalHaar_unitShell : heckeLocalHaar p (heckeLocalUnitShell p) = 1 :=
  Measure.haarMeasure_self

/-- The normalized Haar integral of the finite local test is the standard
Hecke Euler factor for positive real part. -/
theorem integral_heckeLocalTateFactor_haar
    (chi : UnitaryHeckeCharacter K) {s : Complex} (hs : 0 < s.re) :
    integral (heckeLocalHaar p)
      (fun x => heckeLocalTateTest p chi x * heckeLocalTateWeight p chi s x) =
      Inv.inv (1 - heckeLocalParameter chi p * (dedekindPrimeNorm K p : Complex) ^ (-s)) := by
  have hMul : MeasurableMul (Units (p.adicCompletion K)) :=
    { measurable_const_mul := fun x => (continuous_const_mul x).measurable
      measurable_mul_const := fun x => (continuous_mul_const x).measurable }
  exact @integral_heckeLocalTateFactor K _ _ p _ hMul (heckeLocalHaar p) _
    (isOpen_heckeLocalUnitShell p).measurableSet (heckeLocalHaar_unitShell p) chi s hs

end Haar

end LocalHaar

section IdeleNorm

variable {K : Type*} [Field K] [NumberField K]

/-- The finite local norms in an idele differ from one at only finitely
many places. -/
theorem finiteSupport_heckeFiniteIdeleFactors
    (a : Units (FiniteAdeleRing (RingOfIntegers K) K)) :
    Function.HasFiniteMulSupport (fun p : HeightOneSpectrum (RingOfIntegers K) =>
      norm (a.val p)) := by
  have h := (FiniteAdeleRing.isUnit_iff.mp a.isUnit).2
  apply Filter.eventually_cofinite.mp
  refine h.mono ?_
  intro p hp
  change norm (a.val p) = 1
  rw [FinitePlace.norm_def, hp]
  simp

/-- The product of the normalized finite absolute values of an idele. -/
noncomputable def heckeFiniteIdeleNorm :
    MonoidHom (Units (FiniteAdeleRing (RingOfIntegers K) K)) Real where
  toFun a := finprod (fun p : HeightOneSpectrum (RingOfIntegers K) => norm (a.val p))
  map_one' := by
    apply finprod_eq_one_of_forall_eq_one
    intro p
    change norm (1 : p.adicCompletion K) = 1
    exact norm_one
  map_mul' a b := by
    rw [<- finprod_mul_distrib
      (finiteSupport_heckeFiniteIdeleFactors a) (finiteSupport_heckeFiniteIdeleFactors b)]
    apply finprod_congr
    intro p
    change norm (a.val p * b.val p) = norm (a.val p) * norm (b.val p)
    exact norm_mul _ _

/-- The finite idelic norm is positive. -/
theorem heckeFiniteIdeleNorm_pos
    (a : Units (FiniteAdeleRing (RingOfIntegers K) K)) :
    0 < heckeFiniteIdeleNorm a := by
  classical
  change 0 < finprod (fun p : HeightOneSpectrum (RingOfIntegers K) => norm (a.val p))
  have h := finiteSupport_heckeFiniteIdeleFactors a
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ Set.Subset.rfl h]
  exact Finset.prod_pos (fun p _ => norm_pos_iff.mpr ((FiniteAdeleRing.isUnit_iff.mp a.isUnit).1 p))

/-- On principal finite ideles, the finite idelic norm equals the finite
product in the number-field product formula. -/
theorem heckeFiniteIdeleNorm_principal (a : Units K) :
    heckeFiniteIdeleNorm
      (Units.map (algebraMap K (FiniteAdeleRing (RingOfIntegers K) K)).toMonoidHom a) =
      finprod (fun w : FinitePlace K => w (a : K)) := by
  change finprod (fun p : HeightOneSpectrum (RingOfIntegers K) =>
      norm ((algebraMap K (FiniteAdeleRing (RingOfIntegers K) K) (a : K)) p)) = _
  rw [<- finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  congr 1

/-- The archimedean idelic norm has exponent one at real places and
exponent two at complex places. -/
noncomputable def heckeInfiniteIdeleNorm :
    MonoidHom (Units (InfiniteAdeleRing K)) Real where
  toFun a := Finset.prod Finset.univ (fun w : InfinitePlace K => norm (a.val w) ^ w.mult)
  map_one' := by
    apply Finset.prod_eq_one
    intro w _
    change norm (1 : w.Completion) ^ w.mult = 1
    rw [norm_one, one_pow]
  map_mul' a b := by
    rw [<- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro w _
    change norm (a.val w * b.val w) ^ w.mult = _
    rw [norm_mul, mul_pow]

/-- The archimedean idelic norm is positive. -/
theorem heckeInfiniteIdeleNorm_pos (a : Units (InfiniteAdeleRing K)) :
    0 < heckeInfiniteIdeleNorm a := by
  change 0 < Finset.prod Finset.univ (fun w : InfinitePlace K => norm (a.val w) ^ w.mult)
  apply Finset.prod_pos
  intro w _
  have hMul : a.val w * a.inv w = 1 :=
    congrArg (fun f : InfiniteAdeleRing K => f w) a.val_inv
  have hNonzero : Not (a.val w = 0) := by
    intro hZero
    rw [hZero, zero_mul] at hMul
    exact zero_ne_one hMul
  exact pow_pos (norm_pos_iff.mpr hNonzero) _

/-- The archimedean norm of a principal idele is the weighted product
of the original field element's archimedean absolute values. -/
theorem heckeInfiniteIdeleNorm_principal (a : Units K) :
    heckeInfiniteIdeleNorm
      (Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom a) =
      Finset.prod Finset.univ (fun w : InfinitePlace K => w (a : K) ^ w.mult) := by
  change Finset.prod Finset.univ (fun w : InfinitePlace K =>
      norm ((algebraMap K (InfiniteAdeleRing K) (a : K)) w) ^ w.mult) = _
  apply Finset.prod_congr rfl
  intro w _
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact congrArg (fun t : Real => t ^ w.mult)
    (InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.val (a : K)))

/-- The absolute idelic norm on the actual Mathlib adele ring. -/
noncomputable def heckeIdelicNorm :
    MonoidHom (Units (AdeleRing (RingOfIntegers K) K)) Real :=
  (heckeInfiniteIdeleNorm.comp
    (Units.map (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (RingOfIntegers K) K)).toMonoidHom)) *
  (heckeFiniteIdeleNorm.comp
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (RingOfIntegers K) K)).toMonoidHom))

/-- Every idele has strictly positive absolute idelic norm. -/
theorem heckeIdelicNorm_pos (a : Units (AdeleRing (RingOfIntegers K) K)) :
    0 < heckeIdelicNorm a :=
  mul_pos (heckeInfiniteIdeleNorm_pos _) (heckeFiniteIdeleNorm_pos _)

/-- The idelic norm is one on principal ideles, by the product formula. -/
theorem heckeIdelicNorm_principal (a : Units K) :
    heckeIdelicNorm
      (Units.map (algebraMap K (AdeleRing (RingOfIntegers K) K)).toMonoidHom a) = 1 := by
  let z := Units.map (algebraMap K (AdeleRing (RingOfIntegers K) K)).toMonoidHom a
  let piInf := (RingHom.fst (InfiniteAdeleRing K)
    (FiniteAdeleRing (RingOfIntegers K) K)).toMonoidHom
  let piFin := (RingHom.snd (InfiniteAdeleRing K)
    (FiniteAdeleRing (RingOfIntegers K) K)).toMonoidHom
  change heckeInfiniteIdeleNorm (Units.map piInf z) *
    heckeFiniteIdeleNorm (Units.map piFin z) = 1
  have hInf : Units.map piInf z =
      Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom a := by
    apply Units.ext
    rfl
  have hFin : Units.map piFin z =
      Units.map (algebraMap K (FiniteAdeleRing (RingOfIntegers K) K)).toMonoidHom a := by
    apply Units.ext
    rfl
  rw [hInf, hFin, heckeInfiniteIdeleNorm_principal, heckeFiniteIdeleNorm_principal]
  exact NumberField.prod_abs_eq_one a.ne_zero

/-- The product of finite absolute values is continuous in the units
topology of the restricted product. -/
theorem continuous_heckeFiniteIdeleNorm :
    Continuous (heckeFiniteIdeleNorm
      (K := K) : Units (FiniteAdeleRing (RingOfIntegers K) K) -> Real) := by
  let A := FiniteAdeleRing (RingOfIntegers K) K
  let I : Set A := {a | forall p : HeightOneSpectrum (RingOfIntegers K),
    Membership.mem (p.adicCompletionIntegers K) (a p)}
  let U : Set (Units A) := Set.inter
    (Set.preimage (fun a : Units A => a.val) I)
    (Set.preimage (fun a : Units A => a.inv) I)
  have hI : IsOpen I :=
    RestrictedProduct.isOpen_forall_mem
      (R := fun p : HeightOneSpectrum (RingOfIntegers K) => p.adicCompletion K)
      (A := fun p => (p.adicCompletionIntegers K : Set (p.adicCompletion K)))
      (fun p => Valued.isOpen_valuationSubring (p.adicCompletion K))
  have hU : IsOpen U :=
    (hI.preimage Units.continuous_val).inter (hI.preimage Units.continuous_coe_inv)
  have hOne : Membership.mem U (1 : Units A) := by
    refine And.intro ?_ ?_ <;> intro p <;> exact (p.adicCompletionIntegers K).one_mem
  have hNorm : forall a : Units A, Membership.mem U a -> heckeFiniteIdeleNorm a = 1 := by
    intro a ha
    apply finprod_eq_one_of_forall_eq_one
    intro p
    let aP := RestrictedProduct.unitsEquiv
      (fun q : HeightOneSpectrum (RingOfIntegers K) => q.adicCompletion K) a p
    have hP : Valued.v (a.val p) = (1 : WithZero (Multiplicative Int)) :=
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
        (K := K) (v := p) (a := aP)).mp (And.intro (ha.1 p) (ha.2 p))
    rw [FinitePlace.norm_def, hP]
    simp
  rw [continuous_iff_continuousAt]
  intro a
  have hOpen : IsOpen (Set.preimage (fun x : Units A => Inv.inv a * x) U) :=
    hU.preimage (continuous_const_mul (Inv.inv a))
  have hNear : Filter.Eventually (fun x : Units A => Membership.mem U (Inv.inv a * x)) (nhds a) :=
    hOpen.mem_nhds (by
      change Membership.mem U (Inv.inv a * a)
      rw [inv_mul_cancel]
      exact hOne)
  have hEq : Filter.Eventually (fun x : Units A =>
      heckeFiniteIdeleNorm x = heckeFiniteIdeleNorm a) (nhds a) := by
    refine hNear.mono ?_
    intro x hx
    calc
      heckeFiniteIdeleNorm x = heckeFiniteIdeleNorm (a * (Inv.inv a * x)) := by
        rw [<- mul_assoc, mul_inv_cancel, one_mul]
      _ = heckeFiniteIdeleNorm a := by rw [map_mul, hNorm _ hx, mul_one]
  exact (Filter.tendsto_congr' hEq).mpr tendsto_const_nhds

/-- The product of the archimedean absolute values is continuous. -/
theorem continuous_heckeInfiniteIdeleNorm :
    Continuous (heckeInfiniteIdeleNorm (K := K) : Units (InfiniteAdeleRing K) -> Real) := by
  change Continuous (fun a : Units (InfiniteAdeleRing K) =>
    Finset.prod Finset.univ (fun w : InfinitePlace K => norm (a.val w) ^ w.mult))
  apply continuous_finsetProd
  intro w _
  have hc : Continuous (fun a : InfiniteAdeleRing K => a w) := continuous_apply w
  exact ((hc.comp Units.continuous_val).norm).pow _

/-- The absolute idelic norm is continuous. -/
theorem continuous_heckeIdelicNorm :
    Continuous (heckeIdelicNorm (K := K) : Units (AdeleRing (RingOfIntegers K) K) -> Real) := by
  let piInf := (RingHom.fst (InfiniteAdeleRing K)
    (FiniteAdeleRing (RingOfIntegers K) K)).toMonoidHom
  let piFin := (RingHom.snd (InfiniteAdeleRing K)
    (FiniteAdeleRing (RingOfIntegers K) K)).toMonoidHom
  change Continuous (fun a : Units (AdeleRing (RingOfIntegers K) K) =>
    heckeInfiniteIdeleNorm (Units.map piInf a) * heckeFiniteIdeleNorm (Units.map piFin a))
  have hInf : Continuous piInf := continuous_fst
  have hFin : Continuous piFin := continuous_snd
  exact (continuous_heckeInfiniteIdeleNorm.comp (Units.continuous_map hInf)).mul
    (continuous_heckeFiniteIdeleNorm.comp (Units.continuous_map hFin))

/-- The unitary Hecke character obtained by raising the absolute idelic
norm to the imaginary power `i * t`. -/
noncomputable def heckeNormCharacter (t : Real) : UnitaryHeckeCharacter K := by
  let phi : ContinuousMonoidHom (Units (AdeleRing (RingOfIntegers K) K)) Circle :=
    { toFun := fun a => Circle.exp (t * Real.log (heckeIdelicNorm a))
      map_one' := by simp
      map_mul' := by
        intro a b
        rw [map_mul heckeIdelicNorm a b, Real.log_mul
          (ne_of_gt (heckeIdelicNorm_pos a)) (ne_of_gt (heckeIdelicNorm_pos b)),
          mul_add, Circle.exp_add]
      continuous_toFun :=
        Circle.exp.continuous.comp (continuous_const.mul
          (continuous_heckeIdelicNorm.log (fun a => ne_of_gt (heckeIdelicNorm_pos a)))) }
  refine Subtype.mk phi ?_
  intro a
  change Circle.exp (t * Real.log (heckeIdelicNorm
    (Units.map (algebraMap K (AdeleRing (RingOfIntegers K) K)).toMonoidHom a))) = 1
  rw [heckeIdelicNorm_principal, Real.log_one, mul_zero, Circle.exp_zero]

/-- The idelic norm on a single finite component is its normalized
local absolute value. -/
theorem heckeIdelicNorm_localIdeleHom
    (p : HeightOneSpectrum (RingOfIntegers K)) (a : Units (p.adicCompletion K)) :
    heckeIdelicNorm (localIdeleHom K p a) = norm (a : p.adicCompletion K) := by
  let z := localIdeleHom K p a
  let piInf := (RingHom.fst (InfiniteAdeleRing K)
    (FiniteAdeleRing (RingOfIntegers K) K)).toMonoidHom
  let piFin := (RingHom.snd (InfiniteAdeleRing K)
    (FiniteAdeleRing (RingOfIntegers K) K)).toMonoidHom
  change heckeInfiniteIdeleNorm (Units.map piInf z) *
    heckeFiniteIdeleNorm (Units.map piFin z) = _
  have hInf : Units.map piInf z = 1 := by
    apply Units.ext
    rfl
  rw [hInf, map_one, one_mul]
  let f (q : HeightOneSpectrum (RingOfIntegers K)) :=
    norm (finiteLocalAdele K p (a : p.adicCompletion K) q)
  change finprod f = norm (a : p.adicCompletion K)
  have hAway : forall q, Not (q = p) -> f q = 1 := by
    intro q hq
    change norm (finiteLocalAdele K p (a : p.adicCompletion K) q) = 1
    rw [finiteLocalAdele_away K p q (a : p.adicCompletion K) hq, norm_one]
  rw [finprod_eq_single f p hAway]
  change norm (finiteLocalAdele K p (a : p.adicCompletion K) p) = _
  rw [finiteLocalAdele_at]

/-- A pure idelic norm character is unramified at every finite prime. -/
theorem heckeNormCharacter_unramified
    (t : Real) (p : HeightOneSpectrum (RingOfIntegers K)) :
    HeckeUnramifiedAt (heckeNormCharacter t) p := by
  intro a ha
  have hNorm : norm (a : p.adicCompletion K) = 1 := by
    rw [FinitePlace.norm_def, ha]
    simp
  change Circle.exp (t * Real.log (heckeIdelicNorm (localIdeleHom K p a))) = 1
  rw [heckeIdelicNorm_localIdeleHom, hNorm, Real.log_one, mul_zero, Circle.exp_zero]

end IdeleNorm

end Robin1984.GRH
