import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order
import Robin1984.GRH.DedekindArchimedeanLogDerivative
import Robin1984.GRH.GrandRobin

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Euler's product for the reciprocal Gamma function, the standard automorphic completion, and the completed-family triangular criterion.
- Formalization note: Proves order at most one for the reciprocal Gamma factors, removes the archimedean factors, and applies the completed-family equivalence to paired Euler data.
- PROVENANCE-END
-/

/-!
# Growth bounds for standard L-function completions

The Euler product for the reciprocal Gamma function gives order at most one.
The reciprocal real and complex archimedean factors transfer the growth bound
of the pole-cleared completion to the entire pole-cleared ordinary function.
The triangular criterion then applies to any supplied dual-closed standard family
with the stated Euler product, completed functional equation and growth bounds.
-/

set_option autoImplicit false

open Filter Complex.Hadamard Set DedekindZeta

namespace Robin1984.GRH

/-- Uniform power bounds for the compensated factor in Euler's reciprocal
Gamma product, valid for every exponent between one and two. -/
private theorem norm_compensatedGammaFactor_le (z : Complex) {p : Real}
    (hp : 1 <= p) (hp2 : p <= 2) :
    norm ((1 + z) * Complex.exp (-z)) <= Real.exp (2 * norm z ^ p) := by
  by_cases hz : z = 0
  case pos => simp [hz, Real.zero_rpow (show Not (p = 0) by linarith)]
  case neg =>
    have h0 : 0 < norm z := norm_pos_iff.mpr hz
    rw [norm_mul, Complex.norm_exp, Complex.neg_re]
    by_cases hR : norm z <= 1
    case pos =>
      have hn : norm (1 + z) ^ (2 : Nat) = 1 + 2 * z.re + norm z ^ (2 : Nat) := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add]
        ring
      have he : norm (1 + z) ^ (2 : Nat) <=
          (Real.exp (z.re + norm z ^ (2 : Nat) / 2)) ^ (2 : Nat) := by
        rw [hn, pow_two (Real.exp _), <- Real.exp_add]
        rw [show z.re + norm z ^ (2 : Nat) / 2 + (z.re + norm z ^ (2 : Nat) / 2) =
          2 * z.re + norm z ^ (2 : Nat) by ring]
        calc
          _ = 2 * z.re + norm z ^ (2 : Nat) + 1 := by ring
          _ <= _ := Real.add_one_le_exp _
      have h1 : norm (1 + z) <= Real.exp (z.re + norm z ^ (2 : Nat) / 2) := by
        by_contra hi
        have hlt := lt_of_not_ge hi
        have hsum : 0 < norm (1 + z) + Real.exp (z.re + norm z ^ (2 : Nat) / 2) :=
          add_pos_of_nonneg_of_pos (norm_nonneg _) (Real.exp_pos _)
        have hprod := mul_pos (sub_pos.mpr hlt) hsum
        nlinarith only [hprod, he]
      have hPow : norm z ^ (2 : Nat) <= norm z ^ p := by
        rw [<- Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge h0 hR hp2
      calc
        _ <= Real.exp (z.re + norm z ^ (2 : Nat) / 2) * Real.exp (-z.re) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
        _ = Real.exp (norm z ^ (2 : Nat) / 2) := by rw [<- Real.exp_add]; congr 1; ring
        _ <= _ := Real.exp_le_exp.mpr (by
          have hpow0 := Real.rpow_nonneg h0.le p
          linarith only [hPow, hpow0])
    case neg =>
      have h1 : 1 <= norm z := le_of_lt (lt_of_not_ge hR)
      have hp1 : norm z <= norm z ^ p := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h1 hp
      have hR1 : norm (1 + z) <= Real.exp (norm z) := by
        calc
          _ <= 1 + norm z := by simpa only [norm_one] using norm_add_le (1 : Complex) z
          _ <= _ := by simpa only [add_comm] using Real.add_one_le_exp (norm z)
      have hIm : -z.re <= norm z := (neg_le_abs _).trans (Complex.abs_re_le_norm z)
      calc
        _ <= Real.exp (norm z) * Real.exp (-z.re) :=
          mul_le_mul_of_nonneg_right hR1 (Real.exp_nonneg _)
        _ <= _ := by
          rw [<- Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith only [hp1, hIm])

private theorem prod_natCast_succ_eq_factorial (n : Nat) :
    (Finset.range n).prod (fun i => ((i + 1 : Nat) : Complex)) = (n.factorial : Complex) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ, Nat.cast_mul, mul_comm]

private theorem inv_GammaSeq_eq_prod {n : Nat} (hn : 0 < n) (z : Complex) :
    Inv.inv (Complex.GammaSeq z n) =
      z * (n : Complex) ^ (-z) *
        (Finset.range n).prod (fun i => 1 + z / ((i + 1 : Nat) : Complex)) := by
  have hc : Not ((n : Complex) = 0) := Nat.cast_ne_zero.mpr hn.ne'
  have hP : Not ((n : Complex) ^ z = 0) :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hc)
  have hFact : Not ((n.factorial : Complex) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hTerm (i : Nat) : z + ((i + 1 : Nat) : Complex) =
      ((i + 1 : Nat) : Complex) * (1 + z / ((i + 1 : Nat) : Complex)) := by
    have hk : Not (((i + 1 : Nat) : Complex) = 0) := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    field_simp [hk]
    ring
  unfold Complex.GammaSeq
  rw [inv_div, Finset.prod_range_succ', Complex.cpow_neg]
  simp_rw [hTerm]
  rw [Finset.prod_mul_distrib, prod_natCast_succ_eq_factorial]
  simp only [Nat.cast_zero, add_zero]
  field_simp [hFact, hP]

private theorem norm_gammaEulerFactor_le (z : Complex) (j : Nat) {p : Real}
    (hp : 1 <= p) (hp2 : p <= 2) :
    norm (1 + z / ((j + 1 : Nat) : Complex)) <=
      Real.exp (2 * norm z ^ p * (1 / (((j + 1 : Nat) : Real) ^ p)) +
        z.re * Inv.inv (((j + 1 : Nat) : Real))) := by
  let u := z / ((j + 1 : Nat) : Complex)
  have h := norm_compensatedGammaFactor_le u hp hp2
  have hr : u.re = z.re * Inv.inv (((j + 1 : Nat) : Real)) := by
    change (z / ((j + 1 : Nat) : Complex)).re = _
    rw [Complex.div_natCast_re, div_eq_mul_inv]
  have hpow : norm u ^ p = norm z ^ p * (1 / (((j + 1 : Nat) : Real) ^ p)) := by
    change norm (z / ((j + 1 : Nat) : Complex)) ^ p = _
    rw [norm_div, Complex.norm_natCast, Real.div_rpow (norm_nonneg _) (by positivity),
      div_eq_mul_inv, one_div]
  rw [norm_mul, Complex.norm_exp, Complex.neg_re, hpow, hr] at h
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (z.re * Inv.inv (((j + 1 : Nat) : Real))))
  rw [mul_assoc, <- Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, <- Real.exp_add] at h'
  simpa only [u, mul_assoc] using h'

private theorem norm_inv_GammaSeq_le (z : Complex) {n : Nat} (hn : 0 < n) {p : Real}
    (hp : 1 <= p) (hp2 : p <= 2) :
    norm (Inv.inv (Complex.GammaSeq z n)) <=
      norm z * Real.exp
        (2 * norm z ^ p * (Finset.range n).sum (fun j => 1 / (((j + 1 : Nat) : Real) ^ p)) +
          z.re * ((harmonic n : Real) - Real.log n)) := by
  let a : Nat -> Real := fun j => 1 / (((j + 1 : Nat) : Real) ^ p)
  let b : Nat -> Real := fun j => Inv.inv (((j + 1 : Nat) : Real))
  let A : Real := 2 * norm z ^ p
  have hProd :
      norm ((Finset.range n).prod (fun j => 1 + z / ((j + 1 : Nat) : Complex))) <=
        Real.exp (A * (Finset.range n).sum a + z.re * (harmonic n : Real)) := by
    rw [norm_prod]
    calc
      _ <= (Finset.range n).prod (fun j => Real.exp (A * a j + z.re * b j)) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun j _ => norm_gammaEulerFactor_le z j hp hp2)
      _ = _ := by
        rw [<- Real.exp_sum, Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
        have hh : (Finset.range n).sum b = (harmonic n : Real) := by
          simp only [b, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        rw [hh]
  have hnR : 0 < (n : Real) := Nat.cast_pos.mpr hn
  have hC : norm ((n : Complex) ^ (-z)) = Real.exp (-z.re * Real.log n) := by
    rw [<- Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnR, Complex.neg_re,
      Real.rpow_def_of_pos hnR, mul_comm (Real.log (n : Real)) (-z.re)]
  rw [inv_GammaSeq_eq_prod hn, norm_mul, norm_mul, hC]
  calc
    _ <= norm z * Real.exp (-z.re * Real.log n) *
        Real.exp (A * (Finset.range n).sum a + z.re * (harmonic n : Real)) :=
      mul_le_mul_of_nonneg_left hProd (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
    _ = _ := by
      rw [mul_assoc, <- Real.exp_add]
      congr 2
      dsimp only [A, a]
      ring

private theorem summable_gammaEulerWeights {p : Real} (hp : 1 < p) :
    Summable (fun j : Nat => 1 / (((j + 1 : Nat) : Real) ^ p)) :=
  (summable_nat_add_iff (f := fun j : Nat => 1 / ((j : Real) ^ p)) 1).mpr
    (Real.summable_one_div_nat_rpow.mpr hp)

private theorem norm_inv_Gamma_le (z : Complex) {p : Real} (hp : 1 < p) (hp2 : p <= 2) :
    norm (Inv.inv (Complex.Gamma z)) <=
      norm z * Real.exp (2 * norm z ^ p *
        tsum (fun j : Nat => 1 / (((j + 1 : Nat) : Real) ^ p)) +
          z.re * Real.eulerMascheroniConstant) := by
  by_cases h : Complex.Gamma z = 0
  case pos => simp only [h, inv_zero, norm_zero]; positivity
  case neg =>
    let a : Nat -> Real := fun j => 1 / (((j + 1 : Nat) : Real) ^ p)
    have ha : Summable a := summable_gammaEulerWeights hp
    have hS : Tendsto (fun n : Nat => (Finset.range n).sum a) atTop (nhds (tsum a)) :=
      ha.hasSum.tendsto_sum_nat
    have hId : DifferentiableAt Complex (fun v : Complex => v) (Complex.Gamma z) :=
      differentiableAt_id
    have hInv : ContinuousAt (fun v : Complex => Inv.inv v) (Complex.Gamma z) :=
      (hId.inv h).continuousAt
    have hLimit : Tendsto (fun n : Nat => norm (Inv.inv (Complex.GammaSeq z n))) atTop
        (nhds (norm (Inv.inv (Complex.Gamma z)))) :=
      (hInv.tendsto.comp (Complex.GammaSeq_tendsto_Gamma z)).norm
    have hBoundLimit :
        Tendsto (fun n : Nat => norm z * Real.exp (2 * norm z ^ p *
          (Finset.range n).sum a + z.re * ((harmonic n : Real) - Real.log n))) atTop
          (nhds (norm z * Real.exp (2 * norm z ^ p * tsum a +
            z.re * Real.eulerMascheroniConstant))) :=
      (Real.continuous_exp.continuousAt.tendsto.comp
        ((hS.const_mul (2 * norm z ^ p)).add
          (Real.tendsto_harmonic_sub_log.const_mul z.re))).const_mul (norm z)
    apply le_of_tendsto_of_tendsto hLimit hBoundLimit
    filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
    exact norm_inv_GammaSeq_le z hn hp.le hp2

/-- The reciprocal Gamma function is entire of order at most one. -/
theorem reciprocalGamma_entireOfOrderAtMost_one :
    EntireOfOrderAtMost 1 (fun z : Complex => Inv.inv (Complex.Gamma z)) := by
  refine And.intro Complex.differentiable_one_div_Gamma ?_
  intro eps heps
  let p := min (1 + eps) 2
  have hp : 1 < p := lt_min (by linarith) (by norm_num)
  have hp2 : p <= 2 := min_le_right _ _
  have hpE : p <= 1 + eps := min_le_left _ _
  let S := tsum (fun j : Nat => 1 / (((j + 1 : Nat) : Real) ^ p))
  have hS : 0 <= S := tsum_nonneg (fun _ => by positivity)
  let C := 1 + (2 * S + abs Real.eulerMascheroniConstant)
  have hC : 0 < C := by
    dsimp only [C]
    linarith only [hS, abs_nonneg Real.eulerMascheroniConstant]
  refine Exists.intro C (And.intro hC (fun z => ?_))
  let M := (1 + norm z) ^ p
  have hBase : 1 <= 1 + norm z := le_add_of_nonneg_right (norm_nonneg _)
  have hR1 : norm z <= 1 + norm z := le_add_of_nonneg_left zero_le_one
  have hBasePow : 1 + norm z <= M := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hBase hp.le
  have hR : norm z <= M := hR1.trans hBasePow
  have hRp : norm z ^ p <= M := Real.rpow_le_rpow (norm_nonneg _) hR1 (zero_le_one.trans hp.le)
  have hRE : norm z <= Real.exp M := hR.trans
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp M))
  have hS' : 2 * norm z ^ p * S <= 2 * S * M := by
    have h := mul_le_mul_of_nonneg_left hRp (show 0 <= 2 * S by positivity)
    nlinarith only [h]
  have hGamma : z.re * Real.eulerMascheroniConstant <= abs Real.eulerMascheroniConstant * M := by
    calc
      _ <= abs (z.re * Real.eulerMascheroniConstant) := le_abs_self _
      _ = abs z.re * abs Real.eulerMascheroniConstant := abs_mul _ _
      _ <= _ := by
        rw [mul_comm (abs Real.eulerMascheroniConstant) M]
        exact mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm z).trans hR) (abs_nonneg _)
  have hExp : 2 * norm z ^ p * S + z.re * Real.eulerMascheroniConstant <=
      (2 * S + abs Real.eulerMascheroniConstant) * M := by
    nlinarith only [hS', hGamma]
  have hM : M <= (1 + norm z) ^ (1 + eps) :=
    Real.rpow_le_rpow_of_exponent_le hBase hpE
  calc
    _ <= norm z * Real.exp (2 * norm z ^ p * S + z.re * Real.eulerMascheroniConstant) :=
      norm_inv_Gamma_le z hp hp2
    _ <= Real.exp M * Real.exp ((2 * S + abs Real.eulerMascheroniConstant) * M) :=
      mul_le_mul hRE (Real.exp_le_exp.mpr hExp) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (C * M) := by rw [<- Real.exp_add]; congr 1; dsimp only [C]; ring
    _ <= _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hM hC.le)

private theorem one_le_one_add_norm_rpow (z : Complex) {eps : Real} (heps : 0 < eps) :
    1 <= (1 + norm z) ^ (1 + eps) := by
  have hb : 1 <= 1 + norm z := le_add_of_nonneg_right (norm_nonneg _)
  exact hb.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hb (show (1 : Real) <= 1 + eps by linarith))

private theorem norm_le_one_add_norm_rpow (z : Complex) {eps : Real} (heps : 0 < eps) :
    norm z <= (1 + norm z) ^ (1 + eps) := by
  have hb : 1 <= 1 + norm z := le_add_of_nonneg_right (norm_nonneg _)
  exact (le_add_of_nonneg_left zero_le_one : norm z <= 1 + norm z).trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hb (show (1 : Real) <= 1 + eps by linarith))

private theorem entireOrderOne_const (c : Complex) :
    EntireOfOrderAtMost 1 (fun _ : Complex => c) := by
  refine And.intro (differentiable_const c) (fun eps heps =>
    Exists.intro (norm c + 1) (And.intro (by positivity) (fun z => ?_)))
  calc
    _ <= Real.exp (norm c) :=
      (le_add_of_nonneg_right (by norm_num : (0 : Real) <= 1)).trans (Real.add_one_le_exp _)
    _ <= _ := by
      apply Real.exp_le_exp.mpr
      exact (le_add_of_nonneg_right (by norm_num : (0 : Real) <= 1)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_one_add_norm_rpow z heps))

private theorem entireOrderOne_mul {f g : Complex -> Complex}
    (hf : EntireOfOrderAtMost 1 f) (hg : EntireOfOrderAtMost 1 g) :
    EntireOfOrderAtMost 1 (fun z => f z * g z) := by
  refine And.intro (hf.differentiable.mul hg.differentiable) ?_
  intro eps heps
  choose C hC using hf.exists_bound heps
  choose D hD using hg.exists_bound heps
  refine Exists.intro (C + D) (And.intro (add_pos hC.1 hD.1) ?_)
  intro z
  rw [norm_mul]
  calc
    _ <= Real.exp (C * (1 + norm z) ^ (1 + eps)) *
        Real.exp (D * (1 + norm z) ^ (1 + eps)) :=
      mul_le_mul (hC.2 z) (hD.2 z) (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [<- Real.exp_add, add_mul]

private theorem entireOrderOne_affine {f : Complex -> Complex}
    (hf : EntireOfOrderAtMost 1 f) (a b : Complex) :
    EntireOfOrderAtMost 1 (fun z => f (a * z + b)) := by
  have hD : Differentiable Complex (fun z : Complex => a * z + b) :=
    ((differentiable_const a).mul differentiable_id).add_const b
  refine And.intro (hf.differentiable.comp hD) ?_
  intro eps heps
  choose C hC using hf.exists_bound heps
  let M := 1 + norm a + norm b
  have hM : 0 < M := by dsimp [M]; positivity
  refine Exists.intro (C * M ^ (1 + eps)) (And.intro (mul_pos hC.1 (Real.rpow_pos_of_pos hM _)) ?_)
  intro z
  have hArg : 1 + norm (a * z + b) <= M * (1 + norm z) := by
    calc
      _ <= 1 + (norm (a * z) + norm b) := add_le_add le_rfl (norm_add_le _ _)
      _ = 1 + (norm a * norm z + norm b) := by rw [norm_mul]
      _ <= _ := by
        dsimp only [M]
        nlinarith only [norm_nonneg z, norm_nonneg a, mul_nonneg (norm_nonneg b) (norm_nonneg z)]
  refine (hC.2 _).trans (Real.exp_le_exp.mpr ?_)
  have hPow := Real.rpow_le_rpow (by positivity : (0 : Real) <= 1 + norm (a * z + b))
    hArg (show 0 <= 1 + eps by linarith)
  rw [Real.mul_rpow hM.le (by positivity : (0 : Real) <= 1 + norm z)] at hPow
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hPow hC.1.le

private theorem entireOrderOne_exp_linear (a : Complex) :
    EntireOfOrderAtMost 1 (fun z => Complex.exp (a * z)) := by
  have hA : Differentiable Complex (fun z : Complex => a * z) :=
    (differentiable_const a).mul differentiable_id
  refine And.intro (Complex.differentiable_exp.comp hA) ?_
  intro eps heps
  refine Exists.intro (1 + norm a) (And.intro (by positivity) ?_)
  intro z
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm (a * z)).trans ?_)
  rw [norm_mul]
  calc
    _ <= norm a * (1 + norm z) ^ (1 + eps) :=
      mul_le_mul_of_nonneg_left (norm_le_one_add_norm_rpow z heps) (norm_nonneg _)
    _ <= _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)

private theorem entireOrderOne_const_cpow {a : Real} (ha : 0 < a) (c : Complex) :
    EntireOfOrderAtMost 1 (fun z => (a : Complex) ^ (c * z)) := by
  have hEq : (fun z : Complex => (a : Complex) ^ (c * z)) =
      (fun z => Complex.exp ((Complex.log (a : Complex) * c) * z)) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'), mul_assoc]
  rw [hEq]
  exact entireOrderOne_exp_linear _

private theorem entireOrderOne_finsetProd {iota : Type*} (s : Finset iota)
    (f : iota -> Complex -> Complex)
    (hf : forall i, Membership.mem s i -> EntireOfOrderAtMost 1 (f i)) :
    EntireOfOrderAtMost 1 (fun z => s.prod (fun i => f i z)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using entireOrderOne_const 1
  | insert i s hi ih =>
    have hI := hf i (Finset.mem_insert_self i s)
    have hS := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using entireOrderOne_mul hI hS

/-- The factor relating the pole-cleared completion and the pole-cleared
ordinary function. The conductor is positive and the shifts range over
all real and complex archimedean factors in the pair. -/
noncomputable def standardCompletionFactor {realPlaces complexPlaces : Type*}
    [Fintype realPlaces] [Fintype complexPlaces]
    (conductor : Real) (poleOrder : Nat)
    (mu : realPlaces -> Complex) (nu : complexPlaces -> Complex) (s : Complex) : Complex :=
  s ^ poleOrder * (conductor : Complex) ^ (s / 2) *
    (Finset.univ.prod (fun i => LReal (s + mu i))) *
    (Finset.univ.prod (fun i => LComplex (s + nu i)))

private theorem LReal_ne_zero_of_re_pos {s : Complex} (hs : 0 < s.re) :
    Not (LReal s = 0) := by
  have hHalf : 0 < (s / 2).re := by
    have hRe : (s / 2).re = s.re / 2 := by
      simp [div_eq_mul_inv, Complex.mul_re, Complex.inv_re]
    rw [hRe]
    positivity
  have hp : Not ((Real.pi : Complex) = 0) := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold LReal
  exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hp))
    (Complex.Gamma_ne_zero_of_re_pos hHalf)

private theorem LComplex_ne_zero_of_re_pos {s : Complex} (hs : 0 < s.re) :
    Not (LComplex s = 0) := by
  have hp : Not ((2 : Complex) * (Real.pi : Complex) = 0) :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold LComplex
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl hp)))
    (Complex.Gamma_ne_zero_of_re_pos hs)

/-- The standard archimedean parameter bounds give the nonvanishing
completion factor on the full strict right half-plane. -/
theorem standardCompletionFactor_ne_zero {realPlaces complexPlaces : Type*}
    [Fintype realPlaces] [Fintype complexPlaces]
    {conductor : Real} (hConductor : 0 < conductor) (poleOrder : Nat)
    (mu : realPlaces -> Complex) (nu : complexPlaces -> Complex)
    (hMu : forall i, -(1 : Real) / 2 < (mu i).re)
    (hNu : forall i, -(1 : Real) / 2 < (nu i).re)
    {s : Complex} (hs : (1 : Real) / 2 < s.re) :
    Not (standardCompletionFactor conductor poleOrder mu nu s = 0) := by
  have hs0 : 0 < s.re := (by norm_num : (0 : Real) < 1 / 2).trans hs
  have hS : Not (s ^ poleOrder = 0) := pow_ne_zero _ (Complex.ne_zero_of_re_pos hs0)
  have hQ : Not ((conductor : Complex) ^ (s / 2) = 0) :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hConductor.ne'))
  have hArg (z : Complex) (hz : -(1 : Real) / 2 < z.re) : 0 < (s + z).re := by
    rw [Complex.add_re]
    linarith only [hs, hz]
  have hReal : Not ((Finset.univ.prod (fun i => LReal (s + mu i))) = 0) := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact LReal_ne_zero_of_re_pos (hArg (mu i) (hMu i))
  have hComplex : Not ((Finset.univ.prod (fun i => LComplex (s + nu i))) = 0) := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact LComplex_ne_zero_of_re_pos (hArg (nu i) (hNu i))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hS hQ) hReal) hComplex

private theorem entireOrderOne_of_mul_pow {f g : Complex -> Complex}
    (hf : Differentiable Complex f) (hg : EntireOfOrderAtMost 1 g) (m : Nat)
    (hEq : forall z, z ^ m * f z = g z) : EntireOfOrderAtMost 1 f := by
  refine And.intro hf ?_
  intro eps heps
  choose C hC using hg.exists_bound heps
  have hBdd : BddAbove ((fun z : Complex => norm (f z)) '' Metric.closedBall 0 1) :=
    ((isCompact_closedBall (0 : Complex) 1).image hf.continuous.norm).bddAbove
  choose B hB using hBdd
  let D : Real := C + |B| + 1
  have hD : 0 < D := by dsimp [D]; linarith [hC.1, abs_nonneg B]
  refine Exists.intro D (And.intro hD (fun z => ?_))
  by_cases hz : 1 <= norm z
  case pos =>
    have hPow (k : Nat) : (1 : Real) <= norm z ^ k := by
      induction k with
      | zero => rw [pow_zero]
      | succ n hn =>
        rw [pow_succ]
        calc
          _ = 1 * 1 := (one_mul _).symm
          _ <= _ := mul_le_mul hn hz zero_le_one (pow_nonneg (norm_nonneg _) _)
    have hNorm : norm (f z) <= norm (g z) := by
      rw [<- hEq, norm_mul, norm_pow]
      calc
        _ = 1 * norm (f z) := (one_mul _).symm
        _ <= _ := mul_le_mul_of_nonneg_right (hPow m) (norm_nonneg _)
    refine hNorm.trans ((hC.2 z).trans (Real.exp_le_exp.mpr ?_))
    exact mul_le_mul_of_nonneg_right (by dsimp [D]; linarith [abs_nonneg B])
      (Real.rpow_nonneg (by positivity) _)
  case neg =>
    have hBall : Membership.mem (Metric.closedBall (0 : Complex) 1) z := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (lt_of_not_ge hz).le
    have hNorm : norm (f z) <= B := hB (Set.mem_image_of_mem _ hBall)
    calc
      _ <= B := hNorm
      B <= D := by dsimp [D]; linarith [le_abs_self B, hC.1]
      D <= Real.exp D :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp D)
      _ <= _ := Real.exp_le_exp.mpr
        (le_mul_of_one_le_right hD.le (one_le_one_add_norm_rpow z heps))

private theorem entireOrderOne_inv_LReal :
    EntireOfOrderAtMost 1 (fun z => Inv.inv (LReal z)) := by
  have hGamma : EntireOfOrderAtMost 1 (fun z : Complex => Inv.inv (Complex.Gamma (z / 2))) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (entireOrderOne_affine reciprocalGamma_entireOfOrderAtMost_one (Inv.inv (2 : Complex)) 0)
  have hPi : EntireOfOrderAtMost 1 (fun z : Complex => (Real.pi : Complex) ^ (z / 2)) := by
    simpa [div_eq_mul_inv, mul_comm] using entireOrderOne_const_cpow Real.pi_pos (Inv.inv (2 : Complex))
  have hEq : (fun z : Complex => Inv.inv (LReal z)) =
      (fun z : Complex => (Real.pi : Complex) ^ (z / 2) * Inv.inv (Complex.Gamma (z / 2))) := by
    funext z
    simp [LReal, neg_div, Complex.cpow_neg, mul_comm]
  rw [hEq]
  exact entireOrderOne_mul hPi hGamma

private theorem entireOrderOne_inv_LComplex :
    EntireOfOrderAtMost 1 (fun z => Inv.inv (LComplex z)) := by
  have hPi : EntireOfOrderAtMost 1 (fun z : Complex => ((2 : Complex) * (Real.pi : Complex)) ^ z) := by
    simpa only [one_mul, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      entireOrderOne_const_cpow (mul_pos (by norm_num : (0 : Real) < 2) Real.pi_pos) 1
  have hEq : (fun z : Complex => Inv.inv (LComplex z)) =
      (fun z : Complex => (Inv.inv (2 : Complex)) *
        (((2 : Complex) * (Real.pi : Complex)) ^ z * Inv.inv (Complex.Gamma z))) := by
    funext z
    simp [LComplex, Complex.cpow_neg]
    ac_rfl
  rw [hEq]
  exact entireOrderOne_mul (entireOrderOne_const _)
    (entireOrderOne_mul hPi reciprocalGamma_entireOfOrderAtMost_one)

private noncomputable def standardReciprocalArchimedeanFactor {realPlaces complexPlaces : Type*}
    [Fintype realPlaces] [Fintype complexPlaces]
    (conductor : Real) (mu : realPlaces -> Complex) (nu : complexPlaces -> Complex)
    (s : Complex) : Complex :=
  (conductor : Complex) ^ (-(s / 2)) *
    (Finset.univ.prod (fun i => Inv.inv (LReal (s + mu i)))) *
    (Finset.univ.prod (fun i => Inv.inv (LComplex (s + nu i))))

private theorem entireOrderOne_standardReciprocalArchimedeanFactor {realPlaces complexPlaces : Type*}
    [Fintype realPlaces] [Fintype complexPlaces] {conductor : Real} (hConductor : 0 < conductor)
    (mu : realPlaces -> Complex) (nu : complexPlaces -> Complex) :
    EntireOfOrderAtMost 1 (standardReciprocalArchimedeanFactor conductor mu nu) := by
  have hQ : EntireOfOrderAtMost 1 (fun s : Complex => (conductor : Complex) ^ (-(s / 2))) := by
    have hEq (s : Complex) : -(s / 2) = (-1 / 2 : Complex) * s := by ring
    simpa only [hEq] using entireOrderOne_const_cpow hConductor (-1 / 2)
  have hMu : EntireOfOrderAtMost 1 (fun s : Complex =>
      Finset.univ.prod (fun i => Inv.inv (LReal (s + mu i)))) :=
    entireOrderOne_finsetProd _ _ (fun i _ => by
      simpa only [one_mul] using entireOrderOne_affine entireOrderOne_inv_LReal 1 (mu i))
  have hNu : EntireOfOrderAtMost 1 (fun s : Complex =>
      Finset.univ.prod (fun i => Inv.inv (LComplex (s + nu i)))) :=
    entireOrderOne_finsetProd _ _ (fun i _ => by
      simpa only [one_mul] using entireOrderOne_affine entireOrderOne_inv_LComplex 1 (nu i))
  exact entireOrderOne_mul (entireOrderOne_mul hQ hMu) hNu

private theorem standardCompletionFactor_mul_reciprocal {realPlaces complexPlaces : Type*}
    [Fintype realPlaces] [Fintype complexPlaces] {conductor : Real} (hConductor : 0 < conductor)
    (m : Nat) (mu : realPlaces -> Complex) (nu : complexPlaces -> Complex)
    (hMu : forall i, -(1 : Real) / 2 < (mu i).re)
    (hNu : forall i, -(1 : Real) / 2 < (nu i).re)
    {s : Complex} (hs : (1 : Real) / 2 < s.re) :
    standardCompletionFactor conductor m mu nu s *
      standardReciprocalArchimedeanFactor conductor mu nu s = s ^ m := by
  have hQ : (conductor : Complex) ^ (s / 2) * (conductor : Complex) ^ (-(s / 2)) = 1 := by
    rw [Complex.cpow_neg, <- div_eq_mul_inv, div_self]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hConductor.ne'))
  have hArg (z : Complex) (hz : -(1 : Real) / 2 < z.re) : 0 < (s + z).re := by
    rw [Complex.add_re]
    linarith only [hs, hz]
  have hReal : (Finset.univ.prod (fun i => LReal (s + mu i))) *
      (Finset.univ.prod (fun i => Inv.inv (LReal (s + mu i)))) = 1 := by
    rw [<- Finset.prod_mul_distrib]
    calc
      _ = Finset.univ.prod (fun _ : realPlaces => (1 : Complex)) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [<- div_eq_mul_inv, div_self (LReal_ne_zero_of_re_pos (hArg (mu i) (hMu i)))]
      _ = 1 := Finset.prod_const_one
  have hComplex : (Finset.univ.prod (fun i => LComplex (s + nu i))) *
      (Finset.univ.prod (fun i => Inv.inv (LComplex (s + nu i)))) = 1 := by
    rw [<- Finset.prod_mul_distrib]
    calc
      _ = Finset.univ.prod (fun _ : complexPlaces => (1 : Complex)) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [<- div_eq_mul_inv, div_self (LComplex_ne_zero_of_re_pos (hArg (nu i) (hNu i)))]
      _ = 1 := Finset.prod_const_one
  unfold standardCompletionFactor standardReciprocalArchimedeanFactor
  calc
    _ = s ^ m *
        ((conductor : Complex) ^ (s / 2) * (conductor : Complex) ^ (-(s / 2))) *
        ((Finset.univ.prod (fun i => LReal (s + mu i))) *
          (Finset.univ.prod (fun i => Inv.inv (LReal (s + mu i))))) *
        ((Finset.univ.prod (fun i => LComplex (s + nu i))) *
          (Finset.univ.prod (fun i => Inv.inv (LComplex (s + nu i))))) := by ac_rfl
    _ = s ^ m := by rw [hQ, hReal, hComplex, mul_one, mul_one, mul_one]

/-- The reciprocal archimedean factors transfer the order-one bound for
the pole-cleared completion to the entire pole-cleared ordinary function. -/
theorem entireOrderOne_of_standardCompletion {realPlaces complexPlaces : Type*}
    [Fintype realPlaces] [Fintype complexPlaces] {conductor : Real} (hConductor : 0 < conductor)
    (m : Nat) (mu : realPlaces -> Complex) (nu : complexPlaces -> Complex)
    (hMu : forall i, -(1 : Real) / 2 < (mu i).re)
    (hNu : forall i, -(1 : Real) / 2 < (nu i).re)
    {F Lambda : Complex -> Complex}
    (hF : Differentiable Complex F) (hLambda : EntireOfOrderAtMost 1 Lambda)
    (hCompletion : forall s : Complex, (1 : Real) / 2 < s.re ->
      Lambda s = standardCompletionFactor conductor m mu nu s * F s) :
    EntireOfOrderAtMost 1 F := by
  let Q := standardReciprocalArchimedeanFactor conductor mu nu
  have hQ : EntireOfOrderAtMost 1 Q :=
    entireOrderOne_standardReciprocalArchimedeanFactor hConductor mu nu
  have hProduct : EntireOfOrderAtMost 1 (fun s => Lambda s * Q s) :=
    entireOrderOne_mul hLambda hQ
  have hPower : Differentiable Complex (fun s : Complex => s ^ m * F s) :=
    (differentiable_id.pow m).mul hF
  have hRe : (1 : Real) / 2 < (2 : Complex).re := by norm_num
  have hAgree : Filter.EventuallyEq (nhds (2 : Complex))
      (fun s : Complex => s ^ m * F s) (fun s => Lambda s * Q s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hRe] with s hs
    rw [hCompletion s hs, mul_right_comm, standardCompletionFactor_mul_reciprocal hConductor m mu nu hMu hNu hs]
  have hAll : Set.EqOn (fun s : Complex => s ^ m * F s) (fun s => Lambda s * Q s) Set.univ :=
    (hPower.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      (hProduct.differentiable.differentiableOn.analyticOnNhd isOpen_univ)
      isPreconnected_univ (mem_univ (2 : Complex)) hAgree
  exact entireOrderOne_of_mul_pow hF hProduct m (fun s => hAll (mem_univ s))

/-- The triangular bound is equivalent to the completed zero assertion
for a dual-closed standard family with order-one pole-cleared completions.
The real and complex Gamma factors and the positive conductor give both
the order bound for the ordinary functions and the right-half-plane
nonvanishing factor. -/
theorem grandRobinCompletedCriterion_of_standardCompletion
    {Representation : Type*} {powers : Representation -> Type*}
    {realPlaces complexPlaces : Representation -> Type*}
    [forall pi, Countable (powers pi)]
    [forall pi, Fintype (realPlaces pi)] [forall pi, Fintype (complexPlaces pi)]
    (completedL equationFactor : Representation -> Complex -> Complex)
    (dual : Representation -> Representation)
    (data : forall pi, GrandRobinEulerData (powers pi))
    (conductor : Representation -> Real) (originOrder : Representation -> Nat)
    (mu : forall pi, realPlaces pi -> Complex) (nu : forall pi, complexPlaces pi -> Complex)
    (hConductor : forall pi, 0 < conductor pi)
    (hMu : forall pi i, -(1 : Real) / 2 < (mu pi i).re)
    (hNu : forall pi i, -(1 : Real) / 2 < (nu pi i).re)
    (hNorm : forall pi i, 1 <= (data pi).normPower i)
    (hFinite : forall pi T, Set.Finite {i : powers pi | (data pi).normPower i < T})
    (hSummable : forall pi (r : Real), 1 < r ->
      Summable (fun i => norm ((data pi).coefficient i) * ((data pi).normPower i) ^ (-r)))
    (hEntire : forall pi, Differentiable Complex (data pi).poleRemoved)
    (hCompletedOrder : forall pi, EntireOfOrderAtMost 1 (completedL pi))
    (hNonzero : forall pi s, 1 < s.re -> Not ((data pi).poleRemoved s = 0))
    (hEuler : forall pi s, 1 < s.re ->
      logDeriv (data pi).poleRemoved s = ((data pi).poleOrder : Complex) / (s - 1) -
        tsum (fun i => ((data pi).coefficient i : Complex) *
          ((data pi).normPower i : Complex) ^ (-s)))
    (hCompletion : forall pi s, (1 / 2 : Real) < s.re ->
      completedL pi s * completedL (dual pi) s =
        standardCompletionFactor (conductor pi) (originOrder pi) (mu pi) (nu pi) s *
          (data pi).poleRemoved s)
    (hEquation : forall pi s, completedL (dual pi) (1 - s) =
      equationFactor pi s * completedL pi s) :
    CompletedFamilyRH completedL <-> forall pi, GrandRobinTriangularBound (data pi) := by
  have hOrder (pi : Representation) : EntireOfOrderAtMost 1 (data pi).poleRemoved :=
    entireOrderOne_of_standardCompletion (hConductor pi) (originOrder pi) (mu pi) (nu pi)
      (hMu pi) (hNu pi) (hEntire pi)
      (entireOrderOne_mul (hCompletedOrder pi) (hCompletedOrder (dual pi))) (hCompletion pi)
  exact grandRobinCompletedCriterion_of_entireOrder completedL
    (fun pi => standardCompletionFactor (conductor pi) (originOrder pi) (mu pi) (nu pi))
    equationFactor dual data hNorm hFinite hSummable hOrder hNonzero hEuler hCompletion
    (fun pi _ hs => standardCompletionFactor_ne_zero (hConductor pi) (originOrder pi)
      (mu pi) (nu pi) (hMu pi) (hNu pi) hs) hEquation

end Robin1984.GRH
