import Robin1984.GRH.DirichletMultiplicityArithmetic
import Robin1984.GRH.MultiplicityArithmetic

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: The global arithmetic multiplicity criterion applied to every Dirichlet L-function.
- Formalization note: Under Dirichlet GRH this proves equivalence of the complex prime-power inequality and simplicity in the open critical strip.
- PROVENANCE-END
-/

/-!
# A global criterion for simple Dirichlet zeros

Under Dirichlet GRH, the exact twisted von Mangoldt inequalities detect
simplicity of every individual Dirichlet L-function in the critical strip.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open Complex.Hadamard
open scoped Classical

/-- The Gaussian global inequality of the actual twisted von Mangoldt remainder. -/
def DirichletMultiplicityInequality {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) : Prop :=
  GaussianMultiplicityInequality (triangularLogSignal
    (complexTriangularRemainder riemannPrimePowerNorm (dirichletPrimePowerCoefficient chi)
      (dirichletMultiplicityPoleOrder chi)))

private theorem order_pos_of_entire_zero {F : Complex -> Complex} (hF : Differentiable Complex F)
    (hNonzero : exists w, Not (F w = 0)) {z : Complex} (hZero : F z = 0) :
    0 < analyticOrderNatAt F z := by
  have h0 : Not (analyticOrderAt F z = 0) := fun h =>
    ((hF.analyticAt z).analyticOrderAt_eq_zero.mp h) hZero
  have ht : Not (analyticOrderAt F z = Top.top) := by
    intro he
    have hD := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (fun w => hF.analyticAt w)).mp he
    choose w hw using hNonzero
    exact hw (congrFun hD w)
  exact ENat.toNat_pos h0 ht

private theorem dirichletPoleClearedFactor_zero_iff {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) {z : Complex} (hz : Not (z = 1)) :
    dirichletPoleClearedFactor chi z = 0 <-> DirichletCharacter.LFunction chi z = 0 := by
  rw [dirichletPoleClearedFactor_eq_off_pole chi hz]
  have hP : Not ((if chi = 1 then z - 1 else 1) = 0) := by
    by_cases h : chi = 1
    case pos => simpa only [if_pos h] using sub_ne_zero.mpr hz
    case neg => simp [h]
  exact Iff.intro (fun h => (mul_eq_zero.mp h).resolve_left hP) (fun h => by rw [h, mul_zero])

private theorem dirichletOrderOne_in_strip_iff_criticalOccurrences_injective {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N)
    (hRH : forall z : Complex, 0 < z.re -> z.re < 1 ->
      DirichletCharacter.LFunction chi z = 0 -> z.re = 1 / 2) :
    (forall z : Complex, 0 < z.re -> z.re < 1 -> DirichletCharacter.LFunction chi z = 0 ->
      analyticOrderNatAt (DirichletCharacter.LFunction chi) z = 1) <->
    Function.Injective (criticalHadamardOrdinate (F := dirichletPoleClearedFactor chi)) := by
  rw [injective_criticalHadamardOrdinate_iff (differentiable_dirichletPoleClearedFactor chi)]
  have hNonzero : exists w, Not (dirichletPoleClearedFactor chi w = 0) :=
    Exists.intro 1 (dirichletPoleClearedFactor_ne_zero_of_one_le_re chi (by norm_num))
  have hOne {z : Complex} (hz : z.re < 1) : Not (z = 1) := by
    intro h
    rw [h, Complex.one_re] at hz
    exact lt_irrefl _ hz
  constructor
  case mp =>
    intro h z hline hZero
    have hz0 : 0 < z.re := by rw [hline]; norm_num
    have hz1 : z.re < 1 := by rw [hline]; norm_num
    have hZero' := (dirichletPoleClearedFactor_zero_iff chi (hOne hz1)).mp hZero
    rw [analyticOrderNatAt_dirichletPoleClearedFactor_eq chi (hOne hz1), h z hz0 hz1 hZero']
  case mpr =>
    intro h z hz0 hz1 hZero
    have hF := (dirichletPoleClearedFactor_zero_iff chi (hOne hz1)).mpr hZero
    have hPos := order_pos_of_entire_zero (differentiable_dirichletPoleClearedFactor chi) hNonzero hF
    have hLe := h z (hRH z hz0 hz1 hZero) hF
    rw [<- analyticOrderNatAt_dirichletPoleClearedFactor_eq chi (hOne hz1)]
    exact le_antisymm hLe (Nat.succ_le_of_lt hPos)

private theorem dirichlet_simpleZeros_iff_globalMultiplicityInequality {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N)
    (hRH : forall z : Complex, 0 < z.re -> z.re < 1 ->
      DirichletCharacter.LFunction chi z = 0 -> z.re = 1 / 2) :
    (forall z : Complex, 0 < z.re -> z.re < 1 -> DirichletCharacter.LFunction chi z = 0 ->
      analyticOrderNatAt (DirichletCharacter.LFunction chi) z = 1) <->
    DirichletMultiplicityInequality chi := by
  let F := dirichletPoleClearedFactor chi
  have hO := dirichletPoleClearedFactor_entireOrderOne chi
  have hNZ : exists w, Not (F w = 0) :=
    Exists.intro 1 (dirichletPoleClearedFactor_ne_zero_of_one_le_re chi (by norm_num))
  let _ : Countable (entireNonzeroZeroIndex F) := countable_entireNonzeroZeroIndex hO hNZ
  let i := criticalHadamardOccurrence F
  let g : i -> Real := criticalHadamardOrdinate
  let b := dirichletPrimePowerCoefficient chi
  let m := dirichletMultiplicityPoleOrder chi
  let A := triangularLogSignal (complexTriangularRemainder riemannPrimePowerNorm b m)
  have hTrace := complexTriangularLogSignal_has_criticalSpectrum riemannPrimePowerNorm b m F
    one_le_riemannPrimePowerNorm riemannPrimePowerNorm_locallyFinite
    (fun _ hr => summable_norm_dirichletPrimePowerCoefficient chi hr)
    hO hNZ (fun _ => dirichletPoleClearedFactor_zero_re_le_half chi hRH)
    (fun _ hs => dirichletPoleClearedFactor_logDeriv chi hs)
  choose C hC using hTrace.1
  have hSum := summable_criticalHadamardOccurrence_denominator hO hNZ
  have hIff := gaussianMultiplicityInequality_iff_injective A g
    (measurable_complexTriangularLogSignal riemannPrimePowerNorm b m) hC hSum hTrace.2
  exact (dirichletOrderOne_in_strip_iff_criticalOccurrences_injective chi hRH).trans hIff.symm

/-- **Dirichlet GRH and simple zeros.** Under Dirichlet GRH, every
nontrivial zero of every Dirichlet L-function is simple exactly when each
character satisfies the global Gaussian-smoothed prime-power inequality. -/
theorem dirichletGRH_simpleZeros_iff_globalMultiplicityInequality (hGRH : DirichletGRH) :
    (forall (N : Nat) [NeZero N] (chi : DirichletCharacter Complex N) (z : Complex),
      0 < z.re -> z.re < 1 -> DirichletCharacter.LFunction chi z = 0 ->
        analyticOrderNatAt (DirichletCharacter.LFunction chi) z = 1) <->
    (forall (N : Nat) [NeZero N] (chi : DirichletCharacter Complex N),
      DirichletMultiplicityInequality chi) := by
  constructor
  case mp =>
    intro h N _ chi
    exact (dirichlet_simpleZeros_iff_globalMultiplicityInequality chi (hGRH N chi)).mp (h N chi)
  case mpr =>
    intro h N _ chi
    exact (dirichlet_simpleZeros_iff_globalMultiplicityInequality chi (hGRH N chi)).mpr (h N chi)

end Robin1984.GRH
