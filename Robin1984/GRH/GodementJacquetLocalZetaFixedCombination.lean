import Robin1984.GRH.GodementJacquetLocalZetaCoefficientOrbit

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement-Jacquet local zeta integrals and the determinant change of variables under matrix translation.
- Formalization note: Replaces exponent-dependent polynomial weights by constant coefficients on a finite family of translated compact tests.
- PROVENANCE-END
-/

/-!
# Fixed local tests realizing a canonical Godement-Jacquet factor

Apply matrix translations with negative powers of a uniformizer determinant
to absorb the polynomial Euler weights into the local tests and coefficients.
The resulting compact tests, translations, and complex weights are fixed
throughout the half-plane of absolute convergence.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField

namespace Robin1984.GRH

private def negativeNatEmbedding : Function.Embedding Nat Int :=
  Function.Embedding.mk (fun k => -(k : Int))
    (fun _ _ h => Int.ofNat_inj.mp (neg_injective h))

private theorem eval_inv_eq_negativeLaurent (A : Polynomial Complex) (z : Complex) :
    A.eval (Inv.inv z) = (A.support.map negativeNatEmbedding).sum
      (fun j => A.coeff j.natAbs * z ^ j) := by
  rw [Finset.sum_map, Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro k _
  change A.coeff k * (Inv.inv z) ^ k = A.coeff (-(k : Int)).natAbs * z ^ (-(k : Int))
  simp [zpow_neg, inv_pow]

section

variable {K : Type*} [Field K] [NumberField K]
variable (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)

local notation "L" => p.adicCompletion K
local notation "G" => Units (Matrix (Fin (n + 1)) (Fin (n + 1)) L)
local notation "Test" => LocallyConstant (Matrix (Fin (n + 1)) (Fin (n + 1)) L) Complex

/-- The fixed local combination also makes each translated term absolutely
integrable on the same right half-plane. -/
theorem exists_heckeLocalZeta_fixedReciprocalCombination_termwise
    [MeasurableSpace G] [MeasurableMul G]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (u : Units L) (hu : Valued.v u.val = finiteUniformizerValue)
    (D : Polynomial Complex) (c : G -> Complex)
    (hGen : HasHeckeLocalZetaInverseCombination mu
      (fun s : Complex => (norm u.val : Complex) ^ s) D c) :
    exists (m : Nat) (U : Fin m -> G) (Phi : Fin m -> Int -> Test)
        (S : Fin m -> Finset Int) (a : Fin m -> Int -> Complex) (tau : Real),
      And (forall i j, HasCompactSupport (fun X => Phi i j X))
        (forall s : Complex, tau < s.re ->
          let f (g : G) := Finset.univ.sum (fun i : Fin m =>
            (S i).sum (fun j => a i j * ((norm g.val.det : Complex) ^ s *
              (Phi i j g.val * c (U i ^ j * g)))))
          And (forall i : Fin m, forall j : Int,
            Integrable (fun g : G => (norm g.val.det : Complex) ^ s *
              (Phi i j g.val * c (U i ^ j * g))) mu)
            (And (Integrable f mu)
              (integral mu f = Inv.inv (D.eval ((norm u.val : Complex) ^ s))))) := by
  classical
  choose m Phi A tau h using hGen
  have hTranslate (i : Fin m) :=
    exists_heckeLocalZetaTest_primeNormLaurentTranslate p n mu u hu (Phi i) (h.1 i) c
  choose U hU using hTranslate
  have hLocal (i : Fin m) := (hU i).2
  choose Psi hPsi using hLocal
  let S (i : Fin m) := (A i).support.map negativeNatEmbedding
  let a (i : Fin m) (j : Int) := (A i).coeff j.natAbs
  refine Exists.intro m (Exists.intro U (Exists.intro Psi (Exists.intro S (Exists.intro a
    (Exists.intro tau (And.intro (fun i => (hPsi i).1) ?_))))))
  intro s hs f
  let z := (norm u.val : Complex) ^ s
  let q := (dedekindPrimeNorm K p : Complex) ^ s
  have hNorm := norm_eq_inv_of_valuation_finiteUniformizer p u.val hu
  have hz : z = Inv.inv q := by
    dsimp only [z, q]
    rw [hNorm, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) s,
      Complex.ofReal_natCast]
  have hEval (i : Fin m) : (A i).eval z = (S i).sum (fun j => a i j * q ^ j) := by
    rw [hz]
    exact eval_inv_eq_negativeLaurent (A i) q
  let old (i : Fin m) (g : G) := (norm g.val.det : Complex) ^ s * (Phi i g.val * c g)
  let new (i : Fin m) (g : G) := (S i).sum (fun j => a i j *
    ((norm g.val.det : Complex) ^ s * (Psi i j g.val * c (U i ^ j * g))))
  have hOld : forall i : Fin m, Integrable (old i) mu := (h.2 s hs).1
  have hNew (i : Fin m) : And (Integrable (new i) mu)
      (integral mu (new i) = (A i).eval z * integral mu (old i)) := by
    rw [hEval i]
    exact (hPsi i).2 (S i) (a i) s (hOld i)
  have hEach (i : Fin m) (j : Int) :
      Integrable (fun g : G => (norm g.val.det : Complex) ^ s *
        (Psi i j g.val * c (U i ^ j * g))) mu := by
    have hSingleton := ((hPsi i).2 ({j} : Finset Int) (fun _ => 1) s (hOld i)).1
    simpa only [Finset.sum_singleton, one_mul] using hSingleton
  refine And.intro hEach
    (And.intro (integrable_finsetSum Finset.univ (fun i _ => (hNew i).1)) ?_)
  let fOld (g : G) := Finset.univ.sum (fun i : Fin m => (A i).eval z * old i g)
  have hF : integral mu fOld = Inv.inv (D.eval z) := (h.2 s hs).2.2
  have hTerms (i : Fin m) : Integrable (fun g => (A i).eval z * old i g) mu :=
    (hOld i).const_mul _
  calc
    _ = Finset.univ.sum (fun i : Fin m => integral mu (new i)) :=
      integral_finsetSum Finset.univ (fun i _ => (hNew i).1)
    _ = Finset.univ.sum (fun i : Fin m => integral mu (fun g => (A i).eval z * old i g)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(hNew i).2, integral_const_mul]
    _ = integral mu fOld := (integral_finsetSum Finset.univ (fun i _ => hTerms i)).symm
    _ = _ := hF

/-- A reciprocal polynomial realized with polynomial coefficients is also
realized by a finite sum of translated local zeta integrals with fixed
compact tests and constant coefficients. -/
theorem exists_heckeLocalZeta_fixedReciprocalCombination
    [MeasurableSpace G] [MeasurableMul G]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (u : Units L) (hu : Valued.v u.val = finiteUniformizerValue)
    (D : Polynomial Complex) (c : G -> Complex)
    (hGen : HasHeckeLocalZetaInverseCombination mu
      (fun s : Complex => (norm u.val : Complex) ^ s) D c) :
    exists (m : Nat) (U : Fin m -> G) (Phi : Fin m -> Int -> Test)
        (S : Fin m -> Finset Int) (a : Fin m -> Int -> Complex) (tau : Real),
      And (forall i j, HasCompactSupport (fun X => Phi i j X))
        (forall s : Complex, tau < s.re ->
          let f (g : G) := Finset.univ.sum (fun i : Fin m =>
            (S i).sum (fun j => a i j * ((norm g.val.det : Complex) ^ s *
              (Phi i j g.val * c (U i ^ j * g)))))
          And (Integrable f mu)
            (integral mu f = Inv.inv (D.eval ((norm u.val : Complex) ^ s)))) := by
  choose m U Phi S a tau h using exists_heckeLocalZeta_fixedReciprocalCombination_termwise p n mu u hu D c hGen
  refine Exists.intro m (Exists.intro U (Exists.intro Phi (Exists.intro S (Exists.intro a
    (Exists.intro tau ?_)))))
  exact And.intro h.1 (fun s hs => (h.2 s hs).2)

end

end Robin1984.GRH
