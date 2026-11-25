import Robin1984.GRH.GodementJacquetFiniteAdelicFixedTensors

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement-Jacquet finite adelic zeta integrals and factorization over the places.
- Formalization note: Realizes the finite Euler product with canonical ramified factors by a fixed finite sum of integrals of pure local tensors.
- PROVENANCE-END
-/

/-!
# Fixed tensor integrals for the finite Euler product

At each ramified place choose a finite family of compact tests, translated
coefficients, and constant weights realizing the canonical Euler factor.
The finite products of those choices give fixed global tensor tests.
Their integrals combine to the finite Euler product on a common right
half-plane.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField
open MeasureTheory.Measure
open scoped Classical

namespace Robin1984.GRH

section

variable (K : Type*) [Field K] [NumberField K]
local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K

private abbrev TensorTestMatrix (n : Nat) (p : P) :=
  Matrix (Fin (n + 1)) (Fin (n + 1)) (p.adicCompletion K)

private noncomputable abbrev localValuedIntegralMatrixSubgroup (n : Nat) (p : P) :=
  valuationIntegralMatrixSubgroup
    (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) n

set_option maxHeartbeats 1500000 in
/-- Fixed compact local tests realize the ramified factors in a finite sum
of tensor integrals. On a common right half-plane every tensor integrand
is integrable, and their weighted sum of integrals is the finite Euler
product with the canonical ramified factors. -/
theorem exists_finiteAdeleCanonicalFixedTensorIntegral
    (n : Nat) (E : Finset P) [Countable P] [(Filter.atTop : Filter (Finset P)).IsCountablyGenerated]
    [forall S : Finset P, Fintype (S : Set P)]
    [MeasurableSpace FA] [BorelSpace FA]
    [forall p : P, MeasurableSpace (p.adicCompletion K)]
    [forall p : P, BorelSpace (p.adicCompletion K)]
    [forall p : P, MeasurableSpace (Units (p.adicCompletion K))]
    [forall p : P, BorelSpace (Units (p.adicCompletion K))]
    [forall p : P, SigmaFinite (heckeLocalHaar p)]
    [MeasurableSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) FA))]
    [BorelSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) FA))]
    [forall p : P, MeasurableSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) (p.adicCompletion K)))]
    [forall p : P, BorelSpace (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) (p.adicCompletion K)))]
    [forall p : P, MeasurableMul (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) (p.adicCompletion K)))]
    [forall p : P, MeasurableSpace (localValuedIntegralMatrixSubgroup K (n + 1) p)]
    [forall p : P, BorelSpace (localValuedIntegralMatrixSubgroup K (n + 1) p)]
    [forall S : Finset P, MeasurableSpace ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K (n + 1) p.val)]
    [forall S : Finset P, BorelSpace (FiniteAdeleMatrixHaarChart K (n + 1) S)]
    (mu : Measure (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) FA)))
    (localHaar : forall p : P, Measure (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) (p.adicCompletion K))))
    [forall p, (localHaar p).IsMulLeftInvariant] [forall p, SigmaFinite (localHaar p)]
    (hLocalMass : forall p, localHaar p (finiteLocalMatrixUnitSubgroup K (n + 1) p :
      Set (Units (Matrix (Fin (n + 1)) (Fin (n + 1)) (p.adicCompletion K)))) = 1)
    (tailHaar : forall S : Finset P, Measure ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K (n + 1) p.val))
    [forall S, IsProbabilityMeasure (tailHaar S)]
    (hMeasure : forall S : Finset P, mu.comap (finiteAdeleMatrixHaarChartEmbedding K (n + 1) S) =
      (Measure.pi (fun p : (S : Set P) => localHaar p.val)).prod (tailHaar S))
    (nu : forall p : P, Measure (localValuedIntegralMatrixSubgroup K (n + 1) p))
    [forall p, IsProbabilityMeasure (nu p)]
    (u0 : forall p : P, Units (p.adicCompletion K))
    (hu0 : forall p, Valued.v (u0 p).val = finiteUniformizerValue)
    (chi : forall p : P, Fin (n + 1) -> MonoidHom (Units (p.adicCompletion K)) Complex)
    (hUnit : forall p, Not (Membership.mem E p) -> forall i x,
      Membership.mem (heckeLocalUnitShell p) x -> chi p i x = 1)
    (hSpherical : forall p, Not (Membership.mem E p) -> Filter.Eventually
      (fun g => norm (heckeUnramifiedSphericalCoefficient p (n + 1) (nu p)
        (productDiagonalCharacter (n + 1) (chi p)) g) <= 1) (ae (localHaar p)))
    (hWeighted : forall s : Complex, (((n + 1 : Nat) : Real) + 1) / 2 < s.re ->
      forall p, Not (Membership.mem E p) -> forall i, norm (chi p i (u0 p) *
      (dedekindPrimeNorm K p : Complex) ^ (-s)) < 1)
    (D : P -> Polynomial Complex)
    (c : forall p : P, Units (Matrix (Fin (n + 1)) (Fin (n + 1)) (p.adicCompletion K)) -> Complex)
    (hGen : forall p : P, Membership.mem E p -> HasHeckeLocalZetaInverseCombination
      (localHaar p) (fun s : Complex => (norm (u0 p).val : Complex) ^ s) (D p) (c p)) :
    let R := Subtype (fun p : P => Membership.mem E p)
    let delta : Real := (((n + 1 : Nat) : Real) - 1) / 2
    exists (m : R -> Nat) (U : forall p : R, Fin (m p) -> Units (TensorTestMatrix K n p.val))
      (Phi : forall p : R, Fin (m p) -> LocallyConstant (TensorTestMatrix K n p.val) Complex)
      (w : forall p : R, Fin (m p) -> Complex) (tau : Real),
      And (forall p i, HasCompactSupport (fun X => Phi p i X)) (forall s : Complex, tau < s.re ->
        let Choice := forall p : R, Fin (m p)
        let shifted := s + (delta : Complex)
        let term (p : R) (i : Fin (m p)) (g : Units (TensorTestMatrix K n p.val)) :=
          (norm g.val.det : Complex) ^ shifted * (Phi p i g.val * c p.val (U p i * g))
        let basic (p : P) := heckeUnramifiedLocalZetaIntegrand p (n + 1) (nu p) (chi p) s
        let H (j : Choice) := finiteAdeleMatrixRestrictedZetaIntegrand K (n + 1)
          (fun p g => if hp : Membership.mem E p then
            term (Subtype.mk p hp) (j (Subtype.mk p hp)) g else basic p g)
        let A (p : P) :=
          if Membership.mem E p then
            Inv.inv ((D p).eval ((norm (u0 p).val : Complex) ^ shifted))
          else Finset.univ.prod
            (fun i : Fin (n + 1) => Inv.inv (1 - chi p i (u0 p) * (dedekindPrimeNorm K p : Complex) ^ (-s)))
        And (forall j : Choice, Integrable (H j) mu)
          (HasProd A (Finset.univ.sum (fun j : Choice =>
            (Finset.univ.prod (fun p : R => w p (j p))) * integral mu (H j))))) := by
  intro R delta
  choose m U Phi w T hT using fun p : R =>
    exists_heckeLocalZeta_finiteFixedReciprocalCombination p.val n (localHaar p.val)
      (u0 p.val) (hu0 p.val) (D p.val) (c p.val) (hGen p.val p.property)
  let bnd := Finset.univ.sum (fun p : R => abs (T p))
  let minS : Real := (((n + 1 : Nat) : Real) + 1) / 2
  let tau := max (bnd - delta) minS
  refine Exists.intro m (Exists.intro U (Exists.intro Phi (Exists.intro w
    (Exists.intro tau (And.intro (fun p => (hT p).1) ?_)))))
  intro s hs Choice shifted term basic H A
  have hLarge : minS < s.re := (le_max_right _ _).trans_lt hs
  have hShift (p : R) : T p < shifted.re := by
    have hB : T p <= bnd :=
      (le_abs_self _).trans (Finset.single_le_sum (fun q _ => abs_nonneg (T q)) (Finset.mem_univ p))
    change T p < (s + (delta : Complex)).re
    rw [Complex.add_re, Complex.ofReal_re]
    exact hB.trans_lt (sub_lt_iff_lt_add.mp ((le_max_left _ _).trans_lt hs))
  have hOne (p : P) (hp : Not (Membership.mem E p)) (g : Units (TensorTestMatrix K n p))
      (hg : Membership.mem (finiteLocalMatrixUnitSubgroup K (n + 1) p) g) : basic p g = 1 := by
    apply heckeUnramifiedLocalZetaIntegrand_eq_one_of_mem_integral
      p (n + 1) (nu p) (chi p) (hUnit p hp) s g
    rw [mem_valuationIntegralMatrixSubgroup_iff]
    exact hg
  let pick (j : Choice) (p : P) (g : Units (TensorTestMatrix K n p)) :=
    if hp : Membership.mem E p then term (Subtype.mk p hp) (j (Subtype.mk p hp)) g else basic p g
  let combine (p : P) (g : Units (TensorTestMatrix K n p)) :=
    if hp : Membership.mem E p then
      Finset.univ.sum (fun i : Fin (m (Subtype.mk p hp)) => w (Subtype.mk p hp) i * term (Subtype.mk p hp) i g)
    else basic p g
  let euler (p : P) := Finset.univ.prod
    (fun i : Fin (n + 1) => Inv.inv (1 - chi p i (u0 p) * (dedekindPrimeNorm K p : Complex) ^ (-s)))
  let pickedFactor (j : Choice) (p : P) :=
    if hp : Membership.mem E p then integral (localHaar p)
      (term (Subtype.mk p hp) (j (Subtype.mk p hp))) else euler p
  have hEach (j : Choice) : Integrable (H j) mu := by
    have hZ (p : P) (hp : Not (Membership.mem E p)) : pick j p = basic p := by
      funext g
      simp only [pick, dif_neg hp]
    have hE (p : P) (hp : Not (Membership.mem E p)) : pickedFactor j p = euler p := by
      simp only [pickedFactor, dif_neg hp]
    have hR (p : P) (hp : Membership.mem E p) :
        And (Integrable (pick j p) (localHaar p)) (integral (localHaar p) (pick j p) = pickedFactor j p) := by
      let q : R := Subtype.mk p hp
      have hh := (hT q).2 shifted (hShift q)
      simpa only [pick, pickedFactor, dif_pos hp] using
        And.intro (hh.1 (j q)) (rfl : integral (localHaar p) (term q (j q)) = _)
    exact (integrableAndHasProd_finiteAdeleSphericalZetaIntegralWithRamifiedPlaces K (n + 1) E mu
      localHaar hLocalMass tailHaar hMeasure nu u0 (fun p _ => hu0 p) chi hUnit s hLarge
      hSpherical (hWeighted s hLarge) (pick j) (pickedFactor j) hZ hE hR).1
  have hComZ (p : P) (hp : Not (Membership.mem E p)) : combine p = basic p := by
    funext g
    simp only [combine, dif_neg hp]
  have hA (p : P) (hp : Not (Membership.mem E p)) : A p = euler p := by
    simp only [A, if_neg hp, euler]
  have hComR (p : P) (hp : Membership.mem E p) :
      And (Integrable (combine p) (localHaar p)) (integral (localHaar p) (combine p) = A p) := by
    let q : R := Subtype.mk p hp
    simpa only [combine, A, dif_pos hp, if_pos hp] using (hT q).2 shifted (hShift q) |>.2
  have hProd := (integrableAndHasProd_finiteAdeleSphericalZetaIntegralWithRamifiedPlaces K (n + 1) E mu
    localHaar hLocalMass tailHaar hMeasure nu u0 (fun p _ => hu0 p) chi hUnit s hLarge
    hSpherical (hWeighted s hLarge) combine A hComZ hA hComR).2
  have hExpansion := finiteAdeleMatrixRestrictedZetaIntegrand_fixedTensorExpansion K (n + 1)
    E (fun p => Fin (m p)) w term basic hOne
  have hIntegral := (hExpansion.2 mu hEach).2
  refine And.intro hEach ?_
  rw [<- hIntegral]
  exact hProd

end

end Robin1984.GRH
