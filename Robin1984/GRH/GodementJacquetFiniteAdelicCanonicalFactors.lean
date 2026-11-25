import Robin1984.GRH.GodementJacquetLocalZetaCoefficientOrbit

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and the restricted product factorization of finite adelic zeta integrals.
- Formalization note: Chooses a common half-plane for the finite ramified set and inserts the shifted inverse-denominator witnesses into the spherical restricted product.
- PROVENANCE-END
-/

/-!
# Finite adelic Godement-Jacquet integrals with canonical local factors

At each place in a finite ramified set, use a finite combination of compact
local tests whose zeta integral is the reciprocal of the normalized local
denominator. A common right half-plane permits these tests to be combined
with the spherical reference tests in the restricted product Haar integral.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField

namespace Robin1984.GRH

section

variable {K : Type*} [Field K] [NumberField K] (n : Nat)

local notation "Places" => HeightOneSpectrum (RingOfIntegers K)
private noncomputable abbrev localGroup (p : Places) :=
  Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))

/-- Assemble the local reciprocal-denominator integrands over a finite set of
places. Away from that set the integrand is the prescribed spherical one. -/
theorem exists_heckeLocalZeta_ramifiedGeneratorFamily
    (E : Finset Places) (delta : Real)
    [forall p : Places, MeasurableSpace (localGroup n p)]
    (mu : forall p : Places, Measure (localGroup n p))
    (Z : Places -> Complex -> Complex) (D : Places -> Polynomial Complex)
    (c : forall p : Places, localGroup n p -> Complex)
    (spherical : forall p : Places, Complex -> localGroup n p -> Complex)
    (hE : forall p : Places, Membership.mem E p ->
      HasHeckeLocalZetaInverseCombination (mu p) (Z p) (D p) (c p)) :
    exists (tau : Real) (f : forall p : Places, Complex -> localGroup n p -> Complex),
      And (forall p : Places, Not (Membership.mem E p) -> forall s, f p s = spherical p s)
        (forall s : Complex, tau < s.re -> forall p : Places, Membership.mem E p ->
          And (Integrable (f p s) (mu p))
            (integral (mu p) (f p s) = Inv.inv ((D p).eval (Z p (s + (delta : Complex)))))) := by
  classical
  let P := {p : Places // Membership.mem E p}
  have hLocal (p : P) :
      exists (tau : Real) (f : Complex -> localGroup n p.val -> Complex),
        forall s : Complex, tau < s.re ->
          And (Integrable (f s) (mu p.val))
            (integral (mu p.val) (f s) = Inv.inv ((D p.val).eval (Z p.val s))) := by
    choose m Phi A tau h using hE p.val p.property
    let f (s : Complex) (g : localGroup n p.val) := Finset.univ.sum
      (fun i : Fin m => (A i).eval (Z p.val s) *
        ((norm g.val.det : Complex) ^ s * (Phi i g.val * c p.val g)))
    exact Exists.intro tau (Exists.intro f (fun s hs => (h.2 s hs).2))
  choose tau g h using hLocal
  let t (p : Places) : Real := if hp : Membership.mem E p then tau (Subtype.mk p hp) else 0
  let bound : Real := E.sum (fun p => abs (t p))
  let f (p : Places) (s : Complex) : localGroup n p -> Complex :=
    if hp : Membership.mem E p then g (Subtype.mk p hp) (s + (delta : Complex)) else spherical p s
  refine Exists.intro (bound - delta) (Exists.intro f (And.intro ?_ ?_))
  . intro p hp s
    simp only [f, dif_neg hp]
  . intro s hs p hp
    have hBound : tau (Subtype.mk p hp) <= bound := by
      calc
        _ = t p := (dif_pos hp).symm
        _ <= abs (t p) := le_abs_self _
        _ <= bound := Finset.single_le_sum (fun q _ => abs_nonneg (t q)) hp
    have hShift : tau (Subtype.mk p hp) < (s + (delta : Complex)).re := by
      rw [Complex.add_re, Complex.ofReal_re]
      linarith
    simpa only [f, dif_pos hp] using h (Subtype.mk p hp) (s + (delta : Complex)) hShift

end

section FiniteAdelicCanonicalFactors

open MeasureTheory.Measure

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K

private noncomputable abbrev localValuedIntegralMatrixSubgroup (n : Nat) (p : P) :=
  valuationIntegralMatrixSubgroup
    (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) n

/-- On a common right half-plane the finite adelic Haar integral is the
Euler product with the prescribed spherical factors and the reciprocal
canonical ramified denominators in the standard shifted normalization. -/
theorem integrableAndHasProd_finiteAdeleSphericalZetaIntegralWithCanonicalFactors
    (n : Nat) (E : Finset P) [Countable P] [(Filter.atTop : Filter (Finset P)).IsCountablyGenerated]
    [forall S : Finset P, Fintype (S : Set P)]
    [MeasurableSpace FA] [BorelSpace FA]
    [forall p : P, MeasurableSpace (p.adicCompletion K)]
    [forall p : P, BorelSpace (p.adicCompletion K)]
    [forall p : P, MeasurableSpace (Units (p.adicCompletion K))]
    [forall p : P, BorelSpace (Units (p.adicCompletion K))]
    [forall p : P, SigmaFinite (heckeLocalHaar p)]
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [forall p : P, MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [forall p : P, BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [forall p : P, MeasurableSpace (localValuedIntegralMatrixSubgroup K n p)]
    [forall p : P, BorelSpace (localValuedIntegralMatrixSubgroup K n p)]
    [forall S : Finset P, MeasurableSpace ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val)]
    [forall S : Finset P, BorelSpace (FiniteAdeleMatrixHaarChart K n S)]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) FA)))
    (localHaar : forall p : P, Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    [forall p, (localHaar p).IsMulLeftInvariant] [forall p, SigmaFinite (localHaar p)]
    (hLocalMass : forall p, localHaar p (finiteLocalMatrixUnitSubgroup K n p :
      Set (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))) = 1)
    (tailHaar : forall S : Finset P, Measure ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val))
    [forall S, IsProbabilityMeasure (tailHaar S)]
    (hMeasure : forall S : Finset P, mu.comap (finiteAdeleMatrixHaarChartEmbedding K n S) =
      (Measure.pi (fun p : (S : Set P) => localHaar p.val)).prod (tailHaar S))
    (nu : forall p : P, Measure (localValuedIntegralMatrixSubgroup K n p))
    [forall p, IsProbabilityMeasure (nu p)]
    (u0 : forall p : P, Units (p.adicCompletion K))
    (hu0 : forall p, Not (Membership.mem E p) -> Valued.v (u0 p).val = finiteUniformizerValue)
    (chi : forall p : P, Fin n -> MonoidHom (Units (p.adicCompletion K)) Complex)
    (hUnit : forall p, Not (Membership.mem E p) -> forall i x,
      Membership.mem (heckeLocalUnitShell p) x -> chi p i x = 1)
    (hSpherical : forall p, Not (Membership.mem E p) -> Filter.Eventually
      (fun g => norm (heckeUnramifiedSphericalCoefficient p n (nu p)
        (productDiagonalCharacter n (chi p)) g) <= 1) (ae (localHaar p)))
    (hWeighted : forall s : Complex, ((n : Real) + 1) / 2 < s.re ->
      forall p, Not (Membership.mem E p) -> forall i, norm (chi p i (u0 p) *
      (dedekindPrimeNorm K p : Complex) ^ (-s)) < 1)
    (D : P -> Polynomial Complex)
    (c : forall p : P, Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)) -> Complex)
    (hGen : forall p : P, Membership.mem E p -> HasHeckeLocalZetaInverseCombination
      (localHaar p) (fun s : Complex => (norm (u0 p).val : Complex) ^ s) (D p) (c p)) :
    let delta : Real := ((n : Real) - 1) / 2
    let Z (p : P) (s : Complex) := (norm (u0 p).val : Complex) ^ s
    exists (tau : Real) (f : forall p : P, Complex ->
        Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)) -> Complex),
      forall s : Complex, tau < s.re ->
        let a (p : P) := @ite Complex (Membership.mem E p) (Classical.propDecidable _)
          (Inv.inv ((D p).eval (Z p (s + (delta : Complex)))))
          (Finset.univ.prod
            (fun i : Fin n => Inv.inv (1 - chi p i (u0 p) * (dedekindPrimeNorm K p : Complex) ^ (-s))))
        let F := finiteAdeleMatrixRestrictedZetaIntegrand K n (fun p => f p s)
        And (Integrable F mu) (HasProd a (integral mu F)) := by
  intro delta Z
  classical
  let spherical (p : P) (s : Complex) :=
    heckeUnramifiedLocalZetaIntegrand p n (nu p) (chi p) s
  choose tau f h using exists_heckeLocalZeta_ramifiedGeneratorFamily (K := K)
    n E delta localHaar Z D c spherical hGen
  refine Exists.intro (max tau (((n : Real) + 1) / 2)) (Exists.intro f ?_)
  intro s hs a F
  have hLocal : tau < s.re := (le_max_left _ _).trans_lt hs
  have hLarge : ((n : Real) + 1) / 2 < s.re := (le_max_right _ _).trans_lt hs
  have hEuler (p : P) (hp : Not (Membership.mem E p)) :
      a p = Finset.univ.prod
        (fun i : Fin n => Inv.inv (1 - chi p i (u0 p) * (dedekindPrimeNorm K p : Complex) ^ (-s))) := by
    simp only [a, if_neg hp]
  have hRamified (p : P) (hp : Membership.mem E p) :
      And (Integrable (f p s) (localHaar p)) (integral (localHaar p) (f p s) = a p) := by
    simpa only [a, if_pos hp] using h.2 s hLocal p hp
  exact integrableAndHasProd_finiteAdeleSphericalZetaIntegralWithRamifiedPlaces K n E mu
    localHaar hLocalMass tailHaar hMeasure nu u0 hu0 chi hUnit s hLarge
    hSpherical (hWeighted s hLarge) (fun p => f p s) a
    (fun p hp => h.1 p hp s) hEuler hRamified

end FiniteAdelicCanonicalFactors

end Robin1984.GRH
