import Robin1984.GRH.GodementJacquetAdelicProductMeasure
import Robin1984.GRH.GodementJacquetAdelicProductTest

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Godement-Jacquet global zeta integral and its tensor factorization over the places.
- Formalization note: Assembles the archimedean test and the fixed finite adelic zeta tensors into the weighted global zeta integral.
- PROVENANCE-END
-/

/-!
# Fixed tensor sums in the global zeta integral

The determinant-coordinate Haar measure is a positive multiple of the
product Haar measure. This factors a tensor zeta integral, including its
determinant weight. Applied to a finite weighted family of adelic tests,
the calculation transfers the finite-place Euler product to the global
zeta integral with one common archimedean factor.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField

namespace Robin1984.GRH

section

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

private abbrev ZetaArchGroup :=
  Units (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))

private abbrev ZetaFiniteGroup :=
  Units (Matrix (Fin n) (Fin n) (FiniteAdeleRing (RingOfIntegers K) K))

local notation "G" => AdelicGeneralLinearGroup K n
local notation "A" => ZetaArchGroup K n
local notation "F" => ZetaFiniteGroup K n

/-- The determinant-weighted integral of a tensor factors into its two
component integrals up to one positive Haar constant independent of the
exponent. Integrability of the two component integrands suffices. -/
theorem exists_adelicDeterminantProductMeasure_tensorIntegral
    [MeasurableSpace G] [BorelSpace G] [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace F] [BorelSpace F]
    [BorelSpace (Prod A F)]
    [MeasurableSpace (adelicDeterminantLogNorm K n).ker]
    [BorelSpace (adelicDeterminantLogNorm K n).ker]
    (hn : 0 < n) (mu : Measure (adelicDeterminantLogNorm K n).ker) [SFinite mu] [mu.IsHaarMeasure]
    (muA : Measure A) (muF : Measure F) [SFinite muA] [SFinite muF]
    [muA.IsHaarMeasure] [muF.IsHaarMeasure] :
    let e := adelicGeneralLinearGroup_prod K n
    let nu := adelicDeterminantProductMeasure K n hn mu
    exists r : NNReal, And (0 < r)
      (forall (z : Complex) (f : G -> Complex) (a : A -> Complex) (b : F -> Complex),
        (forall g : G, f g = a (e g).1 * b (e g).2) ->
        let wA (x : A) := a x * (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det x) : Complex) ^ z
        let wF (x : F) := b x * (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det x) : Complex) ^ z
        let w (g : G) := f g * (adelicDeterminantNorm K n g : Complex) ^ z
        Integrable wA muA -> Integrable wF muF ->
        And (Integrable w nu) (integral nu w = HSMul.hSMul r
          (integral muA wA * integral muF wF))) := by
  intro e nu
  choose r hr using adelicDeterminantProductMeasure_eq_smul_matrixProductHaar K n hn mu muA muF
  refine Exists.intro r (And.intro hr.1 ?_)
  intro z f a b hSplit wA wF w hA hF
  have hEq : w = (fun g : G => wA (e g).1 * wF (e g).2) := by
    funext g
    change f g * (adelicDeterminantNorm K n g : Complex) ^ z = _
    rw [hSplit g, adelicDeterminantNorm_cpow_prod K n g z]
    change (a (e g).1 * b (e g).2) * _ =
      (a (e g).1 * _) * (b (e g).2 * _)
    ac_rfl
  have hProduct := integrableAndIntegral_adelicMatrixProductHaar K n muA muF wA wF hA hF
  change And (Integrable w (adelicDeterminantProductMeasure K n hn mu))
    (integral (adelicDeterminantProductMeasure K n hn mu) w = _)
  rw [hr.2, hEq]
  refine And.intro hProduct.1.smul_measure_nnreal ?_
  rw [integral_smul_nnreal_measure, hProduct.2]

local notation "Ix" => Prod (Fin n) (Fin n)
local notation "FiniteAdeles" => FiniteAdeleRing (RingOfIntegers K) K
local notation "AMatrix" => Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K)
local notation "Arch" => PiLp 2 (fun _ : Ix => DedekindZeta.Theta.minkowskiSpace K)

open scoped Classical RealInnerProductSpace FourierTransform

/-- A fixed weighted sum of global zeta integrals with factored matrix
coefficients equals the common archimedean zeta integral times the finite
Euler product and one positive Haar constant. The archimedean and finite
integrability hypotheses hold on the specified right half-plane. -/
theorem exists_adelicDeterminantProductMeasure_fixedZetaProduct
    [MeasurableSpace G] [BorelSpace G] [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace F] [BorelSpace F]
    [BorelSpace (Prod A F)]
    [MeasurableSpace (adelicDeterminantLogNorm K n).ker]
    [BorelSpace (adelicDeterminantLogNorm K n).ker]
    (hn : 0 < n) (mu : Measure (adelicDeterminantLogNorm K n).ker) [SFinite mu] [mu.IsHaarMeasure]
    (muA : Measure A) (muF : Measure F) [SFinite muA] [SFinite muF]
    [muA.IsHaarMeasure] [muF.IsHaarMeasure]
    {J : Type*} [Fintype J] {P : Type*}
    (f : SchwartzMap Arch Complex) (Phi : J -> LocallyConstant (Ix -> FiniteAdeles) Complex)
    (archCoefficient : A -> Complex) (finiteCoefficient : J -> F -> Complex)
    (coefficient : J -> G -> Complex)
    (hSplit : forall j g, coefficient j g =
      archCoefficient ((adelicGeneralLinearGroup_prod K n g).1) *
        finiteCoefficient j ((adelicGeneralLinearGroup_prod K n g).2))
    (w : J -> Complex) (tau : Real) (H : Complex -> J -> F -> Complex)
    (localFactor : Complex -> P -> Complex) :
    let arch (X : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) : Arch :=
      WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (X.vec i)))
    let phi (j : J) (X : AMatrix) :=
      f (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (X.vec i).1))) *
          Phi j (fun i : Ix => (X.vec i).2)
    let zetaA (s : Complex) (g : A) :=
      (f (arch g.val) * archCoefficient g) *
        (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
          (s + ((n : Complex) - 1) / 2)
    let zeta (s : Complex) (j : J) (g : G) :=
      (phi j g.val * coefficient j g) *
        (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)
    let nu := adelicDeterminantProductMeasure K n hn mu
    (forall s j g, H s j g = (Phi j g.val.vec * finiteCoefficient j g) *
        (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
          (s + ((n : Complex) - 1) / 2)) ->
    (forall s : Complex, tau < s.re -> Integrable (zetaA s) muA) ->
    (forall s : Complex, tau < s.re -> forall j, Integrable (H s j) muF) ->
    (forall s : Complex, tau < s.re ->
      HasProd (localFactor s) (Finset.univ.sum (fun j => w j * integral muF (H s j)))) ->
    exists r : NNReal, And (0 < r) (forall s : Complex, tau < s.re ->
      And (forall j, Integrable (zeta s j) nu)
        (Finset.univ.sum (fun j => w j * integral nu (zeta s j)) =
          HSMul.hSMul r (integral muA (zetaA s) * tprod (localFactor s)))) := by
  classical
  intro arch phi zetaA zeta nu hH hArch hFinite hProd
  choose r hr using exists_adelicDeterminantProductMeasure_tensorIntegral K n hn mu muA muF
  refine Exists.intro r (And.intro hr.1 ?_)
  intro s hs
  let a (g : A) := f (arch g.val) * archCoefficient g
  let b (j : J) (g : F) := Phi j g.val.vec * finiteCoefficient j g
  let z := s + ((n : Complex) - 1) / 2
  have hSplitTest (j : J) (g : G) :
      phi j g.val * coefficient j g =
        a (adelicGeneralLinearGroup_prod K n g).1 * b j (adelicGeneralLinearGroup_prod K n g).2 := by
    have hArchVec (i : Ix) : ((adelicGeneralLinearGroup_prod K n g).1.val.vec i) =
        (g.val.vec i).1 :=
      (adelicGeneralLinearGroup_prod_val K n g i.2 i.1).1
    have hFiniteVec : ((adelicGeneralLinearGroup_prod K n g).2.val.vec) =
        (fun i : Ix => (g.val.vec i).2) :=
      funext (fun i => (adelicGeneralLinearGroup_prod_val K n g i.2 i.1).2)
    have ha : arch (adelicGeneralLinearGroup_prod K n g).1.val =
        WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
          (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i).1)) := by
      change WithLp.toLp 2 _ = WithLp.toLp 2 _
      exact congrArg (WithLp.toLp 2) (funext (fun i =>
        congrArg (fun x => DedekindZeta.Theta.toMinkowski K
          (InfiniteAdeleRing.ringEquiv_mixedSpace K x)) (hArchVec i)))
    unfold phi a b
    rw [hSplit j g, ha, hFiniteVec]
    ac_rfl
  have hTerm (j : J) := hr.2 z (fun g => phi j g.val * coefficient j g) a (b j)
    (hSplitTest j) (hArch s hs) (by
      have hEq : (fun g : F => b j g *
          (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^ z) = H s j :=
        funext (fun g => (hH s j g).symm)
      rw [hEq]
      exact hFinite s hs j)
  have hEq (j : J) : (fun g : F => b j g *
      (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^ z) = H s j :=
    funext (fun g => (hH s j g).symm)
  refine And.intro (fun j => (hTerm j).1) ?_
  have hInt (j : J) : integral nu (zeta s j) =
      HSMul.hSMul r (integral muA (zetaA s) * integral muF (H s j)) := by
    have he := (hTerm j).2
    change integral nu (zeta s j) =
      HSMul.hSMul r (integral muA (zetaA s) *
        integral muF (fun g : F => b j g *
          (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^ z)) at he
    rwa [hEq j] at he
  rw [(hProd s hs).tprod_eq, Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hInt]
  change w j * (HSMul.hSMul (r : Real) (integral muA (zetaA s) * integral muF (H s j))) =
    HSMul.hSMul (r : Real) (integral muA (zetaA s) * (w j * integral muF (H s j)))
  rw [Complex.real_smul, Complex.real_smul]
  ac_rfl

end

end Robin1984.GRH
