import Robin1984.GRH.GodementJacquetGlobalZetaProduct
import Robin1984.GRH.GodementJacquetMellinFromSquareIntegrability

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The Godement-Jacquet global zeta unfolding and Euler product realization by test vectors.
- Formalization note: Constructs an entire continuation of a half-plane Euler product by the fixed weighted sum of theta Mellin transforms.
- PROVENANCE-END
-/

/-!
# Entire continuation from the weighted Godement-Jacquet Mellin transforms

On the initial half-plane the fixed weighted sum of zeta integrals is a
common archimedean factor times the finite Euler product. Square
integrability connects these integrals to their theta Mellin transforms.
If those transforms are entire, their weighted sum, divided by the
positive Haar constant, continues the completed Euler product.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical RealInnerProductSpace FourierTransform

namespace Robin1984.GRH

section

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "G" => AdelicGeneralLinearGroup K n
local notation "A" => Units (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K
local notation "F" => Units (Matrix (Fin n) (Fin n) FA)
local notation "N" => MonoidHom.ker (adelicDeterminantLogNorm K n)
local notation "Gamma" => MonoidHom.range (adelicPrincipalDeterminantOne K n)
local notation "Ix" => Prod (Fin n) (Fin n)
local notation "FiniteAdeles" => FiniteAdeleRing (RingOfIntegers K) K
local notation "AMatrix" => Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K)
local notation "Arch" => PiLp 2 (fun _ : Ix => DedekindZeta.Theta.minkowskiSpace K)

set_option maxHeartbeats 900000 in
/-- A fixed weighted theta Mellin family gives an entire continuation of
the completed Euler product when the Mellins are entire and the indicated
archimedean and finite zeta integrals realize the local factors. -/
theorem exists_entire_completedEulerProduct_of_weightedThetaMellin
    [MeasurableSpace G] [BorelSpace G] [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace F] [BorelSpace F]
    [BorelSpace (Prod A F)]
    [MeasurableSpace (adelicDeterminantLogNorm K n).ker]
    [BorelSpace (adelicDeterminantLogNorm K n).ker]
    (hn : 0 < n) (mu : Measure N) [SFinite mu] [mu.IsHaarMeasure] [mu.IsMulRightInvariant]
    [MeasurableMul N] [MeasurableSpace AMatrix] [BorelSpace AMatrix]
    (muA : Measure A) (muF : Measure F) [SFinite muA] [SFinite muF]
    [muA.IsHaarMeasure] [muF.IsHaarMeasure]
    {J : Type*} [Fintype J] {P : Type*}
    (f : SchwartzMap Arch Complex) (Phi : J -> LocallyConstant (Ix -> FiniteAdeles) Complex)
    (archCoefficient : A -> Complex) (finiteCoefficient : J -> F -> Complex)
    (D : Set N) (hD : MeasurableSet D)
    (hMul : Measurable (fun p : Prod G G => p.1 * p.2))
    (hUnique : forall x : N, ExistsUnique (fun gamma : Gamma => Membership.mem D (gamma.val * x)))
    (v : J -> G -> Complex) (c : N -> Complex)
    (hV : forall j, Measurable (v j)) (hc : Measurable c)
    (hPrincipal : forall j (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      v j (adelicPrincipalGeneralLinear K n a * g) = v j g)
    (hCentral : forall j (t : Real) (a : N),
      v j (adelicDeterminantSection K n (Multiplicative.ofAdd t) * a.val) = v j a.val)
    (hcI : lintegral (mu.restrict D) (fun a => ENNReal.ofReal (norm (c a) ^ 2)) < Top.top)
    (hVI : forall j, lintegral (mu.restrict D)
      (fun a => ENNReal.ofReal (norm (v j a.val) ^ 2)) < Top.top)
    (hSplit : forall j g, integral (mu.restrict D) (fun h => v j (h.val * g) * c h) =
      archCoefficient ((adelicGeneralLinearGroup_prod K n g).1) *
        finiteCoefficient j ((adelicGeneralLinearGroup_prod K n g).2))
    (w : J -> Complex) (tau : Real) (H : Complex -> J -> F -> Complex)
    (localFactor : Complex -> P -> Complex) (archFactor : Complex -> Complex) :
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
    let zetaM (j : J) (s : Complex) :=
      godementJacquetLogMellin n (fun t =>
        godementJacquetInvertibleDoubleThetaIntegral K n (mu.restrict D) (phi j) c
          (fun a => v j a.val) t) s
    (forall j, Measurable (phi j)) ->
    (forall j (t : Real) (a b : N),
      Summable (fun P : Matrix.GeneralLinearGroup (Fin n) K =>
        godementJacquetDoubleThetaTerm K n (phi j) t a b P.val)) ->
    (forall s : Complex, tau < s.re -> forall j, Integrable (fun g : G => phi j g.val *
      (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2))
      (adelicDeterminantProductMeasure K n hn mu)) ->
    (forall s j g, H s j g = (Phi j g.val.vec * finiteCoefficient j g) *
        (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
          (s + ((n : Complex) - 1) / 2)) ->
    (forall s : Complex, tau < s.re ->
      And (Integrable (zetaA s) muA) (integral muA (zetaA s) = archFactor s)) ->
    (forall s : Complex, tau < s.re -> forall j, Integrable (H s j) muF) ->
    (forall s : Complex, tau < s.re ->
      HasProd (localFactor s) (Finset.univ.sum (fun j => w j * integral muF (H s j)))) ->
    (forall j, Differentiable Complex (zetaM j)) ->
    exists completed : Complex -> Complex, And (Differentiable Complex completed)
      (forall s : Complex, tau < s.re -> completed s = archFactor s * tprod (localFactor s)) := by
  classical
  intro arch phi zetaA zetaM hPhi hSum hW hH hArch hFinite hProd hEntire
  let coeff (j : J) (g : G) := integral (mu.restrict D) (fun h => v j (h.val * g) * c h)
  let nu := adelicDeterminantProductMeasure K n hn mu
  let zeta (s : Complex) (j : J) (g : G) :=
    (phi j g.val * coeff j g) *
      (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)
  choose r hr using exists_adelicDeterminantProductMeasure_fixedZetaProduct K n hn mu muA muF
    f Phi archCoefficient finiteCoefficient coeff hSplit w tau H localFactor hH
      (fun s hs => (hArch s hs).1) hFinite hProd
  let R := ((r : Real) : Complex)
  have hR : Not (R = 0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (show 0 < (r : Real) from hr.1))
  let total (s : Complex) := Finset.univ.sum (fun j => w j * zetaM j s)
  have hAll (S : Finset J) : Differentiable Complex (fun s => S.sum (fun j => w j * zetaM j s)) := by
    induction S using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (differentiable_const (0 : Complex) : Differentiable Complex (fun _ : Complex => (0 : Complex)))
    | @insert j S hj ih =>
      simp only [Finset.sum_insert hj]
      exact ((differentiable_const (w j)).mul (hEntire j)).add ih
  refine Exists.intro (fun s => Inv.inv R * total s)
    (And.intro ((differentiable_const (Inv.inv R)).mul (hAll Finset.univ)) ?_)
  intro s hs
  have hI (j : J) : integral nu (zeta s j) = zetaM j s :=
    integral_adelicGodementJacquetMatrixCoeff_eq_logMellin_of_squareIntegrable
      K n hn mu D hD hMul hUnique (phi j) (v j) c s (hPhi j) (hV j) hc (hSum j)
        (hPrincipal j) (hCentral j) (hW s hs j) hcI (hVI j)
  have he := (hr.2 s hs).2
  change Finset.univ.sum (fun j => w j * integral nu (zeta s j)) =
    HSMul.hSMul r (integral muA (zetaA s) * tprod (localFactor s)) at he
  simp_rw [hI] at he
  rw [(hArch s hs).2] at he
  change total s = HSMul.hSMul (r : Real) (archFactor s * tprod (localFactor s)) at he
  rw [Complex.real_smul] at he
  calc
    _ = Inv.inv R * (R * (archFactor s * tprod (localFactor s))) :=
      congrArg (fun x : Complex => Inv.inv R * x) he
    _ = _ := by rw [<- mul_assoc, show Inv.inv R * R = 1 by field_simp [hR], one_mul]

end

end Robin1984.GRH
