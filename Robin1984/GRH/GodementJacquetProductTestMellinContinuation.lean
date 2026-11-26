import Robin1984.GRH.GodementJacquetDeterminantWeightedTests
import Robin1984.GRH.GodementJacquetEulerMellinContinuation
import Robin1984.GRH.GodementJacquetFullThetaGrowth

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Absolute convergence of Godement-Jacquet theta series for adelic Schwartz functions and global zeta unfolding.
- Formalization note: Obtains the product-test measurability, pointwise summability and weighted integrability hypotheses from the finite rectangle decomposition and the local absolute integrals.
- PROVENANCE-END
-/

/-!
# Mellin continuation for adelic product tests

The full rational matrix theta series is absolutely summable at every
pair of determinant-norm-one group elements. Finite denominators give
this assertion for a Schwartz rectangle. A finite rectangle expansion
then proves it for the product of an archimedean Schwartz function and
a compactly supported locally constant function on finite adeles.
The same test then gives the entire Euler product continuation whenever
the local integrals and entire theta Mellin transforms are supplied.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "Ix" => Prod (Fin n) (Fin n)
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K
local notation "M" => Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K)
local notation "N" => MonoidHom.ker (adelicDeterminantLogNorm K n)
local notation "Arch" => PiLp 2 (fun _ : Ix => DedekindZeta.Theta.minkowskiSpace K)

set_option maxHeartbeats 650000 in
/-- Finite denominator bounds imply pointwise absolute convergence for the
full rational theta series of a matrix rectangle. -/
theorem summable_godementJacquetDoubleThetaTerm_rectangle
    (a : Ix -> FA) (d : RingOfIntegers K) (f : SchwartzMap Arch Complex)
    (t : Real) (A B : N) :
    Summable (godementJacquetDoubleThetaTerm K n
      (godementJacquetMatrixRectangle K a d f) t A B) := by
  let m := Module.finrank Real Arch + 1
  have hm : Module.finrank Real Arch < m := Nat.lt_succ_self _
  choose C hC dX hBound using
    tsum_ofReal_norm_godementJacquetFullTheta_le_of_finiteDenominators K n a d f m hm
  choose dA hdA using exists_godementJacquetMatrix_finiteDenominator K n A.val.val
  choose dB hdB using exists_godementJacquetMatrix_finiteDenominator K n B.val.inv
  let U := godementJacquetDoubleThetaTerm K n
    (godementJacquetMatrixRectangle K a d f) t A B
  have hAbs : tsum (fun P => ENNReal.ofReal (norm (U P))) < Top.top := by
    refine lt_of_le_of_lt (hBound t A B (Subtype.mk dA hdA.1) (Subtype.mk dB hdB.1)
      hdA.2 hdB.2) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC
  have hNorm : Summable (fun P => norm (U P)) := by
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using
      ENNReal.summable_toReal hAbs.ne
  exact hNorm.of_norm

/-- A compact finite-adelic factor and an archimedean Schwartz factor give a
continuous adelic matrix test whose rational theta terms are summable. -/
theorem continuous_and_summable_godementJacquetDoubleThetaTerm_product
    (f : SchwartzMap Arch Complex) (Phi : LocallyConstant (Ix -> FA) Complex)
    (hPhi : HasCompactSupport (fun x => Phi x)) :
    let phi (X : M) :=
      f (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (X.vec i).1))) *
          Phi (fun i : Ix => (X.vec i).2)
    And (Continuous phi) (forall (t : Real) (A B : N),
      Summable (godementJacquetDoubleThetaTerm K n phi t A B)) := by
  intro phi
  choose d S a b h using exists_godementJacquetProductTest_eq_sum_rectangles K n f Phi hPhi
  let rect (i : Set (Ix -> FA)) :=
    godementJacquetMatrixRectangle K (a i) d (HSMul.hSMul (b i) f)
  have hEq : phi = (fun X => S.sum (fun i => rect i X)) := funext h.2
  rw [hEq]
  refine And.intro (continuous_finsetSum S (fun i _ =>
    continuous_godementJacquetMatrixRectangle K (a i) d h.1 (HSMul.hSMul (b i) f))) ?_
  intro t A B
  let term (i : Set (Ix -> FA)) (P : Matrix (Fin n) (Fin n) K) :=
    godementJacquetDoubleThetaTerm K n (rect i) t A B P
  change Summable (fun P => S.sum (fun i => term i P))
  clear hEq h
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact summable_zero
  | @insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    exact (summable_godementJacquetDoubleThetaTerm_rectangle K n (a i) d
      (HSMul.hSMul (b i) f) t A B).add ih

section Continuation

local notation "A" => Units (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))
local notation "F" => Units (Matrix (Fin n) (Fin n) FA)
local notation "G" => AdelicGeneralLinearGroup K n
local notation "Gamma" => MonoidHom.range (adelicPrincipalDeterminantOne K n)
local notation "FiniteAdeles" => FiniteAdeleRing (RingOfIntegers K) K
local notation "AMatrix" => Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K)

set_option maxHeartbeats 900000 in
/-- For compact finite-adelic factors, the unfolding hypotheses for the product
test follow from the local determinant-weighted integrals. Entire theta
Mellins then continue the completed Euler product. -/
theorem exists_entire_completedEulerProduct_of_productTestThetaMellin
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
    (hCompact : forall j, HasCompactSupport (fun x => Phi j x))
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
    (forall s : Complex, tau < s.re -> Integrable (fun g : A => f (arch g.val) *
      (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
        (s + ((n : Complex) - 1) / 2)) muA) ->
    (forall s : Complex, tau < s.re -> forall j, Integrable (fun g : F => Phi j g.val.vec *
      (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
        (s + ((n : Complex) - 1) / 2)) muF) ->
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
  intro arch phi zetaA zetaM hRawArch hRawFinite hH hArch hFinite hProd hEntire
  have hTest (j : J) :=
    continuous_and_summable_godementJacquetDoubleThetaTerm_product K n f (Phi j) (hCompact j)
  have hMeas (j : J) : Measurable (phi j) := (hTest j).1.measurable
  have hSum (j : J) (t : Real) (a b : N) :
      Summable (fun P : Matrix.GeneralLinearGroup (Fin n) K =>
        godementJacquetDoubleThetaTerm K n (phi j) t a b P.val) :=
    ((hTest j).2 t a b).comp_injective Units.val_injective
  have hWeighted (s : Complex) (hs : tau < s.re) (j : J) :
      Integrable (fun g : AdelicGeneralLinearGroup K n => phi j g.val *
        (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2))
        (adelicDeterminantProductMeasure K n hn mu) :=
    integrable_adelicDeterminantWeightedMatrixTest_of_parts K n hn mu muA muF
      f (Phi j) (s + ((n : Complex) - 1) / 2) (hRawArch s hs) (hRawFinite s hs j)
  exact exists_entire_completedEulerProduct_of_weightedThetaMellin K n hn mu muA muF
    f Phi archCoefficient finiteCoefficient D hD hMul hUnique v c hV hc hPrincipal
    hCentral hcI hVI hSplit w tau H localFactor archFactor hMeas hSum hWeighted
    hH hArch hFinite hProd hEntire

end Continuation

end Robin1984.GRH
