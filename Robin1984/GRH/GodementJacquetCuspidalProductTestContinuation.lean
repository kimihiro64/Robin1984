import Robin1984.GRH.GodementJacquetProductTestMellinContinuation
import Robin1984.GRH.GodementJacquetReductionWeights

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and theta cancellation for Schwartz-Bruhat test functions.
- Formalization note: Proves the entire theta Mellin continuation and reflection for the product test on a fixed fundamental domain, and applies it to the Euler product identity.
- PROVENANCE-END
-/

/-!
# Entire continuation for cuspidal product tests

Compact finite projections and weighted cusp bounds on a reduction set
give the theta integrability needed for a finite rectangle decomposition
of a product test. The Mellin continuation and reflection use a chosen
fundamental domain inside the same reduction set. The Euler product
identity uses that domain for the matrix coefficient as well.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical RealInnerProductSpace FourierTransform

namespace Robin1984.GRH

section

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "Ix" => Prod (Fin (n + 1)) (Fin (n + 1))
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K
local notation "AM" => Matrix (Fin (n + 1)) (Fin (n + 1)) (AdeleRing (RingOfIntegers K) K)
local notation "N" => MonoidHom.ker (adelicDeterminantLogNorm K (n + 1))
local notation "Denom" => Subtype (fun d : RingOfIntegers K => Not (d = 0))
local notation "Arch" => PiLp 2 (fun _ : Ix => DedekindZeta.Theta.minkowskiSpace K)

set_option maxHeartbeats 1000000 in
/-- Compact finite matrix projections give common finite denominator bounds
on a reduction set. Weighted cusp bounds on that set imply the entire
Mellin continuation and reflection for the actual product test on its
chosen fundamental domain. -/
theorem godementJacquetInvertibleThetaMellin_entire_and_reflection_productTest_of_reductionSet
    [T2Space (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace (AdelicGeneralLinearGroup K (n + 1))]
    [BorelSpace (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableMul (AdelicGeneralLinearGroup K (n + 1))]
    [MeasurableSpace N]
    [BorelSpace N]
    [MeasurableMul N]
    [MeasurableInv N]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace FA] [BorelSpace FA]
    [MeasurableSpace AM]
    [BorelSpace AM]
    (mu : Measure N) [mu.IsHaarMeasure]
    [SFinite mu] [mu.IsMulRightInvariant]
    (D : Set N) (hD : MeasurableSet D)
    (hUnique : forall A : N, ExistsUnique
      (fun gamma : (adelicPrincipalDeterminantOne K (n + 1)).range => Membership.mem D (gamma.val * A)))
    (hMul : Measurable (fun p : Prod N
      N => p.1 * p.2))
    (S : Set N) (hS : MeasurableSet S) (hDS : Set.Subset D S) (hFin : mu S < Top.top)
    (U : Set FA) (hU : IsCompact U)
    (hLeft : forall A : N, Membership.mem S A -> forall i j, Membership.mem U (A.val.val i j).2)
    (hRight : forall B : N, Membership.mem S B -> forall i j, Membership.mem U (B.val.inv i j).2)
    (f : SchwartzMap Arch Complex) (PhiF : LocallyConstant (Ix -> FA) Complex)
    (hCompact : HasCompactSupport (fun x => PhiF x))
    (c b : N -> Complex) (hc : Measurable c) (hb : Measurable b)
    (hInvariantC : forall gamma : (adelicPrincipalDeterminantOne K (n + 1)).range, forall A,
      c (gamma.val * A) = c A)
    (hInvariantB : forall gamma : (adelicPrincipalDeterminantOne K (n + 1)).range, forall B,
      b (gamma.val * B) = b B)
    (hPeriodsC : HasGodementJacquetVanishingUnipotentPeriods c)
    (hPeriodsB : HasGodementJacquetVanishingUnipotentPeriods b)
    (hMeanC : integral (mu.restrict D) c = 0) (hMeanB : integral (mu.restrict D) b = 0)
    (hcI : lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (c x) ^ 2)) < (Top.top : ENNReal))
    (hbI : lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (b x) ^ 2)) < (Top.top : ENNReal))
    (m : Nat) (hm : Module.finrank Real Arch < m)
    (hBound : forall e : Denom,
      let s := godementJacquetFullTheta_principalScalarMatrixUnit K (n + 1) e.val e.property
      let H := godementJacquetFullTheta_archimedeanHeight K (n + 1)
      exists C : Real, forall A : N, Membership.mem S A ->
        And (norm (c A) * H (s * A.val) 1 ^ m <= C)
          (And (norm (c A) * H 1 (Inv.inv A.val * s) ^ m <= C)
            (And (norm (b A) * H (s * A.val) 1 ^ m <= C)
              (norm (b A) * H 1 (Inv.inv A.val * s) ^ m <= C)))) :
    let phi (X : AM) :=
      f (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (X.vec i).1))) *
          PhiF (fun i : Ix => (X.vec i).2)
    let psi := godementJacquetSelfDualMatrixFourier K phi
    let F t := godementJacquetInvertibleDoubleThetaIntegral K (n + 1) (mu.restrict D) phi c b t
    let G t := godementJacquetInvertibleDoubleThetaIntegral K (n + 1) (mu.restrict D) psi b c t
    And (Differentiable Complex (godementJacquetLogMellin (n + 1) F))
      (forall z : Complex, godementJacquetLogMellin (n + 1) F z =
        godementJacquetLogMellin (n + 1) G (1 - z)) := by
  intro phi
  choose d T a w hTest using
    exists_godementJacquetProductTest_eq_sum_rectangles K (n + 1) f PhiF hCompact
  have hEq : phi = (fun X => T.sum (fun i =>
      godementJacquetMatrixRectangle K (a i) d (HSMul.hSMul (w i) f) X)) :=
    funext hTest.2
  rw [hEq]
  choose e L R hDen using
    exists_godementJacquetDenominators_constant_on_finiteEntryCover K (n + 1) S U hU hLeft hRight
  choose C hC using hBound e
  have hCW := integrableOn_godementJacquetThetaWeights_of_boundedOn_reductionSet K (n + 1) m
    mu S hS hFin e L R hDen.2.2 c hc C
      (fun A hA => And.intro (hC A hA).1 (hC A hA).2.1)
  have hBW := integrableOn_godementJacquetThetaWeights_of_boundedOn_reductionSet K (n + 1) m
    mu S hS hFin e L R hDen.2.2 b hb C (fun A hA => (hC A hA).2.2)
  exact godementJacquetInvertibleThetaMellin_entire_and_reflection_of_weightedFinsetRectangles
    K n mu D hD hUnique hMul T a d hTest.1 (fun i => HSMul.hSMul (w i) f)
    c b hc hb hInvariantC hInvariantB hPeriodsC hPeriodsB hMeanC hMeanB hcI hbI m hm
    L R hDen.1 hDen.2.1 (hCW.1.mono_set hDS) (hBW.2.mono_set hDS)
    (hBW.1.mono_set hDS) (hCW.2.mono_set hDS)

local notation "G" => AdelicGeneralLinearGroup K (n + 1)
local notation "A" => Units (Matrix (Fin (n + 1)) (Fin (n + 1)) (InfiniteAdeleRing K))
local notation "F" => Units (Matrix (Fin (n + 1)) (Fin (n + 1)) FA)
local notation "Gamma" => MonoidHom.range (adelicPrincipalDeterminantOne K (n + 1))
local notation "FiniteAdeles" => FA

set_option maxHeartbeats 1200000 in
/-- Given a reduction set with weighted cusp bounds, the Euler product
realized by local zeta integrals has an entire continuation. The theta
Mellins used in that continuation come from the same fundamental domain
as the matrix coefficient. -/
theorem exists_entire_completedEulerProduct_of_productTestReductionSet
    [MeasurableSpace G] [BorelSpace G] [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace F] [BorelSpace F]
    [BorelSpace (Prod A F)]
    [MeasurableSpace (adelicDeterminantLogNorm K (n + 1)).ker]
    [BorelSpace (adelicDeterminantLogNorm K (n + 1)).ker]
    (mu : Measure N) [SFinite mu] [mu.IsHaarMeasure] [mu.IsMulRightInvariant]
    [MeasurableMul N] [MeasurableInv N] [MeasurableMul G]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace FA] [BorelSpace FA] [MeasurableSpace AM] [BorelSpace AM]
    (muA : Measure A) (muF : Measure F) [SFinite muA] [SFinite muF]
    [muA.IsHaarMeasure] [muF.IsHaarMeasure]
    {J : Type*} [Fintype J] {P : Type*}
    (f : SchwartzMap Arch Complex) (Phi : J -> LocallyConstant (Ix -> FiniteAdeles) Complex)
    (hCompact : forall j, HasCompactSupport (fun x => Phi j x))
    (archCoefficient : A -> Complex) (finiteCoefficient : J -> F -> Complex)
    (D : Set N) (hD : MeasurableSet D)
    (hMul : Measurable (fun p : Prod G G => p.1 * p.2))
    (hMulN : Measurable (fun p : Prod N N => p.1 * p.2))
    (hUnique : forall x : N, ExistsUnique (fun gamma : Gamma => Membership.mem D (gamma.val * x)))
    (S : Set N) (hS : MeasurableSet S) (hDS : Set.Subset D S) (hFin : mu S < Top.top)
    (U : Set FA) (hU : IsCompact U)
    (hLeft : forall x : N, Membership.mem S x -> forall i j, Membership.mem U (x.val.val i j).2)
    (hRight : forall B : N, Membership.mem S B -> forall i j, Membership.mem U (B.val.inv i j).2)
    (v : J -> G -> Complex) (c : N -> Complex)
    (hV : forall j, Measurable (v j)) (hc : Measurable c)
    (hPrincipal : forall j (a : Matrix.GeneralLinearGroup (Fin (n + 1)) K) g,
      v j (adelicPrincipalGeneralLinear K (n + 1) a * g) = v j g)
    (hCentral : forall j (t : Real) (a : N),
      v j (adelicDeterminantSection K (n + 1) (Multiplicative.ofAdd t) * a.val) = v j a.val)
    (hcI : lintegral (mu.restrict D) (fun a => ENNReal.ofReal (norm (c a) ^ 2)) < Top.top)
    (hVI : forall j, lintegral (mu.restrict D)
      (fun a => ENNReal.ofReal (norm (v j a.val) ^ 2)) < Top.top)
    (hSplit : forall j g, integral (mu.restrict D) (fun h => v j (h.val * g) * c h) =
      archCoefficient ((adelicGeneralLinearGroup_prod K (n + 1) g).1) *
        finiteCoefficient j ((adelicGeneralLinearGroup_prod K (n + 1) g).2))
    (hInvariantC : forall gamma : Gamma, forall x, c (gamma.val * x) = c x)
    (hPeriodsC : HasGodementJacquetVanishingUnipotentPeriods c)
    (hPeriodsV : forall j, HasGodementJacquetVanishingUnipotentPeriods (fun a : N => v j a.val))
    (hMeanC : integral (mu.restrict D) c = 0)
    (hMeanV : forall j, integral (mu.restrict D) (fun a : N => v j a.val) = 0)
    (m : Nat) (hm : Module.finrank Real Arch < m)
    (hBound : forall (j : J) (e : Denom),
      let s := godementJacquetFullTheta_principalScalarMatrixUnit K (n + 1) e.val e.property
      let H := godementJacquetFullTheta_archimedeanHeight K (n + 1)
      exists C : Real, forall x : N, Membership.mem S x ->
        And (norm (c x) * H (s * x.val) 1 ^ m <= C)
          (And (norm (c x) * H 1 (Inv.inv x.val * s) ^ m <= C)
            (And (norm (v j x.val) * H (s * x.val) 1 ^ m <= C)
              (norm (v j x.val) * H 1 (Inv.inv x.val * s) ^ m <= C))))
    (w : J -> Complex) (tau : Real) (H : Complex -> J -> F -> Complex)
    (localFactor : Complex -> P -> Complex) (archFactor : Complex -> Complex) :
    let arch (X : Matrix (Fin (n + 1)) (Fin (n + 1)) (InfiniteAdeleRing K)) : Arch :=
      WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (X.vec i)))
    let zetaA (s : Complex) (g : A) :=
      (f (arch g.val) * archCoefficient g) *
        (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
          (s + (((n + 1 : Nat) : Complex) - 1) / 2)
    (forall s : Complex, tau < s.re -> Integrable (fun g : A => f (arch g.val) *
      (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
        (s + (((n + 1 : Nat) : Complex) - 1) / 2)) muA) ->
    (forall s : Complex, tau < s.re -> forall j, Integrable (fun g : F => Phi j g.val.vec *
      (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
        (s + (((n + 1 : Nat) : Complex) - 1) / 2)) muF) ->
    (forall s j g, H s j g = (Phi j g.val.vec * finiteCoefficient j g) *
        (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
          (s + (((n + 1 : Nat) : Complex) - 1) / 2)) ->
    (forall s : Complex, tau < s.re ->
      And (Integrable (zetaA s) muA) (integral muA (zetaA s) = archFactor s)) ->
    (forall s : Complex, tau < s.re -> forall j, Integrable (H s j) muF) ->
    (forall s : Complex, tau < s.re ->
      HasProd (localFactor s) (Finset.univ.sum (fun j => w j * integral muF (H s j)))) ->
    exists completed : Complex -> Complex, And (Differentiable Complex completed)
      (forall s : Complex, tau < s.re -> completed s = archFactor s * tprod (localFactor s)) := by
  intro arch zetaA hRawArch hRawFinite hH hArch hFinite hProd
  have hIncl : Measurable (Subtype.val : N -> G) := continuous_subtype_val.measurable
  have hInvariantV (j : J) (gamma : Gamma) (x : N) :
      v j ((gamma.val * x).val) = v j x.val := by
    choose a ha using gamma.property
    rw [<- ha]
    exact hPrincipal j a x.val
  have hEntire (j : J) :=
    (godementJacquetInvertibleThetaMellin_entire_and_reflection_productTest_of_reductionSet
      K n mu D hD hUnique hMulN S hS hDS hFin U hU hLeft hRight f (Phi j)
      (hCompact j) c (fun a : N => v j a.val) hc ((hV j).comp hIncl) hInvariantC
      (hInvariantV j) hPeriodsC (hPeriodsV j) hMeanC (hMeanV j) hcI (hVI j) m hm
      (hBound j)).1
  exact exists_entire_completedEulerProduct_of_productTestThetaMellin K (n + 1)
    (Nat.zero_lt_succ n) mu muA muF f Phi hCompact archCoefficient finiteCoefficient
    D hD hMul hUnique v c hV hc hPrincipal hCentral hcI hVI hSplit w tau H
    localFactor archFactor hRawArch hRawFinite hH hArch hFinite hProd hEntire

end

end Robin1984.GRH
