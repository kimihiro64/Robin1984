import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Robin1984.GRH.GodementJacquetArchimedeanSphericalProduct
import Robin1984.GRH.GodementJacquetFiniteAdelicTensorTests
import Robin1984.GRH.GodementJacquetGlobalZetaProduct
import Robin1984.GRH.GodementJacquetThetaDecay

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Absolute convergence of determinant-weighted Gaussian and finite compact tensor tests.
- Formalization note: Proves the archimedean and finite integral bounds and combines them in the adelic Mellin coordinates.
- PROVENANCE-END
-/

/-!
# Absolute integrability of determinant-weighted adelic tests

A scalar multiple of the Minkowski Gaussian is integrable with the
archimedean determinant weight when the real part of the parameter exceeds
`(n - 1) / 2`. For compact finite tensor tests, the corresponding range
is `(n + 1) / 2 < s.re`. Their integrability combines on the adelic group
by the determinant product measure.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical RealInnerProductSpace

noncomputable section

namespace Robin1984.GRH

section

variable (K : Type*) [Field K] (n : Nat)
  (F : Type*) [RCLike F] [ProperSpace F] [SecondCountableTopology F]
  [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
  [SigmaFinite (volume : Measure F)]

local notation "Gf" => Units (Matrix (Fin n) (Fin n) F)
local notation "U" => Matrix.unitaryGroup (Fin n) F
local notation "N" => valuationUpperUnitriangularSubgroup F n
local notation "P" => positiveDiagonalSubgroup F n
local notation "T" => positiveUpperTriangularMatrixSubgroup F n
local notation "Gv" => (fun w : InfinitePlace K =>
  Units (Matrix (Fin n) (Fin n) (InfinitePlace.Completion w)))
local notation "d" => Module.finrank Real F

set_option maxHeartbeats 1900000 in
private theorem integrable_archGaussianWeightedTestAtPlace
    (w : InfinitePlace K) (e : RingEquiv w.Completion F) (he : Isometry e)
    (hRank : d = w.mult)
    [MeasurableSpace P] [BorelSpace P] [MeasurableSpace T] [BorelSpace T]
    [MeasurableSpace Gf] [BorelSpace Gf] [MeasurableSpace U] [BorelSpace U]
    [MeasurableSpace (Gv w)] [BorelSpace (Gv w)]
    (mu : Measure Gf) [mu.IsHaarMeasure] [mu.InnerRegular] [SigmaFinite mu]
    (muU : Measure U) [muU.IsHaarMeasure] [IsProbabilityMeasure muU] :
    exists nu : Measure (Gv w), And nu.IsHaarMeasure (And (Nonempty (SigmaFinite nu))
      (forall s : Complex, ((n : Real) - 1) / 2 < s.re ->
        Integrable (fun g : Gv w => archLocalGaussianZetaDensity K n w s g 1) nu)) := by
  let z (i : Fin n) : Complex := ((i.val : Real) - ((n : Real) - 1) / 2 : Real)
  have hSec : forall (r : Fin n -> Real) (_ : forall i, 0 < r i) (u : N) (q : U)
      (g : Gf), g.val = ((Matrix.diagonal (fun i => (r i : F)) * u.val.val.val) * q.val) ->
      (1 : Complex) = Finset.univ.prod (fun i : Fin n =>
        (r i : Complex) ^ ((d : Complex) * z i +
          (d : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2)) := by
    intro r _ u _ _ _
    have hE (i : Fin n) :
        (d : Complex) * z i +
          (d : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2 = 0 := by
      simp only [z, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
        Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    simp only [hE, Complex.cpow_zero, Finset.prod_const_one]
  let B := archSphericalPlaceIntegral_of_section K n F w e he hRank mu muU z (fun _ => 1) hSec
  refine Exists.intro B.haar (And.intro B.isHaar (And.intro (Nonempty.intro B.sigmaFinite) ?_))
  intro s hs
  have hPos (i : Fin n) : 0 < (s + z i).re := by
    rw [Complex.add_re]
    change 0 < s.re + ((i.val : Real) - ((n : Real) - 1) / 2)
    have hi : 0 <= (i.val : Real) := Nat.cast_nonneg i.val
    linarith
  have hCoeff (g : Gv w) : B.coefficient g = 1 := by
    change integral muU (fun _ : U => (1 : Complex)) = 1
    simp
  simpa only [hCoeff] using (B.evaluation s hPos).1

end



section ArchimedeanWeight

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "W" => InfinitePlace K
local notation "G" => Units (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))
local notation "Gv" => (fun w : W => Units (Matrix (Fin n) (Fin n) (InfinitePlace.Completion w)))
local notation "GR" => Units (Matrix (Fin n) (Fin n) Real)
local notation "GC" => Units (Matrix (Fin n) (Fin n) Complex)
local notation "UR" => Matrix.unitaryGroup (Fin n) Real
local notation "UC" => Matrix.unitaryGroup (Fin n) Complex
local notation "DR" => positiveDiagonalSubgroup Real n
local notation "DC" => positiveDiagonalSubgroup Complex n
local notation "TR" => positiveUpperTriangularMatrixSubgroup Real n
local notation "TC" => positiveUpperTriangularMatrixSubgroup Complex n
local notation "Ix" => Prod (Fin n) (Fin n)

set_option maxHeartbeats 2400000 in
/-- A scalar multiple of the Minkowski Gaussian is integrable against the
archimedean determinant weight on the stated right half-plane. -/
theorem integrable_archGaussianWeightedTest
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G]
    [forall w : W, MeasurableSpace (Gv w)] [forall w : W, BorelSpace (Gv w)]
    [BorelSpace (forall w : W, Gv w)]
    [MeasurableSpace DR] [BorelSpace DR] [MeasurableSpace TR] [BorelSpace TR]
    [MeasurableSpace DC] [BorelSpace DC] [MeasurableSpace TC] [BorelSpace TC]
    [MeasurableSpace GR] [BorelSpace GR] [MeasurableSpace GC] [BorelSpace GC]
    [MeasurableSpace UR] [BorelSpace UR] [MeasurableSpace UC] [BorelSpace UC]
    (mu : Measure G) [SFinite mu] [mu.IsHaarMeasure]
    (muR : Measure GR) [muR.IsHaarMeasure] [muR.InnerRegular] [SigmaFinite muR]
    (muC : Measure GC) [muC.IsHaarMeasure] [muC.InnerRegular] [SigmaFinite muC]
    (probR : Measure UR) [probR.IsHaarMeasure] [IsProbabilityMeasure probR]
    (probC : Measure UC) [probC.IsHaarMeasure] [IsProbabilityMeasure probC] :
    forall (s : Complex), ((n : Real) - 1) / 2 < s.re -> forall a : Complex,
      Integrable (fun g : G =>
        (HSMul.hSMul a (archMinkowskiMatrixGaussian K n))
          (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
            (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i)))) *
          (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
            (s + ((n : Complex) - 1) / 2)) mu := by
  classical
  have hEach (w : W) :
    exists nu : Measure (Gv w), And nu.IsHaarMeasure (And (Nonempty (SigmaFinite nu))
      (forall s : Complex, ((n : Real) - 1) / 2 < s.re ->
        Integrable (fun g : Gv w => archLocalGaussianZetaDensity K n w s g 1) nu)) := by
    by_cases h : w.IsReal
    . exact integrable_archGaussianWeightedTestAtPlace K n Real w
        (InfinitePlace.Completion.ringEquivRealOfIsReal h)
        (archRealCompletionIsometry w h) (archRealCompletionRank w h) muR probR
    . have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
      exact integrable_archGaussianWeightedTestAtPlace K n Complex w
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc)
        (archComplexCompletionIsometry w hc) (archComplexCompletionRank w hc) muC probC
  choose nu hv using hEach
  let _ : forall w : W, (nu w).IsHaarMeasure := fun w => (hv w).1
  let _ : forall w : W, SigmaFinite (nu w) := fun w => Classical.choice (hv w).2.1
  choose c hC using exists_archGaussianZetaIntegral_of_integrable K n mu nu
    (fun _ _ => 1) (fun _ => 1) (by intro g; simp)
  intro s hs a
  have hI := (hC.2 s (fun w => (hv w).2.2 s hs)).1
  have hI' : Integrable (fun g : G =>
      (archMinkowskiMatrixGaussian K n)
        (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
          (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i)))) *
        (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
          (s + ((n : Complex) - 1) / 2)) mu := by
    simpa only [mul_one] using hI
  simpa only [smul_apply, smul_eq_mul, mul_assoc] using hI'.const_mul a

end ArchimedeanWeight

section

variable {K : Type*} [Field K] [NumberField K]
  (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)

local notation "L" => p.adicCompletion K
local notation "v" => (Valued.v : Valuation L (WithZero (Multiplicative Int)))
local notation "G" => Units (Matrix (Fin n) (Fin n) L)

set_option maxHeartbeats 900000 in
private theorem heckeUnramifiedLocalMatrixWeight_eq_one_of_integral
    (s : Complex) (g : G) (hg : Membership.mem (finiteLocalMatrixUnitSubgroup K n p) g) :
    heckeUnramifiedLocalMatrixWeight p n s g = 1 := by
  have hEntries : And
      (forall i j : Fin n, Membership.mem (v).integer (g.val i j))
      (forall i j : Fin n, Membership.mem (v).integer (g.inv i j)) := by
    change And
      (forall i j : Fin n, Membership.mem (p.adicCompletionIntegers K) (g.val i j))
      (forall i j : Fin n, Membership.mem (p.adicCompletionIntegers K) (g.inv i j)) at hg
    exact hg
  have hLe (A : Matrix (Fin n) (Fin n) L)
      (hA : forall i j, Membership.mem (v).integer (A i j)) : norm A.det <= 1 := by
    have hB : forall i j, norm (A i j) <= (1 : Real) :=
      fun i j => (heckeLocal_mem_integers_iff_norm_le_one p _).mp (hA i j)
    simpa only [one_pow] using
      norm_godementJacquet_det_le_pow_of_isUltrametricDist n A 1 zero_le_one hB
  have hL := hLe g.val hEntries.1
  have hR := hLe g.inv hEntries.2
  have hProd : norm g.val.det * norm g.inv.det = 1 := by
    rw [<- norm_mul, <- Matrix.det_mul, g.val_inv, Matrix.det_one, norm_one]
  have hNorm : norm g.val.det = 1 :=
    le_antisymm hL (hProd.symm.le.trans (mul_le_of_le_one_right (norm_nonneg _) hR))
  unfold heckeUnramifiedLocalMatrixWeight
  have hMem : Membership.mem {x : G | forall i j : Fin n, Membership.mem (v).integer (x.val i j)} g :=
    hEntries.1
  rw [Set.indicator_of_mem hMem, hNorm, Complex.ofReal_one, Complex.one_cpow]

set_option maxHeartbeats 900000 in
private theorem measurable_heckeUnramifiedLocalMatrixWeight
    [MeasurableSpace G] [BorelSpace G] (s : Complex) :
    Measurable (heckeUnramifiedLocalMatrixWeight p n s) := by
  let S : Set G := {g | forall i j : Fin n, Membership.mem (v).integer (g.val i j)}
  have hS : MeasurableSet S := by
    have hEq : S = Set.iInter (fun i : Fin n => Set.iInter
        (fun j : Fin n => {g : G | norm (g.val i j) <= 1})) := by
      ext g
      simp only [S, Set.mem_ofPred_eq, Set.mem_iInter]
      exact Iff.intro
        (fun h i j => (heckeLocal_mem_integers_iff_norm_le_one p _).mp (h i j))
        (fun h i j => (heckeLocal_mem_integers_iff_norm_le_one p _).mpr (h i j))
    rw [hEq]
    refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    have hA : Continuous (fun A : Matrix (Fin n) (Fin n) L => A i j) :=
      (continuous_apply j).comp (continuous_apply i)
    have hE : Continuous (fun g : G => norm (g.val i j)) :=
      (hA.comp Units.continuous_val).norm
    exact (isClosed_le hE continuous_const).measurableSet
  have hB : Continuous (fun g : G => (norm g.val.det : Complex)) :=
    Complex.continuous_ofReal.comp (Units.continuous_val.matrix_det.norm)
  have hPow : Continuous (fun g : G => (norm g.val.det : Complex) ^
      (s + (((n : Real) - 1) / 2 : Real))) :=
    hB.cpow continuous_const (fun g => Complex.ofReal_mem_slitPlane.mpr
      (norm_pos_iff.mpr (g.isUnit.map Matrix.detMonoidHom).ne_zero))
  exact hPow.measurable.indicator hS

end



section FiniteWeightedTensor

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "Fa" => FiniteAdeleRing (RingOfIntegers K) K
local notation "Ml" => (fun p : P => Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion K p))
local notation "Gl" => (fun p : P => Units (Ml p))
local notation "G" => Units (Matrix (Fin n) (Fin n) Fa)

set_option maxHeartbeats 3500000 in
/-- Compact tests at finitely many places and integral indicators elsewhere
form an absolutely integrable determinant-weighted finite tensor. -/
theorem integrable_finiteAdeleDeterminantWeightedTensor
    (E : Finset P) [Countable P] [(Filter.atTop : Filter (Finset P)).IsCountablyGenerated]
    [forall S : Finset P, Fintype (S : Set P)]
    [MeasurableSpace Fa] [BorelSpace Fa]
    [forall p : P, MeasurableSpace (HeightOneSpectrum.adicCompletion K p)]
    [forall p : P, BorelSpace (HeightOneSpectrum.adicCompletion K p)]
    [forall p : P, MeasurableSpace (Units (HeightOneSpectrum.adicCompletion K p))]
    [forall p : P, BorelSpace (Units (HeightOneSpectrum.adicCompletion K p))]
    [forall p : P, SigmaFinite (heckeLocalHaar p)]
    [MeasurableSpace G] [BorelSpace G]
    [forall p : P, MeasurableSpace (Gl p)] [forall p : P, BorelSpace (Gl p)]
    [forall p : P, MeasurableMul (Gl p)]
    [forall S : Finset P, MeasurableSpace ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val)]
    [forall S : Finset P, BorelSpace (FiniteAdeleMatrixHaarChart K n S)]
    (mu : Measure G)
    (localHaar : forall p : P, Measure (Gl p))
    [forall p, (localHaar p).IsMulLeftInvariant] [forall p, SigmaFinite (localHaar p)]
    (hLocalMass : forall p : P, localHaar p (finiteLocalMatrixUnitSubgroup K n p : Set (Gl p)) = 1)
    (tailHaar : forall S : Finset P, Measure ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val))
    [forall S, IsProbabilityMeasure (tailHaar S)]
    (hMeasure : forall S : Finset P, mu.comap (finiteAdeleMatrixHaarChartEmbedding K n S) =
      (Measure.pi (fun p : (S : Set P) => localHaar p.val)).prod (tailHaar S))
    (u0 : forall p : P, Units (HeightOneSpectrum.adicCompletion K p))
    (hu0 : forall p : P, Valued.v (u0 p).val = finiteUniformizerValue)
    (Phi : forall p : {q : P // Membership.mem E q}, LocallyConstant (Ml p.val) Complex)
    (hPhi : forall p, HasCompactSupport (fun X => Phi p X)) :
    let PhiLocal (p : P) (g : Gl p) := if hp : Membership.mem E p then
      Phi (Subtype.mk p hp) g.val else
      Set.indicator {y : Gl p | forall i j : Fin n,
        Membership.mem (p.adicCompletionIntegers K) (y.val i j)} (fun _ => (1 : Complex)) g
    forall s : Complex, ((n : Real) + 1) / 2 < s.re ->
      Integrable (fun g : G => finiteAdeleMatrixRestrictedZetaIntegrand K n PhiLocal g *
        (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
          (s + ((n : Complex) - 1) / 2)) mu := by
  classical
  intro PhiLocal s hs
  let z := s + (((((n : Real) - 1) / 2) : Real) : Complex)
  have hz : z = s + ((n : Complex) - 1) / 2 := by
    simp only [z, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast,
      Complex.ofReal_one, Complex.ofReal_ofNat]
  let f (p : P) (g : Gl p) := (norm g.val.det : Complex) ^ z * PhiLocal p g
  have hV (p : P) :
      finiteLocalMatrixUnitSubgroup K n p =
        valuationIntegralMatrixSubgroup
          (Valued.v : Valuation (HeightOneSpectrum.adicCompletion K p) (WithZero (Multiplicative Int))) n := by
    ext g
    rw [mem_valuationIntegralMatrixSubgroup_iff]
    change (And
      (forall i j : Fin n, Membership.mem (p.adicCompletionIntegers K) (g.val i j))
      (forall i j : Fin n, Membership.mem (p.adicCompletionIntegers K) (g.inv i j))) <-> _
    rfl
  have hMass (p : P) : localHaar p
      (valuationIntegralMatrixSubgroup
         (Valued.v : Valuation (HeightOneSpectrum.adicCompletion K p) (WithZero (Multiplicative Int))) n :
        Set (Gl p)) = 1 := by
    rw [<- hV p]
    exact hLocalMass p
  have hWeight (p : P) (hp : Not (Membership.mem E p)) :
      f p = heckeUnramifiedLocalMatrixWeight p n s := by
    funext g
    let S : Set (Gl p) := {y | forall i j : Fin n,
      Membership.mem (p.adicCompletionIntegers K) (y.val i j)}
    simp only [f, PhiLocal, dif_neg hp]
    change (norm g.val.det : Complex) ^ z * Set.indicator S (fun _ => (1 : Complex)) g =
      Set.indicator S (fun u => (norm u.val.det : Complex) ^ z) g
    by_cases h : Membership.mem S g
    . rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    . rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  have hEntries (p : P) (g : Gl p) (hg : Membership.mem (finiteLocalMatrixUnitSubgroup K n p) g) :
      forall i j : Fin n, Membership.mem (p.adicCompletionIntegers K) (g.val i j) := by
    change And
      (forall i j : Fin n, Membership.mem (p.adicCompletionIntegers K) (g.val i j))
      (forall i j : Fin n, Membership.mem (p.adicCompletionIntegers K) (g.inv i j)) at hg
    exact hg.1
  have hOne : forall p : P, Not (Membership.mem E p) -> forall g,
      Membership.mem (finiteLocalMatrixUnitSubgroup K n p) g -> f p g = 1 := by
    intro p hp g hg
    rw [hWeight p hp]
    exact heckeUnramifiedLocalMatrixWeight_eq_one_of_integral p n s g hg
  have hPhiOne : forall p : P, Not (Membership.mem E p) -> forall g,
      Membership.mem (finiteLocalMatrixUnitSubgroup K n p) g -> PhiLocal p g = 1 := by
    intro p hp g hg
    simp only [PhiLocal, dif_neg hp]
    have hm : Membership.mem {y : Gl p | forall i j : Fin n,
        Membership.mem (p.adicCompletionIntegers K) (y.val i j)} g := hEntries p g hg
    rw [Set.indicator_of_mem hm]
  have hGood (p : P) (hp : Not (Membership.mem E p)) :
      And (Integrable (f p) (localHaar p))
        (integral (localHaar p) (fun g => norm (f p g)) <=
          unramifiedLocalAbsoluteEulerFactor p n s.re) := by
    rw [hWeight p hp]
    have hm : AEStronglyMeasurable (fun g : Gl p => heckeUnramifiedLocalMatrixWeight p n s g * 1)
        (localHaar p) := by
      simpa only [mul_one] using
        (measurable_heckeUnramifiedLocalMatrixWeight p n s).aestronglyMeasurable
    have hb : Filter.Eventually (fun _ : Gl p => norm (1 : Complex) <= 1) (ae (localHaar p)) :=
      Filter.Eventually.of_forall (fun _ => by simp)
    simpa only [mul_one] using
      integrableAndAbsoluteIntegral_le_unramifiedLocalWeight p n (u0 p) (hu0 p)
        (localHaar p) (hMass p) s hs (fun _ => 1) hb hm
  have hInt (p : P) : Integrable (f p) (localHaar p) := by
    by_cases hp : Membership.mem E p
    . let a := Phi (Subtype.mk p hp)
      have hs' : ((n : Real) - 1) / 2 < s.re := by linarith
      have hMeas : AEStronglyMeasurable (fun _ : Gl p => (1 : Complex)) (localHaar p) :=
        aestronglyMeasurable_const
      have hOneBound : Filter.Eventually (fun _ : Gl p => norm (1 : Complex) <= 1) (ae (localHaar p)) :=
        Filter.Eventually.of_forall (fun _ => by simp)
      have H := integrable_heckeLocalZetaIntegrand_of_compactlySupportedTest p n (u0 p) (hu0 p)
        (localHaar p) (hMass p) s hs' a a.continuous (hPhi (Subtype.mk p hp)) (fun _ => 1) hMeas hOneBound
      simpa only [f, PhiLocal, dif_pos hp, z, a, mul_one] using H
    . exact (hGood p hp).1
  let r (p : P) := integral (localHaar p) (fun g => norm (f p g))
  have hr (p : P) : 0 <= r p := integral_nonneg (fun _ => norm_nonneg _)
  let B := Finset.univ.prod (fun i : Fin n =>
    (dedekindZeta K ((s.re - (((n : Real) - 1) / 2 - (i.val : Real)) : Real) : Complex)).re)
  have hBound (S : Finset P) (hES : E <= S) : S.prod r <= (E.prod r) * B := by
    have hOutside : (SDiff.sdiff S E).prod r <= B := by
      refine le_trans ?_ (prod_unramifiedLocalAbsoluteEulerFactor_le (K := K) n s.re hs
        (SDiff.sdiff S E))
      exact Finset.prod_le_prod (fun p _ => hr p)
        (fun p hp => (hGood p (Finset.mem_sdiff.mp hp).2).2)
    calc
      S.prod r = ((SDiff.sdiff S E).prod r) * E.prod r := (Finset.prod_sdiff hES).symm
      _ <= B * E.prod r := mul_le_mul_of_nonneg_right hOutside (Finset.prod_nonneg (fun p _ => hr p))
      _ = E.prod r * B := mul_comm _ _
  have h := integrableAndHasProd_finiteAdeleMatrixRestrictedZetaIntegrand_withExceptions K n E
    mu localHaar tailHaar hMeasure f hOne hInt (E.prod r * B) hBound
  have hEq (g : G) :
      finiteAdeleMatrixRestrictedZetaIntegrand K n f g =
        finiteAdeleMatrixRestrictedZetaIntegrand K n PhiLocal g *
          (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g) : Complex) ^
            (s + ((n : Complex) - 1) / 2) := by
    have hTensor := finiteAdeleMatrixRestrictedZetaIntegrand_tensorFactorization K n E PhiLocal
      (fun _ _ => 1) hPhiOne (fun _ _ _ _ => rfl) g z
    have hUnitProduct : finiteAdeleMatrixRestrictedZetaIntegrand K n (fun _ _ => 1) g = 1 := by
      simp [finiteAdeleMatrixRestrictedZetaIntegrand]
    rw [hUnitProduct, mul_one] at hTensor
    rw [<- hz, mul_comm]
    simpa only [mul_one, f] using hTensor
  have hEqFun := funext hEq
  rw [<- hEqFun]
  exact h.1

end FiniteWeightedTensor


section AdelicWeightedTest

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "G" => AdelicGeneralLinearGroup K n
local notation "A" => Units (Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))
local notation "Fa" => FiniteAdeleRing (RingOfIntegers K) K
local notation "F" => Units (Matrix (Fin n) (Fin n) Fa)
local notation "Ix" => Prod (Fin n) (Fin n)
local notation "Arch" => PiLp 2 (fun _ : Ix => DedekindZeta.Theta.minkowskiSpace K)

set_option maxHeartbeats 1500000 in
/-- Absolute integrability of the two weighted factors gives absolute
integrability of the product in the global Mellin coordinates. -/
theorem integrable_adelicDeterminantWeightedMatrixTest_of_parts
    [MeasurableSpace G] [BorelSpace G] [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace F] [BorelSpace F]
    [BorelSpace (Prod A F)]
    [MeasurableSpace (adelicDeterminantLogNorm K n).ker]
    [BorelSpace (adelicDeterminantLogNorm K n).ker]
    (hn : 0 < n) (mu : Measure (adelicDeterminantLogNorm K n).ker) [SFinite mu] [mu.IsHaarMeasure]
    (muA : Measure A) (muF : Measure F) [SFinite muA] [SFinite muF]
    [muA.IsHaarMeasure] [muF.IsHaarMeasure]
    (f : SchwartzMap Arch Complex) (Phi : LocallyConstant (Ix -> Fa) Complex)
    (z : Complex) :
    let a (x : A) := f (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
      (InfiniteAdeleRing.ringEquiv_mixedSpace K (x.val.vec i))))
    let b (x : F) := Phi x.val.vec
    let test (g : G) :=
      f (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.vec i).1))) *
          Phi (fun i : Ix => (g.val.vec i).2)
    Integrable (fun x : A => a x *
      (heckeInfiniteIdeleNorm (Matrix.GeneralLinearGroup.det x) : Complex) ^ z) muA ->
    Integrable (fun x : F => b x *
      (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det x) : Complex) ^ z) muF ->
    Integrable (fun g : G => test g * (adelicDeterminantNorm K n g : Complex) ^ z)
      (adelicDeterminantProductMeasure K n hn mu) := by
  intro a b test hA hF
  have hSplit (g : G) : test g =
      a (adelicGeneralLinearGroup_prod K n g).1 *
        b (adelicGeneralLinearGroup_prod K n g).2 := by
    have hArchVec (i : Ix) : ((adelicGeneralLinearGroup_prod K n g).1.val.vec i) =
        (g.val.vec i).1 :=
      (adelicGeneralLinearGroup_prod_val K n g i.2 i.1).1
    have hFiniteVec : ((adelicGeneralLinearGroup_prod K n g).2.val.vec) =
        (fun i : Ix => (g.val.vec i).2) :=
      funext (fun i => (adelicGeneralLinearGroup_prod_val K n g i.2 i.1).2)
    simp only [test, a, b, hArchVec, hFiniteVec]
  choose r hr using exists_adelicDeterminantProductMeasure_tensorIntegral K n hn mu muA muF
  exact (hr.2 z test a b hSplit hA hF).1

end AdelicWeightedTest

end Robin1984.GRH
