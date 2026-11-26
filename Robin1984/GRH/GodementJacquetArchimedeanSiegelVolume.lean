import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Ring
import Robin1984.GRH.GodementJacquetArchimedeanExponentialHaar

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The classical archimedean Iwasawa volume calculation for Siegel sets.
- Formalization note: Proves finite Haar volume for bounded conjugated upper entries, a bounded determinant log, and lower-bounded consecutive diagonal gaps.
- PROVENANCE-END
-/

/-!
# Finite Haar volume of an archimedean Siegel region

Diagonal conjugation changes the upper-entry Haar volume by an exponential
factor. In determinant and consecutive-gap coordinates its exponent splits
into a sum of one-dimensional terms with positive decay coefficients.
-/

set_option autoImplicit false

open MeasureTheory

namespace Robin1984.GRH

private theorem sum_first_logDifference (n : Nat) (x : Fin (n + 1) -> Real) :
    Finset.univ.sum (fun j : Fin n => x 0 - x j.succ) =
      Finset.univ.sum (fun j : Fin n => ((n : Real) - (j.val : Real)) *
        (x j.castSucc - x j.succ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let v := x ((0 : Fin (n + 1)).succ)
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have hg : Finset.univ.sum (fun i : Fin n => x 0 - x i.succ.succ) =
        (n : Real) * (x 0 - v) + Finset.univ.sum (fun i : Fin n => v - x i.succ.succ) := by
      calc
        _ = Finset.univ.sum (fun i : Fin n => (x 0 - v) + (v - x i.succ.succ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
    have ht : Finset.univ.sum (fun i : Fin n =>
          ((((n + 1 : Nat) : Real) - (i.succ.val : Real)) *
            (x i.succ.castSucc - x i.succ.succ))) =
        Finset.univ.sum (fun i : Fin n =>
          ((n : Real) - (i.val : Real)) * (x i.castSucc.succ - x i.succ.succ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      change (((n + 1 : Nat) : Real) - ((i.val + 1 : Nat) : Real)) *
        (x i.castSucc.succ - x i.succ.succ) =
          ((n : Real) - (i.val : Real)) * (x i.castSucc.succ - x i.succ.succ)
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [hg, ht]
    have hTail := ih (fun i => x i.succ)
    change Finset.univ.sum (fun i : Fin n => v - x i.succ.succ) =
      Finset.univ.sum (fun i : Fin n =>
        ((n : Real) - (i.val : Real)) * (x i.castSucc.succ - x i.succ.succ)) at hTail
    rw [hTail]
    simp only [Fin.val_zero, Nat.cast_zero, sub_zero, Nat.cast_succ]
    change x 0 - v + ((n : Real) * (x 0 - v) + _) = ((n : Real) + 1) * (x 0 - v) + _
    ring

def siegelRootMultiplicity (n : Nat) (i : Fin n) : Real :=
  ((i.val : Real) + 1) * ((n : Real) - (i.val : Real))

/-- Each consecutive logarithmic gap is used by exactly
`(i + 1) * (n - i)` strict upper entries in rank `n + 1`. -/
theorem archUpperLogRatioSum_eq_weightedRootGaps (n : Nat) (x : Fin (n + 1) -> Real) :
    archUpperLogRatioSum (n + 1) x = Finset.univ.sum (fun i : Fin n =>
      siegelRootMultiplicity n i * (x i.castSucc - x i.succ)) := by
  induction n with
  | zero => simp [archUpperLogRatioSum]
  | succ n ih =>
    rw [archUpperLogRatioSum, ih, sum_first_logDifference, Fin.sum_univ_succ,
      Fin.sum_univ_succ]
    let g := x 0 - x ((0 : Fin (n + 1)).succ)
    let b (i : Fin n) := x i.castSucc.succ - x i.succ.succ
    let L := Finset.univ.sum (fun i : Fin n => siegelRootMultiplicity n i * b i)
    let R := Finset.univ.sum (fun i : Fin n =>
      (((n + 1 : Nat) : Real) - (i.succ.val : Real)) * b i)
    let T := Finset.univ.sum (fun i : Fin n => siegelRootMultiplicity (n + 1) i.succ * b i)
    have hMass : L + R = T := by
      change _ + _ = Finset.univ.sum (fun i : Fin n => siegelRootMultiplicity (n + 1) i.succ * b i)
      rw [show L = Finset.univ.sum (fun i : Fin n => siegelRootMultiplicity n i * b i) from rfl,
        show R = Finset.univ.sum (fun i : Fin n =>
          (((n + 1 : Nat) : Real) - (i.succ.val : Real)) * b i) from rfl,
        <- Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [siegelRootMultiplicity, Fin.val_succ, Nat.cast_succ]
      ring
    have hZero : siegelRootMultiplicity (n + 1) (0 : Fin (n + 1)) = (n + 1 : Nat) := by
      simp [siegelRootMultiplicity]
    have hz : (Fin.castSucc (0 : Fin (n + 1))) = (0 : Fin (n + 2)) :=
      Fin.ext (by simp)
    simp only [hz, Fin.val_zero, Nat.cast_zero]
    change L + ((((n + 1 : Nat) : Real) - (0 : Real)) * g + R) =
      siegelRootMultiplicity (n + 1) (0 : Fin (n + 1)) * g + T
    rw [hZero, <- hMass, sub_zero]
    ring

/-- The root factor of the Haar density has finite mass on a product of
lower-bounded root coordinates. The formula allows a separate bound
for each coordinate. -/
theorem integrable_and_integral_siegelRootDensity (n : Nat) (d : Real) (hd : 0 < d)
    (lower : Fin n -> Real) :
    let mu := Measure.pi (fun i : Fin n => (volume : Measure Real).restrict (Set.Ioi (lower i)))
    let density (t : Fin n -> Real) :=
      Real.exp (Finset.univ.sum (fun i : Fin n => -(d * siegelRootMultiplicity n i) * t i))
    And (Integrable density mu)
      (integral mu density = Finset.univ.prod (fun i : Fin n =>
        Real.exp (-(d * siegelRootMultiplicity n i) * lower i) / (d * siegelRootMultiplicity n i))) := by
  intro mu density
  let f (i : Fin n) (x : Real) := Real.exp (-(d * siegelRootMultiplicity n i) * x)
  have hc (i : Fin n) : 0 < d * siegelRootMultiplicity n i := mul_pos hd (
    mul_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one)
      (sub_pos.mpr (Nat.cast_lt.mpr i.isLt)))
  have hf (i : Fin n) : Integrable (f i) ((volume : Measure Real).restrict (Set.Ioi (lower i))) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (hc i)) (lower i)
  have heq : density = (fun t => Finset.univ.prod (fun i => f i (t i))) := by
    funext t
    exact Real.exp_sum Finset.univ (fun i : Fin n => -(d * siegelRootMultiplicity n i) * t i)
  rw [heq]
  refine And.intro (Integrable.fin_nat_prod hf) ?_
  change integral (Measure.pi (fun i : Fin n => (volume : Measure Real).restrict (Set.Ioi (lower i))))
      (fun t => Finset.univ.prod (fun i => f i (t i))) = _
  rw [integral_fin_nat_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi
  change integral ((volume : Measure Real).restrict (Set.Ioi (lower i))) (f i) = _
  rw [show f i = (fun x => Real.exp (-(d * siegelRootMultiplicity n i) * x)) from rfl,
    integral_exp_mul_Ioi (neg_lt_zero.mpr (hc i)), div_neg, neg_div, neg_neg]


/-- The determinant log and the consecutive gaps of a diagonal. -/
private def siegelDiagonalCoordinateMap (n : Nat) :
    LinearMap (RingHom.id Real) (Fin (n + 1) -> Real) (Prod Real (Fin n -> Real)) where
  toFun x := Prod.mk (Finset.univ.sum x) (fun i => x i.castSucc - x i.succ)
  map_add' := by
    intro x y
    apply Prod.ext
    . change Finset.univ.sum (fun i => x i + y i) = Finset.univ.sum x + Finset.univ.sum y
      exact Finset.sum_add_distrib
    . funext i
      change (x i.castSucc + y i.castSucc) - (x i.succ + y i.succ) =
        (x i.castSucc - x i.succ) + (y i.castSucc - y i.succ)
      ring
  map_smul' := by
    intro a x
    apply Prod.ext
    . change Finset.univ.sum (fun i => a * x i) = a * Finset.univ.sum x
      rw [Finset.mul_sum]
    . funext i
      change a * x i.castSucc - a * x i.succ = a * (x i.castSucc - x i.succ)
      rw [mul_sub]

private theorem siegelDiagonalCoordinateMap_injective (n : Nat) :
    Function.Injective (siegelDiagonalCoordinateMap n) := by
  intro x y h
  let z (i : Fin (n + 1)) := x i - y i
  have hs : Finset.univ.sum z = 0 := by
    change Finset.univ.sum (fun i => x i - y i) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (congrArg Prod.fst h)
  have hg (i : Fin n) : z i.castSucc = z i.succ := by
    have he : x i.castSucc - x i.succ = y i.castSucc - y i.succ :=
      congrFun (congrArg Prod.snd h) i
    apply sub_eq_zero.mp
    calc
      z i.castSucc - z i.succ =
          (x i.castSucc - x i.succ) - (y i.castSucc - y i.succ) := by
        unfold z
        ring
      _ = 0 := sub_eq_zero.mpr he
  have hc (i : Fin (n + 1)) : z i = z 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i hi => exact (hg i).symm.trans hi
  simp_rw [hc] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hz : z 0 = 0 :=
    (mul_eq_zero.mp hs).resolve_left (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  funext i
  exact sub_eq_zero.mp ((hc i).trans hz)

/-- In rank n + 1 the diagonal log entries are determined by the log of
their determinant and the n consecutive upper-root gaps. -/
noncomputable def siegelDiagonalCoordinates (n : Nat) :
    LinearEquiv (RingHom.id Real) (Fin (n + 1) -> Real) (Prod Real (Fin n -> Real)) :=
  LinearEquiv.ofInjectiveOfFinrankEq (siegelDiagonalCoordinateMap n)
    (siegelDiagonalCoordinateMap_injective n) (by
      rw [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_self,
        Module.finrank_fin_fun, Nat.add_comm])

theorem siegelDiagonalCoordinates_apply (n : Nat) (x : Fin (n + 1) -> Real) :
    siegelDiagonalCoordinates n x =
      Prod.mk (Finset.univ.sum x) (fun i => x i.castSucc - x i.succ) := by
  rfl


/-- The exponential root density is integrable over log diagonals with
bounded determinant log and lower bounds on all consecutive gaps. -/
theorem integrableOn_siegelDiagonalStrip (n : Nat) (d : Real) (hd : 0 < d)
    (a b : Real) (lower : Fin n -> Real) :
    IntegrableOn (fun x : Fin (n + 1) -> Real =>
      Real.exp (-d * Finset.univ.sum (fun i : Fin n =>
        siegelRootMultiplicity n i * (x i.castSucc - x i.succ))))
      {x | And (Set.Icc a b (Finset.univ.sum x))
        (forall i : Fin n, lower i < x i.castSucc - x i.succ)} := by
  let E := siegelDiagonalCoordinates n
  let S := Set.Icc a b
  let T := Set.pi (Set.univ : Set (Fin n)) (fun i => Set.Ioi (lower i))
  let D := Set.prod S T
  let rho (t : Fin n -> Real) := Real.exp (Finset.univ.sum (fun i : Fin n =>
    -(d * siegelRootMultiplicity n i) * t i))
  let V := (volume : Measure (Fin (n + 1) -> Real))
  let mu := (volume : Measure Real).prod (volume : Measure (Fin n -> Real))
  let gamma := Measure.map E V
  let _ : gamma.IsAddHaarMeasure := Measure.MapLinearEquiv.isAddHaarMeasure V E
  have hE : MeasurableEmbedding E := E.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hScale := Measure.isAddLeftInvariant_eq_smul gamma mu
  have hT : MeasurableSet T := by
    have hEq : T = Set.iInter (fun i : Fin n => Set.preimage (fun t : Fin n -> Real => t i)
        (Set.Ioi (lower i))) := by
      ext t
      simp [T]
    rw [hEq]
    exact MeasurableSet.iInter (fun i => measurableSet_Ioi.preimage (measurable_pi_apply i))
  have hD : MeasurableSet D := measurableSet_Icc.prod hT
  have hVol : (volume : Measure Real) S < Top.top := isCompact_Icc.measure_lt_top
  have hOne : Integrable (fun _ : Real => (1 : Real)) ((volume : Measure Real).restrict S) :=
    integrableOn_const hVol.ne
  have hRoots : Integrable rho ((volume : Measure (Fin n -> Real)).restrict T) := by
    rw [volume_pi, Measure.restrict_pi_pi]
    exact (integrable_and_integral_siegelRootDensity n d hd lower).1
  have hDens : Integrable (fun p : Prod Real (Fin n -> Real) => rho p.2) (mu.restrict D) := by
    have hProd : ((volume : Measure Real).restrict S).prod
        ((volume : Measure (Fin n -> Real)).restrict T) = mu.restrict D :=
      Measure.prod_restrict S T
    rw [<- hProd]
    simpa only [one_mul] using hOne.mul_prod hRoots
  have hMapped : Integrable (fun p : Prod Real (Fin n -> Real) => rho p.2) (gamma.restrict D) := by
    rw [hScale, Measure.restrict_smul]
    exact hDens.smul_measure_nnreal
  change Integrable _ ((Measure.map E V).restrict D) at hMapped
  rw [Measure.restrict_map hE.measurable hD] at hMapped
  have hpull := hE.integrable_map_iff.mp hMapped
  have hDomain : Set.preimage E D = {x | And (S (Finset.univ.sum x))
      (forall i : Fin n, lower i < x i.castSucc - x i.succ)} := by
    ext x
    change D (siegelDiagonalCoordinates n x) <-> _
    rw [siegelDiagonalCoordinates_apply]
    change And (S (Finset.univ.sum x)) (T (fun i : Fin n => x i.castSucc - x i.succ)) <-> _
    constructor
    . intro h
      exact And.intro h.1 (fun i => h.2 i (Set.mem_univ _))
    . intro h
      exact And.intro h.1 (fun i _ => h.2 i)
  rw [hDomain] at hpull
  have hRho (x : Fin (n + 1) -> Real) :
      rho (E x).2 = Real.exp (-d * Finset.univ.sum (fun i : Fin n =>
        siegelRootMultiplicity n i * (x i.castSucc - x i.succ))) := by
    change rho (siegelDiagonalCoordinates n x).2 = _
    rw [siegelDiagonalCoordinates_apply]
    unfold rho
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change Integrable (fun x => rho (E x).2) _ at hpull
  simp_rw [hRho] at hpull
  exact hpull


/-- The log diagonal lies in a bounded determinant interval and each
consecutive gap has its own lower bound. -/
def siegelLogDiagonalStrip (n : Nat) (a b : Real) (lower : Fin n -> Real) :
    Set (Fin (n + 1) -> Real) :=
  {x | And (Set.Icc a b (Finset.univ.sum x))
    (forall i : Fin n, lower i < x i.castSucc - x i.succ)}

theorem measurableSet_siegelLogDiagonalStrip (n : Nat) (a b : Real) (lower : Fin n -> Real) :
    MeasurableSet (siegelLogDiagonalStrip n a b lower) := by
  have hSum : Continuous (fun x : Fin (n + 1) -> Real => Finset.univ.sum x) :=
    continuous_finsetSum _ (fun i _ => continuous_apply i)
  have hGap : MeasurableSet {x : Fin (n + 1) -> Real |
      forall i : Fin n, lower i < x i.castSucc - x i.succ} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_Ioi.preimage
      (((continuous_apply i.castSucc).sub (continuous_apply i.succ)).measurable))
  exact (measurableSet_Icc.preimage hSum.measurable).inter hGap

section SiegelBoxVolume

variable (F : Type*) [NormedField F] [NormedSpace Real F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional Real F]

local notation "N" n => valuationUpperUnitriangularSubgroup F n
local instance siegelVolumeUnipotentMeasurableSpace (n : Nat) :
    MeasurableSpace (N n) := borel (N n)
local instance siegelVolumeUnipotentBorelSpace (n : Nat) :
    BorelSpace (N n) := BorelSpace.mk rfl

/-- A chart region with determinant log in a bounded interval, consecutive
gaps bounded below, and the conjugated upper entries in one compact set. -/
def archLogSiegelRegion (n : Nat) (a b : Real) (lower : Fin n -> Real) (B : Set F) :
    Set (Prod (Fin (n + 1) -> Real) (N (n + 1))) :=
  {p | And ((siegelLogDiagonalStrip n a b lower).Mem p.1)
    ((archUnipotentLogRatioBox F (n + 1) p.1 B).Mem p.2)}

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional Real F] in
theorem measurableSet_archLogSiegelRegion
    (n : Nat) (a b : Real) (lower : Fin n -> Real) (B : Set F) (hB : IsClosed B) :
    MeasurableSet (archLogSiegelRegion F n a b lower B) := by
  let _ : SecondCountableTopology (N (n + 1)) := archUnipotent_secondCountable F (n + 1)
  exact ((measurableSet_siegelLogDiagonalStrip n a b lower).preimage measurable_fst).inter
    (isClosed_archUnipotentLogRatioBox F (n + 1) B hB).measurableSet

set_option maxHeartbeats 750000 in
/-- The product of diagonal Lebesgue measure and unipotent Haar measure
assigns finite mass to the log Siegel region. -/
theorem measure_archLogSiegelRegion_lt_top
    (mu : Measure F) [SigmaFinite mu] [mu.IsAddHaarMeasure]
    (n : Nat) (a b : Real) (lower : Fin n -> Real) (B : Set F) (hB : IsCompact B) :
    ((volume : Measure (Fin (n + 1) -> Real)).prod
      (valuationUnitriangularProductMeasure F mu (n + 1)))
      (archLogSiegelRegion F n a b lower B) < Top.top := by
  classical
  let X := Fin (n + 1) -> Real
  let U := N (n + 1)
  let v := valuationUnitriangularProductMeasure F mu (n + 1)
  let S := siegelLogDiagonalStrip n a b lower
  let box (x : X) := archUnipotentLogRatioBox F (n + 1) x B
  let R := archLogSiegelRegion F n a b lower B
  let _ := sigmaFinite_valuationUnitriangularProductMeasure F mu (n + 1)
  have hR := measurableSet_archLogSiegelRegion F n a b lower B hB.isClosed
  have hS := measurableSet_siegelLogDiagonalStrip n a b lower
  have hSect (x : X) :
      Set.preimage (fun u : U => Prod.mk x u) R =
        if S.Mem x then box x else (EmptyCollection.emptyCollection : Set U) := by
    by_cases hx : S.Mem x
    . rw [if_pos hx]
      ext u
      exact Iff.intro And.right (fun hu => And.intro hx hu)
    . rw [if_neg hx]
      ext u
      exact Iff.intro (fun h => (hx h.1).elim) False.elim
  have hFubini : ((volume : Measure X).prod v) R =
      lintegral ((volume : Measure X).restrict S) (fun x => v (box x)) := by
    rw [Measure.prod_apply hR, <- lintegral_indicator hS]
    apply lintegral_congr
    intro x
    rw [hSect]
    by_cases hx : S.Mem x
    . rw [if_pos hx, Set.indicator_of_mem hx]
    . rw [if_neg hx, measure_empty, Set.indicator_of_notMem hx]
  let d := (Module.finrank Real F : Real)
  have hd : 0 < d := Nat.cast_pos.mpr Module.finrank_pos
  let rho (x : X) := Real.exp (-d * Finset.univ.sum (fun i : Fin n =>
    siegelRootMultiplicity n i * (x i.castSucc - x i.succ)))
  let c := (mu B) ^ Nat.choose (n + 1) 2
  have hFin : mu B < Top.top := hB.measure_lt_top
  have hc : c < Top.top := ENNReal.pow_lt_top hFin
  have hi : Integrable (fun x => rho x * c.toReal) ((volume : Measure X).restrict S) :=
    (integrableOn_siegelDiagonalStrip n d hd a b lower).mul_const _
  have hMass (x : X) : v (box x) = ENNReal.ofReal (rho x * c.toReal) := by
    change valuationUnitriangularProductMeasure F mu (n + 1)
      (archUnipotentLogRatioBox F (n + 1) x B) = _
    rw [measure_archUnipotentLogRatioBox F mu B hB, archUpperLogRatioSum_eq_weightedRootGaps,
      ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hc.ne]
  change ((volume : Measure X).prod v) R < Top.top
  rw [hFubini]
  simp_rw [hMass]
  exact hi.lintegral_lt_top

end SiegelBoxVolume

open MeasureTheory.Measure

section ArchimedeanHaarVolume

variable (F : Type*) [RCLike F] [ProperSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional Real F] (n : Nat)

local notation "X" => (Fin (n + 1) -> Real)
local notation "G" => Units (Matrix (Fin (n + 1)) (Fin (n + 1)) F)
local notation "N" => valuationUpperUnitriangularSubgroup F (n + 1)
local notation "P" => positiveDiagonalSubgroup F (n + 1)
local notation "T" => positiveUpperTriangularMatrixSubgroup F (n + 1)
local notation "K" => Matrix.unitaryGroup (Fin (n + 1)) F

local instance siegelHaarUnipotentMeasurableSpace : MeasurableSpace N := borel N
local instance siegelHaarUnipotentBorelSpace : BorelSpace N := BorelSpace.mk rfl

set_option maxHeartbeats 800000 in
/-- The image of the log Siegel region under the local Iwasawa chart,
with unrestricted unitary factor, has finite Haar volume. -/
theorem exists_exponentialIwasawaChart_siegelRegion_finiteHaarVolume
    [MeasurableSpace P] [BorelSpace P] [MeasurableSpace T] [BorelSpace T]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace K] [BorelSpace K]
    (mu : Measure G) [mu.IsHaarMeasure] [mu.InnerRegular]
    (lam : Measure F) [SigmaFinite lam] [lam.IsAddHaarMeasure]
    (muK : Measure K) [muK.IsHaarMeasure] [IsFiniteMeasure muK]
    (a b : Real) (lower : Fin n -> Real) (B : Set F) (hB : IsCompact B) :
    exists E : Homeomorph (Prod (Prod X N) K) G,
      And (forall p, (E p).val =
        (Matrix.diagonal (fun i : Fin (n + 1) => (Real.exp (p.1.1 i) : F)) * p.1.2.val.val.val) *
          (Inv.inv p.2).val)
        (And (MeasurableSet (Set.image E (Set.prod (archLogSiegelRegion F n a b lower B) Set.univ)))
          (mu (Set.image E (Set.prod (archLogSiegelRegion F n a b lower B) Set.univ)) < Top.top)) := by
  let muN := valuationUnitriangularProductMeasure F lam (n + 1)
  let _ : SecondCountableTopology N := archUnipotent_secondCountable F (n + 1)
  let _ : SigmaFinite muN := sigmaFinite_valuationUnitriangularProductMeasure F lam (n + 1)
  let _ : muN.IsHaarMeasure := isHaarMeasure_archUnipotentProduct F lam (n + 1)
  choose E he hScale using exists_pos_smul_map_exponentialIwasawaHaar F (n + 1) mu muN muK
  choose c hc using hScale
  let muX := (volume : Measure X).prod muN
  let R := archLogSiegelRegion F n a b lower B
  let D := Set.prod R (Set.univ : Set K)
  have hR : MeasurableSet R := measurableSet_archLogSiegelRegion F n a b lower B hB.isClosed
  have hD : MeasurableSet D := hR.prod MeasurableSet.univ
  have hIm : MeasurableSet (Set.image E D) := E.measurableEmbedding.measurableSet_image.mpr hD
  refine Exists.intro E (And.intro he (And.intro hIm ?_))
  have hProd : (muX.prod muK) D = muX R * muK Set.univ := Measure.prod_prod R Set.univ
  have hFin : muX R < Top.top := measure_archLogSiegelRegion_lt_top F lam n a b lower B hB
  change mu (Set.image E D) < Top.top
  rw [hc.2, Measure.smul_apply, Measure.map_apply E.continuous.measurable hIm,
    Set.preimage_image_eq _ E.injective, hProd]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top hFin (measure_lt_top _ _))

end ArchimedeanHaarVolume

end Robin1984.GRH
