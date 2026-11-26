import Robin1984.GRH.GodementJacquetThetaAnalyticContinuation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and linearity of absolutely integrable theta sums.
- Formalization note: Transfers the invertible theta reflection and Mellin continuation from Schwartz rectangles to finite sums of rectangles and their actual self-dual Fourier transforms.
- PROVENANCE-END
-/

/-!
# Theta continuation for finite sums of Schwartz rectangles

The invertible theta integral for a finite sum is the sum of the integrals
of its parts. The self-dual Fourier transform has the same linearity.
These identities transfer the theta reflection to the sum. Summing the
termwise decay bounds then gives an entire logarithmic Mellin transform
and the reflection at `1 - s`.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField

namespace Robin1984.GRH

section

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "M" => Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K)
local notation "P" => Matrix (Fin n) (Fin n) K
local notation "G" => MonoidHom.ker (adelicDeterminantLogNorm K n)

private theorem integral_tsum_theta_finsetSum
    [MeasurableSpace G] {I J : Type*} (S : Finset I)
    (p : J -> P) (nu : Measure G) (Phi : I -> M -> Complex)
    (c b : G -> Complex) (t : Real)
    (hSum : forall i, Membership.mem S i -> forall A B : G, Summable
      (fun j => godementJacquetDoubleThetaTerm K n (Phi i) t A B (p j)))
    (hInt : forall i, Membership.mem S i -> Integrable (fun x : Prod G G =>
      tsum (fun j => godementJacquetDoubleThetaTerm K n (Phi i) t x.1 x.2 (p j)) *
        (c x.1 * b x.2)) (nu.prod nu)) :
    integral (nu.prod nu) (fun x : Prod G G =>
      tsum (fun j => godementJacquetDoubleThetaTerm K n
        (fun X => S.sum (fun i => Phi i X)) t x.1 x.2 (p j)) * (c x.1 * b x.2)) =
    S.sum (fun i => integral (nu.prod nu) (fun x : Prod G G =>
      tsum (fun j => godementJacquetDoubleThetaTerm K n (Phi i) t x.1 x.2 (p j)) *
        (c x.1 * b x.2))) := by
  let F (i : I) (x : Prod G G) (j : J) :=
    godementJacquetDoubleThetaTerm K n (Phi i) t x.1 x.2 (p j)
  calc
    _ = integral (nu.prod nu) (fun x : Prod G G =>
        S.sum (fun i => tsum (F i x) * (c x.1 * b x.2))) := by
      congr 1
      funext x
      change tsum (fun j => S.sum (fun i => F i x j)) * (c x.1 * b x.2) = _
      rw [Summable.tsum_finsetSum (fun i hi => hSum i hi x.1 x.2), Finset.sum_mul]
    _ = _ := integral_finsetSum S hInt

/-- Finite sums of tests commute with the invertible theta integral when each
rational matrix series is summable and each quotient integrand is integrable. -/
theorem godementJacquetInvertibleDoubleThetaIntegral_finsetSum
    [MeasurableSpace G] {I : Type*} (S : Finset I)
    (nu : Measure G) (Phi : I -> M -> Complex) (c b : G -> Complex) (t : Real)
    (hSum : forall i, Membership.mem S i -> forall A B : G,
      Summable (godementJacquetDoubleThetaTerm K n (Phi i) t A B))
    (hInt : forall i, Membership.mem S i -> Integrable (fun x : Prod G G =>
      godementJacquetInvertibleDoubleThetaSeries K n (Phi i) t x.1 x.2 *
        (c x.1 * b x.2)) (nu.prod nu)) :
    godementJacquetInvertibleDoubleThetaIntegral K n nu
      (fun X => S.sum (fun i => Phi i X)) c b t =
    S.sum (fun i => godementJacquetInvertibleDoubleThetaIntegral K n nu (Phi i) c b t) :=
  integral_tsum_theta_finsetSum K n S
    (fun j : Matrix.GeneralLinearGroup (Fin n) K => j.val) nu Phi c b t
    (fun i hi A B => (hSum i hi A B).comp_injective Units.val_injective) hInt

open scoped Classical RealInnerProductSpace FourierTransform

private abbrev ThetaPacketIndex (k : Nat) := Prod (Fin k) (Fin k)

set_option maxHeartbeats 1200000 in
/-- Termwise cancellation and integrability give the theta reflection for a
finite sum of Schwartz rectangles and its self-dual Fourier transform. -/
theorem godementJacquetInvertibleDoubleThetaIntegral_reflection_finsetRectangles
    [MeasurableSpace G]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (hn : 0 < n) {I : Type*} (S : Finset I)
    (nu : Measure G) [SFinite nu]
    (a : I -> ThetaPacketIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : I -> SchwartzMap (PiLp 2 (fun _ : ThetaPacketIndex n =>
      DedekindZeta.Theta.minkowskiSpace K)) Complex)
    (c b : G -> Complex) (t : Real) :
    let R (i : I) := godementJacquetMatrixRectangle K (a i) d (f i)
    let Q (i : I) := godementJacquetSelfDualMatrixFourier K (R i)
    let Phi (X : M) := S.sum (fun i => R i X)
    (forall i, Membership.mem S i ->
      godementJacquetDoubleThetaIntegral K n nu (R i) c b t =
        godementJacquetInvertibleDoubleThetaIntegral K n nu (R i) c b t) ->
    (forall i, Membership.mem S i ->
      godementJacquetDoubleThetaIntegral K n nu (Q i) b c (-t) =
        godementJacquetInvertibleDoubleThetaIntegral K n nu (Q i) b c (-t)) ->
    (forall i, Membership.mem S i -> Integrable (fun x : Prod G G =>
      godementJacquetInvertibleDoubleThetaSeries K n (R i) t x.1 x.2 *
        (c x.1 * b x.2)) (nu.prod nu)) ->
    (forall i, Membership.mem S i -> Integrable (fun x : Prod G G =>
      godementJacquetInvertibleDoubleThetaSeries K n (Q i) (-t) x.1 x.2 *
        (b x.1 * c x.2)) (nu.prod nu)) ->
    godementJacquetInvertibleDoubleThetaIntegral K n nu Phi c b t =
      ((Real.exp (-((n : Real) * t)) : Real) : Complex) *
        godementJacquetInvertibleDoubleThetaIntegral K n nu
          (godementJacquetSelfDualMatrixFourier K Phi) b c (-t) := by
  intro R Q Phi hP hQ hIP hIQ
  have hFourier : godementJacquetSelfDualMatrixFourier K Phi =
      (fun Y => S.sum (fun i => Q i Y)) := by
    funext Y
    exact godementJacquetSelfDualMatrixFourier_finsetSum K S R
      (fun i _ => integrable_godementJacquetMatrixRectangle_fromVec K (a i) d hd (f i)) Y
  have hSP (i : I) (_ : Membership.mem S i) (A B : G) :
      Summable (godementJacquetDoubleThetaTerm K n (R i) t A B) :=
    (godementJacquetMatrixRectangle_thetaReflection K n hn
      (Multiplicative.ofAdd t) A B (a i) d hd (f i)).1
  have hSQ (i : I) (_ : Membership.mem S i) (A B : G) :
      Summable (godementJacquetDoubleThetaTerm K n (Q i) (-t) A B) :=
    (godementJacquetMatrixRectangle_thetaReflection K n hn
      (Multiplicative.ofAdd t) B A (a i) d hd (f i)).2.1
  change godementJacquetInvertibleDoubleThetaIntegral K n nu
    (fun X => S.sum (fun i => R i X)) c b t =
      _ * godementJacquetInvertibleDoubleThetaIntegral K n nu
        (godementJacquetSelfDualMatrixFourier K Phi) b c (-t)
  rw [hFourier, godementJacquetInvertibleDoubleThetaIntegral_finsetSum K n S nu
    R c b t hSP hIP, godementJacquetInvertibleDoubleThetaIntegral_finsetSum K n S nu
    Q b c (-t) hSQ hIQ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [<- hP i hi, <- hQ i hi]
  exact godementJacquetDoubleThetaIntegral_reflection K n nu hn t (a i) d hd (f i) c b

set_option maxHeartbeats 1200000 in
/-- The Mellin transform of the invertible theta integral for a finite sum of
Schwartz rectangles is entire and reflects to the transform for its actual
self-dual Fourier transform. Cancellation, quotient integrability, and
positive-time exponential decay are required for each summand. -/
theorem godementJacquetInvertibleThetaMellin_entire_and_reflection_finsetRectangles
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (hn : 0 < n) {I : Type*} (S : Finset I)
    (nu : Measure G) [SFinite nu]
    (a : I -> ThetaPacketIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : I -> SchwartzMap (PiLp 2 (fun _ : ThetaPacketIndex n =>
      DedekindZeta.Theta.minkowskiSpace K)) Complex)
    (c b : G -> Complex) (hc : Measurable c) (hb : Measurable b) :
    let R (i : I) := godementJacquetMatrixRectangle K (a i) d (f i)
    let Q (i : I) := godementJacquetSelfDualMatrixFourier K (R i)
    let Phi (X : M) := S.sum (fun i => R i X)
    let F (i : I) (t : Real) := godementJacquetInvertibleDoubleThetaIntegral K n nu (R i) c b t
    let H (i : I) (t : Real) := godementJacquetInvertibleDoubleThetaIntegral K n nu (Q i) b c t
    let Ftotal (t : Real) := godementJacquetInvertibleDoubleThetaIntegral K n nu Phi c b t
    let Htotal (t : Real) := godementJacquetInvertibleDoubleThetaIntegral K n nu
      (godementJacquetSelfDualMatrixFourier K Phi) b c t
    (forall i, Membership.mem S i -> forall t : Real,
      godementJacquetDoubleThetaIntegral K n nu (R i) c b t = F i t) ->
    (forall i, Membership.mem S i -> forall t : Real,
      godementJacquetDoubleThetaIntegral K n nu (Q i) b c t = H i t) ->
    (forall i, Membership.mem S i -> forall t : Real, Integrable (fun x : Prod G G =>
      godementJacquetInvertibleDoubleThetaSeries K n (R i) t x.1 x.2 *
        (c x.1 * b x.2)) (nu.prod nu)) ->
    (forall i, Membership.mem S i -> forall t : Real, Integrable (fun x : Prod G G =>
      godementJacquetInvertibleDoubleThetaSeries K n (Q i) t x.1 x.2 *
        (b x.1 * c x.2)) (nu.prod nu)) ->
    (forall i (beta : Real), 0 < beta -> exists C : Real, forall t : Real, 0 <= t ->
      norm (F i t) <= C * Real.exp (-beta * t)) ->
    (forall i (beta : Real), 0 < beta -> exists C : Real, forall t : Real, 0 <= t ->
      norm (H i t) <= C * Real.exp (-beta * t)) ->
    And (Differentiable Complex (godementJacquetLogMellin n Ftotal))
      (forall s : Complex, godementJacquetLogMellin n Ftotal s =
        godementJacquetLogMellin n Htotal (1 - s)) := by
  intro R Q Phi F H Ftotal Htotal hP hQ hIP hIQ hDecayF hDecayH
  have hSP (i : I) (t : Real) (A B : G) :
      Summable (godementJacquetDoubleThetaTerm K n (R i) t A B) :=
    (godementJacquetMatrixRectangle_thetaReflection K n hn
      (Multiplicative.ofAdd t) A B (a i) d hd (f i)).1
  have hSQ (i : I) (t : Real) (A B : G) :
      Summable (godementJacquetDoubleThetaTerm K n (Q i) t A B) := by
    have hs := (godementJacquetMatrixRectangle_thetaReflection K n hn
      (Multiplicative.ofAdd (-t)) B A (a i) d hd (f i)).2.1
    change Summable (godementJacquetDoubleThetaTerm K n (Q i) (-(-t)) A B) at hs
    rwa [neg_neg] at hs
  have hFourier : godementJacquetSelfDualMatrixFourier K Phi =
      (fun Y => S.sum (fun i => Q i Y)) := by
    funext Y
    exact godementJacquetSelfDualMatrixFourier_finsetSum K S R
      (fun i _ => integrable_godementJacquetMatrixRectangle_fromVec K (a i) d hd (f i)) Y
  have hFtotal : Ftotal = (fun t => S.sum (fun i => F i t)) := by
    funext t
    exact godementJacquetInvertibleDoubleThetaIntegral_finsetSum K n S nu
      R c b t (fun i _ => hSP i t) (fun i hi => hIP i hi t)
  have hHtotal : Htotal = (fun t => S.sum (fun i => H i t)) := by
    funext t
    change (godementJacquetInvertibleDoubleThetaIntegral K n nu
      (godementJacquetSelfDualMatrixFourier K Phi) b c t) = _
    rw [hFourier]
    exact godementJacquetInvertibleDoubleThetaIntegral_finsetSum K n S nu
      Q b c t (fun i _ => hSQ i t) (fun i hi => hIQ i hi t)
  let Gamma := Matrix.GeneralLinearGroup (Fin n) K
  let p (g : Gamma) : P := g.val
  have hp : Function.Injective p := Units.val_injective
  let : Countable K := (Module.finBasis Rat K).equivFun.injective.countable
  let : Countable P := inferInstanceAs (Countable (Fin n -> Fin n -> K))
  let : Countable Gamma := hp.countable
  have hMF : Measurable Ftotal := by
    rw [hFtotal]
    apply Finset.measurable_fun_sum S
    intro i _
    exact measurable_godementJacquetThetaCurve K n Gamma nu p (R i)
      (continuous_godementJacquetMatrixRectangle K (n := n) (a i) d hd (f i)).measurable
      c b hc hb (fun t A B => (hSP i t A B).comp_injective hp)
  have hMH : Measurable Htotal := by
    rw [hHtotal]
    apply Finset.measurable_fun_sum S
    intro i _
    exact measurable_godementJacquetThetaCurve K n Gamma nu p (Q i)
      (continuous_godementJacquetSelfDualMatrixFourier_rectangle K n (a i) d hd (f i)).measurable
      b c hb hc (fun t A B => (hSQ i t A B).comp_injective hp)
  have hRef (t : Real) : Ftotal t = ((Real.exp (-((n : Real) * t)) : Real) : Complex) *
      Htotal (-t) :=
    godementJacquetInvertibleDoubleThetaIntegral_reflection_finsetRectangles
      K n hn S nu a d hd f c b t (fun i hi => hP i hi t) (fun i hi => hQ i hi (-t))
      (fun i hi => hIP i hi t) (fun i hi => hIQ i hi (-t))
  have hDecayAux (U : I -> Real -> Complex) (beta : Real)
      (h : forall i, exists C : Real, forall t : Real, 0 <= t ->
        norm (U i t) <= C * Real.exp (-beta * t)) :
      exists C : Real, forall t : Real, 0 <= t ->
        norm (S.sum (fun i => U i t)) <= C * Real.exp (-beta * t) := by
    choose C hC using h
    refine Exists.intro (S.sum C) (fun t ht => ?_)
    rw [Finset.sum_mul]
    exact (norm_sum_le S (fun i => U i t)).trans
      (Finset.sum_le_sum (fun i _ => hC i t ht))
  apply godementJacquetLogMellin_entire_and_reflection_of_decay n Ftotal Htotal hMF hMH hRef
  . intro beta hbeta
    rw [hFtotal]
    exact hDecayAux F beta (fun i => hDecayF i beta hbeta)
  . intro beta hbeta
    rw [hHtotal]
    exact hDecayAux H beta (fun i => hDecayH i beta hbeta)

end

end Robin1984.GRH
