import Robin1984.GRH.GodementJacquetFullThetaGrowth
import Robin1984.GRH.GodementJacquetThetaAnalyticContinuation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and absolute convergence for cuspidal cancellation.
- Formalization note: Proves cancellation of the singular theta terms for a Schwartz rectangle and its self-dual Fourier transform under the explicit weighted L1 hypotheses.
- PROVENANCE-END
-/

/-!
# Cuspidal cancellation with weighted integrability

A product bound for the absolute theta sum gives both the Fubini bound
in the first quotient variable and the two product-integrability bounds.
The same polynomial quotient weights apply to a Schwartz rectangle and
to the finite rectangle expansion of its self-dual Fourier transform.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

private abbrev ThetaWeightedAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K
private abbrev ThetaWeightedGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker
private abbrev ThetaWeightedMatrix (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  Matrix (Fin n) (Fin n) (ThetaWeightedAdeles K)

private theorem lintegral_enorm_tsum_mul_lt_top_of_thetaProductMajorant
    {G I : Type*} [MeasurableSpace G] (nu : Measure G)
    (T : I -> G -> Complex) (c : G -> Complex) (H : G -> Real)
    (hH : forall A, 0 <= H A) (k : Real) (hk : 0 <= k)
    (hcH : Integrable (fun A => norm (c A) * H A) nu)
    (hT : forall A, tsum (fun i => enorm (T i A)) <= ENNReal.ofReal (k * H A)) :
    lintegral nu (fun A => tsum (fun i => enorm (T i A * c A))) < (Top.top : ENNReal) := by
  let u (A : G) := norm (c A) * H A
  have hu (A : G) : 0 <= u A := mul_nonneg (norm_nonneg _) (hH A)
  calc
    _ <= lintegral nu (fun A => enorm (u A) * ENNReal.ofReal k) := by
      apply lintegral_mono
      intro A
      simp_rw [enorm_mul, ENNReal.tsum_mul_right]
      refine (mul_le_mul_left (hT A) _).trans_eq ?_
      rw [<- ofReal_norm (c A), <- ofReal_norm (u A), Real.norm_of_nonneg (hu A)]
      simp only [u, ENNReal.ofReal_mul hk, ENNReal.ofReal_mul (norm_nonneg (c A))]
      ac_rfl
    _ = (lintegral nu (fun A => enorm (u A))) * ENNReal.ofReal k :=
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ < _ := ENNReal.mul_lt_top hcH.hasFiniteIntegral ENNReal.ofReal_lt_top

private theorem integrable_mul_of_thetaProductMajorant
    {G : Type*} [MeasurableSpace G] (nu : Measure G)
    (c b : G -> Complex) (hc : Measurable c) (hb : Measurable b)
    (C : Real) (hC : 0 <= C) (H J : G -> Real)
    (hH : forall A, 0 <= H A) (hJ : forall B, 0 <= J B)
    (hcH : Integrable (fun A => norm (c A) * H A) nu)
    (hbJ : Integrable (fun B => norm (b B) * J B) nu)
    (F : Prod G G -> Complex) (hF : Measurable F)
    (hBound : forall q, enorm (F q) <= ENNReal.ofReal (C * H q.1 * J q.2)) :
    Integrable (fun q : Prod G G => F q * (c q.1 * b q.2)) (nu.prod nu) := by
  let u (A : G) := norm (c A) * H A
  let v (B : G) := norm (b B) * J B
  let W (q : Prod G G) := C * (u q.1 * v q.2)
  have hu (A : G) : 0 <= u A := mul_nonneg (norm_nonneg _) (hH A)
  have hv (B : G) : 0 <= v B := mul_nonneg (norm_nonneg _) (hJ B)
  have hW (q : Prod G G) : 0 <= W q := mul_nonneg hC (mul_nonneg (hu q.1) (hv q.2))
  have hIntW : Integrable W (nu.prod nu) := (hcH.mul_prod hbJ).const_mul C
  have hMeasCS : Measurable (fun q : Prod G G => c q.1 * b q.2) :=
    (hc.comp measurable_fst).mul (hb.comp measurable_snd)
  refine hIntW.mono_enorm (hF.mul hMeasCS).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [enorm_mul]
  refine (mul_le_mul_left (hBound q) _).trans_eq ?_
  rw [enorm_mul, <- ofReal_norm (c q.1), <- ofReal_norm (b q.2),
    <- ofReal_norm (W q), Real.norm_of_nonneg (hW q)]
  simp only [W, ENNReal.ofReal_mul (mul_nonneg hC (hH q.1)), ENNReal.ofReal_mul hC,
    ENNReal.ofReal_mul (hu q.1), u, v, ENNReal.ofReal_mul (norm_nonneg (c q.1)),
    ENNReal.ofReal_mul (norm_nonneg (b q.2))]
  ac_rfl

private theorem measurable_thetaTimeSection {G : Type*} [MeasurableSpace G]
    (F : Prod Real (Prod G G) -> Complex) (hF : Measurable F) (t : Real) :
    Measurable (fun q : Prod G G => F (Prod.mk t q)) :=
  hF.comp (measurable_const.prodMk measurable_id)

set_option maxHeartbeats 1500000 in
/-- A product bound on the absolute rational theta series and integrability
of the two weighted cusp functions give all the summability and integrability
conditions of singular cancellation. -/
theorem godementJacquetDoubleThetaIntegral_eq_invertible_of_productMajorant
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (ThetaWeightedGroup K n)] [BorelSpace (ThetaWeightedGroup K n)]
    [MeasurableSpace (ThetaWeightedMatrix K n)] [BorelSpace (ThetaWeightedMatrix K n)]
    (mu : Measure (ThetaWeightedGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (D : Set (ThetaWeightedGroup K n)) (hD : MeasurableSet D)
    (hUnique : forall A : ThetaWeightedGroup K n, ExistsUnique
      (fun gamma : (adelicPrincipalDeterminantOne K n).range => Membership.mem D (gamma.val * A)))
    (t : Real) (Phi : ThetaWeightedMatrix K n -> Complex) (hPhi : Measurable Phi)
    (c b : ThetaWeightedGroup K n -> Complex) (hc : Measurable c) (hb : Measurable b)
    (hInvariant : forall gamma : (adelicPrincipalDeterminantOne K n).range, forall A,
      c (gamma.val * A) = c A)
    (hPeriods : HasGodementJacquetVanishingUnipotentPeriods c)
    (hMean : integral (mu.restrict D) c = 0)
    (C : Real -> Real) (hC : 0 <= C t) (H J : ThetaWeightedGroup K n -> Real)
    (hH : forall A, 1 <= H A) (hJ : forall B, 0 <= J B)
    (hcH : IntegrableOn (fun A => norm (c A) * H A) D mu)
    (hbJ : IntegrableOn (fun B => norm (b B) * J B) D mu)
    (hMajorant : forall s A B,
      tsum (fun P => enorm (godementJacquetDoubleThetaTerm K n Phi s A B P)) <=
        ENNReal.ofReal (C s * H A * J B)) :
    godementJacquetDoubleThetaIntegral K n (mu.restrict D) Phi c b t =
      godementJacquetInvertibleDoubleThetaIntegral K n (mu.restrict D) Phi c b t := by
  let G := ThetaWeightedGroup K n
  let R := Matrix (Fin n) (Fin n) K
  let V := Matrix.GeneralLinearGroup (Fin n) K
  let nu := mu.restrict D
  let u (A : G) : Real := norm (c A) * H A
  let T (s : Real) (P : R) (q : Prod G G) :=
    godementJacquetDoubleThetaTerm K n Phi s q.1 q.2 P
  have hValInjective : Function.Injective (Units.val : V -> R) := Units.val_injective
  have hu (A : G) : 0 <= u A :=
    mul_nonneg (norm_nonneg _) (zero_le_one.trans (hH A))
  have hcInt : IntegrableOn c D mu := by
    refine (show Integrable u nu from hcH).mono hc.aestronglyMeasurable (Filter.Eventually.of_forall fun A => ?_)
    change norm (c A) <= norm (u A)
    rw [Real.norm_of_nonneg (hu A)]
    exact le_mul_of_one_le_right (norm_nonneg _) (hH A)
  have hFullBound (s : Real) (q : Prod G G) : tsum (fun P => enorm (T s P q)) <=
      ENNReal.ofReal (C s * H q.1 * J q.2) := hMajorant s q.1 q.2
  have hInvBound (s : Real) (q : Prod G G) : tsum (fun P : V => enorm (T s P.val q)) <=
      ENNReal.ofReal (C s * H q.1 * J q.2) :=
    (ENNReal.tsum_comp_le_tsum_of_injective hValInjective
      (fun P => enorm (T s P q))).trans (hFullBound s q)
  have hS (s : Real) (q : Prod G G) : Summable (fun P => T s P q) :=
    (tsum_enorm_ne_top_iff_summable_norm.mp
      (ne_of_lt ((hFullBound s q).trans_lt ENNReal.ofReal_lt_top))).of_norm
  have hSI (s : Real) (q : Prod G G) : Summable (fun P : V => T s P.val q) :=
    (tsum_enorm_ne_top_iff_summable_norm.mp
      (ne_of_lt ((hInvBound s q).trans_lt ENNReal.ofReal_lt_top))).of_norm
  have hH0 (A : G) : 0 <= H A := zero_le_one.trans (hH A)
  have hAbs (B : G) : lintegral nu (fun A =>
      tsum (fun P => enorm (T t P (Prod.mk A B) * c A))) < (Top.top : ENNReal) := by
    refine lintegral_enorm_tsum_mul_lt_top_of_thetaProductMajorant nu
      (fun P A => T t P (Prod.mk A B)) c H hH0 (C t * J B) (mul_nonneg hC (hJ B)) hcH
      (fun A => ?_)
    exact (hFullBound t (Prod.mk A B)).trans_eq
      (congrArg ENNReal.ofReal (mul_right_comm (C t) (H A) (J B)))
  let : Countable K := (Module.finBasis Rat K).equivFun.injective.countable
  let : Countable R := inferInstanceAs (Countable (Fin n -> Fin n -> K))
  let : Countable V := hValInjective.countable
  let X := Prod Real (Prod G G)
  let F (p : X) := tsum (fun P : R => T p.1 P p.2)
  let I (p : X) := tsum (fun P : V => T p.1 P.val p.2)
  have hF : Measurable F := by
    exact measurable_godementJacquetThetaSeries K n R (fun P : R => P) Phi hPhi
      (fun s A B => hS s (Prod.mk A B))
  have hI : Measurable I := by
    exact measurable_godementJacquetThetaSeries K n V (Units.val : V -> R) Phi hPhi
      (fun s A B => hSI s (Prod.mk A B))
  have hMeasFull : Measurable (fun q : Prod G G => tsum (fun P : R => T t P q)) := by
    change Measurable (fun q : Prod G G => F (Prod.mk t q))
    exact measurable_thetaTimeSection F hF t
  have hMeasInv : Measurable (fun q : Prod G G => tsum (fun P : V => T t P.val q)) := by
    change Measurable (fun q : Prod G G => I (Prod.mk t q))
    exact measurable_thetaTimeSection I hI t
  have hFullInt : Integrable (fun q : Prod G G =>
      godementJacquetDoubleThetaSeries K n Phi t q.1 q.2 * (c q.1 * b q.2)) (nu.prod nu) := by
    change Integrable (fun q : Prod G G => (tsum (fun P : R => T t P q)) * (c q.1 * b q.2)) _
    exact integrable_mul_of_thetaProductMajorant nu c b hc hb (C t) hC H J hH0 hJ hcH hbJ
      _ hMeasFull (fun q => (enorm_tsum_le_tsum_enorm (f := fun P : R => T t P q)).trans (hFullBound t q))
  have hInvInt : Integrable (fun q : Prod G G =>
      godementJacquetInvertibleDoubleThetaSeries K n Phi t q.1 q.2 * (c q.1 * b q.2)) (nu.prod nu) := by
    change Integrable (fun q : Prod G G => (tsum (fun P : V => T t P.val q)) * (c q.1 * b q.2)) _
    exact integrable_mul_of_thetaProductMajorant nu c b hc hb (C t) hC H J hH0 hJ hcH hbJ
      _ hMeasInv (fun q => (enorm_tsum_le_tsum_enorm (f := fun P : V => T t P.val q)).trans (hInvBound t q))
  exact godementJacquetDoubleThetaIntegral_eq_invertible K n mu D hD hUnique hn t
    Phi hPhi c b hc hInvariant hPeriods hcInt hMean (fun A B => hS t (Prod.mk A B))
    (Filter.Eventually.of_forall hAbs) hFullInt hInvInt

private abbrev RectangleWeightFinite (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K
private abbrev RectangleWeightDenom (K : Type*) [Field K] [NumberField K] :=
  Subtype (fun b : RingOfIntegers K => Not (b = 0))
private abbrev RectangleWeightIndex (n : Nat) := Prod (Fin n) (Fin n)

set_option maxHeartbeats 800000 in
/-- The absolute theta sum of a Schwartz rectangle has a real product
majorant. The powers of the left and right dilation norms depend only
on the denominator functions, so they work for every test rectangle. -/
theorem godementJacquetDoubleThetaTerm_productMajorant_rectangle
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (a : RectangleWeightIndex n -> RectangleWeightFinite K)
    (d : RingOfIntegers K)
    (f : SchwartzMap (PiLp 2 (fun _ : RectangleWeightIndex n => DedekindZeta.Theta.minkowskiSpace K)) Complex)
    (m : Nat) (hm : Module.finrank Real
      (PiLp 2 (fun _ : RectangleWeightIndex n => DedekindZeta.Theta.minkowskiSpace K)) < m)
    (dLeft dRight : ThetaWeightedGroup K n -> RectangleWeightDenom K)
    (hLeft : forall A i j, Membership.mem (heckeIntegralFiniteAdeles (K := K))
      ((algebraMap K (RectangleWeightFinite K)).comp (algebraMap (RingOfIntegers K) K)
        (dLeft A).val * (A.val.val i j).2))
    (hRight : forall B i j, Membership.mem (heckeIntegralFiniteAdeles (K := K))
      ((algebraMap K (RectangleWeightFinite K)).comp (algebraMap (RingOfIntegers K) K)
        (dRight B).val * (B.val.inv i j).2)) :
    let s (b : RectangleWeightDenom K) :=
      godementJacquetFullTheta_principalScalarMatrixUnit K n b.val b.property
    let H := godementJacquetFullTheta_archimedeanHeight K n
    let wLeft (A : ThetaWeightedGroup K n) := H (s (dLeft A) * A.val) 1 ^ m
    let wRight (B : ThetaWeightedGroup K n) := H 1 (Inv.inv B.val * s (dRight B)) ^ m
    let Phi := godementJacquetMatrixRectangle K a d f
    Exists (fun C : Real -> Real => And (forall t, 0 <= C t) (forall t A B,
      tsum (fun P => enorm (godementJacquetDoubleThetaTerm K n Phi t A B P)) <=
        ENNReal.ofReal (C t * wLeft A * wRight B))) := by
  let s (b : RectangleWeightDenom K) :=
    godementJacquetFullTheta_principalScalarMatrixUnit K n b.val b.property
  let H := godementJacquetFullTheta_archimedeanHeight K n
  let G := ThetaWeightedGroup K n
  let L (A : G) := H (s (dLeft A) * A.val) 1
  let R (B : G) := H 1 (Inv.inv B.val * s (dRight B))
  let z (t : Real) := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  choose C hC using tsum_ofReal_norm_godementJacquetFullTheta_le_of_finiteDenominators K n a d f m hm
  choose dX hdX using hC.2
  let T (t : Real) := H (s dX * Inv.inv (z t)) 1
  have hH0 (U V : AdelicGeneralLinearGroup K n) : 0 <= H U V :=
    zero_le_one.trans (le_max_left _ _)
  let ct (t : Real) := T t ^ m * C.toReal
  refine Exists.intro ct (And.intro (fun t => mul_nonneg (pow_nonneg (hH0 _ _) _) ENNReal.toReal_nonneg) ?_)
  intro t A B
  calc
    _ <= ENNReal.ofReal ((T t * L A * R B) ^ m) * C := by
      simpa only [godementJacquetDoubleThetaTerm, ofReal_norm] using
        hdX t A B (dLeft A) (dRight B) (hLeft A) (hRight B)
    _ = ENNReal.ofReal (ct t * L A ^ m * R B ^ m) := by
      have hp : 0 <= (T t * L A * R B) ^ m :=
        pow_nonneg (mul_nonneg (mul_nonneg (hH0 _ _) (hH0 _ _)) (hH0 _ _)) _
      rw [<- ENNReal.ofReal_toReal hC.1.ne, <- ENNReal.ofReal_mul hp]
      dsimp only [ct]
      simp only [mul_pow]
      congr 1
      ac_rfl

set_option maxHeartbeats 1000000 in
/-- The same quotient weights bound any finite sum of Schwartz rectangles.
Only the scalar function of the logarithmic determinant is added. -/
theorem godementJacquetDoubleThetaTerm_productMajorant_finset_rectangles
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (I : Type*) (S : Finset I)
    (a : I -> RectangleWeightIndex n -> RectangleWeightFinite K)
    (d : RingOfIntegers K)
    (f : I -> SchwartzMap (PiLp 2 (fun _ : RectangleWeightIndex n => DedekindZeta.Theta.minkowskiSpace K)) Complex)
    (m : Nat) (hm : Module.finrank Real
      (PiLp 2 (fun _ : RectangleWeightIndex n => DedekindZeta.Theta.minkowskiSpace K)) < m)
    (dLeft dRight : ThetaWeightedGroup K n -> RectangleWeightDenom K)
    (hLeft : forall A i j, Membership.mem (heckeIntegralFiniteAdeles (K := K))
      ((algebraMap K (RectangleWeightFinite K)).comp (algebraMap (RingOfIntegers K) K)
        (dLeft A).val * (A.val.val i j).2))
    (hRight : forall B i j, Membership.mem (heckeIntegralFiniteAdeles (K := K))
      ((algebraMap K (RectangleWeightFinite K)).comp (algebraMap (RingOfIntegers K) K)
        (dRight B).val * (B.val.inv i j).2)) :
    let s (b : RectangleWeightDenom K) :=
      godementJacquetFullTheta_principalScalarMatrixUnit K n b.val b.property
    let H := godementJacquetFullTheta_archimedeanHeight K n
    let wLeft (A : ThetaWeightedGroup K n) := H (s (dLeft A) * A.val) 1 ^ m
    let wRight (B : ThetaWeightedGroup K n) := H 1 (Inv.inv B.val * s (dRight B)) ^ m
    let Phi (X : ThetaWeightedMatrix K n) :=
      S.sum (fun i => godementJacquetMatrixRectangle K (a i) d (f i) X)
    Exists (fun C : Real -> Real => And (forall t, 0 <= C t) (forall t A B,
      tsum (fun P => enorm (godementJacquetDoubleThetaTerm K n Phi t A B P)) <=
        ENNReal.ofReal (C t * wLeft A * wRight B))) := by
  let s (b : RectangleWeightDenom K) :=
    godementJacquetFullTheta_principalScalarMatrixUnit K n b.val b.property
  let H := godementJacquetFullTheta_archimedeanHeight K n
  let L (A : ThetaWeightedGroup K n) := H (s (dLeft A) * A.val) 1 ^ m
  let R (B : ThetaWeightedGroup K n) := H 1 (Inv.inv B.val * s (dRight B)) ^ m
  let Mat := Matrix (Fin n) (Fin n) K
  choose C hC using fun i =>
    godementJacquetDoubleThetaTerm_productMajorant_rectangle K n (a i) d (f i) m hm
      dLeft dRight hLeft hRight
  let ct (t : Real) := S.sum (fun i => C i t)
  refine Exists.intro ct (And.intro (fun t => Finset.sum_nonneg (fun i _ => (hC i).1 t)) ?_)
  intro t A B
  let F (i : I) (P : Mat) :=
    godementJacquetDoubleThetaTerm K n (godementJacquetMatrixRectangle K (a i) d (f i)) t A B P
  let G (i : I) (P : Mat) := enorm (F i P)
  have hFub (U : Finset I) : tsum (fun P => U.sum (fun i => G i P)) =
      U.sum (fun i => tsum (G i)) := by
    induction U using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, tsum_zero]
    | insert j U hj ih =>
      simp only [Finset.sum_insert hj, ENNReal.tsum_add, ih]
  have hL : 0 <= L A := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hR : 0 <= R B := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  calc
    _ <= tsum (fun P => S.sum (fun i => G i P)) := by
      apply ENNReal.tsum_le_tsum
      intro P
      change enorm (S.sum (fun i => F i P)) <= S.sum (fun i => G i P)
      exact enorm_sum_le S _
    _ = S.sum (fun i => tsum (G i)) := hFub S
    _ <= S.sum (fun i => ENNReal.ofReal (C i t * L A * R B)) :=
      Finset.sum_le_sum (fun i _ => (hC i).2 t A B)
    _ = ENNReal.ofReal (ct t * L A * R B) := by
      rw [<- ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (mul_nonneg ((hC i).1 t) hL) hR)]
      simp only [ct, Finset.sum_mul]

set_option maxHeartbeats 1200000 in
/-- Weighted integrability of both cusp functions gives singular
cancellation for a Schwartz rectangle and its actual self-dual Fourier
transform. The same two quotient weights serve both tests. -/
theorem godementJacquetDoubleThetaIntegrals_eq_invertible_of_weightedRectangles
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (RectangleWeightFinite K)] [BorelSpace (RectangleWeightFinite K)]
    [MeasurableSpace (ThetaWeightedGroup K n)] [BorelSpace (ThetaWeightedGroup K n)]
    [MeasurableSpace (ThetaWeightedMatrix K n)] [BorelSpace (ThetaWeightedMatrix K n)]
    (mu : Measure (ThetaWeightedGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (D : Set (ThetaWeightedGroup K n)) (hD : MeasurableSet D)
    (hUnique : forall A : ThetaWeightedGroup K n, ExistsUnique
      (fun gamma : (adelicPrincipalDeterminantOne K n).range => Membership.mem D (gamma.val * A)))
    (a : RectangleWeightIndex n -> RectangleWeightFinite K) (d : RingOfIntegers K)
    (hd : Not (d = 0))
    (f : SchwartzMap (PiLp 2 (fun _ : RectangleWeightIndex n => DedekindZeta.Theta.minkowskiSpace K)) Complex)
    (c b : ThetaWeightedGroup K n -> Complex) (hc : Measurable c) (hb : Measurable b)
    (hInvariantC : forall gamma : (adelicPrincipalDeterminantOne K n).range, forall A,
      c (gamma.val * A) = c A)
    (hInvariantB : forall gamma : (adelicPrincipalDeterminantOne K n).range, forall A,
      b (gamma.val * A) = b A)
    (hPeriodsC : HasGodementJacquetVanishingUnipotentPeriods c)
    (hPeriodsB : HasGodementJacquetVanishingUnipotentPeriods b)
    (hMeanC : integral (mu.restrict D) c = 0) (hMeanB : integral (mu.restrict D) b = 0)
    (m : Nat) (hm : Module.finrank Real
      (PiLp 2 (fun _ : RectangleWeightIndex n => DedekindZeta.Theta.minkowskiSpace K)) < m)
    (dLeft dRight : ThetaWeightedGroup K n -> RectangleWeightDenom K)
    (hLeft : forall A i j, Membership.mem (heckeIntegralFiniteAdeles (K := K))
      ((algebraMap K (RectangleWeightFinite K)).comp (algebraMap (RingOfIntegers K) K)
        (dLeft A).val * (A.val.val i j).2))
    (hRight : forall B i j, Membership.mem (heckeIntegralFiniteAdeles (K := K))
      ((algebraMap K (RectangleWeightFinite K)).comp (algebraMap (RingOfIntegers K) K)
        (dRight B).val * (B.val.inv i j).2)) :
    let s (e : RectangleWeightDenom K) :=
      godementJacquetFullTheta_principalScalarMatrixUnit K n e.val e.property
    let H := godementJacquetFullTheta_archimedeanHeight K n
    let L (A : ThetaWeightedGroup K n) := H (s (dLeft A) * A.val) 1 ^ m
    let R (B : ThetaWeightedGroup K n) := H 1 (Inv.inv B.val * s (dRight B)) ^ m
    let Phi := godementJacquetMatrixRectangle K a d f
    let Psi := godementJacquetSelfDualMatrixFourier K Phi
    IntegrableOn (fun A => norm (c A) * L A) D mu ->
    IntegrableOn (fun B => norm (b B) * R B) D mu ->
    IntegrableOn (fun A => norm (b A) * L A) D mu ->
    IntegrableOn (fun B => norm (c B) * R B) D mu ->
    forall t : Real, And
      (godementJacquetDoubleThetaIntegral K n (mu.restrict D) Phi c b t =
        godementJacquetInvertibleDoubleThetaIntegral K n (mu.restrict D) Phi c b t)
      (godementJacquetDoubleThetaIntegral K n (mu.restrict D) Psi b c t =
        godementJacquetInvertibleDoubleThetaIntegral K n (mu.restrict D) Psi b c t) := by
  intro s H L R Phi Psi hcL hbR hbL hcR
  let G := ThetaWeightedGroup K n
  have hL (A : G) : 1 <= L A := by
    change 1 <= H (s (dLeft A) * A.val) 1 ^ m
    calc
      (1 : Real) = 1 ^ m := (one_pow m).symm
      _ <= _ := by
        gcongr
        exact le_max_left _ _
  have hR (B : G) : 0 <= R B := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hPhi : Measurable Phi :=
    (continuous_godementJacquetMatrixRectangle K (n := n) a d hd f).measurable
  have hPsi : Measurable Psi :=
    (continuous_godementJacquetSelfDualMatrixFourier_rectangle K n a d hd f).measurable
  choose C hC using godementJacquetDoubleThetaTerm_productMajorant_rectangle K n a d f m hm
    dLeft dRight hLeft hRight
  choose d' hd' using exists_godementJacquetSelfDualMatrixFourier_rectangle_eq_sum K n a d hd f
  choose S hS using hd'.2
  choose a' ha' using hS
  choose f' hf' using ha'
  let Q : ThetaWeightedMatrix K n -> Complex :=
    fun Y => S.sum (fun j => godementJacquetMatrixRectangle K (a' j) d' (f' j) Y)
  have hDual : Psi = Q := funext hf'
  choose C' hC' using godementJacquetDoubleThetaTerm_productMajorant_finset_rectangles K n
    (Set (RectangleWeightIndex n -> RectangleWeightFinite K)) S a' d' f' m hm dLeft dRight hLeft hRight
  have hDualMajorant (t : Real) (A B : G) :
      tsum (fun P => enorm (godementJacquetDoubleThetaTerm K n Psi t A B P)) <=
        ENNReal.ofReal (C' t * L A * R B) := by
    rw [hDual]
    exact hC'.2 t A B
  intro t
  exact And.intro
    (godementJacquetDoubleThetaIntegral_eq_invertible_of_productMajorant K n hn mu D hD hUnique
      t Phi hPhi c b hc hb hInvariantC hPeriodsC hMeanC C (hC.1 t) L R hL hR hcL hbR hC.2)
    (godementJacquetDoubleThetaIntegral_eq_invertible_of_productMajorant K n hn mu D hD hUnique
      t Psi hPsi b c hb hc hInvariantB hPeriodsB hMeanB C' (hC'.1 t) L R hL hR hbL hcR hDualMajorant)

end Robin1984.GRH
