import Robin1984.GRH.GodementJacquetSchwartzDilation
import Robin1984.GRH.GodementJacquetUnfolding

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and Mellin reflection of the adelic matrix theta integral.
- Formalization note: Integrates the matrix Poisson reflection over the two quotient variables and proves the standard Mellin reflection after cuspidal cancellation.
- PROVENANCE-END
-/

/-!
# The adelic matrix theta integral and its Mellin reflection

The double theta integral pairs the rational matrix sum with two
functions on the determinant-norm-one quotient. Absolute integrability
and the cuspidal periods allow one to restrict the sum to invertible
rational matrices. The Poisson identity swaps the quotient variables,
and the determinant measure factor gives the standard functional
equation at s and 1 - s.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

section DoubleThetaReflection

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

private abbrev GlobalMatrixAdeles := AdeleRing (RingOfIntegers K) K
private abbrev ThetaNormGroup := (adelicDeterminantLogNorm K n).ker
private abbrev ThetaMatrix := Matrix (Fin n) (Fin n) (GlobalMatrixAdeles K)
private abbrev ThetaFiniteAdeles := FiniteAdeleRing (RingOfIntegers K) K
private abbrev ThetaArchMatrix :=
  PiLp 2 (fun _ : Prod (Fin n) (Fin n) => DedekindZeta.Theta.minkowskiSpace K)

/-- The theta term for a fixed rational matrix and two quotient coordinates. -/
def godementJacquetDoubleThetaTerm (Phi : ThetaMatrix K n -> Complex) (t : Real)
    (A B : ThetaNormGroup K n) (P : Matrix (Fin n) (Fin n) K) : Complex :=
  let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let f := algebraMap K (GlobalMatrixAdeles K)
  Phi ((Inv.inv A.val * z).val * P.map f * B.val.val)

/-- The rational matrix theta series on a pair of determinant-norm-one
variables, with the real logarithmic determinant parameter separated. -/
def godementJacquetDoubleThetaSeries
    (Phi : ThetaMatrix K n -> Complex) (t : Real) (A B : ThetaNormGroup K n) : Complex :=
  tsum (godementJacquetDoubleThetaTerm K n Phi t A B)

/-- The same theta series restricted to invertible rational matrices. -/
def godementJacquetInvertibleDoubleThetaSeries
    (Phi : ThetaMatrix K n -> Complex) (t : Real) (A B : ThetaNormGroup K n) : Complex :=
  tsum (fun P : Matrix.GeneralLinearGroup (Fin n) K =>
    godementJacquetDoubleThetaTerm K n Phi t A B P.val)

/-- The product quotient integral of the double theta series against
the two automorphic functions. -/
def godementJacquetDoubleThetaIntegral
    [MeasurableSpace (ThetaNormGroup K n)] (nu : Measure (ThetaNormGroup K n))
    (Phi : ThetaMatrix K n -> Complex) (c d : ThetaNormGroup K n -> Complex) (t : Real) : Complex :=
  integral (nu.prod nu) (fun p : Prod (ThetaNormGroup K n) (ThetaNormGroup K n) =>
    godementJacquetDoubleThetaSeries K n Phi t p.1 p.2 * (c p.1 * d p.2))

/-- The product quotient integral of the invertible terms. -/
def godementJacquetInvertibleDoubleThetaIntegral
    [MeasurableSpace (ThetaNormGroup K n)] (nu : Measure (ThetaNormGroup K n))
    (Phi : ThetaMatrix K n -> Complex) (c d : ThetaNormGroup K n -> Complex) (t : Real) : Complex :=
  integral (nu.prod nu) (fun p : Prod (ThetaNormGroup K n) (ThetaNormGroup K n) =>
    godementJacquetInvertibleDoubleThetaSeries K n Phi t p.1 p.2 * (c p.1 * d p.2))

/-- Applying singular cancellation in the first quotient variable removes
the singular terms from the double theta integral. -/
theorem godementJacquetDoubleThetaIntegral_eq_invertible
    [MeasurableSpace (ThetaNormGroup K n)] [BorelSpace (ThetaNormGroup K n)]
    (mu : Measure (ThetaNormGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (D : Set (ThetaNormGroup K n)) (hD : MeasurableSet D)
    (hUnique : forall A : ThetaNormGroup K n, ExistsUnique
      (fun gamma : (adelicPrincipalDeterminantOne K n).range => Membership.mem D (gamma.val * A)))
    (hn : 0 < n) (t : Real)
    [MeasurableSpace (ThetaMatrix K n)] [BorelSpace (ThetaMatrix K n)]
    (Phi : ThetaMatrix K n -> Complex) (hPhi : Measurable Phi)
    (c b : ThetaNormGroup K n -> Complex) (hc : Measurable c)
    (hInvariant : forall gamma : (adelicPrincipalDeterminantOne K n).range, forall A,
      c (gamma.val * A) = c A)
    (hPeriods : HasGodementJacquetVanishingUnipotentPeriods c)
    (hCInt : IntegrableOn c D mu) (hMean : integral (mu.restrict D) c = 0)
    (hSum : forall A B : ThetaNormGroup K n,
      Summable (godementJacquetDoubleThetaTerm K n Phi t A B))
    (hAbs : Filter.Eventually (fun B : ThetaNormGroup K n =>
      lintegral (mu.restrict D) (fun A =>
        tsum (fun P => enorm (godementJacquetDoubleThetaTerm K n Phi t A B P * c A))) <
        (Top.top : ENNReal)) (ae (mu.restrict D)))
    (hFull : Integrable (fun p : Prod (ThetaNormGroup K n) (ThetaNormGroup K n) =>
      godementJacquetDoubleThetaSeries K n Phi t p.1 p.2 * (c p.1 * b p.2))
        ((mu.restrict D).prod (mu.restrict D)))
    (hInv : Integrable (fun p : Prod (ThetaNormGroup K n) (ThetaNormGroup K n) =>
      godementJacquetInvertibleDoubleThetaSeries K n Phi t p.1 p.2 * (c p.1 * b p.2))
        ((mu.restrict D).prod (mu.restrict D))) :
    godementJacquetDoubleThetaIntegral K n (mu.restrict D) Phi c b t =
      godementJacquetInvertibleDoubleThetaIntegral K n (mu.restrict D) Phi c b t := by
  let G := ThetaNormGroup K n
  let m := mu.restrict D
  let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let f := algebraMap K (GlobalMatrixAdeles K)
  let full := fun p : Prod G G =>
    godementJacquetDoubleThetaSeries K n Phi t p.1 p.2 * (c p.1 * b p.2)
  let regular := fun p : Prod G G =>
    godementJacquetInvertibleDoubleThetaSeries K n Phi t p.1 p.2 * (c p.1 * b p.2)
  change integral (m.prod m) full = integral (m.prod m) regular
  rw [integral_prod_symm full hFull, integral_prod_symm regular hInv]
  apply integral_congr_ae
  apply hAbs.mono
  intro B hB
  let shifted (X : ThetaMatrix K n) := Phi (z.val * X * B.val.val)
  have hShifted : Measurable shifted :=
    hPhi.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hTerm (A : G) (P : Matrix (Fin n) (Fin n) K) :
      shifted (A.val.inv * P.map f) = godementJacquetDoubleThetaTerm K n Phi t A B P := by
    change Phi (z.val * (A.val.inv * P.map f) * B.val.val) =
      Phi ((A.val.inv * z.val) * P.map f * B.val.val)
    have hComm : z.val * A.val.inv = A.val.inv * z.val :=
      congrArg (fun g : AdelicGeneralLinearGroup K n => g.val)
        (adelicDeterminantSection_commute K n (Multiplicative.ofAdd t) (Inv.inv A.val)).eq
    rw [<- Matrix.mul_assoc, hComm]
  have hS (A : G) : Summable (fun P : Matrix (Fin n) (Fin n) K => shifted (A.val.inv * P.map f)) :=
    (hSum A B).congr (fun P => (hTerm A P).symm)
  have hA : lintegral m (fun A : G => tsum (fun P : Matrix (Fin n) (Fin n) K =>
      enorm (shifted (A.val.inv * P.map f) * c A))) < Top.top := by
    simp_rw [hTerm]
    exact hB
  have hSlice := integral_godementJacquetFullTheta_eq_invertible_of_cuspidal hn mu D hD hUnique
    shifted hShifted c hc hInvariant hPeriods hCInt hMean hS hA
  change integral m (fun A : G =>
      (tsum (fun P : Matrix (Fin n) (Fin n) K => shifted (A.val.inv * P.map f))) * c A) =
    integral m (fun A : G =>
      (tsum (fun P : Matrix.GeneralLinearGroup (Fin n) K => shifted (A.val.inv * P.val.map f))) * c A)
    at hSlice
  simp_rw [hTerm] at hSlice
  have hFull' : (fun A : G => full (Prod.mk A B)) =
      (fun A => (godementJacquetDoubleThetaSeries K n Phi t A B * c A) * b B) := by
    funext A
    exact (mul_assoc _ _ _).symm
  have hRegular' : (fun A : G => regular (Prod.mk A B)) =
      (fun A => (godementJacquetInvertibleDoubleThetaSeries K n Phi t A B * c A) * b B) := by
    funext A
    exact (mul_assoc _ _ _).symm
  change integral m (fun A : G => full (Prod.mk A B)) =
    integral m (fun A : G => regular (Prod.mk A B))
  rw [hFull', hRegular', integral_mul_const, integral_mul_const]
  exact congrArg (fun w : Complex => w * b B) hSlice

variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
  [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]

/-- Integrated Poisson reflection interchanges the quotient variables
and reverses the logarithmic determinant parameter. -/
theorem godementJacquetDoubleThetaIntegral_reflection
    [MeasurableSpace (ThetaNormGroup K n)] (nu : Measure (ThetaNormGroup K n)) [SFinite nu]
    (hn : 0 < n) (t : Real)
    (a : Prod (Fin n) (Fin n) -> ThetaFiniteAdeles K)
    (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (ThetaArchMatrix K n) Complex)
    (c b : ThetaNormGroup K n -> Complex) :
    let Phi := godementJacquetMatrixRectangle K a d f
    godementJacquetDoubleThetaIntegral K n nu Phi c b t =
      ((Real.exp (-((n : Real) * t)) : Real) : Complex) *
        godementJacquetDoubleThetaIntegral K n nu (godementJacquetSelfDualMatrixFourier K Phi) b c (-t) := by
  let G := ThetaNormGroup K n
  let Phi := godementJacquetMatrixRectangle K a d f
  let Psi := godementJacquetSelfDualMatrixFourier K Phi
  let r := Real.exp (-((n : Real) * t))
  let rplus := Real.toNNReal r
  let P (p : Prod G G) := godementJacquetDoubleThetaSeries K n Phi t p.1 p.2 * (c p.1 * b p.2)
  let Q (p : Prod G G) := godementJacquetDoubleThetaSeries K n Psi (-t) p.1 p.2 * (b p.1 * c p.2)
  have hScale : ((rplus : Real) : Complex) = (r : Complex) :=
    congrArg Complex.ofReal (Real.coe_toNNReal _ (Real.exp_pos _).le)
  have hPoint (p : Prod G G) : P p = (r : Complex) * Q p.swap := by
    have hp := (godementJacquetMatrixRectangle_thetaReflection K n hn (Multiplicative.ofAdd t)
      p.1 p.2 a d hd f).2.2
    change godementJacquetDoubleThetaSeries K n Phi t p.1 p.2 =
      HSMul.hSMul rplus (godementJacquetDoubleThetaSeries K n Psi (-t) p.2 p.1) at hp
    change godementJacquetDoubleThetaSeries K n Phi t p.1 p.2 * (c p.1 * b p.2) =
      (r : Complex) * (godementJacquetDoubleThetaSeries K n Psi (-t) p.2 p.1 * (b p.2 * c p.1))
    rw [hp]
    change (((rplus : Real) : Complex) * godementJacquetDoubleThetaSeries K n Psi (-t) p.2 p.1) *
      (c p.1 * b p.2) = _
    rw [hScale, mul_comm (b p.2) (c p.1), mul_assoc]
  change integral (nu.prod nu) P = (r : Complex) * integral (nu.prod nu) Q
  calc
    _ = integral (nu.prod nu) (fun p : Prod G G => (r : Complex) * Q p.swap) :=
      congrArg (integral (nu.prod nu)) (funext hPoint)
    _ = (r : Complex) * integral (nu.prod nu) (fun p : Prod G G => Q p.swap) :=
      integral_const_mul _ _
    _ = _ := congrArg (fun z : Complex => (r : Complex) * z) (integral_prod_swap Q)

end DoubleThetaReflection

/-- The logarithmic Mellin transform in the standard Godement-Jacquet normalization. -/
def godementJacquetLogMellin (n : Nat) (F : Real -> Complex) (s : Complex) : Complex :=
  integral (volume : Measure Real)
    (fun t : Real => F t * Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2)))

/-- A theta reflection with determinant factor exp (-n * t) gives
the functional equation with reflection s to 1 - s. -/
theorem godementJacquetLogMellin_reflection
    (n : Nat) (F G : Real -> Complex)
    (h : forall t : Real, F t = ((Real.exp (-((n : Real) * t)) : Real) : Complex) * G (-t))
    (s : Complex) :
    godementJacquetLogMellin n F s = godementJacquetLogMellin n G (1 - s) := by
  let H (t : Real) :=
    G t * Complex.exp ((t : Complex) * ((1 - s) + ((n : Complex) - 1) / 2))
  have hEq (t : Real) : F t * Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2)) = H (-t) := by
    rw [h t, Complex.ofReal_exp]
    calc
      _ = G (-t) * Complex.exp (((-((n : Real) * t) : Real) : Complex) +
          (t : Complex) * (s + ((n : Complex) - 1) / 2)) := by
        rw [Complex.exp_add]
        ac_rfl
      _ = _ := by
        unfold H
        congr 2
        push_cast
        ring
  calc
    godementJacquetLogMellin n F s = integral (volume : Measure Real) (fun t : Real => H (-t)) :=
      congrArg (integral (volume : Measure Real)) (funext hEq)
    _ = _ := (Measure.measurePreserving_neg (volume : Measure Real)).integral_comp
      (MeasurableEquiv.neg Real).measurableEmbedding H

section InvertibleThetaMellin

variable (K : Type*) [Field K] [NumberField K] (n : Nat)
variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
  [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]

/-- The Mellin transforms of the invertible theta series satisfy the
reflected identity once the singular terms have cancelled on both sides. -/
theorem godementJacquetInvertibleDoubleThetaMellin_reflection
    [MeasurableSpace (ThetaNormGroup K n)] (nu : Measure (ThetaNormGroup K n)) [SFinite nu]
    (hn : 0 < n)
    (a : Prod (Fin n) (Fin n) -> ThetaFiniteAdeles K)
    (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (ThetaArchMatrix K n) Complex)
    (c b : Real -> ThetaNormGroup K n -> Complex)
    (hPrimal : forall t : Real,
      let Phi := godementJacquetMatrixRectangle K a d f
      godementJacquetDoubleThetaIntegral K n nu Phi (c t) (b t) t =
        godementJacquetInvertibleDoubleThetaIntegral K n nu Phi (c t) (b t) t)
    (hDual : forall t : Real,
      let Psi := godementJacquetSelfDualMatrixFourier K (godementJacquetMatrixRectangle K a d f)
      godementJacquetDoubleThetaIntegral K n nu Psi (b (-t)) (c (-t)) t =
        godementJacquetInvertibleDoubleThetaIntegral K n nu Psi (b (-t)) (c (-t)) t)
    (s : Complex) :
    let Phi := godementJacquetMatrixRectangle K a d f
    let Psi := godementJacquetSelfDualMatrixFourier K Phi
    godementJacquetLogMellin n (fun t =>
      godementJacquetInvertibleDoubleThetaIntegral K n nu Phi (c t) (b t) t) s =
    godementJacquetLogMellin n (fun t =>
      godementJacquetInvertibleDoubleThetaIntegral K n nu Psi (b (-t)) (c (-t)) t) (1 - s) := by
  let Phi := godementJacquetMatrixRectangle K a d f
  let Psi := godementJacquetSelfDualMatrixFourier K Phi
  let F (t : Real) := godementJacquetInvertibleDoubleThetaIntegral K n nu Phi (c t) (b t) t
  let G (t : Real) := godementJacquetInvertibleDoubleThetaIntegral K n nu Psi (b (-t)) (c (-t)) t
  apply godementJacquetLogMellin_reflection n F G
  intro t
  calc
    F t = godementJacquetDoubleThetaIntegral K n nu Phi (c t) (b t) t :=
      (hPrimal t).symm
    _ = ((Real.exp (-((n : Real) * t)) : Real) : Complex) *
        godementJacquetDoubleThetaIntegral K n nu Psi (b t) (c t) (-t) :=
      godementJacquetDoubleThetaIntegral_reflection K n nu hn t a d hd f (c t) (b t)
    _ = _ := congrArg (fun x : Complex => ((Real.exp (-((n : Real) * t)) : Real) : Complex) * x)
      (by simpa only [G, neg_neg] using hDual (-t))

end InvertibleThetaMellin

end Robin1984.GRH
