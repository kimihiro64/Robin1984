import Robin1984.GRH.GodementJacquetThetaMellin

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and integration over a measurable fundamental domain.
- Formalization note: Identifies the adelic matrix-coefficient zeta integral with the logarithmic Mellin transform of the invertible double theta integral.
- PROVENANCE-END
-/

/-!
# Matrix-coefficient zeta integrals on the determinant line

We identify the sum over the rational principal group with the invertible theta
series and transfer the quotient integral to the logarithmic Mellin transform
under absolute integrability.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField MeasureTheory
open scoped Classical

private abbrev MatrixCoeffMellinAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K
private abbrev MatrixCoeffMellinGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker
private abbrev MatrixCoeffMellinMatrix (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  Matrix (Fin n) (Fin n) (MatrixCoeffMellinAdeles K)

/-- The invertible rational theta series is the sum over the principal
range used in the quotient unfolding. -/
theorem tsum_godementJacquetPrincipalRange_eq_invertibleDoubleThetaSeries
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (Phi : MatrixCoeffMellinMatrix K n -> Complex) (t : Real)
    (A B : MatrixCoeffMellinGroup K n) :
    let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
    tsum (fun a : (adelicPrincipalDeterminantOne K n).range =>
      Phi ((Inv.inv A.val * (a.val.val * (z * B.val))).val)) =
      godementJacquetInvertibleDoubleThetaSeries K n Phi t A B := by
  let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let e : Equiv (Matrix.GeneralLinearGroup (Fin n) K) (adelicPrincipalDeterminantOne K n).range :=
    Equiv.ofInjective (adelicPrincipalDeterminantOne K n)
      (adelicPrincipalDeterminantOne_injective : Function.Injective (adelicPrincipalDeterminantOne K n))
  let F (a : (adelicPrincipalDeterminantOne K n).range) :=
    Phi ((Inv.inv A.val * (a.val.val * (z * B.val))).val)
  change tsum F = _
  calc
    _ = tsum (fun P => F (e P)) := (e.tsum_eq F).symm
    _ = _ := by
      apply tsum_congr
      intro P
      let q := adelicPrincipalGeneralLinear K n P
      have hz : q * z = z * q :=
        (adelicDeterminantSection_commute K n (Multiplicative.ofAdd t) q).eq.symm
      change Phi ((Inv.inv A.val * (q * (z * B.val))).val) =
        godementJacquetDoubleThetaTerm K n Phi t A B P.val
      have h : Inv.inv A.val * (q * (z * B.val)) = ((Inv.inv A.val * z) * q) * B.val := by
        calc
          _ = Inv.inv A.val * ((q * z) * B.val) := by rw [mul_assoc q z B.val]
          _ = _ := by rw [hz]; simp only [mul_assoc]
      rw [h]
      rfl

/-- Reorder the determinant variable and the first quotient variable in
an absolutely integrable triple kernel. -/
theorem integral_godementJacquetTheta_tripleSwap
    {G : Type*} [MeasurableSpace G] (nu : Measure G) [SFinite nu]
    (F : Real -> G -> G -> Complex)
    (hF : Integrable (fun x : Prod Real (Prod G G) => F x.1 x.2.1 x.2.2)
      ((volume : Measure Real).prod (nu.prod nu))) :
    integral nu (fun A => integral (volume : Measure Real) (fun t => integral nu (F t A))) =
      integral (volume : Measure Real) (fun t =>
        integral (nu.prod nu) (fun q : Prod G G => F t q.1 q.2)) := by
  let m : Measure Real := volume
  let E : MeasurableEquiv (Prod (Prod Real G) G) (Prod Real (Prod G G)) := MeasurableEquiv.prodAssoc
  have hAssoc : Integrable (fun x : Prod (Prod Real G) G => F x.1.1 x.1.2 x.2) ((m.prod nu).prod nu) :=
    ((measurePreserving_prodAssoc m nu nu).integrable_comp_emb E.measurableEmbedding).mpr hF
  have hK : Integrable (fun x : Prod Real G => integral nu (F x.1 x.2)) (m.prod nu) :=
    hAssoc.integral_prod_left
  calc
    _ = integral m (fun t => integral nu (fun A => integral nu (F t A))) :=
      (integral_integral_swap (f := fun t A => integral nu (F t A)) hK).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hF.prod_right_ae] with t ht
      exact (integral_prod (fun q : Prod G G => F t q.1 q.2) ht).symm

set_option maxHeartbeats 1200000 in
/-- Within the domain of absolute convergence, a matrix-coefficient
Godement--Jacquet integral is the Mellin transform of the invertible
double theta integral. The automorphic vector is invariant under the
positive central determinant section in this normalization. -/
theorem integral_adelicGodementJacquetMatrixCoeff_eq_logMellin
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (AdelicGeneralLinearGroup K n)] [BorelSpace (AdelicGeneralLinearGroup K n)]
    [MeasurableSpace (MatrixCoeffMellinGroup K n)] [BorelSpace (MatrixCoeffMellinGroup K n)]
    (mu : Measure (MatrixCoeffMellinGroup K n)) [SFinite mu] [mu.IsHaarMeasure]
    (D : Set (MatrixCoeffMellinGroup K n))
    (hD : IsFundamentalDomain (adelicPrincipalDeterminantOne K n).range D mu)
    (Phi : MatrixCoeffMellinMatrix K n -> Complex)
    (f : AdelicGeneralLinearGroup K n -> Complex)
    (c : MatrixCoeffMellinGroup K n -> Complex) (s : Complex)
    (hPrincipal : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      f (adelicPrincipalGeneralLinear K n a * g) = f g)
    (hCentral : forall t : Real, forall B : MatrixCoeffMellinGroup K n,
      f (adelicDeterminantSection K n (Multiplicative.ofAdd t) * B.val) = f B.val)
    (hInt : Integrable (fun p : Prod (AdelicGeneralLinearGroup K n) (MatrixCoeffMellinGroup K n) =>
      (Phi p.1.val * (f (p.2.val * p.1) * c p.2)) *
        (adelicDeterminantNorm K n p.1 : Complex) ^ (s + ((n : Complex) - 1) / 2))
      ((adelicDeterminantProductMeasure K n hn mu).prod (mu.restrict D)))
    (hTheta : Integrable (fun p : Prod Real (Prod (MatrixCoeffMellinGroup K n) (MatrixCoeffMellinGroup K n)) =>
      (godementJacquetInvertibleDoubleThetaSeries K n Phi p.1 p.2.1 p.2.2 *
        (c p.2.1 * f p.2.2.val)) * Complex.exp ((p.1 : Complex) * (s + ((n : Complex) - 1) / 2)))
      ((volume : Measure Real).prod ((mu.restrict D).prod (mu.restrict D)))) :
    integral (adelicDeterminantProductMeasure K n hn mu)
      (fun g => (Phi g.val * integral (mu.restrict D) (fun h => f (h.val * g) * c h)) *
        (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)) =
      godementJacquetLogMellin n
        (fun t => godementJacquetInvertibleDoubleThetaIntegral K n (mu.restrict D) Phi c
          (fun B => f B.val) t) s := by
  let G := MatrixCoeffMellinGroup K n
  let nu := mu.restrict D
  let m : Measure Real := volume
  let z (t : Real) := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let W (t : Real) := Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2))
  let R (t : Real) (A B : G) := tsum (fun a : (adelicPrincipalDeterminantOne K n).range =>
    Phi ((Inv.inv A.val * (a.val.val * (z t * B.val))).val))
  let T (t : Real) (A B : G) :=
    (godementJacquetInvertibleDoubleThetaSeries K n Phi t A B * (c A * f B.val)) * W t
  have hTheta' : Integrable (fun p : Prod Real (Prod G G) => T p.1 p.2.1 p.2.2) (m.prod (nu.prod nu)) := hTheta
  have hFiber (t : Real) (A : G) :
      (integral nu (fun B : G => R t A B * f (z t * B.val)) * W t) * c A =
        integral nu (T t A) := by
    let F (B : G) := R t A B * f (z t * B.val)
    have hW : integral nu (fun B : G => F B * W t) = integral nu F * W t :=
      integral_mul_const (W t) F
    have hC : integral nu (fun B : G => F B * W t * c A) =
        integral nu (fun B : G => F B * W t) * c A :=
      integral_mul_const (c A) (fun B : G => F B * W t)
    calc
      _ = integral nu (fun B : G => F B * W t * c A) :=
        (hC.trans (congrArg (fun x : Complex => x * c A) hW)).symm
      _ = _ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun B => ?_)
        have hR : R t A B = godementJacquetInvertibleDoubleThetaSeries K n Phi t A B :=
          tsum_godementJacquetPrincipalRange_eq_invertibleDoubleThetaSeries K n Phi t A B
        change (R t A B * f (z t * B.val)) * W t * c A =
          (godementJacquetInvertibleDoubleThetaSeries K n Phi t A B * (c A * f B.val)) * W t
        rw [hR, hCentral t B]
        ac_rfl
  calc
    _ = integral nu (fun A : G =>
      (integral m (fun t : Real => (integral nu (fun B : G => R t A B * f (z t * B.val))) * W t)) * c A) :=
        integral_adelicGodementJacquet_eq_doubleThetaMellin K n hn mu hD Phi f c s hPrincipal hInt
    _ = integral nu (fun A : G => integral m (fun t : Real => integral nu (T t A))) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun A => ?_)
      let F (t : Real) := integral nu (fun B : G => R t A B * f (z t * B.val)) * W t
      have hC : integral m (fun t : Real => F t * c A) = integral m F * c A :=
        integral_mul_const (c A) F
      exact hC.symm.trans (integral_congr_ae (Filter.Eventually.of_forall (fun t => hFiber t A)))
    _ = integral m (fun t : Real => integral (nu.prod nu) (fun q : Prod G G => T t q.1 q.2)) :=
      integral_godementJacquetTheta_tripleSwap nu T hTheta'
    _ = _ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun t => ?_)
      change integral (nu.prod nu) (fun q : Prod G G =>
        (godementJacquetInvertibleDoubleThetaSeries K n Phi t q.1 q.2 * (c q.1 * f q.2.val)) * W t) =
          godementJacquetInvertibleDoubleThetaIntegral K n nu Phi c (fun B => f B.val) t * W t
      exact integral_mul_const (W t)
        (fun q : Prod G G => godementJacquetInvertibleDoubleThetaSeries K n Phi t q.1 q.2 * (c q.1 * f q.2.val))

end Robin1984.GRH
