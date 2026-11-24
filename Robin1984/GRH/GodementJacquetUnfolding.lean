import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Robin1984.GRH.GodementJacquetCoordinates

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and the global matrix-coefficient zeta integral.
- Formalization note: Unfolds the weighted adelic integral into the double theta integral over determinant-one fundamental domains under absolute integrability.
- PROVENANCE-END
-/

/-!
# Unfolding the Godement-Jacquet zeta integral

At each determinant value, a fundamental domain for the rational subgroup
replaces integration by a rational matrix sum. Left invariance and Fubini
then express the matrix-coefficient zeta integral as a double quotient
integral and a logarithmic Mellin transform.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField MeasureTheory

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

private abbrev DeterminantOne :=
  (adelicDeterminantLogNorm K n).ker

private abbrev PrincipalDeterminantOne :=
  (adelicPrincipalDeterminantOne K n).range

/-- The rational principal subgroup in the determinant-one group is countable. -/
theorem countable_adelicPrincipalDeterminantOne : Countable (PrincipalDeterminantOne K n) := by
  let E := (Module.finBasis Rat K).equivFun
  let _ : Countable K := E.injective.countable
  let _ : Countable (Matrix (Fin n) (Fin n) K) := by
    change Countable (Fin n -> Fin n -> K)
    infer_instance
  let _ : Countable (Matrix.GeneralLinearGroup (Fin n) K) :=
    Units.val_injective.countable
  let P := adelicPrincipalDeterminantOne K n
  have h : Function.Surjective P.rangeRestrict := by
    intro a
    choose b hb using a.property
    exact Exists.intro b (Subtype.ext hb)
  exact h.countable

section Unfolding

variable [MeasurableSpace (DeterminantOne K n)] [BorelSpace (DeterminantOne K n)]

/-- At one logarithmic determinant value, the rational subgroup unfolds over its fundamental domain. -/
theorem integral_adelicGodementJacquetSlice_eq_theta
    (mu : Measure (DeterminantOne K n)) [mu.IsMulLeftInvariant]
    {D : Set (DeterminantOne K n)}
    (hD : IsFundamentalDomain (PrincipalDeterminantOne K n) D mu)
    (t : Real) (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (c : AdelicGeneralLinearGroup K n -> Complex)
    (hc : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      c (adelicPrincipalGeneralLinear K n a * g) = c g)
    (hInt : Integrable (fun k : DeterminantOne K n =>
      let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
      Phi ((z * k.val).val) * c (z * k.val)) mu) :
    let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
    integral mu (fun k : DeterminantOne K n => Phi ((z * k.val).val) * c (z * k.val)) =
      integral (mu.restrict D) (fun k : DeterminantOne K n =>
        (tsum (fun a : PrincipalDeterminantOne K n => Phi ((a.val.val * (z * k.val)).val))) *
          c (z * k.val)) := by
  let _ : Countable (PrincipalDeterminantOne K n) := countable_adelicPrincipalDeterminantOne K n
  let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let f : DeterminantOne K n -> Complex := fun k => Phi ((z * k.val).val) * c (z * k.val)
  have hmove (a : PrincipalDeterminantOne K n) (k : DeterminantOne K n) :
      z * (SMul.smul a k).val = a.val.val * (z * k.val) := by
    change z * (a.val.val * k.val) = a.val.val * (z * k.val)
    rw [<- mul_assoc, (adelicDeterminantSection_commute K n (Multiplicative.ofAdd t) a.val.val).eq,
      mul_assoc]
  have hinvariant (a : PrincipalDeterminantOne K n) (k : DeterminantOne K n) :
      c (a.val.val * (z * k.val)) = c (z * k.val) := by
    choose p hp using a.property
    have hp' : adelicPrincipalGeneralLinear K n p = a.val.val := congrArg Subtype.val hp
    rw [<- hp']
    exact hc p _
  have hTheta (k : DeterminantOne K n) :
      tsum (fun a : PrincipalDeterminantOne K n => f (SMul.smul a k)) =
        (tsum (fun a : PrincipalDeterminantOne K n => Phi ((a.val.val * (z * k.val)).val))) *
          c (z * k.val) := by
    simp only [f, hmove, hinvariant, tsum_mul_right]
  change integral mu f = _
  calc
    integral mu f = tsum (fun a : PrincipalDeterminantOne K n =>
        integral (mu.restrict D) (fun k => f (SMul.smul a k))) :=
      hD.integral_eq_tsum'' f hInt
    _ = integral (mu.restrict D) (fun k =>
        tsum (fun a : PrincipalDeterminantOne K n => f (SMul.smul a k))) := by
      symm
      rw [integral_tsum]
      . exact fun a => (hInt.1.comp_quasiMeasurePreserving
          (measurePreserving_smul a mu).quasiMeasurePreserving).restrict
      . intro hInfinite
        exact (ne_of_lt hInt.2) ((hD.lintegral_eq_tsum'' (fun k => enorm (f k))).trans hInfinite)
    _ = _ := by simp only [hTheta, z]

/-- The full weighted integral is the Mellin transform of the rational
matrix sum over a fundamental domain of the determinant-one group. -/
theorem integral_adelicGodementJacquet_eq_thetaMellin
    [MeasurableSpace (AdelicGeneralLinearGroup K n)] [BorelSpace (AdelicGeneralLinearGroup K n)]
    (hn : 0 < n) (mu : Measure (DeterminantOne K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    {D : Set (DeterminantOne K n)} (hD : IsFundamentalDomain (PrincipalDeterminantOne K n) D mu)
    (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (c : AdelicGeneralLinearGroup K n -> Complex) (s : Complex)
    (hc : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      c (adelicPrincipalGeneralLinear K n a * g) = c g)
    (hInt : Integrable (fun g : AdelicGeneralLinearGroup K n =>
      (Phi g.val * c g) * (adelicDeterminantNorm K n g : Complex) ^
        (s + ((n : Complex) - 1) / 2)) (adelicDeterminantProductMeasure K n hn mu)) :
    integral (adelicDeterminantProductMeasure K n hn mu)
      (fun g : AdelicGeneralLinearGroup K n => (Phi g.val * c g) *
        (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)) =
      integral (volume : Measure Real) (fun t : Real =>
        let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
        (integral (mu.restrict D) (fun k : DeterminantOne K n =>
          (tsum (fun a : PrincipalDeterminantOne K n => Phi ((a.val.val * (z * k.val)).val))) *
            c (z * k.val))) *
          Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2))) := by
  let e := (adelicDeterminantHomeomorph K n hn).toMeasurableEquiv
  let f : AdelicGeneralLinearGroup K n -> Complex := fun g =>
    (Phi g.val * c g) * (adelicDeterminantNorm K n g : Complex) ^
      (s + ((n : Complex) - 1) / 2)
  have hPull : Integrable (fun p => f (e p)) ((volume : Measure Real).prod mu) :=
    (integrable_map_equiv e f).mp hInt
  rw [integral_adelicGodementJacquet_eq_logMellin K n hn mu Phi c s hInt]
  apply integral_congr_ae
  filter_upwards [hPull.prod_right_ae] with t ht
  let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let w := Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2))
  have hSlice : Integrable (fun k : DeterminantOne K n =>
      Phi ((z * k.val).val) * c (z * k.val)) mu := by
    apply (ht.mul_const (Inv.inv w)).congr
    refine Filter.Eventually.of_forall (fun k => ?_)
    have hw : (adelicDeterminantNorm K n (e (Prod.mk t k)) : Complex) ^
        (s + ((n : Complex) - 1) / 2) = w :=
      adelicGodementJacquetWeight_coordinates K n hn (Multiplicative.ofAdd t) k s
    change (Phi ((z * k.val).val) * c (z * k.val)) *
      (adelicDeterminantNorm K n (e (Prod.mk t k)) : Complex) ^
        (s + ((n : Complex) - 1) / 2) * Inv.inv w = _
    rw [hw]
    have hw0 : Not (w = 0) := Complex.exp_ne_zero _
    field_simp
  exact congrArg (fun x : Complex => x * w)
    (integral_adelicGodementJacquetSlice_eq_theta K n mu hD t Phi c hc hSlice)

end Unfolding

section MatrixCoefficient

variable [MeasurableSpace (AdelicGeneralLinearGroup K n)]
  [BorelSpace (AdelicGeneralLinearGroup K n)]
  [MeasurableSpace (DeterminantOne K n)]

/-- The quotient matrix-coefficient integral unfolds by Fubini and left
translation on the determinant-one group. -/
theorem integral_adelicGodementJacquetMatrixCoeff_eq_unfolded
    (mu : Measure (AdelicGeneralLinearGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (nu : Measure (DeterminantOne K n)) [SFinite nu]
    (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (phi : AdelicGeneralLinearGroup K n -> Complex)
    (psi : DeterminantOne K n -> Complex) (s : Complex)
    (hInt : Integrable (fun p : Prod (AdelicGeneralLinearGroup K n) (DeterminantOne K n) =>
      (Phi p.1.val * (phi (p.2.val * p.1) * psi p.2)) *
        (adelicDeterminantNorm K n p.1 : Complex) ^ (s + ((n : Complex) - 1) / 2))
      (mu.prod nu)) :
    let w : AdelicGeneralLinearGroup K n -> Complex := fun g =>
      (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)
    integral mu (fun g => (Phi g.val * integral nu (fun k => phi (k.val * g) * psi k)) * w g) =
      integral nu (fun k =>
        (integral mu (fun g => (Phi ((Inv.inv k.val * g).val) * phi g) * w g)) * psi k) := by
  let w : AdelicGeneralLinearGroup K n -> Complex := fun g =>
    (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)
  let f : Prod (AdelicGeneralLinearGroup K n) (DeterminantOne K n) -> Complex :=
    fun p => (Phi p.1.val * (phi (p.2.val * p.1) * psi p.2)) * w p.1
  have hNorm (k : DeterminantOne K n) : adelicDeterminantNorm K n k.val = 1 := by
    have hLog : Real.log (adelicDeterminantNorm K n k.val) = 0 := k.property
    rw [<- Real.exp_log (adelicDeterminantNorm_pos K n k.val), hLog, Real.exp_zero]
  have hLeft (g : AdelicGeneralLinearGroup K n) :
      (Phi g.val * integral nu (fun k => phi (k.val * g) * psi k)) * w g =
        integral nu (fun k => f (Prod.mk g k)) := by
    rw [<- integral_const_mul, <- integral_mul_const]
  have hRight (k : DeterminantOne K n) :
      integral mu (fun g => f (Prod.mk g k)) =
        (integral mu (fun g => (Phi ((Inv.inv k.val * g).val) * phi g) * w g)) * psi k := by
    let F : AdelicGeneralLinearGroup K n -> Complex :=
      fun g => ((Phi ((Inv.inv k.val * g).val) * phi g) * w g) * psi k
    calc
      integral mu (fun g => f (Prod.mk g k)) =
          integral mu (fun g => F (k.val * g)) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun g => ?_)
        dsimp only [f, F, w]
        rw [<- mul_assoc (Inv.inv k.val) k.val g, inv_mul_cancel, one_mul,
          map_mul, hNorm k, one_mul]
        ac_rfl
      _ = integral mu F := integral_mul_left_eq_self F k.val
      _ = _ := by exact integral_mul_const _ _
  change integral mu
      (fun g => (Phi g.val * integral nu (fun k => phi (k.val * g) * psi k)) * w g) =
    integral nu
      (fun k => (integral mu (fun g => (Phi ((Inv.inv k.val * g).val) * phi g) * w g)) * psi k)
  calc
    _ = integral mu (fun g => integral nu (fun k => f (Prod.mk g k))) := by simp only [hLeft]
    _ = integral nu (fun k => integral mu (fun g => f (Prod.mk g k))) :=
      integral_integral_swap (f := fun g k => f (Prod.mk g k)) hInt
    _ = _ := by simp only [hRight]

/-- A quotient matrix coefficient gives the double quotient theta
integral, with the same logarithmic Mellin weight as the original zeta integral. -/
theorem integral_adelicGodementJacquet_eq_doubleThetaMellin
    [BorelSpace (DeterminantOne K n)] (hn : 0 < n)
    (mu : Measure (DeterminantOne K n)) [SFinite mu] [mu.IsHaarMeasure]
    {D : Set (DeterminantOne K n)} (hD : IsFundamentalDomain (PrincipalDeterminantOne K n) D mu)
    (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (phi : AdelicGeneralLinearGroup K n -> Complex)
    (psi : DeterminantOne K n -> Complex) (s : Complex)
    (hc : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      phi (adelicPrincipalGeneralLinear K n a * g) = phi g)
    (hInt : Integrable (fun p : Prod (AdelicGeneralLinearGroup K n) (DeterminantOne K n) =>
      (Phi p.1.val * (phi (p.2.val * p.1) * psi p.2)) *
        (adelicDeterminantNorm K n p.1 : Complex) ^ (s + ((n : Complex) - 1) / 2))
      ((adelicDeterminantProductMeasure K n hn mu).prod (mu.restrict D))) :
    let M := adelicDeterminantProductMeasure K n hn mu
    let nu := mu.restrict D
    integral M (fun g =>
      (Phi g.val * integral nu (fun h => phi (h.val * g) * psi h)) *
        (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)) =
      integral nu (fun h =>
        (integral (volume : Measure Real) (fun t : Real =>
          let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
          (integral nu (fun k : DeterminantOne K n =>
            (tsum (fun a : PrincipalDeterminantOne K n =>
              Phi ((Inv.inv h.val * (a.val.val * (z * k.val))).val))) * phi (z * k.val))) *
            Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2)))) * psi h) := by
  let M := adelicDeterminantProductMeasure K n hn mu
  let nu := mu.restrict D
  let _ : SFinite M := by
    change SFinite (Measure.map (adelicDeterminantHomeomorph K n hn) ((volume : Measure Real).prod mu))
    infer_instance
  let _ : M.IsHaarMeasure := isHaarMeasure_adelicDeterminantProductMeasure K n hn mu
  let w : AdelicGeneralLinearGroup K n -> Complex := fun g =>
    (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)
  let f : Prod (AdelicGeneralLinearGroup K n) (DeterminantOne K n) -> Complex :=
    fun p => (Phi p.1.val * (phi (p.2.val * p.1) * psi p.2)) * w p.1
  have hProduct : Integrable f (M.prod nu) := hInt
  change integral M (fun g =>
      (Phi g.val * integral nu (fun h => phi (h.val * g) * psi h)) * w g) = _
  rw [integral_adelicGodementJacquetMatrixCoeff_eq_unfolded K n M nu Phi phi psi s hProduct]
  apply integral_congr_ae
  filter_upwards [hProduct.prod_left_ae] with h hh
  by_cases hzero : psi h = 0
  . simp only [hzero, mul_zero]
  . let shifted : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex :=
      fun X => Phi ((Inv.inv h.val).val * X)
    have hLog : Real.log (adelicDeterminantNorm K n h.val) = 0 := h.property
    have hNorm : adelicDeterminantNorm K n h.val = 1 := by
      rw [<- Real.exp_log (adelicDeterminantNorm_pos K n h.val), hLog, Real.exp_zero]
    have hmp := measurePreserving_mul_left M (Inv.inv h.val)
    have hTranslated := hmp.integrable_comp_of_integrable hh
    have hShifted : Integrable (fun g : AdelicGeneralLinearGroup K n =>
        (shifted g.val * phi g) * w g) M := by
      apply (hTranslated.mul_const (Inv.inv (psi h))).congr
      refine Filter.Eventually.of_forall (fun g => ?_)
      change (shifted g.val * (phi (h.val * (Inv.inv h.val * g)) * psi h)) *
        w (Inv.inv h.val * g) * Inv.inv (psi h) = _
      have hwg : w (Inv.inv h.val * g) = w g := by
        change (adelicDeterminantNorm K n (Inv.inv h.val * g) : Complex) ^ _ = w g
        rw [map_mul, map_inv, hNorm, inv_one, one_mul]
      rw [<- mul_assoc h.val, mul_inv_cancel, one_mul, hwg]
      calc
        _ = ((shifted g.val * phi g) * w g) * (psi h * Inv.inv (psi h)) := by ac_rfl
        _ = _ := by field_simp
    exact congrArg (fun x : Complex => x * psi h)
      (integral_adelicGodementJacquet_eq_thetaMellin K n hn mu hD shifted phi s hc hShifted)

end MatrixCoefficient

end Robin1984.GRH
