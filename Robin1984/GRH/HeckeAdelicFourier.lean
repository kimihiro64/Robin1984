import Robin1984.GRH.HeckeArchimedean
import Robin1984.GRH.HeckeFiniteHaarDilation
import Robin1984.GRH.HeckeFiniteTateTest

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Tate's adelic zeta integrals and Poisson summation in Algebraic Number Theory (1967).
- Formalization note: Combines archimedean and finite Fourier scaling with Poisson summation for actual translated Hecke test functions.
- PROVENANCE-END
-/

/-!
# Fourier scaling of adelic Hecke test functions

Multiplication by an infinite idele transports the determinant of the
Minkowski dilation to the archimedean idelic norm. At trace frequencies
the inverse-adjoint acts by the inverse idele. Combining this calculation
with the finite Haar scaling formula gives one Poisson identity for
simultaneously translated infinite and finite factors.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure
open scoped Classical FourierTransform

variable {K : Type*} [Field K] [NumberField K]

private abbrev Minkowski (K : Type*) [Field K] := DedekindZeta.Theta.minkowskiSpace K

/-- The mixed embedding preserves the normalized infinite idelic norm. -/
theorem mixedEmbedding_norm_infiniteIdele (b : Units (InfiniteAdeleRing K)) :
    mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace K b.val) =
      heckeInfiniteIdeleNorm b := by
  rw [mixedEmbedding.norm_apply]
  change _ = Finset.univ.prod (fun w : InfinitePlace K => norm (b.val w) ^ w.mult)
  apply Finset.prod_congr rfl
  intro w _
  congr 1
  by_cases h : w.IsReal
  . rw [mixedEmbedding.normAtPlace_apply_of_isReal h, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    have hDist := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).dist_eq (b.val w) 0
    simpa only [map_zero, dist_zero_right] using hDist
  . have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    have hDist := (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq (b.val w) 0
    simpa only [map_zero, dist_zero_right] using hDist

/-- The Minkowski automorphism induced by multiplication by an infinite idele. -/
noncomputable def heckeInfiniteIdeleDilation (b : Units (InfiniteAdeleRing K)) :
    ContinuousLinearEquiv (RingHom.id Real) (Minkowski K) (Minkowski K) :=
  DedekindZeta.Theta.A_x K (x := InfiniteAdeleRing.ringEquiv_mixedSpace K b.val)
    (by rw [mixedEmbedding_norm_infiniteIdele]; exact (heckeInfiniteIdeleNorm_pos b).ne')

/-- The dilation acts by multiplying in the mixed space before transport. -/
theorem heckeInfiniteIdeleDilation_apply (b : Units (InfiniteAdeleRing K)) (z : Minkowski K) :
    heckeInfiniteIdeleDilation b z =
      DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K b.val *
          (DedekindZeta.Theta.toMinkowski K).symm z) :=
  rfl

/-- The Jacobian of the Minkowski dilation is the infinite idelic norm. -/
theorem abs_det_heckeInfiniteIdeleDilation (b : Units (InfiniteAdeleRing K)) :
    abs (LinearMap.det ((heckeInfiniteIdeleDilation b).toLinearEquiv :
        LinearMap (RingHom.id Real) (Minkowski K) (Minkowski K))) = heckeInfiniteIdeleNorm b := by
  unfold heckeInfiniteIdeleDilation
  rw [DedekindZeta.Theta.A_x_det_abs, mixedEmbedding_norm_infiniteIdele]
  exact abs_of_pos (heckeInfiniteIdeleNorm_pos b)

/-- Archimedean Fourier scaling with its inverse-adjoint frequency. -/
theorem fourier_heckeInfiniteIdeleDilation
    (b : Units (InfiniteAdeleRing K)) (f : Minkowski K -> Complex) (z : Minkowski K) :
    (FourierTransform.fourier (fun w : Minkowski K => f (heckeInfiniteIdeleDilation b w)) :
        Minkowski K -> Complex) z =
      HSMul.hSMul ((Inv.inv (heckeInfiniteIdeleNorm b) : Real) : Complex)
        ((FourierTransform.fourier f : Minkowski K -> Complex)
          (ContinuousLinearMap.adjoint ((heckeInfiniteIdeleDilation b).symm :
            ContinuousLinearMap (RingHom.id Real) (Minkowski K) (Minkowski K)) z)) := by
  rw [DedekindZeta.Theta.fourier_comp_continuousLinearEquiv]
  change HSMul.hSMul (((Inv.inv (abs (LinearMap.det
      ((heckeInfiniteIdeleDilation b).toLinearEquiv :
        LinearMap (RingHom.id Real) (Minkowski K) (Minkowski K))))) : Real) : Complex) _ = _
  rw [abs_det_heckeInfiniteIdeleDilation]


/-- The inverse dilation is multiplication by the inverse idele. -/
theorem heckeInfiniteIdeleDilation_symm_apply
    (b : Units (InfiniteAdeleRing K)) (z : Minkowski K) :
    (heckeInfiniteIdeleDilation b).symm z =
      DedekindZeta.Theta.toMinkowski K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K b.inv *
          (DedekindZeta.Theta.toMinkowski K).symm z) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, heckeInfiniteIdeleDilation_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [<- mul_assoc, <- map_mul, b.val_inv, map_one, one_mul,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The inverse-adjoint multiplies by the conjugate of the inverse idele. -/
theorem adjoint_heckeInfiniteIdeleDilation_symm
    (b : Units (InfiniteAdeleRing K)) (z : Minkowski K) :
    ContinuousLinearMap.adjoint ((heckeInfiniteIdeleDilation b).symm :
      ContinuousLinearMap (RingHom.id Real) (Minkowski K) (Minkowski K)) z =
        DedekindZeta.Theta.toMinkowski K
          (DedekindZeta.Theta.conjMixed K
            (InfiniteAdeleRing.ringEquiv_mixedSpace K b.inv) *
            (DedekindZeta.Theta.toMinkowski K).symm z) := by
  let T := DedekindZeta.Theta.toMinkowski K
  let x := InfiniteAdeleRing.ringEquiv_mixedSpace K b.inv
  let y := DedekindZeta.Theta.conjMixed K x
  let B : ContinuousLinearMap (RingHom.id Real) (Minkowski K) (Minkowski K) :=
    T.toContinuousLinearMap.comp
      ((LinearMap.mulLeft Real y).toContinuousLinearMap.comp T.symm.toContinuousLinearMap)
  have hB (v : Minkowski K) : B v = T (y * T.symm v) := rfl
  let A : ContinuousLinearMap (RingHom.id Real) (Minkowski K) (Minkowski K) :=
    (heckeInfiniteIdeleDilation b).symm
  have hInner (u v : Minkowski K) :
      inner Real (A u) v = inner Real u (B v) := by
    have hu : u = T (T.symm u) := (T.apply_symm_apply u).symm
    have hv : v = T (T.symm v) := (T.apply_symm_apply v).symm
    change inner Real ((heckeInfiniteIdeleDilation b).symm u) v = inner Real u (B v)
    rw [heckeInfiniteIdeleDilation_symm_apply, hB]
    conv_lhs => rw [hv]
    conv_rhs => rw [hu]
    change inner Real (T (x * T.symm u)) (T (T.symm v)) =
      inner Real (T (T.symm u)) (T (y * T.symm v))
    rw [DedekindZeta.Theta.toMinkowski_inner, DedekindZeta.Theta.toMinkowski_inner]
    congr 1
    . apply Finset.sum_congr rfl
      intro w _
      simp only [Prod.fst_mul, Pi.mul_apply, y, DedekindZeta.Theta.conjMixed_fst]
      ring
    . apply congrArg (fun c : Real => 2 * c)
      apply Finset.sum_congr rfl
      intro w _
      congr 1
      simp only [Prod.snd_mul, Pi.mul_apply, y, DedekindZeta.Theta.conjMixed_snd, map_mul,
        Complex.conj_conj]
      ring
  have hAB : A = ContinuousLinearMap.adjoint B :=
    (ContinuousLinearMap.eq_adjoint_iff A B).mpr hInner
  have hAdj : ContinuousLinearMap.adjoint A = B := by
    rw [hAB, ContinuousLinearMap.adjoint_adjoint]
  change ContinuousLinearMap.adjoint A z = _
  rw [hAdj, hB]

/-- At a trace frequency the inverse-adjoint transfers to the inverse idele. -/
theorem fourier_heckeInfiniteIdeleDilation_traceFrequency
    (b : Units (InfiniteAdeleRing K)) (f : Minkowski K -> Complex)
    (z : mixedEmbedding.mixedSpace K) :
    (FourierTransform.fourier (fun w : Minkowski K => f (heckeInfiniteIdeleDilation b w)) :
        Minkowski K -> Complex) (DedekindZeta.Theta.toMinkowski K
          (DedekindZeta.Theta.conjMixed K z)) =
      HSMul.hSMul ((Inv.inv (heckeInfiniteIdeleNorm b) : Real) : Complex)
        ((FourierTransform.fourier f : Minkowski K -> Complex)
          (DedekindZeta.Theta.toMinkowski K (DedekindZeta.Theta.conjMixed K
            (InfiniteAdeleRing.ringEquiv_mixedSpace K b.inv * z)))) := by
  rw [fourier_heckeInfiniteIdeleDilation, adjoint_heckeInfiniteIdeleDilation_symm,
    ContinuousLinearEquiv.symm_apply_apply]
  have hc : DedekindZeta.Theta.conjMixed K
      (InfiniteAdeleRing.ringEquiv_mixedSpace K b.inv) * DedekindZeta.Theta.conjMixed K z =
      DedekindZeta.Theta.conjMixed K (InfiniteAdeleRing.ringEquiv_mixedSpace K b.inv * z) := by
    apply Prod.ext
    . funext w
      simp only [Prod.fst_mul, Pi.mul_apply, DedekindZeta.Theta.conjMixed_fst]
    . funext w
      simp only [Prod.snd_mul, Pi.mul_apply, DedekindZeta.Theta.conjMixed_snd, map_mul]
  rw [hc]


private abbrev AdelicFinite (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

variable [MeasurableSpace (AdelicFinite K)] [BorelSpace (AdelicFinite K)]

/-- Poisson summation for simultaneous finite and infinite idele translates, with both idelic norm factors. -/
theorem tsum_heckeTateTest_ideleDilation_eq_fourier
    (chi : UnitaryHeckeCharacter K) (a : Units (InfiniteAdeleRing K))
    (b : Units (AdelicFinite K)) (f : SchwartzMap (Minkowski K) Complex) :
    tsum (fun x : K =>
      f (heckeInfiniteIdeleDilation a (DedekindZeta.Theta.eEmb K x)) *
        heckeFiniteAdditiveTateTest chi (algebraMap K (AdelicFinite K) x * (b : AdelicFinite K))) =
      tsum (fun t : K =>
        Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
          ((Inv.inv (heckeInfiniteIdeleNorm a) : Real) : Complex) *
          ((heckeFiniteIdeleNorm (Inv.inv b) : Real) : Complex) *
          (FourierTransform.fourier (f : Minkowski K -> Complex) : Minkowski K -> Complex)
            (DedekindZeta.Theta.toMinkowski K (DedekindZeta.Theta.conjMixed K
              (InfiniteAdeleRing.ringEquiv_mixedSpace K a.inv * mixedEmbedding K t))) *
          heckeFiniteFourierIntegral heckeFiniteAdeleHaar (heckeFiniteAdditiveTateTest chi)
            (algebraMap K (AdelicFinite K) (-t) * b.inv)) := by
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv Complex (heckeInfiniteIdeleDilation a) f
  have hF (w : Minkowski K) : F w = f (heckeInfiniteIdeleDilation a w) := by
    simp only [F, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  have hFfun : (F : Minkowski K -> Complex) = fun w => f (heckeInfiniteIdeleDilation a w) :=
    funext hF
  have hL :
      tsum (fun x : K =>
        f (heckeInfiniteIdeleDilation a (DedekindZeta.Theta.eEmb K x)) *
          heckeFiniteAdditiveTateTest chi (algebraMap K (AdelicFinite K) x * (b : AdelicFinite K))) =
      tsum (fun x : K => F (DedekindZeta.Theta.eEmb K x) *
          heckeFiniteAdditiveTateTest chi (algebraMap K (AdelicFinite K) x * (b : AdelicFinite K))) :=
    tsum_congr (fun x => by rw [hF])
  rw [hL, tsum_heckeFiniteAdditiveTateTest_translate_eq_fourierIntegral chi b F]
  apply tsum_congr
  intro t
  dsimp only
  have hY : DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t) =
      DedekindZeta.Theta.toMinkowski K (DedekindZeta.Theta.conjMixed K (mixedEmbedding K t)) := by
    rw [DedekindZeta.Theta.conjMink_apply]
    change DedekindZeta.Theta.toMinkowski K (DedekindZeta.Theta.conjMixed K
      ((DedekindZeta.Theta.toMinkowski K).symm
        (DedekindZeta.Theta.toMinkowski K (mixedEmbedding K t)))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hFinite :
      integral heckeFiniteAdeleHaar (fun z : AdelicFinite K =>
        heckeFiniteAdditiveTateTest chi (z * (b : AdelicFinite K)) *
          (heckeFiniteAdelePrincipalChar (-t) z : Complex)) =
      heckeFiniteFourierIntegral heckeFiniteAdeleHaar
        (fun z : AdelicFinite K => heckeFiniteAdditiveTateTest chi (z * (b : AdelicFinite K)))
        (algebraMap K (AdelicFinite K) (-t)) := rfl
  let : LocallyCompactSpace (AdelicFinite K) := locallyCompactSpace_heckeFiniteAdeles
  let : (heckeFiniteAdeleHaar (K := K)).IsAddHaarMeasure := by
    unfold heckeFiniteAdeleHaar
    infer_instance
  let : (heckeFiniteAdeleHaar (K := K)).Regular := by
    unfold heckeFiniteAdeleHaar
    infer_instance
  rw [hFfun, hY, hFinite, fourier_heckeInfiniteIdeleDilation_traceFrequency,
    heckeFiniteFourierIntegral_translate_ideleNorm]
  simp only [Complex.real_smul, smul_eq_mul]
  ring

end Robin1984.GRH
