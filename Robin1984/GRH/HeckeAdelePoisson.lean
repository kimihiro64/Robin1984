import Robin1984.GRH.HeckeAdeleHaar

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Poisson summation for a Schwartz function on the archimedean adeles and one finite adelic coset.
- Formalization note: Identifies the principal points of the coset with an ideal lattice and uses the actual finite adelic character in the trace-dual sum.
- PROVENANCE-END
-/

/-!
# Poisson summation on a finite adelic coset

For a number field, restricting principal points to a single finite adele
coset produces a translate of an ideal lattice in the archimedean space.
Lattice Poisson summation gives the trace-dual sum. The phase is the
canonical additive character of the finite adele at the negative
principal frequency. The same sum is expressed as the archimedean Fourier
transform times the finite Haar Fourier integral over the coset.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform

variable {K : Type*} [Field K] [NumberField K]

private abbrev HeckeFiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

/-- A principal point is in the given coset of the scaled integral finite adeles. -/
def InFiniteAdelePrincipalCoset (a : HeckeFiniteAdeles K) (d x : K) : Prop :=
  forall p : HeightOneSpectrum (RingOfIntegers K),
    Membership.mem (p.adicCompletionIntegers K)
      ((a p - algebraMap K (p.adicCompletion K) x) / algebraMap K (p.adicCompletion K) d)

/-- Subtracting one principal representative of a finite adelic coset
identifies its principal points with the associated global ideal. -/
theorem finiteAdelePrincipalCoset_iff_sub_mem_ideal
    (a : HeckeFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (x0 x : K) (hx0 : InFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d) x0) :
    InFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d) x <->
      Membership.mem
        ((Ideal.span ({d} : Set (RingOfIntegers K)) : Ideal (RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K) (x - x0) := by
  let R := RingOfIntegers K
  let dd := algebraMap R K d
  let I : Ideal R := Ideal.span {d}
  have hn : Not (dd = 0) :=
    (map_ne_zero_iff (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)).mpr hd
  have hI (y : K) :
      Membership.mem (I : FractionalIdeal (nonZeroDivisors R) K) y <->
        Exists (fun b : R => y = dd * algebraMap R K b) := by
    rw [FractionalIdeal.mem_coeIdeal]
    constructor
    case mp =>
      intro hy
      choose b hb using hy
      have ht : Dvd.dvd d b := Ideal.mem_span_singleton.mp hb.1
      choose c hc using ht
      refine Exists.intro c ?_
      rw [<- hb.2, hc, map_mul]
    case mpr =>
      intro hy
      choose b hb using hy
      refine Exists.intro (d * b) (And.intro ?_ ?_)
      case refine_1 =>
        exact Ideal.mem_span_singleton.mpr (Dvd.intro b rfl)
      case refine_2 =>
        rw [map_mul, <- hb]
  rw [hI, <- principal_mem_finiteAdele_modulus_iff (x - x0) dd hn]
  constructor
  case mp =>
    intro hx p
    have hm := sub_mem (hx0 p) (hx p)
    rw [<- sub_div, sub_sub_sub_cancel_left, <- map_sub] at hm
    exact hm
  case mpr =>
    intro h p
    have hm := sub_mem (hx0 p) (h p)
    rw [<- sub_div, map_sub, sub_sub_sub_cancel_right] at hm
    exact hm

/-- The principal sum in a single finite adelic coset is the periodisation
of the archimedean Schwartz function over the corresponding ideal lattice. -/
theorem tsum_finiteAdelePrincipalCoset_eq_periodisation
    (a : HeckeFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (x0 : K) (hx0 : InFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d) x0)
    (f : SchwartzMap (DedekindZeta.Theta.minkowskiSpace K) Complex) :
    tsum (fun x : Subtype (InFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d)) =>
      f (DedekindZeta.Theta.eEmb K x.val)) =
    DedekindZeta.PoissonSummation.periodisation
      (DedekindZeta.Theta.idealLattice K
        (Ideal.span ({d} : Set (RingOfIntegers K)) : Ideal (RingOfIntegers K))) f
      (DedekindZeta.Theta.eEmb K x0) := by
  let R := RingOfIntegers K
  let I : FractionalIdeal (nonZeroDivisors R) K := (Ideal.span ({d} : Set R) : Ideal R)
  let C := Subtype (InFiniteAdelePrincipalCoset a (algebraMap R K d))
  let D := (I : Submodule R K)
  let phi : Equiv C D :=
    { toFun := fun x => Subtype.mk (x.val - x0)
        ((finiteAdelePrincipalCoset_iff_sub_mem_ideal a d hd x0 x.val hx0).mp x.property)
      invFun := fun y => Subtype.mk (y.val + x0) (by
        apply (finiteAdelePrincipalCoset_iff_sub_mem_ideal a d hd x0 (y.val + x0) hx0).mpr
        rw [add_sub_cancel_right]
        exact y.property)
      left_inv := fun x => Subtype.ext (sub_add_cancel x.val x0)
      right_inv := fun y => Subtype.ext (add_sub_cancel_right y.val x0) }
  let E := DedekindZeta.Theta.idealLatticeEquiv K I
  have hJ : Not ((Ideal.span ({d} : Set R) : Ideal R) = 0) :=
    fun h => hd (Ideal.span_singleton_eq_bot.mp h)
  have hI : Not (I = 0) := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  let : DiscreteTopology (DedekindZeta.Theta.idealLattice K I) :=
    DedekindZeta.Theta.discreteTopology_idealLattice K I hI
  let : IsZLattice Real (DedekindZeta.Theta.idealLattice K I) :=
    DedekindZeta.Theta.isZLattice_idealLattice K I hI
  rw [DedekindZeta.PoissonSummation.periodisation_apply (DedekindZeta.Theta.idealLattice K I),
    <- E.tsum_eq, <- phi.symm.tsum_eq (fun x : C => f (DedekindZeta.Theta.eEmb K x.val))]
  apply tsum_congr
  intro y
  change f (DedekindZeta.Theta.eEmb K (y.val + x0)) =
    f (DedekindZeta.Theta.eEmb K x0 + DedekindZeta.Theta.eEmb K y.val)
  have he := map_add (DedekindZeta.Theta.eEmbHom K) y.val x0
  rw [DedekindZeta.Theta.eEmbHom_apply, DedekindZeta.Theta.eEmbHom_apply,
    DedekindZeta.Theta.eEmbHom_apply] at he
  rw [he, add_comm]

/-- Poisson summation for principal points in a finite adelic coset. The
dual sum runs over the global trace-dual ideal. -/
theorem tsum_finiteAdelePrincipalCoset_eq_traceDualFourier
    (a : HeckeFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (x0 : K) (hx0 : InFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d) x0)
    (f : SchwartzMap (DedekindZeta.Theta.minkowskiSpace K) Complex) :
    let I := Ideal.span ({d} : Set (RingOfIntegers K))
    tsum (fun x : Subtype (InFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d)) =>
      f (DedekindZeta.Theta.eEmb K x.val)) =
    tsum (fun w : (DedekindZeta.Theta.dualIdeal K I : Submodule (RingOfIntegers K) K) =>
      let y := DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K w.val)
      (Real.fourierChar (inner Real (DedekindZeta.Theta.eEmb K x0) y) : Complex) *
        (Inv.inv (DedekindZeta.Theta.covolume K I : Complex) *
          FourierTransform.fourier (f : DedekindZeta.Theta.minkowskiSpace K -> Complex) y)) := by
  let R := RingOfIntegers K
  let I : Ideal R := Ideal.span ({d} : Set R)
  let I' : FractionalIdeal (nonZeroDivisors R) K := I
  let V := DedekindZeta.Theta.minkowskiSpace K
  let L := DedekindZeta.Theta.idealLattice K I'
  have hI : Not (I = 0) := fun h => hd (Ideal.span_singleton_eq_bot.mp h)
  have hI' : Not (I' = 0) := FractionalIdeal.coeIdeal_ne_zero.mpr hI
  let : DiscreteTopology L := DedekindZeta.Theta.discreteTopology_idealLattice K I' hI'
  let : IsZLattice Real L := DedekindZeta.Theta.isZLattice_idealLattice K I' hI'
  let Id := DedekindZeta.Theta.dualIdeal K I
  let Ld := DedekindZeta.Theta.idealLattice K Id
  let c := (DedekindZeta.Theta.conjMink K).toLinearEquiv.restrictScalars Int
  have hDual : DedekindZeta.PoissonSummation.dualLattice L = Ld.map c.toLinearMap :=
    DedekindZeta.Theta.dualLattice_idealLattice K I hI
  let E1 := DedekindZeta.Theta.idealLatticeEquiv K Id
  let E2 := Submodule.equivMapOfInjective c.toLinearMap c.injective Ld
  let E3 := Equiv.setCongr
    (congrArg (fun S : Submodule Int V => (S : Set V)) hDual.symm)
  let E : Equiv (Id : Submodule R K) (DedekindZeta.PoissonSummation.dualLattice L) :=
    E1.trans (E2.toEquiv.trans E3)
  dsimp only
  rw [tsum_finiteAdelePrincipalCoset_eq_periodisation a d hd x0 hx0 f,
    DedekindZeta.PoissonSummation.periodisation_eq_tsum_fourier L f,
    DedekindZeta.Theta.covolume_idealLattice K I hI, <- E.tsum_eq]
  apply tsum_congr
  intro w
  change
    (Real.fourierChar (inner Real (DedekindZeta.Theta.eEmb K x0)
        (DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K w.val))) : Complex) *
      (Inv.inv (DedekindZeta.Theta.covolume K I : Complex) *
        FourierTransform.fourier (f : V -> Complex)
          (DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K w.val))) = _
  rfl

/-- The Minkowski inner product with the conjugate of a principal
frequency is the rational field trace pairing. -/
theorem inner_eEmb_conjMink_eq_trace (x t : K) :
    inner Real (DedekindZeta.Theta.eEmb K x)
      (DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t)) =
      (Algebra.trace Rat K (t * x) : Real) := by
  open DedekindZeta.Theta in
  have hTrace : traceForm K (mixedEmbedding K t) x =
      (Algebra.trace Rat K (t * x) : Real) := by
    rw [traceForm_mixedEmbedding]
    exact RingHom.congr_fun
      (Subsingleton.elim (algebraMap Rat Real) (Rat.castHom Real)) _
  rw [<- hTrace, real_inner_comm, DedekindZeta.Theta.conjMink_apply]
  change inner Real (DedekindZeta.Theta.toMinkowski K (DedekindZeta.Theta.conjMixed K
    ((DedekindZeta.Theta.toMinkowski K).symm
      (DedekindZeta.Theta.toMinkowski K (mixedEmbedding K t)))))
    (DedekindZeta.Theta.eEmb K x) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  let u := DedekindZeta.Theta.conjMixed K (mixedEmbedding K t)
  open DedekindZeta.Theta in
  change inner Real (toMinkowski K u) (eEmb K x) = traceForm K (mixedEmbedding K t) x
  open DedekindZeta.Theta in
  rw [WithLp.prod_inner_apply,
    show (WithLp.ofLp (toMinkowski K u)).1 = WithLp.toLp 2 (scaleMixed K u).1 from rfl,
    show (WithLp.ofLp (eEmb K x)).1 =
      WithLp.toLp 2 (scaleMixed K (mixedEmbedding K x)).1 from rfl,
    show (WithLp.ofLp (toMinkowski K u)).2 = WithLp.toLp 2 (scaleMixed K u).2 from rfl,
    show (WithLp.ofLp (eEmb K x)).2 =
      WithLp.toLp 2 (scaleMixed K (mixedEmbedding K x)).2 from rfl, traceForm]
  open DedekindZeta.Theta in
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, scaleMixed,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_refl', id_eq,
    ContinuousLinearEquiv.smulLeft_apply_apply, real_inner_eq_re_inner Complex]
  rw [Finset.mul_sum]
  congr 1
  next =>
    exact Finset.sum_congr rfl (fun w _ => mul_comm _ _)
  next =>
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have hs : (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = ((2 : Real) : Complex) := by
      rw [<- Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    have hP : (HSMul.hSMul DedekindZeta.Theta.sqrtTwo (mixedEmbedding K x).2) w *
        starRingEnd Complex ((HSMul.hSMul DedekindZeta.Theta.sqrtTwo u.2) w) =
        ((2 : Real) : Complex) * ((mixedEmbedding K t).2 w * (mixedEmbedding K x).2 w) := by
      simp only [Pi.smul_apply, Units.smul_def, DedekindZeta.Theta.sqrtTwo,
        Units.val_mk0, Complex.real_smul, map_mul, Complex.conj_ofReal, u,
        DedekindZeta.Theta.conjMixed_snd, Complex.conj_conj]
      rw [<- hs]
      ring
    rw [hP]
    exact Complex.re_ofReal_mul _ _

private abbrev HeckeAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

/-- At a frequency in the trace-dual ideal, the finite character of a
coset equals the character of any principal representative of the coset. -/
theorem heckeAdeleAddChar_finiteCoset_eq
    (a : HeckeFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (x0 : K) (hx0 : InFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d) x0)
    (t : K) (ht : Membership.mem
      (DedekindZeta.Theta.dualIdeal K (Ideal.span ({d} : Set (RingOfIntegers K))) :
        Submodule (RingOfIntegers K) K) t) :
    heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K)
      (a * algebraMap K (HeckeFiniteAdeles K) t) : HeckeAdeles K) =
      Real.fourierChar (-(Algebra.trace Rat K (x0 * t) : Real)) := by
  let R := RingOfIntegers K
  let A := HeckeFiniteAdeles K
  let q := algebraMap K A
  let dd := algebraMap R K d
  have hdK : Not (dd = 0) :=
    (map_ne_zero_iff (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)).mpr hd
  have hInv : Inv.inv dd * dd = 1 := by field_simp [hdK]
  let b := (a - q x0) * q (Inv.inv dd)
  have hb : forall p : HeightOneSpectrum R,
      Membership.mem (p.adicCompletionIntegers K) (b p) := by
    intro p
    let e := algebraMap K (p.adicCompletion K)
    have he := (map_ne_zero_iff e e.injective).mpr hdK
    have hDiv : e (Inv.inv dd) = 1 / e dd := by
      apply (eq_div_iff he).2
      rw [<- map_mul, hInv, map_one]
    change Membership.mem (p.adicCompletionIntegers K)
      ((a p - e x0) * e (Inv.inv dd))
    rw [hDiv, one_div, <- div_eq_mul_inv]
    exact hx0 p
  have hProd : b * q (dd * t) = (a - q x0) * q t := by
    have hEq : Inv.inv dd * (dd * t) = t := by rw [<- mul_assoc, hInv, one_mul]
    rw [show b = (a - q x0) * q (Inv.inv dd) from rfl, mul_assoc, <- map_mul, hEq]
  let F (z : A) : HeckeAdeles K := Prod.mk 0 z
  have hDifference : F (a * q t) - F (q x0 * q t) = F ((a - q x0) * q t) := by
    change Prod.mk ((0 : InfiniteAdeleRing K) - 0) (a * q t - q x0 * q t) =
      Prod.mk 0 ((a - q x0) * q t)
    rw [sub_self, sub_mul]
  have hGood := (heckeAdeleAddChar_finitePrincipalIdeal_annihilator_iff d hd t).mpr ht b hb
  have hSame : heckeAdeleAddChar (F (a * q t)) = heckeAdeleAddChar (F (q x0 * q t)) := by
    apply eq_of_div_eq_one
    rw [<- AddChar.map_sub_eq_div, hDifference, <- hProd]
    exact hGood
  have hRep : forall p : HeightOneSpectrum R,
      Membership.mem (p.adicCompletionIntegers K)
        ((q x0 * q t) p - algebraMap K (p.adicCompletion K) (x0 * t)) := by
    intro p
    let e := algebraMap K (p.adicCompletion K)
    change Membership.mem (p.adicCompletionIntegers K) (e x0 * e t - e (x0 * t))
    rw [map_mul, sub_self]
    exact (p.adicCompletionIntegers K).zero_mem
  exact hSame.trans (heckeAdeleAddChar_finitePart_eq_of_representative (q x0 * q t) (x0 * t) hRep)

/-- Poisson summation on the principal points in one finite adelic coset.
The phase on the dual side is the actual finite adele character at the
negative frequency. -/
theorem tsum_finiteAdelePrincipalCoset_eq_adelicFourier
    (a : HeckeFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (DedekindZeta.Theta.minkowskiSpace K) Complex) :
    let I := Ideal.span ({d} : Set (RingOfIntegers K))
    tsum (fun x : Subtype (InFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d)) =>
      f (DedekindZeta.Theta.eEmb K x.val)) =
    tsum (fun w : (DedekindZeta.Theta.dualIdeal K I : Submodule (RingOfIntegers K) K) =>
      let y := DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K w.val)
      ((heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K)
        (a * algebraMap K (HeckeFiniteAdeles K) (-w.val)) : HeckeAdeles K)) : Complex) *
        (Inv.inv (DedekindZeta.Theta.covolume K I : Complex) *
          FourierTransform.fourier (f : DedekindZeta.Theta.minkowskiSpace K -> Complex) y)) := by
  let R := RingOfIntegers K
  let e := algebraMap R K
  have hD : Not (e d = 0) :=
    (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective R K)).mpr hd
  choose x0 hx0 using exists_finiteAdele_sub_principal_modulus a (e d) hD
  change InFiniteAdelePrincipalCoset a (e d) x0 at hx0
  dsimp only
  rw [tsum_finiteAdelePrincipalCoset_eq_traceDualFourier a d hd x0 hx0 f]
  apply tsum_congr
  intro w
  have hNeg : Membership.mem
      (DedekindZeta.Theta.dualIdeal K (Ideal.span ({d} : Set R)) : Submodule R K) (-w.val) :=
    neg_mem w.property
  have hPhase := heckeAdeleAddChar_finiteCoset_eq a d hd x0 hx0 (-w.val) hNeg
  dsimp only
  rw [hPhase, inner_eEmb_conjMink_eq_trace, mul_neg, map_neg (Algebra.trace Rat K),
    Rat.cast_neg, neg_neg, mul_comm x0 w.val]

variable [MeasurableSpace (HeckeFiniteAdeles K)] [BorelSpace (HeckeFiniteAdeles K)]

/-- Poisson summation for a Schwartz function on the archimedean adeles
and the indicator of one principal coset on the finite adeles. The
archimedean Fourier transform has the trace pairing and the factor
`1 / sqrt |discr K|` for this choice of finite Haar measure. -/
theorem tsum_finiteAdelePrincipalCoset_eq_fourierIntegral
    (a : HeckeFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (DedekindZeta.Theta.minkowskiSpace K) Complex) :
    let D := heckeScaledIntegralFiniteAdeles (algebraMap (RingOfIntegers K) K d)
    let C := Set.image (fun z : HeckeFiniteAdeles K => a + z) (D : Set (HeckeFiniteAdeles K))
    tsum (fun x : Subtype (InFiniteAdelePrincipalCoset a (algebraMap (RingOfIntegers K) K d)) =>
      f (DedekindZeta.Theta.eEmb K x.val)) =
      tsum (fun t : K =>
        let y := DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t)
        Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex) *
          FourierTransform.fourier (f : DedekindZeta.Theta.minkowskiSpace K -> Complex) y *
          integral (heckeFiniteAdeleHaar.restrict C) (fun z => (heckeFiniteAdelePrincipalChar (-t) z : Complex))) := by
  let R := RingOfIntegers K
  let I := Ideal.span ({d} : Set R)
  let Q := (DedekindZeta.Theta.dualIdeal K I : Submodule R K)
  let D := heckeScaledIntegralFiniteAdeles (algebraMap R K d)
  let C := Set.image (fun z : HeckeFiniteAdeles K => a + z) (D : Set (HeckeFiniteAdeles K))
  let r : Complex := Real.sqrt (abs (NumberField.discr K : Real))
  let n : Complex := Ideal.absNorm I
  let F (t : K) := FourierTransform.fourier (f : DedekindZeta.Theta.minkowskiSpace K -> Complex)
    (DedekindZeta.Theta.conjMink K (DedekindZeta.Theta.eEmb K t))
  let phase (t : K) : Complex := heckeFiniteAdelePrincipalChar (-t) a
  let G (t : K) : Complex := phase t * (Inv.inv (DedekindZeta.Theta.covolume K I : Complex) * F t)
  have hCov : Inv.inv (DedekindZeta.Theta.covolume K I : Complex) = Inv.inv n * Inv.inv r := by
    change Inv.inv (Complex.ofReal ((Ideal.absNorm I : Real) *
      Real.sqrt (abs (NumberField.discr K : Real)))) = _
    rw [Complex.ofReal_mul, Complex.ofReal_natCast]
    change Inv.inv (n * r) = Inv.inv n * Inv.inv r
    by_cases hn : n = 0
    case pos => simp only [hn, zero_mul, inv_zero]
    case neg =>
      by_cases hr : r = 0
      case pos => simp only [hr, mul_zero, inv_zero]
      case neg => field_simp [hn, hr]
  have hSum := tsum_finiteAdelePrincipalCoset_eq_adelicFourier a d hd f
  change _ = tsum (fun t : Subtype (Q : Set K) => G t.val) at hSum
  dsimp only
  rw [hSum]
  refine (tsum_subtype (Q : Set K) G).trans ?_
  apply tsum_congr
  intro t
  change (Q : Set K).indicator G t =
    Inv.inv r * F t *
      integral (heckeFiniteAdeleHaar.restrict C) (fun z => (heckeFiniteAdelePrincipalChar (-t) z : Complex))
  rw [integral_heckeFiniteAdeleHaar_principalCoset a d hd (-t)]
  have hNeg : Membership.mem Q (-t) <-> Membership.mem Q t := by
    constructor
    case mp =>
      intro ht
      simpa only [neg_neg] using Q.neg_mem ht
    case mpr => exact Q.neg_mem
  by_cases ht : Membership.mem Q t
  case pos =>
    rw [Set.indicator_of_mem ht, if_pos (hNeg.mpr ht)]
    change phase t * (Inv.inv (DedekindZeta.Theta.covolume K I : Complex) * F t) =
      Inv.inv r * F t * (phase t * Inv.inv n)
    rw [hCov]
    ring
  case neg =>
    rw [Set.indicator_of_notMem ht, if_neg (fun h => ht (hNeg.mp h)), mul_zero]

end Robin1984.GRH
