import Robin1984.GRH.GodementJacquetProductLattice
import Robin1984.GRH.HeckeAdelePoisson

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Poisson summation on the additive adelic matrix space in Godement and Jacquet, Zeta Functions of Simple Algebras.
- Formalization note: Proves Poisson summation for finite adelic rectangles and arbitrary archimedean Schwartz functions, with the trace-dual ideal and the exact discriminant normalization.
- PROVENANCE-END
-/

/-!
# Poisson summation for finite adelic rectangles

A principal point in the finite rectangle determines a translate of a
product ideal lattice. Shifted Poisson summation allows the archimedean
Schwartz function to depend jointly on all coordinates. On the dual side
each finite character integral vanishes off the trace-dual ideal.

The finite additive Haar measure assigns mass one to the integral
finite adeles. Each coordinate contributes the inverse square root of
the absolute discriminant to the normalized Fourier integral.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical nonZeroDivisors RealInnerProductSpace FourierTransform

variable (K : Type*) [Field K] [NumberField K] (I : Type*) [Fintype I]

private abbrev VecFiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev ArchCoordinate (K : Type*) [Field K] :=
  DedekindZeta.Theta.minkowskiSpace K

local instance : SecondCountableTopology (ArchCoordinate K) :=
  (DedekindZeta.Theta.toMinkowski K).symm.toHomeomorph.isEmbedding.secondCountableTopology

local instance : BorelSpace (PiLp 2 (fun _ : I => ArchCoordinate K)) := by
  let h : forall _ : I, BorelSpace (ArchCoordinate K) := fun _ => inferInstance
  let t : forall _ : I, SecondCountableTopology (ArchCoordinate K) := fun _ => inferInstance
  exact PiLp.borelSpace (p := 2) (X := fun _ : I => ArchCoordinate K)

/-- The weighted Minkowski embedding in each vector coordinate. -/
def heckePrincipalMinkowskiVector (x : I -> K) :
    PiLp 2 (fun _ : I => ArchCoordinate K) :=
  WithLp.toLp 2 (fun i => DedekindZeta.Theta.eEmb K (x i))

/-- The archimedean conjugation that turns the Euclidean pairing into
the field trace pairing, applied to each vector coordinate. -/
def heckeConjMinkowskiVector (x : PiLp 2 (fun _ : I => ArchCoordinate K)) :
    PiLp 2 (fun _ : I => ArchCoordinate K) :=
  WithLp.toLp 2 (fun i => DedekindZeta.Theta.conjMink K (x i))

theorem inner_heckePrincipalMinkowskiVector_conj_eq_trace_sum (x t : I -> K) :
    inner Real (heckePrincipalMinkowskiVector K I x)
      (heckeConjMinkowskiVector K I (heckePrincipalMinkowskiVector K I t)) =
      Finset.univ.sum (fun i => (Algebra.trace Rat K (t i * x i) : Real)) := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => inner_eEmb_conjMink_eq_trace (x i) (t i))

private def vectorProductLatticeEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (L : Submodule Int E) : Equiv (I -> L) (euclideanProductZLattice I L) where
  toFun x := Subtype.mk (WithLp.toLp 2 (fun i => (x i).val))
    ((mem_euclideanProductZLattice I L _).mpr (fun i => (x i).property))
  invFun x i := Subtype.mk (x.val i)
    ((mem_euclideanProductZLattice I L _).mp x.property i)
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact WithLp.toLp_ofLp 2 x.val

/-- Periodisation over the product ideal lattice for a finite adelic
rectangle with a common nonzero denominator. -/
private theorem principalVectorCosetSummable_periodisation
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (x0 : I -> K)
    (hx0 : forall i, InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x0 i))
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) :
    let C := Subtype (fun x : I -> K => forall i,
      InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x i))
    let U := fun x : C => f (heckePrincipalMinkowskiVector K I x.val)
    And (Summable U) (tsum U =
      DedekindZeta.PoissonSummation.periodisation
        (euclideanProductZLattice I (DedekindZeta.Theta.idealLattice K
          (Ideal.span (Set.singleton d) : Ideal (RingOfIntegers K)))) f
        (heckePrincipalMinkowskiVector K I x0)) := by
  let R := RingOfIntegers K
  let J : FractionalIdeal (nonZeroDivisors R) K := (Ideal.span (Set.singleton d) : Ideal R)
  let M := (J : Submodule R K)
  let L := DedekindZeta.Theta.idealLattice K J
  let C := Subtype (fun x : I -> K => forall i,
    InFiniteAdelePrincipalCoset (a i) (algebraMap R K d) (x i))
  let P : Equiv C (I -> M) :=
    { toFun := fun x i => Subtype.mk (x.val i - x0 i)
        ((finiteAdelePrincipalCoset_iff_sub_mem_ideal (a i) d hd (x0 i) (x.val i) (hx0 i)).mp
          (x.property i))
      invFun := fun y => Subtype.mk (fun i => (y i).val + x0 i) (by
        intro i
        apply (finiteAdelePrincipalCoset_iff_sub_mem_ideal (a i) d hd (x0 i) _ (hx0 i)).mpr
        rw [add_sub_cancel_right]
        exact (y i).property)
      left_inv := fun x => Subtype.ext (funext (fun i => sub_add_cancel (x.val i) (x0 i)))
      right_inv := fun y => funext (fun i => Subtype.ext (add_sub_cancel_right (y i).val (x0 i))) }
  let E : Equiv (I -> M) (I -> L) :=
    Equiv.piCongrRight (fun _ : I => DedekindZeta.Theta.idealLatticeEquiv K J)
  let Q := E.trans (vectorProductLatticeEquiv I L)
  have hJ : Not ((Ideal.span (Set.singleton d) : Ideal R) = 0) :=
    fun he => hd (Ideal.span_singleton_eq_bot.mp he)
  have hI : Not (J = 0) := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  let : DiscreteTopology L := DedekindZeta.Theta.discreteTopology_idealLattice K J hI
  let : IsZLattice Real L := DedekindZeta.Theta.isZLattice_idealLattice K J hI
  let F := P.trans Q
  let xA := heckePrincipalMinkowskiVector K I x0
  let G (y : euclideanProductZLattice I L) : Complex := f (xA + y.val)
  have hS : Summable G :=
    DedekindZeta.PoissonSummation.summable_periodisation (euclideanProductZLattice I L) f xA
  have hF (x : C) : G (F x) = f (heckePrincipalMinkowskiVector K I x.val) := by
    change f (xA + (F x).val) = f (heckePrincipalMinkowskiVector K I x.val)
    apply congrArg (f : PiLp 2 (fun _ : I => ArchCoordinate K) -> Complex)
    apply (PiLp.continuousLinearEquiv 2 Real (fun _ : I => ArchCoordinate K)).injective
    funext i
    change DedekindZeta.Theta.eEmb K (x0 i) + DedekindZeta.Theta.eEmb K (x.val i - x0 i) =
      DedekindZeta.Theta.eEmb K (x.val i)
    have he := map_add (DedekindZeta.Theta.eEmbHom K) (x0 i) (x.val i - x0 i)
    rw [add_comm (x0 i), sub_add_cancel] at he
    simpa only [DedekindZeta.Theta.eEmbHom_apply] using he.symm
  constructor
  . exact (F.summable_iff.mpr hS).congr hF
  . calc
      _ = tsum (fun x : C => G (F x)) := tsum_congr (fun x => (hF x).symm)
      _ = tsum G := F.tsum_eq G
      _ = _ := (DedekindZeta.PoissonSummation.periodisation_apply
        (euclideanProductZLattice I L) f xA).symm

/-- The principal Schwartz sum is absolutely convergent. -/
theorem summable_finiteAdelePrincipalVectorCoset
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (x0 : I -> K)
    (hx0 : forall i, InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x0 i))
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) :
    Summable (fun x : Subtype (fun x : I -> K => forall i,
      InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x i)) =>
        f (heckePrincipalMinkowskiVector K I x.val)) :=
  (principalVectorCosetSummable_periodisation K I a d hd x0 hx0 f).1

/-- The principal Schwartz sum is the shifted lattice periodisation. -/
theorem tsum_finiteAdelePrincipalVectorCoset_eq_periodisation
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (x0 : I -> K)
    (hx0 : forall i, InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x0 i))
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) :
    tsum (fun x : Subtype (fun x : I -> K => forall i,
      InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x i)) =>
        f (heckePrincipalMinkowskiVector K I x.val)) =
      DedekindZeta.PoissonSummation.periodisation
        (euclideanProductZLattice I (DedekindZeta.Theta.idealLattice K
          (Ideal.span (Set.singleton d) : Ideal (RingOfIntegers K)))) f
        (heckePrincipalMinkowskiVector K I x0) :=
  (principalVectorCosetSummable_periodisation K I a d hd x0 hx0 f).2

set_option maxHeartbeats 1000000 in
/-- The shifted Poisson formula for a finite adelic rectangle, with
frequencies indexed by vectors in the field trace-dual ideal. -/
private theorem principalVectorCosetSummable_traceDualFourier
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (x0 : I -> K)
    (hx0 : forall i, InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x0 i))
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) :
    let J := Ideal.span (Set.singleton d)
    let U := fun t : I -> (DedekindZeta.Theta.dualIdeal K J : Submodule (RingOfIntegers K) K) =>
      let y := heckeConjMinkowskiVector K I (heckePrincipalMinkowskiVector K I (fun i => (t i).val))
      (Real.fourierChar (inner Real (heckePrincipalMinkowskiVector K I x0) y) : Complex) *
        (Inv.inv (((DedekindZeta.Theta.covolume K J) ^ Fintype.card I : Real) : Complex) *
          FourierTransform.fourier (f : PiLp 2 (fun _ : I => ArchCoordinate K) -> Complex) y)
    And (Summable U) (tsum (fun x : Subtype (fun x : I -> K => forall i,
      InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x i)) =>
        f (heckePrincipalMinkowskiVector K I x.val)) = tsum U) := by
  let R := RingOfIntegers K
  let J : Ideal R := Ideal.span (Set.singleton d)
  let J' : FractionalIdeal (nonZeroDivisors R) K := J
  let L := DedekindZeta.Theta.idealLattice K J'
  have hJ : Not (J = 0) := fun h => hd (Ideal.span_singleton_eq_bot.mp h)
  have hJ' : Not (J' = 0) := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  let : DiscreteTopology L := DedekindZeta.Theta.discreteTopology_idealLattice K J' hJ'
  let : IsZLattice Real L := DedekindZeta.Theta.isZLattice_idealLattice K J' hJ'
  let D := DedekindZeta.Theta.dualIdeal K J
  let c := (DedekindZeta.Theta.conjMink K).toLinearEquiv.restrictScalars Int
  let Ld := DedekindZeta.Theta.idealLattice K D
  have hDual : DedekindZeta.PoissonSummation.dualLattice L = Ld.map c.toLinearMap :=
    DedekindZeta.Theta.dualLattice_idealLattice K J hJ
  let E1 := DedekindZeta.Theta.idealLatticeEquiv K D
  let E2 := Submodule.equivMapOfInjective c.toLinearMap c.injective Ld
  let E3 := Equiv.setCongr
    (congrArg (fun S : Submodule Int (ArchCoordinate K) => (S : Set (ArchCoordinate K))) hDual.symm)
  let E := E1.trans (E2.toEquiv.trans E3)
  let Eprod := (Equiv.piCongrRight (fun _ : I => E)).trans
    (vectorProductLatticeEquiv I (DedekindZeta.PoissonSummation.dualLattice L))
  constructor
  . have hSum := DedekindZeta.PoissonSummation.summable_periodisation_fourier
      (euclideanProductZLattice I L) f (heckePrincipalMinkowskiVector K I x0)
    rw [dualLattice_euclideanProductZLattice I L,
      covolume_euclideanProductZLattice I L (Module.finBasis Int L),
      DedekindZeta.Theta.covolume_idealLattice K J hJ] at hSum
    simp only [Circle.smul_def, smul_eq_mul] at hSum
    exact Eprod.summable_iff.mpr hSum
  . dsimp only
    rw [tsum_finiteAdelePrincipalVectorCoset_eq_periodisation K I a d hd x0 hx0 f]
    rw [DedekindZeta.PoissonSummation.periodisation_apply,
      poisson_euclideanProductZLattice I L (Module.finBasis Int L) f,
      DedekindZeta.Theta.covolume_idealLattice K J hJ, <- Eprod.tsum_eq]
    rfl

/-- Shifted adelic rectangle Poisson summation over the trace-dual ideal. -/
theorem tsum_finiteAdelePrincipalVectorCoset_eq_traceDualFourier
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (x0 : I -> K)
    (hx0 : forall i, InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x0 i))
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) :
    let J := Ideal.span (Set.singleton d)
    tsum (fun x : Subtype (fun x : I -> K => forall i,
      InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x i)) =>
        f (heckePrincipalMinkowskiVector K I x.val)) =
    tsum (fun t : I -> (DedekindZeta.Theta.dualIdeal K J : Submodule (RingOfIntegers K) K) =>
      let y := heckeConjMinkowskiVector K I (heckePrincipalMinkowskiVector K I (fun i => (t i).val))
      (Real.fourierChar (inner Real (heckePrincipalMinkowskiVector K I x0) y) : Complex) *
        (Inv.inv (((DedekindZeta.Theta.covolume K J) ^ Fintype.card I : Real) : Complex) *
          FourierTransform.fourier (f : PiLp 2 (fun _ : I => ArchCoordinate K) -> Complex) y)) :=
  (principalVectorCosetSummable_traceDualFourier K I a d hd x0 hx0 f).2

private theorem coe_addChar_finset_sum {A B : Type*} [AddCommMonoid A]
    (chi : AddChar A Circle) (s : Finset B) (v : B -> A) :
    (chi (s.sum v) : Complex) = s.prod (fun i => (chi (v i) : Complex)) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, AddChar.map_zero_eq_one, Circle.coe_one, Finset.prod_empty]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

variable [MeasurableSpace (VecFiniteAdeles K)] [BorelSpace (VecFiniteAdeles K)]

/-- The discriminant-normalized Fourier coefficient for a Schwartz
function on the archimedean product and a finite adelic rectangle. -/
def heckeAdeleVectorRectangleFourierIntegral
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K)
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) (t : I -> K) : Complex :=
  let y := heckeConjMinkowskiVector K I (heckePrincipalMinkowskiVector K I t)
  (Inv.inv (Real.sqrt (abs (NumberField.discr K : Real)) : Complex)) ^ Fintype.card I *
    FourierTransform.fourier (f : PiLp 2 (fun _ : I => ArchCoordinate K) -> Complex) y *
    Finset.univ.prod (fun i =>
      integral (heckeFiniteAdeleHaar.restrict
        (heckeFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d)))
        (fun z => (heckeFiniteAdelePrincipalChar (-(t i)) z : Complex)))

private def heckeAdeleVectorTraceDualFourierValue
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K)
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) (t : I -> K) : Complex :=
  let J := Ideal.span (Set.singleton d)
  let y := heckeConjMinkowskiVector K I (heckePrincipalMinkowskiVector K I t)
  (Finset.univ.prod (fun i => (heckeFiniteAdelePrincipalChar (-(t i)) (a i) : Complex))) *
    (Inv.inv (((DedekindZeta.Theta.covolume K J) ^ Fintype.card I : Real) : Complex) *
      FourierTransform.fourier (f : PiLp 2 (fun _ : I => ArchCoordinate K) -> Complex) y)

private theorem traceDualVector_indicator_eq_rectangleFourierIntegral
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) (t : I -> K) :
    let J := Ideal.span (Set.singleton d)
    let D := (DedekindZeta.Theta.dualIdeal K J : Submodule (RingOfIntegers K) K)
    let T : Set (I -> K) := fun v => forall i, Membership.mem D (v i)
    T.indicator (heckeAdeleVectorTraceDualFourierValue K I a d f) t =
      heckeAdeleVectorRectangleFourierIntegral K I a d f t := by
  let R := RingOfIntegers K
  let J : Ideal R := Ideal.span (Set.singleton d)
  let D := (DedekindZeta.Theta.dualIdeal K J : Submodule R K)
  let T : Set (I -> K) := fun v => forall i, Membership.mem D (v i)
  let c : Complex := Real.sqrt (abs (NumberField.discr K : Real))
  let n : Complex := Ideal.absNorm J
  let phase (i : I) : Complex := heckeFiniteAdelePrincipalChar (-(t i)) (a i)
  let value (i : I) : Complex := integral (heckeFiniteAdeleHaar.restrict
    (heckeFiniteAdelePrincipalCoset (a i) (algebraMap R K d)))
    (fun z => (heckeFiniteAdelePrincipalChar (-(t i)) z : Complex))
  have hValue (i : I) : value i =
      if Membership.mem D (t i) then phase i * Inv.inv n else 0 := by
    have hNeg : Membership.mem D (-(t i)) <-> Membership.mem D (t i) := by
      constructor
      case mp =>
        intro ht
        simpa only [neg_neg] using D.neg_mem ht
      case mpr => exact D.neg_mem
    exact (integral_heckeFiniteAdeleHaar_principalCoset (a i) d hd (-(t i))).trans
      (if_congr hNeg rfl rfl)
  have hCov : Inv.inv (((DedekindZeta.Theta.covolume K J) ^ Fintype.card I : Real) : Complex) =
      (Inv.inv c) ^ Fintype.card I * (Inv.inv n) ^ Fintype.card I := by
    change Inv.inv (Complex.ofReal (((Ideal.absNorm J : Real) *
      Real.sqrt (abs (NumberField.discr K : Real))) ^ Fintype.card I)) = _
    rw [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_natCast, <- inv_pow, mul_inv_rev, mul_pow]
  let F := FourierTransform.fourier (f : PiLp 2 (fun _ : I => ArchCoordinate K) -> Complex)
    (heckeConjMinkowskiVector K I (heckePrincipalMinkowskiVector K I t))
  change T.indicator (heckeAdeleVectorTraceDualFourierValue K I a d f) t =
    Inv.inv c ^ Fintype.card I * F * Finset.univ.prod value
  by_cases ht : Membership.mem T t
  case pos =>
    have hProd : Finset.univ.prod value =
        Finset.univ.prod phase * (Inv.inv n) ^ Fintype.card I := by
      calc
        Finset.univ.prod value =
            Finset.univ.prod (fun i => phase i * Inv.inv n) :=
          Finset.prod_congr rfl (fun i _ => (hValue i).trans (if_pos (ht i)))
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    rw [Set.indicator_of_mem ht, hProd]
    change Finset.univ.prod phase *
      (Inv.inv (((DedekindZeta.Theta.covolume K J) ^ Fintype.card I : Real) : Complex) * F) = _
    rw [hCov]
    ac_rfl
  case neg =>
    have hNot : Not (forall i, Membership.mem D (t i)) := ht
    choose i hi using not_forall.mp hNot
    have hz : value i = 0 := (hValue i).trans (if_neg hi)
    have hProd : Finset.univ.prod value = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [Set.indicator_of_notMem ht, hProd, mul_zero]

/-- Poisson summation for a Schwartz function on the archimedean
product multiplied by the indicator of a finite adelic rectangle. -/
private theorem principalVectorCosetSummable_fourierIntegral
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) :
    let V := heckeAdeleVectorRectangleFourierIntegral K I a d f
    And (Summable V) (tsum (fun x : Subtype (fun x : I -> K => forall i,
      InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x i)) =>
        f (heckePrincipalMinkowskiVector K I x.val)) = tsum V) := by
  let R := RingOfIntegers K
  let J : Ideal R := Ideal.span (Set.singleton d)
  let D := (DedekindZeta.Theta.dualIdeal K J : Submodule R K)
  let T : Set (I -> K) := fun v => forall i, Membership.mem D (v i)
  let e := algebraMap R K
  have hD : Not (e d = 0) :=
    (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective R K)).mpr hd
  have hRep : forall i, Exists (InFiniteAdelePrincipalCoset (a i) (e d)) :=
    fun i => exists_finiteAdele_sub_principal_modulus (a i) (e d) hD
  choose x0 hx0 using hRep
  let E : Equiv (I -> D) T :=
    { toFun := fun t => Subtype.mk (fun i => (t i).val) (fun i => (t i).property)
      invFun := fun t i => Subtype.mk (t.val i) (t.property i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let G := heckeAdeleVectorTraceDualFourierValue K I a d f
  let U (t : I -> D) : Complex :=
    let y := heckeConjMinkowskiVector K I (heckePrincipalMinkowskiVector K I (fun i => (t i).val))
    (Real.fourierChar (inner Real (heckePrincipalMinkowskiVector K I x0) y) : Complex) *
      (Inv.inv (((DedekindZeta.Theta.covolume K J) ^ Fintype.card I : Real) : Complex) *
        FourierTransform.fourier (f : PiLp 2 (fun _ : I => ArchCoordinate K) -> Complex) y)
  have hUG (t : I -> D) : U t = G (E t).val := by
    have hPhase (i : I) :
        (Real.fourierChar (Algebra.trace Rat K ((t i).val * x0 i) : Real) : Complex) =
          (heckeFiniteAdelePrincipalChar (-(t i).val) (a i) : Complex) := by
      have h := heckeAdeleAddChar_finiteCoset_eq (a i) d hd (x0 i) (hx0 i)
        (-(t i).val) (D.neg_mem (t i).property)
      rw [mul_neg, map_neg (Algebra.trace Rat K), Rat.cast_neg, neg_neg, mul_comm (x0 i) (t i).val] at h
      exact congrArg (fun z : Circle => (z : Complex)) h.symm
    dsimp only [U]
    rw [inner_heckePrincipalMinkowskiVector_conj_eq_trace_sum, coe_addChar_finset_sum]
    have hProd := Finset.prod_congr (rfl : Finset.univ = (Finset.univ : Finset I))
      (fun i _ => hPhase i)
    exact congrArg (fun z : Complex => z * _) hProd
  have hDual := principalVectorCosetSummable_traceDualFourier K I a d hd x0 hx0 f
  have hU : Summable U := hDual.1
  have hG : Summable (fun t : T => G t.val) := E.summable_iff.mp (hU.congr hUG)
  have hV := traceDualVector_indicator_eq_rectangleFourierIntegral K I a d hd f
  constructor
  . exact (summable_subtype_iff_indicator.mp hG).congr hV
  . calc
      _ = tsum U := hDual.2
      _ = tsum (fun t : I -> D => G (E t).val) := tsum_congr hUG
      _ = tsum (fun t : T => G t.val) := E.tsum_eq (fun t : T => G t.val)
      _ = _ := (tsum_subtype T G).trans (tsum_congr hV)

/-- The normalized Fourier sum of a Schwartz rectangle is absolutely convergent. -/
theorem summable_heckeAdeleVectorRectangleFourierIntegral
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) :
    Summable (heckeAdeleVectorRectangleFourierIntegral K I a d f) :=
  (principalVectorCosetSummable_fourierIntegral K I a d hd f).1

/-- Poisson summation for a Schwartz rectangle with the normalized Fourier integral. -/
theorem tsum_finiteAdelePrincipalVectorCoset_eq_fourierIntegral
    (a : I -> VecFiniteAdeles K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (f : SchwartzMap (PiLp 2 (fun _ : I => ArchCoordinate K)) Complex) :
    tsum (fun x : Subtype (fun x : I -> K => forall i,
      InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x i)) =>
        f (heckePrincipalMinkowskiVector K I x.val)) =
      tsum (heckeAdeleVectorRectangleFourierIntegral K I a d f) :=
  (principalVectorCosetSummable_fourierIntegral K I a d hd f).2

end Robin1984.GRH
