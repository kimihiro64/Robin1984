import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Trace.Basic
import Robin1984.GRH.HeckeAdeleLattice

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The additive character of the adeles that is trivial on the principal field, as used in Tate's thesis.
- Formalization note: Constructs the character using finite strong approximation, the trace at the infinite places, and the integer trace of an algebraic integer.
- PROVENANCE-END
-/

/-!
# The additive character of a number field's adeles

Finite strong approximation writes the finite coordinates of an adele as
those of a principal element plus local integers. The character evaluates the
archimedean trace after subtracting that principal element. The difference
between two choices is a global integer, whose trace is an ordinary integer.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- The real-valued trace on the archimedean component of the adele ring. -/
noncomputable def infiniteAdeleTrace : AddMonoidHom (InfiniteAdeleRing K) Real where
  toFun a := Finset.sum Finset.univ (fun s : AlgHom Rat K Complex =>
    (InfinitePlace.Completion.extensionEmbedding
      (InfinitePlace.mk s.toRingHom) (a (InfinitePlace.mk s.toRingHom))).re)
  map_zero' := by
    change Finset.sum Finset.univ (fun s : AlgHom Rat K Complex =>
      (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk s.toRingHom) 0).re) = 0
    apply Finset.sum_eq_zero
    intro s _
    rw [map_zero, Complex.zero_re]
  map_add' a b := by
    change Finset.sum Finset.univ (fun s : AlgHom Rat K Complex =>
      (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk s.toRingHom)
        (a (InfinitePlace.mk s.toRingHom) + b (InfinitePlace.mk s.toRingHom))).re) = _
    simp only [map_add, Complex.add_re, Finset.sum_add_distrib]

/-- The archimedean trace is continuous in the product topology. -/
theorem continuous_infiniteAdeleTrace :
    Continuous (infiniteAdeleTrace (K := K)) := by
  unfold infiniteAdeleTrace
  refine continuous_finsetSum _ (fun s _ => ?_)
  exact Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp
      (continuous_apply _))

/-- The archimedean trace of a principal element equals the rational field trace. -/
theorem infiniteAdeleTrace_algebraMap (x : K) :
    infiniteAdeleTrace (algebraMap K (InfiniteAdeleRing K) x) =
      (Algebra.trace Rat K x : Real) := by
  let reAdd : AddMonoidHom Complex Real :=
    { toFun := Complex.re, map_zero' := Complex.zero_re, map_add' := Complex.add_re }
  calc
    infiniteAdeleTrace (algebraMap K (InfiniteAdeleRing K) x) =
        Finset.sum Finset.univ (fun s : AlgHom Rat K Complex => reAdd (s x)) := by
      unfold infiniteAdeleTrace
      change Finset.sum Finset.univ
        (fun s : AlgHom Rat K Complex =>
          (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk s.toRingHom)
            ((algebraMap K (InfiniteAdeleRing K) x) (InfinitePlace.mk s.toRingHom))).re) = _
      apply Finset.sum_congr rfl
      intro s _
      rw [InfiniteAdeleRing.algebraMap_apply,
        InfinitePlace.Completion.extensionEmbedding_coe]
      rcases InfinitePlace.embedding_mk_eq s.toRingHom with h | h
      next => rw [h]; rfl
      next => rw [h]; rfl
    _ = reAdd (Finset.sum Finset.univ (fun s : AlgHom Rat K Complex => s x)) :=
      (map_sum reAdd _ _).symm
    _ = (Algebra.trace Rat K x : Real) := by
      rw [<- trace_eq_sum_embeddings Complex]
      exact Complex.ratCast_re _

private abbrev HeckeAdele (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

private def IsFiniteRepresentative (a : HeckeAdele K) (x : K) : Prop :=
  forall p : HeightOneSpectrum (RingOfIntegers K),
    Membership.mem (p.adicCompletionIntegers K)
      (a.2 p - algebraMap K (p.adicCompletion K) x)

private theorem exists_finiteRepresentative (a : HeckeAdele K) :
    Exists (IsFiniteRepresentative a) :=
  exists_finiteAdele_sub_principal_integral a.2

private theorem fourierChar_int (n : Int) :
    Real.fourierChar (n : Real) = 1 := by
  apply Subtype.ext
  rw [Real.fourierChar_apply, Circle.coe_one]
  push_cast
  rw [mul_comm (2 * (Real.pi : Complex)) (n : Complex), mul_assoc]
  exact Complex.exp_int_mul_two_pi_mul_I n

private theorem archimedeanChar_eq_of_finiteRepresentative
    (a : HeckeAdele K) {x y : K} (hx : IsFiniteRepresentative a x)
    (hy : IsFiniteRepresentative a y) :
    Real.fourierChar (infiniteAdeleTrace
        (a.1 - algebraMap K (InfiniteAdeleRing K) x)) =
      Real.fourierChar (infiniteAdeleTrace
        (a.1 - algebraMap K (InfiniteAdeleRing K) y)) := by
  let R := RingOfIntegers K
  have hIntegral := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := R) K
    (y - x) (by
      intro p
      have hp := sub_mem (hx p) (hy p)
      rw [sub_sub_sub_cancel_left, <- map_sub] at hp
      change Valued.v ((y - x : K) : p.adicCompletion K) <=
        (1 : WithZero (Multiplicative Int)) at hp
      rw [HeightOneSpectrum.adicCompletion.valued_coe] at hp
      exact hp)
  choose b hb using hIntegral
  have hTrace : (Algebra.trace Rat K (y - x) : Real) =
      (Algebra.trace Int R b : Real) := by
    rw [<- hb, <- Algebra.coe_trace_int]
    exact Rat.cast_intCast _
  apply eq_of_div_eq_one
  rw [<- Real.fourierChar.map_sub_eq_div, <- map_sub, sub_sub_sub_cancel_left,
    <- map_sub, infiniteAdeleTrace_algebraMap, hTrace]
  exact fourierChar_int _

/-- The canonical additive circle character of the adeles of a number field. -/
noncomputable def heckeAdeleAddChar : AddChar (AdeleRing (RingOfIntegers K) K) Circle where
  toFun a := Real.fourierChar (infiniteAdeleTrace
    (a.1 - algebraMap K (InfiniteAdeleRing K)
      (Classical.choose (exists_finiteRepresentative a))))
  map_zero_eq_one' := by
    have h0 : IsFiniteRepresentative (0 : HeckeAdele K) 0 := by
      intro p
      change Membership.mem (p.adicCompletionIntegers K)
        (0 - algebraMap K (p.adicCompletion K) 0)
      rw [map_zero, sub_zero]
      exact (p.adicCompletionIntegers K).zero_mem
    rw [archimedeanChar_eq_of_finiteRepresentative 0
      (Classical.choose_spec (exists_finiteRepresentative 0)) h0]
    change Real.fourierChar (infiniteAdeleTrace
      ((0 : InfiniteAdeleRing K) - algebraMap K (InfiniteAdeleRing K) 0)) = 1
    rw [map_zero, sub_zero, map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by
    let x := Classical.choose (exists_finiteRepresentative a)
    let y := Classical.choose (exists_finiteRepresentative b)
    have hx : IsFiniteRepresentative a x := Classical.choose_spec
      (exists_finiteRepresentative a)
    have hy : IsFiniteRepresentative b y := Classical.choose_spec
      (exists_finiteRepresentative b)
    have hxy : IsFiniteRepresentative (a + b) (x + y) := by
      intro p
      change Membership.mem (p.adicCompletionIntegers K)
        (a.2 p + b.2 p - algebraMap K (p.adicCompletion K) (x + y))
      rw [map_add, add_sub_add_comm]
      exact add_mem (hx p) (hy p)
    rw [archimedeanChar_eq_of_finiteRepresentative (a + b)
      (Classical.choose_spec (exists_finiteRepresentative (a + b))) hxy]
    change Real.fourierChar (infiniteAdeleTrace
        (a.1 + b.1 - algebraMap K (InfiniteAdeleRing K) (x + y))) =
      Real.fourierChar (infiniteAdeleTrace (a.1 - algebraMap K (InfiniteAdeleRing K) x)) *
        Real.fourierChar (infiniteAdeleTrace (b.1 - algebraMap K (InfiniteAdeleRing K) y))
    rw [map_add, add_sub_add_comm, map_add, AddChar.map_add_eq_mul]

private theorem heckeAdeleAddChar_of_representative (a : HeckeAdele K)
    (x : K) (hx : IsFiniteRepresentative a x) :
    heckeAdeleAddChar a =
      Real.fourierChar (infiniteAdeleTrace (a.1 - algebraMap K (InfiniteAdeleRing K) x)) :=
  archimedeanChar_eq_of_finiteRepresentative a
    (Classical.choose_spec (exists_finiteRepresentative a)) hx

/-- The adelic additive character is trivial on the diagonal copy of the number field. -/
theorem heckeAdeleAddChar_principal (x : K) :
    heckeAdeleAddChar (algebraMap K (AdeleRing (RingOfIntegers K) K) x) = 1 := by
  have hx : IsFiniteRepresentative (algebraMap K (HeckeAdele K) x) x := by
    intro p
    change Membership.mem (p.adicCompletionIntegers K)
      (algebraMap K (p.adicCompletion K) x - algebraMap K (p.adicCompletion K) x)
    rw [sub_self]
    exact (p.adicCompletionIntegers K).zero_mem
  rw [heckeAdeleAddChar_of_representative _ x hx]
  change Real.fourierChar (infiniteAdeleTrace
    (algebraMap K (InfiniteAdeleRing K) x - algebraMap K (InfiniteAdeleRing K) x)) = 1
  rw [sub_self, map_zero, AddChar.map_zero_eq_one]

/-- The canonical additive character is continuous in the restricted product topology. -/
theorem continuous_heckeAdeleAddChar : Continuous (heckeAdeleAddChar (K := K)) := by
  refine continuous_iff_continuousAt.mpr (fun a => ?_)
  let x := Classical.choose (exists_finiteRepresentative a)
  have hx : IsFiniteRepresentative a x := Classical.choose_spec
    (exists_finiteRepresentative a)
  let T := {b : FiniteAdeleRing (RingOfIntegers K) K |
    forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K) (b p)}
  have hT : IsOpen T :=
    RestrictedProduct.isOpen_forall_mem
      (R := fun p : HeightOneSpectrum (RingOfIntegers K) => p.adicCompletion K)
      (A := fun p => (p.adicCompletionIntegers K : Set (p.adicCompletion K)))
      (fun p => Valued.isOpen_valuationSubring (p.adicCompletion K))
  let f (b : HeckeAdele K) := b.2 - algebraMap K (FiniteAdeleRing (RingOfIntegers K) K) x
  have hf : Continuous f := continuous_snd.sub continuous_const
  have ha : Membership.mem (Set.preimage f T) a := hx
  have hNear := (hT.preimage hf).mem_nhds ha
  let g (b : HeckeAdele K) :=
    Real.fourierChar (infiniteAdeleTrace (b.1 - algebraMap K (InfiniteAdeleRing K) x))
  have hg : Continuous g := Real.continuous_fourierChar.comp
    (continuous_infiniteAdeleTrace.comp (continuous_fst.sub continuous_const))
  apply hg.continuousAt.congr
  exact Filter.mem_of_superset hNear (fun b hb =>
    (heckeAdeleAddChar_of_representative b x hb).symm)

/-- For an adele with integral finite coordinates, the character is the
archimedean trace character. -/
theorem heckeAdeleAddChar_of_integralFinitePart (a : AdeleRing (RingOfIntegers K) K)
    (ha : forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K) (a.2 p)) :
    heckeAdeleAddChar a = Real.fourierChar (infiniteAdeleTrace a.1) := by
  have h0 : IsFiniteRepresentative a 0 := by
    intro p
    rw [map_zero, sub_zero]
    exact ha p
  rw [heckeAdeleAddChar_of_representative a 0 h0, map_zero, sub_zero]

end Robin1984.GRH
