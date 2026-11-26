import DedekindZeta.Theta
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Robin1984.GRH.HeckeAdeleCharacter

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The trace pairing and annihilators of compact open finite adelic subgroups in Tate's thesis.
- Formalization note: Matches the finite character annihilator with the principal trace-dual ideal and aligns the actual infinite adele trace with the existing Minkowski pairing.
- PROVENANCE-END
-/

/-!
# The trace pairing and finite adelic annihilators

The additive character on the finite adeles pairs integral coordinates
with principal frequencies through the field trace. The annihilator of a
principal multiple of the integral coordinates is the trace-dual ideal.
The archimedean pairing agrees with the one used by the lattice Poisson
theorem.
-/

set_option autoImplicit false

namespace Robin1984.GRH

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

private theorem real_fourierChar_eq_one_iff (r : Real) :
    Real.fourierChar r = 1 <-> Exists (fun n : Int => r = (n : Real)) := by
  constructor
  case mp =>
    intro h
    have hc := congrArg (fun z : Circle => (z : Complex)) h
    rw [Real.fourierChar_apply, Circle.coe_one] at hc
    choose n hn using Complex.exp_eq_one_iff.mp hc
    let q := 2 * (Real.pi : Complex) * Complex.I
    have hq : Not (q = 0) := mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    have hEq : q * (r : Complex) = q * (n : Complex) := by
      push_cast at hn
      calc
        _ = 2 * (Real.pi : Complex) * (r : Complex) * Complex.I := by unfold q; ring
        _ = _ := by rw [hn]; unfold q; ring
    have hZero : q * ((r : Complex) - (n : Complex)) = 0 := by
      rw [mul_sub, hEq, sub_self]
    have hCast := sub_eq_zero.mp ((mul_eq_zero.mp hZero).resolve_left hq)
    exact Exists.intro n (by simpa using congrArg Complex.re hCast)
  case mpr =>
    intro h
    choose n hn using h
    subst r
    apply Subtype.ext
    rw [Real.fourierChar_apply, Circle.coe_one]
    push_cast
    rw [mul_comm (2 * (Real.pi : Complex)) (n : Complex), mul_assoc]
    exact Complex.exp_int_mul_two_pi_mul_I n

private theorem algebraMap_rat_real (q : Rat) : algebraMap Rat Real q = (q : Real) :=
  RingHom.congr_fun (Subsingleton.elim (algebraMap Rat Real) (Rat.castHom Real)) q

private abbrev HeckeFiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

private abbrev HeckeAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K

/-- Evaluation on the finite adeles uses archimedean trace of the negative
of any principal representative modulo the local integer rings. -/
theorem heckeAdeleAddChar_finitePart_eq_of_representative
    (a : HeckeFiniteAdeles K) (x : K)
    (hx : forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K)
        (a p - algebraMap K (p.adicCompletion K) x)) :
    heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K) a : HeckeAdeles K) =
      Real.fourierChar (-(Algebra.trace Rat K x : Real)) := by
  let u : HeckeAdeles K := Prod.mk 0 a
  let y := u - algebraMap K (HeckeAdeles K) x
  have hy : forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K) (y.2 p) := hx
  have h := heckeAdeleAddChar_of_integralFinitePart y hy
  change heckeAdeleAddChar (u - algebraMap K (HeckeAdeles K) x) =
    Real.fourierChar (infiniteAdeleTrace
      ((0 : InfiniteAdeleRing K) - algebraMap K (InfiniteAdeleRing K) x)) at h
  rw [AddChar.map_sub_eq_div, heckeAdeleAddChar_principal, div_one, zero_sub, map_neg,
    infiniteAdeleTrace_algebraMap] at h
  exact h

/-- A principal frequency annihilates the integral finite adeles exactly
when pairing it with every global integer has integer field trace. -/
theorem heckeAdeleAddChar_finiteIntegral_annihilator_iff (t : K) :
    (forall a : HeckeFiniteAdeles K,
      (forall p : HeightOneSpectrum (RingOfIntegers K),
        Membership.mem (p.adicCompletionIntegers K) (a p)) ->
      heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K)
        (a * algebraMap K (HeckeFiniteAdeles K) t) : HeckeAdeles K) = 1) <->
    (forall b : RingOfIntegers K, Exists (fun n : Int =>
      (Algebra.trace Rat K (algebraMap (RingOfIntegers K) K b * t) : Real) = (n : Real))) := by
  let R := RingOfIntegers K
  let A := HeckeFiniteAdeles K
  let g := algebraMap K A
  constructor
  case mp =>
    intro h b
    let bK := algebraMap R K b
    have hb : forall p : HeightOneSpectrum R,
        Membership.mem (p.adicCompletionIntegers K) (g bK p) :=
      fun p => HeightOneSpectrum.coe_algebraMap_mem R K p b
    have hChar := h (g bK) hb
    have hRep : forall p : HeightOneSpectrum R,
        Membership.mem (p.adicCompletionIntegers K)
          ((g bK * g t) p - algebraMap K (p.adicCompletion K) (bK * t)) := by
      intro p
      change Membership.mem (p.adicCompletionIntegers K)
        (algebraMap K (p.adicCompletion K) bK * algebraMap K (p.adicCompletion K) t -
          algebraMap K (p.adicCompletion K) (bK * t))
      rw [map_mul, sub_self]
      exact (p.adicCompletionIntegers K).zero_mem
    rw [heckeAdeleAddChar_finitePart_eq_of_representative (g bK * g t) (bK * t) hRep] at hChar
    choose n hn using (real_fourierChar_eq_one_iff _).mp hChar
    exact Exists.intro (-n) (by rw [Int.cast_neg, <- hn, neg_neg])
  case mpr =>
    intro h a ha
    choose d hd using exists_finiteAdele_integral_multiple (g t)
    let y (p : HeightOneSpectrum R) : p.adicCompletionIntegers K := Subtype.mk (a p) (ha p)
    choose b hb using exists_adicCompletionIntegers_simultaneous_approximation d hd.1 y
    let bK := algebraMap R K b
    have hRep : forall p : HeightOneSpectrum R,
        Membership.mem (p.adicCompletionIntegers K)
          ((a * g t) p - algebraMap K (p.adicCompletion K) (bK * t)) := by
      intro p
      let e := algebraMap K (p.adicCompletion K)
      let V := (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
      change V (a p * e t - e (bK * t)) <= 1
      rw [map_mul, <- sub_mul, V.map_mul]
      have hBound : V (a p - e bK) <=
          V (algebraMap R (p.adicCompletion K) d) := by
        rw [V.map_sub_swap]
        exact hb p
      refine (mul_le_mul_of_nonneg_right hBound (zero_le : 0 <= V (e t))).trans ?_
      rw [<- V.map_mul, mul_comm]
      exact hd.2 p
    rw [heckeAdeleAddChar_finitePart_eq_of_representative (a * g t) (bK * t) hRep]
    apply (real_fourierChar_eq_one_iff _).mpr
    choose n hn using h b
    exact Exists.intro (-n) (by rw [Int.cast_neg, hn])

/-- The finite annihilator for a scaled integral tube is the same trace-dual
ideal used by the archimedean lattice Poisson formula. -/
theorem heckeAdeleAddChar_finitePrincipalIdeal_annihilator_iff
    (d : RingOfIntegers K) (hd : Not (d = 0)) (t : K) :
    (forall a : HeckeFiniteAdeles K,
      (forall p : HeightOneSpectrum (RingOfIntegers K),
        Membership.mem (p.adicCompletionIntegers K) (a p)) ->
      heckeAdeleAddChar (Prod.mk (0 : InfiniteAdeleRing K)
        (a * algebraMap K (HeckeFiniteAdeles K) (algebraMap (RingOfIntegers K) K d * t)) :
          HeckeAdeles K) = 1) <->
    Membership.mem
      (DedekindZeta.Theta.dualIdeal K (Ideal.span ({d} : Set (RingOfIntegers K))) :
        Submodule (RingOfIntegers K) K) t := by
  let R := RingOfIntegers K
  let I : Ideal R := Ideal.span {d}
  have hI : Not (I = 0) := by
    intro h
    exact hd (Ideal.span_singleton_eq_bot.mp h)
  rw [heckeAdeleAddChar_finiteIntegral_annihilator_iff,
    <- DedekindZeta.Theta.traceForm_mixedEmbedding_int_iff_mem_dualIdeal K I hI]
  constructor
  case mp =>
    intro h a ha
    have ha' := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors R)).mp ha
    choose b hb using ha'
    have hba := hb.2
    have hD : Dvd.dvd d b := Ideal.mem_span_singleton.mp hb.1
    choose c hc using hD
    have hT := h c
    rw [DedekindZeta.Theta.traceForm_mixedEmbedding, algebraMap_rat_real]
    rw [<- hba, hc, map_mul (algebraMap R K) d c]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hT
  case mpr =>
    intro h b
    have hb : Membership.mem I (d * b) :=
      Ideal.mem_span_singleton.mpr (Dvd.intro b rfl)
    have hb' : Membership.mem (I : FractionalIdeal (nonZeroDivisors R) K)
      (algebraMap R K (d * b)) := FractionalIdeal.mem_coeIdeal_of_mem _ hb
    have hT := h _ hb'
    rw [DedekindZeta.Theta.traceForm_mixedEmbedding, algebraMap_rat_real,
      map_mul (algebraMap R K) d b] at hT
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hT

/-- The archimedean part of the adelic trace pairing agrees with the
trace pairing in the existing Minkowski lattice Poisson theorem. -/
theorem infiniteAdeleTrace_mul_principal (x : InfiniteAdeleRing K) (a : K) :
    infiniteAdeleTrace (x * algebraMap K (InfiniteAdeleRing K) a) =
      DedekindZeta.Theta.traceForm K (InfiniteAdeleRing.ringEquiv_mixedSpace K x) a := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  have he : Continuous (fun y : InfiniteAdeleRing K => e y) := by
    have heq (y : InfiniteAdeleRing K) :=
      InfiniteAdeleRing.ringEquiv_mixedSpace_apply (K := K) y
    simp only [e, heq]
    exact (continuous_pi (fun w =>
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.property).continuous.comp
        (continuous_apply w.val))).prodMk
      (continuous_pi (fun w =>
        (InfinitePlace.Completion.isometry_extensionEmbedding w.val).continuous.comp
          (continuous_apply w.val)))
  let f (y : InfiniteAdeleRing K) :=
    infiniteAdeleTrace (y * algebraMap K (InfiniteAdeleRing K) a)
  let g (y : InfiniteAdeleRing K) := DedekindZeta.Theta.traceForm K (e y) a
  have hf : Continuous f := continuous_infiniteAdeleTrace.comp
    (continuous_id.mul continuous_const)
  have hg : Continuous g := by
    have hSymm (y : InfiniteAdeleRing K) :
        g y = DedekindZeta.Theta.traceFormLin K (mixedEmbedding K a) (e y) := by
      simp only [g, DedekindZeta.Theta.traceForm, DedekindZeta.Theta.traceFormLin_apply,
        mul_comm]
    simp only [g, hSymm]
    exact (DedekindZeta.Theta.traceFormLin K
      (mixedEmbedding K a)).continuous_of_finiteDimensional.comp he
  have hEq : f = g := (InfiniteAdeleRing.denseRange_algebraMap (K := K)).equalizer hf hg (by
    funext b
    change infiniteAdeleTrace (algebraMap K (InfiniteAdeleRing K) b *
      algebraMap K (InfiniteAdeleRing K) a) = DedekindZeta.Theta.traceForm K
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (algebraMap K (InfiniteAdeleRing K) b)) a
    rw [<- map_mul, infiniteAdeleTrace_algebraMap,
      <- InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      DedekindZeta.Theta.traceForm_mixedEmbedding, algebraMap_rat_real])
  exact congrFun hEq x

end Robin1984.GRH
