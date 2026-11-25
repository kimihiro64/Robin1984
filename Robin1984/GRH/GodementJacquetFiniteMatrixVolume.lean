import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.Units
import Robin1984.GRH.HeckeAdeleLattice

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Integral local matrix subgroups and finite adelic approximation in the Godement--Jacquet construction.
- Formalization note: Bounds the Haar measure of integral finite adelic matrices whose inverses have a fixed denominator by the number of residue matrices times the mass of the integral matrix subgroup.
- PROVENANCE-END
-/

/-!
# Haar volume with a fixed finite matrix denominator

Integral finite adeles admit simultaneous residue representatives modulo
a positive integer. Two integral matrices represented by the same residues
belong to the same left coset of the compact integral matrix subgroup if
that integer clears both inverse matrices. Counting the residue classes
bounds the Haar volume for one fixed denominator.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain
open scoped Classical

private abbrev IntegralResidueIndex (K : Type*) [Field K] [NumberField K] (N : Nat) :=
  Fin (Module.finrank Int (RingOfIntegers K)) -> Fin N

/-- The integral representative obtained by lifting each basis coordinate. -/
def finiteAdeleIntegralResidueRepresentative
    (K : Type*) [Field K] [NumberField K] (N : Nat)
    (c : IntegralResidueIndex K N) : RingOfIntegers K :=
  (Module.finBasis Int (RingOfIntegers K)).equivFun.symm
    (fun i => ((c i).val : Int))

private theorem exists_integralBasisResidue
    (K : Type*) [Field K] [NumberField K] (N : Nat) (hN : 0 < N) (b : RingOfIntegers K) :
    Exists (fun c : IntegralResidueIndex K N => Exists (fun z : RingOfIntegers K =>
      b - finiteAdeleIntegralResidueRepresentative K N c = (N : RingOfIntegers K) * z)) := by
  let R := RingOfIntegers K
  let E := (Module.finBasis Int R).equivFun
  let s (i : Fin (Module.finrank Int R)) : Int := E b i % (N : Int)
  have hNpos : 0 < (N : Int) := by exact_mod_cast hN
  have hN0 : Not ((N : Int) = 0) := ne_of_gt hNpos
  have hS0 (i : Fin (Module.finrank Int R)) : 0 <= s i := Int.emod_nonneg _ hN0
  have hS (i : Fin (Module.finrank Int R)) : (s i).toNat < N := by
    have h := Int.emod_lt_of_pos (E b i) hNpos
    change s i < (N : Int) at h
    exact Int.ofNat_lt.mp ((Int.toNat_of_nonneg (hS0 i)).trans_lt h)
  let c : IntegralResidueIndex K N := fun i => Fin.mk (s i).toNat (hS i)
  let z := E.symm (fun i => E b i / (N : Int))
  let a := finiteAdeleIntegralResidueRepresentative K N c
  have hac (i : Fin (Module.finrank Int R)) : E a i = s i := by
    change E (E.symm (fun j => ((c j).val : Int))) i = s i
    rw [E.apply_symm_apply]
    exact Int.toNat_of_nonneg (hS0 i)
  have hzc (i : Fin (Module.finrank Int R)) : E z i = E b i / (N : Int) := by
    dsimp only [z]
    rw [E.apply_symm_apply]
  refine Exists.intro c (Exists.intro z ?_)
  change b - a = (N : R) * z
  have hSc : (N : R) * z = HSMul.hSMul (N : Int) z := by
    rw [zsmul_eq_mul, Int.cast_natCast]
  rw [hSc]
  apply E.injective
  rw [map_sub, map_smul]
  funext i
  change E b i - E a i = (N : Int) * E z i
  rw [hac, hzc, sub_eq_iff_eq_add]
  exact (Int.mul_ediv_add_emod (E b i) (N : Int)).symm

/-- Integral finite adeles admit a family of representatives modulo a
positive rational integer indexed by one residue in every integral basis
coordinate. -/
theorem exists_finiteAdeleIntegralResidueRepresentative
    (K : Type*) [Field K] [NumberField K] (N : Nat) (hN : 0 < N)
    (x : FiniteAdeleRing (RingOfIntegers K) K)
    (hx : forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K) (x p)) :
    Exists (fun c : IntegralResidueIndex K N => forall p : HeightOneSpectrum (RingOfIntegers K),
      (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
        (x p - algebraMap (RingOfIntegers K) (p.adicCompletion K)
          (finiteAdeleIntegralResidueRepresentative K N c)) <=
      (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
        (algebraMap (RingOfIntegers K) (p.adicCompletion K) (N : RingOfIntegers K))) := by
  let R := RingOfIntegers K
  let P := HeightOneSpectrum R
  let d : R := N
  have hd : Not (d = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  let y (p : P) : p.adicCompletionIntegers K := Subtype.mk (x p) (hx p)
  choose b hb using exists_adicCompletionIntegers_simultaneous_approximation d hd y
  choose c z hz using exists_integralBasisResidue K N hN b
  refine Exists.intro c (fun p => ?_)
  let A := p.adicCompletion K
  let V : Valuation A (WithZero (Multiplicative Int)) := Valued.v
  let e : RingHom R A := algebraMap R A
  let u := finiteAdeleIntegralResidueRepresentative K N c
  change V (x p - e u) <= V (e d)
  have hB : V (x p - e b) <= V (e d) := by
    rw [V.map_sub_swap]
    exact hb p
  have hZ : V (e z) <= 1 := HeightOneSpectrum.coe_algebraMap_mem R K p z
  have hMul : V (e d * e z) <= V (e d) := by
    rw [map_mul]
    calc
      _ <= V (e d) * 1 := mul_le_mul_right hZ _
      _ = _ := mul_one _
  have hDiff : x p - e u = (x p - e b) + e d * e z := by
    have hEq : e b - e u = e d * e z := by
      rw [<- map_sub, <- map_mul]
      exact congrArg e hz
    rw [<- hEq]
    abel
  rw [hDiff]
  exact (V.map_add _ _).trans (max_le hB hMul)

section MatrixCongruence

variable {R : Type*} [CommRing R] {I : Type*} [Fintype I] [DecidableEq I]

private theorem matrix_inv_mul_of_scalarCongruence
    (d : R) (A B : Units (Matrix I I R)) (C : Matrix I I R)
    (hC : B.val - A.val = HSMul.hSMul d C) :
    A.inv * B.val = 1 + HSMul.hSMul d A.inv * C := by
  have hB : B.val = A.val + HSMul.hSMul d C := by
    rw [<- hC, add_sub_cancel]
  calc
    _ = A.inv * (A.val + HSMul.hSMul d C) := congrArg (fun M => A.inv * M) hB
    _ = _ := by rw [mul_add, A.inv_val, Matrix.mul_smul, Matrix.smul_mul]

/-- Integral scaled inverses and congruent matrix entries identify the
same left coset of the integral matrix subgroup. -/
theorem mem_matrixSubringUnits_inv_mul_of_scalarCongruence
    (S : Subring R) (d : R) (A B : Units (Matrix I I R)) (C : Matrix I I R)
    (hA : Membership.mem S.matrix (HSMul.hSMul d A.inv))
    (hB : Membership.mem S.matrix (HSMul.hSMul d B.inv))
    (hC : Membership.mem S.matrix C)
    (hDiff : B.val - A.val = HSMul.hSMul d C) :
    Membership.mem S.matrix.toSubmonoid.units (Inv.inv A * B) := by
  have hNeg : A.val - B.val = HSMul.hSMul d (-C) := by
    rw [smul_neg, <- hDiff, neg_sub]
  change And (Membership.mem S.matrix (A.inv * B.val)) (Membership.mem S.matrix (B.inv * A.val))
  rw [matrix_inv_mul_of_scalarCongruence d A B C hDiff,
    matrix_inv_mul_of_scalarCongruence d B A (-C) hNeg]
  exact And.intro (S.matrix.add_mem S.matrix.one_mem (S.matrix.mul_mem hA hC))
    (S.matrix.add_mem S.matrix.one_mem (S.matrix.mul_mem hB (S.matrix.neg_mem hC)))

end MatrixCongruence

private abbrev FiniteAdelicScalars (K : Type*) [Field K] [NumberField K] :=
  FiniteAdeleRing (RingOfIntegers K) K

/-- Scalar finite adeles integral at every place form a subring. -/
def integralFiniteAdeleSubring (K : Type*) [Field K] [NumberField K] :
    Subring (FiniteAdelicScalars K) where
  carrier := Set.ofPred (fun x => forall p : HeightOneSpectrum (RingOfIntegers K),
    Membership.mem (p.adicCompletionIntegers K) (x p))
  zero_mem' := fun p => (p.adicCompletionIntegers K).zero_mem
  one_mem' := fun p => (p.adicCompletionIntegers K).one_mem
  add_mem' hx hy := fun p => (p.adicCompletionIntegers K).toSubring.add_mem (hx p) (hy p)
  mul_mem' hx hy := fun p => (p.adicCompletionIntegers K).toSubring.mul_mem (hx p) (hy p)
  neg_mem' hx := fun p => (p.adicCompletionIntegers K).toSubring.neg_mem (hx p)

/-- Invertible finite adelic matrices whose value and inverse are integral. -/
def integralFiniteAdeleMatrixGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (FiniteAdelicScalars K)) :=
  (integralFiniteAdeleSubring K).matrix.toSubmonoid.units

/-- Integral invertible matrices form a compact subgroup of the finite
adelic general linear group. -/
theorem isCompact_integralFiniteAdeleMatrixGroup
    (K : Type*) [Field K] [NumberField K] (n : Nat) :
    IsCompact (integralFiniteAdeleMatrixGroup K n).carrier := by
  let F := FiniteAdelicScalars K
  let P := HeightOneSpectrum (RingOfIntegers K)
  let R := integralFiniteAdeleSubring K
  let S (p : P) := p.adicCompletion K
  let projection (a : F) (p : P) : S p := a p
  have hInj : Function.Injective projection := DFunLike.coe_injective
  have hCont : Continuous projection := continuous_pi (fun p => RestrictedProduct.continuous_eval p)
  let _ : T2Space F := T2Space.of_injective_continuous hInj hCont
  change IsCompact ((R.matrix : Subring (Matrix (Fin n) (Fin n) F)).toSubmonoid.units).carrier
  apply Submonoid.units_isCompact
  let T := Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => (R : Set F)))
  have hT : IsCompact T :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_integralFiniteAdeles))
  have he : (R.matrix : Subring (Matrix (Fin n) (Fin n) F)).toSubmonoid.carrier = T := by
    ext A
    change (forall i j, Membership.mem R (A i j)) <-> Membership.mem T A
    constructor
    . intro h i hi j hj
      exact h i j
    . intro h i j
      exact h i (Set.mem_univ i) j (Set.mem_univ j)
  exact (congrArg IsCompact he).mpr hT

open MeasureTheory

private abbrev FiniteGL (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  Matrix.GeneralLinearGroup (Fin n) (FiniteAdelicScalars K)

private abbrev MatrixResidueIndex (K : Type*) [Field K] [NumberField K] (n N : Nat) :=
  Fin n -> Fin n -> IntegralResidueIndex K N

private def finiteMatrixHasResidues
    (K : Type*) [Field K] [NumberField K] (n N : Nat)
    (g : FiniteGL K n) (c : MatrixResidueIndex K n N) : Prop :=
  forall (i j : Fin n) (p : HeightOneSpectrum (RingOfIntegers K)),
    (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
      ((g.val i j) p - algebraMap (RingOfIntegers K) (p.adicCompletion K)
        (finiteAdeleIntegralResidueRepresentative K N (c i j))) <=
    (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
      (N : p.adicCompletion K)

/-- Integral matrices whose inverses become integral under multiplication
by the fixed positive denominator. -/
def finiteAdeleMatrixDenominatorSet
    (K : Type*) [Field K] [NumberField K] (n N : Nat) : Set (FiniteGL K n) :=
  Set.ofPred (fun g =>
    And (Membership.mem (integralFiniteAdeleSubring K).matrix g.val)
      (Membership.mem (integralFiniteAdeleSubring K).matrix
        (HSMul.hSMul (N : FiniteAdelicScalars K) g.inv)))

private theorem exists_finiteMatrixHasResidues
    (K : Type*) [Field K] [NumberField K] (n N : Nat) (hN : 0 < N)
    (g : FiniteGL K n) (hg : Membership.mem (finiteAdeleMatrixDenominatorSet K n N) g) :
    Exists (finiteMatrixHasResidues K n N g) := by
  have hInt (i j : Fin n) (p : HeightOneSpectrum (RingOfIntegers K)) :
      Membership.mem (p.adicCompletionIntegers K) ((g.val i j) p) := hg.1 i j p
  choose c hc using fun i j => exists_finiteAdeleIntegralResidueRepresentative K N hN (g.val i j) (hInt i j)
  refine Exists.intro c (fun i j p => ?_)
  simpa only [map_natCast] using hc i j p

private theorem mem_integralFiniteAdeleMatrixGroup_of_sameResidues
    (K : Type*) [Field K] [NumberField K] (n N : Nat) (hN : 0 < N)
    (g h : FiniteGL K n)
    (hg : Membership.mem (finiteAdeleMatrixDenominatorSet K n N) g)
    (hh : Membership.mem (finiteAdeleMatrixDenominatorSet K n N) h)
    (c : MatrixResidueIndex K n N)
    (hgC : finiteMatrixHasResidues K n N g c) (hhC : finiteMatrixHasResidues K n N h c) :
    Membership.mem (integralFiniteAdeleMatrixGroup K n) (Inv.inv g * h) := by
  let F := FiniteAdelicScalars K
  let R := integralFiniteAdeleSubring K
  let t : K := Inv.inv (N : K)
  let u : F := algebraMap K F t
  let D := h.val - g.val
  let C := HSMul.hSMul u D
  have hN0 : Not ((N : K) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have ht : (N : K) * t = 1 := by
    dsimp only [t]
    field_simp [hN0]
  have hInvF : (N : F) * u = 1 := by
    simpa only [map_mul, map_natCast, map_one] using congrArg (algebraMap K F) ht
  have hCeq : D = HSMul.hSMul (N : F) C := by
    dsimp only [C]
    rw [smul_smul, hInvF, one_smul]
  have hC : Membership.mem R.matrix C := by
    intro i j p
    let A := p.adicCompletion K
    let V : Valuation A (WithZero (Multiplicative Int)) := Valued.v
    let e : RingHom K A := algebraMap K A
    let s := algebraMap (RingOfIntegers K) A (finiteAdeleIntegralResidueRepresentative K N (c i j))
    have hp : V ((h.val i j) p - (g.val i j) p) <= V (N : A) := by
      have hEq : (h.val i j) p - (g.val i j) p =
          ((h.val i j) p - s) - ((g.val i j) p - s) := by abel
      rw [hEq]
      exact (V.map_sub _ _).trans (max_le (hhC i j p) (hgC i j p))
    have hInvA : e t * (N : A) = 1 := by
      rw [mul_comm]
      simpa only [map_mul, map_natCast, map_one] using congrArg e ht
    change V (e t * ((h.val i j) p - (g.val i j) p)) <= 1
    rw [map_mul]
    calc
      _ <= V (e t) * V (N : A) := mul_le_mul_right hp _
      _ = _ := by rw [<- map_mul, hInvA, map_one]
  exact mem_matrixSubringUnits_inv_mul_of_scalarCongruence R (N : F) g h C hg.2 hh.2 hC hCeq

/-- For a fixed positive inverse denominator, the residue matrices give
a left coset cover by the compact integral subgroup. -/
theorem exists_finiteAdeleMatrixDenominatorSet_cosetCover
    (K : Type*) [Field K] [NumberField K] (n N : Nat) (hN : 0 < N) :
    Exists (fun center : Fin (N ^ (Module.finrank Int (RingOfIntegers K) * n * n)) -> FiniteGL K n =>
      forall g : FiniteGL K n, Membership.mem (finiteAdeleMatrixDenominatorSet K n N) g ->
        Exists (fun i => Membership.mem (integralFiniteAdeleMatrixGroup K n) (Inv.inv (center i) * g))) := by
  let G := FiniteGL K n
  let S := finiteAdeleMatrixDenominatorSet K n N
  let I := MatrixResidueIndex K n N
  let E (i : I) := Exists (fun g : G => And (Membership.mem S g) (finiteMatrixHasResidues K n N g i))
  let center (i : I) : G := if hi : E i then Classical.choose hi else 1
  have hCard :
      Fintype.card I = N ^ (Module.finrank Int (RingOfIntegers K) * n * n) := by
    dsimp only [I, MatrixResidueIndex, IntegralResidueIndex]
    simp only [Fintype.card_fun, Fintype.card_fin, <- pow_mul]
  let e := (Fintype.equivFin I).trans (finCongr hCard)
  refine Exists.intro (fun i => center (e.symm i)) (fun g hg => ?_)
  choose i hi using exists_finiteMatrixHasResidues K n N hN g hg
  have hE : E i := Exists.intro g (And.intro hg hi)
  have hc : center i = Classical.choose hE := dif_pos hE
  have hPick := Classical.choose_spec hE
  refine Exists.intro (e i) ?_
  simp only [e.symm_apply_apply]
  rw [hc]
  exact mem_integralFiniteAdeleMatrixGroup_of_sameResidues K n N hN _ g hPick.1 hg i hPick.2 hi

/-- An integer upper bound for the inverse denominator gives one finite
family covering every corresponding integral matrix. -/
theorem exists_finiteAdeleMatrixDenominatorSet_cosetCover_le
    (K : Type*) [Field K] [NumberField K] (n B : Nat) :
    let d := Module.finrank Int (RingOfIntegers K) * n * n
    Exists (fun center : Prod (Fin B) (Fin (B ^ d)) -> FiniteGL K n =>
      forall (N : Nat), 0 < N -> N <= B ->
        forall g : FiniteGL K n, Membership.mem (finiteAdeleMatrixDenominatorSet K n N) g ->
          Exists (fun i => Membership.mem (integralFiniteAdeleMatrixGroup K n) (Inv.inv (center i) * g))) := by
  let d := Module.finrank Int (RingOfIntegers K) * n * n
  have hC (i : Fin B) := exists_finiteAdeleMatrixDenominatorSet_cosetCover K n (i.val + 1) (Nat.zero_lt_succ _)
  choose center hCenter using hC
  let F (i : Prod (Fin B) (Fin (B ^ d))) : FiniteGL K n :=
    if hi : i.2.val < (i.1.val + 1) ^ d then center i.1 (Fin.mk i.2.val hi) else 1
  refine Exists.intro F (fun N hN hNB g hg => ?_)
  let i : Fin B := Fin.mk (N - 1) (by omega)
  have hi : i.val + 1 = N := by
    change N - 1 + 1 = N
    omega
  have hg' : Membership.mem (finiteAdeleMatrixDenominatorSet K n (i.val + 1)) g := by rwa [hi]
  choose j hj using hCenter i g hg'
  have hPow : (i.val + 1) ^ d <= B ^ d := by
    have hiB : i.val + 1 <= B := hi.trans_le hNB
    gcongr
  let J : Fin (B ^ d) := Fin.mk j.val (j.isLt.trans_le hPow)
  refine Exists.intro (Prod.mk i J) ?_
  have hJ : J.val < (i.val + 1) ^ d := j.isLt
  change Membership.mem (integralFiniteAdeleMatrixGroup K n)
    (Inv.inv (if h : J.val < (i.val + 1) ^ d then center i (Fin.mk J.val h) else 1) * g)
  rw [dif_pos hJ]
  exact hj

/-- The finite Haar measure with one fixed inverse denominator is bounded
by the number of integral residue matrices times the mass of the compact
integral subgroup. -/
theorem measure_finiteAdeleMatrixDenominatorSet_le
    (K : Type*) [Field K] [NumberField K] (n N : Nat) (hN : 0 < N)
    [MeasurableSpace (FiniteGL K n)] [BorelSpace (FiniteGL K n)]
    [MeasurableMul (FiniteGL K n)]
    (mu : Measure (FiniteGL K n)) [mu.IsMulLeftInvariant] :
    mu (finiteAdeleMatrixDenominatorSet K n N) <=
      (N : ENNReal) ^ (Module.finrank Int (RingOfIntegers K) * n * n) *
        mu (integralFiniteAdeleMatrixGroup K n).carrier := by
  let G := FiniteGL K n
  let S := finiteAdeleMatrixDenominatorSet K n N
  let H := integralFiniteAdeleMatrixGroup K n
  let I := Fin (N ^ (Module.finrank Int (RingOfIntegers K) * n * n))
  choose center hCenter using exists_finiteAdeleMatrixDenominatorSet_cosetCover K n N hN
  let coset (i : I) := Set.preimage (fun g : G => Inv.inv (center i) * g) (H : Set G)
  let F := FiniteAdelicScalars K
  let P := HeightOneSpectrum (RingOfIntegers K)
  let projection (a : F) (p : P) : p.adicCompletion K := a p
  have hInj : Function.Injective projection := DFunLike.coe_injective
  have hCont : Continuous projection := continuous_pi (fun p => RestrictedProduct.continuous_eval p)
  let _ : T2Space F := T2Space.of_injective_continuous hInj hCont
  have hH : MeasurableSet (H : Set G) :=
    (isCompact_integralFiniteAdeleMatrixGroup K n).isClosed.measurableSet
  have hCoset (i : I) : mu (coset i) = mu (H : Set G) :=
    (measurePreserving_mul_left mu (Inv.inv (center i))).measure_preimage hH.nullMeasurableSet
  have hCover : S <= Set.iUnion coset := by
    intro g hg
    choose i hi using hCenter g hg
    exact Set.mem_iUnion.mpr (Exists.intro i hi)
  calc
    _ <= mu (Set.iUnion coset) := measure_mono hCover
    _ <= tsum (fun i => mu (coset i)) := measure_iUnion_le coset
    _ = _ := by
      have hCard : Fintype.card I = N ^ (Module.finrank Int (RingOfIntegers K) * n * n) :=
        Fintype.card_fin _
      simp_rw [hCoset, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hCard, Nat.cast_pow]
      rfl

section FiniteMatrixCoordinates

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K

private abbrev finiteLocalMatrix (n : Nat) (p : P) :=
  Matrix (Fin n) (Fin n) (p.adicCompletion K)

private abbrev finiteLocalIntegralMatrices (n : Nat) (p : P) :=
  (p.adicCompletionIntegers K).matrix (n := Fin n)

/-- Evaluate a finite adelic matrix at one finite place. -/
def finiteAdeleMatrixEval (n : Nat) (p : P) :
    RingHom (Matrix (Fin n) (Fin n) FA) (finiteLocalMatrix K n p) :=
  (RestrictedProduct.evalRingHom (fun q : P => q.adicCompletion K) p :
    RingHom FA (p.adicCompletion K)).mapMatrix

/-- Local evaluation acts on each matrix entry. -/
theorem finiteAdeleMatrixEval_apply (n : Nat) (p : P)
    (M : Matrix (Fin n) (Fin n) FA) (i j : Fin n) :
    finiteAdeleMatrixEval K n p M i j = M i j p := rfl

/-- Finite adelic matrices are the restricted product of local matrices with
respect to their integral matrix rings. -/
def finiteAdeleMatrixRestrictedProductEquiv (n : Nat) :
    RingEquiv (Matrix (Fin n) (Fin n) FA)
      (RestrictedProduct (finiteLocalMatrix K n)
        (fun p => (finiteLocalIntegralMatrices K n p : Set (finiteLocalMatrix K n p)))
        Filter.cofinite) where
  toFun M := Subtype.mk (fun p => finiteAdeleMatrixEval K n p M) (by
    have hMem (ij : Prod (Fin n) (Fin n)) : Filter.Eventually
        (fun p : P => Membership.mem (p.adicCompletionIntegers K) (M ij.1 ij.2 p))
        Filter.cofinite := (M ij.1 ij.2).2
    filter_upwards [Filter.eventually_all.mpr hMem] with p hp
    intro i j
    exact hp (i, j))
  invFun X := Matrix.of (fun i j => Subtype.mk (fun p => X p i j) (by
    filter_upwards [X.2] with p hp
    exact hp i j))
  left_inv M := by
    apply Matrix.ext
    intro i j
    apply FiniteAdeleRing.ext
    intro p
    rfl
  right_inv X := by
    apply RestrictedProduct.ext
    intro p
    apply Matrix.ext
    intro i j
    rfl
  map_mul' M N := by
    apply RestrictedProduct.ext
    intro p
    exact map_mul (finiteAdeleMatrixEval K n p) M N
  map_add' M N := by
    apply RestrictedProduct.ext
    intro p
    exact map_add (finiteAdeleMatrixEval K n p) M N

/-- Finite adelic matrix units are the restricted product of local matrix
units with respect to their integral subgroups. -/
def finiteAdeleMatrixUnitsRestrictedProductEquiv (n : Nat) :
    MulEquiv (Units (Matrix (Fin n) (Fin n) FA))
      (RestrictedProduct (fun p : P => Units (finiteLocalMatrix K n p))
        (fun p => (Submonoid.ofClass (finiteLocalIntegralMatrices K n p)).units)
        Filter.cofinite) :=
  (Units.mapEquiv (finiteAdeleMatrixRestrictedProductEquiv K n).toMulEquiv).trans
    (RestrictedProduct.unitsEquiv (finiteLocalMatrix K n)
      (B := finiteLocalIntegralMatrices K n))

/-- In the restricted product, the coordinate at each place is local
matrix evaluation on units. -/
theorem finiteAdeleMatrixUnitsRestrictedProductEquiv_apply (n : Nat) (p : P)
    (g : Units (Matrix (Fin n) (Fin n) FA)) :
    finiteAdeleMatrixUnitsRestrictedProductEquiv K n g p =
      Units.map (finiteAdeleMatrixEval K n p) g := rfl


private abbrev finiteAdeleMatrixUnits (n : Nat) :=
  Units (Matrix (Fin n) (Fin n) FA)

/-- Invertible matrices whose matrices and inverses have integral entries
at a finite place. -/
abbrev finiteLocalMatrixUnitSubgroup (n : Nat) (p : P) :=
  (Submonoid.ofClass (finiteLocalIntegralMatrices K n p)).units

/-- Local matrix units with an integrality restriction on the given filter. -/
abbrev finiteLocalMatrixUnitProduct (n : Nat) (f : Filter P) :=
  RestrictedProduct (fun p : P => Units (finiteLocalMatrix K n p))
    (fun p => (finiteLocalMatrixUnitSubgroup K n p : Set (Units (finiteLocalMatrix K n p)))) f

private theorem continuous_finiteAdeleMatrixEval (n : Nat) (p : P) :
    Continuous (finiteAdeleMatrixEval K n p) := by
  change Continuous (fun M : Matrix (Fin n) (Fin n) FA => fun i j => M i j p)
  exact continuous_pi (fun i => continuous_pi (fun j =>
    (RestrictedProduct.continuous_eval p).comp ((continuous_apply j).comp (continuous_apply i))))

private theorem isOpen_finiteLocalMatrixUnitSubgroup (n : Nat) (p : P) :
    IsOpen (finiteLocalMatrixUnitSubgroup K n p : Set (Units (finiteLocalMatrix K n p))) := by
  apply Submonoid.isOpen_units
  have hInt : IsOpen (p.adicCompletionIntegers K : Set (p.adicCompletion K)) :=
    Valued.isOpen_valuationSubring (p.adicCompletion K)
  have hEntry (i j : Fin n) :
      Continuous (fun M : finiteLocalMatrix K n p => M i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have hOpen := isOpen_iInter_of_finite (fun i : Fin n =>
    isOpen_iInter_of_finite (fun j : Fin n => hInt.preimage (hEntry i j)))
  convert hOpen using 1
  ext M
  simp only [Set.mem_iInter, Set.mem_preimage]
  rfl

/-- The local coordinates of finite adelic matrix units are continuous
for the restricted-product topology. -/
theorem continuous_finiteAdeleMatrixUnitsRestrictedProductEquiv (n : Nat) :
    Continuous (finiteAdeleMatrixUnitsRestrictedProductEquiv K n) := by
  let G := finiteAdeleMatrixUnits K n
  let e := finiteAdeleMatrixUnitsRestrictedProductEquiv K n
  let b : (p : P) -> Set (Units (finiteLocalMatrix K n p)) :=
    fun p => (finiteLocalMatrixUnitSubgroup K n p : Set (Units (finiteLocalMatrix K n p)))
  let _ : Fact (forall p, IsOpen (b p)) :=
    Fact.mk (isOpen_finiteLocalMatrixUnitSubgroup K n)
  let I : Set FA := {a | forall p : P, Membership.mem (p.adicCompletionIntegers K) (a p)}
  let T : Set (Matrix (Fin n) (Fin n) FA) := Set.iInter (fun i : Fin n =>
    Set.iInter (fun j : Fin n => Set.preimage (fun M => M i j) I))
  let U : Set G := Set.inter (Set.preimage (fun g : G => g.val) T)
    (Set.preimage (fun g : G => g.inv) T)
  have hI : IsOpen I :=
    RestrictedProduct.isOpen_forall_mem
      (R := fun p : P => p.adicCompletion K)
      (A := fun p => (p.adicCompletionIntegers K : Set (p.adicCompletion K)))
      (fun p => Valued.isOpen_valuationSubring (p.adicCompletion K))
  have hT : IsOpen T :=
    isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j =>
      hI.preimage ((continuous_apply j).comp (continuous_apply i))))
  have hU : IsOpen U :=
    (hT.preimage Units.continuous_val).inter (hT.preimage Units.continuous_coe_inv)
  have hOne : Membership.mem U (1 : G) := by
    have hE (i j : Fin n) : Membership.mem I ((1 : Matrix (Fin n) (Fin n) FA) i j) := by
      intro p
      by_cases eij : i = j
      next => simp [eij, Matrix.one_apply, show (1 : FA) p = 1 from rfl]
      next => simp [eij, show (0 : FA) p = 0 from rfl]
    have hIdentity : Membership.mem T (1 : Matrix (Fin n) (Fin n) FA) := by
      simpa only [T, Set.mem_preimage, Set.mem_iInter] using hE
    exact And.intro hIdentity hIdentity
  have hCoord (p : P) : Continuous (fun g : G => e g p) :=
    (continuous_finiteAdeleMatrixEval K n p).units_map _
  let u : U -> finiteLocalMatrixUnitProduct K n Top.top := fun g =>
    Subtype.mk (fun p => e g.val p) (Filter.eventually_top.mpr (by
      intro p
      have hVal : forall i j : Fin n, Membership.mem I (g.val.val i j) := by
        simpa only [T, Set.mem_preimage, Set.mem_iInter] using g.property.1
      have hInv : forall i j : Fin n, Membership.mem I (g.val.inv i j) := by
        simpa only [T, Set.mem_preimage, Set.mem_iInter] using g.property.2
      exact And.intro (fun i j => hVal i j p) (fun i j => hInv i j p)))
  have hChart : Continuous u := RestrictedProduct.continuous_rng_of_top.mpr
    (continuous_pi (fun p => (hCoord p).comp continuous_subtype_val))
  have hRestr : ContinuousOn e U := continuousOn_iff_continuous_domRestrict.mpr
    ((RestrictedProduct.continuous_inclusion (le_top : Filter.cofinite <= (Top.top : Filter P))).comp
      hChart)
  exact continuous_of_continuousAt_one e (hRestr.continuousAt (hU.mem_nhds hOne))

/-- Reassembling the local matrix units into a finite adelic matrix unit
is continuous. -/
theorem continuous_finiteAdeleMatrixUnitsRestrictedProductEquiv_symm (n : Nat) :
    Continuous (finiteAdeleMatrixUnitsRestrictedProductEquiv K n).symm := by
  let e := finiteAdeleMatrixUnitsRestrictedProductEquiv K n
  let C := finiteLocalMatrixUnitProduct K n Filter.cofinite
  let b : (p : P) -> Set (p.adicCompletion K) :=
    fun p => (p.adicCompletionIntegers K : Set (p.adicCompletion K))
  apply Units.continuous_iff.mpr
  have hEntry (i j : Fin n) :
      Continuous (fun x : C => (e.symm x).val i j) := by
    apply RestrictedProduct.continuous_dom.mpr
    intro S hS
    let y : finiteLocalMatrixUnitProduct K n (Filter.principal S) ->
        RestrictedProduct (fun p : P => p.adicCompletion K) b (Filter.principal S) :=
      fun x => Subtype.mk (fun p => (x p).val i j)
        (x.2.mono (fun p hp => hp.1 i j))
    have hy : Continuous y := by
      apply RestrictedProduct.continuous_rng_of_principal.mpr
      apply continuous_pi
      intro p
      change Continuous (fun x : finiteLocalMatrixUnitProduct K n (Filter.principal S) =>
        (x p).val i j)
      have hIJ : Continuous (fun M : finiteLocalMatrix K n p => M i j) :=
        (continuous_apply j).comp (continuous_apply i)
      exact hIJ.comp (Units.continuous_val.comp (RestrictedProduct.continuous_eval p))
    exact (RestrictedProduct.continuous_inclusion hS).comp hy
  have hInvEntry (i j : Fin n) :
      Continuous (fun x : C => (e.symm x).inv i j) := by
    apply RestrictedProduct.continuous_dom.mpr
    intro S hS
    let y : finiteLocalMatrixUnitProduct K n (Filter.principal S) ->
        RestrictedProduct (fun p : P => p.adicCompletion K) b (Filter.principal S) :=
      fun x => Subtype.mk (fun p => (x p).inv i j)
        (x.2.mono (fun p hp => hp.2 i j))
    have hy : Continuous y := by
      apply RestrictedProduct.continuous_rng_of_principal.mpr
      apply continuous_pi
      intro p
      change Continuous (fun x : finiteLocalMatrixUnitProduct K n (Filter.principal S) =>
        (x p).inv i j)
      have hIJ : Continuous (fun M : finiteLocalMatrix K n p => M i j) :=
        (continuous_apply j).comp (continuous_apply i)
      exact hIJ.comp (Units.continuous_coe_inv.comp (RestrictedProduct.continuous_eval p))
    exact (RestrictedProduct.continuous_inclusion hS).comp hy
  exact And.intro (continuous_pi (fun i => continuous_pi (hEntry i)))
    (continuous_pi (fun i => continuous_pi (hInvEntry i)))

/-- The local matrix unit coordinates give a topological group
isomorphism of finite adelic matrix units and the restricted product. -/
def finiteAdeleMatrixUnitsRestrictedProductHomeomorph (n : Nat) :
    ContinuousMulEquiv (finiteAdeleMatrixUnits K n)
      (finiteLocalMatrixUnitProduct K n Filter.cofinite) where
  __ := finiteAdeleMatrixUnitsRestrictedProductEquiv K n
  continuous_toFun := continuous_finiteAdeleMatrixUnitsRestrictedProductEquiv K n
  continuous_invFun := continuous_finiteAdeleMatrixUnitsRestrictedProductEquiv_symm K n

end FiniteMatrixCoordinates

section PrincipalSubgroupChart

variable {J : Type*} (G : J -> Type*)
variable [forall p, Group (G p)] [forall p, TopologicalSpace (G p)]
variable (U : forall p, Subgroup (G p))

local notation "C" => fun p => (U p : Set (G p))

/-- A principal restricted-product chart has unrestricted coordinates on
its exceptional set and subgroup coordinates at every other place. -/
def restrictedProductPrincipalSubgroupChart (S : Set J) :
    ContinuousMulEquiv (RestrictedProduct G C
      (Filter.principal {p | Not (Membership.mem S p)}))
      (Prod ((p : S) -> G p.val)
        ((p : {j : J // Not (Membership.mem S j)}) -> U p.val)) := by
  classical
  let X := RestrictedProduct G C (Filter.principal {p | Not (Membership.mem S p)})
  let Y := Prod ((p : S) -> G p.val)
    ((p : {j : J // Not (Membership.mem S j)}) -> U p.val)
  let evalOutside (x : X) (p : {j : J // Not (Membership.mem S j)}) : U p.val :=
    Subtype.mk (x p.val) (Filter.eventually_principal.mp x.2 p.val p.property)
  let merge (y : Y) (p : J) : G p :=
    if hp : Membership.mem S p then y.1 (Subtype.mk p hp)
      else (y.2 (Subtype.mk p hp)).val
  let e : MulEquiv X Y :=
    { toFun := fun x => (fun p => x p.val, evalOutside x)
      invFun := fun y => Subtype.mk (merge y) (Filter.eventually_principal.mpr (by
        intro p hp
        change Not (Membership.mem S p) at hp
        simp only [merge, dif_neg hp]
        exact (y.2 (Subtype.mk p hp)).property))
      left_inv := by
        intro x
        apply RestrictedProduct.ext
        intro p
        change merge (fun p : S => x p.val, evalOutside x) p = x p
        by_cases hp : Membership.mem S p <;> simp [merge, hp, evalOutside]
      right_inv := by
        intro y
        apply Prod.ext
        next =>
          funext p
          change merge y p.val = y.1 p
          simp [merge, p.property]
        next =>
          funext p
          apply Subtype.ext
          change merge y p.val = (y.2 p).val
          simp [merge, p.property]
      map_mul' := by
        intro x y
        rfl }
  refine { __ := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  next =>
    exact (continuous_pi (fun p => RestrictedProduct.continuous_eval p.val)).prodMk
      (continuous_pi (fun p => (RestrictedProduct.continuous_eval p.val).subtype_mk _))
  next =>
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro p
    change Continuous (fun y : Y => merge y p)
    by_cases hp : Membership.mem S p
    next =>
      have hMerge : (fun y : Y => merge y p) = (fun y : Y => y.1 (Subtype.mk p hp)) := by
        funext y
        exact dif_pos hp
      rw [hMerge]
      exact (continuous_apply (Subtype.mk p hp)).comp continuous_fst
    next =>
      have hMerge : (fun y : Y => merge y p) =
          (fun y : Y => (y.2 (Subtype.mk p hp)).val) := by
        funext y
        exact dif_neg hp
      rw [hMerge]
      exact continuous_subtype_val.comp ((continuous_apply (Subtype.mk p hp)).comp continuous_snd)

end PrincipalSubgroupChart

section FiniteMatrixHaarCharts

open MeasureTheory MeasureTheory.Measure

variable (K : Type*) [Field K] [NumberField K]

local notation "P" => HeightOneSpectrum (RingOfIntegers K)
local notation "FA" => FiniteAdeleRing (RingOfIntegers K) K

/-- The matrix-unit coordinates in a finite-place chart. Each exceptional
place contributes the whole local group, and each other place contributes
its integral subgroup. -/
abbrev FiniteAdeleMatrixHaarChart (n : Nat) (S : Finset P) :=
  Prod ((p : (S : Set P)) -> Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K)))
    ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val)

omit [NumberField K] in
private theorem cofinite_le_principal_finitePlaceComplement (S : Finset P) :
    Filter.cofinite <= Filter.principal (Compl.compl (S : Set P)) := by
  apply Filter.le_principal_iff.mpr
  apply Filter.mem_cofinite.mpr
  rw [compl_compl]
  exact S.finite_toSet

private def finiteAdeleMatrixHaarChartIntoRestrictedProduct (n : Nat) (S : Finset P) :
    MonoidHom (FiniteAdeleMatrixHaarChart K n S)
      (finiteLocalMatrixUnitProduct K n Filter.cofinite) := by
  let hS := cofinite_le_principal_finitePlaceComplement K S
  let U := finiteLocalMatrixUnitSubgroup K n
  let T := fun p : P => Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))
  let c := restrictedProductPrincipalSubgroupChart T U (S : Set P)
  let F := Filter.principal (Compl.compl (S : Set P))
  let incl : MonoidHom (finiteLocalMatrixUnitProduct K n F)
      (finiteLocalMatrixUnitProduct K n Filter.cofinite) :=
    { toFun := RestrictedProduct.inclusion T (fun p => (U p : Set (T p))) hS
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact incl.comp c.symm.toMonoidHom

/-- Reassemble the chart coordinates into a finite adelic matrix unit. -/
def finiteAdeleMatrixHaarChartEmbedding (n : Nat) (S : Finset P) :
    MonoidHom (FiniteAdeleMatrixHaarChart K n S)
      (Units (Matrix (Fin n) (Fin n) FA)) :=
  (finiteAdeleMatrixUnitsRestrictedProductHomeomorph K n).symm.toMonoidHom.comp
    (finiteAdeleMatrixHaarChartIntoRestrictedProduct K n S)

/-- The finite-place product chart identifies an open subset of the finite
adelic matrix-unit group. -/
theorem isOpenEmbedding_finiteAdeleMatrixHaarChartEmbedding (n : Nat) (S : Finset P) :
    Topology.IsOpenEmbedding (finiteAdeleMatrixHaarChartEmbedding K n S) := by
  let U := finiteLocalMatrixUnitSubgroup K n
  let T := fun p : P => Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))
  let c := restrictedProductPrincipalSubgroupChart T U (S : Set P)
  let d := finiteAdeleMatrixUnitsRestrictedProductHomeomorph K n
  let hS := cofinite_le_principal_finitePlaceComplement K S
  have hU (p : P) : IsOpen (U p : Set (T p)) := isOpen_finiteLocalMatrixUnitSubgroup K n p
  have hIncl := RestrictedProduct.isOpenEmbedding_inclusion_principal
    (R := T) (A := fun p => (U p : Set (T p))) hU hS
  exact d.symm.toHomeomorph.isOpenEmbedding.comp
    (hIncl.comp c.symm.toHomeomorph.isOpenEmbedding)

/-- The pullback of finite adelic Haar measure by a product chart is Haar. -/
theorem isHaarMeasure_comap_finiteAdeleMatrixHaarChartEmbedding
    (n : Nat) (S : Finset P)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [MeasurableMul (Units (Matrix (Fin n) (Fin n) FA))]
    [MeasurableSpace (FiniteAdeleMatrixHaarChart K n S)]
    [BorelSpace (FiniteAdeleMatrixHaarChart K n S)]
    [MeasurableMul (FiniteAdeleMatrixHaarChart K n S)]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) FA))) [mu.IsHaarMeasure] :
    (mu.comap (finiteAdeleMatrixHaarChartEmbedding K n S)).IsHaarMeasure :=
  IsHaarMeasure.comap (mH := inferInstance) mu
    (isOpenEmbedding_finiteAdeleMatrixHaarChartEmbedding K n S)


/-- At an exceptional place the assembled matrix evaluates to the
unrestricted chart coordinate. -/
theorem finiteAdeleMatrixHaarChartEval_of_mem (n : Nat) (S : Finset P)
    (x : FiniteAdeleMatrixHaarChart K n S) (p : (S : Set P)) :
    Units.map (finiteAdeleMatrixEval K n p.val) (finiteAdeleMatrixHaarChartEmbedding K n S x) =
      x.1 p := by
  let T := fun p : P => Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))
  let c := restrictedProductPrincipalSubgroupChart T (finiteLocalMatrixUnitSubgroup K n) (S : Set P)
  let d := finiteAdeleMatrixUnitsRestrictedProductHomeomorph K n
  let z := finiteAdeleMatrixHaarChartIntoRestrictedProduct K n S x
  have hd := congrArg (fun w : finiteLocalMatrixUnitProduct K n Filter.cofinite => w p.val)
    (d.apply_symm_apply z)
  have hc := congrArg (fun w : FiniteAdeleMatrixHaarChart K n S => w.1 p)
    (c.apply_symm_apply x)
  exact hd.trans hc

/-- Outside the exceptional places the assembled matrix evaluates to the
integral chart coordinate. -/
theorem finiteAdeleMatrixHaarChartEval_of_notMem (n : Nat) (S : Finset P)
    (x : FiniteAdeleMatrixHaarChart K n S) (p : {q : P // Not (Membership.mem (S : Set P) q)}) :
    Units.map (finiteAdeleMatrixEval K n p.val) (finiteAdeleMatrixHaarChartEmbedding K n S x) =
      (x.2 p).val := by
  let T := fun p : P => Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))
  let c := restrictedProductPrincipalSubgroupChart T (finiteLocalMatrixUnitSubgroup K n) (S : Set P)
  let d := finiteAdeleMatrixUnitsRestrictedProductHomeomorph K n
  let z := finiteAdeleMatrixHaarChartIntoRestrictedProduct K n S x
  have hd := congrArg (fun w : finiteLocalMatrixUnitProduct K n Filter.cofinite => w p.val)
    (d.apply_symm_apply z)
  have hc := congrArg (fun w : FiniteAdeleMatrixHaarChart K n S => (w.2 p).val)
    (c.apply_symm_apply x)
  exact hd.trans hc

/-- A finite adelic matrix unit is integral exactly when it and its inverse
have integral entries at every finite place. -/
theorem mem_integralFiniteAdeleMatrixGroup_iff_forall_local (n : Nat)
    (g : Units (Matrix (Fin n) (Fin n) FA)) :
    Membership.mem (integralFiniteAdeleMatrixGroup K n) g <->
      forall p : P, Membership.mem (finiteLocalMatrixUnitSubgroup K n p)
        (Units.map (finiteAdeleMatrixEval K n p) g) := by
  constructor
  next =>
    intro hg p
    exact And.intro (fun i j => hg.1 i j p) (fun i j => hg.2 i j p)
  next =>
    intro h
    exact And.intro (fun i j p => (h p).1 i j) (fun i j p => (h p).2 i j)

/-- The integral part of a chart restricts its exceptional coordinates
to the local integral subgroups. -/
def finiteAdeleMatrixHaarChartIntegralSet (n : Nat) (S : Finset P) :
    Set (FiniteAdeleMatrixHaarChart K n S) :=
  Set.prod (Set.pi Set.univ
    (fun p : (S : Set P) => (finiteLocalMatrixUnitSubgroup K n p.val :
      Set (Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K)))))) Set.univ

/-- The chart coordinates of the global integral subgroup are integral
at all exceptional places. -/
theorem preimage_integralFiniteAdeleMatrixGroup_finiteAdeleMatrixHaarChartEmbedding
    (n : Nat) (S : Finset P) :
    Set.preimage (finiteAdeleMatrixHaarChartEmbedding K n S)
      (integralFiniteAdeleMatrixGroup K n : Set (Units (Matrix (Fin n) (Fin n) FA))) =
      finiteAdeleMatrixHaarChartIntegralSet K n S := by
  ext x
  change Membership.mem (integralFiniteAdeleMatrixGroup K n)
    (finiteAdeleMatrixHaarChartEmbedding K n S x) <-> _
  rw [mem_integralFiniteAdeleMatrixGroup_iff_forall_local K n]
  constructor
  next =>
    intro h
    refine And.intro ?_ (Set.mem_univ _)
    intro p hp
    have hLocal := h p.val
    rwa [finiteAdeleMatrixHaarChartEval_of_mem K n S x p] at hLocal
  next =>
    intro h p
    by_cases hp : Membership.mem (S : Set P) p
    next =>
      rw [finiteAdeleMatrixHaarChartEval_of_mem K n S x (Subtype.mk p hp)]
      exact h.1 (Subtype.mk p hp) (Set.mem_univ _)
    next =>
      rw [finiteAdeleMatrixHaarChartEval_of_notMem K n S x (Subtype.mk p hp)]
      exact (x.2 (Subtype.mk p hp)).property

/-- A matrix unit belongs to a chart exactly when its local coordinates
are integral outside the exceptional places. -/
theorem mem_range_finiteAdeleMatrixHaarChartEmbedding_iff (n : Nat) (S : Finset P)
    (g : Units (Matrix (Fin n) (Fin n) FA)) :
    Membership.mem (Set.range (finiteAdeleMatrixHaarChartEmbedding K n S)) g <->
      forall p : P, Not (Membership.mem (S : Set P) p) ->
        Membership.mem (finiteLocalMatrixUnitSubgroup K n p)
          (Units.map (finiteAdeleMatrixEval K n p) g) := by
  constructor
  next =>
    intro h p hp
    choose x hx using h
    rw [<- hx, finiteAdeleMatrixHaarChartEval_of_notMem K n S x (Subtype.mk p hp)]
    exact (x.2 (Subtype.mk p hp)).property
  next =>
    intro h
    let T := fun p : P => Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))
    let U := finiteLocalMatrixUnitSubgroup K n
    let c := restrictedProductPrincipalSubgroupChart T U (S : Set P)
    let d := finiteAdeleMatrixUnitsRestrictedProductHomeomorph K n
    let hS := cofinite_le_principal_finitePlaceComplement K S
    let w : finiteLocalMatrixUnitProduct K n (Filter.principal (Compl.compl (S : Set P))) :=
      Subtype.mk (fun p => d g p) (Filter.eventually_principal.mpr h)
    refine Exists.intro (c w) ?_
    change d.symm (RestrictedProduct.inclusion T (fun p => (U p : Set (T p))) hS
      (c.symm (c w))) = g
    rw [c.symm_apply_apply]
    exact d.symm_apply_apply g

/-- Allowing more exceptional places enlarges the chart image. -/
theorem monotone_range_finiteAdeleMatrixHaarChartEmbedding (n : Nat) :
    Monotone (fun S : Finset P => Set.range (finiteAdeleMatrixHaarChartEmbedding K n S)) := by
  intro S T hST g hg
  have h := (mem_range_finiteAdeleMatrixHaarChartEmbedding_iff K n S g).mp hg
  exact (mem_range_finiteAdeleMatrixHaarChartEmbedding_iff K n T g).mpr
    (fun p hp => h p (fun hs => hp (hST hs)))

/-- The finite-place chart images cover the finite adelic matrix-unit group. -/
theorem iUnion_range_finiteAdeleMatrixHaarChartEmbedding (n : Nat) :
    Set.iUnion (fun S : Finset P => Set.range (finiteAdeleMatrixHaarChartEmbedding K n S)) =
      (Set.univ : Set (Units (Matrix (Fin n) (Fin n) FA))) := by
  ext g
  constructor
  next =>
    intro _
    exact Set.mem_univ g
  next =>
    intro _
    let z := finiteAdeleMatrixUnitsRestrictedProductHomeomorph K n g
    let Q : Set P := {p | Membership.mem (finiteLocalMatrixUnitSubgroup K n p) (z p)}
    have hQ : (Compl.compl Q).Finite := Filter.mem_cofinite.mp z.2
    apply Set.mem_iUnion.mpr
    refine Exists.intro hQ.toFinset ?_
    apply (mem_range_finiteAdeleMatrixHaarChartEmbedding_iff K n hQ.toFinset g).mpr
    intro p hp
    by_contra h
    apply hp
    exact (Set.Finite.mem_toFinset hQ).mpr h

/-- The integral part of each chart maps onto the whole integral
finite adelic matrix subgroup. -/
theorem image_finiteAdeleMatrixHaarChartIntegralSet (n : Nat) (S : Finset P) :
    Set.image (finiteAdeleMatrixHaarChartEmbedding K n S)
      (finiteAdeleMatrixHaarChartIntegralSet K n S) =
      (integralFiniteAdeleMatrixGroup K n : Set (Units (Matrix (Fin n) (Fin n) FA))) := by
  have hRange : (integralFiniteAdeleMatrixGroup K n : Set (Units (Matrix (Fin n) (Fin n) FA))) <=
      Set.range (finiteAdeleMatrixHaarChartEmbedding K n S) := by
    intro g hg
    exact (mem_range_finiteAdeleMatrixHaarChartEmbedding_iff K n S g).mpr
      (fun p _ => (mem_integralFiniteAdeleMatrixGroup_iff_forall_local K n g).mp hg p)
  rw [<- preimage_integralFiniteAdeleMatrixGroup_finiteAdeleMatrixHaarChartEmbedding K n S,
    Set.image_preimage_eq_inter_range, Set.inter_eq_self_of_subset_left hRange]

/-- Haar measure normalized on the global integral subgroup pulls back
to the product of the individually normalized local Haar measures at
the exceptional places and Haar probability measure on the tail. -/
theorem comap_finiteAdeleMatrixHaarChartEmbedding_eq_pi_prod
    (n : Nat) (S : Finset P) [Fintype (S : Set P)]
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [MeasurableMul (Units (Matrix (Fin n) (Fin n) FA))]
    [forall p : (S : Set P), MeasurableSpace
      (Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K)))]
    [forall p : (S : Set P), MeasurableMul
      (Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K)))]
    [MeasurableSpace ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val)]
    [MeasurableMul ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val)]
    [BorelSpace (FiniteAdeleMatrixHaarChart K n S)]
    [LocallyCompactSpace (FiniteAdeleMatrixHaarChart K n S)]
    [SecondCountableTopology (FiniteAdeleMatrixHaarChart K n S)]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) FA))) [mu.IsHaarMeasure]
    (hMu : mu (integralFiniteAdeleMatrixGroup K n :
      Set (Units (Matrix (Fin n) (Fin n) FA))) = 1)
    (localHaar : forall p : (S : Set P),
      Measure (Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K))))
    [forall p, (localHaar p).IsHaarMeasure] [forall p, SigmaFinite (localHaar p)]
    (hLocal : forall p, localHaar p (finiteLocalMatrixUnitSubgroup K n p.val :
      Set (Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K)))) = 1)
    (tailHaar : Measure ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val))
    [tailHaar.IsHaarMeasure] [IsProbabilityMeasure tailHaar] :
    mu.comap (finiteAdeleMatrixHaarChartEmbedding K n S) =
      (Measure.pi localHaar).prod tailHaar := by
  let D := FiniteAdeleMatrixHaarChart K n S
  let E := finiteAdeleMatrixHaarChartEmbedding K n S
  let W := finiteAdeleMatrixHaarChartIntegralSet K n S
  let rho : Measure D := mu.comap E
  let eta : Measure D := (Measure.pi localHaar).prod tailHaar
  let _ : rho.IsHaarMeasure := isHaarMeasure_comap_finiteAdeleMatrixHaarChartEmbedding K n S mu
  let _ : eta.IsHaarMeasure := inferInstanceAs (((Measure.pi localHaar).prod tailHaar).IsHaarMeasure)
  have hRho : rho W = 1 := by
    change (mu.comap E) W = 1
    rw [(isOpenEmbedding_finiteAdeleMatrixHaarChartEmbedding K n S).measurableEmbedding.comap_apply,
      image_finiteAdeleMatrixHaarChartIntegralSet K n S, hMu]
  have hEta : eta W = 1 := by
    let V := Set.pi Set.univ (fun p : (S : Set P) =>
      (finiteLocalMatrixUnitSubgroup K n p.val :
        Set (Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K)))))
    have hV : (Measure.pi localHaar) V = 1 := by
      dsimp only [V]
      rw [Measure.pi_pi]
      simp only [hLocal, Finset.prod_const_one]
    change ((Measure.pi localHaar).prod tailHaar) (Set.prod V Set.univ) = 1
    calc
      _ = (Measure.pi localHaar) V * tailHaar Set.univ := Measure.prod_prod _ _
      _ = 1 := by rw [hV, IsProbabilityMeasure.measure_univ, one_mul]
  let k := haarScalarFactor rho eta
  have hScale : rho = SMul.smul k eta := isMulLeftInvariant_eq_smul rho eta
  have hK : k = 1 := by
    apply ENNReal.coe_eq_one.mp
    calc
      (k : ENNReal) = (k : ENNReal) * eta W := by rw [hEta, mul_one]
      _ = (SMul.smul k eta) W := (Measure.coe_nnreal_smul_apply k eta W).symm
      _ = rho W := (congrArg (fun M : Measure D => M W) hScale).symm
      _ = 1 := hRho
  exact hScale.trans (by rw [hK]; exact one_smul NNReal eta)


/-- On a chart with product measure, the integral of a function that
factors through the exceptional coordinates is the product of the
local integrals. Local integrability implies integrability on the chart. -/
theorem integrableOnAndSetIntegral_finiteAdeleMatrixHaarChartEmbedding
    {k : Type*} [RCLike k] (n : Nat) (S : Finset P) [Fintype (S : Set P)]
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [forall p : (S : Set P), MeasurableSpace
      (Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K)))]
    [MeasurableSpace ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val)]
    [BorelSpace (FiniteAdeleMatrixHaarChart K n S)]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) FA)))
    (localHaar : forall p : (S : Set P),
      Measure (Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K))))
    [forall p, SigmaFinite (localHaar p)]
    (tailHaar : Measure ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val))
    [IsProbabilityMeasure tailHaar]
    (hMeasure : mu.comap (finiteAdeleMatrixHaarChartEmbedding K n S) =
      (Measure.pi localHaar).prod tailHaar)
    (F : Units (Matrix (Fin n) (Fin n) FA) -> k)
    (f : forall p : (S : Set P), Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K)) -> k)
    (hInt : forall p, Integrable (f p) (localHaar p))
    (hFactor : forall x : FiniteAdeleMatrixHaarChart K n S,
      F (finiteAdeleMatrixHaarChartEmbedding K n S x) =
        Finset.univ.prod (fun p => f p (x.1 p))) :
    let S' := Set.range (finiteAdeleMatrixHaarChartEmbedding K n S)
    And (IntegrableOn F S' mu) (integral (mu.restrict S') F =
      Finset.univ.prod (fun p => integral (localHaar p) (f p))) := by
  let D := FiniteAdeleMatrixHaarChart K n S
  let E := finiteAdeleMatrixHaarChartEmbedding K n S
  let nu := Measure.pi localHaar
  let m : Measure D := nu.prod tailHaar
  let B (x : (p : (S : Set P)) -> Units (Matrix (Fin n) (Fin n) (p.val.adicCompletion K))) :=
    Finset.univ.prod (fun p => f p (x p))
  have hE : MeasurableEmbedding E :=
    (isOpenEmbedding_finiteAdeleMatrixHaarChartEmbedding K n S).measurableEmbedding
  have hPres : MeasurePreserving E m (mu.restrict (Set.range E)) :=
    { measurable := hE.measurable
      map_eq := by
        change Measure.map E ((Measure.pi localHaar).prod tailHaar) =
          mu.restrict (Set.range E)
        rw [<- hMeasure]
        exact hE.map_comap mu }
  have hFst : MeasurePreserving (Prod.fst : D -> _) m nu := measurePreserving_fst
  have hB : Integrable B nu := Integrable.fintype_prod_dep hInt
  have hF : Function.comp F E = Function.comp B (Prod.fst : D -> _) := funext hFactor
  have hIntComp : Integrable (Function.comp F E) m := by
    rw [hF]
    exact hFst.integrable_comp_of_integrable hB
  have hStrong : AEStronglyMeasurable B (Measure.map Prod.fst m) := by
    rw [hFst.map_eq]
    exact hB.aestronglyMeasurable
  refine And.intro ((hPres.integrable_comp_emb hE).mp hIntComp) ?_
  calc
    integral (mu.restrict (Set.range E)) F = integral m (Function.comp F E) :=
      (hPres.integral_comp hE F).symm
    _ = integral m (Function.comp B Prod.fst) := by rw [hF]
    _ = integral (Measure.map Prod.fst m) B :=
      (integral_map hFst.measurable.aemeasurable hStrong).symm
    _ = integral nu B := by rw [hFst.map_eq]
    _ = Finset.univ.prod (fun p => integral (localHaar p) (f p)) :=
      integral_fintype_prod_eq_prod f

/-- Form the finite adelic zeta integrand from its finite-place factors.
When all the factors are one on the integral subgroups, the restricted
product condition makes this product pointwise finite. -/
def finiteAdeleMatrixRestrictedZetaIntegrand (n : Nat)
    (f : forall p : P, Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)) -> Complex)
    (g : Units (Matrix (Fin n) (Fin n) FA)) : Complex :=
  finprod (fun p : P => f p (Units.map (finiteAdeleMatrixEval K n p) g))

/-- On a chart only the exceptional finite places contribute to the product. -/
theorem finiteAdeleMatrixRestrictedZetaIntegrand_on_chart
    (n : Nat) (S : Finset P) [Fintype (S : Set P)]
    (f : forall p : P, Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)) -> Complex)
    (hUnit : forall p g, Membership.mem (finiteLocalMatrixUnitSubgroup K n p) g -> f p g = 1)
    (x : FiniteAdeleMatrixHaarChart K n S) :
    finiteAdeleMatrixRestrictedZetaIntegrand K n f (finiteAdeleMatrixHaarChartEmbedding K n S x) =
      Finset.univ.prod (fun p : (S : Set P) => f p.val (x.1 p)) := by
  classical
  let u (p : P) := f p (Units.map (finiteAdeleMatrixEval K n p)
    (finiteAdeleMatrixHaarChartEmbedding K n S x))
  have hSupport : Set.Subset (Function.mulSupport u) (S : Set P) := by
    intro p hp
    by_contra hNot
    let q : {q : P // Not (Membership.mem (S : Set P) q)} := Subtype.mk p hNot
    have hEval := finiteAdeleMatrixHaarChartEval_of_notMem K n S x q
    have hOne : u p = 1 := (congrArg (f p) hEval).trans (hUnit p _ (x.2 q).property)
    exact hp hOne
  change finprod u = _
  have hS : S.finite_toSet.toFinset = S := Finset.finite_toSet_toFinset S
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hSupport S.finite_toSet, hS,
    Finset.prod_subtype (p := fun p => Membership.mem (S : Set P) p) S (fun _ => Iff.rfl)]
  apply Finset.prod_congr rfl
  intro p _
  exact congrArg (f p.val) (finiteAdeleMatrixHaarChartEval_of_mem K n S x p)

/-- Pass from the finite chart integrals to the full finite adelic integral
under a uniform bound on the integrals of the norm. -/
private theorem integrableAndHasProd_of_finiteAdeleMatrixHaarChartExhaustion
    (n : Nat) [Countable P] [(Filter.atTop : Filter (Finset P)).IsCountablyGenerated]
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) FA))] [BorelSpace (Units (Matrix (Fin n) (Fin n) FA))] (mu : Measure (Units (Matrix (Fin n) (Fin n) FA)))
    (F : Units (Matrix (Fin n) (Fin n) FA) -> Complex) (hF : AEStronglyMeasurable F mu)
    (C : Real)
    (hInt : forall S : Finset P, IntegrableOn F
      (Set.range (finiteAdeleMatrixHaarChartEmbedding K n S)) mu)
    (hBound : forall S : Finset P,
      integral (mu.restrict (Set.range (finiteAdeleMatrixHaarChartEmbedding K n S)))
        (fun g => norm (F g)) <= C)
    (a : P -> Complex)
    (hChart : forall S : Finset P,
      integral (mu.restrict (Set.range (finiteAdeleMatrixHaarChartEmbedding K n S))) F = S.prod a) :
    And (Integrable F mu) (HasProd a (integral mu F)) := by
  classical
  let U := fun S : Finset P => Set.range (finiteAdeleMatrixHaarChartEmbedding K n S)
  let w : Units (Matrix (Fin n) (Fin n) FA) -> ENNReal := fun g => ENorm.enorm (F g)
  let cut := fun S : Finset P => (U S).indicator w
  have hU : Monotone U := monotone_range_finiteAdeleMatrixHaarChartEmbedding K n
  have hAll : Set.iUnion U = Set.univ := iUnion_range_finiteAdeleMatrixHaarChartEmbedding K n
  have hMeas (S : Finset P) : MeasurableSet (U S) :=
    (isOpenEmbedding_finiteAdeleMatrixHaarChartEmbedding K n S).isOpen_range.measurableSet
  have hAEM (S : Finset P) : AEMeasurable (cut S) mu := hF.enorm.indicator (hMeas S)
  have hMon : Monotone cut := by
    intro S T hST g
    by_cases hS : Membership.mem (U S) g
    next =>
      have hT : Membership.mem (U T) g := hU hST hS
      change (U S).indicator w g <= (U T).indicator w g
      rw [Set.indicator_of_mem hS, Set.indicator_of_mem hT]
    next =>
      change (U S).indicator w g <= (U T).indicator w g
      rw [Set.indicator_of_notMem hS]
      exact zero_le
  have hSup (g : Units (Matrix (Fin n) (Fin n) FA)) : iSup (fun S => cut S g) = w g := by
    apply le_antisymm
    next =>
      apply iSup_le
      intro S
      change (U S).indicator w g <= w g
      by_cases hS : Membership.mem (U S) g
      next => rw [Set.indicator_of_mem hS]
      next =>
        rw [Set.indicator_of_notMem hS]
        exact zero_le
    next =>
      have hUnion : Membership.mem (Set.iUnion U) g := by
        rw [hAll]
        exact Set.mem_univ _
      choose S hS using Set.mem_iUnion.mp hUnion
      have hEq : cut S g = w g := Set.indicator_of_mem hS _
      rw [<- hEq]
      exact le_iSup (fun T => cut T g) S
  have hFin : lintegral mu w <= ENNReal.ofReal C := by
    calc
      lintegral mu w = iSup (fun S => lintegral mu (cut S)) := by
        rw [<- funext hSup]
        exact lintegral_iSup_directed hAEM hMon.directed_le
      _ <= ENNReal.ofReal C := by
        apply iSup_le
        intro S
        change lintegral mu ((U S).indicator w) <= ENNReal.ofReal C
        rw [lintegral_indicator (hMeas S)]
        exact (ofReal_integral_norm_eq_lintegral_enorm (hInt S)).symm.le.trans
          (ENNReal.ofReal_le_ofReal (hBound S))
  have hGlobal : Integrable F mu :=
    And.intro hF (hasFiniteIntegral_iff_enorm.mpr (hFin.trans_lt ENNReal.ofReal_lt_top))
  have hUnionInt : IntegrableOn F (Set.iUnion U) mu := by
    rw [hAll]
    exact hGlobal.integrableOn
  have hTendsto : Filter.Tendsto (fun S => integral (mu.restrict (U S)) F)
      Filter.atTop (nhds (integral mu F)) := by
    simpa only [hAll, Measure.restrict_univ] using
      tendsto_setIntegral_of_monotone hMeas hU hUnionInt
  refine And.intro hGlobal ?_
  change Filter.Tendsto (fun S : Finset P => S.prod a) Filter.atTop (nhds (integral mu F))
  rw [<- funext hChart]
  exact hTendsto


/-- Normalized chart measures turn an absolutely integrable restricted
product of local factors into an Euler product of local integrals. A single
bound on all finite products of the absolute local integrals gives global
integrability. -/
theorem integrableAndHasProd_finiteAdeleMatrixRestrictedZetaIntegrand
    (n : Nat) [Countable P] [(Filter.atTop : Filter (Finset P)).IsCountablyGenerated]
    [forall S : Finset P, Fintype (S : Set P)]
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) FA))]
    [forall p : P, MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [forall S : Finset P, MeasurableSpace ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val)]
    [forall S : Finset P, BorelSpace (FiniteAdeleMatrixHaarChart K n S)]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) FA)))
    (localHaar : forall p : P, Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    [forall p, SigmaFinite (localHaar p)]
    (tailHaar : forall S : Finset P, Measure ((p : {q : P // Not (Membership.mem (S : Set P) q)}) ->
      finiteLocalMatrixUnitSubgroup K n p.val))
    [forall S, IsProbabilityMeasure (tailHaar S)]
    (hMeasure : forall S : Finset P, mu.comap (finiteAdeleMatrixHaarChartEmbedding K n S) =
      (Measure.pi (fun p : (S : Set P) => localHaar p.val)).prod (tailHaar S))
    (f : forall p : P, Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)) -> Complex)
    (hUnit : forall p g, Membership.mem (finiteLocalMatrixUnitSubgroup K n p) g -> f p g = 1)
    (hInt : forall p, Integrable (f p) (localHaar p))
    (C : Real)
    (hBound : forall S : Finset P,
      S.prod (fun p => integral (localHaar p) (fun g => norm (f p g))) <= C) :
    let F := finiteAdeleMatrixRestrictedZetaIntegrand K n f
    And (Integrable F mu) (HasProd (fun p => integral (localHaar p) (f p)) (integral mu F)) := by
  classical
  let F := finiteAdeleMatrixRestrictedZetaIntegrand K n f
  let U := fun S : Finset P => Set.range (finiteAdeleMatrixHaarChartEmbedding K n S)
  have hLocal (S : Finset P) := integrableOnAndSetIntegral_finiteAdeleMatrixHaarChartEmbedding
    K n S mu (fun p => localHaar p.val) (tailHaar S) (hMeasure S) F (fun p => f p.val)
    (fun p => hInt p.val) (finiteAdeleMatrixRestrictedZetaIntegrand_on_chart K n S f hUnit)
  have hMeas : AEStronglyMeasurable F mu := by
    have h := aestronglyMeasurable_iUnion_iff.mpr (fun S : Finset P => (hLocal S).1.1)
    change AEStronglyMeasurable F (mu.restrict (Set.iUnion U)) at h
    rwa [show Set.iUnion U = Set.univ from iUnion_range_finiteAdeleMatrixHaarChartEmbedding K n,
      Measure.restrict_univ] at h
  refine integrableAndHasProd_of_finiteAdeleMatrixHaarChartExhaustion K n mu F hMeas C
    (fun S => (hLocal S).1) ?_ (fun p => integral (localHaar p) (f p)) ?_
  next =>
    intro S
    have hNormFactor (x : FiniteAdeleMatrixHaarChart K n S) :
        norm (F (finiteAdeleMatrixHaarChartEmbedding K n S x)) =
          Finset.univ.prod (fun p : (S : Set P) => norm (f p.val (x.1 p))) := by
      rw [show F (finiteAdeleMatrixHaarChartEmbedding K n S x) =
          Finset.univ.prod (fun p : (S : Set P) => f p.val (x.1 p)) from
        finiteAdeleMatrixRestrictedZetaIntegrand_on_chart K n S f hUnit x, Complex.norm_prod]
    have hNorm := (integrableOnAndSetIntegral_finiteAdeleMatrixHaarChartEmbedding
      K n S mu (fun p => localHaar p.val) (tailHaar S) (hMeasure S)
      (fun g => norm (F g)) (fun p g => norm (f p.val g)) (fun p => (hInt p.val).norm)
      hNormFactor).2
    rw [hNorm, <- Finset.prod_subtype (p := fun p => Membership.mem (S : Set P) p) S
      (fun _ => Iff.rfl) (fun p => integral (localHaar p) (fun g => norm (f p g)))]
    exact hBound S
  next =>
    intro S
    exact (hLocal S).2.trans
      (Finset.prod_subtype (p := fun p => Membership.mem (S : Set P) p) S
        (fun _ => Iff.rfl) (fun p => integral (localHaar p) (f p))).symm

end FiniteMatrixHaarCharts

end Robin1984.GRH
