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

end Robin1984.GRH
