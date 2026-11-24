import Robin1984.GRH.GodementJacquetFiniteMatrixVolume
import Robin1984.GRH.HeckeFiniteIdealClass

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Finite idele norms and adjugate matrices in the Godement--Jacquet construction.
- Formalization note: Proves that the reciprocal finite determinant norm of an integral finite adelic matrix is a positive integer and clears the inverse matrix at every finite place.
- PROVENANCE-END
-/

/-!
# The finite determinant norm as an inverse denominator

For an integral finite idele the reciprocal norm is the product of prime
ideal norms raised to the local valuation exponents. That integer lies
in the required prime ideal powers and clears the inverse at each place.
Applying this to the determinant of an integral matrix and using the
adjugate identity gives a denominator for every entry of its inverse.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain
open scoped Classical

private theorem exists_localIntegralNormExponent
    {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (x : p.adicCompletion K)
    (hx0 : Not (x = 0)) (hx : Membership.mem (p.adicCompletionIntegers K) x) :
    Exists (fun n : Nat =>
      And ((Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) x =
          WithZero.exp (-(n : Int)))
        (norm x = Inv.inv ((p.asIdeal.absNorm : Real) ^ n))) := by
  let V : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
  have hv0 : Not (V x = 0) := V.ne_zero_iff.mpr hx0
  let e := WithZero.log (V x)
  have he : WithZero.exp e = V x := WithZero.exp_log hv0
  have he0 : e <= 0 := by
    apply WithZero.exp_le_exp.mp
    rw [he, WithZero.exp_zero]
    exact hx
  let n := (-e).toNat
  have hn : -(n : Int) = e := by
    have h := Int.toNat_of_nonneg (neg_nonneg.mpr he0)
    change (n : Int) = -e at h
    omega
  have hV : V x = WithZero.exp (-(n : Int)) := by rw [hn, he]
  refine Exists.intro n (And.intro hV ?_)
  rw [FinitePlace.norm_def, hV, WithZeroMulInt.toNNReal_neg_apply _ (by simp [WithZero.exp])]
  simp only [WithZero.exp, WithZero.unzero_coe]
  change NNReal.toReal ((p.asIdeal.absNorm : NNReal) ^ (-(n : Int))) = _
  simp only [zpow_neg, zpow_natCast, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_natCast]

/-- The reciprocal of the finite norm of an integral finite idele is a
positive rational integer that clears its inverse at every finite place. -/
theorem exists_finiteIdele_inverseDenominator_of_integral
    {K : Type*} [Field K] [NumberField K]
    (u : Units (FiniteAdeleRing (RingOfIntegers K) K))
    (hu : forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K) (u.val p)) :
    Exists (fun N : Nat => And (0 < N)
      (And ((N : Real) = Inv.inv (heckeFiniteIdeleNorm u))
        (forall p : HeightOneSpectrum (RingOfIntegers K),
          Membership.mem (p.adicCompletionIntegers K)
            (algebraMap (RingOfIntegers K) (p.adicCompletion K) (N : RingOfIntegers K) * u.inv p)))) := by
  let R := RingOfIntegers K
  let P := HeightOneSpectrum R
  let V (p : P) : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
  let f (p : P) := V p (u.val p)
  have huLocal (p : P) : Not (u.val p = 0) := (FiniteAdeleRing.isUnit_iff.mp u.isUnit).1 p
  have hSupp : Function.HasFiniteMulSupport f :=
    Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp u.isUnit).2
  let T := hSupp.toFinset
  choose n hn using fun p : P => exists_localIntegralNormExponent p (u.val p) (huLocal p) (hu p)
  let q (p : P) := p.asIdeal.absNorm ^ n p
  let N := Finset.prod T q
  have hN : 0 < N := Finset.prod_pos (fun p _ =>
    pow_pos (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)) _)
  have hS : Function.mulSupport (fun p : P => norm (u.val p)) <= Function.mulSupport f := by
    intro p hp
    change Not (norm (u.val p) = 1) at hp
    change Not (V p (u.val p) = 1)
    intro hv
    apply hp
    rw [FinitePlace.norm_def, hv]
    simp
  have hNorm : heckeFiniteIdeleNorm u = Inv.inv (N : Real) := by
    change finprod (fun p : P => norm (u.val p)) = _
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hS hSupp]
    simp_rw [(hn _).2]
    change Finset.prod T (fun p => Inv.inv ((p.asIdeal.absNorm : Real) ^ n p)) = _
    rw [Finset.prod_inv_distrib]
    congr 1
    simp [N, q]
  have hNorm' : (N : Real) = Inv.inv (heckeFiniteIdeleNorm u) := by rw [hNorm, inv_inv]
  refine Exists.intro N (And.intro hN (And.intro hNorm' (fun p => ?_)))
  let A := p.adicCompletion K
  let e : RingHom R A := algebraMap R A
  have hNle : V p (e (N : R)) <= V p (u.val p) := by
    by_cases hp : Membership.mem T p
    . have hMemPow : Membership.mem (p.asIdeal ^ n p) ((q p : Nat) : R) := by
        change Membership.mem (p.asIdeal ^ n p) (((p.asIdeal.absNorm ^ n p) : Nat) : R)
        rw [Nat.cast_pow]
        exact Ideal.pow_mem_pow p.asIdeal.absNorm_mem _
      choose j hj using (Finset.dvd_prod_of_mem q hp : Dvd.dvd (q p) N)
      have hjR : (N : R) = (q p : R) * (j : R) := by
        calc
          (N : R) = ((q p * j : Nat) : R) := congrArg (fun z : Nat => (z : R)) hj
          _ = _ := Nat.cast_mul _ _
      have hMem : Membership.mem (p.asIdeal ^ n p) (N : R) := by
        rw [hjR]
        exact Ideal.mul_mem_right _ _ hMemPow
      have hVal : V p (e (N : R)) = p.intValuation (N : R) :=
        (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) (v := p) (N : R)).trans
          (HeightOneSpectrum.valuation_of_algebraMap (K := K) p (N : R))
      rw [hVal, (hn p).1]
      exact (p.intValuation_le_pow_iff_mem (N : R) (n p)).mpr hMem
    . have hp' : Not (Membership.mem (Function.mulSupport f) p) := by
        intro h
        exact hp (Set.Finite.mem_toFinset hSupp |>.mpr h)
      have hV : V p (u.val p) = 1 := not_not.mp hp'
      rw [hV]
      exact HeightOneSpectrum.coe_algebraMap_mem R K p (N : R)
  have hOne : u.val p * u.inv p = (1 : A) :=
    congrArg (fun a : FiniteAdeleRing R K => a p) u.val_inv
  change V p (e (N : R) * u.inv p) <= 1
  rw [map_mul]
  calc
    _ <= V p (u.val p) * V p (u.inv p) := mul_le_mul_left hNle _
    _ = _ := by rw [<- map_mul, hOne, map_one]

/-- The reciprocal finite determinant norm of an integral matrix gives
an integer that clears every entry of its inverse. -/
theorem exists_finiteAdeleMatrixDenominatorSet_of_integral
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (g : Matrix.GeneralLinearGroup (Fin n) (FiniteAdeleRing (RingOfIntegers K) K))
    (hg : Membership.mem (integralFiniteAdeleSubring K).matrix g.val) :
    Exists (fun N : Nat => And (0 < N)
      (And ((N : Real) = Inv.inv (heckeFiniteIdeleNorm (Matrix.GeneralLinearGroup.det g)))
        (Membership.mem (finiteAdeleMatrixDenominatorSet K n N) g))) := by
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let R := integralFiniteAdeleSubring K
  let u := Matrix.GeneralLinearGroup.det g
  let M : Matrix (Fin n) (Fin n) R := Matrix.of (fun i j => Subtype.mk (g.val i j) (hg i j))
  have hMap : R.subtype.mapMatrix M = g.val := by ext i j; rfl
  have hDet : Membership.mem R u.val := by
    change Membership.mem R g.val.det
    rw [<- hMap, <- RingHom.map_det]
    exact M.det.property
  have hAdj : Membership.mem R.matrix g.val.adjugate := by
    rw [<- hMap, <- RingHom.map_adjugate]
    intro i j
    exact (M.adjugate i j).property
  choose N hN using exists_finiteIdele_inverseDenominator_of_integral u hDet
  have hNU : Membership.mem R ((N : F) * u.inv) := by
    intro p
    let e : RingHom F (p.adicCompletion K) :=
      RestrictedProduct.evalRingHom (fun q : HeightOneSpectrum (RingOfIntegers K) => q.adicCompletion K) p
    change Membership.mem (p.adicCompletionIntegers K) (e ((N : F) * u.inv))
    rw [map_mul, map_natCast, show e u.inv = u.inv p from rfl]
    simpa only [map_natCast] using hN.2.2 p
  have hAdjEq : g.val.adjugate = HSMul.hSMul u.val g.inv := by
    calc
      _ = g.inv * (g.val * g.val.adjugate) := by rw [<- mul_assoc, g.inv_val, one_mul]
      _ = _ := by
        rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one]
        rfl
  have hInv : HSMul.hSMul (N : F) g.inv =
      HSMul.hSMul ((N : F) * u.inv) g.val.adjugate := by
    rw [hAdjEq, smul_smul, mul_assoc, u.inv_val, mul_one]
  refine Exists.intro N (And.intro hN.1 (And.intro hN.2.1 (And.intro hg ?_)))
  rw [hInv]
  intro i j
  exact R.mul_mem hNU (hAdj i j)

end Robin1984.GRH
