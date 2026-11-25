import Robin1984.GRH.GodementJacquetSubgroupAveraging
import Robin1984.GRH.ValuationPrincipalCongruenceFactorization

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Cayley-Hamilton and the rational generating series of a linear recurrence.
- Formalization note: Proves multiplicativity of compression on ordered diagonal units and an affine-ray generating series with a denominator fixed by the direction operator.
- PROVENANCE-END
-/

/-!
# Generating series of ordered diagonal matrix coefficients

On the principal congruence-fixed range, the two-element double-coset
identity makes the compressed diagonal action multiplicative. The
reversed characteristic polynomial of one direction then gives a
common denominator for its translates in the ordered diagonal monoid.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

/-- The diagonal units whose valuations are ordered form a multiplicative
monoid. -/
def valuationOrderedDiagonalSubmonoid
    {F W : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    (vf : Valuation F W) (rank : Nat) : Submonoid (Units (Fin rank -> F)) where
  carrier := {a | forall i j, i <= j -> vf (a.val i) <= vf (a.val j)}
  one_mem' := by
    intro i j _
    change vf (1 : F) <= vf (1 : F)
    exact le_rfl
  mul_mem' := by
    intro a b ha hb i j hij
    change vf (a.val i * b.val i) <= vf (a.val j * b.val j)
    rw [vf.map_mul, vf.map_mul]
    exact mul_le_mul' (ha i j hij) (hb i j hij)

/-- Compressing the action to the congruence-fixed range gives a monoid
homomorphism on ordered diagonal units. -/
def HeckeLocalSubgroupAverage.orderedDiagonalOperators
    {F W V : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    [AddCommGroup V] [Module Complex V]
    (vf : Valuation F W) (rank : Nat) (r : W) (hr : r < 1)
    (rho : MonoidHom (Units (Matrix (Fin rank) (Fin rank) F)) (Module.End Complex V))
    (P : HeckeLocalSubgroupAverage rho (valuationPrincipalCongruenceSubgroup vf rank r)) :
    MonoidHom (valuationOrderedDiagonalSubmonoid vf rank)
      (Module.End Complex (LinearMap.range P.proj)) where
  toFun a := P.operator ((valuationDiagonalSection F rank a.val).val)
  map_one' := by
    change P.operator ((valuationDiagonalSection F rank 1).val) = 1
    rw [map_one]
    change P.operator (1 : Units (Matrix (Fin rank) (Fin rank) F)) = 1
    have h := P.operator_pow 1 (fun m k =>
      Exists.intro k (Exists.intro 1 (by simp))) 0
    simpa only [pow_zero] using h.symm
  map_mul' a b := by
    change P.operator ((valuationDiagonalSection F rank (a.val * b.val)).val) =
      P.operator ((valuationDiagonalSection F rank a.val).val) *
        P.operator ((valuationDiagonalSection F rank b.val).val)
    rw [map_mul]
    exact (P.operator_mul ((valuationDiagonalSection F rank a.val).val)
      ((valuationDiagonalSection F rank b.val).val)
      (exists_valuationPrincipalCongruence_doubleCoset_factor_of_ordered
        vf rank r hr a.val b.val a.property b.property)).symm

private theorem exists_polynomial_relation_of_monic_recurrence
    (a c : Nat -> Complex) (d : Nat) (hc : c d = 1)
    (hRec : forall n : Nat, (Finset.range (d + 1)).sum (fun j => c j * a (n + j)) = 0) :
    let denominator : Polynomial Complex :=
      (Finset.range (d + 1)).sum (fun j => Polynomial.C (c j) * Polynomial.X ^ (d - j))
    exists numerator : Polynomial Complex,
      And (denominator.eval 0 = 1)
        (forall z : Complex, Summable (fun n : Nat => a n * z ^ n) ->
          denominator.eval z * (tsum (fun n : Nat => a n * z ^ n)) = numerator.eval z) := by
  intro q
  let qterm (j : Nat) : Polynomial Complex := Polynomial.C (c j) * Polynomial.X ^ (d - j)
  let initial (j : Nat) : Polynomial Complex :=
    (Finset.range j).sum (fun n => Polynomial.C (a n) * Polynomial.X ^ n)
  let p : Polynomial Complex := (Finset.range (d + 1)).sum (fun j => qterm j * initial j)
  have hq (z : Complex) :
      q.eval z = (Finset.range (d + 1)).sum (fun j => c j * z ^ (d - j)) := by
    change Polynomial.evalRingHom z ((Finset.range (d + 1)).sum qterm) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have hInitial (z : Complex) (j : Nat) :
      Polynomial.evalRingHom z (initial j) = (Finset.range j).sum (fun n => a n * z ^ n) := by
    change Polynomial.evalRingHom z
      ((Finset.range j).sum (fun n => Polynomial.C (a n) * Polynomial.X ^ n)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp
  have hp (z : Complex) :
      p.eval z = (Finset.range (d + 1)).sum
        (fun j => (c j * z ^ (d - j)) * (Finset.range j).sum (fun n => a n * z ^ n)) := by
    change Polynomial.evalRingHom z ((Finset.range (d + 1)).sum (fun j => qterm j * initial j)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, hInitial z j]
    simp [qterm]
  refine Exists.intro p (And.intro ?_ ?_)
  next =>
    rw [hq, Finset.sum_eq_single d]
    next => simp [hc]
    next =>
      intro j hj hne
      have hjd : j <= d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hsub : Not (d - j = 0) := Nat.ne_of_gt (Nat.sub_pos_of_lt (lt_of_le_of_ne hjd hne))
      rw [zero_pow hsub, mul_zero]
    next =>
      intro h
      exact False.elim (h (Finset.mem_range.mpr (Nat.lt_succ_self d)))
  next =>
    intro z hz
    have hTail (j : Nat) : Summable (fun n : Nat => a (n + j) * z ^ (n + j)) :=
      (summable_nat_add_iff j).mpr hz
    have hRecWeighted (n : Nat) :
        (Finset.range (d + 1)).sum
          (fun j => (c j * z ^ (d - j)) * (a (n + j) * z ^ (n + j))) = 0 := by
      calc
        _ = (Finset.range (d + 1)).sum (fun j => z ^ (n + d) * (c j * a (n + j))) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjd : j <= d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hExp : d - j + (n + j) = n + d := by omega
          calc
            _ = (z ^ (d - j) * z ^ (n + j)) * (c j * a (n + j)) := by ac_rfl
            _ = _ := by rw [<- pow_add, hExp]
        _ = 0 := by rw [<- Finset.mul_sum, hRec n, mul_zero]
    have hCancel : (Finset.range (d + 1)).sum
        (fun j => (c j * z ^ (d - j)) * tsum (fun n : Nat => a (n + j) * z ^ (n + j))) = 0 := by
      have hSummable (j : Nat) (_ : Membership.mem (Finset.range (d + 1)) j) :
          Summable (fun n : Nat => (c j * z ^ (d - j)) * (a (n + j) * z ^ (n + j))) :=
        (hTail j).mul_left _
      have hWeightedZero : (fun n : Nat => (Finset.range (d + 1)).sum
          (fun j => (c j * z ^ (d - j)) * (a (n + j) * z ^ (n + j)))) = fun _ => 0 :=
        funext hRecWeighted
      calc
        _ = tsum (fun n : Nat => (Finset.range (d + 1)).sum
            (fun j => (c j * z ^ (d - j)) * (a (n + j) * z ^ (n + j)))) := by
          rw [Summable.tsum_finsetSum hSummable]
          apply Finset.sum_congr rfl
          intro j _
          exact ((hTail j).tsum_mul_left (c j * z ^ (d - j))).symm
        _ = 0 := by rw [hWeightedZero, tsum_zero]
    rw [hq, hp, Finset.sum_mul]
    calc
      _ = (Finset.range (d + 1)).sum (fun j => (c j * z ^ (d - j)) *
          ((Finset.range j).sum (fun n => a n * z ^ n) +
            tsum (fun n : Nat => a (n + j) * z ^ (n + j)))) := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun x => (c j * z ^ (d - j)) * x) (hz.sum_add_tsum_nat_add j).symm
      _ = _ := by simp only [mul_add, Finset.sum_add_distrib, hCancel, add_zero]

/-- Every affine ray in the ordered diagonal monoid has a rational
matrix-coefficient series. Its denominator is the reversed characteristic
polynomial of the direction operator and is independent of the base
diagonal element and both coefficient vectors. -/
theorem valuationPrincipalCongruence_affineDiagonalRay_series
    {F W V : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    [AddCommGroup V] [Module Complex V]
    (vf : Valuation F W) (rank : Nat) (r : W) (hr : r < 1)
    (rho : MonoidHom (Units (Matrix (Fin rank) (Fin rank) F)) (Module.End Complex V))
    (P : HeckeLocalSubgroupAverage rho (valuationPrincipalCongruenceSubgroup vf rank r))
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (a : valuationOrderedDiagonalSubmonoid vf rank) :
    let op := P.orderedDiagonalOperators vf rank r hr rho
    let d := Module.finrank Complex (LinearMap.range P.proj)
    let q := (op a).charpoly
    let denominator : Polynomial Complex :=
      (Finset.range (d + 1)).sum (fun j => Polynomial.C (q.coeff j) * Polynomial.X ^ (d - j))
    forall (b : valuationOrderedDiagonalSubmonoid vf rank)
      (ell : LinearMap (RingHom.id Complex) V Complex),
      (forall (k : valuationPrincipalCongruenceSubgroup vf rank r) (w : V),
        ell (rho k.val w) = ell w) ->
      forall (w : V),
      (forall k : valuationPrincipalCongruenceSubgroup vf rank r, rho k.val w = w) ->
      let aseq (m : Nat) := ell (rho ((valuationDiagonalSection F rank (b * a ^ m).val).val) w)
      exists numerator : Polynomial Complex,
        And (denominator.eval 0 = 1)
          (forall z : Complex, Summable (fun m : Nat => aseq m * z ^ m) ->
            denominator.eval z * (tsum (fun m : Nat => aseq m * z ^ m)) = numerator.eval z) := by
  intro op d q denominator b ell hEll w hW aseq
  have hDeg : q.natDegree = d := LinearMap.charpoly_natDegree (op a)
  have hLead : q.coeff d = 1 := by
    rw [<- hDeg]
    exact LinearMap.charpoly_monic (op a)
  let lifted : LinearMap.range P.proj :=
    Subtype.mk w (Exists.intro w (P.proj_eq_of_fixed w hW))
  let ellW := (ell.comp (LinearMap.range P.proj).subtype).comp (op b)
  have hZeroOp :
      (Finset.range (d + 1)).sum (fun j => HSMul.hSMul (q.coeff j) ((op a) ^ j)) = 0 := by
    rw [<- hDeg, <- Polynomial.aeval_eq_sum_range (p := q) (op a)]
    exact LinearMap.aeval_self_charpoly (op a)
  have hRec (m : Nat) :
      (Finset.range (d + 1)).sum (fun j => q.coeff j * aseq (m + j)) = 0 := by
    have h := congrArg (fun T : Module.End Complex (LinearMap.range P.proj) =>
      ellW (T (((op a) ^ m) lifted))) hZeroOp
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, map_sum,
      map_smul, smul_eq_mul, map_zero] at h
    have hTerm (j : Nat) : ellW (((op a) ^ j) (((op a) ^ m) lifted)) = aseq (m + j) := by
      change (ell.comp (LinearMap.range P.proj).subtype)
        (op b ((((op a) ^ j) * ((op a) ^ m)) lifted)) = _
      rw [<- pow_add, Nat.add_comm j m, <- map_pow, <- Module.End.mul_apply, <- map_mul]
      exact P.pairing_proj ell hEll _
    simpa only [hTerm] using h
  exact exists_polynomial_relation_of_monic_recurrence aseq q.coeff d hLead hRec

end Robin1984.GRH
