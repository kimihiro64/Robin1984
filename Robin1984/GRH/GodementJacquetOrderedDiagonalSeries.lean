import Robin1984.GRH.GodementJacquetSubgroupAveraging
import Robin1984.GRH.ValuationPrincipalCongruenceFactorization

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Cayley-Hamilton and the rational generating series of a linear recurrence.
- Formalization note: Proves multiplicativity of compression on ordered diagonal units and gives common denominators for affine rays and finitely generated weighted cones.
- PROVENANCE-END
-/

/-!
# Generating series of ordered diagonal matrix coefficients

On the principal congruence-fixed range, the two-element double-coset
identity makes the compressed diagonal action multiplicative. The
reversed characteristic polynomial gives a common denominator for
each direction. Their weight-dilated product controls the sum over a
finite family of directions.
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

private theorem mul_tsum_reversed_recurrence
    (a c : Nat -> Complex) (d : Nat)
    (hRec : forall n : Nat, (Finset.range (d + 1)).sum (fun j => c j * a (n + j)) = 0)
    (z : Complex) (hz : Summable (fun n : Nat => a n * z ^ n)) :
    ((Finset.range (d + 1)).sum (fun j => c j * z ^ (d - j))) *
        tsum (fun n : Nat => a n * z ^ n) =
      (Finset.range (d + 1)).sum
        (fun j => (c j * z ^ (d - j)) * (Finset.range j).sum (fun n => a n * z ^ n)) := by
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
  rw [Finset.sum_mul]
  calc
    _ = (Finset.range (d + 1)).sum (fun j => (c j * z ^ (d - j)) *
        ((Finset.range j).sum (fun n => a n * z ^ n) +
          tsum (fun n : Nat => a (n + j) * z ^ (n + j)))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun x => (c j * z ^ (d - j)) * x) (hz.sum_add_tsum_nat_add j).symm
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, hCancel, add_zero]

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
    rw [hq, hp]
    exact mul_tsum_reversed_recurrence a c d hRec z hz

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

private def weightedConeExponent {n : Nat} (w e : Fin n -> Nat) : Nat :=
  Finset.univ.sum (fun i => w i * e i)

private def weightedRecurrencePolynomial (w d : Nat) (c : Nat -> Complex) :
    Polynomial Complex :=
  (Finset.range (d + 1)).sum (fun j => Polynomial.C (c j) * Polynomial.X ^ (w * (d - j)))

private theorem eval_weightedRecurrencePolynomial (w d : Nat) (c : Nat -> Complex)
    (z : Complex) :
    (weightedRecurrencePolynomial w d c).eval z =
      (Finset.range (d + 1)).sum (fun j => c j * (z ^ w) ^ (d - j)) := by
  change Polynomial.evalRingHom z ((Finset.range (d + 1)).sum
    (fun j => Polynomial.C (c j) * Polynomial.X ^ (w * (d - j)))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [pow_mul]

private def weightedConeNumerator :
    (n : Nat) -> (Fin n -> Nat) -> (Fin n -> Nat) ->
      (Fin n -> Nat -> Complex) -> ((Fin n -> Nat) -> Complex) -> Polynomial Complex
  | 0, _, _, _, f => Polynomial.C (f (fun i => Fin.elim0 i))
  | n + 1, w, d, c, f =>
    (Finset.range (d 0 + 1)).sum (fun j =>
      (Polynomial.C (c 0 j) * Polynomial.X ^ (w 0 * (d 0 - j))) *
        (Finset.range j).sum (fun m =>
          weightedConeNumerator n (fun i => w i.succ) (fun i => d i.succ)
            (fun i => c i.succ) (fun t => f (Fin.cons m t)) *
          Polynomial.X ^ (w 0 * m)))

private theorem update_finCons_zero {n : Nat} (m j : Nat) (t : Fin n -> Nat) :
    Function.update (Fin.cons m t : Fin (n + 1) -> Nat) 0 j = Fin.cons j t := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  next => simp
  next => simp

private theorem update_finCons_succ {n : Nat} (m j : Nat) (t : Fin n -> Nat) (i : Fin n) :
    Function.update (Fin.cons m t : Fin (n + 1) -> Nat) i.succ j =
      Fin.cons m (Function.update t i j) := by
  funext a
  refine Fin.cases ?_ (fun a => ?_) a
  next => simp [Function.update_of_ne (Fin.succ_ne_zero i).symm]
  next =>
    by_cases h : a = i
    next => subst a; simp
    next =>
      have h' : Not (a.succ = i.succ) := fun he => h (Fin.succ_inj.mp he)
      simp [Function.update_of_ne h', Function.update_of_ne h]

private theorem weightedConeSummable_at_zero
    (n : Nat) (w : Fin n -> Nat) (hW : forall i, 0 < w i) (f : (Fin n -> Nat) -> Complex) :
    Summable (fun t => f t * (0 : Complex) ^ weightedConeExponent w t) := by
  classical
  let o : Fin n -> Nat := fun _ => 0
  apply summable_of_ne_finset_zero (s := {o})
  intro t ht
  have hne : Not (t = o) := fun h => ht (Finset.mem_singleton.mpr h)
  choose i hi using Function.ne_iff.mp hne
  have hi0 : Not (t i = 0) := hi
  have hPos : 0 < weightedConeExponent w t :=
    (Nat.mul_pos (hW i) (Nat.pos_of_ne_zero hi0)).trans_le
      (Finset.single_le_sum (fun j _ => Nat.zero_le (w j * t j)) (Finset.mem_univ i))
  rw [zero_pow hPos.ne', mul_zero]

/-- Independent recurrences in the coordinates of an exponent cone
give a product denominator for its weighted sum. The numerator is obtained
by retaining only the finite initial segments in each coordinate. -/
private theorem weightedCone_tsum_polynomial
    (n : Nat) (w d : Fin n -> Nat) (c : Fin n -> Nat -> Complex)
    (f : (Fin n -> Nat) -> Complex) (hW : forall i, 0 < w i)
    (hRec : forall (i : Fin n) (t : Fin n -> Nat),
      (Finset.range (d i + 1)).sum (fun j => c i j * f (Function.update t i (t i + j))) = 0) :
    forall z : Complex, Summable (fun t => f t * z ^ weightedConeExponent w t) ->
      (Finset.univ.prod (fun i => weightedRecurrencePolynomial (w i) (d i) (c i))).eval z *
        tsum (fun t => f t * z ^ weightedConeExponent w t) =
          (weightedConeNumerator n w d c f).eval z := by
  induction n with
  | zero =>
    intro z _
    let _ : Unique (Fin 0 -> Nat) :=
      { default := fun i => Fin.elim0 i, uniq := fun _ => funext (fun i => Fin.elim0 i) }
    let _ : Fintype (Fin 0 -> Nat) := Fintype.ofFinite _
    simp [weightedConeExponent, weightedConeNumerator, tsum_fintype]
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    intro z hz
    let wt : Fin n -> Nat := fun i => w i.succ
    let dt : Fin n -> Nat := fun i => d i.succ
    let ct : Fin n -> Nat -> Complex := fun i => c i.succ
    let row (m : Nat) (t : Fin n -> Nat) := f (Fin.cons m t)
    let B (m : Nat) (t : Fin n -> Nat) := row m t * z ^ weightedConeExponent wt t
    let Z := z ^ w 0
    let T (p : Prod (Fin n -> Nat) Nat) := B p.2 p.1 * Z ^ p.2
    let ix : Equiv (Prod (Fin n -> Nat) Nat) (Fin (n + 1) -> Nat) :=
      (Equiv.prodComm (Fin n -> Nat) Nat).trans (Fin.consEquiv (fun _ => Nat))
    have hTerm (p : Prod (Fin n -> Nat) Nat) :
        f (ix p) * z ^ weightedConeExponent w (ix p) = T p := by
      change f (Fin.cons p.2 p.1) *
        z ^ Finset.univ.sum (fun i => w i * (Fin.cons p.2 p.1 : Fin (n + 1) -> Nat) i) = _
      rw [Fin.sum_univ_succ, Fin.cons_zero, pow_add, pow_mul]
      simp only [Fin.cons_succ, T, B, row, Z, weightedConeExponent, wt]
      ac_rfl
    have hProd : Summable T := ((ix.summable_iff).mpr hz).congr hTerm
    have hTsum : tsum (fun t => f t * z ^ weightedConeExponent w t) =
        tsum (fun t : Fin n -> Nat => tsum (fun m : Nat => T (t,m))) := by
      rw [<- hProd.tsum_prod]
      exact (ix.tsum_eq (fun t => f t * z ^ weightedConeExponent w t)).symm.trans (tsum_congr hTerm)
    have hB (m : Nat) : Summable (B m) := by
      by_cases hz0 : z = 0
      next =>
        subst z
        exact weightedConeSummable_at_zero n wt (fun i => hW i.succ) (row m)
      next =>
        have hZ : Not (Z ^ m = 0) := pow_ne_zero _ (pow_ne_zero _ hz0)
        refine (((hProd.prod_symm.prod_factor m).mul_right (Inv.inv (Z ^ m))).congr ?_)
        intro t
        change (B m t * Z ^ m) * Inv.inv (Z ^ m) = B m t
        rw [mul_assoc]
        simp [hZ]
    have hRowRec (m : Nat) (i : Fin n) (t : Fin n -> Nat) :
        (Finset.range (dt i + 1)).sum (fun j => ct i j *
          row m (Function.update t i (t i + j))) = 0 := by
      simpa only [dt, ct, row, Fin.cons_succ, update_finCons_succ] using
        hRec i.succ (Fin.cons m t)
    let term (j : Nat) := c 0 j * Z ^ (d 0 - j)
    let headDen := (Finset.range (d 0 + 1)).sum term
    have hFirst (t : Fin n -> Nat) :
        headDen * tsum (fun m : Nat => T (t,m)) =
          (Finset.range (d 0 + 1)).sum (fun j => term j *
            (Finset.range j).sum (fun m => B m t * Z ^ m)) := by
      have hRecHead (m : Nat) :
          (Finset.range (d 0 + 1)).sum (fun j => c 0 j * B (m + j) t) = 0 := by
        have h := hRec 0 (Fin.cons m t)
        simp only [Fin.cons_zero, update_finCons_zero] at h
        simp only [B, row, <- mul_assoc, <- Finset.sum_mul, h, zero_mul]
      exact mul_tsum_reversed_recurrence (fun m => B m t) (c 0) (d 0) hRecHead Z
        (hProd.prod_factor t)
    have hHeadSum : headDen * tsum (fun t => f t * z ^ weightedConeExponent w t) =
        (Finset.range (d 0 + 1)).sum (fun j => term j *
          (Finset.range j).sum (fun m => tsum (B m) * Z ^ m)) := by
      have hFinite (j : Nat) : Summable (fun t : Fin n -> Nat =>
          (Finset.range j).sum (fun m => B m t * Z ^ m)) :=
        summable_sum (fun m _ => (hB m).mul_right _)
      rw [hTsum, <- (hProd.prod.tsum_mul_left headDen)]
      rw [tsum_congr hFirst]
      rw [Summable.tsum_finsetSum (fun j _ => (hFinite j).mul_left (term j))]
      apply Finset.sum_congr rfl
      intro j _
      rw [(hFinite j).tsum_mul_left, Summable.tsum_finsetSum (fun m _ => (hB m).mul_right _)]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      exact (hB m).tsum_mul_right _
    let Q := Finset.univ.prod (fun i => weightedRecurrencePolynomial (wt i) (dt i) (ct i))
    have hEvalD : (Finset.univ.prod (fun i =>
        weightedRecurrencePolynomial (w i) (d i) (c i))).eval z = headDen * Q.eval z := by
      rw [Fin.prod_univ_succ, Polynomial.eval_mul, eval_weightedRecurrencePolynomial]
    have hSmall (m : Nat) : Q.eval z * tsum (B m) =
        (weightedConeNumerator n wt dt ct (row m)).eval z :=
      ih wt dt ct (row m) (fun i => hW i.succ) (hRowRec m) z (hB m)
    have hEvalN : (weightedConeNumerator (n + 1) w d c f).eval z =
        (Finset.range (d 0 + 1)).sum (fun j => term j *
          (Finset.range j).sum (fun m =>
            (weightedConeNumerator n wt dt ct (row m)).eval z * Z ^ m)) := by
      rw [weightedConeNumerator]
      change Polynomial.evalRingHom z ((Finset.range (d 0 + 1)).sum _) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul, map_sum]
      have hTermEval : Polynomial.evalRingHom z
          (Polynomial.C (c 0 j) * Polynomial.X ^ (w 0 * (d 0 - j))) = term j := by
        simp [term, Z, pow_mul]
      rw [hTermEval]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      rw [map_mul]
      have hPower : Polynomial.evalRingHom z (Polynomial.X ^ (w 0 * m)) = Z ^ m := by
        simp [Z, pow_mul]
      rw [hPower]
      rfl
    rw [hEvalD, mul_comm headDen (Q.eval z), mul_assoc, hHeadSum, hEvalN, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    rw [<- mul_assoc, hSmall]


private theorem coordinateRecurrence_mul_powers
    (n : Nat) (d : Fin n -> Nat) (c : Fin n -> Nat -> Complex)
    (alpha : Fin n -> Complex) (f : (Fin n -> Nat) -> Complex)
    (hRec : forall (i : Fin n) (t : Fin n -> Nat),
      (Finset.range (d i + 1)).sum (fun j => c i j * f (Function.update t i (t i + j))) = 0) :
    let C (i : Fin n) (j : Nat) := c i j * alpha i ^ (d i - j)
    let F (t : Fin n -> Nat) := f t * Finset.univ.prod (fun i => alpha i ^ t i)
    forall (i : Fin n) (t : Fin n -> Nat),
      (Finset.range (d i + 1)).sum (fun j => C i j * F (Function.update t i (t i + j))) = 0 := by
  intro C F i t
  let rest := (Finset.univ.erase i).prod (fun k => alpha k ^ t k)
  have hProduct (j : Nat) :
      Finset.univ.prod (fun k => alpha k ^ Function.update t i (t i + j) k) =
        rest * alpha i ^ (t i + j) := by
    rw [<- Finset.prod_erase_mul Finset.univ
      (fun k => alpha k ^ Function.update t i (t i + j) k) (Finset.mem_univ i),
      Function.update_self]
    congr 1
    exact Finset.prod_congr rfl (fun k hk => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])
  have hTerm (j : Nat) (hj : Membership.mem (Finset.range (d i + 1)) j) :
      C i j * F (Function.update t i (t i + j)) =
        (rest * alpha i ^ (t i + d i)) * (c i j * f (Function.update t i (t i + j))) := by
    have hjd : j <= d i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hPower : d i - j + (t i + j) = t i + d i := by
      calc
        _ = t i + (d i - j + j) := by ac_rfl
        _ = _ := by rw [Nat.sub_add_cancel hjd]
    change (c i j * alpha i ^ (d i - j)) *
      (f (Function.update t i (t i + j)) *
        Finset.univ.prod (fun k => alpha k ^ Function.update t i (t i + j) k)) = _
    rw [hProduct j]
    calc
      _ = (rest * (alpha i ^ (d i - j) * alpha i ^ (t i + j))) *
          (c i j * f (Function.update t i (t i + j))) := by ac_rfl
      _ = _ := by rw [<- pow_add, hPower]
  rw [Finset.sum_congr rfl hTerm, <- Finset.mul_sum, hRec i t, mul_zero]

/-- A single exponential majorant controls a coefficient array that satisfies a monic recurrence in each coordinate. -/
private theorem coordinateRecurrence_exponential_bound
    (n : Nat) (d : Fin n -> Nat) (c : Fin n -> Nat -> Complex)
    (f : (Fin n -> Nat) -> Complex) (M : Real) (hM : 1 <= M)
    (hLead : forall i, c i (d i) = 1)
    (hCoeff : forall i, (Finset.range (d i)).sum (fun j => norm (c i j)) <= M)
    (hRec : forall (i : Fin n) (t : Fin n -> Nat),
      (Finset.range (d i + 1)).sum (fun j => c i j * f (Function.update t i (t i + j))) = 0) :
    exists C : Real, And (0 <= C)
      (forall e : Fin n -> Nat, norm (f e) <= C * M ^ Finset.univ.sum e) := by
  classical
  let B := {e : Fin n -> Nat // forall i, e i < d i}
  let inj (e : B) (i : Fin n) : Fin (d i) := Fin.mk (e.val i) (e.property i)
  have hInj : Function.Injective inj := by
    intro a b h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  let _ : Finite B := Finite.of_injective inj hInj
  let _ : Fintype B := Fintype.ofFinite B
  let C := Finset.univ.sum (fun e : B => norm (f e.val))
  have hC : 0 <= C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM0 : 0 <= M := zero_le_one.trans hM
  have hPow : Monotone (fun k : Nat => M ^ k) := by
    apply monotone_nat_of_le_succ
    intro k
    rw [pow_succ]
    calc
      M ^ k = M ^ k * 1 := (mul_one _).symm
      _ <= M ^ k * M := mul_le_mul_of_nonneg_left hM (pow_nonneg hM0 _)
  let total (e : Fin n -> Nat) := Finset.univ.sum e
  have hBound : forall N : Nat, forall e : Fin n -> Nat, total e = N -> norm (f e) <= C * M ^ N := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro e hN
      by_cases he : forall i, e i < d i
      . have hBase := Finset.single_le_sum (f := fun a : B => norm (f a.val))
          (fun a _ => norm_nonneg _) (Finset.mem_univ (Subtype.mk e he : B))
        exact hBase.trans (by
          calc
            C = C * M ^ 0 := by rw [pow_zero, mul_one]
            _ <= C * M ^ N := mul_le_mul_of_nonneg_left (hPow (Nat.zero_le N)) hC)
      . have hex : exists i, d i <= e i := by
          by_contra hn
          apply he
          intro i
          exact lt_of_not_ge (fun h => hn (Exists.intro i h))
        choose i hi using hex
        let t := Function.update e i (e i - d i)
        let r (j : Nat) := Function.update e i (e i - d i + j)
        have hUpd (j : Nat) : Function.update t i (t i + j) = r j := by
          funext k
          by_cases hk : k = i
          . subst k
            simp only [t, r, Function.update_self]
          . simp only [t, r, Function.update_of_ne hk]
        have hTop : r (d i) = e := by
          funext k
          by_cases hk : k = i
          . subst k
            simp only [r, Function.update_self, Nat.sub_add_cancel hi]
          . simp only [r, Function.update_of_ne hk]
        have hRel := hRec i t
        simp only [hUpd] at hRel
        rw [Finset.sum_range_succ, hLead i, one_mul, hTop] at hRel
        by_cases hd : d i = 0
        . rw [hd, Finset.range_zero, Finset.sum_empty, zero_add] at hRel
          rw [hRel, norm_zero]
          exact mul_nonneg hC (pow_nonneg hM0 _)
        . have hZero : f e = -((Finset.range (d i)).sum (fun j => c i j * f (r j))) :=
            eq_neg_of_add_eq_zero_left ((add_comm _ _).trans hRel)
          have hNpos : 0 < N := by
            have hE : e i <= total e :=
              Finset.single_le_sum (f := e) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
            exact (Nat.pos_of_ne_zero hd).trans_le (hi.trans (hE.trans_eq hN))
          have hR (j : Nat) (hj : Membership.mem (Finset.range (d i)) j) :
              total (r j) < N := by
            have hh : e i - d i + j < e i :=
              (Nat.add_lt_add_left (Finset.mem_range.mp hj) _).trans_eq (Nat.sub_add_cancel hi)
            have hSplit : total (r j) =
                (Finset.univ.erase i).sum e + (e i - d i + j) := by
              change Finset.univ.sum (r j) = _
              rw [<- Finset.sum_erase_add Finset.univ (r j) (Finset.mem_univ i)]
              simp only [r, Function.update_self]
              congr 1
              exact Finset.sum_congr rfl (fun k hk => Function.update_of_ne (Finset.ne_of_mem_erase hk) _ _)
            rw [hSplit, <- hN]
            change (Finset.univ.erase i).sum e + (e i - d i + j) < Finset.univ.sum e
            rw [<- Finset.sum_erase_add Finset.univ e (Finset.mem_univ i)]
            exact Nat.add_lt_add_left hh _
          have hAll (j : Nat) (hj : Membership.mem (Finset.range (d i)) j) :
              norm (f (r j)) <= C * M ^ (N - 1) := by
            have hh := ih (total (r j)) (hR j hj) (r j) rfl
            have hjlt := hR j hj
            have hj' : total (r j) <= N - 1 := by omega
            exact hh.trans (mul_le_mul_of_nonneg_left (hPow hj') hC)
          calc
            norm (f e) <= (Finset.range (d i)).sum (fun j => norm (c i j) * norm (f (r j))) := by
              rw [hZero, norm_neg]
              simpa only [norm_mul] using norm_sum_le (Finset.range (d i)) (fun j => c i j * f (r j))
            _ <= (Finset.range (d i)).sum (fun j => norm (c i j) * (C * M ^ (N - 1))) :=
              Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hAll j hj) (norm_nonneg _))
            _ <= M * (C * M ^ (N - 1)) := by
              rw [<- Finset.sum_mul]
              exact mul_le_mul_of_nonneg_right (hCoeff i) (mul_nonneg hC (pow_nonneg hM0 _))
            _ = C * M ^ N := by
              calc
                _ = C * (M ^ (N - 1) * M) := by ac_rfl
                _ = _ := by rw [<- pow_succ, Nat.sub_add_cancel hNpos]
  exact Exists.intro C (And.intro hC (fun e => hBound (total e) e rfl))

private theorem summable_geometric_gap_cone (n : Nat) (q : Real) (hq0 : 0 <= q) (hq1 : q < 1) :
    Summable (fun t : Fin n -> Nat => q ^ Finset.univ.sum t) := by
  induction n with
  | zero =>
    let _ : Unique (Fin 0 -> Nat) :=
      { default := fun i => Fin.elim0 i, uniq := fun _ => funext (fun i => Fin.elim0 i) }
    exact Summable.of_finite
  | succ n ih =>
    let T (p : Prod (Fin n -> Nat) Nat) := q ^ Finset.univ.sum p.1 * q ^ p.2
    let ix : Equiv (Prod (Fin n -> Nat) Nat) (Fin (n + 1) -> Nat) :=
      (Equiv.prodComm (Fin n -> Nat) Nat).trans (Fin.consEquiv (fun _ => Nat))
    have hTerm (p : Prod (Fin n -> Nat) Nat) :
        q ^ Finset.univ.sum (ix p) = T p := by
      change q ^ Finset.univ.sum (Fin.cons p.2 p.1 : Fin (n + 1) -> Nat) =
        q ^ Finset.univ.sum p.1 * q ^ p.2
      rw [Fin.sum_univ_succ, Fin.cons_zero, pow_add, mul_comm]
      rfl
    have hGeom : Summable (fun m : Nat => q ^ m) := summable_geometric_of_lt_one hq0 hq1
    have hNonneg (p : Prod (Fin n -> Nat) Nat) : 0 <= T p :=
      mul_nonneg (pow_nonneg hq0 _) (pow_nonneg hq0 _)
    have hProd : Summable T := by
      apply (summable_prod_of_nonneg hNonneg).mpr
      constructor
      . intro t
        exact hGeom.mul_left (q ^ Finset.univ.sum t)
      . have hRow (t : Fin n -> Nat) : tsum (fun m : Nat => T (t, m)) =
            q ^ Finset.univ.sum t * tsum (fun m : Nat => q ^ m) := by
          change tsum (fun m : Nat => q ^ Finset.univ.sum t * q ^ m) = _
          exact hGeom.tsum_mul_left (q ^ Finset.univ.sum t)
        simpa only [hRow] using ih.mul_right (tsum (fun m : Nat => q ^ m))
    exact ix.summable_iff.mp (hProd.congr (fun p => (hTerm p).symm))

private theorem summable_weightedCone_of_coordinateRecurrence
    {n : Nat} (w d : Fin n -> Nat) (c : Fin n -> Nat -> Complex)
    (f : (Fin n -> Nat) -> Complex) (M : Real) (hM : 1 <= M)
    (hw : forall i, 1 <= w i) (hLead : forall i, c i (d i) = 1)
    (hCoeff : forall i, (Finset.range (d i)).sum (fun j => norm (c i j)) <= M)
    (hRec : forall (i : Fin n) (t : Fin n -> Nat),
      (Finset.range (d i + 1)).sum (fun j =>
        c i j * f (Function.update t i (t i + j))) = 0)
    {z : Complex} (hz : M * norm z < 1) :
    Summable (fun t => f t * z ^ (Finset.univ.sum (fun i => w i * t i))) := by
  obtain hc := coordinateRecurrence_exponential_bound n d c f M hM hLead hCoeff hRec
  choose C hC using hc
  have hM0 : 0 <= M := zero_le_one.trans hM
  have hZ : norm z <= 1 := by
    have h : 1 * norm z <= M * norm z := mul_le_mul_of_nonneg_right hM (norm_nonneg z)
    rw [one_mul] at h
    exact h.trans hz.le
  have hPower : Antitone (fun k : Nat => norm z ^ k) := by
    apply antitone_nat_of_succ_le
    intro k
    rw [pow_succ]
    calc
      norm z ^ k * norm z <= norm z ^ k * 1 :=
        mul_le_mul_of_nonneg_left hZ (pow_nonneg (norm_nonneg z) k)
      _ = norm z ^ k := mul_one _
  apply Summable.of_norm_bounded
    ((summable_geometric_gap_cone n (M * norm z)
      (mul_nonneg hM0 (norm_nonneg _)) hz).mul_left C)
  intro t
  have hE : Finset.univ.sum t <= (Finset.univ.sum (fun i => w i * t i)) := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [one_mul] using Nat.mul_le_mul_right (t i) (hw i)
  calc
    norm (f t * z ^ (Finset.univ.sum (fun i => w i * t i))) =
        norm (f t) * norm z ^ (Finset.univ.sum (fun i => w i * t i)) := by rw [norm_mul, norm_pow]
    _ <= (C * M ^ Finset.univ.sum t) * norm z ^ Finset.univ.sum t :=
      mul_le_mul (hC.2 t) (hPower hE)
        (pow_nonneg (norm_nonneg _) _) (mul_nonneg hC.1 (pow_nonneg hM0 _))
    _ = C * (M * norm z) ^ Finset.univ.sum t := by rw [mul_pow, mul_assoc]

private theorem weightedCone_tsum_polynomial_mul_powers_near_zero
    (n : Nat) (w d : Fin n -> Nat) (c : Fin n -> Nat -> Complex)
    (alpha : Fin n -> Complex) (f : (Fin n -> Nat) -> Complex)
    (hW : forall i, 0 < w i) (hLead : forall i, c i (d i) = 1)
    (hRec : forall (i : Fin n) (t : Fin n -> Nat),
      (Finset.range (d i + 1)).sum (fun j => c i j * f (Function.update t i (t i + j))) = 0) :
    let F (t : Fin n -> Nat) := f t * Finset.univ.prod (fun i => alpha i ^ t i)
    let denominator : Polynomial Complex := Finset.univ.prod (fun i =>
      (Finset.range (d i + 1)).sum (fun j =>
        Polynomial.C (c i j * alpha i ^ (d i - j)) * Polynomial.X ^ (w i * (d i - j))))
    exists M : Real, And (1 <= M)
      (exists numerator : Polynomial Complex,
        And (denominator.eval 0 = 1)
          (And (forall z : Complex, M * norm z < 1 ->
            Summable (fun t : Fin n -> Nat => F t * z ^ Finset.univ.sum (fun i => w i * t i)))
            (forall z : Complex,
          Summable (fun t => F t * z ^ Finset.univ.sum (fun i => w i * t i)) ->
          denominator.eval z * tsum (fun t => F t * z ^ Finset.univ.sum (fun i => w i * t i)) =
            numerator.eval z))) := by
  intro F denominator
  let C (i : Fin n) (j : Nat) := c i j * alpha i ^ (d i - j)
  have hC (i : Fin n) : C i (d i) = 1 := by
    simp [C, hLead i]
  have hDen : denominator.eval 0 = 1 := by
    change Polynomial.evalRingHom 0
      (Finset.univ.prod (fun i => weightedRecurrencePolynomial (w i) (d i) (C i))) = 1
    rw [map_prod]
    refine Finset.prod_eq_one (fun i _ => ?_)
    change (weightedRecurrencePolynomial (w i) (d i) (C i)).eval 0 = 1
    rw [eval_weightedRecurrencePolynomial, zero_pow (hW i).ne', Finset.sum_eq_single (d i)]
    next => simp [hC]
    next =>
      intro j hj hne
      have hjd : j <= d i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hsub : Not (d i - j = 0) := Nat.ne_of_gt (Nat.sub_pos_of_lt (lt_of_le_of_ne hjd hne))
      rw [zero_pow hsub, mul_zero]
    next =>
      intro h
      exact False.elim (h (Finset.mem_range.mpr (Nat.lt_succ_self (d i))))
  let B (i : Fin n) := (Finset.range (d i)).sum (fun j => norm (C i j))
  let M := 1 + Finset.univ.sum B
  have hB (i : Fin n) : 0 <= B i := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM : 1 <= M := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
  have hCoeff (i : Fin n) : B i <= M :=
    (Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hScaled := coordinateRecurrence_mul_powers n d c alpha f hRec
  refine Exists.intro M (And.intro hM (Exists.intro (weightedConeNumerator n w d C F)
    (And.intro hDen (And.intro ?_ ?_))))
  . intro z hz
    exact summable_weightedCone_of_coordinateRecurrence w d C F M hM hW hC hCoeff hScaled hz
  . exact weightedCone_tsum_polynomial n w d C F hW hScaled

/-- A coordinatewise monic recurrence gives a rational cone series after
multiplying each coordinate by its own geometric weight. -/
theorem weightedCone_tsum_polynomial_mul_powers
    (n : Nat) (w d : Fin n -> Nat) (c : Fin n -> Nat -> Complex)
    (alpha : Fin n -> Complex) (f : (Fin n -> Nat) -> Complex)
    (hW : forall i, 0 < w i) (hLead : forall i, c i (d i) = 1)
    (hRec : forall (i : Fin n) (t : Fin n -> Nat),
      (Finset.range (d i + 1)).sum (fun j => c i j * f (Function.update t i (t i + j))) = 0) :
    let F (t : Fin n -> Nat) := f t * Finset.univ.prod (fun i => alpha i ^ t i)
    let denominator : Polynomial Complex := Finset.univ.prod (fun i =>
      (Finset.range (d i + 1)).sum (fun j =>
        Polynomial.C (c i j * alpha i ^ (d i - j)) * Polynomial.X ^ (w i * (d i - j))))
    exists numerator : Polynomial Complex,
      And (denominator.eval 0 = 1)
        (forall z : Complex,
          Summable (fun t => F t * z ^ Finset.univ.sum (fun i => w i * t i)) ->
          denominator.eval z * tsum (fun t => F t * z ^ Finset.univ.sum (fun i => w i * t i)) =
            numerator.eval z) := by
  intro F denominator
  obtain hs := weightedCone_tsum_polynomial_mul_powers_near_zero n w d c alpha f hW hLead hRec
  choose M hM using hs
  choose numerator hn using hM.2
  exact Exists.intro numerator (And.intro hn.1 hn.2.2)

/-- The weighted ordered-diagonal series converges absolutely near zero and agrees there with a rational function whose denominator has constant term one. -/
theorem valuationPrincipalCongruence_diagonalCone_series_mul_powers_near_zero
    {F W V : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    [AddCommGroup V] [Module Complex V]
    (vf : Valuation F W) (rank : Nat) (r : W) (hr : r < 1)
    (rho : MonoidHom (Units (Matrix (Fin rank) (Fin rank) F)) (Module.End Complex V))
    (P : HeckeLocalSubgroupAverage rho (valuationPrincipalCongruenceSubgroup vf rank r))
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (n : Nat) (a : Fin n -> valuationOrderedDiagonalSubmonoid vf rank)
    (w : Fin n -> Nat) (hW : forall i, 0 < w i) (alpha : Fin n -> Complex) :
    let op := P.orderedDiagonalOperators vf rank r hr rho
    let d := Module.finrank Complex (LinearMap.range P.proj)
    let c (i : Fin n) := (op (a i)).charpoly.coeff
    let denominator : Polynomial Complex := Finset.univ.prod (fun i =>
      (Finset.range (d + 1)).sum (fun j => Polynomial.C (c i j * alpha i ^ (d - j)) *
        Polynomial.X ^ (w i * (d - j))))
    forall (b : valuationOrderedDiagonalSubmonoid vf rank)
      (ell : LinearMap (RingHom.id Complex) V Complex),
      (forall (k : valuationPrincipalCongruenceSubgroup vf rank r) (u : V),
        ell (rho k.val u) = ell u) ->
      forall (u : V),
      (forall k : valuationPrincipalCongruenceSubgroup vf rank r, rho k.val u = u) ->
      let aseq (e : Fin n -> Nat) :=
        ell (rho ((valuationDiagonalSection F rank
          (b * Finset.univ.prod (fun i => a i ^ e i)).val).val) u)
      let F (e : Fin n -> Nat) := aseq e * Finset.univ.prod (fun i => alpha i ^ e i)
      exists M : Real, And (1 <= M)
        (exists numerator : Polynomial Complex,
          And (denominator.eval 0 = 1)
            (And (forall z : Complex, M * norm z < 1 ->
              Summable (fun e : Fin n -> Nat => F e * z ^ Finset.univ.sum (fun i => w i * e i)))
              (forall z : Complex,
            Summable (fun e : Fin n -> Nat => F e * z ^ Finset.univ.sum (fun i => w i * e i)) ->
            denominator.eval z *
              tsum (fun e : Fin n -> Nat => F e * z ^ Finset.univ.sum (fun i => w i * e i)) =
              numerator.eval z))) := by
  intro op d c denominator b ell hEll u hU aseq F
  have hDeg (i : Fin n) : (op (a i)).charpoly.natDegree = d :=
    LinearMap.charpoly_natDegree (op (a i))
  have hLead (i : Fin n) : c i d = 1 := by
    change (op (a i)).charpoly.coeff d = 1
    rw [<- hDeg i]
    exact LinearMap.charpoly_monic _
  let fixed : LinearMap.range P.proj := Subtype.mk u (Exists.intro u (P.proj_eq_of_fixed u hU))
  have hRec (i : Fin n) (e : Fin n -> Nat) :
      (Finset.range (d + 1)).sum (fun j => c i j * aseq (Function.update e i (e i + j))) = 0 := by
    let A := op (a i)
    let rest := (Finset.univ.erase i).prod (fun k => a k ^ e k)
    let ellW := (ell.comp (LinearMap.range P.proj).subtype).comp (op (b * rest))
    have hOp : (Finset.range (d + 1)).sum (fun j => HSMul.hSMul (c i j) (A ^ j)) = 0 := by
      change (Finset.range (d + 1)).sum
        (fun j => HSMul.hSMul (A.charpoly.coeff j) (A ^ j)) = 0
      rw [<- hDeg i, <- Polynomial.aeval_eq_sum_range (p := A.charpoly) A]
      exact LinearMap.aeval_self_charpoly A
    have h := congrArg (fun T : Module.End Complex (LinearMap.range P.proj) =>
      ellW (T ((A ^ e i) fixed))) hOp
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, map_sum,
      map_smul, smul_eq_mul, map_zero] at h
    have hTerm (j : Nat) :
        ellW ((A ^ j) ((A ^ e i) fixed)) = aseq (Function.update e i (e i + j)) := by
      have hSplit : Finset.univ.prod (fun k => a k ^ Function.update e i (e i + j) k) =
          rest * a i ^ (e i + j) := by
        rw [<- Finset.prod_erase_mul Finset.univ
          (fun k => a k ^ Function.update e i (e i + j) k) (Finset.mem_univ i)]
        rw [Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro k hk
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      change (ell.comp (LinearMap.range P.proj).subtype)
        (op (b * rest) ((((op (a i)) ^ j) * ((op (a i)) ^ e i)) fixed)) = _
      rw [<- pow_add, Nat.add_comm j (e i), <- map_pow, <- Module.End.mul_apply, <- map_mul]
      rw [mul_assoc, <- hSplit]
      exact P.pairing_proj ell hEll _
    simpa only [hTerm] using h
  exact weightedCone_tsum_polynomial_mul_powers_near_zero n w (fun _ => d) c alpha aseq hW hLead hRec

/-- The ordered diagonal cone series with a geometric multiplier in each
coordinate, on the principal congruence fixed space. -/
theorem valuationPrincipalCongruence_diagonalCone_series_mul_powers
    {F W V : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    [AddCommGroup V] [Module Complex V]
    (vf : Valuation F W) (rank : Nat) (r : W) (hr : r < 1)
    (rho : MonoidHom (Units (Matrix (Fin rank) (Fin rank) F)) (Module.End Complex V))
    (P : HeckeLocalSubgroupAverage rho (valuationPrincipalCongruenceSubgroup vf rank r))
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (n : Nat) (a : Fin n -> valuationOrderedDiagonalSubmonoid vf rank)
    (w : Fin n -> Nat) (hW : forall i, 0 < w i) (alpha : Fin n -> Complex) :
    let op := P.orderedDiagonalOperators vf rank r hr rho
    let d := Module.finrank Complex (LinearMap.range P.proj)
    let c (i : Fin n) := (op (a i)).charpoly.coeff
    let denominator : Polynomial Complex := Finset.univ.prod (fun i =>
      (Finset.range (d + 1)).sum (fun j => Polynomial.C (c i j * alpha i ^ (d - j)) *
        Polynomial.X ^ (w i * (d - j))))
    forall (b : valuationOrderedDiagonalSubmonoid vf rank)
      (ell : LinearMap (RingHom.id Complex) V Complex),
      (forall (k : valuationPrincipalCongruenceSubgroup vf rank r) (u : V),
        ell (rho k.val u) = ell u) ->
      forall (u : V),
      (forall k : valuationPrincipalCongruenceSubgroup vf rank r, rho k.val u = u) ->
      let aseq (e : Fin n -> Nat) :=
        ell (rho ((valuationDiagonalSection F rank
          (b * Finset.univ.prod (fun i => a i ^ e i)).val).val) u)
      let F (e : Fin n -> Nat) := aseq e * Finset.univ.prod (fun i => alpha i ^ e i)
      exists numerator : Polynomial Complex,
        And (denominator.eval 0 = 1)
          (forall z : Complex,
            Summable (fun e : Fin n -> Nat => F e * z ^ Finset.univ.sum (fun i => w i * e i)) ->
            denominator.eval z *
              tsum (fun e : Fin n -> Nat => F e * z ^ Finset.univ.sum (fun i => w i * e i)) =
              numerator.eval z) := by
  intro op d c denominator b ell hEll u hU aseq F
  obtain hs := valuationPrincipalCongruence_diagonalCone_series_mul_powers_near_zero
    vf rank r hr rho P n a w hW alpha b ell hEll u hU
  choose M hM using hs
  choose numerator hn using hM.2
  exact Exists.intro numerator (And.intro hn.1 hn.2.2)

/-- The weighted sum over any finite family of ordered diagonal directions
has the product of their reversed, weight-dilated characteristic polynomials
as a denominator. This denominator is fixed by the directions and the weights. -/
theorem valuationPrincipalCongruence_diagonalCone_series
    {F W V : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    [AddCommGroup V] [Module Complex V]
    (vf : Valuation F W) (rank : Nat) (r : W) (hr : r < 1)
    (rho : MonoidHom (Units (Matrix (Fin rank) (Fin rank) F)) (Module.End Complex V))
    (P : HeckeLocalSubgroupAverage rho (valuationPrincipalCongruenceSubgroup vf rank r))
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (n : Nat) (a : Fin n -> valuationOrderedDiagonalSubmonoid vf rank)
    (w : Fin n -> Nat) (hW : forall i, 0 < w i) :
    let op := P.orderedDiagonalOperators vf rank r hr rho
    let d := Module.finrank Complex (LinearMap.range P.proj)
    let c (i : Fin n) := (op (a i)).charpoly.coeff
    let denominator : Polynomial Complex := Finset.univ.prod (fun i =>
      (Finset.range (d + 1)).sum (fun j => Polynomial.C (c i j) *
        Polynomial.X ^ (w i * (d - j))))
    forall (b : valuationOrderedDiagonalSubmonoid vf rank)
      (ell : LinearMap (RingHom.id Complex) V Complex),
      (forall (k : valuationPrincipalCongruenceSubgroup vf rank r) (u : V),
        ell (rho k.val u) = ell u) ->
      forall (u : V),
      (forall k : valuationPrincipalCongruenceSubgroup vf rank r, rho k.val u = u) ->
      let aseq (e : Fin n -> Nat) :=
        ell (rho ((valuationDiagonalSection F rank
          (b * Finset.univ.prod (fun i => a i ^ e i)).val).val) u)
      exists numerator : Polynomial Complex,
        And (denominator.eval 0 = 1)
          (forall z : Complex,
            Summable (fun e : Fin n -> Nat => aseq e * z ^ Finset.univ.sum (fun i => w i * e i)) ->
            denominator.eval z *
              tsum (fun e : Fin n -> Nat => aseq e * z ^ Finset.univ.sum (fun i => w i * e i)) =
              numerator.eval z) := by
  intro op d c denominator b ell hEll u hU aseq
  have h := valuationPrincipalCongruence_diagonalCone_series_mul_powers
    vf rank r hr rho P n a w hW (fun _ => (1 : Complex)) b ell hEll u hU
  simpa only [one_pow, Finset.prod_const_one, mul_one] using h

end Robin1984.GRH
