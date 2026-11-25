import Robin1984.GRH.GodementJacquetCartanTestPartition

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Cartan double cosets, principal congruence fixed spaces, and rational generating series of coordinatewise linear recurrences.
- Formalization note: Regroups the finite-place integral on the integral matrix locus into finitely many rational cone series using locally constant tests and normalized Haar volumes.
- PROVENANCE-END
-/

/-!
# Finite-place Cartan integrals and rational cone expansions

The finite quotient averages reduce the integral to sums indexed by ordered
Cartan gaps. A test constant modulo the chosen uniformizer power breaks these
gaps into finitely many patterns. Each pattern contributes a translated
matrix coefficient series with a geometric Haar weight.
-/

set_option autoImplicit false

open IsDedekindDomain MeasureTheory NumberField Topology

namespace Robin1984.GRH

private theorem tsum_truncatedGapPartition
    (n R : Nat) (F : (Fin n -> Nat) -> Complex) (hF : Summable F) :
    tsum F = Finset.univ.sum (fun pat : Fin n -> Fin (R + 1) =>
      tsum (fun e : {e : Fin n -> Nat // forall i, (pat i).val < R -> e i = 0} =>
        F (fun i => (pat i).val + e.val i))) := by
  let P (g : Fin n -> Nat) (i : Fin n) : Fin (R + 1) :=
    Fin.mk (min R (g i)) (Nat.lt_succ_of_le (min_le_left _ _))
  let E := Equiv.sigmaFiberEquiv P
  have hS := hF.comp_injective E.injective
  calc
    tsum F = tsum (fun x => F (E x)) := (E.tsum_eq F).symm
    _ = tsum (fun pat => tsum (fun g : {g : Fin n -> Nat // P g = pat} => F g.val)) := hS.tsum_sigma
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro pat _
      let A : Equiv ({g : Fin n -> Nat // P g = pat})
          {g : Fin n -> Nat // forall i, min R (g i) = (pat i).val} :=
        Equiv.subtypeEquivRight (fun g => by
          constructor
          . intro h i
            exact congrArg Fin.val (congrFun h i)
          . intro h
            funext i
            exact Fin.ext (h i))
      let B := A.trans (gapPatternFiber_equiv_zeroInactive n R pat)
      have hInv (e : {e : Fin n -> Nat // forall i, (pat i).val < R -> e i = 0}) :
          (B.symm e).val = fun i => (pat i).val + e.val i := rfl
      rw [<- B.symm.tsum_eq]
      exact tsum_congr (fun e => congrArg F (hInv e))

private theorem cartan_gapVolume_add_of_positiveGaps
    {K : Type*} [Field K] [NumberField K]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (n : Nat) (pi : Units (p.adicCompletion K))
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    [mu.IsHaarMeasure] (b t : Fin n -> Nat) :
    let v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
    let C := valuationIntegralMatrixSubgroup v n
    let D (g : Fin n -> Nat) := valuationIntegralDiagonalDoubleCoset v n
      (valuationUniformizerGapDiagonal n pi g)
    v pi.val = finiteUniformizerValue -> v pi.val < 1 ->
    mu (C : Set (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))) = 1 ->
    (forall i, 0 < (b + t) i <-> 0 < b i) ->
    ((mu (D (b + t))).toReal : Complex) = ((mu (D b)).toReal : Complex) *
      Finset.univ.prod (fun i : Fin n =>
        (((Inv.inv (norm pi.val) : Real) : Complex) ^ ((i.val + 1) * (n - (i.val + 1)))) ^ t i) := by
  intro v C D hp hl hm hSame
  let W (g : Fin n -> Nat) :=
    Finset.univ.sum (fun i : Fin n => ((i.val + 1) * (n - (i.val + 1))) * g i)
  have hW : W (b + t) = W b + W t := by
    simp only [W, Pi.add_apply, Nat.mul_add, Finset.sum_add_distrib]
  have hCard := natCard_valuationCartanAdmissibleResidueMatrix_eq_of_positiveGaps
    v n (b + t) b hSame
  have hCount := cartanPositivePairCount_eq_of_positiveGaps n (b + t) b hSame
  have hb := measure_heckeLocal_valuationUniformizerGapDoubleCoset_eq_monomial
    p n pi mu b hp hl hm
  have ht := measure_heckeLocal_valuationUniformizerGapDoubleCoset_eq_monomial
    p n pi mu (b + t) hp hl hm
  have h := calc
    mu (D (b + t)) = _ := ht
    _ = mu (D b) * (Inv.inv (ENNReal.ofReal (norm pi.val))) ^ W t := by
      rw [hCard, hCount]
      change _ * (Inv.inv (ENNReal.ofReal (norm pi.val))) ^ W (b + t) = _
      rw [hW, pow_add, <- mul_assoc, <- hb]
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (norm_nonneg _), Complex.ofReal_mul, Complex.ofReal_pow]
  congr 1
  unfold W
  rw [<- Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [pow_mul]

private theorem exists_common_rational_denominator_finset
    {I : Type*} (s : Finset I) (f : I -> Complex -> Complex)
    (h : forall i, Membership.mem s i ->
      exists M : Real, exists P Q : Polynomial Complex,
        And (1 <= M) (And (Q.eval 0 = 1)
          (forall z : Complex, M * norm z < 1 -> Q.eval z * f i z = P.eval z))) :
    exists M : Real, exists P Q : Polynomial Complex,
      And (1 <= M) (And (Q.eval 0 = 1)
        (forall z : Complex, M * norm z < 1 ->
          Q.eval z * s.sum (fun i => f i z) = P.eval z)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine Exists.intro 1 (Exists.intro 0 (Exists.intro 1 (And.intro le_rfl (And.intro ?_ ?_))))
    . exact Polynomial.eval_one
    . intro z _
      simp
  | insert a s ha ih =>
    have hA := h a (Finset.mem_insert_self a s)
    have hS := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    choose M A B hab using hA
    choose N C D hcd using hS
    refine Exists.intro (max M N) (Exists.intro (A * D + B * C)
      (Exists.intro (B * D) (And.intro (hab.1.trans (le_max_left _ _)) (And.intro ?_ ?_))))
    . rw [Polynomial.eval_mul, hab.2.1, hcd.2.1, one_mul]
    . intro z hz
      have hzM := (mul_le_mul_of_nonneg_right (le_max_left M N) (norm_nonneg z)).trans_lt hz
      have hzN := (mul_le_mul_of_nonneg_right (le_max_right M N) (norm_nonneg z)).trans_lt hz
      rw [Finset.sum_insert ha, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul]
      calc
        _ = (B.eval z * f a z) * D.eval z +
            B.eval z * (D.eval z * s.sum (fun i => f i z)) := by
          rw [mul_add]
          ac_rfl
        _ = _ := by rw [hab.2.2 z hzM, hcd.2.2 z hzN]

private theorem principalCongruence_translated_fixed_pair
    {F W V : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    [AddCommGroup V] [Module Complex V] (v : Valuation F W) (n : Nat) (r : W)
    (rho : MonoidHom (Units (Matrix (Fin n) (Fin n) F)) (Module.End Complex V))
    (ell : LinearMap (RingHom.id Complex) V Complex) (u : V)
    (hEll : forall (h : valuationPrincipalCongruenceSubgroup v n r) (x : V),
      ell (rho h.val x) = ell x)
    (hU : forall h : valuationPrincipalCongruenceSubgroup v n r, rho h.val u = u)
    (k : valuationIntegralMatrixSubgroup v n) :
    And (forall (h : valuationPrincipalCongruenceSubgroup v n r) (x : V),
      (ell.comp (rho k.val)) (rho h.val x) = (ell.comp (rho k.val)) x)
      (forall h : valuationPrincipalCongruenceSubgroup v n r,
        rho h.val (rho k.val u) = rho k.val u) := by
  let C := valuationIntegralMatrixSubgroup v n
  let U := valuationPrincipalCongruenceSubgroup v n r
  have hConj (l : C) (h : U) : Membership.mem U (l.val * h.val * Inv.inv l.val) := by
    let j : C := Subtype.mk h.val h.property.1
    have hj : Membership.mem (U.comap C.subtype) j := h.property
    have h := principalCongruence_normal_in_integralMatrixSubgroup v n r l j hj
    exact h
  constructor
  . intro h x
    let h' : U := Subtype.mk (k.val * h.val * Inv.inv k.val) (hConj k h)
    have hEq : k.val * h.val = h'.val * k.val := by simp [h', mul_assoc]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, <- Module.End.mul_apply,
      <- map_mul, hEq, map_mul, Module.End.mul_apply]
    exact hEll h' (rho k.val x)
  . intro h
    let h' : U := Subtype.mk ((Inv.inv k).val * h.val * Inv.inv (Inv.inv k).val)
      (hConj (Inv.inv k) h)
    have hEq : h.val * k.val = k.val * h'.val := by simp [h', mul_assoc]
    rw [<- Module.End.mul_apply, <- map_mul, hEq, map_mul, Module.End.mul_apply, hU h']

private theorem local_test_coefficient_biinvariant
    {F W V : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    [AddCommGroup V] [Module Complex V] (v : Valuation F W) (n : Nat) (r : W)
    (rho : MonoidHom (Units (Matrix (Fin n) (Fin n) F)) (Module.End Complex V))
    (ell : LinearMap (RingHom.id Complex) V Complex) (u : V)
    (hEll : forall (h : valuationPrincipalCongruenceSubgroup v n r) (x : V),
      ell (rho h.val x) = ell x)
    (hU : forall h : valuationPrincipalCongruenceSubgroup v n r, rho h.val u = u)
    (phi : (Fin n -> Fin n -> F) -> Complex)
    (hMod : forall X Y : Fin n -> Fin n -> F, (forall i j, v (X i j) <= 1) ->
      (forall i j, v (Y i j - X i j) <= r) -> phi Y = phi X)
    (g : Units (Matrix (Fin n) (Fin n) F)) (hg : forall i j, v (g.val i j) <= 1)
    (h : valuationPrincipalCongruenceSubgroup v n r) :
    let f (a : Units (Matrix (Fin n) (Fin n) F)) :=
      phi (fun i j => a.val i j) * ell (rho a u)
    And (f (h.val * g) = f g) (f (g * h.val) = f g) := by
  intro f
  have hTest := congruence_test_invariant_on_integralMatrices v n r phi hMod g hg h
  constructor
  . change phi (fun i j => (h.val * g).val i j) * ell (rho (h.val * g) u) = _
    rw [hTest.1, map_mul, Module.End.mul_apply, hEll h]
  . change phi (fun i j => (g * h.val).val i j) * ell (rho (g * h.val) u) = _
    rw [hTest.2, map_mul, Module.End.mul_apply, hU h]

/-- An integrable determinant-weighted test matrix coefficient on the integral matrix locus expands into its normalized finite Cartan averages. -/
theorem hasSum_heckeLocal_detWeightedIntegral_finiteCartanAverages
    {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module Complex V]
    (p : HeightOneSpectrum (RingOfIntegers K)) (n : Nat)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (pi a : Units (p.adicCompletion K))
    (hPi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue)
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    [mu.IsMulLeftInvariant]
    (rho : MonoidHom (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))) (Module.End Complex V))
    (ell : LinearMap (RingHom.id Complex) V Complex) (u : V)
    (phi : (Fin n -> Fin n -> p.adicCompletion K) -> Complex) (z : Complex) :
    let L := p.adicCompletion K
    let G := Units (Matrix (Fin n) (Fin n) L)
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let C := valuationIntegralMatrixSubgroup v n
    let U := valuationPrincipalCongruenceSubgroup v n (v a.val)
    let H := U.comap C.subtype
    let Q := Quotient (QuotientGroup.leftRel H)
    let w := Inv.inv (Nat.card Q : Real)
    let S := Set.ofPred (fun g : G => forall i j, v (g.val i j) <= 1)
    let dg (gaps : Fin n -> Nat) := valuationUniformizerGapDiagonal n pi gaps
    let d (gaps : Fin n -> Nat) := (valuationDiagonalSection L n (dg gaps)).val
    let D (gaps : Fin n -> Nat) := valuationIntegralDiagonalDoubleCoset v n (dg gaps)
    let f (g : G) := phi (fun i j => g.val i j) * ell (rho g u)
    let F (g : G) := (norm g.val.det : Complex) ^ z * f g
    (forall (h : U) (x : V), ell (rho h.val x) = ell x) ->
    (forall h : U, rho h.val u = u) ->
    (forall X Y : Fin n -> Fin n -> L, (forall i j, v (X i j) <= 1) ->
      (forall i j, v (Y i j - X i j) <= v a.val) -> phi Y = phi X) ->
    mu (C : Set G) = 1 -> IntegrableOn F S mu ->
    HasSum (fun gaps : Fin n -> Nat =>
      ((norm pi.val : Complex) ^ z) ^ Finset.univ.sum (fun j => (j.val + 1) * gaps j) *
        (HSMul.hSMul ((mu (D gaps)).toReal)
          (tsum (fun l : Q => HSMul.hSMul w
            (tsum (fun r : Q => HSMul.hSMul w (f (l.out.val * d gaps * r.out.val))))))))
      (integral (mu.restrict S) F) := by
  intro L G v C U H Q w S dg d D f F hEll hU hMod hNorm hInt
  let _ : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  have hRow : IsOpenEmbedding (heckeLocalMatrixUnitEntries (I := Fin n) (F := L)) :=
    isOpenEmbedding_heckeLocalMatrixUnitEntries
  let _ : SecondCountableTopology G := hRow.isEmbedding.secondCountableTopology
  have hVO : IsOpen (v.integer : Set L) := Valued.isOpen_valuationSubring L
  have hVC : IsCompact (v.integer : Set L) :=
    isCompact_iff_compactSpace.mpr (compactSpace_heckeLocalIntegers p)
  have hC := isOpen_valuationIntegralMatrixSubgroup v n hVO
  have hCompact := isCompact_valuationIntegralMatrixSubgroup v n hVC
  have hUeq : H.map C.subtype = U :=
    map_comap_principalCongruence_integralMatrixSubgroup v n (v a.val)
  have hUopen : IsOpen (U : Set G) := isOpen_valuationPrincipalCongruenceSubgroup v n a hVO
  have hMapOpen : IsOpen ((H.map C.subtype : Subgroup G) : Set G) := by
    rw [hUeq]
    exact hUopen
  have hNormal := principalCongruence_normal_in_integralMatrixSubgroup v n (v a.val)
  have hUnion : Set.iUnion D = S := iUnion_heckeLocal_valuationUniformizerGapDoubleCosets p n pi hPi
  have hMeas (b : Fin n -> Nat) : MeasurableSet (D b) :=
    (isOpen_valuationIntegralDiagonalDoubleCoset v n (dg b) hVO).measurableSet
  have hSub (b : Fin n -> Nat) : D b <= S := by
    intro g hg
    rw [<- hUnion]
    exact Set.mem_iUnion_of_mem b hg
  have hIntegrable (b : Fin n -> Nat) : IntegrableOn f (D b) mu := by
    let m := Finset.univ.sum (fun j : Fin n => (j.val + 1) * b j)
    let c := ((norm pi.val ^ m : Real) : Complex) ^ z
    have hPos : 0 < norm pi.val ^ m := pow_pos (norm_pos_iff.mpr pi.ne_zero) _
    have hC0 : Not (c = 0) := Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hPos)))
    have hSame (g : G) (hg : Membership.mem (D b) g) : f g = Inv.inv c * F g := by
      have hv := norm_det_of_mem_heckeLocal_valuationUniformizerGapDoubleCoset p n pi b g hg
      change f g = Inv.inv c * ((norm g.val.det : Complex) ^ z * f g)
      rw [hv]
      change f g = Inv.inv c * (c * f g)
      rw [<- mul_assoc]
      simp [hC0]
    exact (integrableOn_congr_fun hSame (hMeas b)).mpr
      ((hInt.mono_set (hSub b)).const_mul (Inv.inv c))
  have hSet (b : Fin n -> Nat) : D b = DoubleCoset.doubleCoset (d b) (C : Set G) (C : Set G) :=
    valuationIntegralDiagonalDoubleCoset_eq_doubleCoset v n (dg b)
  have hAvg (b : Fin n -> Nat) : integral (mu.restrict (D b)) f =
      HSMul.hSMul ((mu (D b)).toReal) (tsum (fun l : Q => HSMul.hSMul w
        (tsum (fun r : Q => HSMul.hSMul w (f (l.out.val * d b * r.out.val)))))) := by
    rw [hSet b]
    refine integral_cartanDoubleCoset_eq_finite_coset_average mu C H hCompact hC hNorm
      hNormal (d b) f hMapOpen ?_ ?_ ?_
    . rw [<- hSet b]
      exact hIntegrable b
    . intro g hg h hh
      rw [<- hSet b] at hg
      have hhU : Membership.mem U h := by
        rw [<- hUeq]
        exact hh
      exact (local_test_coefficient_biinvariant v n (v a.val) rho ell u hEll hU phi hMod
        g (hSub b hg) (Subtype.mk h hhU)).1
    . intro g hg h hh
      rw [<- hSet b] at hg
      have hhU : Membership.mem U h := by
        rw [<- hUeq]
        exact hh
      exact (local_test_coefficient_biinvariant v n (v a.val) rho ell u hEll hU phi hMod
        g (hSub b hg) (Subtype.mk h hhU)).2
  have h := hasSum_heckeLocal_detWeightedIntegral_valuationUniformizerGapDoubleCosets
    p n pi hPi mu f z hInt
  change HasSum (fun b : Fin n -> Nat => ((norm pi.val : Complex) ^ z) ^
    Finset.univ.sum (fun j => (j.val + 1) * b j) * integral (mu.restrict (D b)) f) _ at h
  simpa only [hAvg] using h

private theorem masked_uniformizerCone_near_zero
    {F W V : Type*} [Field F] [LinearOrderedCommGroupWithZero W]
    [AddCommGroup V] [Module Complex V]
    (v : Valuation F W) (n R : Nat) (r : W) (hr : r < 1)
    (rho : MonoidHom (Units (Matrix (Fin n) (Fin n) F)) (Module.End Complex V))
    (P : HeckeLocalSubgroupAverage rho (valuationPrincipalCongruenceSubgroup v n r))
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (pi : Units F) (hp : v pi.val <= 1) (pat : Fin n -> Fin (R + 1))
    (alpha : Fin n -> Complex)
    (ell : LinearMap (RingHom.id Complex) V Complex) (u : V)
    (hEll : forall (h : valuationPrincipalCongruenceSubgroup v n r) (x : V),
      ell (rho h.val x) = ell x)
    (hU : forall h : valuationPrincipalCongruenceSubgroup v n r, rho h.val u = u) :
    let B (i : Fin n) := (pat i).val
    let E (e : Fin n -> Nat) := Finset.univ.sum (fun i => (i.val + 1) * e i)
    let Active (e : Fin n -> Nat) := forall i, (pat i).val < R -> e i = 0
    let T (z : Complex) (e : Fin n -> Nat) :=
      ell (rho ((valuationDiagonalSection F n
        (valuationUniformizerGapDiagonal n pi (fun i => B i + e i))).val) u) *
        Finset.univ.prod (fun i => alpha i ^ e i) * z ^ E e
    exists M : Real, exists N D : Polynomial Complex,
      And (1 <= M) (And (D.eval 0 = 1)
        (forall z : Complex, M * norm z < 1 ->
          And (Summable (fun e : {e : Fin n -> Nat // Active e} => T z e.val))
            (D.eval z * tsum (fun e : {e : Fin n -> Nat // Active e} => T z e.val) =
              N.eval z))) := by
  classical
  intro B E Active T
  let a := valuationUniformizerConeDirections v n pi hp
  let base : valuationOrderedDiagonalSubmonoid v n :=
    Finset.univ.prod (fun i => a i ^ B i)
  let beta (i : Fin n) := if (pat i).val < R then (0 : Complex) else alpha i
  let w (i : Fin n) := i.val + 1
  have hW (i : Fin n) : 0 < w i := Nat.succ_pos _
  let op := P.orderedDiagonalOperators v n r hr rho
  let d := Module.finrank Complex (LinearMap.range P.proj)
  let c (i : Fin n) := (op (a i)).charpoly.coeff
  let D : Polynomial Complex := Finset.univ.prod (fun i =>
    (Finset.range (d + 1)).sum (fun j => Polynomial.C (c i j * beta i ^ (d - j)) *
      Polynomial.X ^ (w i * (d - j))))
  let F0 (z : Complex) (e : Fin n -> Nat) :=
    ell (rho ((valuationDiagonalSection F n
      (base * Finset.univ.prod (fun i => a i ^ e i)).val).val) u) *
      Finset.univ.prod (fun i => beta i ^ e i) * z ^ E e
  have hProd (e : Fin n -> Nat) : (Finset.univ.prod (fun i => a i ^ e i)).val =
      valuationUniformizerGapDiagonal n pi e := by
    change (valuationOrderedDiagonalSubmonoid v n).subtype (Finset.univ.prod (fun i => a i ^ e i)) = _
    rw [map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact map_pow (valuationOrderedDiagonalSubmonoid v n).subtype (a i) (e i)
  have hDiag (e : Fin n -> Nat) :
      (base * Finset.univ.prod (fun i => a i ^ e i)).val =
        valuationUniformizerGapDiagonal n pi (fun i => B i + e i) := by
    change base.val * (Finset.univ.prod (fun i => a i ^ e i)).val = _
    rw [hProd e]
    change (Finset.univ.prod (fun i => a i ^ B i)).val * valuationUniformizerGapDiagonal n pi e = _
    rw [hProd B]
    simp only [valuationUniformizerGapDiagonal, pow_add, Finset.prod_mul_distrib]
  have hF (z : Complex) (e : Fin n -> Nat) :
      F0 z e = if Active e then T z e else 0 := by
    unfold F0
    rw [hDiag]
    have hMask := masked_gap_weights n R pat alpha e
    change Finset.univ.prod (fun i => beta i ^ e i) =
      (if Active e then Finset.univ.prod (fun i => alpha i ^ e i) else 0) at hMask
    rw [hMask]
    by_cases he : Active e
    . simp only [if_pos he, T]
    . simp only [if_neg he, mul_zero, zero_mul]
  have h := valuationPrincipalCongruence_diagonalCone_series_mul_powers_near_zero
    v n r hr rho P n a w hW beta base ell hEll u hU
  choose M hM using h
  choose N hn using hM.2
  have hD : D.eval 0 = 1 := hn.1
  refine Exists.intro M (Exists.intro N (Exists.intro D (And.intro hM.1 (And.intro hD ?_))))
  intro z hz
  have hSum : Summable (F0 z) := hn.2.1 z hz
  have hF0 : D.eval z * tsum (F0 z) = N.eval z := hn.2.2 z hSum
  have hFace : Summable (fun e : {e : Fin n -> Nat // Active e} => T z e.val) :=
    (hSum.comp_injective Subtype.val_injective).congr
      (fun e => (hF z e.val).trans (if_pos e.property))
  have hTsum : tsum (fun e : {e : Fin n -> Nat // Active e} => T z e.val) = tsum (F0 z) := by
    let S := Set.ofPred Active
    change tsum (fun e : S => T z e.val) = _
    exact (tsum_subtype S (T z)).trans (tsum_congr (fun e => by
      change S.indicator (T z) e = F0 z e
      rw [hF]
      by_cases he : Active e
      . have hm : Membership.mem S e := he
        rw [Set.indicator_of_mem hm, if_pos he]
      . have hn : Not (Membership.mem S e) := he
        rw [Set.indicator_of_notMem hn, if_neg he]))
  exact And.intro hFace (by rw [hTsum, hF0])

private theorem heckeLocal_cartanPattern_pair_rational
    {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module Complex V]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (n R : Nat) (hR : 0 < R) (pi : Units (p.adicCompletion K))
    (hPi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue)
    (hLt : Valued.v (pi : p.adicCompletion K) < 1)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    [mu.IsHaarMeasure]
    (rho : MonoidHom (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))) (Module.End Complex V))
    (P : HeckeLocalSubgroupAverage rho
      (valuationPrincipalCongruenceSubgroup Valued.v n (Valued.v (pi : p.adicCompletion K) ^ R)))
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (ell : LinearMap (RingHom.id Complex) V Complex) (u : V)
    (phi : (Fin n -> Fin n -> p.adicCompletion K) -> Complex) :
    let L := p.adicCompletion K
    let G := Units (Matrix (Fin n) (Fin n) L)
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let C := valuationIntegralMatrixSubgroup v n
    let U := valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R)
    let d (g : Fin n -> Nat) := (valuationDiagonalSection L n (valuationUniformizerGapDiagonal n pi g)).val
    let D (g : Fin n -> Nat) := valuationIntegralDiagonalDoubleCoset v n (valuationUniformizerGapDiagonal n pi g)
    let E (g : Fin n -> Nat) := Finset.univ.sum (fun i => (i.val + 1) * g i)
    let f (g : G) := phi (fun i j => g.val i j) * ell (rho g u)
    (forall (h : U) (x : V), ell (rho h.val x) = ell x) ->
    (forall h : U, rho h.val u = u) ->
    (forall X Y : Fin n -> Fin n -> L, (forall i j, v (X i j) <= 1) ->
      (forall i j, v (Y i j - X i j) <= v pi.val ^ R) -> phi Y = phi X) ->
    mu (C : Set G) = 1 ->
    forall (pat : Fin n -> Fin (R + 1)) (l k : C),
      let A := {e : Fin n -> Nat // forall i, (pat i).val < R -> e i = 0}
      let b (i : Fin n) := (pat i).val
      let F (z : Complex) (e : A) :=
        z ^ E (b + e.val) * ((mu (D (b + e.val))).toReal : Complex) *
          f (l.val * d (b + e.val) * k.val)
      exists M : Real, exists N Q : Polynomial Complex,
        And (1 <= M) (And (Q.eval 0 = 1)
          (forall z : Complex, M * norm z < 1 ->
            And (Summable (F z)) (Q.eval z * tsum (F z) = N.eval z))) := by
  intro L G v C U d D E f hEll hU hMod hNorm pat l k A b F
  have hRad : v pi.val ^ R < 1 :=
    (pow_lt_one_iff_of_nonneg (zero_le : 0 <= v pi.val) hR.ne').mpr hLt
  let ell' := ell.comp (rho l.val)
  let u' := rho k.val u
  have hL := (principalCongruence_translated_fixed_pair v n (v pi.val ^ R)
    rho ell u hEll hU l).1
  have hK := (principalCongruence_translated_fixed_pair v n (v pi.val ^ R)
    rho ell u hEll hU k).2
  let alpha (i : Fin n) : Complex :=
    ((Inv.inv (norm pi.val) : Real) : Complex) ^ ((i.val + 1) * (n - (i.val + 1)))
  let T (z : Complex) (e : A) :=
    ell' (rho (d (b + e.val)) u') * Finset.univ.prod (fun i => alpha i ^ e.val i) * z ^ E e.val
  have hCone := masked_uniformizerCone_near_zero v n R (v pi.val ^ R) hRad rho P
    pi hLt.le pat alpha ell' u' hL hK
  choose M N Q hQ using hCone
  let base := l.val * d b * k.val
  let ph := phi (fun i j => base.val i j)
  let factor : Complex := ((mu (D b)).toReal : Complex) * ph
  let poly := Polynomial.C factor * Polynomial.X ^ E b * N
  refine Exists.intro M (Exists.intro poly (Exists.intro Q (And.intro hQ.1 (And.intro hQ.2.1 ?_))))
  intro z hz
  have hz0 := hQ.2.2 z hz
  have hSum : Summable (T z) := hz0.1
  have hRat : Q.eval z * tsum (T z) = N.eval z := hz0.2
  have hUnion : Set.iUnion D = Set.ofPred (fun g : G => forall i j, v (g.val i j) <= 1) :=
    iUnion_heckeLocal_valuationUniformizerGapDoubleCosets p n pi hPi
  have hBaseMem : Membership.mem (D b) base := by
    have hSet : D b = DoubleCoset.doubleCoset (d b) (C : Set G) (C : Set G) :=
      valuationIntegralDiagonalDoubleCoset_eq_doubleCoset v n (valuationUniformizerGapDiagonal n pi b)
    rw [hSet]
    exact DoubleCoset.mem_doubleCoset.mpr (Exists.intro l.val
      (And.intro l.property (Exists.intro k.val (And.intro k.property rfl))))
  have hBase (i j : Fin n) : v (base.val i j) <= 1 := by
    have h := Set.mem_iUnion_of_mem b hBaseMem
    rw [hUnion] at h
    exact h i j
  have hl (i j : Fin n) : v (l.val.val i j) <= 1 :=
    ((mem_valuationIntegralMatrixSubgroup_iff v n l.val).mp l.property).1 i j
  have hk (i j : Fin n) : v (k.val.val i j) <= 1 :=
    ((mem_valuationIntegralMatrixSubgroup_iff v n k.val).mp k.property).1 i j
  have hTerm (e : A) : F z e = (factor * z ^ E b) * T z e := by
    have hCut (i : Fin n) : min R ((b + e.val) i) = min R (b i) := by
      have he := ((gapPatternFiber_equiv_zeroInactive n R pat).symm e).property i
      change min R ((b + e.val) i) = b i at he
      exact he.trans (min_eq_right (Nat.le_of_lt_succ (pat i).isLt)).symm
    have hDiag : forall i j, v ((d (b + e.val)).val i j - (d b).val i j) <= v pi.val ^ R :=
      valuationUniformizerGapDiagonal_congruent_of_min_gaps v n R pi hLt.le _ _ hCut
    have hPhi : phi (fun i j => (l.val * d (b + e.val) * k.val).val i j) = ph := by
      apply hMod _ _ hBase
      exact valuation_integral_matrix_multipliers_preserve_congruence v n (v pi.val ^ R)
        l.val.val (d (b + e.val)).val (d b).val k.val.val hl hk hDiag
    have hSupport (i : Fin n) : 0 < (b + e.val) i <-> 0 < b i :=
      (positiveGap_iff_of_min_gaps n R hR _ _ hCut) i
    have hVol : ((mu (D (b + e.val))).toReal : Complex) = ((mu (D b)).toReal : Complex) *
        Finset.univ.prod (fun i => alpha i ^ e.val i) :=
      cartan_gapVolume_add_of_positiveGaps p n pi mu b e.val hPi hLt hNorm hSupport
    have hE : E (b + e.val) = E b + E e.val := by
      simp only [E, Pi.add_apply, Nat.mul_add, Finset.sum_add_distrib]
    unfold F f
    rw [hE, pow_add, hVol, hPhi]
    simp only [T, factor, ell', u', map_mul, Module.End.mul_apply, LinearMap.comp_apply]
    ac_rfl
  have hSumF : Summable (F z) := (hSum.mul_left (factor * z ^ E b)).congr (fun e => (hTerm e).symm)
  have hTF : tsum (F z) = (factor * z ^ E b) * tsum (T z) :=
    (tsum_congr hTerm).trans (hSum.tsum_mul_left _)
  refine And.intro hSumF ?_
  rw [hTF, mul_left_comm, hRat]
  simp only [poly, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]

private theorem finite_family_rational_series
    {I A : Type*} [Fintype I] (u : I -> Complex -> A -> Complex)
    (h : forall i, exists M : Real, exists N Q : Polynomial Complex,
      And (1 <= M) (And (Q.eval 0 = 1)
        (forall z : Complex, M * norm z < 1 ->
          And (Summable (u i z)) (Q.eval z * tsum (u i z) = N.eval z)))) :
    exists M : Real, exists N Q : Polynomial Complex,
      And (1 <= M) (And (Q.eval 0 = 1)
        (forall z : Complex, M * norm z < 1 ->
          And (Summable (fun a => Finset.univ.sum (fun i => u i z a)))
            (Q.eval z * tsum (fun a => Finset.univ.sum (fun i => u i z a)) = N.eval z))) := by
  classical
  choose M N Q hQ using h
  have hR := exists_common_rational_denominator_finset Finset.univ
    (fun i z => tsum (u i z)) (fun i _ =>
      Exists.intro (M i) (Exists.intro (N i) (Exists.intro (Q i)
        (And.intro (hQ i).1 (And.intro (hQ i).2.1 (fun z hz => ((hQ i).2.2 z hz).2))))))
  choose K P D hD using hR
  let B := 1 + Finset.univ.sum M
  have hB (i : I) : M i <= B :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hQ j).1) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine Exists.intro (max B K) (Exists.intro P (Exists.intro D
    (And.intro (hD.1.trans (le_max_right _ _)) (And.intro hD.2.1 ?_))))
  intro z hz
  have hzK := (mul_le_mul_of_nonneg_right (le_max_right B K) (norm_nonneg z)).trans_lt hz
  have hSummable (i : I) (_ : Membership.mem (Finset.univ : Finset I) i) : Summable (u i z) :=
    ((hQ i).2.2 z ((mul_le_mul_of_nonneg_right ((hB i).trans (le_max_left B K))
      (norm_nonneg z)).trans_lt hz)).1
  refine And.intro (summable_sum hSummable) ?_
  rw [Summable.tsum_finsetSum hSummable]
  exact hD.2.2 z hzK

/-- For a congruence-constant test and a coefficient fixed at the same depth,
the finite-place determinant-weighted integral on the integral matrix locus
agrees with a rational function of the uniformizer weight wherever that
weight is sufficiently small and the integral is integrable. The denominator
has constant coefficient one. -/
theorem heckeLocal_detWeightedIntegral_rational
    {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module Complex V]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (n R : Nat) (hR : 0 < R) (pi : Units (p.adicCompletion K))
    (hPi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue)
    (hLt : Valued.v (pi : p.adicCompletion K) < 1)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    [mu.IsHaarMeasure]
    (rho : MonoidHom (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))) (Module.End Complex V))
    (P : HeckeLocalSubgroupAverage rho
      (valuationPrincipalCongruenceSubgroup Valued.v n (Valued.v (pi : p.adicCompletion K) ^ R)))
    [FiniteDimensional Complex (LinearMap.range P.proj)]
    (ell : LinearMap (RingHom.id Complex) V Complex) (u : V)
    (phi : (Fin n -> Fin n -> p.adicCompletion K) -> Complex) :
    let L := p.adicCompletion K
    let G := Units (Matrix (Fin n) (Fin n) L)
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let C := valuationIntegralMatrixSubgroup v n
    let U := valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R)
    let f (g : G) := phi (fun i j => g.val i j) * ell (rho g u)
    (forall (h : U) (x : V), ell (rho h.val x) = ell x) ->
    (forall h : U, rho h.val u = u) ->
    (forall X Y : Fin n -> Fin n -> L, (forall i j, v (X i j) <= 1) ->
      (forall i j, v (Y i j - X i j) <= v pi.val ^ R) -> phi Y = phi X) ->
    mu (C : Set G) = 1 ->
    let S := Set.ofPred (fun g : G => forall i j, v (g.val i j) <= 1)
    let Z (s : Complex) := (norm pi.val : Complex) ^ s
    let F (s : Complex) (g : G) := (norm g.val.det : Complex) ^ s * f g
    exists M : Real, exists N Q : Polynomial Complex,
      And (1 <= M) (And (Q.eval 0 = 1)
        (forall s : Complex, M * norm (Z s) < 1 -> IntegrableOn (F s) S mu ->
          Q.eval (Z s) * integral (mu.restrict S) (F s) = N.eval (Z s))) := by
  classical
  intro L G v C U f hEll hU hMod hNorm S Z F
  let d (g : Fin n -> Nat) := (valuationDiagonalSection L n (valuationUniformizerGapDiagonal n pi g)).val
  let D (g : Fin n -> Nat) := valuationIntegralDiagonalDoubleCoset v n (valuationUniformizerGapDiagonal n pi g)
  let E (g : Fin n -> Nat) := Finset.univ.sum (fun i => (i.val + 1) * g i)
  let H := U.comap C.subtype
  let Q0 := Quotient (QuotientGroup.leftRel H)
  have hVO : IsOpen (v.integer : Set L) := Valued.isOpen_valuationSubring L
  have hVC : IsCompact (v.integer : Set L) := isCompact_iff_compactSpace.mpr (compactSpace_heckeLocalIntegers p)
  let _ : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_valuationIntegralMatrixSubgroup v n hVC)
  have hVPowAux (j : Nat) : v (pi ^ j).val = v pi.val ^ j := by
    induction j with
    | zero =>
      rw [pow_zero, pow_zero]
      exact map_one v
    | succ j ih =>
      rw [pow_succ pi, Units.val_mul, map_mul, ih, pow_succ]
  have hVPow := hVPowAux R
  have hOpenU : IsOpen (U : Set G) := by
    change IsOpen (valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R) : Set G)
    rw [<- hVPow]
    exact isOpen_valuationPrincipalCongruenceSubgroup v n (pi ^ R) hVO
  have hOpenH : IsOpen (H : Set C) := hOpenU.preimage continuous_subtype_val
  let _ : Finite Q0 := H.quotient_finite_of_isOpen hOpenH
  let _ : Fintype Q0 := Fintype.ofFinite Q0
  let w := Inv.inv (Nat.card Q0 : Real)
  let B := Fin n -> Fin (R + 1)
  let O (pat : B) := {e : Fin n -> Nat // forall i, (pat i).val < R -> e i = 0}
  let Gaps (pat : B) (e : O pat) := fun i => (pat i).val + e.val i
  let term (pat : B) (q : Prod Q0 Q0) (z : Complex) (e : O pat) :=
    z ^ E (Gaps pat e) * ((mu (D (Gaps pat e))).toReal : Complex) *
      f (q.1.out.val * d (Gaps pat e) * q.2.out.val)
  have hp (pat : B) := finite_family_rational_series (term pat)
    (fun q => heckeLocal_cartanPattern_pair_rational p n R hR pi hPi hLt mu
      rho P ell u phi hEll hU hMod hNorm pat q.1.out q.2.out)
  choose M0 N0 Q1 hQ1 using hp
  let g (pat : B) (z : Complex) :=
    (w : Complex) ^ 2 * tsum (fun e => Finset.univ.sum (fun q => term pat q z e))
  have hPat (pat : B) (_ : Membership.mem (Finset.univ : Finset B) pat) :
      exists M : Real, exists N Q : Polynomial Complex,
        And (1 <= M) (And (Q.eval 0 = 1)
          (forall z : Complex, M * norm z < 1 -> Q.eval z * g pat z = N.eval z)) := by
    refine Exists.intro (M0 pat) (Exists.intro (Polynomial.C ((w : Complex) ^ 2) * N0 pat)
      (Exists.intro (Q1 pat) (And.intro (hQ1 pat).1 (And.intro (hQ1 pat).2.1 ?_))))
    intro z hz
    unfold g
    rw [mul_left_comm, ((hQ1 pat).2.2 z hz).2, Polynomial.eval_mul, Polynomial.eval_C]
  have hComb := exists_common_rational_denominator_finset Finset.univ g hPat
  choose M1 N Q hQ using hComb
  let L0 := 1 + Finset.univ.sum M0
  have hL (pat : B) : M0 pat <= L0 :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hQ1 j).1) (Finset.mem_univ pat)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine Exists.intro (max L0 M1) (Exists.intro N (Exists.intro Q
    (And.intro (hQ.1.trans (le_max_right _ _)) (And.intro hQ.2.1 ?_))))
  intro s hs hInt
  let z := Z s
  have hz1 : M1 * norm z < 1 :=
    (mul_le_mul_of_nonneg_right (le_max_right L0 M1) (norm_nonneg z)).trans_lt hs
  have hz0 (pat : B) : M0 pat * norm z < 1 :=
    (mul_le_mul_of_nonneg_right ((hL pat).trans (le_max_left L0 M1)) (norm_nonneg z)).trans_lt hs
  have hEll0 : forall (h : valuationPrincipalCongruenceSubgroup v n (v (pi ^ R).val)) (x : V),
      ell (rho h.val x) = ell x := by rw [hVPow]; exact hEll
  have hU0 : forall (h : valuationPrincipalCongruenceSubgroup v n (v (pi ^ R).val)), rho h.val u = u := by
    rw [hVPow]; exact hU
  have hMod0 : forall X Y : Fin n -> Fin n -> L, (forall i j, v (X i j) <= 1) ->
      (forall i j, v (Y i j - X i j) <= v (pi ^ R).val) -> phi Y = phi X := by rw [hVPow]; exact hMod
  let T (b : Fin n -> Nat) := z ^ E b * ((mu (D b)).toReal : Complex) *
    tsum (fun l : Q0 => (w : Complex) * tsum (fun r : Q0 => (w : Complex) * f (l.out.val * d b * r.out.val)))
  have hSum : HasSum T (integral (mu.restrict S) (F s)) := by
    have h := hasSum_heckeLocal_detWeightedIntegral_finiteCartanAverages p n pi (pi ^ R)
      hPi mu rho ell u phi s hEll0 hU0 hMod0 hNorm hInt
    rw [hVPow] at h
    simpa only [T, Complex.real_smul, mul_assoc] using h
  have hTerm (pat : B) (e : O pat) :
      T (Gaps pat e) = (w : Complex) ^ 2 * Finset.univ.sum (fun q : Prod Q0 Q0 => term pat q z e) := by
    have hInner (l : Q0) :
        tsum (fun r : Q0 => (w : Complex) * f (l.out.val * d (Gaps pat e) * r.out.val)) =
          (w : Complex) * Finset.univ.sum (fun r : Q0 => f (l.out.val * d (Gaps pat e) * r.out.val)) := by
      rw [tsum_fintype, Finset.mul_sum]
    unfold T
    simp only [hInner, tsum_fintype, <- Finset.mul_sum, <- mul_assoc]
    rw [<- Finset.univ_product_univ, Finset.sum_product]
    simp only [term, <- Finset.mul_sum]
    rw [pow_two]
    ac_rfl
  have hTotal : integral (mu.restrict S) (F s) = Finset.univ.sum (fun pat : B => g pat z) := by
    rw [<- hSum.tsum_eq, tsum_truncatedGapPartition n R T hSum.summable]
    apply Finset.sum_congr rfl
    intro pat _
    change tsum (fun e : O pat => T (Gaps pat e)) = g pat z
    exact (tsum_congr (hTerm pat)).trans (((hQ1 pat).2.2 z (hz0 pat)).1.tsum_mul_left _)
  rw [hTotal]
  exact hQ.2.2 z hz1

end Robin1984.GRH
