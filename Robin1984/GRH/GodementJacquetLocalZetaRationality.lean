import Robin1984.GRH.GodementJacquetCartanLocalIntegral

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement-Jacquet local zeta integrals, compact support, and smooth admissible representations.
- Formalization note: Uses scalar dilation and a common congruence depth to deduce right-half-plane convergence and rationality for compactly supported locally constant matrix tests.
- PROVENANCE-END
-/

/-!
# Rationality for compactly supported local zeta tests

A scalar uniformizer power moves the compact support into the integral
matrix locus. Smoothness and local constancy give a common congruence
depth there, where the finite-place Cartan integral theorem applies.
-/

set_option autoImplicit false

open Filter IsDedekindDomain MeasureTheory NumberField Topology

namespace Robin1984.GRH

private theorem norm_le_uniformizer_pow_of_valuation_le
    {K : Type*} [Field K] [NumberField K]
    (p : HeightOneSpectrum (RingOfIntegers K)) (pi : Units (p.adicCompletion K))
    (R : Nat) (x : p.adicCompletion K)
    (hx : Valued.v x <= Valued.v pi.val ^ R) : norm x <= norm pi.val ^ R := by
  let v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)) := Valued.v
  let c := pi ^ R
  have hC : v c.val = v pi.val ^ R := v.map_pow _ _
  have hCInv : v (Inv.inv c).val * v c.val = 1 := by
    rw [<- v.map_mul, show (Inv.inv c).val * c.val = 1 from c.inv_val, v.map_one]
  have hW : v ((Inv.inv c).val * x) <= 1 := by
    rw [v.map_mul]
    have hLe : v x <= v c.val := by rw [hC]; exact hx
    exact (mul_le_mul' le_rfl hLe).trans_eq hCInv
  have hNorm : norm ((Inv.inv c).val * x) <= 1 := by
    rw [FinitePlace.norm_def]
    exact (WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal p)).mpr hW
  have he : c.val * ((Inv.inv c).val * x) = x := by
    rw [<- mul_assoc, show c.val * (Inv.inv c).val = 1 from c.val_inv, one_mul]
  calc
    norm x = norm c.val * norm ((Inv.inv c).val * x) := by rw [<- norm_mul, he]
    _ <= norm c.val := mul_le_of_le_one_right (norm_nonneg _) hNorm
    _ = _ := norm_pow _ _

/-- Every identity neighborhood contains a principal congruence subgroup of positive depth at least the prescribed lower bound. -/
theorem exists_principalCongruence_in_neighborhood
    {K : Type*} [Field K] [NumberField K] (p : HeightOneSpectrum (RingOfIntegers K))
    (n Rmin : Nat) (pi : Units (p.adicCompletion K)) (hp : norm pi.val < 1)
    (U : Set (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    (hU : Membership.mem (nhds 1) U) :
    exists R : Nat, And (0 < R) (And (Rmin <= R)
      (SetLike.coe (valuationPrincipalCongruenceSubgroup
        (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int))) n
        (Valued.v pi.val ^ R)) <= U)) := by
  let L := p.adicCompletion K
  let G := Units (Matrix (Fin n) (Fin n) L)
  let f := heckeLocalMatrixUnitEntries (I := Fin n) (F := L)
  have hEmb : IsOpenEmbedding f := isOpenEmbedding_heckeLocalMatrixUnitEntries
  have hPull : Membership.mem (Filter.comap f (nhds (f (1 : G)))) U := by
    rwa [<- hEmb.isEmbedding.isInducing.nhds_eq_comap (1 : G)]
  choose V hV hSub using Filter.mem_comap.mp hPull
  choose delta hDelta hBall using Metric.mem_nhds_iff.mp hV
  have hPow := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg pi.val) hp
  have hSmall : Filter.Eventually (fun m : Nat => norm pi.val ^ m < delta) atTop :=
    hPow.eventually (gt_mem_nhds hDelta)
  choose T hT using eventually_atTop.mp hSmall
  let R := max T Rmin + 1
  have hR : 0 < R := Nat.succ_pos _
  have hRt : T <= R := (le_max_left _ _).trans (Nat.le_succ _)
  have hRmin : Rmin <= R := (le_max_right _ _).trans (Nat.le_succ _)
  refine Exists.intro R (And.intro hR (And.intro hRmin ?_))
  intro g hg
  have hRadius : 0 <= norm pi.val ^ R := pow_nonneg (norm_nonneg _) _
  have hDist : dist (f g) (f (1 : G)) <= norm pi.val ^ R := by
    refine (dist_pi_le_iff hRadius).mpr (fun i => ?_)
    refine (dist_pi_le_iff hRadius).mpr (fun j => ?_)
    rw [dist_eq_norm]
    have hg' : Valued.v ((g.val - 1) i j) <= Valued.v pi.val ^ R := hg.2 i j
    exact norm_le_uniformizer_pow_of_valuation_le p pi R _ hg'
  exact hSub (hBall (Metric.mem_ball.mpr (hDist.trans_lt (hT R hRt))))

private theorem compactSupport_uniformizerPower_integralEntries
    {K : Type*} [Field K] [NumberField K] (p : HeightOneSpectrum (RingOfIntegers K))
    (n : Nat) (pi : Units (p.adicCompletion K)) (hp : norm pi.val < 1)
    (Phi : Matrix (Fin n) (Fin n) (p.adicCompletion K) -> Complex)
    (hPhi : HasCompactSupport Phi) :
    exists m : Nat, forall X, Membership.mem (tsupport Phi) X ->
      forall i j, Valued.v (pi.val ^ m * X i j) <= 1 := by
  let L := p.adicCompletion K
  have hEntries (i j : Fin n) : Exists (fun C : Real => forall X,
      Membership.mem (tsupport Phi) X -> norm (X i j) <= C) :=
    hPhi.exists_bound_of_continuousOn
      (f := fun X : Matrix (Fin n) (Fin n) L => X i j)
      (((continuous_apply j).comp (continuous_apply i) : Continuous
        (fun X : Matrix (Fin n) (Fin n) L => X i j)).continuousOn)
  choose C hC using hEntries
  let R (i j : Fin n) := max 1 (C i j)
  have hR (i j : Fin n) : 0 < R i j := zero_lt_one.trans_le (le_max_left _ _)
  have hPow := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg pi.val) hp
  have hSmall : Filter.Eventually (fun m : Nat => forall i j : Fin n,
      norm pi.val ^ m < 1 / R i j) atTop :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j =>
      hPow.eventually (gt_mem_nhds (div_pos zero_lt_one (hR i j)))))
  choose m hm using hSmall.exists
  refine Exists.intro m ?_
  intro X hX i j
  have hNum : norm (X i j) <= R i j := (hC i j X hX).trans (le_max_right _ _)
  have hScale := (mul_lt_mul_of_pos_right (hm i j) (hR i j)).le
  have hCancel : (1 / R i j) * R i j = 1 := by field_simp [(hR i j).ne']
  rw [hCancel] at hScale
  have hNorm : norm (pi.val ^ m * X i j) <= 1 := by
    rw [norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_left hNum (pow_nonneg (norm_nonneg _) _)).trans hScale
  rw [FinitePlace.norm_def] at hNorm
  exact (WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal p)).mp hNorm

private theorem det_scalar_uniformizer_unit
    {F : Type*} [Field F] (n m : Nat) (pi : Units F) :
    let A : Units (Matrix (Fin n) (Fin n) F) :=
      Units.map (Matrix.scalar (Fin n)).toMonoidHom (pi ^ m)
    A.val.det = pi.val ^ (m * n) := by
  intro A
  change (Matrix.scalar (Fin n) (pi ^ m).val).det = _
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Units.val_pow_eq_pow_val, pow_mul]

/-- The subspace of vectors fixed by every element of a local subgroup. -/
def heckeLocalFixedSubmodule
    {G V : Type*} [Group G] [AddCommGroup V] [Module Complex V]
    (rho : MonoidHom G (Module.End Complex V)) (H : Subgroup G) : Submodule Complex V where
  carrier := Set.ofPred (fun u => forall k : H, rho k.val u = u)
  zero_mem' := fun k => map_zero (rho k.val)
  add_mem' := by
    intro x y hx hy k
    change rho k.val (x + y) = x + y
    rw [map_add, hx k, hy k]
  smul_mem' := by
    intro c x hx k
    change rho k.val (HSMul.hSMul c x) = HSMul.hSMul c x
    rw [map_smul, hx k]

private theorem range_average_eq_fixedSubmodule
    {G V : Type*} [Group G] [AddCommGroup V] [Module Complex V]
    (rho : MonoidHom G (Module.End Complex V)) (H : Subgroup G)
    (P : HeckeLocalSubgroupAverage rho H) :
    LinearMap.range P.proj = heckeLocalFixedSubmodule rho H := by
  ext x
  change (exists v, P.proj v = x) <-> (forall k : H, rho k.val x = x)
  constructor
  . intro hx k
    choose y hy using hx
    rw [<- hy]
    exact P.fixed k y
  . intro hx
    exact Exists.intro x (P.proj_eq_of_fixed x hx)

private theorem mul_norm_cpow_lt_one_of_log_threshold
    {q M : Real} (hq0 : 0 < q) (hq1 : q < 1) (hM : 0 < M)
    (s : Complex) (hs : Real.log M / (-Real.log q) < s.re) :
    M * norm ((q : Complex) ^ s) < 1 := by
  have hNeg : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq0 hq1)
  have hL := mul_lt_mul_of_pos_right hs hNeg
  have hCancel : Real.log M / (-Real.log q) * (-Real.log q) = Real.log M := by
    field_simp [(Real.log_neg hq0 hq1).ne]
  rw [hCancel, mul_neg, mul_comm s.re (Real.log q)] at hL
  have hExp : Real.log M + Real.log q * s.re < 0 := by linarith
  have hn : norm ((q : Complex) ^ s) = Real.exp (Real.log q * s.re) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq0.ne'),
      <- Complex.ofReal_log hq0.le, Complex.norm_exp, Complex.mul_re]
    simp
  rw [hn, <- Real.exp_log hM, <- Real.exp_add]
  exact (Real.exp_lt_exp.mpr hExp).trans_eq Real.exp_zero

/-- For a locally constant compactly supported test and a smooth matrix
coefficient, finite-dimensional principal congruence fixed spaces ensure
absolute convergence of the local zeta integral on a right half-plane.
Its value is rational in the uniformizer weight. The dilation of the test
support contributes a monomial denominator factor. -/
theorem heckeLocal_compactlySupportedTest_integral_rational
    {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module Complex V]
    [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    [BorelSpace (FiniteAdeleRing (RingOfIntegers K) K)]
    (p : HeightOneSpectrum (RingOfIntegers K))
    [MeasurableSpace (p.adicCompletion K)] [BorelSpace (p.adicCompletion K)]
    (n : Nat) (pi : Units (p.adicCompletion K))
    (hPi : Valued.v (pi : p.adicCompletion K) = finiteUniformizerValue)
    (hLt : Valued.v (pi : p.adicCompletion K) < 1) (hp : norm pi.val < 1)
    [MeasurableSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    [BorelSpace (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K)))]
    (mu : Measure (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))))
    [mu.IsHaarMeasure]
    (rho : MonoidHom (Units (Matrix (Fin n) (Fin n) (p.adicCompletion K))) (Module.End Complex V))
    (ell : LinearMap (RingHom.id Complex) V Complex) (u : V)
    (Phi : Matrix (Fin n) (Fin n) (p.adicCompletion K) -> Complex)
    (hLc : IsLocallyConstant Phi) (hComp : HasCompactSupport Phi) :
    let L := p.adicCompletion K
    let G := Units (Matrix (Fin n) (Fin n) L)
    let v : Valuation L (WithZero (Multiplicative Int)) := Valued.v
    let C := valuationIntegralMatrixSubgroup v n
    let Z (s : Complex) := (norm pi.val : Complex) ^ s
    let F (s : Complex) (g : G) := (norm g.val.det : Complex) ^ s * (Phi g.val * ell (rho g u))
    (forall x : V, Filter.Eventually (fun g : G => rho g x = x) (nhds 1)) ->
    Filter.Eventually (fun g : G => forall x : V, ell (rho g x) = ell x) (nhds 1) ->
    (forall R : Nat, FiniteDimensional Complex (heckeLocalFixedSubmodule rho
      (valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R)))) ->
    mu (C : Set G) = 1 ->
    exists m : Nat, exists sigma : Real, exists N Q : Polynomial Complex,
      And (Q.eval 0 = 1)
        (forall s : Complex, sigma < s.re ->
          And (Integrable (F s) mu)
            (Z s ^ (m * n) * Q.eval (Z s) * integral mu (F s) = N.eval (Z s))) := by
  intro L G v C Z F hSmooth hSmoothEll hAdmissible hNorm
  classical
  let _ : SecondCountableTopology L := secondCountableLocalAdditiveCompletion p
  have hRow : IsOpenEmbedding (heckeLocalMatrixUnitEntries (I := Fin n) (F := L)) :=
    isOpenEmbedding_heckeLocalMatrixUnitEntries
  let _ : SecondCountableTopology G := hRow.isEmbedding.secondCountableTopology
  choose m hm using compactSupport_uniformizerPower_integralEntries p n pi hp Phi hComp
  let A : G := Units.map (Matrix.scalar (Fin n)).toMonoidHom (pi ^ m)
  let B := Inv.inv A
  have hAB : A * B = (1 : G) := by
    apply Units.ext
    exact A.val_inv
  have hBA : B * A = (1 : G) := by
    apply Units.ext
    exact A.inv_val
  let psi (X : Fin n -> Fin n -> L) := Phi (B.val * Matrix.of X)
  let ell' := ell.comp (rho B)
  have hPsi : IsLocallyConstant psi := hLc.comp_continuous
    (continuous_const.mul (continuous_matrixOf.mpr continuous_id) :
      Continuous (fun X : Fin n -> Fin n -> L => B.val * Matrix.of X))
  choose R0 hR0 using exists_uniformizer_radius_local_matrix_test p n pi hp psi hPsi
  have hConj : Continuous (fun g : G => B * g * A) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hMove : Filter.Tendsto (fun g : G => B * g * A) (nhds 1) (nhds 1) := by
    have h := hConj.tendsto (1 : G)
    simpa only [mul_one, hBA] using h
  have hEllEvent : Filter.Eventually (fun g : G => forall x : V, ell' (rho g x) = ell' x) (nhds 1) := by
    refine (hMove.eventually hSmoothEll).mono ?_
    intro g hg x
    change ell (rho B (rho g x)) = ell (rho B x)
    have hEq : B * g = (B * g * A) * B := by rw [mul_assoc (B * g) A B, hAB, mul_one]
    rw [<- Module.End.mul_apply, <- map_mul, hEq, map_mul, Module.End.mul_apply]
    exact hg (rho B x)
  let U := Set.ofPred (fun g : G => And (rho g u = u) (forall x : V, ell' (rho g x) = ell' x))
  have hU : Membership.mem (nhds 1) U := (hSmooth u).and hEllEvent
  choose R hR using exists_principalCongruence_in_neighborhood p n R0 pi hp U hU
  let H := valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R)
  have hFixU (k : H) : rho k.val u = u := (hR.2.2 k.property).1
  have hFixEll (k : H) (x : V) : ell' (rho k.val x) = ell' x := (hR.2.2 k.property).2 x
  have hOrder : Antitone (fun r : Nat => v pi.val ^ r) := by
    apply antitone_nat_of_succ_le
    intro r
    rw [pow_succ]
    exact (mul_le_mul' le_rfl hLt.le).trans_eq (mul_one _)
  have hMod (X Y : Fin n -> Fin n -> L) (hX : forall i j, v (X i j) <= 1)
      (hXY : forall i j, v (Y i j - X i j) <= v pi.val ^ R) : psi Y = psi X :=
    hR0.2 X Y hX (fun i j => (hXY i j).trans (hOrder hR.2.1))
  have hVC : IsCompact (v.integer : Set L) :=
    isCompact_iff_compactSpace.mpr (compactSpace_heckeLocalIntegers p)
  have hVal : v (pi ^ R).val = v pi.val ^ R := v.map_pow _ _
  have hH : IsCompact (H : Set G) := by
    change IsCompact (valuationPrincipalCongruenceSubgroup v n (v pi.val ^ R) : Set G)
    rw [<- hVal]
    exact isCompact_valuationPrincipalCongruenceSubgroup v n (pi ^ R) hVC
  let P := HeckeLocalSubgroupAverage.ofCompactSmooth rho H hH hSmooth
  let _ : FiniteDimensional Complex (LinearMap.range P.proj) := by
    rw [range_average_eq_fixedSubmodule rho H P]
    exact hAdmissible R
  let S := Set.ofPred (fun g : G => forall i j, v (g.val i j) <= 1)
  let Fs (s : Complex) (g : G) := (norm g.val.det : Complex) ^ s *
    (psi (fun i j => g.val i j) * ell' (rho g u))
  obtain h := heckeLocal_detWeightedIntegral_integrable_rational p n R hR.1 pi hPi hLt mu
    rho P ell' u psi hFixEll hFixU hMod hNorm
  choose M N Q ht using h
  refine Exists.intro m (Exists.intro (Real.log M / (-Real.log (norm pi.val)))
    (Exists.intro N (Exists.intro Q (And.intro ht.2.1 ?_))))
  intro s hs
  have hQ0 : 0 < norm pi.val := norm_pos_iff.mpr pi.ne_zero
  have hs0 : M * norm (Z s) < 1 :=
    mul_norm_cpow_lt_one_of_log_threshold hQ0 hp (zero_lt_one.trans_le ht.1) s hs
  have hPart : And (IntegrableOn (Fs s) S mu)
      (Q.eval (Z s) * integral (mu.restrict S) (Fs s) = N.eval (Z s)) := ht.2.2 s hs0
  have hVO : IsOpen (v.integer : Set L) := Valued.isOpen_valuationSubring L
  have hUnion : Set.iUnion (fun b : Fin n -> Nat => valuationIntegralDiagonalDoubleCoset v n
    (valuationUniformizerGapDiagonal n pi b)) = S :=
    iUnion_heckeLocal_valuationUniformizerGapDoubleCosets p n pi hPi
  have hS : MeasurableSet S := by
    rw [<- hUnion]
    exact (isOpen_iUnion (fun b => isOpen_valuationIntegralDiagonalDoubleCoset v n
      (valuationUniformizerGapDiagonal n pi b) hVO)).measurableSet
  have hSupport (x : G) (hx : Not (Membership.mem S x)) : Fs s x = 0 := by
    have hPhi : Phi (B * x).val = 0 := by
      by_contra hNZ
      have ht : Membership.mem (tsupport Phi) (B * x).val := subset_closure
        (show Membership.mem (Function.support Phi) (B * x).val from hNZ)
      apply hx
      intro i j
      have hMul : A * (B * x) = x := by rw [<- mul_assoc, hAB, one_mul]
      rw [<- hMul]
      change v ((Matrix.scalar (Fin n) (pi ^ m).val * (B * x).val) i j) <= 1
      rw [Matrix.scalar_apply, Matrix.diagonal_mul, Units.val_pow_eq_pow_val]
      exact hm _ ht i j
    have hPsi0 : psi (fun i j => x.val i j) = 0 := hPhi
    simp only [Fs, hPsi0, zero_mul, mul_zero]
  have hInd : S.indicator (Fs s) = Fs s := by
    funext x
    by_cases hx : Membership.mem S x
    . exact Set.indicator_of_mem hx _
    . rw [Set.indicator_of_notMem hx, hSupport x hx]
  have hInt : Integrable (Fs s) mu := by
    rw [<- hInd]
    exact (integrable_indicator_iff hS).mpr hPart.1
  have hEqS : integral mu (Fs s) = integral (mu.restrict S) (Fs s) := by
    exact (congrArg (integral mu) hInd).symm.trans (integral_indicator hS)
  let c : Complex := (norm B.val.det : Complex) ^ s
  have hTrans : (fun x : G => F s (B * x)) = fun x => c * Fs s x := by
    funext x
    change (norm (B * x).val.det : Complex) ^ s * (Phi (B * x).val * ell (rho (B * x) u)) = _
    rw [Units.val_mul, Matrix.det_mul, norm_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _), map_mul, Module.End.mul_apply]
    exact mul_assoc _ _ _
  have hShift : F s = fun x => c * Fs s (A * x) := by
    funext x
    have h := congrFun hTrans (A * x)
    simpa only [<- mul_assoc, hBA, one_mul] using h
  have hIntF : Integrable (F s) mu := by
    rw [hShift]
    exact ((measurePreserving_mul_left mu A).integrable_comp_of_integrable hInt).const_mul c
  refine And.intro hIntF ?_
  have hEqInt : integral mu (F s) = c * integral (mu.restrict S) (Fs s) := by
    calc
      _ = integral mu (fun x => F s (B * x)) := (integral_mul_left_eq_self (F s) B).symm
      _ = _ := by rw [hTrans, integral_const_mul, hEqS]
  have hDet : A.val.det = pi.val ^ (m * n) := det_scalar_uniformizer_unit n m pi
  have hNormPow (j : Nat) : (((norm pi.val ^ j : Real) : Complex) ^ s) = Z s ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ (norm pi.val), Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _), ih]
      exact (pow_succ (Z s) j).symm
  have hZpow : (norm A.val.det : Complex) ^ s = Z s ^ (m * n) := by
    rw [hDet, norm_pow, hNormPow]
  have hDetMul : A.val.det * B.val.det = 1 := by
    rw [<- Matrix.det_mul, show A.val * B.val = 1 from A.val_inv, Matrix.det_one]
  have hScalar : Z s ^ (m * n) * c = 1 := by
    change Z s ^ (m * n) * ((norm B.val.det : Complex) ^ s) = _
    rw [<- hZpow, <- Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
      <- Complex.ofReal_mul, <- norm_mul, hDetMul, norm_one, Complex.ofReal_one, Complex.one_cpow]
  calc
    _ = (Z s ^ (m * n) * c) * (Q.eval (Z s) * integral (mu.restrict S) (Fs s)) := by
      rw [hEqInt]
      ac_rfl
    _ = _ := by rw [hScalar, one_mul, hPart.2]

end Robin1984.GRH
