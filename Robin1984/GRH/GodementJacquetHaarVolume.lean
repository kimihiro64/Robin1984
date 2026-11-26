import Robin1984.GRH.GodementJacquetAdelicMatrixBounds

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Haar measure on adelic general linear groups and the determinant coordinates in Godement and Jacquet, Zeta Functions of Simple Algebras.
- Formalization note: Proves dyadic Haar volume bounds on the ambient adelic matrix group and on the norm-one group over a finite rectangle.
- PROVENANCE-END
-/

/-!
# Dyadic Haar volume bounds for adelic matrices

Finite residue classes and archimedean dyadic covers place the ratios of covered matrices in a fixed compact set. The finite number of translates bounds the ambient Haar volume. Logarithmic determinant coordinates then transfer the bound to the norm-one group for a fixed finite rectangle.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

/-- If a finite collection of classes covers a set and each class has
all pairwise ratios in one measurable set, left invariance bounds the
volume by the number of classes times the volume of that set. -/
theorem measure_le_card_mul_of_pairwise_ratios
    {G I : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [Fintype I]
    (mu : Measure G) [mu.IsMulLeftInvariant]
    (S C : Set G) (hC : MeasurableSet C)
    (rel : G -> I -> Prop)
    (hCover : forall g : G, Membership.mem S g -> Exists (fun i => rel g i))
    (hRatio : forall (g h : G) (i : I), Membership.mem S g -> Membership.mem S h ->
      rel g i -> rel h i -> Membership.mem C (Inv.inv g * h)) :
    mu S <= (Fintype.card I : ENNReal) * mu C := by
  let E (i : I) := Exists (fun g : G => And (Membership.mem S g) (rel g i))
  let center (i : I) : G := if hi : E i then Classical.choose hi else 1
  let U (i : I) := Set.preimage (fun g : G => Inv.inv (center i) * g) C
  have hU (i : I) : mu (U i) = mu C :=
    (measurePreserving_mul_left mu (Inv.inv (center i))).measure_preimage hC.nullMeasurableSet
  have hIncl : S <= Set.iUnion U := by
    intro g hg
    choose i hi using hCover g hg
    have hE : E i := Exists.intro g (And.intro hg hi)
    have hChoice := Classical.choose_spec hE
    have hEq : center i = Classical.choose hE := dif_pos hE
    refine Set.mem_iUnion.mpr (Exists.intro i ?_)
    change Membership.mem C (Inv.inv (center i) * g)
    rw [hEq]
    exact hRatio _ g i hChoice.1 hg hChoice.2 hi
  calc
    _ <= mu (Set.iUnion U) := measure_mono hIncl
    _ <= tsum (fun i => mu (U i)) := measure_iUnion_le U
    _ = _ := by rw [tsum_fintype]; simp_rw [hU, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem norm_inverseMul_entry_le
    {F : Type*} [NormedField F] (n : Nat)
    (g h : Matrix.GeneralLinearGroup (Fin n) F) (L rho : Real)
    (hInv : forall i j : Fin n, norm (g.inv i j) <= L)
    (hClose : forall i j : Fin n, norm (h.val i j - g.val i j) <= rho)
    (i j : Fin n) :
    norm ((Inv.inv g * h).val i j) <= 1 + (n : Real) * (L * rho) := by
  have hEq : (Inv.inv g * h).val = 1 + g.inv * (h.val - g.val) := by
    change g.inv * h.val = _
    rw [mul_sub, g.inv_val]
    abel
  have hOne : norm ((1 : Matrix (Fin n) (Fin n) F) i j) <= 1 := by
    by_cases hI : i = j <;> simp [Matrix.one_apply, hI]
  have hProd : norm ((g.inv * (h.val - g.val)) i j) <= (n : Real) * (L * rho) := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ <= Finset.sum Finset.univ (fun _ : Fin n => L * rho) := by
        apply Finset.sum_le_sum
        intro k hk
        change norm (g.inv i k * (h.val k j - g.val k j)) <= L * rho
        rw [norm_mul]
        exact mul_le_mul (hInv i k) (hClose k j) (norm_nonneg _) ((norm_nonneg _).trans (hInv i k))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hEq, Matrix.add_apply]
  exact (norm_add_le _ _).trans (add_le_add hOne hProd)

private abbrev volumeFiniteMatrixProjection (K : Type*) [Field K] [NumberField K] (n : Nat) :
    MonoidHom (AdelicGeneralLinearGroup K n)
      (Matrix.GeneralLinearGroup (Fin n) (FiniteAdeleRing (RingOfIntegers K) K)) :=
  Matrix.GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (RingOfIntegers K) K))

/-- Two adelic matrices with nearby archimedean entries and the same
integral finite coset have their ratio in the fixed compact matrix part
when their archimedean inverse entries are bounded. -/
theorem mem_godementJacquetBoundedIntegralMatrixUnits_inv_mul
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (g h : AdelicGeneralLinearGroup K n) (L rho : Real)
    (hG : forall (w : InfinitePlace K) (i j : Fin n), norm ((g.inv i j).1 w) <= L)
    (hH : forall (w : InfinitePlace K) (i j : Fin n), norm ((h.inv i j).1 w) <= L)
    (hClose : forall (w : InfinitePlace K) (i j : Fin n),
      norm ((h.val i j).1 w - (g.val i j).1 w) <= rho)
    (hF : Membership.mem (integralFiniteAdeleMatrixGroup K n)
      (Inv.inv (volumeFiniteMatrixProjection K n g) * volumeFiniteMatrixProjection K n h)) :
    Membership.mem (godementJacquetBoundedIntegralMatrixUnits K n (1 + (n : Real) * (L * rho)))
      (Inv.inv g * h) := by
  let A := AdeleRing (RingOfIntegers K) K
  let I := InfiniteAdeleRing K
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let E (w : InfinitePlace K) : RingHom A w.Completion :=
    (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp (RingHom.fst I F)
  let P (w : InfinitePlace K) :
      MonoidHom (AdelicGeneralLinearGroup K n) (Matrix.GeneralLinearGroup (Fin n) w.Completion) :=
    Matrix.GeneralLinearGroup.map (E w)
  have hClose' (w : InfinitePlace K) (i j : Fin n) :
      norm ((g.val i j).1 w - (h.val i j).1 w) <= rho := by
    rw [<- neg_sub, norm_neg]
    exact hClose w i j
  have hArch (i j : Fin n) (w : InfinitePlace K) :
      norm (((Inv.inv g * h).val i j).1 w) <= 1 + (n : Real) * (L * rho) := by
    have hb := norm_inverseMul_entry_le n (P w g) (P w h) L rho (hG w) (hClose w) i j
    change norm (((P w) (Inv.inv g * h)).val i j) <= _
    rw [map_mul, map_inv]
    exact hb
  have hInvArch (i j : Fin n) (w : InfinitePlace K) :
      norm (((Inv.inv g * h).inv i j).1 w) <= 1 + (n : Real) * (L * rho) := by
    have hb := norm_inverseMul_entry_le n (P w h) (P w g) L rho (hH w) (hClose' w) i j
    change norm (((P w) (Inv.inv h * g)).val i j) <= _
    rw [map_mul, map_inv]
    exact hb
  let q := volumeFiniteMatrixProjection K n
  have hFin : Membership.mem (integralFiniteAdeleMatrixGroup K n) (q (Inv.inv g * h)) := by
    rw [map_mul, map_inv]
    exact hF
  exact And.intro
    (fun i j => And.intro (hArch i j) (fun p => hFin.1 i j p))
    (fun i j => And.intro (hInvArch i j) (fun p => hFin.2 i j p))

private abbrev VolumeArchSpace (K : Type*) [Field K] (n : Nat) :=
  PiLp 2 (fun _ : Prod (Fin n) (Fin n) => DedekindZeta.Theta.minkowskiSpace K)

/-- The archimedean matrix written in Minkowski coordinates. -/
def godementJacquetArchMatrixVector
    (K : Type*) [Field K] [NumberField K] (n : Nat) (g : AdelicGeneralLinearGroup K n) :
    VolumeArchSpace K n :=
  heckeAdeleMinkowskiVector K (Prod (Fin n) (Fin n)) g.val.vec

private theorem norm_archEntry_sub_le_norm_archMatrixVector_sub
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (g h : AdelicGeneralLinearGroup K n) (w : InfinitePlace K) (i j : Fin n) :
    norm ((h.val i j).1 w - (g.val i j).1 w) <=
      norm (godementJacquetArchMatrixVector K n h - godementJacquetArchMatrixVector K n g) := by
  let I := Prod (Fin n) (Fin n)
  let V := godementJacquetArchMatrixVector K n
  let e := heckeAdeleMixedCoordinate K
  let T := DedekindZeta.Theta.toMinkowski K
  let z (a : I) := h.val.vec a - g.val.vec a
  let Z := heckeAdeleMinkowskiVector K I z
  have hZ : V h - V g = Z := by
    apply (PiLp.continuousLinearEquiv 2 Real (fun _ : I => DedekindZeta.Theta.minkowskiSpace K)).injective
    funext a
    change T (e (h.val.vec a)) - T (e (g.val.vec a)) = T (e (h.val.vec a - g.val.vec a))
    rw [map_sub, map_sub]
  rw [hZ]
  have hLocal := norm_infiniteAdele_apply_le_minkowski K ((h.val i j).1 - (g.val i j).1) w
  exact hLocal.trans (PiLp.norm_apply_le Z (Prod.mk j i))

private theorem norm_archEntry_sub_le_of_commonArchBall
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (g h : AdelicGeneralLinearGroup K n) (R eta : Real) (hR : 0 < R)
    (center : VolumeArchSpace K n)
    (hG : norm (HSMul.hSMul (Inv.inv R) (godementJacquetArchMatrixVector K n g) - center) <= eta)
    (hH : norm (HSMul.hSMul (Inv.inv R) (godementJacquetArchMatrixVector K n h) - center) <= eta)
    (w : InfinitePlace K) (i j : Fin n) :
    norm ((h.val i j).1 w - (g.val i j).1 w) <= R * (eta + eta) := by
  let V := godementJacquetArchMatrixVector K n
  let W (u : AdelicGeneralLinearGroup K n) := HSMul.hSMul (Inv.inv R) (V u)
  have hSub : HSMul.hSMul R (W h - W g) = V h - V g := by
    dsimp only [W]
    rw [<- smul_sub, smul_smul]
    have hOne : R * Inv.inv R = 1 := by field_simp [ne_of_gt hR]
    rw [hOne, one_smul]
  have hClose : norm (W h - W g) <= eta + eta := by
    have he : W h - W g = (W h - center) - (W g - center) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hH hG)
  calc
    _ <= norm (V h - V g) := norm_archEntry_sub_le_norm_archMatrixVector_sub K n g h w i j
    _ = R * norm (W h - W g) := by rw [<- hSub, norm_smul, Real.norm_of_nonneg hR.le]
    _ <= _ := mul_le_mul_of_nonneg_left hClose hR.le

/-- The ambient ball has total determinant norm at least one, bounded
archimedean matrix radius, and a fixed bound on every finite entry. -/
def godementJacquetAdelicMatrixBall
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (u : Units (FiniteAdeleRing (RingOfIntegers K) K)) (R : Real) :
    Set (AdelicGeneralLinearGroup K n) :=
  Set.ofPred (fun g =>
    And (1 <= adelicDeterminantNorm K n g)
      (And (norm (godementJacquetArchMatrixVector K n g) <= R)
        (forall (p : HeightOneSpectrum (RingOfIntegers K)) (i j : Fin n),
          norm ((g.val i j).2 p) <= norm (u.val p))))

/-- On the fixed finite support the adelic matrix ball has at most
geometric Haar growth along dyadic radii. -/
theorem exists_godementJacquetAdelicMatrixBall_dyadicHaarBound
    (K : Type*) [Field K] [NumberField K] (m : Nat)
    (u : Units (FiniteAdeleRing (RingOfIntegers K) K))
    [T2Space (AdelicGeneralLinearGroup K (m + 1))]
    [MeasurableSpace (AdelicGeneralLinearGroup K (m + 1))]
    [BorelSpace (AdelicGeneralLinearGroup K (m + 1))]
    [MeasurableMul (AdelicGeneralLinearGroup K (m + 1))]
    (mu : Measure (AdelicGeneralLinearGroup K (m + 1))) [mu.IsHaarMeasure] :
    Exists (fun B : Real => Exists (fun q : Real => And (0 <= B) (And (0 <= q)
      (forall k : Nat, mu (godementJacquetAdelicMatrixBall K (m + 1) u ((2 : Real) ^ (k + 1))) <=
        ENNReal.ofReal (B * q ^ k))))) := by
  let n := m + 1
  let G := AdelicGeneralLinearGroup K n
  let X := VolumeArchSpace K n
  let D := Finset.sum Finset.univ (fun v : InfinitePlace K => v.mult)
  let f := n * D
  let b := f + m
  let d := Module.finrank Int (RingOfIntegers K) * n * n
  let C := heckeFiniteIdeleNorm u ^ n
  let J := (Nat.factorial n : Real) ^ D
  let Cinv := (1 + C * J) * (Nat.factorial m : Real)
  let Part := godementJacquetBoundedIntegralMatrixUnits K n (1 + (n : Real) * (2 * Cinv))
  have hPart := isCompact_godementJacquetBoundedIntegralMatrixUnits K n (1 + (n : Real) * (2 * Cinv))
  have hPartMeas : MeasurableSet Part := hPart.isClosed.measurableSet
  let W := (mu Part).toReal
  have hW : ENNReal.ofReal W = mu Part := ENNReal.ofReal_toReal hPart.measure_lt_top.ne
  choose A0 hA0 using exists_nat_ge (C * J)
  choose P hP using (exists_unitBall_dyadicCover (E := X))
  let Q := P ^ (b + 1) * ((2 : Nat) ^ f) ^ (d + 1)
  let A := (A0 : Real) ^ (d + 1) * (Q : Real) * W
  have hA : 0 <= A :=
    mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) ENNReal.toReal_nonneg
  refine Exists.intro A (Exists.intro (Q : Real) (And.intro hA (And.intro (Nat.cast_nonneg _) ?_)))
  intro k
  let R := (2 : Real) ^ (k + 1)
  let S := godementJacquetAdelicMatrixBall K n u R
  let M := A0 * ((2 : Nat) ^ f) ^ (k + 1)
  let j := (b + 1) * (k + 1)
  let eta := (1 / 2 : Real) ^ j
  let rho := R * (eta + eta)
  let L := Cinv * R ^ b
  let Ia := Fin j -> Fin P
  let If := Prod (Fin M) (Fin (M ^ d))
  let Ig := Prod Ia If
  let Vf := godementJacquetScaledFiniteComponent K n u
  let V := godementJacquetArchMatrixVector K n
  let H := integralFiniteAdeleMatrixGroup K n
  have hR : 0 < R := by dsimp only [R]; positivity
  have hR1 : 1 <= R := by
    calc
      1 = (1 : Real) ^ (k + 1) := (one_pow _).symm
      _ <= _ := by
        have h2 : (1 : Real) <= 2 := by norm_num
        change (1 : Real) ^ (k + 1) <= (2 : Real) ^ (k + 1)
        gcongr
  have hC : 0 < C := pow_pos (heckeFiniteIdeleNorm_pos u) _
  have hRC : R * Inv.inv R = 1 := by field_simp [ne_of_gt hR]
  have hScaleMesh : L * rho = 2 * Cinv := by
    have he : (2 : Real) ^ j = R ^ (b + 1) := by
      dsimp only [j, R]
      rw [Nat.mul_comm, pow_mul]
    have he' : eta = Inv.inv (R ^ (b + 1)) := by
      dsimp only [eta]
      rw [one_div, inv_pow, he]
    calc
      _ = 2 * Cinv * (R ^ (b + 1) * eta) := by dsimp only [L, rho]; rw [pow_succ]; ring
      _ = _ := by rw [he']; field_simp [ne_of_gt hR]
  choose centerA hCenterA using hP j
  choose centerF hCenterF using exists_finiteAdeleMatrixDenominatorSet_cosetCover_le K n M
  let rel (g : G) (i : Ig) : Prop :=
    And (norm (HSMul.hSMul (Inv.inv R) (V g) - centerA i.1) <= eta)
      (Membership.mem H (Inv.inv (centerF i.2) * Vf g))
  have hGrowth (g : G) (hg : Membership.mem S g) :=
    exists_scaledFiniteInverseDenominator_le_archNorm K n u g R hg.2.2 hg.2.1 hg.1
  have hInv (g : G) (hg : Membership.mem S g) (w : InfinitePlace K) (i j : Fin n) :
      norm ((g.inv i j).1 w) <= L := by
    choose N hN using hGrowth g hg
    have h := norm_godementJacquet_adelicInverse_archEntry_le K m g R (Inv.inv C) hR1
      (inv_pos.mpr hC) hg.2.1 hN.2.2.2 w i j
    simpa only [inv_inv, L, Cinv, J, b, f] using h
  have hCover (g : G) (hg : Membership.mem S g) : Exists (fun i => rel g i) := by
    have hArch : norm (HSMul.hSMul (Inv.inv R) (V g)) <= 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
      calc
        _ <= Inv.inv R * R := mul_le_mul_of_nonneg_left hg.2.1 (inv_nonneg.mpr hR.le)
        _ = _ := (mul_comm _ _).trans hRC
    choose a ha using hCenterA _ hArch
    choose N hN using hGrowth g hg
    have hNreal : (N : Real) <= (M : Real) := by
      have h0 := hN.2.2.1
      rw [mul_pow, <- pow_mul] at h0
      calc
        _ <= (C * J) * R ^ f := by simpa only [mul_assoc, J, f] using h0
        _ <= (A0 : Real) * R ^ f := mul_le_mul_of_nonneg_right hA0 (pow_nonneg hR.le _)
        _ = _ := by
          dsimp only [M, R]
          norm_cast
          rw [<- pow_mul, <- pow_mul, Nat.mul_comm (k + 1) f]
    have hNM : N <= M := by exact_mod_cast hNreal
    choose i hi using hCenterF N hN.1 hNM _ hN.2.1
    exact Exists.intro (Prod.mk a i) (And.intro ha hi)
  have hRatio (g h : G) (z : Ig) (hg : Membership.mem S g) (hh : Membership.mem S h)
      (hG : rel g z) (hH : rel h z) : Membership.mem Part (Inv.inv g * h) := by
    let pf := volumeFiniteMatrixProjection K n
    have hFin : Membership.mem H (Inv.inv (pf g) * pf h) := by
      have hf := H.mul_mem (H.inv_mem hG.2) hH.2
      have he : Inv.inv (Inv.inv (centerF z.2) * Vf g) * (Inv.inv (centerF z.2) * Vf h) =
          Inv.inv (pf g) * pf h := by
        simp [Vf, pf, godementJacquetScaledFiniteComponent, volumeFiniteMatrixProjection, mul_assoc]
        rfl
      rwa [he] at hf
    have hP := mem_godementJacquetBoundedIntegralMatrixUnits_inv_mul K n g h L rho
      (hInv g hg) (hInv h hh)
      (norm_archEntry_sub_le_of_commonArchBall K n g h R eta hR (centerA z.1) hG.1 hH.1) hFin
    rw [hScaleMesh] at hP
    exact hP
  have hCard : Fintype.card Ig = A0 ^ (d + 1) * Q ^ (k + 1) := by
    dsimp only [Ig, Ia, If]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    rw [<- pow_succ', show P ^ j = (P ^ (b + 1)) ^ (k + 1) from pow_mul _ _ _]
    have hm : M ^ (d + 1) = A0 ^ (d + 1) * (((2 : Nat) ^ f) ^ (d + 1)) ^ (k + 1) := by
      dsimp only [M]
      rw [mul_pow, <- pow_mul, Nat.mul_comm (k + 1) (d + 1), pow_mul]
    rw [hm]
    dsimp only [Q]
    rw [mul_pow]
    ac_rfl
  calc
    mu S <= (Fintype.card Ig : ENNReal) * mu Part :=
      measure_le_card_mul_of_pairwise_ratios mu S Part hPartMeas rel hCover hRatio
    _ = ENNReal.ofReal ((Fintype.card Ig : Real) * W) := by
      rw [<- hW, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = _ := by
      congr 1
      rw [hCard, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
      dsimp only [A]
      rw [pow_succ]
      ring

private abbrev VolumeNormOne (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker

/-- The norm-one matrices in the chosen finite rectangle with bounded
archimedean radius. -/
def godementJacquetNormOneThetaBall
    (K : Type*) [Field K] [NumberField K] (n : Nat)
    (a : Prod (Fin n) (Fin n) -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (R : Real) : Set (VolumeNormOne K n) :=
  Set.ofPred (fun g =>
    And (norm (godementJacquetArchMatrixVector K n g.val) <= R)
      (Membership.mem (finiteAdelePrincipalRectangle K (Prod (Fin n) (Fin n)) a
        (algebraMap (RingOfIntegers K) K d)) (fun i => (g.val.val.vec i).2)))

/-- Thickening a norm-one ball through one unit of logarithmic determinant
time transfers the dyadic ambient Haar bound to the norm-one group. -/
theorem exists_godementJacquetNormOneThetaBall_dyadicHaarBound
    (K : Type*) [Field K] [NumberField K] (m : Nat)
    [T2Space (AdelicGeneralLinearGroup K (m + 1))]
    [MeasurableSpace (AdelicGeneralLinearGroup K (m + 1))]
    [BorelSpace (AdelicGeneralLinearGroup K (m + 1))]
    [MeasurableMul (AdelicGeneralLinearGroup K (m + 1))]
    [MeasurableSpace (VolumeNormOne K (m + 1))] [BorelSpace (VolumeNormOne K (m + 1))]
    (mu : Measure (VolumeNormOne K (m + 1))) [mu.IsHaarMeasure] [SFinite mu]
    (a : Prod (Fin (m + 1)) (Fin (m + 1)) -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) :
    Exists (fun B : Real => Exists (fun q : Real => And (0 <= B) (And (0 <= q)
      (forall k : Nat, mu (godementJacquetNormOneThetaBall K (m + 1) a d ((2 : Real) ^ (k + 1))) <=
        ENNReal.ofReal (B * q ^ k))))) := by
  let n := m + 1
  let G := VolumeNormOne K n
  let I := Prod (Fin n) (Fin n)
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let T := finiteAdelePrincipalRectangle K I a (algebraMap (RingOfIntegers K) K d)
  let E := Set.iUnion (fun i : I => Set.image (fun z : I -> F => z i) T)
  have hE : IsCompact E := isCompact_iUnion (fun i : I =>
    (isCompact_finiteAdelePrincipalRectangle K I a (algebraMap (RingOfIntegers K) K d)).image
      (continuous_apply i))
  choose u hu using exists_finiteIdele_dominating_compact K E hE
  have hn : 0 < n := Nat.zero_lt_succ _
  let muA := adelicDeterminantProductMeasure K n hn mu
  let _ : muA.IsHaarMeasure := isHaarMeasure_adelicDeterminantProductMeasure K n hn mu
  choose B q hB using exists_godementJacquetAdelicMatrixBall_dyadicHaarBound K m u muA
  let C := Real.exp (((1 : Real) / (n : Real)) / (Module.finrank Rat K : Real))
  choose j hj using pow_unbounded_of_one_lt C (by norm_num : (1 : Real) < 2)
  refine Exists.intro (B * q ^ j) (Exists.intro q
    (And.intro (mul_nonneg hB.1 (pow_nonneg hB.2.1 _)) (And.intro hB.2.1 ?_)))
  intro k
  let R := (2 : Real) ^ (k + 1)
  let R' := (2 : Real) ^ (k + j + 1)
  let S := godementJacquetNormOneThetaBall K n a d R
  let U := godementJacquetAdelicMatrixBall K n u R'
  let e := adelicDeterminantHomeomorph K n hn
  have hR : 0 <= R := by dsimp only [R]; positivity
  have hScale : C * R <= R' := by
    calc
      _ <= (2 : Real) ^ j * R := mul_le_mul_of_nonneg_right hj.le hR
      _ = _ := by dsimp only [R, R']; rw [<- pow_add]; congr 1; omega
  have hIncl : (Set.Icc (0 : Real) 1).prod S <= Set.preimage e U := by
    intro x hx
    let t := x.1
    let p := x.2
    let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
    have ht0 : 0 <= t := hx.1.1
    have ht1 : t <= 1 := hx.1.2
    change Membership.mem U (z * p.val)
    have hD : 1 <= adelicDeterminantNorm K n (z * p.val) := by
      have h := adelicDeterminantNorm_coordinates K n hn (Multiplicative.ofAdd t) p
      change adelicDeterminantNorm K n (z * p.val) = Real.exp t at h
      rw [h]
      exact Real.one_le_exp_iff.mpr ht0
    have ha : norm (godementJacquetArchMatrixVector K n (z * p.val)) <= R' := by
      unfold godementJacquetArchMatrixVector
      rw [heckeAdeleMinkowskiVector_adelicDeterminantSection_mul K n t p.val, norm_smul,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      have hC : Real.exp ((t / (n : Real)) / (Module.finrank Rat K : Real)) <= C :=
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right ht1 (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      exact (mul_le_mul hC hx.2.1 (norm_nonneg _) (Real.exp_pos _).le).trans hScale
    have hz : volumeFiniteMatrixProjection K n z = 1 := adelicDeterminantSection_map_finite K n t
    have hF : volumeFiniteMatrixProjection K n (z * p.val) = volumeFiniteMatrixProjection K n p.val := by
      rw [map_mul, hz, one_mul]
    refine And.intro hD (And.intro ha (fun q i j => ?_))
    have hv : Membership.mem T (fun l : I => (p.val.val.vec l).2) := hx.2.2
    have hi : Membership.mem E ((p.val.val i j).2) :=
      Set.mem_iUnion.mpr (Exists.intro (Prod.mk j i) (Exists.intro _ (And.intro hv rfl)))
    have hEq : ((z * p.val).val i j).2 = (p.val.val i j).2 :=
      congrArg (fun M : Matrix.GeneralLinearGroup (Fin n) F => M.val i j) hF
    rw [hEq]
    exact hu _ hi q
  have hm : mu S <= muA U := by
    have hUnit : (volume : Measure Real) (Set.Icc (0 : Real) 1) = 1 := by
      rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
    calc
      _ = ((volume : Measure Real).prod mu) ((Set.Icc (0 : Real) 1).prod S) := by
        have hp : ((volume : Measure Real).prod mu) ((Set.Icc (0 : Real) 1).prod S) =
            (volume : Measure Real) (Set.Icc (0 : Real) 1) * mu S :=
          Measure.prod_prod _ _
        rw [hp, hUnit, one_mul]
      _ <= ((volume : Measure Real).prod mu) (Set.preimage e U) := measure_mono hIncl
      _ = _ := (e.measurableEmbedding.map_apply ((volume : Measure Real).prod mu) U).symm
  refine hm.trans ?_
  have h := hB.2.2 (k + j)
  refine h.trans_eq ?_
  congr 1
  rw [pow_add]
  ring

end Robin1984.GRH
