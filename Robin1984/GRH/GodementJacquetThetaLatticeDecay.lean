import Robin1984.GRH.GodementJacquetThetaDecay
import Robin1984.GRH.GodementJacquetThetaMellin

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and inverse-power sums over shifted Euclidean lattices.
- Formalization note: Bounds the positive-time invertible theta curve using the time-zero lattice weight and proves summability of that weight at each pair of quotient representatives.
- PROVENANCE-END
-/

/-!
# A time-zero lattice bound for the invertible theta integral

The finite support is unchanged by positive determinant time and the
archimedean norm is nondecreasing. The inverse-power sum on the time-zero
finite support is summable at each pair of representatives when its
exponent exceeds the real dimension. Integrability of the weighted sum
against the two quotient functions gives arbitrary positive-time decay.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

private abbrev ThetaAdeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K
private abbrev DecayNormGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker
private abbrev DecayIndex (n : Nat) := Prod (Fin n) (Fin n)
private abbrev DecayArch (K : Type*) [Field K] (n : Nat) :=
  PiLp 2 (fun _ : DecayIndex n => DedekindZeta.Theta.minkowskiSpace K)

/-- The inverse archimedean power on the support of the test. -/
def godementJacquetInvertibleThetaArchWeight
    (K : Type*) [Field K] [NumberField K] (n m : Nat)
    (Phi : Matrix (Fin n) (Fin n) (ThetaAdeles K) -> Complex)
    (t : Real) (A B : DecayNormGroup K n) (P : Matrix.GeneralLinearGroup (Fin n) K) : Real :=
  let X := Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t) *
    adelicPrincipalGeneralLinear K n P * B.val
  if Phi X.val = 0 then 0 else
    Inv.inv (max 1 (norm (heckeAdeleMinkowskiVector K (DecayIndex n) X.val.vec)) ^ m)

/-- The summable factor in the pointwise weighted theta bound can be
taken to be the inverse archimedean power on the support. -/
theorem exists_godementJacquetMatrixRectangle_le_archWeight
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    (a : DecayIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (f : SchwartzMap (DecayArch K n) Complex)
    (m : Nat) (b : Real) :
    Exists (fun C : Real => And (0 <= C)
      (forall t : Real, 0 <= t ->
        forall (A B : DecayNormGroup K n) (P : Matrix.GeneralLinearGroup (Fin n) K),
          let Phi := godementJacquetMatrixRectangle K a d f
          norm (godementJacquetDoubleThetaTerm K n Phi t A B P.val) <=
            C * Real.exp (-(b * t)) * godementJacquetInvertibleThetaArchWeight K n m Phi t A B P)) := by
  choose C0 h0 using exists_godementJacquetMatrixRectangle_weightedDecay K n hn a d f 0 b
  choose Cm hm using exists_godementJacquetMatrixRectangle_weightedDecay K n hn a d f m b
  let C := max C0 Cm
  have hC : 0 <= C := h0.1.trans (le_max_left _ _)
  refine Exists.intro C (And.intro hC ?_)
  intro t ht A B P
  let Phi := godementJacquetMatrixRectangle K a d f
  let X := Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t) *
    adelicPrincipalGeneralLinear K n P * B.val
  let r := norm (heckeAdeleMinkowskiVector K (DecayIndex n) X.val.vec)
  let R := max 1 r
  change norm (Phi X.val) <= C * Real.exp (-(b * t)) *
    (if Phi X.val = 0 then 0 else Inv.inv (R ^ m))
  by_cases hz : Phi X.val = 0
  . simp [hz]
  rw [if_neg hz]
  have hWeighted : norm (Phi X.val) * R ^ m * Real.exp (b * t) <= C := by
    by_cases hr : r <= 1
    . change norm (Phi X.val) * (max 1 r) ^ m * Real.exp (b * t) <= C
      rw [max_eq_left hr, one_pow, mul_one]
      simpa only [pow_zero, mul_one] using (h0.2 t ht A B P).trans (le_max_left C0 Cm)
    . change norm (Phi X.val) * (max 1 r) ^ m * Real.exp (b * t) <= C
      rw [max_eq_right (le_of_not_ge hr)]
      exact (hm.2 t ht A B P).trans (le_max_right C0 Cm)
  have hR : 0 < R ^ m := pow_pos (zero_lt_one.trans_le (le_max_left 1 r)) _
  have hInv : R ^ m * Inv.inv (R ^ m) = 1 := by
    field_simp [hR.ne']
  have hExp : Real.exp (b * t) * Real.exp (-(b * t)) = 1 := by
    rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    norm (Phi X.val) =
        (norm (Phi X.val) * R ^ m * Real.exp (b * t)) *
          (Inv.inv (R ^ m) * Real.exp (-(b * t))) := by
      calc
        _ = norm (Phi X.val) * ((R ^ m * Inv.inv (R ^ m)) *
            (Real.exp (b * t) * Real.exp (-(b * t)))) := by rw [hInv, hExp, mul_one, mul_one]
        _ = _ := by ring
    _ <= C * (Inv.inv (R ^ m) * Real.exp (-(b * t))) :=
      mul_le_mul_of_nonneg_right hWeighted (mul_nonneg (inv_nonneg.mpr hR.le) (Real.exp_nonneg _))
    _ = _ := by ring

/-- A time-uniform integrable majorant of the lattice power sum gives the
positive-time estimate for the integrated invertible theta curve. -/
theorem exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_archWeight
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (DecayNormGroup K n)] (nu : Measure (DecayNormGroup K n))
    (a : DecayIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (f : SchwartzMap (DecayArch K n) Complex)
    (c g : DecayNormGroup K n -> Complex) (m : Nat)
    (H : Prod (DecayNormGroup K n) (DecayNormGroup K n) -> Real)
    (hI : Integrable (fun p => H p * norm (c p.1 * g p.2)) (nu.prod nu))
    (hW : forall t : Real, 0 <= t ->
      Filter.Eventually (fun p : Prod (DecayNormGroup K n) (DecayNormGroup K n) =>
        let w := godementJacquetInvertibleThetaArchWeight K n m
          (godementJacquetMatrixRectangle K a d f) t p.1 p.2
        And (Summable w) (tsum w <= H p)) (ae (nu.prod nu)))
    (b : Real) :
    Exists (fun M : Real => forall t : Real, 0 <= t ->
      norm (godementJacquetInvertibleDoubleThetaIntegral K n nu
        (godementJacquetMatrixRectangle K a d f) c g t) <= M * Real.exp (-(b * t))) := by
  let Phi := godementJacquetMatrixRectangle K a d f
  choose C hC using exists_godementJacquetMatrixRectangle_le_archWeight K n hn a d f m b
  let h (p : Prod (DecayNormGroup K n) (DecayNormGroup K n)) := H p * norm (c p.1 * g p.2)
  refine Exists.intro (C * integral (nu.prod nu) h) ?_
  intro t ht
  let L := C * Real.exp (-(b * t))
  have hL : 0 <= L := mul_nonneg hC.1 (Real.exp_nonneg _)
  have hBound : Filter.Eventually
      (fun p : Prod (DecayNormGroup K n) (DecayNormGroup K n) =>
        norm (godementJacquetInvertibleDoubleThetaSeries K n Phi t p.1 p.2 * (c p.1 * g p.2)) <= L * h p)
      (ae (nu.prod nu)) := by
    filter_upwards [hW t ht] with p hp
    let w := godementJacquetInvertibleThetaArchWeight K n m Phi t p.1 p.2
    let z (P : Matrix.GeneralLinearGroup (Fin n) K) :=
      godementJacquetDoubleThetaTerm K n Phi t p.1 p.2 P.val
    have hPoint (P : Matrix.GeneralLinearGroup (Fin n) K) : norm (z P) <= L * w P :=
      hC.2 t ht p.1 p.2 P
    have hw : Summable (fun P => L * w P) := hp.1.mul_left L
    have hz : Summable (fun P => norm (z P)) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hPoint hw
    have hSeries : norm (tsum z) <= L * H p := by
      calc
        _ <= tsum (fun P => norm (z P)) := norm_tsum_le_tsum_norm hz
        _ <= tsum (fun P => L * w P) := hz.tsum_le_tsum hPoint hw
        _ = L * tsum w := tsum_mul_left
        _ <= L * H p := mul_le_mul_of_nonneg_left hp.2 hL
    change norm (tsum z * (c p.1 * g p.2)) <= L * (H p * norm (c p.1 * g p.2))
    rw [norm_mul, <- mul_assoc]
    exact mul_le_mul_of_nonneg_right hSeries (norm_nonneg _)
  calc
    _ <= integral (nu.prod nu) (fun p => L * h p) :=
      norm_integral_le_of_norm_le (hI.const_mul L) hBound
    _ = L * integral (nu.prod nu) h := integral_const_mul _ _
    _ = _ := by dsimp [L]; ring

/-- The time-zero inverse power of the archimedean norm, restricted to
the finite support rectangle, is an envelope for every positive time. -/
def godementJacquetInvertibleThetaTimeZeroWeight
    (K : Type*) [Field K] [NumberField K] (n m : Nat)
    (a : DecayIndex n -> FiniteAdeleRing (RingOfIntegers K) K) (d : RingOfIntegers K)
    (A B : DecayNormGroup K n) (P : Matrix.GeneralLinearGroup (Fin n) K) : Real :=
  let Y := Inv.inv A.val * adelicPrincipalGeneralLinear K n P * B.val
  let R := finiteAdelePrincipalRectangle K (DecayIndex n) a (algebraMap (RingOfIntegers K) K d)
  if Membership.mem R (fun i => (Y.val.vec i).2) then
    Inv.inv (max 1 (norm (heckeAdeleMinkowskiVector K (DecayIndex n) Y.val.vec)) ^ m)
  else 0

/-- The bound on the rational lattice weights is independent of the
positive logarithmic determinant parameter and of the Schwartz factor. -/
theorem godementJacquetInvertibleThetaArchWeight_le_timeZeroWeight
    (K : Type*) [Field K] [NumberField K] (n m : Nat)
    (a : DecayIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (f : SchwartzMap (DecayArch K n) Complex)
    (t : Real) (ht : 0 <= t) (A B : DecayNormGroup K n) (P : Matrix.GeneralLinearGroup (Fin n) K) :
    godementJacquetInvertibleThetaArchWeight K n m
        (godementJacquetMatrixRectangle K a d f) t A B P <=
      godementJacquetInvertibleThetaTimeZeroWeight K n m a d A B P := by
  let I := DecayIndex n
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let R := finiteAdelePrincipalRectangle K I a (algebraMap (RingOfIntegers K) K d)
  let Phi := godementJacquetMatrixRectangle K a d f
  let X := Inv.inv A.val * adelicDeterminantSection K n (Multiplicative.ofAdd t) *
    adelicPrincipalGeneralLinear K n P * B.val
  let Y := Inv.inv A.val * adelicPrincipalGeneralLinear K n P * B.val
  let r (U : AdelicGeneralLinearGroup K n) := norm (heckeAdeleMinkowskiVector K I U.val.vec)
  let h (U : AdelicGeneralLinearGroup K n) : I -> F := fun i => (U.val.vec i).2
  change (if Phi X.val = 0 then 0 else Inv.inv (max 1 (r X) ^ m)) <=
    (if Membership.mem R (h Y) then Inv.inv (max 1 (r Y) ^ m) else 0)
  by_cases hz : Phi X.val = 0
  . rw [if_pos hz]
    split
    . exact inv_nonneg.mpr (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
    . exact le_rfl
  have hX : Membership.mem R (h X) := by
    apply (mem_finiteAdelePrincipalRectangle_iff K I a (h X) (algebraMap (RingOfIntegers K) K d)).mpr
    intro i
    by_contra hi
    apply hz
    let C (j : I) := heckeFiniteAdelePrincipalCoset (a j) (algebraMap (RingOfIntegers K) K d)
    let z (j : I) := (C j).indicator (fun _ => (1 : Complex)) (h X j)
    change f (heckeAdeleMinkowskiVector K I X.val.vec) * Finset.prod Finset.univ z = 0
    have hi0 : z i = 0 := Set.indicator_of_notMem hi _
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi0, mul_zero]
  have hXY : h X = h Y :=
    congrArg (fun M : Matrix.GeneralLinearGroup (Fin n) F => M.val.vec)
      (godementJacquetThetaArgument_map_finite K n t A B P)
  have hY : Membership.mem R (h Y) :=
    Eq.mp (congrArg (fun v : I -> F => Membership.mem R v) hXY) hX
  rw [if_neg hz, if_pos hY]
  have hNorm : r Y <= r X := norm_godementJacquetThetaArgument_ge_base K n t ht A B P
  have hMax : max 1 (r Y) <= max 1 (r X) := max_le_max_left _ hNorm
  have hPow : max 1 (r Y) ^ m <= max 1 (r X) ^ m := by gcongr
  have hPos : 0 < max 1 (r Y) ^ m := pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _
  simpa only [one_div] using one_div_le_one_div_of_le hPos hPow

/-- Integrability of the time-zero rational lattice weight against the two
cuspidal factors gives all positive exponential decay rates for the
invertible quotient theta integral. -/
theorem exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_timeZeroWeight
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (DecayNormGroup K n)] (nu : Measure (DecayNormGroup K n))
    (a : DecayIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (f : SchwartzMap (DecayArch K n) Complex)
    (c g : DecayNormGroup K n -> Complex) (m : Nat)
    (hSum : Filter.Eventually (fun p : Prod (DecayNormGroup K n) (DecayNormGroup K n) =>
      Summable (godementJacquetInvertibleThetaTimeZeroWeight K n m a d p.1 p.2)) (ae (nu.prod nu)))
    (hI : Integrable (fun p : Prod (DecayNormGroup K n) (DecayNormGroup K n) =>
      tsum (godementJacquetInvertibleThetaTimeZeroWeight K n m a d p.1 p.2) * norm (c p.1 * g p.2))
      (nu.prod nu))
    (b : Real) :
    Exists (fun M : Real => forall t : Real, 0 <= t ->
      norm (godementJacquetInvertibleDoubleThetaIntegral K n nu
        (godementJacquetMatrixRectangle K a d f) c g t) <= M * Real.exp (-(b * t))) := by
  refine exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_archWeight K n hn nu a d f c g m
    (fun p => tsum (godementJacquetInvertibleThetaTimeZeroWeight K n m a d p.1 p.2)) hI ?_ b
  intro t ht
  filter_upwards [hSum] with p hp
  let v := godementJacquetInvertibleThetaArchWeight K n m
    (godementJacquetMatrixRectangle K a d f) t p.1 p.2
  have hLe := godementJacquetInvertibleThetaArchWeight_le_timeZeroWeight K n m a d f t ht p.1 p.2
  have hv : Summable v := Summable.of_nonneg_of_le
    (fun P => by
      dsimp only [v, godementJacquetInvertibleThetaArchWeight]
      split
      . exact le_rfl
      . exact inv_nonneg.mpr (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
    hLe hp
  exact And.intro hv (hv.tsum_le_tsum hLe hp)

private abbrev ShiftedArchVector (K I : Type*) [Field K] :=
  PiLp 2 (fun _ : I => DedekindZeta.Theta.minkowskiSpace K)

/-- A finite adelic principal rectangle has a summable inverse-power
weight on its rational points once the power exceeds the real dimension. -/
theorem summable_finiteAdelePrincipalVectorCoset_invNormPow
    (K : Type*) [Field K] [NumberField K] (I : Type*) [Fintype I]
    (a : I -> FiniteAdeleRing (RingOfIntegers K) K) (d : RingOfIntegers K)
    (hd : Not (d = 0)) (x0 : I -> K)
    (hx0 : forall i, InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x0 i))
    (m : Nat) (hm : Module.finrank Real (ShiftedArchVector K I) < m) :
    Summable (fun x : Subtype (fun x : I -> K => forall i,
      InFiniteAdelePrincipalCoset (a i) (algebraMap (RingOfIntegers K) K d) (x i)) =>
      Inv.inv (norm (heckePrincipalMinkowskiVector K I x.val)) ^ m) := by
  let R := RingOfIntegers K
  let J : FractionalIdeal (nonZeroDivisors R) K := (Ideal.span (Set.singleton d) : Ideal R)
  let L := DedekindZeta.Theta.idealLattice K J
  let Q := euclideanProductZLattice I L
  let C := Subtype (fun x : I -> K => forall i,
    InFiniteAdelePrincipalCoset (a i) (algebraMap R K d) (x i))
  have hJ : Not ((Ideal.span (Set.singleton d) : Ideal R) = 0) :=
    fun h => hd (Ideal.span_singleton_eq_bot.mp h)
  have hI : Not (J = 0) := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  let : DiscreteTopology L := DedekindZeta.Theta.discreteTopology_idealLattice K J hI
  let : IsZLattice Real L := DedekindZeta.Theta.isZLattice_idealLattice K J hI
  let toL (x : C) (i : I) : L := DedekindZeta.Theta.idealLatticeEquiv K J
    (Subtype.mk (x.val i - x0 i)
      ((finiteAdelePrincipalCoset_iff_sub_mem_ideal (a i) d hd (x0 i) _ (hx0 i)).mp (x.property i)))
  let F (x : C) : Q := Subtype.mk (WithLp.toLp 2 (fun i : I => (toL x i).val))
    ((mem_euclideanProductZLattice I L _).mpr (fun i => (toL x i).property))
  have hEmb : Function.Injective (DedekindZeta.Theta.eEmb K) :=
    (DedekindZeta.Theta.toMinkowski K).injective.comp (mixedEmbedding K).injective
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have he := congrArg (fun z : Q => z.val i) hxy
    change DedekindZeta.Theta.eEmb K (x.val i - x0 i) =
      DedekindZeta.Theta.eEmb K (y.val i - x0 i) at he
    exact (sub_left_inj).mp (hEmb he)
  let z0 := heckePrincipalMinkowskiVector K I x0
  have hShift (x : C) : (F x).val - (-z0) = heckePrincipalMinkowskiVector K I x.val := by
    apply (PiLp.continuousLinearEquiv 2 Real (fun _ : I => DedekindZeta.Theta.minkowskiSpace K)).injective
    funext i
    change DedekindZeta.Theta.eEmb K (x.val i - x0 i) -
      (-DedekindZeta.Theta.eEmb K (x0 i)) = DedekindZeta.Theta.eEmb K (x.val i)
    rw [sub_neg_eq_add]
    have he := map_add (DedekindZeta.Theta.eEmbHom K) (x.val i - x0 i) (x0 i)
    rw [sub_add_cancel] at he
    exact he.symm
  have hRank : Module.finrank Int Q < m := by
    rw [ZLattice.rank Real Q]
    exact hm
  have hSum := (ZLattice.summable_norm_sub_inv_pow Q m hRank (-z0)).comp_injective hF
  refine hSum.congr (fun x => ?_)
  change Inv.inv (norm ((F x).val - (-z0))) ^ m =
    Inv.inv (norm (heckePrincipalMinkowskiVector K I x.val)) ^ m
  rw [hShift x]

private theorem summable_indicator_of_finiteCover
    {X J : Type*} [Fintype J] (S : Set X) (U : J -> Set X) (W : X -> Real)
    (hW : forall x : X, 0 <= W x)
    (hS : forall x : X, Membership.mem S x -> Exists (fun j : J => Membership.mem (U j) x))
    (hU : forall j : J, Summable ((U j).indicator W)) :
    Summable (S.indicator W) := by
  classical
  have hFin : Summable (fun x : X => Finset.sum Finset.univ (fun j : J => (U j).indicator W x)) :=
    summable_sum (fun j _ => hU j)
  refine Summable.of_nonneg_of_le (fun x => Set.indicator_nonneg (fun _ _ => hW x) x) ?_ hFin
  intro x
  by_cases hx : Membership.mem S x
  . choose j hj using hS x hx
    rw [Set.indicator_of_mem hx]
    calc
      W x = (U j).indicator W x := (Set.indicator_of_mem hj _).symm
      _ <= _ := Finset.single_le_sum
        (fun k _ => Set.indicator_nonneg (fun _ _ => hW x) x) (Finset.mem_univ j)
  . rw [Set.indicator_of_notMem hx]
    exact Finset.sum_nonneg (fun k _ => Set.indicator_nonneg (fun _ _ => hW x) x)

private theorem summable_principalPoints_rectangle_indicator_invNormPow
    (K : Type*) [Field K] [NumberField K] (I : Type*) [Fintype I] [DecidableEq I]
    (a : I -> FiniteAdeleRing (RingOfIntegers K) K) (d : RingOfIntegers K)
    (hd : Not (d = 0)) (m : Nat) (hm : Module.finrank Real (ShiftedArchVector K I) < m) :
    let F := FiniteAdeleRing (RingOfIntegers K) K
    let R := finiteAdelePrincipalRectangle K I a (algebraMap (RingOfIntegers K) K d)
    let S := Set.preimage (fun x : I -> K => fun i => algebraMap K F (x i)) R
    Summable (S.indicator (fun x : I -> K => Inv.inv (norm (heckePrincipalMinkowskiVector K I x)) ^ m)) := by
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let e := algebraMap (RingOfIntegers K) K
  let S : Set (I -> K) := fun x => forall i, InFiniteAdelePrincipalCoset (a i) (e d) (x i)
  let W (x : I -> K) := Inv.inv (norm (heckePrincipalMinkowskiVector K I x)) ^ m
  let : MeasurableSpace F := borel F
  let : BorelSpace F := { measurable_eq := rfl }
  have hd' : Not (e d = 0) :=
    (map_ne_zero_iff e (FaithfulSMul.algebraMap_injective (RingOfIntegers K) K)).mpr hd
  have hS :
      Set.preimage (fun x : I -> K => fun i => algebraMap K F (x i))
        (finiteAdelePrincipalRectangle K I a (e d)) = S := by
    apply Set.ext
    intro x
    change Membership.mem (finiteAdelePrincipalRectangle K I a (e d))
      (fun i => algebraMap K F (x i)) <-> Membership.mem S x
    rw [mem_finiteAdelePrincipalRectangle_iff]
    exact forall_congr' (fun i => (finiteAdelePrincipalCoset_iff_mem_translate (a i) (e d) (x i) hd').symm)
  change Summable ((Set.preimage _ _).indicator W)
  rw [hS]
  by_cases h : Nonempty S
  . let x0 := Classical.choice h
    exact summable_subtype_iff_indicator.mp
      (summable_finiteAdelePrincipalVectorCoset_invNormPow K I a d hd x0.val x0.property m hm)
  . have hz : S.indicator W = fun _ : I -> K => 0 := by
      funext x
      exact Set.indicator_of_notMem (fun hx => h (Nonempty.intro (Subtype.mk x hx))) _
    rw [hz]
    exact summable_zero

/-- The inverse-power weight remains summable after an invertible finite
adelic matrix pulls back the finite support rectangle. -/
theorem summable_finiteAdelePrincipalVectorRectangle_pullback_invNormPow
    (K : Type*) [Field K] [NumberField K] (I : Type*) [Fintype I] [DecidableEq I]
    (D : Matrix.GeneralLinearGroup I (FiniteAdeleRing (RingOfIntegers K) K))
    (a : I -> FiniteAdeleRing (RingOfIntegers K) K) (d : RingOfIntegers K) (hd : Not (d = 0))
    (m : Nat) (hm : Module.finrank Real (ShiftedArchVector K I) < m) :
    let F := FiniteAdeleRing (RingOfIntegers K) K
    let e := algebraMap (RingOfIntegers K) K
    let p (x : I -> K) : I -> F := fun i => algebraMap K F (x i)
    let S := Set.preimage (fun x : I -> K => D.val.mulVec (p x)) (finiteAdelePrincipalRectangle K I a (e d))
    Summable (S.indicator (fun x : I -> K => Inv.inv (norm (heckePrincipalMinkowskiVector K I x)) ^ m)) := by
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let e := algebraMap (RingOfIntegers K) K
  let p (x : I -> K) : I -> F := fun i => algebraMap K F (x i)
  let R := finiteAdelePrincipalRectangle K I a (e d)
  let P := Set.preimage D.val.mulVec R
  let S := Set.preimage p P
  let W (x : I -> K) := Inv.inv (norm (heckePrincipalMinkowskiVector K I x)) ^ m
  let : MeasurableSpace F := borel F
  let : BorelSpace F := { measurable_eq := rfl }
  change Summable (S.indicator W)
  choose b hb using exists_disjoint_principalRectangles_mulVec_preimage K I D a d hd
  choose T hT using hb.2
  let U (C : T) := Set.preimage p C.val
  refine summable_indicator_of_finiteCover S U W
    (fun _ => pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _) ?_ ?_
  . intro x hx
    have hxP : Membership.mem P (p x) := hx
    have hxU : Membership.mem
        (Set.iUnion (fun C : Set (I -> F) => Set.iUnion (fun _ : Membership.mem T C => C))) (p x) :=
      Eq.mp (congrArg (fun V : Set (I -> F) => Membership.mem V (p x)) hT.2.2) hxP
    choose C hC using Set.mem_iUnion.mp hxU
    choose hCT hxC using Set.mem_iUnion.mp hC
    exact Exists.intro (Subtype.mk C hCT) hxC
  . intro C
    choose aC hC using hT.1 C.val C.property
    change Summable ((Set.preimage p C.val).indicator W)
    rw [hC.2]
    exact summable_principalPoints_rectangle_indicator_invNormPow K I aC b hb.1 m hm

private theorem heckeAdeleMinkowskiVector_principal
    (K : Type*) [Field K] [NumberField K] (I : Type*) [Fintype I] (x : I -> K) :
    heckeAdeleMinkowskiVector K I
      (fun i => algebraMap K (ThetaAdeles K) (x i)) = heckePrincipalMinkowskiVector K I x := by
  apply (PiLp.continuousLinearEquiv 2 Real (fun _ : I => DedekindZeta.Theta.minkowskiSpace K)).injective
  funext i
  change DedekindZeta.Theta.toMinkowski K
    (InfiniteAdeleRing.ringEquiv_mixedSpace K (algebraMap K (InfiniteAdeleRing K) (x i))) =
    DedekindZeta.Theta.toMinkowski K (mixedEmbedding K (x i))
  exact congrArg (DedekindZeta.Theta.toMinkowski K)
    (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := K) (x := x i)).symm

private theorem norm_heckePrincipalMinkowskiVector_vec_pos
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    (P : Matrix.GeneralLinearGroup (Fin n) K) :
    0 < norm (heckePrincipalMinkowskiVector K (DecayIndex n) P.val.vec) := by
  apply norm_pos_iff.mpr
  intro h
  have hEmb : Function.Injective (DedekindZeta.Theta.eEmb K) :=
    (DedekindZeta.Theta.toMinkowski K).injective.comp (mixedEmbedding K).injective
  have hZ : P.val = 0 := by
    apply Matrix.ext
    intro i j
    have hij := congrArg (fun z : DecayArch K n => z (Prod.mk j i)) h
    change DedekindZeta.Theta.eEmb K (P.val i j) = 0 at hij
    exact hEmb (hij.trans (map_zero (DedekindZeta.Theta.eEmbHom K)).symm)
  let i : Fin n := Fin.mk 0 hn
  have hOne : P.val * P.inv = 1 := P.val_inv
  rw [hZ, zero_mul] at hOne
  have hi := congrArg (fun X : Matrix (Fin n) (Fin n) K => X i i) hOne
  exact zero_ne_one (by simpa only [Matrix.zero_apply, Matrix.one_apply_eq] using hi)

/-- At each pair of quotient representatives the time-zero lattice
weight is summable above the real dimension of the matrix space. -/
theorem summable_godementJacquetInvertibleThetaTimeZeroWeight
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    (a : DecayIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (hd : Not (d = 0))
    (m : Nat) (hm : Module.finrank Real (DecayArch K n) < m) (A B : DecayNormGroup K n) :
    Summable (godementJacquetInvertibleThetaTimeZeroWeight K n m a d A B) := by
  let I := DecayIndex n
  let F := FiniteAdeleRing (RingOfIntegers K) K
  let g : RingHom (ThetaAdeles K) F := RingHom.snd (InfiniteAdeleRing K) F
  let M := godementJacquetMatrixDilation (Inv.inv A.val) B.val
  let D := Matrix.GeneralLinearGroup.map g M
  let T := heckeAdeleArchimedeanMatrixDilation K I M
  let C := max 1 (norm T.symm.toContinuousLinearMap)
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  let R := finiteAdelePrincipalRectangle K I a (algebraMap (RingOfIntegers K) K d)
  let p (v : I -> K) : I -> F := fun i => algebraMap K F (v i)
  let S := Set.preimage (fun v : I -> K => D.val.mulVec (p v)) R
  let W (v : I -> K) := Inv.inv (norm (heckePrincipalMinkowskiVector K I v)) ^ m
  have hS : Summable (S.indicator W) :=
    summable_finiteAdelePrincipalVectorRectangle_pullback_invNormPow K I D a d hd m hm
  let j (P : Matrix.GeneralLinearGroup (Fin n) K) : I -> K := P.val.vec
  have hj : Function.Injective j := by
    intro P Q h
    apply Units.ext
    apply Matrix.ext
    intro i k
    exact congrFun h (Prod.mk k i)
  have hSum : Summable (fun P : Matrix.GeneralLinearGroup (Fin n) K =>
      C ^ m * S.indicator W (j P)) := (hS.comp_injective hj).mul_left _
  refine Summable.of_nonneg_of_le ?_ ?_ hSum
  . intro P
    dsimp only [godementJacquetInvertibleThetaTimeZeroWeight]
    split
    . exact inv_nonneg.mpr (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
    . exact le_rfl
  intro P
  let Y := Inv.inv A.val * adelicPrincipalGeneralLinear K n P * B.val
  let v (i : I) := algebraMap K (ThetaAdeles K) (j P i)
  let x := heckePrincipalMinkowskiVector K I (j P)
  let y := heckeAdeleMinkowskiVector K I Y.val.vec
  let r := max 1 (norm y)
  change (if Membership.mem R (fun i : I => (Y.val.vec i).2) then Inv.inv (r ^ m) else 0) <=
    C ^ m * S.indicator W (j P)
  by_cases hR : Membership.mem R (fun i : I => (Y.val.vec i).2)
  . have hVec : Y.val.vec = M.val.mulVec v :=
      (godementJacquetMatrixDilation_vec (Inv.inv A.val) B.val
        (P.val.map (algebraMap K (ThetaAdeles K)))).symm
    have hFinite : (fun i : I => (Y.val.vec i).2) = D.val.mulVec (p (j P)) := by
      funext i
      exact (congrArg (fun w : I -> ThetaAdeles K => g (w i)) hVec).trans
        (RingHom.map_mulVec g M.val v i)
    have hSP : Membership.mem S (j P) :=
      Eq.mp (congrArg (fun z : I -> F => Membership.mem R z) hFinite) hR
    rw [if_pos hR, Set.indicator_of_mem hSP]
    have hy : y = T x := by
      calc
        _ = heckeAdeleMinkowskiVector K I (M.val.mulVec v) :=
          congrArg (heckeAdeleMinkowskiVector K I) hVec
        _ = T (heckeAdeleMinkowskiVector K I v) := heckeAdeleMinkowskiVector_mulVec K I M v
        _ = _ := congrArg T (heckeAdeleMinkowskiVector_principal K I (j P))
    have hInvOp := T.symm.toContinuousLinearMap.le_opNorm (T x)
    change norm (T.symm (T x)) <= norm T.symm.toContinuousLinearMap * norm (T x) at hInvOp
    rw [T.symm_apply_apply, <- hy] at hInvOp
    have hx : norm x <= C * r := hInvOp.trans
      (mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _) hC.le)
    have hxPos : 0 < norm x := norm_heckePrincipalMinkowskiVector_vec_pos K n hn P
    have hr : 0 < r := zero_lt_one.trans_le (le_max_left _ _)
    have hRecip : Inv.inv r <= C * Inv.inv (norm x) := by
      calc
        _ = C * Inv.inv (C * r) := by field_simp [hC.ne', hr.ne']
        _ <= _ := mul_le_mul_of_nonneg_left
          (by simpa only [one_div] using one_div_le_one_div_of_le hxPos hx) hC.le
    calc
      _ = Inv.inv r ^ m := (inv_pow r m).symm
      _ <= (C * Inv.inv (norm x)) ^ m := by gcongr
      _ = _ := mul_pow _ _ _
  . rw [if_neg hR]
    exact mul_nonneg (pow_nonneg hC.le _) (Set.indicator_nonneg
      (fun v _ => pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _) (j P))

/-- For powers above the real dimension, integrability of the time-zero
lattice sum against the cuspidal factors gives arbitrary positive-time
decay of the invertible Godement-Jacquet theta integral. -/
theorem exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_integrable_timeZeroWeight
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (DecayNormGroup K n)] (nu : Measure (DecayNormGroup K n))
    (a : DecayIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (hd : Not (d = 0)) (f : SchwartzMap (DecayArch K n) Complex)
    (c g : DecayNormGroup K n -> Complex) (m : Nat) (hm : Module.finrank Real (DecayArch K n) < m)
    (hI : Integrable (fun p : Prod (DecayNormGroup K n) (DecayNormGroup K n) =>
      tsum (godementJacquetInvertibleThetaTimeZeroWeight K n m a d p.1 p.2) * norm (c p.1 * g p.2))
      (nu.prod nu))
    (b : Real) :
    Exists (fun M : Real => forall t : Real, 0 <= t ->
      norm (godementJacquetInvertibleDoubleThetaIntegral K n nu
        (godementJacquetMatrixRectangle K a d f) c g t) <= M * Real.exp (-(b * t))) :=
  exists_godementJacquetInvertibleDoubleThetaIntegral_decay_of_timeZeroWeight K n hn nu a d f c g m
    (Filter.Eventually.of_forall (fun p =>
      summable_godementJacquetInvertibleThetaTimeZeroWeight K n hn a d hd m hm p.1 p.2)) hI b

end Robin1984.GRH
