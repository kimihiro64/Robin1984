import Robin1984.GRH.GodementJacquetThetaLatticeDecay

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, together with Tonelli's theorem and geometric-series estimates.
- Formalization note: Unfolds the nonnegative time-zero theta kernel into a convolution and controls the integral by square-integrability on the quotient and a dyadic volume bound for the group weight.
- PROVENANCE-END
-/

/-!
# Integrability of the time-zero theta kernel

Unfolding the rational translates turns the nonnegative integral over two
quotient domains into an integral over the norm-one group. The inner
correlation is uniformly bounded by the squared norms of the two quotient
functions. A sufficiently large inverse power is integrable when the
volume of dyadic norm balls grows at the stipulated geometric rate.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open MeasureTheory

section QuotientConvolution

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- The quotient integral is invariant under right translation when the
group measure is both left and right invariant. -/
theorem lintegral_rightTranslate_eq_of_leftFundamentalDomain
    (Gamma : Subgroup G) [Countable Gamma]
    (mu : Measure G) [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
    (D : Set G) (hD : MeasurableSet D)
    (hUnique : forall x : G, ExistsUnique (fun gamma : Gamma => Membership.mem D (gamma.val * x)))
    (f : G -> ENNReal) (hInv : forall (gamma : Gamma) x, f (gamma.val * x) = f x)
    (g : G) :
    lintegral (mu.restrict D) (fun x => f (x * g)) = lintegral (mu.restrict D) f := by
  let E := MeasurableEquiv.mulRight g
  let T := Set.preimage E.symm D
  have hT : MeasurableSet T := E.symm.measurable hD
  have hUniqueT (x : G) : ExistsUnique (fun gamma : Gamma => Membership.mem T (gamma.val * x)) := by
    have hEq (gamma : Gamma) : Membership.mem T (gamma.val * x) <->
        Membership.mem D (gamma.val * (x * Inv.inv g)) := by
      change Membership.mem D ((gamma.val * x) * Inv.inv g) <->
        Membership.mem D (gamma.val * (x * Inv.inv g))
      rw [mul_assoc]
    choose y hy using hUnique (x * Inv.inv g)
    exact Exists.intro y (And.intro ((hEq y).mpr hy.1) (fun z hz => hy.2 z ((hEq z).mp hz)))
  have hDomD : IsFundamentalDomain Gamma D mu := IsFundamentalDomain.mk' hD.nullMeasurableSet hUnique
  have hDomT : IsFundamentalDomain Gamma T mu := IsFundamentalDomain.mk' hT.nullMeasurableSet hUniqueT
  have hPre : Set.preimage E T = D := by
    ext x
    change Membership.mem D (E.symm (E x)) <-> Membership.mem D x
    rw [E.symm_apply_apply]
  have hPres : MeasurePreserving E (mu.restrict D) (mu.restrict T) := by
    have h := (measurePreserving_mul_right mu g).restrict_preimage_emb E.measurableEmbedding T
    change MeasurePreserving E (mu.restrict (Set.preimage E T)) (mu.restrict T) at h
    rwa [hPre] at h
  calc
    _ = lintegral (mu.restrict T) f := hPres.lintegral_comp_emb E.measurableEmbedding f
    _ = _ := hDomT.setLIntegral_eq hDomD f hInv

variable [MeasurableInv G]

omit [MeasurableMul G] in
private theorem measurable_quotientKernel
    (Gamma : Subgroup G) [Countable Gamma]
    (hMul : Measurable (fun p : Prod G G => p.1 * p.2))
    (w c f : G -> ENNReal) (hw : Measurable w) (hc : Measurable c) (hf : Measurable f) :
    Measurable (fun p : Prod G G =>
      tsum (fun gamma : Gamma => w (Inv.inv p.1 * gamma.val * p.2)) * (c p.1 * f p.2)) := by
  apply Measurable.mul _ ((hc.comp measurable_fst).mul (hf.comp measurable_snd))
  have hGamma (gamma : Gamma) :
      Measurable (fun p : Prod G G => Inv.inv p.1 * gamma.val * p.2) :=
    hMul.comp ((hMul.comp (measurable_fst.inv.prodMk measurable_const)).prodMk measurable_snd)
  exact Measurable.tsum (fun gamma => hw.comp (hGamma gamma))

/-- Unfold the nonnegative sum over rational translates and move the
two quotient functions into a right-translation convolution. -/
theorem lintegral_quotientKernel_eq_unfolded
    (Gamma : Subgroup G) [Countable Gamma]
    (mu : Measure G) [SFinite mu] [mu.IsMulLeftInvariant]
    (D : Set G) (hD : MeasurableSet D)
    (hUnique : forall x : G, ExistsUnique (fun gamma : Gamma => Membership.mem D (gamma.val * x)))
    (hMul : Measurable (fun p : Prod G G => p.1 * p.2))
    (w c f : G -> ENNReal) (hw : Measurable w) (hc : Measurable c) (hf : Measurable f)
    (hInv : forall (gamma : Gamma) x, f (gamma.val * x) = f x) :
    let nu := mu.restrict D
    lintegral (nu.prod nu) (fun p : Prod G G =>
      tsum (fun gamma : Gamma => w (Inv.inv p.1 * gamma.val * p.2)) * (c p.1 * f p.2)) =
      lintegral mu (fun g => w g * lintegral nu (fun a => c a * f (a * g))) := by
  let nu := mu.restrict D
  let K (p : Prod G G) :=
    tsum (fun gamma : Gamma => w (Inv.inv p.1 * gamma.val * p.2)) * (c p.1 * f p.2)
  let V (p : Prod G G) := w p.2 * (c p.1 * f (p.1 * p.2))
  have hFund : IsFundamentalDomain Gamma D mu :=
    IsFundamentalDomain.mk' hD.nullMeasurableSet hUnique
  have hMeasK : Measurable K := measurable_quotientKernel Gamma hMul w c f hw hc hf
  have hMeasV : Measurable V :=
    (hw.comp measurable_snd).mul ((hc.comp measurable_fst).mul (hf.comp hMul))
  have hSlice (a : G) :
      lintegral nu (fun b => K (Prod.mk a b)) = lintegral mu (fun g => V (Prod.mk a g)) := by
    let F (b : G) := w (Inv.inv a * b) * (c a * f b)
    have hF : Measurable F :=
      (hw.comp (measurable_const_mul (Inv.inv a))).mul (measurable_const.mul hf)
    have hRoll := hFund.lintegral_eq_tsum'' F
    change lintegral mu F = tsum (fun gamma : Gamma =>
      lintegral nu (fun b => F (gamma.val * b))) at hRoll
    calc
      _ = lintegral nu (fun b => tsum (fun gamma : Gamma => F (gamma.val * b))) := by
        apply lintegral_congr
        intro b
        change (tsum (fun gamma : Gamma => w (Inv.inv a * gamma.val * b))) * (c a * f b) = _
        have hTerm (gamma : Gamma) : F (gamma.val * b) =
            w (Inv.inv a * gamma.val * b) * (c a * f b) := by
          change w (Inv.inv a * (gamma.val * b)) * (c a * f (gamma.val * b)) = _
          rw [hInv gamma b, mul_assoc (Inv.inv a) gamma.val b]
        simp_rw [hTerm]
        exact ENNReal.tsum_mul_right.symm
      _ = tsum (fun gamma : Gamma => lintegral nu (fun b => F (gamma.val * b))) :=
        lintegral_tsum (fun gamma => (hF.comp (measurable_const_mul gamma.val)).aemeasurable)
      _ = lintegral mu F := hRoll.symm
      _ = _ := by
        have hShift : lintegral mu (fun g => F (a * g)) = lintegral mu F :=
          lintegral_mul_left_eq_self F a
        calc
          _ = lintegral mu (fun g => F (a * g)) := hShift.symm
          _ = _ := by
            apply lintegral_congr
            intro g
            simp only [F, V, <- mul_assoc, inv_mul_cancel, one_mul]
  have hInner (g : G) : Measurable (fun a => c a * f (a * g)) :=
    hc.mul (hf.comp (measurable_mul_const g))
  change lintegral (nu.prod nu) K = _
  calc
    _ = lintegral nu (fun a => lintegral nu (fun b => K (Prod.mk a b))) :=
      lintegral_prod K hMeasK.aemeasurable
    _ = lintegral nu (fun a => lintegral mu (fun g => V (Prod.mk a g))) :=
      lintegral_congr hSlice
    _ = lintegral mu (fun g => lintegral nu (fun a => V (Prod.mk a g))) :=
      lintegral_lintegral_swap hMeasV.aemeasurable
    _ = _ := lintegral_congr (fun g => lintegral_const_mul (w g) (hInner g))

/-- A nonnegative integrable group kernel gives a finite absolute
quotient integral against two square-integrable invariant functions. -/
theorem lintegral_quotientKernel_lt_top_of_square_integrable
    (Gamma : Subgroup G) [Countable Gamma]
    (mu : Measure G) [SFinite mu] [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
    (D : Set G) (hD : MeasurableSet D)
    (hUnique : forall x : G, ExistsUnique (fun gamma : Gamma => Membership.mem D (gamma.val * x)))
    (hMul : Measurable (fun p : Prod G G => p.1 * p.2))
    (w : G -> ENNReal) (hw : Measurable w) (hwI : lintegral mu w < (Top.top : ENNReal))
    (c f : G -> Real) (hc : Measurable c) (hf : Measurable f)
    (hc0 : forall a, 0 <= c a)
    (hInv : forall (gamma : Gamma) a, f (gamma.val * a) = f a)
    (hcI : lintegral (mu.restrict D) (fun a => ENNReal.ofReal (c a ^ 2)) < (Top.top : ENNReal))
    (hfI : lintegral (mu.restrict D) (fun a => ENNReal.ofReal (f a ^ 2)) < (Top.top : ENNReal)) :
    let nu := mu.restrict D
    lintegral (nu.prod nu) (fun p : Prod G G =>
      tsum (fun gamma : Gamma => w (Inv.inv p.1 * gamma.val * p.2)) *
        (ENNReal.ofReal (c p.1) * ENNReal.ofReal (f p.2))) < (Top.top : ENNReal) := by
  let nu := mu.restrict D
  let h (a : G) := ENNReal.ofReal (c a ^ 2)
  let k (a : G) := ENNReal.ofReal (f a ^ 2)
  let C := lintegral nu h + lintegral nu k
  have hC : C < (Top.top : ENNReal) := ENNReal.add_lt_top.mpr (And.intro hcI hfI)
  have hKh : Measurable h := (hc.pow_const 2).ennreal_ofReal
  have hR (g : G) : lintegral nu (fun a => k (a * g)) = lintegral nu k :=
    lintegral_rightTranslate_eq_of_leftFundamentalDomain Gamma mu D hD hUnique k
      (fun gamma a => congrArg (fun r : Real => ENNReal.ofReal (r ^ 2)) (hInv gamma a)) g
  have hInner (g : G) :
      lintegral nu (fun a => ENNReal.ofReal (c a) * ENNReal.ofReal (f (a * g))) <= C := by
    calc
      _ <= lintegral nu (fun a => h a + k (a * g)) := by
        apply lintegral_mono
        intro a
        change ENNReal.ofReal (c a) * ENNReal.ofReal (f (a * g)) <=
          ENNReal.ofReal (c a ^ 2) + ENNReal.ofReal (f (a * g) ^ 2)
        rw [<- ENNReal.ofReal_mul (hc0 a), <- ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (c a - f (a * g))])
      _ = lintegral nu h + lintegral nu (fun a => k (a * g)) := lintegral_add_left hKh _
      _ = C := congrArg (fun y => lintegral nu h + y) (hR g)
  have hEq := lintegral_quotientKernel_eq_unfolded Gamma mu D hD hUnique hMul w
    (fun a => ENNReal.ofReal (c a)) (fun a => ENNReal.ofReal (f a))
    hw hc.ennreal_ofReal hf.ennreal_ofReal (fun gamma a => congrArg ENNReal.ofReal (hInv gamma a))
  refine hEq.le.trans_lt ?_
  calc
    _ <= lintegral mu (fun g => w g * C) := by
      apply lintegral_mono
      intro g
      exact mul_le_mul_right (hInner g) (w g)
    _ = C * lintegral mu w := by
      simp_rw [mul_comm _ C]
      exact lintegral_const_mul C hw
    _ < Top.top := ENNReal.mul_lt_top hC hwI

end QuotientConvolution

open NumberField IsDedekindDomain
open scoped Classical

private abbrev ThetaKernelGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker
private abbrev ThetaKernelIndex (n : Nat) := Prod (Fin n) (Fin n)

/-- The time-zero matrix weight as a nonnegative function on the norm-one group. -/
def godementJacquetThetaGroupWeight
    (K : Type*) [Field K] [NumberField K] (n m : Nat)
    (a : ThetaKernelIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (Y : ThetaKernelGroup K n) : ENNReal :=
  ENNReal.ofReal (if Membership.mem
    (finiteAdelePrincipalRectangle K (ThetaKernelIndex n) a (algebraMap (RingOfIntegers K) K d))
    (fun i => (Y.val.val.vec i).2) then
      Inv.inv (max 1 (norm (heckeAdeleMinkowskiVector K (ThetaKernelIndex n) Y.val.val.vec)) ^ m)
    else 0)

/-- An integrable group weight controls the time-zero theta sum against two
square-integrable quotient functions on the determinant-norm-one group. -/
theorem integrable_godementJacquetInvertibleThetaTimeZeroWeight_of_groupWeight
    (K : Type*) [Field K] [NumberField K] (n : Nat) (hn : 0 < n)
    [MeasurableSpace (ThetaKernelGroup K n)] [MeasurableMul (ThetaKernelGroup K n)]
    [MeasurableInv (ThetaKernelGroup K n)]
    (mu : Measure (ThetaKernelGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
    (D : Set (ThetaKernelGroup K n)) (hD : MeasurableSet D)
    (hUnique : forall x : ThetaKernelGroup K n,
      ExistsUnique (fun gamma : (adelicPrincipalDeterminantOne K n).range =>
        Membership.mem D (gamma.val * x)))
    (hMul : Measurable (fun p : Prod (ThetaKernelGroup K n) (ThetaKernelGroup K n) => p.1 * p.2))
    (a : ThetaKernelIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (hd : Not (d = 0))
    (m : Nat) (hm : Module.finrank Real
      (PiLp 2 (fun _ : ThetaKernelIndex n => DedekindZeta.Theta.minkowskiSpace K)) < m)
    (hw : Measurable (godementJacquetThetaGroupWeight K n m a d))
    (hwI : lintegral mu (godementJacquetThetaGroupWeight K n m a d) < (Top.top : ENNReal))
    (c f : ThetaKernelGroup K n -> Complex) (hc : Measurable c) (hf : Measurable f)
    (hInv : forall (gamma : (adelicPrincipalDeterminantOne K n).range) x, f (gamma.val * x) = f x)
    (hcI : lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (c x) ^ 2)) < (Top.top : ENNReal))
    (hfI : lintegral (mu.restrict D) (fun x => ENNReal.ofReal (norm (f x) ^ 2)) < (Top.top : ENNReal)) :
    Integrable (fun p : Prod (ThetaKernelGroup K n) (ThetaKernelGroup K n) =>
      tsum (godementJacquetInvertibleThetaTimeZeroWeight K n m a d p.1 p.2) * norm (c p.1 * f p.2))
      ((mu.restrict D).prod (mu.restrict D)) := by
  let G := ThetaKernelGroup K n
  let H := adelicPrincipalDeterminantOne K n
  let Gamma := H.range
  let nu := mu.restrict D
  let w := godementJacquetThetaGroupWeight K n m a d
  let r (p : Prod G G) :=
    tsum (godementJacquetInvertibleThetaTimeZeroWeight K n m a d p.1 p.2) * norm (c p.1 * f p.2)
  let L (p : Prod G G) :=
    tsum (fun gamma : Gamma => w (Inv.inv p.1 * gamma.val * p.2)) *
      (ENNReal.ofReal (norm (c p.1)) * ENNReal.ofReal (norm (f p.2)))
  let _ : Countable Gamma := countable_adelicPrincipalDeterminantOne K n
  let E : Equiv (Matrix.GeneralLinearGroup (Fin n) K) Gamma :=
    Equiv.ofInjective H adelicPrincipalDeterminantOne_injective
  have hC : Measurable (fun x : G => ENNReal.ofReal (norm (c x))) := hc.norm.ennreal_ofReal
  have hF : Measurable (fun x : G => ENNReal.ofReal (norm (f x))) := hf.norm.ennreal_ofReal
  have hL : Measurable L :=
    measurable_quotientKernel Gamma hMul w _ _ hw hC hF
  have hFin : lintegral (nu.prod nu) L < (Top.top : ENNReal) :=
    lintegral_quotientKernel_lt_top_of_square_integrable Gamma mu D hD hUnique hMul w hw hwI
      (fun x => norm (c x)) (fun x => norm (f x)) hc.norm hf.norm (fun x => norm_nonneg (c x))
      (fun gamma x => congrArg norm (hInv gamma x)) hcI hfI
  have hWeight (p : Prod G G) (P : Matrix.GeneralLinearGroup (Fin n) K) :
      0 <= godementJacquetInvertibleThetaTimeZeroWeight K n m a d p.1 p.2 P := by
    dsimp only [godementJacquetInvertibleThetaTimeZeroWeight]
    split
    . exact inv_nonneg.mpr (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
    . exact le_rfl
  have hR (p : Prod G G) : 0 <= r p :=
    mul_nonneg (tsum_nonneg (hWeight p)) (norm_nonneg _)
  have hEq (p : Prod G G) : ENNReal.ofReal (r p) = L p := by
    have hS := summable_godementJacquetInvertibleThetaTimeZeroWeight K n hn a d hd m hm p.1 p.2
    dsimp only [r, L]
    rw [ENNReal.ofReal_mul (tsum_nonneg (hWeight p)), ENNReal.ofReal_tsum_of_nonneg (hWeight p) hS,
      norm_mul, ENNReal.ofReal_mul (norm_nonneg (c p.1))]
    have hTerm (P : Matrix.GeneralLinearGroup (Fin n) K) :
        ENNReal.ofReal (godementJacquetInvertibleThetaTimeZeroWeight K n m a d p.1 p.2 P) =
          w (Inv.inv p.1 * (E P).val * p.2) := rfl
    simp_rw [hTerm]
    exact congrArg (fun s : ENNReal => s * (ENNReal.ofReal (norm (c p.1)) * ENNReal.ofReal (norm (f p.2))))
      (E.tsum_eq (fun gamma => w (Inv.inv p.1 * gamma.val * p.2)))
  have hMeas : Measurable r := by
    have he : r = fun p => ENNReal.toReal (L p) := by
      funext p
      rw [<- hEq p, ENNReal.toReal_ofReal (hR p)]
    rw [he]
    exact ENNReal.measurable_toReal.comp hL
  change Integrable r (nu.prod nu)
  refine And.intro hMeas.aestronglyMeasurable ?_
  rw [hasFiniteIntegral_iff_norm]
  have hNorm (p : Prod G G) : ENNReal.ofReal (norm (r p)) = L p := by
    rw [Real.norm_of_nonneg (hR p), hEq p]
  exact (lintegral_congr hNorm).trans_lt hFin

/-- A dyadic volume bound on the support of a weight gives a finite integral
of a reciprocal power when the scaled geometric ratio is less than one. -/
theorem lintegral_reciprocalPower_lt_top_of_dyadicVolumeBound
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (S : Set X) (hS : MeasurableSet S) (r : X -> Real) (hr : Measurable r)
    (m : Nat) (B q : Real) (hB : 0 <= B) (hq : 0 <= q) (hRatio : q / (2 : Real) ^ m < 1)
    (hVolume : forall k : Nat,
      mu (S.inter (Set.preimage r (Set.Iic ((2 : Real) ^ (k + 1))))) <=
        ENNReal.ofReal (B * q ^ k)) :
    lintegral mu (S.indicator (fun x => ENNReal.ofReal (Inv.inv (max 1 (r x) ^ m)))) <
      (Top.top : ENNReal) := by
  let T (k : Nat) := S.inter (Set.preimage r (Set.Iic ((2 : Real) ^ (k + 1))))
  let a : Real := Inv.inv ((2 : Real) ^ m)
  let v (k : Nat) (x : X) := (T k).indicator (fun _ => ENNReal.ofReal (a ^ k)) x
  have ha : 0 <= a := by
    dsimp [a]
    positivity
  have hT (k : Nat) : MeasurableSet (T k) := hS.inter (hr measurableSet_Iic)
  have hMeas (k : Nat) : Measurable (v k) := measurable_const.indicator (hT k)
  have hExists (x : X) : Exists (fun k : Nat => r x <= (2 : Real) ^ (k + 1)) := by
    choose j hj using pow_unbounded_of_one_lt (r x) (by norm_num : (1 : Real) < 2)
    refine Exists.intro j (hj.le.trans ?_)
    rw [pow_succ]
    have hj0 : 0 <= (2 : Real) ^ j := by positivity
    linarith
  have hPoint (x : X) :
      S.indicator (fun y => ENNReal.ofReal (Inv.inv (max 1 (r y) ^ m))) x <=
        tsum (fun k => v k x) := by
    by_cases hx : Membership.mem S x
    . let k := Nat.find (hExists x)
      have hk : r x <= (2 : Real) ^ (k + 1) := Nat.find_spec (hExists x)
      have hTmem : Membership.mem (T k) x := And.intro hx hk
      have hLower : (2 : Real) ^ k <= max 1 (r x) := by
        cases h : k with
        | zero => simpa only [pow_zero] using le_max_left (1 : Real) (r x)
        | succ j =>
          have hj : j < Nat.find (hExists x) := by
            change j < k
            rw [h]
            exact Nat.lt_succ_self j
          have hn : Not (r x <= (2 : Real) ^ (j + 1)) := Nat.find_min (hExists x) hj
          exact (lt_of_not_ge hn).le.trans (le_max_right 1 (r x))
      have hP (j : Nat) : ((2 : Real) ^ k) ^ j <= max 1 (r x) ^ j := by
        induction j with
        | zero => simp
        | succ j ih =>
          rw [pow_succ, pow_succ]
          exact mul_le_mul ih hLower (by positivity) (by positivity)
      have hp : 0 < ((2 : Real) ^ k) ^ m := by positivity
      have hinv : Inv.inv (max 1 (r x) ^ m) <= Inv.inv (((2 : Real) ^ k) ^ m) := by
        simpa only [one_div] using one_div_le_one_div_of_le hp (hP m)
      rw [Set.indicator_of_mem hx]
      calc
        _ <= ENNReal.ofReal (Inv.inv (((2 : Real) ^ k) ^ m)) := ENNReal.ofReal_le_ofReal hinv
        _ = v k x := by
          have hPow : ((2 : Real) ^ k) ^ m = ((2 : Real) ^ m) ^ k := by
            rw [<- pow_mul, <- pow_mul, Nat.mul_comm k m]
          dsimp only [v, a]
          rw [Set.indicator_of_mem hTmem, hPow, inv_pow]
        _ <= _ := ENNReal.le_tsum k
    . rw [Set.indicator_of_notMem hx]
      exact bot_le
  have hScale (k : Nat) :
      lintegral mu (v k) <= ENNReal.ofReal (B * (q * a) ^ k) := by
    change lintegral mu ((T k).indicator (fun _ => ENNReal.ofReal (a ^ k))) <= _
    rw [lintegral_indicator_const (hT k)]
    calc
      _ <= ENNReal.ofReal (a ^ k) * ENNReal.ofReal (B * q ^ k) :=
        mul_le_mul_right (hVolume k) _
      _ = _ := by
        rw [<- ENNReal.ofReal_mul (pow_nonneg ha _), mul_pow]
        congr 1
        ring
  have hQ : q * a < 1 := by
    change q * Inv.inv ((2 : Real) ^ m) < 1
    rwa [<- div_eq_mul_inv]
  have hSeries : Summable (fun k : Nat => B * (q * a) ^ k) :=
    (summable_geometric_of_lt_one (mul_nonneg hq ha) hQ).mul_left B
  calc
    _ <= lintegral mu (fun x => tsum (fun k => v k x)) := lintegral_mono hPoint
    _ = tsum (fun k => lintegral mu (v k)) := lintegral_tsum (fun k => (hMeas k).aemeasurable)
    _ <= tsum (fun k => ENNReal.ofReal (B * (q * a) ^ k)) := ENNReal.tsum_le_tsum hScale
    _ = ENNReal.ofReal (tsum (fun k : Nat => B * (q * a) ^ k)) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hB (pow_nonneg (mul_nonneg hq ha) _)) hSeries).symm
    _ < Top.top := ENNReal.ofReal_lt_top

/-- Dyadic volume growth on the finite rectangle controls the precise
reciprocal-power weight used in the time-zero theta convolution. -/
theorem lintegral_godementJacquetThetaGroupWeight_lt_top_of_dyadicVolumeBound
    (K : Type*) [Field K] [NumberField K] (n m : Nat)
    [MeasurableSpace (ThetaKernelGroup K n)] (mu : Measure (ThetaKernelGroup K n))
    (a : ThetaKernelIndex n -> FiniteAdeleRing (RingOfIntegers K) K)
    (d : RingOfIntegers K) (B q : Real) (hB : 0 <= B) (hq : 0 <= q) (hRatio : q / (2 : Real) ^ m < 1) :
    let S := Set.ofPred (fun Y : ThetaKernelGroup K n => Membership.mem
      (finiteAdelePrincipalRectangle K (ThetaKernelIndex n) a (algebraMap (RingOfIntegers K) K d))
      (fun i => (Y.val.val.vec i).2))
    let r (Y : ThetaKernelGroup K n) :=
      norm (heckeAdeleMinkowskiVector K (ThetaKernelIndex n) Y.val.val.vec)
    MeasurableSet S -> Measurable r ->
    (forall k : Nat, mu (S.inter (Set.preimage r (Set.Iic ((2 : Real) ^ (k + 1))))) <=
      ENNReal.ofReal (B * q ^ k)) ->
    lintegral mu (godementJacquetThetaGroupWeight K n m a d) < (Top.top : ENNReal) := by
  intro S r hS hr hVol
  have hWeight : godementJacquetThetaGroupWeight K n m a d =
      S.indicator (fun Y => ENNReal.ofReal (Inv.inv (max 1 (r Y) ^ m))) := by
    funext Y
    by_cases h : Membership.mem S Y
    . rw [Set.indicator_of_mem h]
      dsimp only [godementJacquetThetaGroupWeight]
      split
      . rfl
      . rename_i hOutside
        exact False.elim (hOutside h)
    . rw [Set.indicator_of_notMem h]
      dsimp only [godementJacquetThetaGroupWeight]
      split
      . rename_i hInside
        exact False.elim (h hInside)
      . exact ENNReal.ofReal_zero
  rw [hWeight]
  exact lintegral_reciprocalPower_lt_top_of_dyadicVolumeBound mu S hS r hr m B q hB hq hRatio hVol

end Robin1984.GRH
