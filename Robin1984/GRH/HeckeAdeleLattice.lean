import Robin1984.GRH.HeckeEulerProduct

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The additive strong approximation and lattice theorem for number-field adeles in Tate's thesis.
- Formalization note: Uses the product formula, local finite residue arithmetic, the Chinese remainder theorem, and the archimedean integer lattice to prove discreteness and compactness of the additive adelic quotient.
- PROVENANCE-END
-/

/-!
# The diagonal number field in its additive adele ring

The product formula isolates zero among the principal adeles. Finite
approximation and a compact set of archimedean representatives give a
compact set meeting every coset of the diagonal number field.
-/

set_option autoImplicit false

open Complex Filter IsDedekindDomain NumberField Set

namespace Robin1984.GRH

section PrincipalSubgroup

variable (K : Type*) [Field K] [NumberField K]

/-- The diagonal copy of the number field has an open neighborhood of
zero in the additive adele ring containing no other field element. -/
theorem exists_adelicNeighborhood_inter_principal_eq_zero :
    Exists (fun U : Set (AdeleRing (RingOfIntegers K) K) =>
      IsOpen U /\ Membership.mem U 0 /\
        forall x : K, Membership.mem U (algebraMap K (AdeleRing (RingOfIntegers K) K) x) -> x = 0) := by
  classical
  let AInf := InfiniteAdeleRing K
  let AFin := FiniteAdeleRing (RingOfIntegers K) K
  let S : Set AInf := {a | forall w : InfinitePlace K, norm (a w) < 1}
  let T : Set AFin := {a | forall p : HeightOneSpectrum (RingOfIntegers K),
    Membership.mem (p.adicCompletionIntegers K) (a p)}
  let U : Set (AdeleRing (RingOfIntegers K) K) := Set.prod S T
  have hS : IsOpen S := by
    have hEq : S = iInter (fun w : InfinitePlace K => {a : AInf | norm (a w) < 1}) := by
      ext a
      simp [S]
    rw [hEq]
    apply isOpen_iInter_of_finite
    intro w
    have hEv : Continuous (fun a : AInf => a w) := continuous_apply w
    exact isOpen_lt hEv.norm continuous_const
  have hT : IsOpen T :=
    RestrictedProduct.isOpen_forall_mem
      (R := fun p : HeightOneSpectrum (RingOfIntegers K) => p.adicCompletion K)
      (A := fun p => (p.adicCompletionIntegers K : Set (p.adicCompletion K)))
      (fun p => Valued.isOpen_valuationSubring (p.adicCompletion K))
  refine Exists.intro U (And.intro (hS.prod hT) (And.intro ?_ ?_))
  case refine_1 =>
    exact And.intro
      (by
        intro w
        change norm (0 : w.Completion) < 1
        rw [norm_zero]
        exact zero_lt_one)
      (by
        intro p
        exact (p.adicCompletionIntegers K).zero_mem)
  case refine_2 =>
    intro x hx
    by_contra hx0
    let u := Units.mk0 x hx0
    let ui := Units.map (algebraMap K AInf).toMonoidHom u
    let uf := Units.map (algebraMap K AFin).toMonoidHom u
    have hEdge : heckeInfiniteIdeleNorm ui * heckeFiniteIdeleNorm uf = 1 :=
      heckeIdelicNorm_principal u
    have hInf : heckeInfiniteIdeleNorm ui < 1 := by
      change Finset.prod Finset.univ (fun w : InfinitePlace K => norm (ui.val w) ^ w.mult) < 1
      calc
        _ < Finset.prod (Finset.univ : Finset (InfinitePlace K)) (fun _ => (1 : Real)) := by
          apply Finset.prod_lt_prod_of_nonempty
          case hf =>
            intro w hw
            have hMul : ui.val w * ui.inv w = 1 :=
              congrArg (fun a : AInf => a w) ui.val_inv
            have hn : Not (ui.val w = 0) := by
              intro h
              rw [h, zero_mul] at hMul
              exact zero_ne_one hMul
            exact pow_pos (norm_pos_iff.mpr hn) _
          case hfg =>
            intro w hw
            exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) w.mult_ne_zero).mpr (hx.1 w)
          case h_ne => exact Finset.univ_nonempty
        _ = 1 := Finset.prod_const_one
    have hFin : heckeFiniteIdeleNorm uf <= 1 := by
      let f (p : HeightOneSpectrum (RingOfIntegers K)) := norm (uf.val p)
      have hSupport : Function.HasFiniteMulSupport f := finiteSupport_heckeFiniteIdeleFactors uf
      change finprod f <= 1
      rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ Set.Subset.rfl hSupport]
      apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
      intro p hp
      have hVal : Valued.v (uf.val p) <= (1 : WithZero (Multiplicative Int)) :=
        hx.2 p
      change norm (uf.val p) <= 1
      rw [FinitePlace.norm_def, <- NNReal.coe_one, NNReal.coe_le_coe]
      have hNN : (1 : NNReal) < (Ideal.absNorm p.asIdeal : NNReal) := by
        exact_mod_cast one_lt_dedekindPrimeNorm K p
      exact (WithZeroMulInt.toNNReal_le_one_iff hNN).mpr hVal
    have hPos := heckeInfiniteIdeleNorm_pos ui
    have hTotal : heckeInfiniteIdeleNorm ui * heckeFiniteIdeleNorm uf < 1 := by
      calc
        _ <= heckeInfiniteIdeleNorm ui * 1 := mul_le_mul_of_nonneg_left hFin hPos.le
        _ < 1 := by rw [mul_one]; exact hInf
    rw [hEdge] at hTotal
    exact (lt_irrefl (1 : Real)) hTotal

/-- The principal additive subgroup of the adele ring is discrete. -/
theorem discreteTopology_principalAdeles :
    DiscreteTopology (AdeleRing.principalSubgroup (RingOfIntegers K) K) := by
  let A := AdeleRing (RingOfIntegers K) K
  let H := AdeleRing.principalSubgroup (RingOfIntegers K) K
  have h := exists_adelicNeighborhood_inter_principal_eq_zero K
  choose U hU using h
  have hEq : Set.preimage (fun a : H => (a : A)) U = ({0} : Set H) := by
    ext a
    constructor
    case mp =>
      intro ha
      have hDiag : Exists (fun x : K => algebraMap K A x = (a : A)) := a.property
      choose x hx using hDiag
      have hx0 : x = 0 := hU.2.2 x (by rw [hx]; exact ha)
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      show (a : A) = 0
      rw [<- hx, hx0, map_zero]
    case mpr =>
      intro ha
      rw [Set.mem_singleton_iff.mp ha]
      exact hU.2.1
  change DiscreteTopology H
  apply discreteTopology_of_isOpen_singleton_zero
  rw [<- hEq]
  exact hU.1.preimage continuous_subtype_val

/-- The principal additive subgroup is closed in the adele ring. -/
theorem isClosed_principalAdeles :
    IsClosed (AdeleRing.principalSubgroup (RingOfIntegers K) K :
      Set (AdeleRing (RingOfIntegers K) K)) := by
  have hInf : T2Space (InfiniteAdeleRing K) := by
    change T2Space ((w : InfinitePlace K) -> w.Completion)
    infer_instance
  have hFin : T2Space (FiniteAdeleRing (RingOfIntegers K) K) := by
    let projection (a : FiniteAdeleRing (RingOfIntegers K) K)
        (p : HeightOneSpectrum (RingOfIntegers K)) := a p
    have hInj : Function.Injective projection := DFunLike.coe_injective
    have hCont : Continuous projection := continuous_pi (fun p =>
      RestrictedProduct.continuous_eval p)
    exact T2Space.of_injective_continuous hInj hCont
  have hAdele : T2Space (AdeleRing (RingOfIntegers K) K) := by
    change T2Space (Prod (InfiniteAdeleRing K) (FiniteAdeleRing (RingOfIntegers K) K))
    infer_instance
  have hDiscrete := discreteTopology_principalAdeles K
  exact AddSubgroup.isClosed_of_discrete

end PrincipalSubgroup

section Cocompactness

variable {K : Type*} [Field K] [NumberField K]

/-- A single nonzero global algebraic integer clears the denominators
of every component of a finite adele. -/
theorem exists_finiteAdele_integral_multiple
    (a : FiniteAdeleRing (RingOfIntegers K) K) :
    Exists (fun d : RingOfIntegers K => Not (d = 0) /\
      forall p : HeightOneSpectrum (RingOfIntegers K),
        Membership.mem (p.adicCompletionIntegers K)
          (a p * algebraMap (RingOfIntegers K) (p.adicCompletion K) d)) := by
  classical
  let P := HeightOneSpectrum (RingOfIntegers K)
  let good (p : P) := Membership.mem (p.adicCompletionIntegers K) (a p)
  have hGood : Filter.Eventually good Filter.cofinite := a.property
  have hBad := Filter.eventually_cofinite.mp hGood
  let bad := hBad.toFinset
  have hLocal : forall p : P, Exists (fun d : RingOfIntegers K =>
      Membership.mem (nonZeroDivisors (RingOfIntegers K)) d /\
        Membership.mem (p.adicCompletionIntegers K)
          (a p * algebraMap (RingOfIntegers K) (p.adicCompletion K) d)) :=
    fun p => HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers p (a p)
  choose d hd using hLocal
  let D := Finset.prod bad d
  refine Exists.intro D (And.intro ?_ ?_)
  case refine_1 =>
    exact Finset.prod_ne_zero_iff.mpr (fun p _ => nonZeroDivisors.ne_zero (hd p).1)
  case refine_2 =>
    intro p
    let B := p.adicCompletionIntegers K
    let e := algebraMap (RingOfIntegers K) (p.adicCompletion K)
    have hAll : forall r : RingOfIntegers K, Membership.mem B (e r) :=
      fun r => HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers K) K p r
    by_cases hp : Membership.mem bad p
    case pos =>
      have hDiv : Dvd.dvd (d p) D := Finset.dvd_prod_of_mem d hp
      have hExists : Exists (fun c : RingOfIntegers K => D = d p * c) := hDiv
      choose c hc using hExists
      change Membership.mem B (a p * e D)
      rw [hc, map_mul, <- mul_assoc]
      exact B.mul_mem _ _ (hd p).2 (hAll c)
    case neg =>
      have ha : good p := by
        by_contra h
        exact hp (hBad.mem_toFinset.mpr h)
      exact B.mul_mem _ _ ha (hAll D)

/-- A tuple of local integers has a simultaneous global representative
modulo any nonzero global algebraic integer. -/
theorem exists_adicCompletionIntegers_simultaneous_approximation
    (d : RingOfIntegers K) (hd : Not (d = 0))
    (y : forall p : HeightOneSpectrum (RingOfIntegers K), p.adicCompletionIntegers K) :
    Exists (fun b : RingOfIntegers K =>
      forall p : HeightOneSpectrum (RingOfIntegers K),
        (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
          (algebraMap (RingOfIntegers K) (p.adicCompletion K) b - (y p : p.adicCompletion K)) <=
        (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
          (algebraMap (RingOfIntegers K) (p.adicCompletion K) d)) := by
  classical
  let P := HeightOneSpectrum (RingOfIntegers K)
  let R := RingOfIntegers K
  let e (p : P) := algebraMap R (p.adicCompletion K)
  let V (p : P) := (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative Int)))
  let S : Set P := {p | Membership.mem p.asIdeal d}
  have hSpan : Not (Ideal.span ({d} : Set R) = 0) := by
    intro h
    exact hd (Ideal.span_singleton_eq_bot.mp (show Ideal.span ({d} : Set R) = Bot.bot from h))
  have hS : S.Finite := by
    simp only [S, <- Ideal.dvd_span_singleton]
    exact Ideal.finite_factors hSpan
  let F := hS.toFinset
  let n (p : P) := multiplicity p.asIdeal (Ideal.span ({d} : Set R))
  let I (p : F) := p.val.asIdeal ^ n p.val
  have hMap (p : P) (a : R) : Membership.mem (p.adicCompletionIntegers K) (e p a) :=
    HeightOneSpectrum.coe_algebraMap_mem R K p a
  have hValue (p : P) (a : R) : V p (e p a) = p.intValuation a :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) (v := p) a).trans
      (HeightOneSpectrum.valuation_of_algebraMap (K := K) p a)
  have hLocal (p : P) : Exists (fun b : R =>
      V p (e p b - (y p : p.adicCompletion K)) < V p (e p d)) :=
    exists_adicCompletionIntegers_approximation p (y p) (e p d)
      (fun h => hd ((FaithfulSMul.algebraMap_injective R (p.adicCompletion K))
        (h.trans (map_zero (e p)).symm)))
      (hMap p d)
  choose r hr using hLocal
  have hCoprime : Pairwise (fun p q : F => IsCoprime (I p) (I q)) := by
    intro p q hpq
    have hDiff : Not (p.val.asIdeal = q.val.asIdeal) := by
      intro heq
      exact hpq (Subtype.ext (HeightOneSpectrum.ext_iff.mpr heq))
    have hp := HeightOneSpectrum.isMaximal p.val
    have hq := HeightOneSpectrum.isMaximal q.val
    exact (Ideal.isCoprime_of_isMaximal hDiff).pow
  let rbar (p : F) := Ideal.Quotient.mk (I p) (r p.val)
  have hQuot := (Ideal.quotientInfToPiQuotient_surj (I := I) hCoprime) rbar
  choose bbar hbbar using hQuot
  have hB := Ideal.Quotient.mk_surjective bbar
  choose b hb using hB
  refine Exists.intro b ?_
  intro p
  by_cases hp : Membership.mem F p
  case pos =>
    let q : F := Subtype.mk p hp
    have hEq := congrFun hbbar q
    rw [<- hb, Ideal.quotientInfToPiQuotient_mk'] at hEq
    have hMem : Membership.mem (p.asIdeal ^ n p) (b - r p) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hEq, sub_self]
    have hDiff : V p (e p b - e p (r p)) <= V p (e p d) := by
      rw [<- map_sub, hValue, hValue]
      rw [p.intValuation_eq_exp_neg_multiplicity hd]
      exact (p.intValuation_le_pow_iff_mem (b - r p) (n p)).mpr hMem
    change V p (e p b - (y p : p.adicCompletion K)) <= V p (e p d)
    calc
      _ = V p ((e p b - e p (r p)) + (e p (r p) - (y p : p.adicCompletion K))) := by
        rw [sub_add_sub_cancel]
      _ <= max (V p (e p b - e p (r p)))
          (V p (e p (r p) - (y p : p.adicCompletion K))) := (V p).map_add _ _
      _ <= V p (e p d) := max_le hDiff (le_of_lt (hr p))
  case neg =>
    have hDPrime : Not (Membership.mem p.asIdeal d) := fun h => hp (hS.mem_toFinset.mpr h)
    have hOne : V p (e p d) = 1 := (hValue p d).trans
      ((p.intValuation_eq_one_iff_mem_primeCompl d).mpr hDPrime)
    change V p (e p b - (y p : p.adicCompletion K)) <= V p (e p d)
    rw [hOne]
    exact (p.adicCompletionIntegers K).toSubring.sub_mem (hMap p b) (y p).property

/-- Every finite adele differs from a global field element by a tuple
of local integers. -/
theorem exists_finiteAdele_sub_principal_integral
    (a : FiniteAdeleRing (RingOfIntegers K) K) :
    Exists (fun x : K => forall p : HeightOneSpectrum (RingOfIntegers K),
      Membership.mem (p.adicCompletionIntegers K)
        (a p - algebraMap K (p.adicCompletion K) x)) := by
  let R := RingOfIntegers K
  let P := HeightOneSpectrum R
  let e (p : P) := algebraMap R (p.adicCompletion K)
  have h := exists_finiteAdele_integral_multiple a
  choose d hd using h
  let y (p : P) : p.adicCompletionIntegers K := Subtype.mk (a p * e p d) (hd.2 p)
  have hout := exists_adicCompletionIntegers_simultaneous_approximation d hd.1 y
  choose b hb using hout
  let dK := algebraMap R K d
  let bK := algebraMap R K b
  let x := bK / dK
  have hdK : Not (dK = 0) := by
    intro he
    exact hd.1 ((FaithfulSMul.algebraMap_injective R K)
      (he.trans (map_zero (algebraMap R K)).symm))
  have hEqK : x * dK = bK := (eq_div_iff hdK).mp rfl
  refine Exists.intro x ?_
  intro p
  let E := p.adicCompletion K
  let V := (Valued.v : Valuation E (WithZero (Multiplicative Int)))
  have hdE : Not (e p d = 0) := by
    intro he
    exact hd.1 ((FaithfulSMul.algebraMap_injective R E) (he.trans (map_zero (e p)).symm))
  have hdV : 0 < V (e p d) := zero_lt_iff.mpr ((V.ne_zero_iff).mpr hdE)
  have hEqE : (algebraMap K E x) * e p d = e p b := by
    change (algebraMap K E x) * (algebraMap K E dK) = algebraMap K E bK
    rw [<- map_mul, hEqK]
  change V (a p - algebraMap K E x) <= 1
  apply le_of_mul_le_mul_right ?_ hdV
  rw [one_mul, <- map_mul, sub_mul, hEqE, V.map_sub_swap]
  exact hb p

/-- The set of finite adeles that are integral at every place is compact. -/
theorem isCompact_integralFiniteAdeles :
    IsCompact {a : FiniteAdeleRing (RingOfIntegers K) K |
      forall p : HeightOneSpectrum (RingOfIntegers K),
        Membership.mem (p.adicCompletionIntegers K) (a p)} := by
  let P := HeightOneSpectrum (RingOfIntegers K)
  let A := FiniteAdeleRing (RingOfIntegers K) K
  let O (p : P) := (p.adicCompletionIntegers K : Set (p.adicCompletion K))
  let f : (forall p : P, p.adicCompletionIntegers K) -> A :=
    RestrictedProduct.structureMap (fun p : P => p.adicCompletion K) O Filter.cofinite
  have hEmbed : Topology.IsEmbedding f :=
    RestrictedProduct.isEmbedding_structureMap (R := fun p : P => p.adicCompletion K) (A := O)
  have hCont : Continuous f := hEmbed.continuous
  have hRange : Set.range f =
      {a : A | forall p : P, Membership.mem (p.adicCompletionIntegers K) (a p)} := by
    ext a
    constructor
    case mp =>
      intro ha
      choose b hb using ha
      rw [<- hb]
      intro p
      exact (b p).property
    case mpr =>
      intro ha
      let b : forall p : P, p.adicCompletionIntegers K :=
        fun p => Subtype.mk (a p) (ha p)
      refine Exists.intro b ?_
      apply DFunLike.ext
      intro p
      rfl
  rw [<- hRange]
  let localCompact (p : P) : CompactSpace (p.adicCompletionIntegers K) :=
    compactSpace_heckeLocalIntegers p
  exact isCompact_range hCont

/-- The archimedean quotient by the ring of integers has a compact
set of representatives. -/
theorem exists_compact_infiniteAdele_integer_reduction :
    Exists (fun C : Set (InfiniteAdeleRing K) => IsCompact C /\
      forall a : InfiniteAdeleRing K, Exists (fun b : RingOfIntegers K =>
        Membership.mem C (a - algebraMap K (InfiniteAdeleRing K)
          (algebraMap (RingOfIntegers K) K b)))) := by
  classical
  let M := mixedEmbedding.mixedSpace K
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  have hCont : Continuous (fun x : M => e.symm x) := by
    change Continuous (fun x : M => fun w : InfinitePlace K => e.symm x w)
    apply continuous_pi
    intro w
    by_cases hw : w.IsReal
    case pos =>
      let ew := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      have hCoordinate : (fun x : M => e.symm x w) =
          fun x : M => ew.symm (x.1 (Subtype.mk w hw)) := by
        funext x
        apply ew.injective
        rw [ew.apply_symm_apply]
        have hEq := congrArg (fun y : M => y.1 (Subtype.mk w hw)) (e.apply_symm_apply x)
        change (InfiniteAdeleRing.ringEquiv_mixedSpace K (e.symm x)).1
            (Subtype.mk w hw) = x.1 (Subtype.mk w hw) at hEq
        rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hEq
        exact hEq
      rw [hCoordinate]
      exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.comp
        ((continuous_apply (Subtype.mk w hw)).comp continuous_fst)
    case neg =>
      have hComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      let ew := InfinitePlace.Completion.ringEquivComplexOfIsComplex hComplex
      have hCoordinate : (fun x : M => e.symm x w) =
          fun x : M => ew.symm (x.2 (Subtype.mk w hComplex)) := by
        funext x
        apply ew.injective
        rw [ew.apply_symm_apply]
        have hEq := congrArg (fun y : M => y.2 (Subtype.mk w hComplex)) (e.apply_symm_apply x)
        change (InfiniteAdeleRing.ringEquiv_mixedSpace K (e.symm x)).2
            (Subtype.mk w hComplex) = x.2 (Subtype.mk w hComplex) at hEq
        rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hEq
        exact hEq
      rw [hCoordinate]
      exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hComplex).symm.continuous.comp
        ((continuous_apply (Subtype.mk w hComplex)).comp continuous_snd)
  let B := mixedEmbedding.latticeBasis K
  have hBound := ZSpan.fundamentalDomain_isBounded B
  have hRadius := (Metric.isBounded_iff_subset_closedBall (0 : M)).mp hBound
  choose r hr using hRadius
  let C := Set.image (fun x : M => e.symm x) (Metric.closedBall (0 : M) r)
  have hC : IsCompact C := (isCompact_closedBall (0 : M) r).image hCont
  refine Exists.intro C (And.intro hC ?_)
  intro a
  have hExists := (ZSpan.exist_unique_vadd_mem_fundamentalDomain B (e a)).exists
  choose v hv using hExists
  have hBasis : Membership.mem (mixedEmbedding.integerLattice K) (v : M) := by
    rw [<- mixedEmbedding.span_latticeBasis]
    exact v.property
  have hInteger : Exists (fun u : RingOfIntegers K =>
      mixedEmbedding K (algebraMap (RingOfIntegers K) K u) = (v : M)) := hBasis
  choose u hu using hInteger
  refine Exists.intro (-u) ?_
  have hvDomain : Membership.mem (ZSpan.fundamentalDomain B) ((v : M) + e a) := hv
  refine Exists.intro ((v : M) + e a) (And.intro (hr hvDomain) ?_)
  apply e.injective
  rw [e.apply_symm_apply, map_sub, map_neg (algebraMap (RingOfIntegers K) K),
    map_neg, map_neg, sub_neg_eq_add]
  rw [<- InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hu, add_comm]

/-- A compact subset of the additive adele ring meets every coset of
the principal adeles. -/
theorem exists_compact_adele_principal_reduction :
    Exists (fun C : Set (AdeleRing (RingOfIntegers K) K) => IsCompact C /\
      forall a : AdeleRing (RingOfIntegers K) K, Exists (fun x : K =>
        Membership.mem C (a - algebraMap K (AdeleRing (RingOfIntegers K) K) x))) := by
  let R := RingOfIntegers K
  let A := AdeleRing R K
  let AInf := InfiniteAdeleRing K
  let AFin := FiniteAdeleRing R K
  let T : Set AFin := {a | forall p : HeightOneSpectrum R,
    Membership.mem (p.adicCompletionIntegers K) (a p)}
  have hT : IsCompact T := isCompact_integralFiniteAdeles
  have hInf := exists_compact_infiniteAdele_integer_reduction (K := K)
  choose C hC using hInf
  refine Exists.intro (Set.prod C T) (And.intro (hC.1.prod hT) ?_)
  intro a
  have hFinRep := exists_finiteAdele_sub_principal_integral a.2
  choose x hx using hFinRep
  let b : A := a - algebraMap K A x
  have hInfRep := hC.2 b.1
  choose y hy using hInfRep
  refine Exists.intro (x + algebraMap R K y) ?_
  have hDecomp : a - algebraMap K A (x + algebraMap R K y) =
      b - algebraMap K A (algebraMap R K y) := by
    rw [map_add, sub_sub]
  rw [hDecomp]
  refine And.intro hy ?_
  intro p
  exact (p.adicCompletionIntegers K).toSubring.sub_mem (hx p)
    (HeightOneSpectrum.coe_algebraMap_mem R K p y)

/-- The adelic additive quotient by the diagonal number field is compact. -/
theorem compactSpace_adeleModuloPrincipal :
    CompactSpace (HasQuotient.Quotient (AdeleRing (RingOfIntegers K) K)
      (AdeleRing.principalSubgroup (RingOfIntegers K) K)) := by
  let R := RingOfIntegers K
  let A := AdeleRing R K
  let H := AdeleRing.principalSubgroup R K
  let Q := HasQuotient.Quotient A H
  let f : A -> Q := QuotientAddGroup.mk' H
  have hContinuous : Continuous f := QuotientAddGroup.continuous_mk
  have h := exists_compact_adele_principal_reduction (K := K)
  choose C hC using h
  have hImage : Set.image f C = (Set.univ : Set Q) := by
    ext z
    refine Iff.intro (fun _ => Set.mem_univ _) ?_
    intro _
    have hSurj : Function.Surjective f := QuotientAddGroup.mk_surjective
    choose a ha using hSurj z
    choose x hx using hC.2 a
    refine Exists.intro (a - algebraMap K A x) (And.intro hx ?_)
    rw [<- ha]
    change (QuotientAddGroup.mk' H) (a - algebraMap K A x) =
      (QuotientAddGroup.mk' H) a
    have hZero : (QuotientAddGroup.mk' H) (algebraMap K A x) = 0 :=
      (QuotientAddGroup.eq_zero_iff (algebraMap K A x)).mpr (Exists.intro x rfl)
    rw [map_sub, hZero, sub_zero]
  refine CompactSpace.mk ?_
  rw [<- hImage]
  exact hC.1.image hContinuous

end Cocompactness

end Robin1984.GRH
