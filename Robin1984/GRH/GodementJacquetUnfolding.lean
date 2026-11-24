import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Robin1984.GRH.GodementJacquetFundamentalDomain

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Godement and Jacquet, Zeta Functions of Simple Algebras, and the global matrix-coefficient zeta integral.
- Formalization note: Unfolds the weighted adelic integral into the double theta integral over determinant-one fundamental domains under absolute integrability.
- PROVENANCE-END
-/

/-!
# Unfolding the Godement-Jacquet zeta integral

At each determinant value, a fundamental domain for the rational subgroup
replaces integration by a rational matrix sum. Left invariance and Fubini
then express the matrix-coefficient zeta integral as a double quotient
integral and a logarithmic Mellin transform.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

open NumberField MeasureTheory Topology

section RankCoordinates

variable {R S m : Type*} [CommRing R] [CommRing S] [Fintype m] [DecidableEq m]
variable {r k : Nat}

private abbrev RankBlockGL (R : Type*) [CommRing R] (r k : Nat) :=
  Matrix.GeneralLinearGroup (Sum (Fin r) (Fin k)) R

theorem godementJacquetRankTransport_val
    (e : Equiv m (Sum (Fin r) (Fin k))) (a : Matrix.GeneralLinearGroup m R)
    (u : RankBlockGL R r k) :
    (godementJacquetRankTransport e a u).val = a.inv * u.val.submatrix e e * a.val := by
  change ((MulAut.conj (Inv.inv a))
      ((Units.mapEquiv (Matrix.reindexRingEquiv (R := R) e.symm).toMulEquiv) u)).val = _
  rw [MulAut.conj_apply, inv_inv]
  rfl

theorem godementJacquetRankTransport_det
    (e : Equiv m (Sum (Fin r) (Fin k))) (a : Matrix.GeneralLinearGroup m R)
    (u : RankBlockGL R r k) :
    Matrix.GeneralLinearGroup.det (godementJacquetRankTransport e a u) =
      Matrix.GeneralLinearGroup.det u := by
  let v := (Units.mapEquiv (Matrix.reindexRingEquiv (R := R) e.symm).toMulEquiv) u
  have hv : Matrix.GeneralLinearGroup.det v = Matrix.GeneralLinearGroup.det u := by
    apply Units.ext
    exact Matrix.det_submatrix_equiv_self e u.val
  change Matrix.GeneralLinearGroup.det ((MulAut.conj (Inv.inv a)) v) = _
  rw [MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv, hv]
  rw [mul_comm (Inv.inv (Matrix.GeneralLinearGroup.det a)), mul_assoc, inv_mul_cancel, mul_one]

theorem godementJacquetRankTransport_map
    (f : RingHom R S) (e : Equiv m (Sum (Fin r) (Fin k)))
    (a : Matrix.GeneralLinearGroup m R) (u : RankBlockGL R r k) :
    Matrix.GeneralLinearGroup.map f (godementJacquetRankTransport e a u) =
      godementJacquetRankTransport e (Matrix.GeneralLinearGroup.map f a)
        (Matrix.GeneralLinearGroup.map f u) := by
  apply Units.ext
  let fm : RingHom (Matrix m m R) (Matrix m m S) := RingHom.mapMatrix f
  change fm (godementJacquetRankTransport e a u).val = _
  rw [godementJacquetRankTransport_val, godementJacquetRankTransport_val, map_mul, map_mul]
  rfl

theorem godementJacquetUpperUnipotent_map
    (f : RingHom R S) (B : Matrix (Fin r) (Fin k) R) :
    Matrix.GeneralLinearGroup.map f (godementJacquetUpperUnipotent B) =
      godementJacquetUpperUnipotent (B.map f) := by
  apply Units.ext
  change (Matrix.fromBlocks 1 B 0 1).map f = Matrix.fromBlocks 1 (B.map f) 0 1
  rw [Matrix.fromBlocks_map]
  simp

end RankCoordinates

section AdelicUnipotent

variable {K : Type*} [Field K] [NumberField K] {n r k : Nat}

private abbrev Adeles (K : Type*) [Field K] [NumberField K] :=
  AdeleRing (RingOfIntegers K) K
private abbrev Blocks (K : Type*) [Field K] [NumberField K] (r k : Nat) :=
  Matrix (Fin r) (Fin k) (Adeles K)

/-- The adelic upper unipotent translations in the coordinates of a
singular rational matrix act by determinant-norm-one matrices. -/
def godementJacquetAdelicUnipotent
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a : Matrix.GeneralLinearGroup (Fin n) K) :
    MonoidHom (Multiplicative (Blocks K r k)) (adelicDeterminantLogNorm K n).ker := by
  let aA := Matrix.GeneralLinearGroup.map (algebraMap K (Adeles K)) a
  let u := (godementJacquetRankTransport e aA).toMonoidHom.comp
    (godementJacquetUpperUnipotentHom (R := Adeles K) (r := r) (k := k))
  refine u.codRestrict (adelicDeterminantLogNorm K n).ker ?_
  intro B
  have hDet : Matrix.GeneralLinearGroup.det (u B) = 1 :=
    (godementJacquetRankTransport_det e aA _).trans
      (godementJacquetUpperUnipotent_det (Multiplicative.toAdd B))
  change Real.log (heckeIdelicNorm (Matrix.GeneralLinearGroup.det (u B))) = 0
  rw [hDet, map_one, Real.log_one]

theorem godementJacquetAdelicUnipotent_principal
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a : Matrix.GeneralLinearGroup (Fin n) K) (B : Matrix (Fin r) (Fin k) K) :
    godementJacquetAdelicUnipotent e a (Multiplicative.ofAdd (B.map (algebraMap K (Adeles K)))) =
      godementJacquetPrincipalRankTransport e a (godementJacquetUpperUnipotent B) := by
  apply Subtype.ext
  let f := algebraMap K (Adeles K)
  change godementJacquetRankTransport e (Matrix.GeneralLinearGroup.map f a)
      (godementJacquetUpperUnipotent (B.map f)) =
    Matrix.GeneralLinearGroup.map f (godementJacquetRankTransport e a (godementJacquetUpperUnipotent B))
  rw [godementJacquetRankTransport_map, godementJacquetUpperUnipotent_map]

/-- The rational subgroup of the adelic translations is exactly the
rational unipotent factor of the transported stabilizer. -/
theorem mem_godementJacquetPrincipalUnipotent_iff
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a : Matrix.GeneralLinearGroup (Fin n) K)
    (x : (adelicDeterminantLogNorm K n).ker) :
    Membership.mem ((godementJacquetProjectionUnipotent K r k).map
      (godementJacquetPrincipalRankTransport e a)) x <->
    Exists (fun B : Blocks K r k => And (Membership.mem (godementJacquetPrincipalMatrixBlock K r k) B)
      (godementJacquetAdelicUnipotent e a (Multiplicative.ofAdd B) = x)) := by
  let f := algebraMap K (Adeles K)
  constructor
  . intro hx
    choose u hu using hx
    choose B hB using hu.1
    refine Exists.intro ((Multiplicative.toAdd B).map f) (And.intro ?_ ?_)
    . exact (mem_godementJacquetPrincipalMatrixBlock K r k _).mpr
        (Exists.intro (Multiplicative.toAdd B) rfl)
    . rw [godementJacquetAdelicUnipotent_principal]
      change godementJacquetUpperUnipotent (Multiplicative.toAdd B) = u at hB
      rw [hB]
      exact hu.2
  . intro hx
    choose C hC using hx
    choose B hB using (mem_godementJacquetPrincipalMatrixBlock K r k C).mp hC.1
    refine Exists.intro (godementJacquetUpperUnipotent B) (And.intro ?_ ?_)
    . exact Exists.intro (Multiplicative.ofAdd B) rfl
    . rw [<- godementJacquetAdelicUnipotent_principal, hB]
      exact hC.2

theorem continuous_godementJacquetAdelicUnipotent
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a : Matrix.GeneralLinearGroup (Fin n) K) :
    Continuous (fun B : Blocks K r k => godementJacquetAdelicUnipotent e a (Multiplicative.ofAdd B)) := by
  let aA := Matrix.GeneralLinearGroup.map (algebraMap K (Adeles K)) a
  let u := (godementJacquetRankTransport e aA).toMonoidHom.comp
    (godementJacquetUpperUnipotentHom (R := Adeles K) (r := r) (k := k))
  have hEntries : Continuous (fun B : Blocks K r k => (godementJacquetUpperUnipotent B).val) := by
    refine continuous_pi (fun i => continuous_pi (fun j => ?_))
    cases i <;> cases j
    . exact continuous_const
    . rename_i i j
      change Continuous (fun B : Blocks K r k => B i j)
      exact (continuous_apply j).comp (continuous_apply i)
    . exact continuous_const
    . exact continuous_const
  have hSub : Continuous (fun B : Blocks K r k => (godementJacquetUpperUnipotent B).val.submatrix e e) :=
    continuous_pi (fun i => continuous_pi (fun j =>
      (continuous_apply (e j)).comp ((continuous_apply (e i)).comp hEntries)))
  have hv : Continuous (fun B : Blocks K r k => (u (Multiplicative.ofAdd B)).val) := by
    change Continuous (fun B : Blocks K r k =>
      (godementJacquetRankTransport e aA (godementJacquetUpperUnipotent B)).val)
    simp_rw [godementJacquetRankTransport_val]
    exact (continuous_const.mul hSub).mul continuous_const
  have hi : Continuous (fun B : Blocks K r k => (Inv.inv (u (Multiplicative.ofAdd B))).val) := by
    simp_rw [<- map_inv]
    exact hv.comp continuous_neg
  have hu : Continuous (fun B : Blocks K r k => u (Multiplicative.ofAdd B)) :=
    Units.continuous_iff.mpr (And.intro hv hi)
  exact hu.subtype_mk _

private abbrev NormGroup (K : Type*) [Field K] [NumberField K] (n : Nat) :=
  (adelicDeterminantLogNorm K n).ker

private abbrev RationalUnipotent
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a : Matrix.GeneralLinearGroup (Fin n) K) : Subgroup (NormGroup K n) :=
  (godementJacquetProjectionUnipotent K r k).map (godementJacquetPrincipalRankTransport e a)

private abbrev RationalUnipotentOrbits
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a : Matrix.GeneralLinearGroup (Fin n) K) :=
  Quotient (MulAction.orbitRel (RationalUnipotent e a) (NormGroup K n))

private abbrev UnipotentClasses (K : Type*) [Field K] [NumberField K] (r k : Nat) :=
  GodementJacquetUnipotentClassGroup K r k

/-- The actual compact unipotent quotient acts jointly measurably on
rational unipotent orbits and preserves their quotient measure. -/
theorem exists_godementJacquetUnipotentOrbitAction
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a : Matrix.GeneralLinearGroup (Fin n) K)
    [MeasurableSpace (NormGroup K n)] [BorelSpace (NormGroup K n)]
    [MeasurableSpace (UnipotentClasses K r k)] [BorelSpace (UnipotentClasses K r k)]
    (mu : Measure (NormGroup K n)) [mu.IsMulLeftInvariant]
    (W : Set (NormGroup K n)) (hW : MeasurableSet W)
    (hUnique : forall g : NormGroup K n, ExistsUnique
      (fun u : RationalUnipotent e a => Membership.mem W (u.val * g))) :
    let q := Quotient.mk (MulAction.orbitRel (RationalUnipotent e a) (NormGroup K n))
    let D := godementJacquetPrincipalMatrixBlock K r k
    let nu := (mu.restrict W).map q
    Exists (fun act : MulAction (UnipotentClasses K r k) (RationalUnipotentOrbits e a) =>
      And (forall (B : Blocks K r k) (g : NormGroup K n),
          act.smul (Multiplicative.ofAdd (QuotientAddGroup.mk' D B)) (q g) =
          q (godementJacquetAdelicUnipotent e a (Multiplicative.ofAdd B) * g))
        (And (Measurable (fun p : Prod (UnipotentClasses K r k) (RationalUnipotentOrbits e a) =>
            act.smul p.1 p.2))
          (forall c : UnipotentClasses K r k, MeasurePreserving (act.smul c) nu nu))) := by
  let U := RationalUnipotent e a
  let X := RationalUnipotentOrbits e a
  let q := Quotient.mk (MulAction.orbitRel U (NormGroup K n))
  let D := godementJacquetPrincipalMatrixBlock K r k
  let C := UnipotentClasses K r k
  let P := HasQuotient.Quotient (Blocks K r k) D
  let alpha := godementJacquetAdelicUnipotent e a
  let : SecondCountableTopology (AdelicGeneralLinearGroup K n) :=
    secondCountableTopology_adelicGeneralLinearGroup K n
  let : SecondCountableTopology (NormGroup K n) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      (fun g : NormGroup K n => g.val)).secondCountableTopology
  let : DiscreteTopology U :=
    discreteTopology_godementJacquetPrincipalRankSubgroup e a (godementJacquetProjectionUnipotent K r k)
  let : Countable U := countable_of_Lindelof_of_discrete
  have hMul : Measurable (fun p : Prod (NormGroup K n) (NormGroup K n) => p.1 * p.2) :=
    (continuous_fst.mul continuous_snd).measurable
  have hNorm (B : Multiplicative (Blocks K r k)) (u : U) :
      Membership.mem U (alpha B * u.val * Inv.inv (alpha B)) := by
    choose d hd using (mem_godementJacquetPrincipalUnipotent_iff e a u.val).mp u.property
    rw [<- hd.2]
    change Membership.mem U (alpha B * alpha (Multiplicative.ofAdd d) * Inv.inv (alpha B))
    rw [<- map_inv, <- map_mul, <- map_mul, mul_comm B (Multiplicative.ofAdd d),
      mul_assoc, mul_inv_cancel, mul_one]
    rw [show alpha (Multiplicative.ofAdd d) = u.val from hd.2]
    exact u.property
  have hRat (B : Blocks K r k) (hB : Membership.mem D B) :
      Membership.mem U (alpha (Multiplicative.ofAdd B)) :=
    (mem_godementJacquetPrincipalUnipotent_iff e a _).mpr
      (Exists.intro B (And.intro hB rfl))
  choose act hAct using exists_leftOrbitAddQuotientMulAction D U alpha hNorm hRat
  let : MeasurableSpace (Blocks K r k) := borel _
  let : BorelSpace (Blocks K r k) := BorelSpace.mk rfl
  let : MeasurableSpace C := inferInstanceAs (MeasurableSpace (UnipotentClasses K r k))
  let : MeasurableSpace P := show MeasurableSpace C from inferInstance
  let : BorelSpace P := show BorelSpace C from inferInstance
  choose sA hsA using exists_measurable_godementJacquetUnipotentRepresentative K r k
  choose sX hsX using exists_measurable_leftOrbitSection U W hW hUnique
  refine Exists.intro act (And.intro hAct (And.intro ?_ ?_))
  . change Measurable (fun p : Prod C X => act.smul p.1 p.2)
    exact measurable_leftOrbitAddQuotientMulAction
      (continuous_godementJacquetAdelicUnipotent e a).measurable hMul act hAct
      sA hsA.1 hsA.2 sX hsX.1 hsX.2
  . intro c
    exact measurePreserving_leftOrbitAddQuotientMulAction alpha hNorm act hAct
      mu W hW hUnique c

end AdelicUnipotent

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

private abbrev DeterminantOne :=
  (adelicDeterminantLogNorm K n).ker

private abbrev PrincipalDeterminantOne :=
  (adelicPrincipalDeterminantOne K n).range

/-- The rational principal subgroup in the determinant-one group is countable. -/
theorem countable_adelicPrincipalDeterminantOne : Countable (PrincipalDeterminantOne K n) := by
  let E := (Module.finBasis Rat K).equivFun
  let _ : Countable K := E.injective.countable
  let _ : Countable (Matrix (Fin n) (Fin n) K) := by
    change Countable (Fin n -> Fin n -> K)
    infer_instance
  let _ : Countable (Matrix.GeneralLinearGroup (Fin n) K) :=
    Units.val_injective.countable
  let P := adelicPrincipalDeterminantOne K n
  have h : Function.Surjective P.rangeRestrict := by
    intro a
    choose b hb using a.property
    exact Exists.intro b (Subtype.ext hb)
  exact h.countable

section Unfolding

variable [MeasurableSpace (DeterminantOne K n)] [BorelSpace (DeterminantOne K n)]

/-- At one logarithmic determinant value, the rational subgroup unfolds over its fundamental domain. -/
theorem integral_adelicGodementJacquetSlice_eq_theta
    (mu : Measure (DeterminantOne K n)) [mu.IsMulLeftInvariant]
    {D : Set (DeterminantOne K n)}
    (hD : IsFundamentalDomain (PrincipalDeterminantOne K n) D mu)
    (t : Real) (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (c : AdelicGeneralLinearGroup K n -> Complex)
    (hc : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      c (adelicPrincipalGeneralLinear K n a * g) = c g)
    (hInt : Integrable (fun k : DeterminantOne K n =>
      let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
      Phi ((z * k.val).val) * c (z * k.val)) mu) :
    let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
    integral mu (fun k : DeterminantOne K n => Phi ((z * k.val).val) * c (z * k.val)) =
      integral (mu.restrict D) (fun k : DeterminantOne K n =>
        (tsum (fun a : PrincipalDeterminantOne K n => Phi ((a.val.val * (z * k.val)).val))) *
          c (z * k.val)) := by
  let _ : Countable (PrincipalDeterminantOne K n) := countable_adelicPrincipalDeterminantOne K n
  let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let f : DeterminantOne K n -> Complex := fun k => Phi ((z * k.val).val) * c (z * k.val)
  have hmove (a : PrincipalDeterminantOne K n) (k : DeterminantOne K n) :
      z * (SMul.smul a k).val = a.val.val * (z * k.val) := by
    change z * (a.val.val * k.val) = a.val.val * (z * k.val)
    rw [<- mul_assoc, (adelicDeterminantSection_commute K n (Multiplicative.ofAdd t) a.val.val).eq,
      mul_assoc]
  have hinvariant (a : PrincipalDeterminantOne K n) (k : DeterminantOne K n) :
      c (a.val.val * (z * k.val)) = c (z * k.val) := by
    choose p hp using a.property
    have hp' : adelicPrincipalGeneralLinear K n p = a.val.val := congrArg Subtype.val hp
    rw [<- hp']
    exact hc p _
  have hTheta (k : DeterminantOne K n) :
      tsum (fun a : PrincipalDeterminantOne K n => f (SMul.smul a k)) =
        (tsum (fun a : PrincipalDeterminantOne K n => Phi ((a.val.val * (z * k.val)).val))) *
          c (z * k.val) := by
    simp only [f, hmove, hinvariant, tsum_mul_right]
  change integral mu f = _
  calc
    integral mu f = tsum (fun a : PrincipalDeterminantOne K n =>
        integral (mu.restrict D) (fun k => f (SMul.smul a k))) :=
      hD.integral_eq_tsum'' f hInt
    _ = integral (mu.restrict D) (fun k =>
        tsum (fun a : PrincipalDeterminantOne K n => f (SMul.smul a k))) := by
      symm
      rw [integral_tsum]
      . exact fun a => (hInt.1.comp_quasiMeasurePreserving
          (measurePreserving_smul a mu).quasiMeasurePreserving).restrict
      . intro hInfinite
        exact (ne_of_lt hInt.2) ((hD.lintegral_eq_tsum'' (fun k => enorm (f k))).trans hInfinite)
    _ = _ := by simp only [hTheta, z]

/-- The full weighted integral is the Mellin transform of the rational
matrix sum over a fundamental domain of the determinant-one group. -/
theorem integral_adelicGodementJacquet_eq_thetaMellin
    [MeasurableSpace (AdelicGeneralLinearGroup K n)] [BorelSpace (AdelicGeneralLinearGroup K n)]
    (hn : 0 < n) (mu : Measure (DeterminantOne K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    {D : Set (DeterminantOne K n)} (hD : IsFundamentalDomain (PrincipalDeterminantOne K n) D mu)
    (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (c : AdelicGeneralLinearGroup K n -> Complex) (s : Complex)
    (hc : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      c (adelicPrincipalGeneralLinear K n a * g) = c g)
    (hInt : Integrable (fun g : AdelicGeneralLinearGroup K n =>
      (Phi g.val * c g) * (adelicDeterminantNorm K n g : Complex) ^
        (s + ((n : Complex) - 1) / 2)) (adelicDeterminantProductMeasure K n hn mu)) :
    integral (adelicDeterminantProductMeasure K n hn mu)
      (fun g : AdelicGeneralLinearGroup K n => (Phi g.val * c g) *
        (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)) =
      integral (volume : Measure Real) (fun t : Real =>
        let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
        (integral (mu.restrict D) (fun k : DeterminantOne K n =>
          (tsum (fun a : PrincipalDeterminantOne K n => Phi ((a.val.val * (z * k.val)).val))) *
            c (z * k.val))) *
          Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2))) := by
  let e := (adelicDeterminantHomeomorph K n hn).toMeasurableEquiv
  let f : AdelicGeneralLinearGroup K n -> Complex := fun g =>
    (Phi g.val * c g) * (adelicDeterminantNorm K n g : Complex) ^
      (s + ((n : Complex) - 1) / 2)
  have hPull : Integrable (fun p => f (e p)) ((volume : Measure Real).prod mu) :=
    (integrable_map_equiv e f).mp hInt
  rw [integral_adelicGodementJacquet_eq_logMellin K n hn mu Phi c s hInt]
  apply integral_congr_ae
  filter_upwards [hPull.prod_right_ae] with t ht
  let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
  let w := Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2))
  have hSlice : Integrable (fun k : DeterminantOne K n =>
      Phi ((z * k.val).val) * c (z * k.val)) mu := by
    apply (ht.mul_const (Inv.inv w)).congr
    refine Filter.Eventually.of_forall (fun k => ?_)
    have hw : (adelicDeterminantNorm K n (e (Prod.mk t k)) : Complex) ^
        (s + ((n : Complex) - 1) / 2) = w :=
      adelicGodementJacquetWeight_coordinates K n hn (Multiplicative.ofAdd t) k s
    change (Phi ((z * k.val).val) * c (z * k.val)) *
      (adelicDeterminantNorm K n (e (Prod.mk t k)) : Complex) ^
        (s + ((n : Complex) - 1) / 2) * Inv.inv w = _
    rw [hw]
    have hw0 : Not (w = 0) := Complex.exp_ne_zero _
    field_simp
  exact congrArg (fun x : Complex => x * w)
    (integral_adelicGodementJacquetSlice_eq_theta K n mu hD t Phi c hc hSlice)

end Unfolding

section MatrixCoefficient

variable [MeasurableSpace (AdelicGeneralLinearGroup K n)]
  [BorelSpace (AdelicGeneralLinearGroup K n)]
  [MeasurableSpace (DeterminantOne K n)]

/-- The quotient matrix-coefficient integral unfolds by Fubini and left
translation on the determinant-one group. -/
theorem integral_adelicGodementJacquetMatrixCoeff_eq_unfolded
    (mu : Measure (AdelicGeneralLinearGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (nu : Measure (DeterminantOne K n)) [SFinite nu]
    (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (phi : AdelicGeneralLinearGroup K n -> Complex)
    (psi : DeterminantOne K n -> Complex) (s : Complex)
    (hInt : Integrable (fun p : Prod (AdelicGeneralLinearGroup K n) (DeterminantOne K n) =>
      (Phi p.1.val * (phi (p.2.val * p.1) * psi p.2)) *
        (adelicDeterminantNorm K n p.1 : Complex) ^ (s + ((n : Complex) - 1) / 2))
      (mu.prod nu)) :
    let w : AdelicGeneralLinearGroup K n -> Complex := fun g =>
      (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)
    integral mu (fun g => (Phi g.val * integral nu (fun k => phi (k.val * g) * psi k)) * w g) =
      integral nu (fun k =>
        (integral mu (fun g => (Phi ((Inv.inv k.val * g).val) * phi g) * w g)) * psi k) := by
  let w : AdelicGeneralLinearGroup K n -> Complex := fun g =>
    (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)
  let f : Prod (AdelicGeneralLinearGroup K n) (DeterminantOne K n) -> Complex :=
    fun p => (Phi p.1.val * (phi (p.2.val * p.1) * psi p.2)) * w p.1
  have hNorm (k : DeterminantOne K n) : adelicDeterminantNorm K n k.val = 1 := by
    have hLog : Real.log (adelicDeterminantNorm K n k.val) = 0 := k.property
    rw [<- Real.exp_log (adelicDeterminantNorm_pos K n k.val), hLog, Real.exp_zero]
  have hLeft (g : AdelicGeneralLinearGroup K n) :
      (Phi g.val * integral nu (fun k => phi (k.val * g) * psi k)) * w g =
        integral nu (fun k => f (Prod.mk g k)) := by
    rw [<- integral_const_mul, <- integral_mul_const]
  have hRight (k : DeterminantOne K n) :
      integral mu (fun g => f (Prod.mk g k)) =
        (integral mu (fun g => (Phi ((Inv.inv k.val * g).val) * phi g) * w g)) * psi k := by
    let F : AdelicGeneralLinearGroup K n -> Complex :=
      fun g => ((Phi ((Inv.inv k.val * g).val) * phi g) * w g) * psi k
    calc
      integral mu (fun g => f (Prod.mk g k)) =
          integral mu (fun g => F (k.val * g)) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun g => ?_)
        dsimp only [f, F, w]
        rw [<- mul_assoc (Inv.inv k.val) k.val g, inv_mul_cancel, one_mul,
          map_mul, hNorm k, one_mul]
        ac_rfl
      _ = integral mu F := integral_mul_left_eq_self F k.val
      _ = _ := by exact integral_mul_const _ _
  change integral mu
      (fun g => (Phi g.val * integral nu (fun k => phi (k.val * g) * psi k)) * w g) =
    integral nu
      (fun k => (integral mu (fun g => (Phi ((Inv.inv k.val * g).val) * phi g) * w g)) * psi k)
  calc
    _ = integral mu (fun g => integral nu (fun k => f (Prod.mk g k))) := by simp only [hLeft]
    _ = integral nu (fun k => integral mu (fun g => f (Prod.mk g k))) :=
      integral_integral_swap (f := fun g k => f (Prod.mk g k)) hInt
    _ = _ := by simp only [hRight]

/-- A quotient matrix coefficient gives the double quotient theta
integral, with the same logarithmic Mellin weight as the original zeta integral. -/
theorem integral_adelicGodementJacquet_eq_doubleThetaMellin
    [BorelSpace (DeterminantOne K n)] (hn : 0 < n)
    (mu : Measure (DeterminantOne K n)) [SFinite mu] [mu.IsHaarMeasure]
    {D : Set (DeterminantOne K n)} (hD : IsFundamentalDomain (PrincipalDeterminantOne K n) D mu)
    (Phi : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex)
    (phi : AdelicGeneralLinearGroup K n -> Complex)
    (psi : DeterminantOne K n -> Complex) (s : Complex)
    (hc : forall (a : Matrix.GeneralLinearGroup (Fin n) K) g,
      phi (adelicPrincipalGeneralLinear K n a * g) = phi g)
    (hInt : Integrable (fun p : Prod (AdelicGeneralLinearGroup K n) (DeterminantOne K n) =>
      (Phi p.1.val * (phi (p.2.val * p.1) * psi p.2)) *
        (adelicDeterminantNorm K n p.1 : Complex) ^ (s + ((n : Complex) - 1) / 2))
      ((adelicDeterminantProductMeasure K n hn mu).prod (mu.restrict D))) :
    let M := adelicDeterminantProductMeasure K n hn mu
    let nu := mu.restrict D
    integral M (fun g =>
      (Phi g.val * integral nu (fun h => phi (h.val * g) * psi h)) *
        (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)) =
      integral nu (fun h =>
        (integral (volume : Measure Real) (fun t : Real =>
          let z := adelicDeterminantSection K n (Multiplicative.ofAdd t)
          (integral nu (fun k : DeterminantOne K n =>
            (tsum (fun a : PrincipalDeterminantOne K n =>
              Phi ((Inv.inv h.val * (a.val.val * (z * k.val))).val))) * phi (z * k.val))) *
            Complex.exp ((t : Complex) * (s + ((n : Complex) - 1) / 2)))) * psi h) := by
  let M := adelicDeterminantProductMeasure K n hn mu
  let nu := mu.restrict D
  let _ : SFinite M := by
    change SFinite (Measure.map (adelicDeterminantHomeomorph K n hn) ((volume : Measure Real).prod mu))
    infer_instance
  let _ : M.IsHaarMeasure := isHaarMeasure_adelicDeterminantProductMeasure K n hn mu
  let w : AdelicGeneralLinearGroup K n -> Complex := fun g =>
    (adelicDeterminantNorm K n g : Complex) ^ (s + ((n : Complex) - 1) / 2)
  let f : Prod (AdelicGeneralLinearGroup K n) (DeterminantOne K n) -> Complex :=
    fun p => (Phi p.1.val * (phi (p.2.val * p.1) * psi p.2)) * w p.1
  have hProduct : Integrable f (M.prod nu) := hInt
  change integral M (fun g =>
      (Phi g.val * integral nu (fun h => phi (h.val * g) * psi h)) * w g) = _
  rw [integral_adelicGodementJacquetMatrixCoeff_eq_unfolded K n M nu Phi phi psi s hProduct]
  apply integral_congr_ae
  filter_upwards [hProduct.prod_left_ae] with h hh
  by_cases hzero : psi h = 0
  . simp only [hzero, mul_zero]
  . let shifted : Matrix (Fin n) (Fin n) (AdeleRing (RingOfIntegers K) K) -> Complex :=
      fun X => Phi ((Inv.inv h.val).val * X)
    have hLog : Real.log (adelicDeterminantNorm K n h.val) = 0 := h.property
    have hNorm : adelicDeterminantNorm K n h.val = 1 := by
      rw [<- Real.exp_log (adelicDeterminantNorm_pos K n h.val), hLog, Real.exp_zero]
    have hmp := measurePreserving_mul_left M (Inv.inv h.val)
    have hTranslated := hmp.integrable_comp_of_integrable hh
    have hShifted : Integrable (fun g : AdelicGeneralLinearGroup K n =>
        (shifted g.val * phi g) * w g) M := by
      apply (hTranslated.mul_const (Inv.inv (psi h))).congr
      refine Filter.Eventually.of_forall (fun g => ?_)
      change (shifted g.val * (phi (h.val * (Inv.inv h.val * g)) * psi h)) *
        w (Inv.inv h.val * g) * Inv.inv (psi h) = _
      have hwg : w (Inv.inv h.val * g) = w g := by
        change (adelicDeterminantNorm K n (Inv.inv h.val * g) : Complex) ^ _ = w g
        rw [map_mul, map_inv, hNorm, inv_one, one_mul]
      rw [<- mul_assoc h.val, mul_inv_cancel, one_mul, hwg]
      calc
        _ = ((shifted g.val * phi g) * w g) * (psi h * Inv.inv (psi h)) := by ac_rfl
        _ = _ := by field_simp
    exact congrArg (fun x : Complex => x * psi h)
      (integral_adelicGodementJacquet_eq_thetaMellin K n hn mu hD shifted phi s hc hShifted)

end MatrixCoefficient

end Robin1984.GRH
