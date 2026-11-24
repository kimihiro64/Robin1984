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

For a singular matrix of positive rank, its rational stabilizer splits
into a unipotent group and a Levi group. The compact unipotent average
of the cusp form gives cancellation on the stabilizer quotient.
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

section BlockLeviScalars

variable {R S : Type*} [CommRing R] [CommRing S] {r k : Nat}

theorem godementJacquetBlockLevi_map (f : RingHom R S)
    (V : Matrix.GeneralLinearGroup (Fin k) R) :
    Matrix.GeneralLinearGroup.map f (godementJacquetBlockLevi (r := r) V) =
      godementJacquetBlockLevi (r := r) (Matrix.GeneralLinearGroup.map f V) := by
  apply Units.ext
  change (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) R) 0 0 V.val).map f =
    Matrix.fromBlocks 1 0 0 (V.val.map f)
  rw [Matrix.fromBlocks_map]
  simp

end BlockLeviScalars

section LeviOnUnipotentOrbits

variable {K : Type*} [Field K] [NumberField K] {n r k : Nat}

/-- Conjugation by the inverse rational Levi element on adelic upper
unipotents acts by right multiplication by the Levi block. -/
theorem godementJacquetAdelicUnipotent_levi_conj
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k))) (a : Matrix.GeneralLinearGroup (Fin n) K)
    (V : Matrix.GeneralLinearGroup (Fin k) K) (B : Blocks K r k) :
    let l := godementJacquetPrincipalRankTransport e a (godementJacquetBlockLevi (r := r) V)
    let va := Matrix.GeneralLinearGroup.map (algebraMap K (Adeles K)) V
    Inv.inv l * godementJacquetAdelicUnipotent e a (Multiplicative.ofAdd B) * l =
      godementJacquetAdelicUnipotent e a (Multiplicative.ofAdd (B * va.val)) := by
  let f := algebraMap K (Adeles K)
  let va := Matrix.GeneralLinearGroup.map f V
  let aa := Matrix.GeneralLinearGroup.map f a
  let T := (godementJacquetRankTransport e aa).toMonoidHom
  let lv := godementJacquetBlockLevi (r := r) V
  let u := godementJacquetUpperUnipotent (R := Adeles K) (r := r) (k := k)
  apply Subtype.ext
  change Inv.inv (Matrix.GeneralLinearGroup.map f (godementJacquetRankTransport e a lv)) *
      T (u B) * Matrix.GeneralLinearGroup.map f (godementJacquetRankTransport e a lv) =
    T (u (B * va.val))
  rw [godementJacquetRankTransport_map, godementJacquetBlockLevi_map]
  change Inv.inv (T (godementJacquetBlockLevi (r := r) va)) * T (u B) *
      T (godementJacquetBlockLevi (r := r) va) = _
  rw [<- map_inv, <- map_mul, <- map_mul]
  apply congrArg T
  have hi : godementJacquetBlockLevi (r := r) (Inv.inv va) =
      Inv.inv (godementJacquetBlockLevi (r := r) va) :=
    map_inv (godementJacquetBlockLeviHom (Adeles K) r k) va
  have h := godementJacquetBlockLevi_upperUnipotent_conj (r := r) (Inv.inv va) B
  rw [hi, inv_inv] at h
  exact h

/-- The class of an adelic upper unipotent block modulo principal blocks. -/
def godementJacquetUnipotentClass (B : Blocks K r k) : UnipotentClasses K r k :=
  Multiplicative.ofAdd (QuotientAddGroup.mk' (godementJacquetPrincipalMatrixBlock K r k) B)

theorem godementJacquetUnipotentClassLeviEquiv_apply_class
    (V : Matrix.GeneralLinearGroup (Fin k) K) (B : Blocks K r k) :
    godementJacquetUnipotentClassLeviEquiv K r k V (godementJacquetUnipotentClass B) =
      godementJacquetUnipotentClass
        (B * (Matrix.GeneralLinearGroup.map (algebraMap K (Adeles K)) V).val) := rfl

private theorem compactUnipotentClass_surjective :
    Function.Surjective (godementJacquetUnipotentClass (K := K) (r := r) (k := k)) := by
  intro c
  choose B hB using QuotientAddGroup.mk'_surjective
    (godementJacquetPrincipalMatrixBlock K r k) (Multiplicative.toAdd c)
  exact Exists.intro B (congrArg Multiplicative.ofAdd hB)

/-- On the compact quotient the inverse Levi action is the action of the inverse block. -/
theorem godementJacquetUnipotentClassLeviEquiv_symm_apply
    (V : Matrix.GeneralLinearGroup (Fin k) K) (c : UnipotentClasses K r k) :
    (godementJacquetUnipotentClassLeviEquiv K r k V).symm c =
      godementJacquetUnipotentClassLeviEquiv K r k (Inv.inv V) c := by
  choose B hB using compactUnipotentClass_surjective c
  rw [<- hB]
  apply (godementJacquetUnipotentClassLeviEquiv K r k V).injective
  rw [MulEquiv.apply_symm_apply, godementJacquetUnipotentClassLeviEquiv_apply_class,
    godementJacquetUnipotentClassLeviEquiv_apply_class]
  apply congrArg godementJacquetUnipotentClass
  rw [map_inv]
  change B = (B * (Matrix.GeneralLinearGroup.map _ V).inv) *
    (Matrix.GeneralLinearGroup.map _ V).val
  rw [Matrix.mul_assoc, Units.inv_val, Matrix.mul_one]

private def compactUnipotentLeviMeasurableEquiv
    [MeasurableSpace (UnipotentClasses K r k)] [BorelSpace (UnipotentClasses K r k)]
    (nu : Measure (UnipotentClasses K r k)) [nu.IsHaarMeasure] [IsProbabilityMeasure nu]
    (V : Matrix.GeneralLinearGroup (Fin k) K) :
    MeasurableEquiv (UnipotentClasses K r k) (UnipotentClasses K r k) where
  toEquiv := (godementJacquetUnipotentClassLeviEquiv K r k V).toEquiv
  measurable_toFun := (measurePreserving_godementJacquetUnipotentClassLeviEquiv K r k V nu).measurable
  measurable_invFun := by
    change Measurable (fun c => (godementJacquetUnipotentClassLeviEquiv K r k V).symm c)
    simp_rw [godementJacquetUnipotentClassLeviEquiv_symm_apply]
    exact (measurePreserving_godementJacquetUnipotentClassLeviEquiv K r k (Inv.inv V) nu).measurable

private abbrev RationalLevi
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k))) (a : Matrix.GeneralLinearGroup (Fin n) K) :=
  (godementJacquetProjectionLevi K r k).map (godementJacquetPrincipalRankTransport e a)

/-- The rational Levi action intertwines compact translations with the
Haar-preserving automorphisms of the compact unipotent group. -/
theorem exists_godementJacquetLeviOrbitCompatibility
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k))) (a : Matrix.GeneralLinearGroup (Fin n) K)
    [MeasurableSpace (NormGroup K n)] [MeasurableMul (NormGroup K n)]
    [MeasurableSpace (UnipotentClasses K r k)] [BorelSpace (UnipotentClasses K r k)]
    (hNorm : forall (l : RationalLevi e a) (u : RationalUnipotent e a),
      Membership.mem (RationalUnipotent e a) (l.val * u.val * Inv.inv l.val))
    (act : MulAction (UnipotentClasses K r k) (RationalUnipotentOrbits e a))
    (hAct : forall (B : Blocks K r k) (g : NormGroup K n),
      let q := Quotient.mk (MulAction.orbitRel (RationalUnipotent e a) (NormGroup K n))
      act.smul (godementJacquetUnipotentClass B) (q g) =
        q (godementJacquetAdelicUnipotent e a (Multiplicative.ofAdd B) * g))
    (nu : Measure (UnipotentClasses K r k)) [nu.IsHaarMeasure] [IsProbabilityMeasure nu] :
    let E := leftOrbitNormalizerSubgroupEquiv (RationalUnipotent e a) (RationalLevi e a) hNorm
    Exists (fun aut : RationalLevi e a -> MeasurableEquiv
        (UnipotentClasses K r k) (UnipotentClasses K r k) =>
      And (forall l, MeasurePreserving (aut l) nu nu)
        (forall (l : RationalLevi e a) (c : UnipotentClasses K r k) (x : RationalUnipotentOrbits e a),
          act.smul c (E l x) = E l (act.smul (aut l c) x))) := by
  let f := godementJacquetPrincipalRankTransport e a
  let L := RationalLevi e a
  let U := RationalUnipotent e a
  let q := Quotient.mk (MulAction.orbitRel U (NormGroup K n))
  let E := leftOrbitNormalizerSubgroupEquiv U L hNorm
  let alpha := godementJacquetAdelicUnipotent e a
  have hLift (l : L) : Exists (fun V : Matrix.GeneralLinearGroup (Fin k) K =>
      f (godementJacquetBlockLevi (r := r) V) = l.val) := by
    have hl := l.property
    choose x hx using hl
    choose V hV using hx.1
    refine Exists.intro V ?_
    change godementJacquetBlockLevi (r := r) V = x at hV
    rw [hV]
    exact hx.2
  choose V hV using hLift
  let aut := fun l : L => compactUnipotentLeviMeasurableEquiv (r := r) nu (V l)
  refine Exists.intro aut (And.intro ?_ ?_)
  . intro l
    exact measurePreserving_godementJacquetUnipotentClassLeviEquiv K r k (V l) nu
  . intro l c x
    change act.smul c (E l x) = E l (act.smul (aut l c) x)
    choose B hB using compactUnipotentClass_surjective c
    rw [<- hB]
    refine Quotient.inductionOn x ?_
    intro g
    let va := Matrix.GeneralLinearGroup.map (algebraMap K (Adeles K)) (V l)
    have hc : aut l (godementJacquetUnipotentClass B) = godementJacquetUnipotentClass (B * va.val) :=
      godementJacquetUnipotentClassLeviEquiv_apply_class (V l) B
    have hE (z : NormGroup K n) : E l (q z) = q (l.val * z) := rfl
    have hConj : Inv.inv l.val * alpha (Multiplicative.ofAdd B) * l.val =
        alpha (Multiplicative.ofAdd (B * va.val)) := by
      rw [<- hV l]
      exact godementJacquetAdelicUnipotent_levi_conj e a (V l) B
    have hComm : alpha (Multiplicative.ofAdd B) * l.val =
        l.val * alpha (Multiplicative.ofAdd (B * va.val)) := calc
      _ = l.val * (Inv.inv l.val * alpha (Multiplicative.ofAdd B) * l.val) := by simp [mul_assoc]
      _ = _ := by rw [hConj]
    change act.smul (godementJacquetUnipotentClass B) (E l (q g)) =
      E l (act.smul (aut l (godementJacquetUnipotentClass B)) (q g))
    rw [hE, hAct, hc, hAct, hE, <- mul_assoc, <- mul_assoc, hComm]

private abbrev RationalStabilizer
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k))) (a : Matrix.GeneralLinearGroup (Fin n) K) :=
  (godementJacquetProjectionStabilizer K r k).map (godementJacquetPrincipalRankTransport e a)

/-- A rational stabilizer integral vanishes when the compact unipotent
constant term of its invariant integrand vanishes. -/
theorem integral_godementJacquetRationalStabilizer_eq_zero_of_constantTerm
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k))) (a : Matrix.GeneralLinearGroup (Fin n) K)
    [MeasurableSpace (NormGroup K n)] [BorelSpace (NormGroup K n)]
    [MeasurableSpace (UnipotentClasses K r k)] [BorelSpace (UnipotentClasses K r k)]
    (nu : Measure (UnipotentClasses K r k)) [nu.IsHaarMeasure] [IsProbabilityMeasure nu]
    [nu.IsMulRightInvariant]
    (mu : Measure (NormGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (S : Set (NormGroup K n)) (hS : MeasurableSet S)
    (hUnique : forall g : NormGroup K n, ExistsUnique
      (fun h : RationalStabilizer e a => Membership.mem S (h.val * g)))
    (F : NormGroup K n -> Complex) (hF : Measurable F) (hInt : IntegrableOn F S mu)
    (hInvariant : forall h : RationalStabilizer e a, forall g, F (h.val * g) = F g)
    (representative : UnipotentClasses K r k -> Blocks K r k)
    (hRep : Function.RightInverse representative godementJacquetUnipotentClass)
    (hConstantTerm : forall g : NormGroup K n,
      integral nu (fun c => F (godementJacquetAdelicUnipotent e a
        (Multiplicative.ofAdd (representative c)) * g)) = 0) :
    integral (mu.restrict S) F = 0 := by
  let G := NormGroup K n
  let C := UnipotentClasses K r k
  let hom := godementJacquetPrincipalRankTransport e a
  let U := RationalUnipotent e a
  let L := RationalLevi e a
  let H := RationalStabilizer e a
  let X := RationalUnipotentOrbits e a
  let q := Quotient.mk (MulAction.orbitRel U G)
  let T := Set.image q S
  let : SecondCountableTopology (AdelicGeneralLinearGroup K n) :=
    secondCountableTopology_adelicGeneralLinearGroup K n
  let : SecondCountableTopology G :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (fun g : G => g.val)).secondCountableTopology
  let : DiscreteTopology U :=
    discreteTopology_godementJacquetPrincipalRankSubgroup e a (godementJacquetProjectionUnipotent K r k)
  let : DiscreteTopology L :=
    discreteTopology_godementJacquetPrincipalRankSubgroup e a (godementJacquetProjectionLevi K r k)
  let : Countable U := countable_of_Lindelof_of_discrete
  let : Countable L := countable_of_Lindelof_of_discrete
  have hU : U <= H := Subgroup.map_mono (godementJacquetProjectionUnipotent_le_stabilizer K r k)
  have hL : L <= H := Subgroup.map_mono (godementJacquetProjectionLevi_le_stabilizer K r k)
  have hSplitNorm := exists_godementJacquetProjectionStabilizer_map_split hom
    (godementJacquetPrincipalRankTransport_injective e a)
  choose split hSplit using hSplitNorm.1
  have hNorm := hSplitNorm.2
  choose W hW using exists_leftOrbitRestriction_of_splitSubgroup U L H hU hL split hSplit mu S hS hUnique
  let m := (mu.restrict W).map q
  have hT : MeasurableSet T := hW.2.2.1
  have hRestrict : m.restrict T = (mu.restrict S).map q := hW.2.2.2
  choose act hAct using exists_godementJacquetUnipotentOrbitAction e a mu W hW.1 hW.2.1
  choose aut hAut using exists_godementJacquetLeviOrbitCompatibility e a hNorm act hAct.1 nu
  let : MulAction C X := act
  let : MulAction L X := leftOrbitNormalizerMulAction U L hNorm
  have hPC (c : C) : MeasurePreserving (fun x : X => HSMul.hSMul c x) m m := hAct.2.2 c
  have hPL (l : L) : MeasurePreserving (fun x : X => HSMul.hSMul l x) m m := by
    exact measurePreserving_leftOrbitNormalizerEquiv U mu W hW.1 hW.2.1 l.val
      (hNorm l) (fun u => by
        simpa only [Subgroup.coe_inv, inv_inv] using hNorm (Inv.inv l) u)
  let : MeasurableConstSMul C X := MeasurableConstSMul.mk (fun c => (hPC c).measurable)
  let : MeasurableConstSMul L X := MeasurableConstSMul.mk (fun l => (hPL l).measurable)
  let : SMulInvariantMeasure C X m := SMulInvariantMeasure.mk (fun c s hs => by
    rw [<- Measure.map_apply (hPC c).measurable hs, (hPC c).map_eq])
  let : SMulInvariantMeasure L X m := SMulInvariantMeasure.mk (fun l s hs => by
    rw [<- Measure.map_apply (hPL l).measurable hs, (hPL l).map_eq])
  let : SFinite m := inferInstanceAs (SFinite ((mu.restrict W).map q))
  have hUT : forall x : X, ExistsUnique (fun l : L => Membership.mem T (HSMul.hSMul l x)) :=
    existsUnique_leftOrbitNormalizerSubgroup_imageDomain U L H hNorm split hSplit S hUnique
  have hDom : IsFundamentalDomain L T m := IsFundamentalDomain.mk' hT.nullMeasurableSet hUT
  let f : X -> Complex := Quotient.lift F (by
    intro g h hr
    change Exists (fun u : U => u.val * h = g) at hr
    choose u hu using hr
    rw [<- hu]
    exact hInvariant (Subtype.mk u.val (hU u.property)) h)
  have hq : Measurable q := fun _ hs => measurableSet_quotient.mp hs
  have hf : Measurable f := measurable_from_quotient.mpr hF
  have hIntT : IntegrableOn f T m := by
    change Integrable f (m.restrict T)
    rw [hRestrict]
    exact (integrable_map_measure hf.aestronglyMeasurable hq.aemeasurable).mpr hInt
  have hInv (l : L) (x : X) : f (HSMul.hSMul l x) = f x := by
    refine Quotient.inductionOn x ?_
    intro g
    exact hInvariant (Subtype.mk l.val (hL l.property)) g
  have hMean (x : X) : integral nu (fun c : C => f (HSMul.hSMul c x)) = 0 := by
    refine Quotient.inductionOn x ?_
    intro g
    have he : (fun c : C => f (HSMul.hSMul c (q g))) =
        (fun c => F (godementJacquetAdelicUnipotent e a (Multiplicative.ofAdd (representative c)) * g)) := by
      funext c
      have hc := hAct.1 (representative c) g
      change act.smul (godementJacquetUnipotentClass (representative c)) (q g) = _ at hc
      rw [hRep c] at hc
      exact congrArg f hc
    change integral nu (fun c : C => f (HSMul.hSMul c (q g))) = 0
    rw [he]
    exact hConstantTerm g
  have hZero := setIntegral_eq_zero_of_orbitAverage nu m T hDom hT hUT
    hAct.2.1 aut hAut.1 hAut.2 f hf hIntT hInv (Filter.Eventually.of_forall hMean)
  rw [hRestrict, integral_map hq.aemeasurable hf.aestronglyMeasurable] at hZero
  exact hZero

/-- Every adelic upper unipotent in the transported block fixes the rational
matrix after scalar extension to the adeles. -/
theorem godementJacquetAdelicUnipotent_fixes_singularMatrix
    (P : Matrix (Fin n) (Fin n) K) (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a b : Matrix.GeneralLinearGroup (Fin n) K)
    (h : a.val * P * b.val = (godementJacquetRankProjection K r k).submatrix e e)
    (B : Blocks K r k) :
    let PA := P.map (algebraMap K (Adeles K))
    (godementJacquetAdelicUnipotent e a (Multiplicative.ofAdd B)).val.val * PA = PA := by
  let f := algebraMap K (Adeles K)
  let fM : RingHom (Matrix (Fin n) (Fin n) K)
      (Matrix (Fin n) (Fin n) (Adeles K)) := RingHom.mapMatrix f
  let aa := Matrix.GeneralLinearGroup.map f a
  let ba := Matrix.GeneralLinearGroup.map f b
  have hA := congrArg fM h
  rw [map_mul, map_mul] at hA
  have hProjection :
      (godementJacquetRankProjection K r k).map f =
      godementJacquetRankProjection (Adeles K) r k := by
    simp [godementJacquetRankProjection, Matrix.fromBlocks_map]
  have hMapped : aa.val * P.map f * ba.val =
      (godementJacquetRankProjection (Adeles K) r k).submatrix e e := by
    change aa.val * P.map f * ba.val =
      ((godementJacquetRankProjection K r k).map f).submatrix e e at hA
    rw [hProjection] at hA
    exact hA
  exact (godementJacquetRankTransport_mul_eq_iff (P.map f) e aa ba hMapped
    (godementJacquetUpperUnipotent B)).mpr (godementJacquetUpperUnipotent_mul_rankProjection B)

/-- A singular theta term vanishes on the rational stabilizer quotient
when the cusp form has zero constant term for the transported unipotent. -/
theorem integral_godementJacquetSingularTerm_eq_zero_of_cuspidal
    (P : Matrix (Fin n) (Fin n) K) (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a b : Matrix.GeneralLinearGroup (Fin n) K)
    (h : a.val * P * b.val = (godementJacquetRankProjection K r k).submatrix e e)
    [MeasurableSpace (NormGroup K n)] [BorelSpace (NormGroup K n)]
    [MeasurableSpace (UnipotentClasses K r k)] [BorelSpace (UnipotentClasses K r k)]
    (nu : Measure (UnipotentClasses K r k)) [nu.IsHaarMeasure] [IsProbabilityMeasure nu]
    [nu.IsMulRightInvariant]
    (mu : Measure (NormGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (S : Set (NormGroup K n)) (hS : MeasurableSet S)
    (hUnique : forall g : NormGroup K n, ExistsUnique
      (fun h : RationalStabilizer e a => Membership.mem S (h.val * g)))
    [MeasurableSpace (Matrix (Fin n) (Fin n) (Adeles K))]
    [BorelSpace (Matrix (Fin n) (Fin n) (Adeles K))]
    (phi : Matrix (Fin n) (Fin n) (Adeles K) -> Complex) (hPhi : Measurable phi)
    (cusp : NormGroup K n -> Complex) (hCusp : Measurable cusp)
    (hInvariant : forall gamma : (adelicPrincipalDeterminantOne K n).range, forall g,
      cusp (gamma.val * g) = cusp g)
    (representative : UnipotentClasses K r k -> Blocks K r k)
    (hRep : Function.RightInverse representative godementJacquetUnipotentClass)
    (hCuspPeriod : forall g : NormGroup K n,
      integral nu (fun c => cusp (godementJacquetAdelicUnipotent e a
        (Multiplicative.ofAdd (representative c)) * g)) = 0) :
    let PA := P.map (algebraMap K (Adeles K))
    let F := fun g : NormGroup K n => phi (g.val.inv * PA) * cusp g
    IntegrableOn F S mu -> integral (mu.restrict S) F = 0 := by
  let G := NormGroup K n
  let C := UnipotentClasses K r k
  let PA := P.map (algebraMap K (Adeles K))
  let F := fun g : G => phi (g.val.inv * PA) * cusp g
  let alpha := godementJacquetAdelicUnipotent e a
  change IntegrableOn F S mu -> integral (mu.restrict S) F = 0
  intro hInt
  have hMatrix (l : G) (hl : l.val.val * PA = PA) (g : G) :
      (l * g).val.inv * PA = g.val.inv * PA := by
    have hi : l.val.inv * PA = PA := calc
      _ = l.val.inv * (l.val.val * PA) := congrArg (fun P => l.val.inv * P) hl.symm
      _ = _ := by rw [<- Matrix.mul_assoc, l.val.inv_val, Matrix.one_mul]
    change (g.val.inv * l.val.inv) * PA = _
    rw [Matrix.mul_assoc, hi]
  have hF : Measurable F := by
    have hc : Continuous (fun g : G => g.val.inv * PA) :=
      (Units.continuous_val.comp continuous_subtype_val.inv).mul continuous_const
    exact (hPhi.comp hc.measurable).mul hCusp
  refine integral_godementJacquetRationalStabilizer_eq_zero_of_constantTerm e a nu mu S hS hUnique
    F hF hInt ?_ representative hRep ?_
  . intro l g
    have hl := (mem_godementJacquetPrincipalSingularStabilizer_iff P e a b h l.val).mp l.property
    change phi ((l.val * g).val.inv * PA) * cusp (l.val * g) = phi (g.val.inv * PA) * cusp g
    rw [hMatrix l.val hl.2 g, hInvariant (Subtype.mk l.val hl.1) g]
  . intro g
    have he : (fun c : C => F (alpha (Multiplicative.ofAdd (representative c)) * g)) =
        (fun c => phi (g.val.inv * PA) *
          cusp (alpha (Multiplicative.ofAdd (representative c)) * g)) := by
      funext c
      have hFix := godementJacquetAdelicUnipotent_fixes_singularMatrix P e a b h (representative c)
      change phi ((alpha (Multiplicative.ofAdd (representative c)) * g).val.inv * PA) * _ = _
      rw [hMatrix _ hFix g]
    change integral nu (fun c : C => F (alpha (Multiplicative.ofAdd (representative c)) * g)) = 0
    rw [he, integral_const_mul, hCuspPeriod, mul_zero]

end LeviOnUnipotentOrbits

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

section CosetDomains

variable {G : Type*} [Group G]

/-- Cosets of the smaller subgroup for its left action on the larger group. -/
abbrev LeftSubgroupCosets (H Gamma : Subgroup G) :=
  Quotient (MulAction.orbitRel (H.subgroupOf Gamma) Gamma)

/-- A representative of a coset for the left action. -/
def leftSubgroupCosetRepresentative (H Gamma : Subgroup G) (j : LeftSubgroupCosets H Gamma) : Gamma :=
  Classical.choose (Quotient.mk_surjective j)

theorem leftSubgroupCosetRepresentative_spec (H Gamma : Subgroup G) (j : LeftSubgroupCosets H Gamma) :
    Quotient.mk (MulAction.orbitRel (H.subgroupOf Gamma) Gamma)
      (leftSubgroupCosetRepresentative H Gamma j) = j :=
  Classical.choose_spec (Quotient.mk_surjective j)

/-- A map with the cosets as fibers identifies those cosets with its range. -/
def leftSubgroupCosetEquivRange {Y : Type*} (H Gamma : Subgroup G)
    (f : Gamma -> Y)
    (hFiber : forall (x y : Gamma), f x = f y <->
      Membership.mem H (x.val * Inv.inv y.val)) :
    Equiv (LeftSubgroupCosets H Gamma) (Set.range f) := by
  let J := LeftSubgroupCosets H Gamma
  let rep := leftSubgroupCosetRepresentative H Gamma
  let q := Quotient.mk (MulAction.orbitRel (H.subgroupOf Gamma) Gamma)
  have hRep (j : J) : q (rep j) = j := leftSubgroupCosetRepresentative_spec H Gamma j
  let F (j : J) : Set.range f := Subtype.mk (f (rep j)) (Exists.intro (rep j) rfl)
  refine Equiv.ofBijective F (And.intro ?_ ?_)
  . intro i j h
    have he := congrArg Subtype.val h
    have hm := (hFiber (rep i) (rep j)).mp he
    let w : H.subgroupOf Gamma := Subtype.mk (rep i * Inv.inv (rep j)) hm
    have hr : q (rep i) = q (rep j) := Quotient.sound
      (Exists.intro w (show (rep i * Inv.inv (rep j)) * rep j = rep i by simp [mul_assoc]))
    exact (hRep i).symm.trans (hr.trans (hRep j))
  . intro y
    choose x hx using y.property
    let j := q x
    have he := Quotient.exact (hRep j)
    change Exists (fun w : H.subgroupOf Gamma => w.val * x = rep j) at he
    choose w hw using he
    have hw' : rep j * Inv.inv x = w.val := by rw [<- hw]; simp [mul_assoc]
    have hm : Membership.mem H ((rep j).val * Inv.inv x.val) := by
      change Membership.mem H (rep j * Inv.inv x).val
      rw [hw']
      exact w.property
    exact Exists.intro j (Subtype.ext (((hFiber (rep j) x).mpr hm).trans hx))

/-- Translates of an exact Borel domain by left-coset representatives. -/
def leftSubgroupCosetTile (H Gamma : Subgroup G) (S : Set G) (j : LeftSubgroupCosets H Gamma) :
    Set G :=
  Set.preimage (fun x => Inv.inv (leftSubgroupCosetRepresentative H Gamma j).val * x) S

/-- The tiles are disjoint and together give an exact domain for the smaller subgroup. -/
theorem leftSubgroupCosetTiles_fundamental
    (H Gamma : Subgroup G) (hSub : H <= Gamma) (S : Set G)
    (hUnique : forall x : G, ExistsUnique (fun gamma : Gamma => Membership.mem S (gamma.val * x))) :
    let tile := leftSubgroupCosetTile H Gamma S
    And (Pairwise (fun i j => Disjoint (tile i) (tile j)))
      (forall x : G, ExistsUnique (fun h : H =>
        Membership.mem (Set.iUnion tile) (h.val * x))) := by
  let rep := leftSubgroupCosetRepresentative H Gamma
  let tile := leftSubgroupCosetTile H Gamma S
  let q := Quotient.mk (MulAction.orbitRel (H.subgroupOf Gamma) Gamma)
  have hRep (j : LeftSubgroupCosets H Gamma) : q (rep j) = j :=
    leftSubgroupCosetRepresentative_spec H Gamma j
  refine And.intro ?_ ?_
  . intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hri : Membership.mem S ((Inv.inv (rep i)).val * x) := hi
    have hrj : Membership.mem S ((Inv.inv (rep j)).val * x) := hj
    have hv : Inv.inv (rep i) = Inv.inv (rep j) := (hUnique x).unique hri hrj
    have he : rep i = rep j := inv_injective hv
    exact hij ((hRep i).symm.trans ((congrArg q he).trans (hRep j)))
  . intro x
    choose gamma hGamma using (hUnique x).exists
    let t := Inv.inv gamma
    let i := q t
    have hr := Quotient.exact (hRep i)
    change Exists (fun w : H.subgroupOf Gamma => w.val * t = rep i) at hr
    choose w hw using hr
    let h : H := Subtype.mk w.val.val w.property
    refine Exists.intro h (And.intro ?_ ?_)
    . apply Set.mem_iUnion.mpr
      refine Exists.intro i ?_
      change Membership.mem S (Inv.inv (rep i).val * (h.val * x))
      have hw' : Inv.inv (rep i) * w.val = gamma := by
        rw [<- hw]
        simp [t, mul_inv_rev, mul_assoc]
      rw [<- mul_assoc, show Inv.inv (rep i).val * h.val = gamma.val from congrArg Subtype.val hw']
      exact hGamma
    . intro v hv
      choose j hj using Set.mem_iUnion.mp hv
      let z : Gamma := Subtype.mk v.val (hSub v.property)
      have hzS : Membership.mem S ((Inv.inv (rep j) * z).val * x) := by
        change Membership.mem S ((Inv.inv (rep j).val * v.val) * x)
        rw [mul_assoc]
        exact hj
      have hz : Inv.inv (rep j) * z = gamma := (hUnique x).unique hzS hGamma
      have hzt : z * t = rep j := calc
        _ = (rep j * (Inv.inv (rep j) * z)) * t := by simp
        _ = _ := by rw [hz]; simp [t, mul_assoc]
      let zH : H.subgroupOf Gamma := Subtype.mk z v.property
      have hj' : q (rep j) = i := Quotient.sound (Exists.intro zH hzt)
      have hji : j = i := (hRep j).symm.trans hj'
      rw [hji] at hzt
      have he : z = w.val := mul_right_cancel (hzt.trans hw.symm)
      exact Subtype.ext (congrArg (fun y : Gamma => y.val) he)

variable [MeasurableSpace G] [MeasurableMul G]

/-- The exact domain assembled from the coset tiles is Borel. -/
theorem measurableSet_leftSubgroupCosetTiles
    (H Gamma : Subgroup G) [Countable Gamma] {S : Set G} (hS : MeasurableSet S) :
    MeasurableSet (Set.iUnion (leftSubgroupCosetTile H Gamma S)) := by
  let : Countable (LeftSubgroupCosets H Gamma) := Quotient.mk_surjective.countable
  apply MeasurableSet.iUnion
  intro j
  exact (MeasurableEquiv.mulLeft (Inv.inv (leftSubgroupCosetRepresentative H Gamma j).val)).measurable hS

private theorem measurePreserving_leftSubgroupCosetTile
    (H Gamma : Subgroup G) (mu : Measure G) [mu.IsMulLeftInvariant]
    (D : Set G) (j : LeftSubgroupCosets H Gamma) :
    MeasurePreserving (fun g => (leftSubgroupCosetRepresentative H Gamma j).val * g)
      (mu.restrict D) (mu.restrict (leftSubgroupCosetTile H Gamma D j)) := by
  let g := (leftSubgroupCosetRepresentative H Gamma j).val
  let E := MeasurableEquiv.mulLeft g
  let T := leftSubgroupCosetTile H Gamma D j
  have he : Set.preimage E T = D := by
    ext x
    change Membership.mem D (Inv.inv g * (g * x)) <-> Membership.mem D x
    simp
  have h := (measurePreserving_mul_left mu g).restrict_preimage_emb E.measurableEmbedding T
  change MeasurePreserving E (mu.restrict (Set.preimage E T)) (mu.restrict T) at h
  rwa [he] at h

/-- The absolute integral on the nested domain is the absolute coset
sum integrated over the original domain. -/
theorem lintegral_leftSubgroupCosetTiles_eq_tsum
    (H Gamma : Subgroup G) [Countable Gamma] (hSub : H <= Gamma)
    (mu : Measure G) [mu.IsMulLeftInvariant] (D : Set G) (hD : MeasurableSet D)
    (hUnique : forall x : G, ExistsUnique (fun gamma : Gamma => Membership.mem D (gamma.val * x)))
    (F : G -> ENNReal) (hF : Measurable F) :
    lintegral (mu.restrict (Set.iUnion (leftSubgroupCosetTile H Gamma D))) F =
      lintegral (mu.restrict D) (fun x =>
        tsum (fun j : LeftSubgroupCosets H Gamma => F ((leftSubgroupCosetRepresentative H Gamma j).val * x))) := by
  let J := LeftSubgroupCosets H Gamma
  let tile := leftSubgroupCosetTile H Gamma D
  let m (j : J) := mu.restrict (tile j)
  let rep (j : J) := (leftSubgroupCosetRepresentative H Gamma j).val
  let : Countable J := Quotient.mk_surjective.countable
  have hM (j : J) : MeasurableSet (tile j) :=
    (MeasurableEquiv.mulLeft (Inv.inv (rep j))).measurable hD
  have hUnion : mu.restrict (Set.iUnion tile) = Measure.sum m :=
    Measure.restrict_iUnion (leftSubgroupCosetTiles_fundamental H Gamma hSub D hUnique).1 hM
  have hPres (j : J) : MeasurePreserving (fun x => rep j * x) (mu.restrict D) (m j) :=
    measurePreserving_leftSubgroupCosetTile H Gamma mu D j
  change lintegral (mu.restrict (Set.iUnion tile)) F = _
  calc
    _ = tsum (fun j : J => lintegral (m j) F) := by rw [hUnion, lintegral_sum_measure]
    _ = tsum (fun j : J => lintegral (mu.restrict D) (fun x => F (rep j * x))) := by
      apply tsum_congr
      intro j
      have hh : lintegral (Measure.map (fun x => rep j * x) (mu.restrict D)) F =
          lintegral (mu.restrict D) (fun x => F (rep j * x)) :=
        lintegral_map hF (hPres j).measurable
      rwa [(hPres j).map_eq] at hh
    _ = _ := (lintegral_tsum (fun j => (hF.comp (hPres j).measurable).aemeasurable)).symm

/-- Absolute integrability on the nested domain identifies its integral
with the integral of the corresponding coset sum on the original domain. -/
theorem integral_leftSubgroupCosetTiles_eq_tsum
    (H Gamma : Subgroup G) [Countable Gamma] (hSub : H <= Gamma)
    (mu : Measure G) [mu.IsMulLeftInvariant] (S : Set G) (hS : MeasurableSet S)
    (hUnique : forall x : G, ExistsUnique (fun gamma : Gamma => Membership.mem S (gamma.val * x)))
    (F : G -> Complex) (hF : Measurable F)
    (hInt : IntegrableOn F (Set.iUnion (leftSubgroupCosetTile H Gamma S)) mu) :
    integral (mu.restrict (Set.iUnion (leftSubgroupCosetTile H Gamma S))) F =
      integral (mu.restrict S) (fun x =>
        tsum (fun j : LeftSubgroupCosets H Gamma => F ((leftSubgroupCosetRepresentative H Gamma j).val * x))) := by
  let J := LeftSubgroupCosets H Gamma
  let tile := leftSubgroupCosetTile H Gamma S
  let W := Set.iUnion tile
  let rep := leftSubgroupCosetRepresentative H Gamma
  let E (j : J) := MeasurableEquiv.mulLeft (rep j).val
  let m (j : J) := mu.restrict (tile j)
  let : Countable J := Quotient.mk_surjective.countable
  have hT (j : J) : MeasurableSet (tile j) :=
    (MeasurableEquiv.mulLeft (Inv.inv (rep j).val)).measurable hS
  have hUnion : mu.restrict W = Measure.sum m :=
    Measure.restrict_iUnion (leftSubgroupCosetTiles_fundamental H Gamma hSub S hUnique).1 hT
  have hMP (j : J) : MeasurePreserving (E j) (mu.restrict S) (m j) :=
    measurePreserving_leftSubgroupCosetTile H Gamma mu S j
  have hAbs (j : J) : lintegral (mu.restrict S) (fun x => enorm (F (E j x))) =
      lintegral (m j) (fun x => enorm (F x)) := by
    have h : lintegral (Measure.map (E j) (mu.restrict S)) (fun x => enorm (F x)) =
        lintegral (mu.restrict S) (fun x => enorm (F (E j x))) :=
      lintegral_map hF.enorm (hMP j).measurable
    rw [(hMP j).map_eq] at h
    exact h.symm
  have hFinite : Not (tsum (fun j : J => lintegral (mu.restrict S)
      (fun x => enorm (F (E j x)))) = (Top.top : ENNReal)) := by
    intro hinfinite
    have he : lintegral (mu.restrict W) (fun x => enorm (F x)) = Top.top := calc
      _ = tsum (fun j : J => lintegral (m j) (fun x => enorm (F x))) := by
        rw [hUnion, lintegral_sum_measure]
      _ = tsum (fun j : J => lintegral (mu.restrict S) (fun x => enorm (F (E j x)))) :=
        tsum_congr (fun j => (hAbs j).symm)
      _ = _ := hinfinite
    exact (ne_of_lt hInt.2) he
  have hInt' : Integrable F (Measure.sum m) := by
    rw [<- hUnion]
    exact hInt
  calc
    integral (mu.restrict W) F = tsum (fun j : J => integral (m j) F) := by
      rw [hUnion]
      exact integral_sum_measure hInt'
    _ = tsum (fun j : J => integral (mu.restrict S) (fun x => F (E j x))) :=
      tsum_congr (fun j => ((hMP j).integral_comp (E j).measurableEmbedding F).symm)
    _ = _ := (integral_tsum (fun j => (hF.comp (hMP j).measurable).aestronglyMeasurable) hFinite).symm

end CosetDomains

section ExactSingularOrbit

variable {K : Type*} [Field K] [NumberField K] {n r k : Nat}

/-- The left orbit of a rational matrix in the adelic matrix space. -/
def godementJacquetRationalMatrixOrbit (P : Matrix (Fin n) (Fin n) K) :
    Set (Matrix (Fin n) (Fin n) (Adeles K)) :=
  Set.range (fun gamma : PrincipalDeterminantOne K n =>
    gamma.val.val.inv * P.map (algebraMap K (Adeles K)))

private theorem orbitStabilizer_le_principal (P : Matrix (Fin n) (Fin n) K)
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k))) (a b : Matrix.GeneralLinearGroup (Fin n) K)
    (h : a.val * P * b.val = (godementJacquetRankProjection K r k).submatrix e e) :
    RationalStabilizer e a <= PrincipalDeterminantOne K n := by
  intro g hg
  exact ((mem_godementJacquetPrincipalSingularStabilizer_iff P e a b h g).mp hg).1

private theorem rationalMatrixOrbit_fiber (P : Matrix (Fin n) (Fin n) K)
    (e : Equiv (Fin n) (Sum (Fin r) (Fin k))) (a b : Matrix.GeneralLinearGroup (Fin n) K)
    (h : a.val * P * b.val = (godementJacquetRankProjection K r k).submatrix e e)
    (x y : PrincipalDeterminantOne K n) :
    let PA := P.map (algebraMap K (Adeles K))
    x.val.val.inv * PA = y.val.val.inv * PA <->
      Membership.mem (RationalStabilizer e a) (x.val * Inv.inv y.val) := by
  let PA := P.map (algebraMap K (Adeles K))
  have hstab := mem_godementJacquetPrincipalSingularStabilizer_iff P e a b h
    (x.val * Inv.inv y.val)
  constructor
  . intro he
    refine hstab.mpr (And.intro
      ((PrincipalDeterminantOne K n).mul_mem x.property ((PrincipalDeterminantOne K n).inv_mem y.property)) ?_)
    change (x.val.val.val * y.val.val.inv) * PA = PA
    rw [Matrix.mul_assoc, <- he, <- Matrix.mul_assoc, x.val.val.val_inv, Matrix.one_mul]
  . intro hm
    have hfix := (hstab.mp hm).2
    change (x.val.val.val * y.val.val.inv) * PA = PA at hfix
    have he := congrArg (fun M => x.val.val.inv * M) hfix
    rw [<- Matrix.mul_assoc, <- Matrix.mul_assoc, x.val.val.inv_val, Matrix.one_mul] at he
    exact he.symm

/-- The singular orbital theta sum over the principal quotient integrates
to zero by the vanishing of the corresponding unipotent constant term. -/
theorem integral_godementJacquetSingularOrbit_eq_zero_of_cuspidal
    (P : Matrix (Fin n) (Fin n) K) (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
    (a b : Matrix.GeneralLinearGroup (Fin n) K)
    (h : a.val * P * b.val = (godementJacquetRankProjection K r k).submatrix e e)
    [MeasurableSpace (NormGroup K n)] [BorelSpace (NormGroup K n)]
    [MeasurableSpace (GodementJacquetUnipotentClassGroup K r k)]
    [BorelSpace (GodementJacquetUnipotentClassGroup K r k)]
    (nu : Measure (GodementJacquetUnipotentClassGroup K r k))
    [nu.IsHaarMeasure] [IsProbabilityMeasure nu] [nu.IsMulRightInvariant]
    (mu : Measure (NormGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (D : Set (NormGroup K n)) (hD : MeasurableSet D)
    (hUnique : forall g : NormGroup K n, ExistsUnique
      (fun gamma : PrincipalDeterminantOne K n => Membership.mem D (gamma.val * g)))
    [MeasurableSpace (Matrix (Fin n) (Fin n) (Adeles K))]
    [BorelSpace (Matrix (Fin n) (Fin n) (Adeles K))]
    (phi : Matrix (Fin n) (Fin n) (Adeles K) -> Complex) (hPhi : Measurable phi)
    (cusp : NormGroup K n -> Complex) (hCusp : Measurable cusp)
    (hInvariant : forall gamma : PrincipalDeterminantOne K n, forall g, cusp (gamma.val * g) = cusp g)
    (representative : GodementJacquetUnipotentClassGroup K r k ->
      Matrix (Fin r) (Fin k) (Adeles K))
    (hRep : Function.RightInverse representative godementJacquetUnipotentClass)
    (hCuspPeriod : forall g : NormGroup K n,
      integral nu (fun c => cusp (godementJacquetAdelicUnipotent e a
        (Multiplicative.ofAdd (representative c)) * g)) = 0) :
    let H := RationalStabilizer e a
    let Gamma := PrincipalDeterminantOne K n
    let S := Set.iUnion (leftSubgroupCosetTile H Gamma D)
    let PA := P.map (algebraMap K (Adeles K))
    let F := fun g : NormGroup K n => phi (g.val.inv * PA) * cusp g
    IntegrableOn F S mu -> integral (mu.restrict D) (fun g =>
      (tsum (fun Q : godementJacquetRationalMatrixOrbit P => phi (g.val.inv * Q.val))) *
        cusp g) = 0 := by
  let G := NormGroup K n
  let H := RationalStabilizer e a
  let Gamma := PrincipalDeterminantOne K n
  let S := Set.iUnion (leftSubgroupCosetTile H Gamma D)
  let PA := P.map (algebraMap K (Adeles K))
  let F := fun g : G => phi (g.val.inv * PA) * cusp g
  change IntegrableOn F S mu -> _
  intro hInt
  let : Countable Gamma := countable_adelicPrincipalDeterminantOne K n
  let : SecondCountableTopology (AdelicGeneralLinearGroup K n) :=
    secondCountableTopology_adelicGeneralLinearGroup K n
  let : SecondCountableTopology G :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (fun g : G => g.val)).secondCountableTopology
  have hSub := orbitStabilizer_le_principal P e a b h
  have hS : MeasurableSet S := measurableSet_leftSubgroupCosetTiles H Gamma hD
  have hUniqueS := (leftSubgroupCosetTiles_fundamental H Gamma hSub D hUnique).2
  have hZero := integral_godementJacquetSingularTerm_eq_zero_of_cuspidal P e a b h
    nu mu S hS hUniqueS phi hPhi cusp hCusp hInvariant representative hRep hCuspPeriod hInt
  have hF : Measurable F := by
    have hc : Continuous (fun g : G => g.val.inv * PA) :=
      (Units.continuous_val.comp continuous_subtype_val.inv).mul continuous_const
    exact (hPhi.comp hc.measurable).mul hCusp
  have hSum := integral_leftSubgroupCosetTiles_eq_tsum H Gamma hSub mu D hD hUnique F hF hInt
  let E : Equiv (LeftSubgroupCosets H Gamma) (godementJacquetRationalMatrixOrbit P) :=
    leftSubgroupCosetEquivRange H Gamma (fun gamma => gamma.val.val.inv * PA)
      (rationalMatrixOrbit_fiber P e a b h)
  have he (g : G) :
      tsum (fun j : LeftSubgroupCosets H Gamma => F ((leftSubgroupCosetRepresentative H Gamma j).val * g)) =
        (tsum (fun Q : godementJacquetRationalMatrixOrbit P => phi (g.val.inv * Q.val))) * cusp g := by
    have hTerm (j : LeftSubgroupCosets H Gamma) :
        F ((leftSubgroupCosetRepresentative H Gamma j).val * g) =
          phi (g.val.inv * (E j).val) * cusp g := by
      let gamma := leftSubgroupCosetRepresentative H Gamma j
      change phi ((g.val.inv * gamma.val.val.inv) * PA) * cusp (gamma.val * g) =
        phi (g.val.inv * (gamma.val.val.inv * PA)) * cusp g
      rw [Matrix.mul_assoc, hInvariant gamma g]
    simp_rw [hTerm, tsum_mul_right]
    rw [E.tsum_eq (fun Q => phi (g.val.inv * Q.val))]
  change integral (mu.restrict D)
    (fun g : G => (tsum (fun Q : godementJacquetRationalMatrixOrbit P =>
      phi (g.val.inv * Q.val))) * cusp g) = 0
  simp_rw [he] at hSum
  exact hSum.symm.trans hZero

end ExactSingularOrbit

section IntegrablePartition

variable {I J X : Type*} [Countable I] [Countable J] [MeasurableSpace X]

private theorem measurable_complexTsum_of_summable (F : I -> X -> Complex)
    (hF : forall i, Measurable (F i))
    (hSum : forall x, Summable (fun i => F i x)) :
    Measurable (fun x => tsum (fun i => F i x)) := by
  classical
  apply measurable_of_tendsto_metrizable' (f := fun S : Finset I => fun x =>
    S.sum (fun i => F i x)) Filter.atTop
  . intro s
    exact Finset.measurable_fun_sum s (fun i _ => hF i)
  . exact tendsto_pi_nhds.mpr (fun x => (hSum x).hasSum)

private abbrev IndexFiber (q : I -> J) (j : J) :=
  Subtype (fun i : I => q i = j)

/-- Under absolute integrability, a countable sum of functions with
zero fiber integrals has zero integral over the whole partition. -/
theorem integral_tsum_eq_zero_of_fiberIntegrals
    (q : I -> J) (mu : Measure X) (F : I -> X -> Complex)
    (hF : forall i, Measurable (F i))
    (hSum : forall x, Summable (fun i => F i x))
    (hAbs : lintegral mu (fun x => tsum (fun i => enorm (F i x))) < (Top.top : ENNReal))
    (hZero : forall j : J,
      integral mu (fun x => tsum (fun i : IndexFiber q j => F i.val x)) = 0) :
    integral mu (fun x => tsum (fun i => F i x)) = 0 := by
  let G (j : J) (x : X) := tsum (fun i : IndexFiber q j => F i.val x)
  let e := Equiv.sigmaFiberEquiv q
  have hG (j : J) : Measurable (G j) :=
    measurable_complexTsum_of_summable (fun i : IndexFiber q j => F i.val)
      (fun i => hF i.val) (fun x => (hSum x).comp_injective Subtype.val_injective)
  have hsigma (x : X) : tsum (fun i => F i x) = tsum (fun j => G j x) := calc
    _ = tsum (fun p : Sigma (IndexFiber q) => F (e p) x) := (e.tsum_eq (fun i => F i x)).symm
    _ = _ := ((hSum x).comp_injective e.injective).tsum_sigma
  have hComparison (x : X) :
      tsum (fun j => enorm (G j x)) <= tsum (fun i => enorm (F i x)) := calc
    _ <= tsum (fun j : J => tsum (fun i : IndexFiber q j => enorm (F i.val x))) :=
      ENNReal.tsum_le_tsum (fun _ => enorm_tsum_le_tsum_enorm)
    _ = tsum (fun p : Sigma (IndexFiber q) => enorm (F (e p) x)) :=
      (ENNReal.tsum_sigma' (fun p : Sigma (IndexFiber q) => enorm (F (e p) x))).symm
    _ = _ := e.tsum_eq (fun i => enorm (F i x))
  have hFinite :
      tsum (fun j => lintegral mu (fun x => enorm (G j x))) < (Top.top : ENNReal) := by
    rw [<- lintegral_tsum (fun j => (hG j).enorm.aemeasurable)]
    exact lt_of_le_of_lt (lintegral_mono hComparison) hAbs
  simp_rw [hsigma]
  rw [integral_tsum (fun j => (hG j).aestronglyMeasurable) (ne_of_lt hFinite)]
  simp only [hZero, tsum_zero, G]

end IntegrablePartition

section RationalSingularIndex

variable {K : Type*} [Field K] [NumberField K] {n : Nat}

/-- Rational matrices of strictly positive, non-full rank. -/
abbrev GodementJacquetPositiveSingularMatrix (K : Type*) [Field K] (n : Nat) :=
  Subtype (fun P : Matrix (Fin n) (Fin n) K => And (P.det = 0) (0 < P.rank))

local instance rationalSingularMulAction :
    MulAction (Matrix.GeneralLinearGroup (Fin n) K) (GodementJacquetPositiveSingularMatrix K n) where
  smul a P := Subtype.mk (a.val * P.val) (by
    have hDet := (Matrix.isUnit_iff_isUnit_det a.val).mp a.isUnit
    refine And.intro ?_ ?_
    . rw [Matrix.det_mul, P.property.1, mul_zero]
    . rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ hDet]
      exact P.property.2)
  one_smul P := Subtype.ext (Matrix.one_mul P.val)
  mul_smul a b P := Subtype.ext (Matrix.mul_assoc a.val b.val P.val)

/-- The countable index of rational left orbits in the positive singular matrices. -/
def godementJacquetPositiveSingularOrbitMap :
    GodementJacquetPositiveSingularMatrix K n ->
      Quotient (MulAction.orbitRel (Matrix.GeneralLinearGroup (Fin n) K)
        (GodementJacquetPositiveSingularMatrix K n)) :=
  Quotient.mk _

/-- Each rational orbit fiber is identified with its image in the adelic matrix space. -/
def godementJacquetPositiveSingularFiberEquiv (P : GodementJacquetPositiveSingularMatrix K n) :
    Equiv (Subtype (fun Q : GodementJacquetPositiveSingularMatrix K n =>
      godementJacquetPositiveSingularOrbitMap Q = godementJacquetPositiveSingularOrbitMap P))
      (godementJacquetRationalMatrixOrbit P.val) := by
  let I := GodementJacquetPositiveSingularMatrix K n
  let q := godementJacquetPositiveSingularOrbitMap (K := K) (n := n)
  let Gamma := (adelicPrincipalDeterminantOne K n).range
  let f := algebraMap K (Adeles K)
  let fm : RingHom (Matrix (Fin n) (Fin n) K) (Matrix (Fin n) (Fin n) (Adeles K)) :=
    RingHom.mapMatrix f
  let e (Q : Subtype (fun Q : I => q Q = q P)) : godementJacquetRationalMatrixOrbit P.val :=
    Subtype.mk (fm Q.val.val) (by
      have h := Quotient.exact Q.property
      choose a ha using h
      let b := adelicPrincipalDeterminantOne K n (Inv.inv a)
      let c : Gamma := Subtype.mk b (Exists.intro (Inv.inv a) rfl)
      refine Exists.intro c ?_
      change fm a.val * fm P.val = fm Q.val.val
      rw [<- map_mul]
      exact congrArg (fun T : I => fm T.val) ha)
  refine Equiv.ofBijective e (And.intro ?_ ?_)
  . intro A B h
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    apply AdeleRing.algebraMap_injective (RingOfIntegers K) K
    exact congrArg (fun T : godementJacquetRationalMatrixOrbit P.val => T.val i j) h
  . intro Y
    have hY := Y.property
    change Exists (fun gamma : Gamma => gamma.val.val.inv * fm P.val = Y.val) at hY
    choose g hg using hY
    choose a ha using g.property
    let Q : I := HSMul.hSMul (Inv.inv a) P
    let T : Subtype (fun Q : I => q Q = q P) :=
      Subtype.mk Q (Quotient.sound (Exists.intro (Inv.inv a) rfl))
    refine Exists.intro T (Subtype.ext ?_)
    change fm (a.inv * P.val) = Y.val
    rw [map_mul]
    rw [<- ha] at hg
    exact hg

/-- The constant-term condition used to remove the positive-rank singular
terms. It requires vanishing along the conjugates of the proper
two-block upper unipotent radicals. -/
def HasGodementJacquetVanishingUnipotentPeriods
    (cusp : NormGroup K n -> Complex) : Prop :=
  forall (r k : Nat), 0 < r -> 0 < k ->
    forall (e : Equiv (Fin n) (Sum (Fin r) (Fin k)))
      (a : Matrix.GeneralLinearGroup (Fin n) K),
    let C := GodementJacquetUnipotentClassGroup K r k
    let : MeasurableSpace C := borel C
    Exists (fun nu : Measure C => And nu.IsHaarMeasure
      (And (IsProbabilityMeasure nu) (And nu.IsMulRightInvariant
        (Exists (fun representative : C -> Matrix (Fin r) (Fin k) (Adeles K) =>
          And (Function.RightInverse representative godementJacquetUnipotentClass)
            (forall g : NormGroup K n,
              integral nu (fun c => cusp (godementJacquetAdelicUnipotent e a
                (Multiplicative.ofAdd (representative c)) * g)) = 0))))))

/-- All positive-rank singular terms disappear from the theta integral
with vanishing cusp constant terms and an absolutely integrable sum. -/
theorem integral_godementJacquetPositiveSingularTheta_eq_zero
    [MeasurableSpace (NormGroup K n)] [BorelSpace (NormGroup K n)]
    (mu : Measure (NormGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (D : Set (NormGroup K n)) (hD : MeasurableSet D)
    (hUnique : forall g : NormGroup K n, ExistsUnique
      (fun gamma : PrincipalDeterminantOne K n => Membership.mem D (gamma.val * g)))
    [MeasurableSpace (Matrix (Fin n) (Fin n) (Adeles K))]
    [BorelSpace (Matrix (Fin n) (Fin n) (Adeles K))]
    (phi : Matrix (Fin n) (Fin n) (Adeles K) -> Complex) (hPhi : Measurable phi)
    (cusp : NormGroup K n -> Complex) (hCusp : Measurable cusp)
    (hInvariant : forall gamma : PrincipalDeterminantOne K n, forall g, cusp (gamma.val * g) = cusp g)
    (hPeriods : HasGodementJacquetVanishingUnipotentPeriods cusp)
    (hSum : forall g : NormGroup K n,
      Summable (fun P : GodementJacquetPositiveSingularMatrix K n =>
        phi (g.val.inv * P.val.map (algebraMap K (Adeles K)))))
    (hAbs : lintegral (mu.restrict D) (fun g : NormGroup K n =>
      tsum (fun P : GodementJacquetPositiveSingularMatrix K n =>
        enorm (phi (g.val.inv * P.val.map (algebraMap K (Adeles K))) * cusp g))) <
      (Top.top : ENNReal)) :
    integral (mu.restrict D) (fun g : NormGroup K n =>
      (tsum (fun P : GodementJacquetPositiveSingularMatrix K n =>
        phi (g.val.inv * P.val.map (algebraMap K (Adeles K))))) * cusp g) = 0 := by
  let G := NormGroup K n
  let Gamma := PrincipalDeterminantOne K n
  let I := GodementJacquetPositiveSingularMatrix K n
  let J := Quotient (MulAction.orbitRel (Matrix.GeneralLinearGroup (Fin n) K) I)
  let q : I -> J := godementJacquetPositiveSingularOrbitMap
  let f := algebraMap K (Adeles K)
  let F (P : I) (g : G) := phi (g.val.inv * P.val.map f) * cusp g
  let : Countable K := (Module.finBasis Rat K).equivFun.injective.countable
  let : Countable (Matrix (Fin n) (Fin n) K) := inferInstanceAs (Countable (Fin n -> Fin n -> K))
  let : Countable I := Subtype.val_injective.countable
  let : Countable J := Quotient.mk_surjective.countable
  let : Countable Gamma := countable_adelicPrincipalDeterminantOne K n
  let : SecondCountableTopology (AdelicGeneralLinearGroup K n) :=
    secondCountableTopology_adelicGeneralLinearGroup K n
  let : SecondCountableTopology G :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (fun g : G => g.val)).secondCountableTopology
  have hF (P : I) : Measurable (F P) := by
    have hc : Continuous (fun g : G => g.val.inv * P.val.map f) :=
      (Units.continuous_val.comp continuous_subtype_val.inv).mul continuous_const
    exact (hPhi.comp hc.measurable).mul hCusp
  have hZero (j : J) : integral (mu.restrict D) (fun g : G =>
      tsum (fun P : IndexFiber q j => F P.val g)) = 0 := by
    have hSurj : Function.Surjective q := Quotient.mk_surjective
    choose P hP using hSurj j
    subst j
    let r := P.val.rank
    let k := Fintype.card (Fin n) - r
    have hOrb := exists_godementJacquetSingularOrbit P.val P.property.1
    have hr : 0 < r := P.property.2
    have hk : 0 < k := hOrb.1
    choose e a b hab using hOrb.2
    let C := GodementJacquetUnipotentClassGroup K r k
    let : MeasurableSpace C := borel C
    let : BorelSpace C := BorelSpace.mk rfl
    have hData := hPeriods r k hr hk e a
    choose nu hNu using hData
    let : nu.IsHaarMeasure := hNu.1
    let : IsProbabilityMeasure nu := hNu.2.1
    let : nu.IsMulRightInvariant := hNu.2.2.1
    choose representative hRep using hNu.2.2.2
    let H := RationalStabilizer e a
    let M := Set.iUnion (leftSubgroupCosetTile H Gamma D)
    let JH := LeftSubgroupCosets H Gamma
    let PA := P.val.map f
    let A := godementJacquetPositiveSingularFiberEquiv P
    let E : Equiv JH (godementJacquetRationalMatrixOrbit P.val) :=
      leftSubgroupCosetEquivRange H Gamma (fun gamma => gamma.val.val.inv * PA)
        (rationalMatrixOrbit_fiber P.val e a b hab)
    let liftMatrix (j : JH) : I := (A.symm (E j)).val
    have hLift : Function.Injective liftMatrix :=
      Subtype.val_injective.comp (A.symm.injective.comp E.injective)
    have hSub : H <= Gamma := orbitStabilizer_le_principal P.val e a b hab
    have hEntry (j : JH) : (E j).val = (liftMatrix j).val.map f :=
      (congrArg (fun Q : godementJacquetRationalMatrixOrbit P.val => Q.val)
        (A.apply_symm_apply (E j))).symm
    have hTerm (j : JH) (g : G) :
        F P ((leftSubgroupCosetRepresentative H Gamma j).val * g) = F (liftMatrix j) g := by
      let gamma := leftSubgroupCosetRepresentative H Gamma j
      change phi ((g.val.inv * gamma.val.val.inv) * PA) * cusp (gamma.val * g) =
        phi (g.val.inv * (liftMatrix j).val.map f) * cusp g
      rw [Matrix.mul_assoc, hInvariant gamma g, <- hEntry j]
      rfl
    have hInt : IntegrableOn (F P) M mu := by
      refine And.intro (hF P).aestronglyMeasurable ?_
      change lintegral (mu.restrict M) (fun g => enorm (F P g)) < Top.top
      rw [lintegral_leftSubgroupCosetTiles_eq_tsum H Gamma hSub mu D hD hUnique _ (hF P).enorm]
      refine lt_of_le_of_lt (lintegral_mono (fun g => ?_)) hAbs
      simp_rw [hTerm]
      exact ENNReal.summable.tsum_le_tsum_of_inj liftMatrix hLift
        (fun _ _ => zero_le) (fun _ => le_rfl) ENNReal.summable
    have hOrbZero := integral_godementJacquetSingularOrbit_eq_zero_of_cuspidal P.val e a b hab
      nu mu D hD hUnique phi hPhi cusp hCusp hInvariant representative hRep.1 hRep.2 hInt
    have hFiber (g : G) : tsum (fun Q : IndexFiber q (q P) => F Q.val g) =
        (tsum (fun Q : godementJacquetRationalMatrixOrbit P.val => phi (g.val.inv * Q.val))) * cusp g := by
      simp only [F, tsum_mul_right]
      exact congrArg (fun z : Complex => z * cusp g)
        (A.tsum_eq (fun Q => phi (g.val.inv * Q.val)))
    simp_rw [hFiber]
    exact hOrbZero
  have h := integral_tsum_eq_zero_of_fiberIntegrals q (mu.restrict D) F hF
    (fun g => (hSum g).mul_right (cusp g)) hAbs hZero
  simpa only [F, tsum_mul_right] using h

end RationalSingularIndex

section RationalMatrixSplit

universe u

variable {K : Type u} [Field K] {n : Nat}

private theorem matrix_eq_zero_of_rank_eq_zero
    (P : Matrix (Fin n) (Fin n) K) (hP : P.rank = 0) : P = 0 := by
  have hRange : LinearMap.range P.mulVecLin = Bot.bot := Submodule.finrank_eq_zero.mp hP
  have hLin : P.mulVecLin = 0 := LinearMap.range_eq_bot.mp hRange
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_zero, hLin]

/-- Every rational matrix of positive size is invertible, singular of
positive rank, or the zero matrix. -/
def godementJacquetRationalMatrixSplitEquiv (hn : 0 < n) :
    Equiv (Sum (Matrix.GeneralLinearGroup (Fin n) K)
      (Sum (GodementJacquetPositiveSingularMatrix K n) Unit)) (Matrix (Fin n) (Fin n) K) := by
  let : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hn)
  let RationalGL := Matrix.GeneralLinearGroup (Fin n) K
  let S := GodementJacquetPositiveSingularMatrix K n
  let right : Sum S Unit -> Matrix (Fin n) (Fin n) K := Sum.elim Subtype.val (fun _ => 0)
  let f : Sum RationalGL (Sum S Unit) -> Matrix (Fin n) (Fin n) K := Sum.elim Units.val right
  have hZero : (0 : Matrix (Fin n) (Fin n) K).det = 0 := Matrix.det_zero
  have hDetRight (P : Sum S Unit) : (right P).det = 0 := by
    cases P with
    | inl P => exact P.property.1
    | inr _ => exact hZero
  have hDetLeft (P : RationalGL) : Not (P.val.det = 0) :=
    ((Matrix.isUnit_iff_isUnit_det P.val).mp P.isUnit).ne_zero
  have hNotZero (P : S) : Not (P.val = 0) := by
    intro hp
    have hr := P.property.2
    rw [hp, Matrix.rank_zero] at hr
    exact (Nat.lt_irrefl 0) hr
  have hIRight : Function.Injective right := by
    intro A B h
    cases A with
    | inl A =>
      cases B with
      | inl B => exact congrArg Sum.inl (Subtype.ext h)
      | inr _ => exact False.elim (hNotZero A h)
    | inr A =>
      cases B with
      | inl B => exact False.elim (hNotZero B h.symm)
      | inr B => exact congrArg Sum.inr (Subsingleton.elim A B)
  refine Equiv.ofBijective f (And.intro ?_ ?_)
  . intro A B h
    cases A with
    | inl A =>
      cases B with
      | inl B => exact congrArg Sum.inl (Units.ext h)
      | inr B => exact False.elim (hDetLeft A ((congrArg Matrix.det h).trans (hDetRight B)))
    | inr A =>
      cases B with
      | inl B => exact False.elim (hDetLeft B ((congrArg Matrix.det h.symm).trans (hDetRight A)))
      | inr B => exact congrArg Sum.inr (hIRight h)
  . intro P
    by_cases hd : P.det = 0
    . by_cases hr : P.rank = 0
      . exact Exists.intro (Sum.inr (Sum.inr ())) (matrix_eq_zero_of_rank_eq_zero P hr).symm
      . exact Exists.intro (Sum.inr (Sum.inl (Subtype.mk P (And.intro hd (Nat.pos_of_ne_zero hr))))) rfl
    . have hP := (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hd)
      exact Exists.intro (Sum.inl hP.unit) hP.unit_spec

/-- The partition of rational matrices splits any convergent theta sum
into its invertible, positive-rank singular, and zero contributions. -/
theorem godementJacquetRationalMatrixTsum_split (hn : 0 < n)
    (f : Matrix (Fin n) (Fin n) K -> Complex) (hf : Summable f) :
    tsum f = (tsum (fun A : Matrix.GeneralLinearGroup (Fin n) K => f A.val)) +
      ((tsum (fun A : GodementJacquetPositiveSingularMatrix K n => f A.val)) + f 0) := by
  let RationalGL := Matrix.GeneralLinearGroup (Fin n) K
  let S := GodementJacquetPositiveSingularMatrix K n
  let e := godementJacquetRationalMatrixSplitEquiv (K := K) hn
  let g := f.comp e
  let right : Sum S Unit -> Complex := g.comp Sum.inr
  have h := hf.comp_injective e.injective
  have hleft : Summable (g.comp (Sum.inl : RationalGL -> Sum RationalGL (Sum S Unit))) :=
    h.comp_injective Sum.inl_injective
  have hright : Summable right := h.comp_injective Sum.inr_injective
  have hpos : Summable (right.comp (Sum.inl : S -> Sum S Unit)) :=
    hright.comp_injective Sum.inl_injective
  have hzero : Summable (right.comp (Sum.inr : Unit -> Sum S Unit)) :=
    hright.comp_injective Sum.inr_injective
  rw [<- e.tsum_eq f]
  change tsum g = _
  rw [Summable.tsum_sum hleft hright]
  change _ + tsum right = _
  rw [Summable.tsum_sum hpos hzero]
  have hUnit : tsum (fun u : Unit => right (Sum.inr u)) = f 0 :=
    tsum_eq_single () (fun u hu => False.elim (hu (Subsingleton.elim u ())))
  rw [hUnit]
  rfl

section FullCuspidalTheta

variable [NumberField K]

/-- Under absolute integrability the full rational theta integral equals its
invertible part. The proper unipotent periods remove the positive-rank terms
and the average of the cusp form removes the zero matrix term. -/
theorem integral_godementJacquetFullTheta_eq_invertible_of_cuspidal (hn : 0 < n)
    [MeasurableSpace (NormGroup K n)] [BorelSpace (NormGroup K n)]
    (mu : Measure (NormGroup K n)) [SFinite mu] [mu.IsMulLeftInvariant]
    (D : Set (NormGroup K n)) (hD : MeasurableSet D)
    (hUnique : forall g : NormGroup K n, ExistsUnique
      (fun gamma : (adelicPrincipalDeterminantOne K n).range => Membership.mem D (gamma.val * g)))
    [MeasurableSpace (Matrix (Fin n) (Fin n) (Adeles K))]
    [BorelSpace (Matrix (Fin n) (Fin n) (Adeles K))]
    (phi : Matrix (Fin n) (Fin n) (Adeles K) -> Complex) (hPhi : Measurable phi)
    (cusp : NormGroup K n -> Complex) (hCusp : Measurable cusp)
    (hInvariant : forall gamma : (adelicPrincipalDeterminantOne K n).range, forall g,
      cusp (gamma.val * g) = cusp g)
    (hPeriods : HasGodementJacquetVanishingUnipotentPeriods cusp)
    (hCuspInt : IntegrableOn cusp D mu) (hMean : integral (mu.restrict D) cusp = 0)
    (hSum : forall g : NormGroup K n,
      Summable (fun P : Matrix (Fin n) (Fin n) K =>
        phi (g.val.inv * P.map (algebraMap K (Adeles K)))))
    (hAbs : lintegral (mu.restrict D) (fun g : NormGroup K n =>
      tsum (fun P : Matrix (Fin n) (Fin n) K =>
        enorm (phi (g.val.inv * P.map (algebraMap K (Adeles K))) * cusp g))) <
      (Top.top : ENNReal)) :
    integral (mu.restrict D) (fun g : NormGroup K n =>
      (tsum (fun P : Matrix (Fin n) (Fin n) K =>
        phi (g.val.inv * P.map (algebraMap K (Adeles K))))) * cusp g) =
    integral (mu.restrict D) (fun g : NormGroup K n =>
      (tsum (fun P : Matrix.GeneralLinearGroup (Fin n) K =>
        phi (g.val.inv * P.val.map (algebraMap K (Adeles K))))) * cusp g) := by
  let G := NormGroup K n
  let M := Matrix (Fin n) (Fin n) K
  let R := Matrix.GeneralLinearGroup (Fin n) K
  let S := GodementJacquetPositiveSingularMatrix K n
  let m := mu.restrict D
  let f := algebraMap K (Adeles K)
  let KPhi (P : M) (g : G) := phi (g.val.inv * P.map f)
  let F (P : M) (g : G) := KPhi P g * cusp g
  let RTerm (g : G) := (tsum (fun P : R => KPhi P.val g)) * cusp g
  let STerm (g : G) := (tsum (fun P : S => KPhi P.val g)) * cusp g
  let ZTerm (g : G) := phi 0 * cusp g
  let : Countable K := (Module.finBasis Rat K).equivFun.injective.countable
  let : Countable M := inferInstanceAs (Countable (Fin n -> Fin n -> K))
  let : SecondCountableTopology (AdelicGeneralLinearGroup K n) :=
    secondCountableTopology_adelicGeneralLinearGroup K n
  let : SecondCountableTopology G :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (fun g : G => g.val)).secondCountableTopology
  have hF (P : M) : Measurable (F P) := by
    have hc : Continuous (fun g : G => g.val.inv * P.map f) :=
      (Units.continuous_val.comp continuous_subtype_val.inv).mul continuous_const
    exact (hPhi.comp hc.measurable).mul hCusp
  have hAbsSub {A : Type u} (i : A -> M) (hi : Function.Injective i) :
      lintegral m (fun g => tsum (fun a => enorm (F (i a) g))) < Top.top := by
    apply lt_of_le_of_lt (lintegral_mono (fun g => ?_)) hAbs
    exact ENNReal.summable.tsum_le_tsum_of_inj i hi
      (fun _ _ => zero_le) (fun _ => le_rfl) ENNReal.summable
  have hIntSub {A : Type u} (i : A -> M) (hi : Function.Injective i) :
      Integrable (fun g : G => (tsum (fun a => KPhi (i a) g)) * cusp g) m := by
    let : Countable A := hi.countable
    have hSumF (g : G) : Summable (fun a => F (i a) g) :=
      ((hSum g).mul_right (cusp g)).comp_injective hi
    have hMeas := measurable_complexTsum_of_summable (fun a => F (i a)) (fun a => hF (i a)) hSumF
    have hInt : Integrable (fun g : G => tsum (fun a => F (i a) g)) m :=
      And.intro hMeas.aestronglyMeasurable
        (lt_of_le_of_lt (lintegral_mono (fun g => enorm_tsum_le_tsum_enorm)) (hAbsSub i hi))
    simpa only [F, tsum_mul_right] using hInt
  have hRInt : Integrable RTerm m := hIntSub (fun P : R => P.val) Units.val_injective
  have hSInt : Integrable STerm m := hIntSub (fun P : S => P.val) Subtype.val_injective
  have hZInt : Integrable ZTerm m := hCuspInt.smul (phi 0)
  have hSZ : integral m STerm = 0 :=
    integral_godementJacquetPositiveSingularTheta_eq_zero mu D hD hUnique phi hPhi cusp hCusp
      hInvariant hPeriods (fun g => (hSum g).comp_injective (Subtype.val_injective (p := fun Q : M =>
        And (Q.det = 0) (0 < Q.rank)))) (hAbsSub (fun P : S => P.val) Subtype.val_injective)
  have hZZ : integral m ZTerm = 0 := by
    change integral m (fun g => phi 0 * cusp g) = 0
    rw [integral_const_mul, hMean, mul_zero]
  have hSplit (g : G) : (tsum (fun P : M => KPhi P g)) * cusp g =
      RTerm g + (STerm g + ZTerm g) := by
    rw [godementJacquetRationalMatrixTsum_split hn (fun P : M => KPhi P g) (hSum g)]
    have hMapZero : (0 : M).map f = 0 := Matrix.ext (fun _ _ => map_zero f)
    simp only [RTerm, STerm, ZTerm, KPhi, hMapZero, Matrix.mul_zero, add_mul]
    rfl
  change integral m (fun g : G => (tsum (fun P : M => KPhi P g)) * cusp g) = integral m RTerm
  simp_rw [hSplit]
  calc
    integral m (fun g => RTerm g + (STerm g + ZTerm g)) =
        integral m RTerm + integral m (fun g => STerm g + ZTerm g) :=
      integral_add hRInt (hSInt.add hZInt)
    _ = integral m RTerm + (integral m STerm + integral m ZTerm) :=
      congrArg (fun z : Complex => integral m RTerm + z) (integral_add hSInt hZInt)
    _ = _ := by rw [hSZ, hZZ, add_zero, add_zero]

end FullCuspidalTheta

end RationalMatrixSplit

end Robin1984.GRH
