import DedekindZeta.PoissonSummation

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Poisson summation for full-rank Euclidean lattices and the matrix lattice in the Godement-Jacquet zeta integral.
- Formalization note: Identifies the product lattice, its dual, and its covolume, then applies shifted Poisson summation to an arbitrary Schwartz function on the product.
- PROVENANCE-END
-/

/-!
# Euclidean product lattices in the matrix Poisson formula

A finite product of copies of a full-rank lattice is again a full-rank
lattice. In the Euclidean product norm its volume is product measure,
its covolume is the corresponding power, and its dual lattice is the
product of the original dual lattices.

The shifted Poisson formula applies to every Schwartz function on the
product space. In particular, the choice of coordinates can enumerate
the entries of a rational matrix.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

section ProductLattice

variable (I : Type*) [Fintype I] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

private def piZLattice (L : Submodule Int E) : Submodule Int (I -> E) :=
  Submodule.pi Set.univ (fun _ : I => L)

private instance (L : Submodule Int E) [DiscreteTopology L] :
    DiscreteTopology (piZLattice I L) := by
  let r (x : piZLattice I L) (i : I) : L :=
    Subtype.mk (x.val i) ((Submodule.mem_pi.mp x.property) i (Set.mem_univ i))
  have hc : Continuous r := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective r := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg (fun z : I -> L => (z i).val) h
  exact DiscreteTopology.of_continuous_injective hc hi

private instance (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L] :
    IsZLattice Real (piZLattice I L) where
  span_top := by
    classical
    let S := Submodule.span Real (piZLattice I L : Set (I -> E))
    have hcoord (i : I) (x : E) : Membership.mem S (Pi.single i x) := by
      let f : LinearMap (RingHom.id Real) E (I -> E) := LinearMap.single Real (fun _ : I => E) i
      have h (y : E) (hy : Membership.mem L y) :
          Membership.mem (S.comap f) y := by
        change Membership.mem S (Pi.single i y)
        apply Submodule.subset_span
        apply Submodule.mem_pi.mpr
        intro j _
        by_cases hij : j = i
        . subst j
          simp [hy]
        . simp [Pi.single_eq_of_ne hij]
      have hc := Submodule.span_le.mpr h
      have hx : Membership.mem (Submodule.span Real (L : Set E)) x := by
        rw [IsZLattice.span_top]
        exact Submodule.mem_top
      exact hc hx
    apply top_unique
    intro x _
    have he : Finset.univ.sum (fun i : I => Pi.single i (x i)) = x := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [<- he]
    exact Submodule.sum_mem S (fun i _ => hcoord i (x i))

/-- The Cartesian product of a lattice with itself, in the Euclidean product norm. -/
def euclideanProductZLattice (L : Submodule Int E) :
    Submodule Int (PiLp 2 (fun _ : I => E)) :=
  ZLattice.comap Real (piZLattice I L)
    (PiLp.continuousLinearEquiv 2 Real (fun _ : I => E)).toLinearMap

instance (L : Submodule Int E) [DiscreteTopology L] :
    DiscreteTopology (euclideanProductZLattice I L) := by
  unfold euclideanProductZLattice
  infer_instance

instance (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L] :
    IsZLattice Real (euclideanProductZLattice I L) := by
  unfold euclideanProductZLattice
  infer_instance

theorem mem_euclideanProductZLattice (L : Submodule Int E)
    (x : PiLp 2 (fun _ : I => E)) :
    Membership.mem (euclideanProductZLattice I L) x <->
      forall i : I, Membership.mem L (x i) := by
  change Membership.mem (Submodule.pi Set.univ (fun _ : I => L)) (WithLp.ofLp x) <-> _
  simp [Submodule.mem_pi]

end ProductLattice

section ProductVolume

open MeasureTheory
open scoped RealInnerProductSpace

private theorem measurePreserving_curryReal (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (fun f : Sigma (fun _ : I => J) -> Real => fun i j => f (Sigma.mk i j))
      (Measure.pi (fun _ : Sigma (fun _ : I => J) => (volume : Measure Real)))
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => (volume : Measure Real)))) := by
  classical
  let e : MeasurableEquiv (Sigma (fun _ : I => J) -> Real) (I -> J -> Real) :=
    { toEquiv :=
        { toFun := fun u i j => u (Sigma.mk i j)
          invFun := fun v p => v p.1 p.2
          left_inv := fun u => by funext p; cases p; rfl
          right_inv := fun _ => rfl }
      measurable_toFun := by
        refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
        change Measurable (fun u : Sigma (fun _ : I => J) -> Real => u (Sigma.mk i j))
        exact measurable_pi_apply (@Sigma.mk I (fun _ : I => J) i j)
      measurable_invFun := measurable_pi_lambda _ (fun p =>
        (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)) }
  have he : MeasurePreserving e.symm
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => (volume : Measure Real))))
      (Measure.pi (fun _ : Sigma (fun _ : I => J) => (volume : Measure Real))) := by
    refine MeasurePreserving.mk e.symm.measurable ?_
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply e.symm.measurable (MeasurableSet.pi Set.countable_univ (fun p _ => hs p))]
    have hpre : Set.preimage e.symm (Set.pi Set.univ s) =
        Set.pi Set.univ (fun i : I => Set.pi Set.univ (fun j : J => s (Sigma.mk i j))) := by
      ext v
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
      constructor
      . intro hv i j
        exact hv (Sigma.mk i j)
      . intro hv p
        exact hv p.1 p.2
    rw [hpre, Measure.pi_pi]
    simp only [Measure.pi_pi]
    rw [<- Finset.univ_sigma_univ, Finset.prod_sigma]
  exact MeasurePreserving.symm e.symm he

theorem measurePreserving_euclidean_product_ofLp (I E : Type*) [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] :
    MeasurePreserving (WithLp.ofLp : PiLp 2 (fun _ : I => E) -> I -> E)
      volume (Measure.pi (fun _ : I => (volume : Measure E))) := by
  classical
  let J := Fin (Module.finrank Real E)
  let o : OrthonormalBasis J Real E := stdOrthonormalBasis Real E
  let JI := Sigma (fun _ : I => J)
  let c := LinearIsometryEquiv.piLpCurry Real 2 (fun (_ : I) (_ : J) => Real)
  let d := LinearIsometryEquiv.piLpCongrRight 2 (fun _ : I => o.repr.symm)
  let e := c.trans d
  have hcoords : MeasurePreserving (fun f : I -> J -> Real => fun i =>
      o.repr.symm (WithLp.toLp 2 (f i)))
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => (volume : Measure Real))))
      (Measure.pi (fun _ : I => (volume : Measure E))) :=
    measurePreserving_pi _ _ (fun _ => o.measurePreserving_repr_symm.comp
      (PiLp.volume_preserving_toLp J))
  have hreal := (measurePreserving_curryReal I J).comp (PiLp.volume_preserving_ofLp JI)
  have he : MeasurePreserving (Function.comp WithLp.ofLp e)
      (volume : Measure (EuclideanSpace Real JI)) (Measure.pi (fun _ : I => (volume : Measure E))) := by
    exact hcoords.comp hreal
  have h := he.comp e.symm.measurePreserving
  have hf : Function.comp (Function.comp WithLp.ofLp e) e.symm =
      (WithLp.ofLp : PiLp 2 (fun _ : I => E) -> I -> E) := by
    funext x
    change WithLp.ofLp (e (e.symm x)) = WithLp.ofLp x
    rw [e.apply_symm_apply]
  rw [hf] at h
  exact h

/-- The covolume of a finite Euclidean product of copies of a lattice
is the corresponding power of the original covolume. -/
theorem covolume_euclideanProductZLattice (I : Type*) [Fintype I] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L]
    {J : Type*} [Finite J] (b : Module.Basis J Int L) :
    ZLattice.covolume (euclideanProductZLattice I L) volume =
      (ZLattice.covolume L volume) ^ Fintype.card I := by
  classical
  let V := PiLp 2 (fun _ : I => E)
  let Lambda := euclideanProductZLattice I L
  let D := ZSpan.fundamentalDomain (b.ofZLatticeBasis Real)
  let rect := Set.pi Set.univ (fun _ : I => D)
  let Dprod : Set V := Set.preimage WithLp.ofLp rect
  have hOne : IsAddFundamentalDomain L D (volume : Measure E) :=
    ZLattice.isAddFundamentalDomain b volume
  have hD : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet (b.ofZLatticeBasis Real)
  have hRect : MeasurableSet rect := MeasurableSet.pi Set.countable_univ (fun _ _ => hD)
  have hp := measurePreserving_euclidean_product_ofLp I E
  have hDprod : MeasurableSet Dprod := hp.measurable hRect
  have hExact (x : E) :
      ExistsUnique (fun l : L => Membership.mem D (l.val + x)) := by
    let L0 := Submodule.span Int (Set.range (b.ofZLatticeBasis Real))
    have hL : L0 = L := b.ofZLatticeBasis_span Real
    choose u hu using ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis Real) x
    let v : L := Subtype.mk u.val
      ((congrArg (fun S : Submodule Int E => Membership.mem S u.val) hL).mp u.property)
    refine ExistsUnique.intro v hu.1 ?_
    intro y hy
    let w : L0 := Subtype.mk y.val
      ((congrArg (fun S : Submodule Int E => Membership.mem S y.val) hL).mpr y.property)
    apply Subtype.ext
    exact congrArg (fun z : L0 => z.val) (hu.2 w hy)
  have hmem (x : V) : Membership.mem Dprod x <->
      forall i : I, Membership.mem D (x i) := by
    simp [Dprod, rect, Set.mem_pi]
  have hMany : IsAddFundamentalDomain Lambda Dprod (volume : Measure V) := by
    refine IsAddFundamentalDomain.mk' hDprod.nullMeasurableSet ?_
    intro x
    choose l hl using fun i : I => hExact (x i)
    let y : V := WithLp.toLp 2 (fun i : I => (l i).val)
    let z : Lambda := Subtype.mk y ((mem_euclideanProductZLattice I L y).mpr
      (fun i => (l i).property))
    refine ExistsUnique.intro z ?_ ?_
    . apply (hmem _).mpr
      intro i
      exact (hl i).1
    . intro w hw
      apply Subtype.ext
      apply (PiLp.continuousLinearEquiv 2 Real (fun _ : I => E)).injective
      funext i
      let wi : L := Subtype.mk (w.val i)
        ((mem_euclideanProductZLattice I L w.val).mp w.property i)
      have hwi : Membership.mem D (wi.val + x i) := (hmem _).mp hw i
      exact congrArg Subtype.val ((hl i).2 wi hwi)
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Lambda volume hMany,
    ZLattice.covolume_eq_measure_fundamentalDomain L volume hOne]
  have hVol := hp.measure_preimage hRect.nullMeasurableSet
  change (volume : Measure V) Dprod =
    (Measure.pi (fun _ : I => (volume : Measure E))) rect at hVol
  change ENNReal.toReal ((volume : Measure V) Dprod) =
    (ENNReal.toReal ((volume : Measure E) D)) ^ Fintype.card I
  rw [hVol]
  simp [rect, Measure.pi_pi, ENNReal.toReal_pow]

end ProductVolume

section ProductDual

variable (I : Type*) [Fintype I] {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]

/-- Taking the dual lattice for the Euclidean product inner product
acts on each lattice coordinate. -/
theorem dualLattice_euclideanProductZLattice (L : Submodule Int E) :
    DedekindZeta.PoissonSummation.dualLattice (euclideanProductZLattice I L) =
      euclideanProductZLattice I (DedekindZeta.PoissonSummation.dualLattice L) := by
  classical
  ext w
  rw [DedekindZeta.PoissonSummation.mem_dualLattice, mem_euclideanProductZLattice]
  constructor
  . intro h i
    apply DedekindZeta.PoissonSummation.mem_dualLattice.mpr
    intro x hx
    let v : I -> E := Pi.single i x
    let y : PiLp 2 (fun _ : I => E) := WithLp.toLp 2 v
    have hy : Membership.mem (euclideanProductZLattice I L) y := by
      apply (mem_euclideanProductZLattice I L y).mpr
      intro j
      change Membership.mem L (v j)
      by_cases hij : j = i
      . subst j
        simp [v, hx]
      . simp [v, Pi.single_eq_of_ne hij]
    have hinner : inner Real w y = inner Real (w i) x := by
      rw [PiLp.inner_apply]
      change Finset.univ.sum (fun j : I => inner Real (w j) (v j)) =
        inner Real (w i) x
      rw [Finset.sum_eq_single i]
      . simp [v]
      . intro j _ hji
        simp [v, Pi.single_eq_of_ne hji]
      . simp
    rw [<- hinner]
    exact h y hy
  . intro h x hx
    rw [PiLp.inner_apply]
    apply Submodule.sum_mem
    intro i _
    exact (DedekindZeta.PoissonSummation.mem_dualLattice.mp (h i)) (x i)
      ((mem_euclideanProductZLattice I L x).mp hx i)

open MeasureTheory
open scoped RealInnerProductSpace FourierTransform

/-- Shifted Poisson summation for an arbitrary Schwartz function on
the Euclidean product of copies of a full-rank lattice. -/
theorem poisson_euclideanProductZLattice (L : Submodule Int E)
    [DiscreteTopology L] [IsZLattice Real L] {J : Type*} [Finite J]
    (b : Module.Basis J Int L) (f : SchwartzMap (PiLp 2 (fun _ : I => E)) Complex)
    (x : PiLp 2 (fun _ : I => E)) :
    tsum (fun v : euclideanProductZLattice I L => f (x + v.val)) =
      tsum (fun w : euclideanProductZLattice I (DedekindZeta.PoissonSummation.dualLattice L) =>
        (Real.fourierChar (inner Real x w.val) : Complex) *
          (Inv.inv (((ZLattice.covolume L volume) ^ Fintype.card I : Real) : Complex) *
            FourierTransform.fourier (f : PiLp 2 (fun _ : I => E) -> Complex) w.val)) := by
  rw [<- DedekindZeta.PoissonSummation.periodisation_apply,
    DedekindZeta.PoissonSummation.periodisation_eq_tsum_fourier,
    covolume_euclideanProductZLattice I L b, dualLattice_euclideanProductZLattice I L]
  rfl

end ProductDual

end Robin1984.GRH
