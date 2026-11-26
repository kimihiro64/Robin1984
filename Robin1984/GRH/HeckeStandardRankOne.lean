import Robin1984.GRH.HeckePoleFreeMultiplicity

/-!
## Provenance

- Classification: **Primarily project-original**.
- Mathematical source: Tate's standard unitary Hecke completions and the individual and paired prime-power criteria.
- Formalization note: States the critical-line and prescribed-order equivalences for the full standard rank-one family over a number field.
- PROVENANCE-END
-/

/-!
# The prime-power criteria for the standard rank-one family

The family consists of all unitary Hecke characters of a number field.
The norm characters use vertical translates of the pole-cleared Dedekind
completion. Every other character uses the pole-free Tate completion and
its individual coefficients for the prescribed-order test.
-/

set_option autoImplicit false

noncomputable section
namespace Robin1984.GRH

variable (K : Type*) [Field K] [NumberField K]

/-- The standard entire unitary Hecke completions, specified by the
completed Euler products and the pole-cleared Dedekind norm twists. -/
structure IsHeckeStandardCompletedFamily (L : UnitaryHeckeCharacter K -> Complex -> Complex) : Prop where
  entire : forall chi, Differentiable Complex (L chi)
  poleFreeEuler : forall (i : HeckePoleFreeCharacter K) (s : Complex), 1 < s.re ->
    L i.val s = heckeTateStandardCompletedEulerValue i.val s
  normTwist : forall (chi : UnitaryHeckeCharacter K),
    (forall z : heckeNormOneIdeleClass K, heckeNormOneClassCharacter chi z = 1) ->
    exists t : Real, And (chi = heckeNormCharacter t)
      (forall s : Complex, L chi s =
        DedekindZeta.completedDedekindPoleCleared K (s + (t : Complex) * Complex.I))

/-- Prescribed zero orders for a vertical translate, indexed by the
ordinates of the original function. -/
def HasNormTwistPrescribedZeroOrders (F : Complex -> Complex) (t : Real)
    (E J : Finset Real) (order : Real -> Nat) : Prop :=
  And (forall delta, Not (Membership.mem E delta) ->
    analyticOrderNatAt F (multiplicityCriticalPoint (delta - t)) <= 1)
  (forall delta, Membership.mem J delta ->
    analyticOrderNatAt F (multiplicityCriticalPoint (delta - t)) = order delta)

/-- The Dedekind multiplicity inequality gives the prescribed orders of
every pole-cleared Dedekind norm twist in the translated coordinates. -/
theorem completedDedekindNormTwist_prescribedOrders_iff
    (t : Real) (E J : Finset Real) (order : Real -> Nat) (hERH : DedekindRH K) :
    HasNormTwistPrescribedZeroOrders
      (fun s : Complex => DedekindZeta.completedDedekindPoleCleared K
        (s + (t : Complex) * Complex.I)) t E J order <->
    ExceptionalPrimePowerMultiplicityInequality
      (dedekindPrimeIdealMultiplicityLogInput K) E J order := by
  unfold HasNormTwistPrescribedZeroOrders
  simp only [completedDedekindNormTwist_order]
  exact dedekindERH_prescribedOrders_iff_globalPrimeIdealMultiplicity K E J order hERH

/-- Prescribed zero orders for the whole standard rank-one family.
The data for the Dedekind completion are shared by its norm twists. -/
def HeckeStandardFamilyPrescribedZeroOrders
    (L : UnitaryHeckeCharacter K -> Complex -> Complex)
    (E0 J0 : Finset Real) (order0 : Real -> Nat)
    (E J : HeckePoleFreeCharacter K -> Finset Real)
    (order : HeckePoleFreeCharacter K -> Real -> Nat) : Prop :=
  And (forall (chi : UnitaryHeckeCharacter K),
    (forall z : heckeNormOneIdeleClass K, heckeNormOneClassCharacter chi z = 1) ->
    exists t : Real, And (chi = heckeNormCharacter t)
      (And (forall s : Complex, L chi s =
        DedekindZeta.completedDedekindPoleCleared K (s + (t : Complex) * Complex.I))
        (HasNormTwistPrescribedZeroOrders (L chi) t E0 J0 order0)))
    (forall i, HasPrescribedZeroOrders (L i.val) (E i) (J i) (order i))

/-- On the critical line, prescribed zero orders for the full standard
rank-one family are equivalent to the Dedekind prime-ideal inequality
and the individual pole-free Hecke prime-power inequalities. -/
theorem heckeStandardFamily_prescribedOrders_iff_globalMultiplicityInequality
    (L : UnitaryHeckeCharacter K -> Complex -> Complex)
    (hL : IsHeckeStandardCompletedFamily K L) (hRH : CompletedFamilyRH L)
    (E0 J0 : Finset Real) (order0 : Real -> Nat)
    (E J : HeckePoleFreeCharacter K -> Finset Real)
    (order : HeckePoleFreeCharacter K -> Real -> Nat) :
    HeckeStandardFamilyPrescribedZeroOrders K L E0 J0 order0 E J order <->
      And (ExceptionalPrimePowerMultiplicityInequality
        (dedekindPrimeIdealMultiplicityLogInput K) E0 J0 order0)
        (forall i, ExceptionalPrimePowerMultiplicityInequality
          (heckePrimePowerMultiplicitySignal K i.val) (E i) (J i) (order i)) := by
  let chi0 : UnitaryHeckeCharacter K := heckeNormCharacter 0
  have hChi0 : forall z : heckeNormOneIdeleClass K, heckeNormOneClassCharacter chi0 z = 1 :=
    (heckeNormOneClassCharacter_trivial_iff_normCharacter chi0).mpr (Exists.intro 0 rfl)
  choose t0 _ hTwist0 using hL.normTwist chi0 hChi0
  have hDedLine (s : Complex) (hs : DedekindZeta.completedDedekindPoleCleared K
      (s + (t0 : Complex) * Complex.I) = 0) : s.re = 1 / 2 :=
    hRH chi0 s ((hTwist0 s).trans hs)
  have hERH := (dedekindRH_iff_dedekindTriangularRobin K).mpr
    ((completedDedekindNormTwist_RH_iff_triangular K t0).mp hDedLine)
  have hFree := heckePoleFree_prescribedOrders_iff_globalMultiplicityInequality K
    (fun i => L i.val) (fun i => hL.entire i.val) hL.poleFreeEuler E J order
    (fun i => hRH i.val)
  constructor
  . intro h
    choose t _ hTwist hOrder using h.1 chi0 hChi0
    have hF : L chi0 = fun s : Complex => DedekindZeta.completedDedekindPoleCleared K
        (s + (t : Complex) * Complex.I) := funext hTwist
    rw [hF] at hOrder
    exact And.intro ((completedDedekindNormTwist_prescribedOrders_iff K t E0 J0 order0 hERH).mp hOrder)
      (hFree.mp h.2)
  . intro h
    refine And.intro ?_ (hFree.mpr h.2)
    intro chi hc
    choose t ht hTwist using hL.normTwist chi hc
    refine Exists.intro t (And.intro ht (And.intro hTwist ?_))
    have hF : L chi = fun s : Complex => DedekindZeta.completedDedekindPoleCleared K
        (s + (t : Complex) * Complex.I) := funext hTwist
    rw [hF]
    exact (completedDedekindNormTwist_prescribedOrders_iff K t E0 J0 order0 hERH).mpr h.1

/-- Over every number field there is a standard completed rank-one
family, and the critical-line hypothesis for all its members is equivalent
to the Dedekind and paired Hecke triangular bounds. -/
theorem exists_heckeStandardFamily_criticalLine_iff_triangularBounds :
    exists L : UnitaryHeckeCharacter K -> Complex -> Complex,
      And (IsHeckeStandardCompletedFamily K L)
        (CompletedFamilyRH L <-> And (DedekindTriangularRobin K)
          (forall i : HeckePoleFreeCharacter K, HeckeTriangularBound i.val 0)) := by
  choose L hL using exists_heckeStandardCompletedFamily_triangularCriterion K
  exact Exists.intro L (And.intro
    { entire := hL.1, poleFreeEuler := hL.2.1, normTwist := hL.2.2.1 } hL.2.2.2)

end Robin1984.GRH
