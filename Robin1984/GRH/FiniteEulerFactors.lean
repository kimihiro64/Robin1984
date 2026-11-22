import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Tuple.Basic

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: Products of finitely many absolutely convergent geometric series.
- Formalization note: Exponent assignments are reindexed by a product with one coordinate removed, and absolute convergence is retained at each step.
- PROVENANCE-END
-/

/-!
# Expanding finitely many Euler factors

The finite product of geometric factors is the absolutely summable
series indexed by all nonnegative exponents on those factors.
-/

namespace Robin1984.GRH

private theorem finiteGeometricSeries_fin (n : Nat) (a : Fin n -> Complex)
    (ha : forall i, norm (a i) < 1) :
    let W := fun e : Fin n -> Nat => Finset.univ.prod (fun i => a i ^ e i)
    And (Summable (fun e => norm (W e)))
      (tsum W = Finset.univ.prod (fun i => Inv.inv (1 - a i))) := by
  induction n with
  | zero =>
    let _ : Unique (Fin 0 -> Nat) :=
      { default := fun i => Fin.elim0 i, uniq := fun _ => funext (fun i => Fin.elim0 i) }
    let _ : Fintype (Fin 0 -> Nat) := Fintype.ofFinite _
    constructor
    exact (hasSum_fintype _).summable
    simp [tsum_fintype]
  | succ n ih =>
    let W := fun e : Fin (n + 1) -> Nat => Finset.univ.prod (fun i => a i ^ e i)
    let J := fun e : Fin n -> Nat => Finset.univ.prod (fun i => a i.succ ^ e i)
    let ix : Equiv (Prod Nat (Fin n -> Nat)) (Fin (n + 1) -> Nat) :=
      Fin.consEquiv (fun _ => Nat)
    have hJ := ih (fun i => a i.succ) (fun i => ha i.succ)
    have h0 : Summable (fun m : Nat => norm (a 0 ^ m)) :=
      summable_norm_geometric_of_norm_lt_one (ha 0)
    have hJnorm : Summable (fun e => norm (J e)) := hJ.1
    have hTerm (p : Prod Nat (Fin n -> Nat)) : W (ix p) = a 0 ^ p.1 * J p.2 := by
      change Finset.univ.prod (fun i => a i ^ Fin.cons p.1 p.2 i) = _
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ, J]
    have hProduct : Summable (fun p : Prod Nat (Fin n -> Nat) => norm (a 0 ^ p.1 * J p.2)) := by
      simpa only [norm_mul] using h0.mul_of_nonneg hJnorm
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hSum : Summable (fun e => norm (W e)) := by
      apply (ix.summable_iff).mp
      simpa only [Function.comp_def, hTerm] using hProduct
    refine And.intro hSum ?_
    calc
      tsum W = tsum (fun p : Prod Nat (Fin n -> Nat) => W (ix p)) := (ix.tsum_eq W).symm
      _ = tsum (fun p : Prod Nat (Fin n -> Nat) => a 0 ^ p.1 * J p.2) := tsum_congr hTerm
      _ = (tsum (fun m : Nat => a 0 ^ m)) * tsum J :=
        (tsum_mul_tsum_of_summable_norm h0 hJnorm).symm
      _ = _ := by
        rw [tsum_geometric_of_norm_lt_one (ha 0), show tsum J = _ from hJ.2, Fin.prod_univ_succ]

/-- The finite product of Euler factors expands over all exponent assignments. -/
theorem finiteGeometricSeries {P : Type*} [Fintype P] (a : P -> Complex)
    (ha : forall i, norm (a i) < 1) :
    let W := fun e : P -> Nat => Finset.univ.prod (fun i => a i ^ e i)
    And (Summable (fun e => norm (W e)))
      (tsum W = Finset.univ.prod (fun i => Inv.inv (1 - a i))) := by
  classical
  let n := Fintype.card P
  let i : Equiv (Fin n) P := (Fintype.equivFin P).symm
  let e : Equiv (Fin n -> Nat) (P -> Nat) := Equiv.arrowCongr i (Equiv.refl Nat)
  let W := fun p : P -> Nat => Finset.univ.prod (fun j => a j ^ p j)
  let V := fun q : Fin n -> Nat => Finset.univ.prod (fun j => a (i j) ^ q j)
  have h := finiteGeometricSeries_fin n (fun j => a (i j)) (fun j => ha (i j))
  have hTerm (q : Fin n -> Nat) : W (e q) = V q := by
    unfold W V
    rw [<- Equiv.prod_comp i (fun j => a j ^ e q j)]
    apply Finset.prod_congr rfl
    intro j _
    simp [e, Equiv.arrowCongr_apply]
  change And (Summable (fun p => norm (W p)))
    (tsum W = Finset.univ.prod (fun j => Inv.inv (1 - a j)))
  constructor
  case left =>
    apply (e.summable_iff).mp
    have hAbs : Summable (fun q => norm (V q)) := h.1
    simpa only [Function.comp_def, hTerm] using hAbs
  case right =>
    calc
      tsum W = tsum (fun q : Fin n -> Nat => W (e q)) := (e.tsum_eq W).symm
      _ = tsum V := tsum_congr hTerm
      _ = Finset.univ.prod (fun j => Inv.inv (1 - a (i j))) := h.2
      _ = Finset.univ.prod (fun j => Inv.inv (1 - a j)) :=
        Equiv.prod_comp i (fun j : P => Inv.inv (1 - a j))

end Robin1984.GRH
