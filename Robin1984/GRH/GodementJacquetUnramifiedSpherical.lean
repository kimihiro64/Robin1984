import Robin1984.GRH.GodementJacquetUnramifiedMeasure

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The unramified spherical section and unipotent integration in Goldfeld and Jacquet, Automorphic Representations and L-functions for GL(n), Section 2.4.
- Formalization note: Evaluates the unipotent fibre of the actual finite-place spherical kernel in every rank using the normalized additive-product measure.
- PROVENANCE-END
-/

/-!
# Unipotent integration of the unramified spherical section

Triangular-integral factorization defines the spherical section of a
normalized inducing character. With the matrix-integrality test, only
the scaled upper-entry box contributes on an integral diagonal. Its
Haar volume cancels the shift in the determinant weight and the half
modulus of the inducing character.
-/

set_option autoImplicit false

noncomputable section

namespace Robin1984.GRH

variable {F V : Type*} [Field F] [LinearOrderedCommGroupWithZero V]
variable (v : Valuation F V) (n : Nat)

local notation "G" => Units (Matrix (Fin n) (Fin n) F)
local notation "B" => valuationUpperTriangularSubgroup F n
local notation "K" => valuationIntegralMatrixSubgroup v n

/-- The right-integral-invariant section of the induced character,
defined using triangular-integral factorization. -/
def valuationSphericalSection (w : MonoidHom B Complex) (g : G) : Complex :=
  w (Classical.choose (valuationIwasawaSubgroupFactorization v n g))

/-- The spherical section evaluates to the inducing character on any
triangular component of an Iwasawa factorization. -/
theorem valuationSphericalSection_eq
    (w : MonoidHom B Complex)
    (hw : forall b : B, Membership.mem K b.val -> w b = 1)
    {g : G} {b : B} (hb : Membership.mem K (Inv.inv b.val * g)) :
    valuationSphericalSection v n w g = w b := by
  let c : B := Classical.choose (valuationIwasawaSubgroupFactorization v n g)
  have hc : Membership.mem K (Inv.inv c.val * g) :=
    Classical.choose_spec (valuationIwasawaSubgroupFactorization v n g)
  have hRel : (Inv.inv c * b).val = (Inv.inv c.val * g) * Inv.inv (Inv.inv b.val * g) := by
    change Inv.inv c.val * b.val = _
    rw [mul_inv_rev, inv_inv, mul_assoc, <- mul_assoc g (Inv.inv g) b.val,
      mul_inv_cancel, one_mul]
  have hCB : Membership.mem K (Inv.inv c * b).val := by
    rw [hRel]
    exact (valuationIntegralMatrixSubgroup v n).mul_mem hc
      ((valuationIntegralMatrixSubgroup v n).inv_mem hb)
  change w c = w b
  calc
    w c = w c * w (Inv.inv c * b) := by rw [hw _ hCB, mul_one]
    _ = w b := by rw [<- map_mul, mul_inv_cancel_left]

/-- The spherical section is invariant on the right by integral units. -/
theorem valuationSphericalSection_mul_integral
    (w : MonoidHom B Complex)
    (hw : forall b : B, Membership.mem K b.val -> w b = 1)
    (g k : G) (hk : Membership.mem K k) :
    valuationSphericalSection v n w (g * k) = valuationSphericalSection v n w g := by
  let b : B := Classical.choose (valuationIwasawaSubgroupFactorization v n g)
  have hb : Membership.mem K (Inv.inv b.val * g) :=
    Classical.choose_spec (valuationIwasawaSubgroupFactorization v n g)
  have hBK : Membership.mem K (Inv.inv b.val * (g * k)) := by
    rw [<- mul_assoc]
    exact (valuationIntegralMatrixSubgroup v n).mul_mem hb hk
  exact valuationSphericalSection_eq v n w hw hBK

/-- Left multiplication by a triangular element acts by the inducing
character. -/
theorem valuationSphericalSection_mul_triangular
    (w : MonoidHom B Complex)
    (hw : forall b : B, Membership.mem K b.val -> w b = 1)
    (b : B) (g : G) :
    valuationSphericalSection v n w (b.val * g) =
      w b * valuationSphericalSection v n w g := by
  let c : B := Classical.choose (valuationIwasawaSubgroupFactorization v n g)
  have hc : Membership.mem K (Inv.inv c.val * g) :=
    Classical.choose_spec (valuationIwasawaSubgroupFactorization v n g)
  have hBC : Membership.mem K (Inv.inv (b * c).val * (b.val * g)) := by
    change Membership.mem K (Inv.inv (b.val * c.val) * (b.val * g))
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact hc
  rw [valuationSphericalSection_eq v n w hw hBC, map_mul]
  rfl

/-- The section is locally constant because the integral subgroup is open. -/
theorem continuous_valuationSphericalSection
    [TopologicalSpace F] [IsTopologicalRing F]
    (hOpen : IsOpen (v.integer : Set F))
    (w : MonoidHom B Complex)
    (hw : forall b : B, Membership.mem K b.val -> w b = 1) :
    Continuous (valuationSphericalSection v n w) := by
  rw [continuous_iff_continuousAt]
  intro g
  let S : Set G := Set.preimage (fun x : G => Inv.inv g * x) (K : Set G)
  have hS : IsOpen S := (isOpen_valuationIntegralMatrixSubgroup v n hOpen).preimage
    (continuous_const.mul continuous_id)
  have hg : Membership.mem S g := by
    change Membership.mem K (Inv.inv g * g)
    rw [inv_mul_cancel]
    exact (valuationIntegralMatrixSubgroup v n).one_mem
  have hNear : Filter.EventuallyEq (nhds g) (fun _ : G => valuationSphericalSection v n w g)
      (valuationSphericalSection v n w) := by
    filter_upwards [hS.mem_nhds hg] with y hy
    have hY : g * (Inv.inv g * y) = y := mul_inv_cancel_left g y
    rw [<- hY]
    exact (valuationSphericalSection_mul_integral v n w hw g _ hy).symm
  exact continuousAt_const.congr hNear

/-- Right multiplication of a diagonal matrix by a unitriangular matrix
scales its \(i\)-th row by the \(i\)-th diagonal coordinate. -/
theorem valuationDiagonal_mul_unitriangular_apply
    (a : Units (Fin n -> F)) (u : valuationUpperUnitriangularSubgroup F n)
    (i j : Fin n) :
    ((valuationDiagonalSection F n a * u.val).val.val) i j =
      a.val i * u.val.val.val i j := by
  change (Matrix.diagonal a.val * u.val.val.val) i j = _
  simp only [Matrix.diagonal_mul]

private theorem valuationDiagonal_mul_unitriangular_diag
    (a : Units (Fin n -> F)) (u : valuationUpperUnitriangularSubgroup F n) (i : Fin n) :
    ((valuationDiagonalSection F n a * u.val).val.val) i i = a.val i := by
  have hu : valuationTriangularDiagonalHom F n u.val = 1 := u.property
  have hd : valuationTriangularDiagonalHom F n (valuationDiagonalSection F n a * u.val) = a := by
    rw [map_mul, valuationTriangularDiagonalHom_section, hu, mul_one]
  exact congrArg (fun b : Units (Fin n -> F) => b.val i) hd

/-- In triangular coordinates, the matrix test is the diagonal ball
times the scaled boxes in the upper entries. -/
theorem valuationDiagonal_mul_unitriangular_integral_iff
    (a : Units (Fin n -> F)) (u : valuationUpperUnitriangularSubgroup F n) :
    (forall i j : Fin n,
      Membership.mem v.integer (((valuationDiagonalSection F n a * u.val).val.val) i j)) <->
      And (forall i : Fin n, Membership.mem v.integer (a.val i))
        (forall i j : Fin n, i < j -> Membership.mem v.integer (a.val i * u.val.val.val i j)) := by
  let b := valuationDiagonalSection F n a * u.val
  constructor
  case mp =>
    intro h
    refine And.intro ?_ ?_
    next =>
      intro i
      simpa only [valuationDiagonal_mul_unitriangular_diag n a u i] using h i i
    next =>
      intro i j _
      simpa only [valuationDiagonal_mul_unitriangular_apply n a u i j] using h i j
  case mpr =>
    intro h i j
    rcases lt_trichotomy i j with hij | heq | hji
    case inl =>
      change Membership.mem v.integer (b.val.val i j)
      rw [valuationDiagonal_mul_unitriangular_apply n a u i j]
      exact h.2 i j hij
    case inr.inl =>
      subst j
      rw [valuationDiagonal_mul_unitriangular_diag n a u i]
      exact h.1 i
    case inr.inr =>
      change Membership.mem v.integer (b.val.val i j)
      rw [b.property hji]
      exact v.integer.zero_mem

/-- The determinant in the diagonal and unitriangular coordinates is
the product of the diagonal coordinates. -/
theorem det_valuationDiagonal_mul_unitriangular
    (a : Units (Fin n -> F)) (u : valuationUpperUnitriangularSubgroup F n) :
    ((valuationDiagonalSection F n a * u.val).val.val).det =
      Finset.univ.prod (fun i : Fin n => a.val i) := by
  let b := valuationDiagonalSection F n a * u.val
  rw [Matrix.det_of_isUpperTriangular b.property]
  exact Finset.prod_congr rfl (fun i _ => valuationDiagonal_mul_unitriangular_diag n a u i)

section

variable (L : Type*) [NormedField L]

/-- The square root of the upper-triangular modulus on a diagonal unit. -/
def valuationDiagonalHalfModulus (m : Nat) : MonoidHom (Units (Fin m -> L)) Complex where
  toFun a := (Finset.univ.prod (fun i : Fin m =>
    (norm (a.val i)) ^ (((m : Real) - 1) / 2 - (i.val : Real))) : Real)
  map_one' := by
    simp
  map_mul' a b := by
    change ((Finset.univ.prod (fun i : Fin m =>
      norm (a.val i * b.val i) ^ (((m : Real) - 1) / 2 - (i.val : Real))) : Real) : Complex) = _
    simp_rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    rw [Finset.prod_mul_distrib, Complex.ofReal_mul]

/-- The inducing character is the diagonal character times the square
root of the triangular modulus. -/
def valuationNormalizedInducingCharacter (m : Nat)
    (chi : MonoidHom (Units (Fin m -> L)) Complex) :
    MonoidHom (valuationUpperTriangularSubgroup L m) Complex :=
  (valuationDiagonalHalfModulus L m * chi).comp (valuationTriangularDiagonalHom L m)

/-- The normalized inducing character is trivial on integral triangular
units when the original diagonal character is unramified. -/
theorem valuationNormalizedInducingCharacter_eq_one
    {W : Type*} [LinearOrderedCommGroupWithZero W] (val : Valuation L W)
    (hNorm : forall x : L, Membership.mem val.integer x <-> norm x <= 1)
    (m : Nat) (chi : MonoidHom (Units (Fin m -> L)) Complex)
    (hChi : forall a, Membership.mem (valuationDiagonalIntegralSubgroup L m val) a -> chi a = 1)
    (b : valuationUpperTriangularSubgroup L m)
    (hb : Membership.mem (valuationIntegralMatrixSubgroup val m) b.val) :
    valuationNormalizedInducingCharacter L m chi b = 1 := by
  let E := valuationTriangularHomeomorph L m
  let a := valuationTriangularDiagonalHom L m b
  have hPre : Membership.mem
      (Set.preimage E.symm
        ((valuationIntegralMatrixSubgroup val m).comap (valuationUpperTriangularSubgroup L m).subtype :
          Set (valuationUpperTriangularSubgroup L m))) (E b) := by
    change Membership.mem (valuationIntegralMatrixSubgroup val m) (E.symm (E b)).val
    rwa [E.symm_apply_apply]
  have hProd := preimage_valuationTriangularHomeomorph_integral L m val
  rw [hProd] at hPre
  have ha : Membership.mem (valuationDiagonalIntegralSubgroup L m val) a := hPre.1
  have hEntry := (mem_valuationIntegralMatrixSubgroup_iff val m
    (valuationDiagonalSection L m a).val).mp ha
  have hn (i : Fin m) : norm (a.val i) = 1 := by
    have hx := hEntry.1 i i
    have hy := hEntry.2 i i
    change Membership.mem val.integer (Matrix.diagonal a.val i i) at hx
    change Membership.mem val.integer (Matrix.diagonal a.inv i i) at hy
    rw [Matrix.diagonal_apply_eq] at hx hy
    have hLeft := (hNorm (a.val i)).mp hx
    have hRight := (hNorm (a.inv i)).mp hy
    have hUnit : norm (a.val i) * norm (a.inv i) = 1 := by
      rw [<- norm_mul]
      change norm ((a.val * a.inv) i) = 1
      rw [a.val_inv]
      exact norm_one
    have hGe := hUnit.symm.le.trans (mul_le_of_le_one_right (norm_nonneg _) hRight)
    exact le_antisymm hLeft hGe
  change ((Finset.univ.prod (fun i : Fin m =>
    norm (a.val i) ^ (((m : Real) - 1) / 2 - (i.val : Real))) : Real) : Complex) * chi a = 1
  simp only [hn, Real.one_rpow, Finset.prod_const_one, Complex.ofReal_one, hChi a ha, mul_one]

/-- After integrating the upper entries, the triangular modulus and the
local determinant shift leave exactly the power \(s\) in each coordinate. -/
theorem valuationSphericalDiagonalWeight
    (m : Nat) (a : Units (Fin m -> L)) (s : Complex) :
    ((Finset.univ.prod (fun i : Fin m => norm (a.val i)) : Real) : Complex) ^
        (s + (((m : Real) - 1) / 2 : Real)) *
      valuationDiagonalHalfModulus L m a *
      ((Finset.univ.prod (fun i : Fin m =>
        (ENNReal.ofReal (Inv.inv (norm (a.val i)))) ^ (m - (i.val + 1)))).toReal : Complex) =
      Finset.univ.prod (fun i : Fin m => (norm (a.val i) : Complex) ^ s) := by
  let r (i : Fin m) := norm (a.val i)
  let alpha : Real := ((m : Real) - 1) / 2
  let q := s + (alpha : Complex)
  let e (i : Fin m) := alpha - (i.val : Real)
  let k (i : Fin m) := m - (i.val + 1)
  have hPos (i : Fin m) : 0 < r i := by
    apply norm_pos_iff.mpr
    intro hi
    have hUnit := congrArg (fun f : Fin m -> L => f i) a.val_inv
    change a.val i * a.inv i = 1 at hUnit
    rw [hi, zero_mul] at hUnit
    exact zero_ne_one hUnit
  have hPower (S : Finset (Fin m)) :
      ((S.prod r : Real) : Complex) ^ q = S.prod (fun i => (r i : Complex) ^ q) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (hPos i).le (Finset.prod_nonneg (fun j _ => (hPos j).le)), ih]
  have hModulus : valuationDiagonalHalfModulus L m a =
      Finset.univ.prod (fun i : Fin m => ((r i ^ e i : Real) : Complex)) := by
    change ((Finset.univ.prod (fun i : Fin m => r i ^ e i) : Real) : Complex) = _
    exact map_prod Complex.ofRealHom _ _
  have hVolume : ((Finset.univ.prod (fun i : Fin m =>
        (ENNReal.ofReal (Inv.inv (r i))) ^ k i)).toReal : Complex) =
      Finset.univ.prod (fun i : Fin m => (((Inv.inv (r i)) ^ k i : Real) : Complex)) := by
    rw [ENNReal.toReal_prod]
    simp_rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_nonneg.mpr (hPos _).le)]
    exact map_prod Complex.ofRealHom _ _
  change ((Finset.univ.prod r : Real) : Complex) ^ q * valuationDiagonalHalfModulus L m a *
    ((Finset.univ.prod (fun i : Fin m => (ENNReal.ofReal (Inv.inv (r i))) ^ k i)).toReal : Complex) =
      Finset.univ.prod (fun i : Fin m => (r i : Complex) ^ s)
  rw [hPower, hModulus, hVolume, <- Finset.prod_mul_distrib, <- Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i _
  have hNonzero : Not ((r i : Complex) = 0) := Complex.ofReal_ne_zero.mpr (hPos i).ne'
  have hInv : (((Inv.inv (r i)) ^ k i : Real) : Complex) = (r i : Complex) ^ (-(k i : Complex)) := by
    rw [Complex.ofReal_pow, Complex.ofReal_inv, inv_pow, Complex.cpow_neg, Complex.cpow_natCast]
  rw [Complex.ofReal_cpow (hPos i).le, hInv, <- Complex.cpow_add _ _ hNonzero,
    <- Complex.cpow_add _ _ hNonzero]
  congr 1
  have hk : (k i : Complex) = (m : Complex) - ((i.val : Complex) + 1) := by
    dsimp [k]
    rw [Nat.cast_sub (Nat.succ_le_of_lt i.isLt), Nat.cast_succ]
  rw [hk]
  simp only [q, e, alpha, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  ring
end

open MeasureTheory

section FiberIntegral

variable (L : Type*) [NormedField L]
variable {W : Type*} [LinearOrderedCommGroupWithZero W]
variable (val : Valuation L W) (m : Nat)

local notation "U" => valuationUpperUnitriangularSubgroup L m
local notation "TT" => valuationUpperTriangularSubgroup L m
local notation "GG" => Units (Matrix (Fin m) (Fin m) L)

/-- The matrix-integrality test times the shifted determinant and spherical section. -/
def valuationUnramifiedSphericalIntegrand
    (chi : MonoidHom (Units (Fin m -> L)) Complex) (s : Complex) : GG -> Complex :=
  Set.indicator
    {g : GG | forall i j : Fin m, Membership.mem val.integer (g.val i j)}
    (fun g : GG =>
      (norm g.val.det : Complex) ^ (s + (((m : Real) - 1) / 2 : Real)) *
        valuationSphericalSection val m (valuationNormalizedInducingCharacter L m chi) g)

/-- The scaled unipotent box is open, since each upper entry is a
continuous function and the local valuation ring is open. -/
private theorem isOpen_valuationScaledUpperBox
    (hOpen : IsOpen (val.integer : Set L)) (a : Units (Fin m -> L)) :
    IsOpen {u : U | forall i j : Fin m, i < j ->
      Membership.mem val.integer (a.val i * u.val.val.val i j)} := by
  classical
  let A (i j : Fin m) : Set U := if i < j then
    Set.preimage (fun u : U => a.val i * u.val.val.val i j) (val.integer : Set L)
    else Set.univ
  have hRep : {u : U | forall i j : Fin m, i < j ->
      Membership.mem val.integer (a.val i * u.val.val.val i j)} =
      Set.iInter (fun i : Fin m => Set.iInter (A i)) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    next =>
      intro h i j
      by_cases hij : i < j
      next =>
        rw [show A i j = _ from if_pos hij]
        exact h i j hij
      next =>
        rw [show A i j = _ from if_neg hij]
        exact Set.mem_univ u
    next =>
      intro h i j hij
      have hh := h i j
      rw [show A i j = _ from if_pos hij] at hh
      exact hh
  have hMatrix : Continuous (fun u : U => u.val.val.val) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  rw [hRep]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  change IsOpen (A i j)
  by_cases hij : i < j
  next =>
    rw [show A i j = _ from if_pos hij]
    apply hOpen.preimage
    have hEntry : Continuous (fun u : U => u.val.val.val i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hMatrix)
    exact continuous_const.mul hEntry
  next =>
    rw [show A i j = _ from if_neg hij]
    exact isOpen_univ

/-- Integral over the unipotent fibre of the unramified spherical kernel.
The volume of the scaled box cancels the triangular modulus and the
determinant shift. -/
theorem integral_valuationUnramifiedSpherical_fibre
    [MeasurableSpace U] [BorelSpace U]
    (hOpen : IsOpen (val.integer : Set L))
    (mu : Measure U) (a : Units (Fin m -> L))
    (hDiag : forall i : Fin m, Membership.mem val.integer (a.val i))
    (chi : MonoidHom (Units (Fin m -> L)) Complex)
    (hChi : forall b : TT, Membership.mem (valuationIntegralMatrixSubgroup val m) b.val ->
      valuationNormalizedInducingCharacter L m chi b = 1)
    (s : Complex)
    (hVolume : mu {u : U | forall i j : Fin m, i < j ->
        Membership.mem val.integer (a.val i * u.val.val.val i j)} =
      Finset.univ.prod (fun i : Fin m =>
        (ENNReal.ofReal (Inv.inv (norm (a.val i)))) ^ (m - (i.val + 1)))) :
    integral mu (fun u : U =>
      valuationUnramifiedSphericalIntegrand L val m chi s
        (valuationDiagonalSection L m a * u.val).val) =
      (Finset.univ.prod (fun i : Fin m => (norm (a.val i) : Complex) ^ s)) * chi a := by
  classical
  let S : Set U := {u : U | forall i j : Fin m, i < j ->
    Membership.mem val.integer (a.val i * u.val.val.val i j)}
  let G0 : Set GG := {g : GG | forall i j : Fin m,
    Membership.mem val.integer (g.val i j)}
  let w := valuationNormalizedInducingCharacter L m chi
  let A0 : Complex :=
    ((Finset.univ.prod (fun i : Fin m => norm (a.val i)) : Real) : Complex) ^
      (s + (((m : Real) - 1) / 2 : Real))
  let C := A0 * (valuationDiagonalHalfModulus L m a * chi a)
  have hS : MeasurableSet S := (isOpen_valuationScaledUpperBox L val m hOpen a).measurableSet
  have hPoint : (fun u : U => valuationUnramifiedSphericalIntegrand L val m chi s
      (valuationDiagonalSection L m a * u.val).val) =
      S.indicator (fun _ : U => C) := by
    funext u
    let b : TT := valuationDiagonalSection L m a * u.val
    have hb : Membership.mem G0 b.val <-> Membership.mem S u := by
      change (forall i j : Fin m, Membership.mem val.integer (b.val.val i j)) <-> _
      rw [valuationDiagonal_mul_unitriangular_integral_iff val m a u]
      exact and_iff_right hDiag
    by_cases hU : Membership.mem S u
    next =>
      have hG : Membership.mem G0 b.val := hb.mpr hU
      change G0.indicator (fun g : GG =>
        (norm g.val.det : Complex) ^ (s + (((m : Real) - 1) / 2 : Real)) *
          valuationSphericalSection val m w g) b.val = _
      rw [Set.indicator_of_mem hG, Set.indicator_of_mem hU]
      have hbK : Membership.mem (valuationIntegralMatrixSubgroup val m)
          (Inv.inv b.val * b.val) := by
        rw [inv_mul_cancel]
        exact (valuationIntegralMatrixSubgroup val m).one_mem
      have hD : valuationTriangularDiagonalHom L m b = a := by
        change valuationTriangularDiagonalHom L m (valuationDiagonalSection L m a * u.val) = a
        have hu : valuationTriangularDiagonalHom L m u.val = 1 := u.property
        rw [map_mul, valuationTriangularDiagonalHom_section, hu, mul_one]
      have hw : w b = valuationDiagonalHalfModulus L m a * chi a := by
        change (valuationDiagonalHalfModulus L m * chi)
          (valuationTriangularDiagonalHom L m b) = _
        rw [hD]
        rfl
      rw [valuationSphericalSection_eq val m w hChi hbK, hw]
      change (norm ((valuationDiagonalSection L m a * u.val).val.val).det : Complex) ^
        (s + (((m : Real) - 1) / 2 : Real)) * _ = C
      rw [det_valuationDiagonal_mul_unitriangular, norm_prod]
    next =>
      have hG : Not (Membership.mem G0 b.val) := fun hh => hU (hb.mp hh)
      change G0.indicator (fun g : GG =>
        (norm g.val.det : Complex) ^ (s + (((m : Real) - 1) / 2 : Real)) *
          valuationSphericalSection val m w g) b.val = _
      rw [Set.indicator_of_notMem hG, Set.indicator_of_notMem hU]
  rw [hPoint, integral_indicator_const C hS]
  change ((mu S).toReal : Complex) * C = _
  change mu S = _ at hVolume
  rw [hVolume]
  dsimp [C]
  calc
    _ = (A0 * valuationDiagonalHalfModulus L m a *
          ((Finset.univ.prod (fun i : Fin m =>
            (ENNReal.ofReal (Inv.inv (norm (a.val i)))) ^ (m - (i.val + 1)))).toReal : Complex)) *
              chi a := by ring
    _ = _ := by rw [show A0 * valuationDiagonalHalfModulus L m a *
          ((Finset.univ.prod (fun i : Fin m =>
            (ENNReal.ofReal (Inv.inv (norm (a.val i)))) ^ (m - (i.val + 1)))).toReal : Complex) =
        _ from valuationSphericalDiagonalWeight L m a s]

/-- Outside the integral diagonal cone, the matrix test vanishes
identically along the associated unipotent fibre. -/
theorem valuationUnramifiedSphericalIntegrand_of_nonintegral
    (a : Units (Fin m -> L)) (u : U)
    (hDiag : Not (forall i : Fin m, Membership.mem val.integer (a.val i)))
    (chi : MonoidHom (Units (Fin m -> L)) Complex) (s : Complex) :
    valuationUnramifiedSphericalIntegrand L val m chi s
      (valuationDiagonalSection L m a * u.val).val = 0 := by
  have hNot : Not (forall i j : Fin m, Membership.mem val.integer
      (((valuationDiagonalSection L m a * u.val).val.val) i j)) := by
    intro hMem
    exact hDiag ((valuationDiagonal_mul_unitriangular_integral_iff val m a u).mp hMem).1
  let S : Set GG := {g : GG | forall i j : Fin m, Membership.mem val.integer (g.val i j)}
  have hNotMem : Not (Membership.mem S (valuationDiagonalSection L m a * u.val).val) := hNot
  exact Set.indicator_of_notMem hNotMem _

end FiberIntegral

open IsDedekindDomain NumberField

section ActualFinitePlace

variable {K0 : Type*} [Field K0] [NumberField K0]
variable [MeasurableSpace (FiniteAdeleRing (RingOfIntegers K0) K0)]
variable [BorelSpace (FiniteAdeleRing (RingOfIntegers K0) K0)]

private abbrev normalizedAdicValuation
    (p : HeightOneSpectrum (RingOfIntegers K0)) :
    Valuation (p.adicCompletion K0) (WithZero (Multiplicative Int)) :=
  Valued.v

/-- The actual finite-place unipotent integral with the normalized local Haar
measure and the unramified spherical section. -/
theorem integral_heckeUnramifiedSpherical_fibre
    (p : HeightOneSpectrum (RingOfIntegers K0))
    [MeasurableSpace (p.adicCompletion K0)] [BorelSpace (p.adicCompletion K0)]
    (n : Nat) (a : Units (Fin n -> p.adicCompletion K0))
    (hDiag : forall i : Fin n, Membership.mem (p.adicCompletionIntegers K0) (a.val i))
    (chi : MonoidHom (Units (Fin n -> p.adicCompletion K0)) Complex)
    (hChi : forall b : valuationUpperTriangularSubgroup (p.adicCompletion K0) n,
      Membership.mem (valuationIntegralMatrixSubgroup (normalizedAdicValuation p) n) b.val ->
      valuationNormalizedInducingCharacter (p.adicCompletion K0) n chi b = 1)
    (s : Complex) :
    integral
      (valuationUnitriangularProductMeasure (p.adicCompletion K0) (heckeLocalAdditiveMeasure p) n)
      (fun u : valuationUpperUnitriangularSubgroup (p.adicCompletion K0) n =>
        valuationUnramifiedSphericalIntegrand (p.adicCompletion K0) (normalizedAdicValuation p)
          n chi s (valuationDiagonalSection (p.adicCompletion K0) n a * u.val).val) =
      (Finset.univ.prod (fun i : Fin n => (norm (a.val i) : Complex) ^ s)) * chi a := by
  let L := p.adicCompletion K0
  let _ : MeasurableSpace (valuationUpperUnitriangularSubgroup L n) :=
    borel (valuationUpperUnitriangularSubgroup L n)
  let _ : BorelSpace (valuationUpperUnitriangularSubgroup L n) := BorelSpace.mk rfl
  exact integral_valuationUnramifiedSpherical_fibre L (normalizedAdicValuation p) n
    (Valued.isOpen_valuationSubring L) _ a hDiag chi hChi s
    (measure_heckeLocalUnitriangular_scaledIntegral p n a)

end ActualFinitePlace

end Robin1984.GRH
