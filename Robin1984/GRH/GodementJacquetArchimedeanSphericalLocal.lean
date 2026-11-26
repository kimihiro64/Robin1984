import DedekindZeta.Statements
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring
import Robin1984.GRH.GodementJacquetArchimedeanExponentialHaar
import Robin1984.GRH.GodementJacquetArchimedeanSphericalGaussian

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The spherical archimedean case of the Godement-Jacquet local zeta integral.
- Formalization note: Evaluates the normalized Gaussian integral for a spherical inducing section and its compact-group average.
- PROVENANCE-END
-/

/-!
# The spherical archimedean Gaussian zeta integral

For a section with normalized spherical Iwasawa values, the determinant
weight produces the shifted row powers of the Gaussian integral. The
Iwasawa Haar formula and the Gaussian calculation give the Gamma product
with a single positive normalization constant. A left unitary average
preserves the integral and absolute convergence.
-/

set_option autoImplicit false

open scoped Real

namespace Robin1984.GRH

private theorem archSphericalRowExponent
    (n d : Nat) (i : Fin n) (s z : Complex) :
    (d : Complex) * (s + ((n : Complex) - 1) / 2) +
      ((d : Complex) * z +
        (d : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2) =
      (d : Complex) * (s + z) + ((d * (n - (i.val + 1)) : Nat) : Complex) := by
  have hNat : n - (i.val + 1) + (i.val + 1) = n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt i.isLt)
  have hCast : ((n - (i.val + 1) : Nat) : Complex) + ((i.val : Nat) : Complex) + 1 = (n : Complex) := by
    exact_mod_cast (Nat.add_assoc (n - (i.val + 1)) i.val 1).trans hNat
  have hDiff : (n : Complex) - 1 - (i.val : Complex) = ((n - (i.val + 1) : Nat) : Complex) := by
    rw [<- hCast]
    ring
  calc
    _ = (d : Complex) * (s + z) + (d : Complex) * ((n : Complex) - 1 - (i.val : Complex)) := by ring
    _ = _ := by rw [hDiff, Nat.cast_mul]

private theorem archProductDeterminantCpow
    (n d : Nat) (a : Fin n -> Real) (ha : forall i, 0 < a i) (s : Complex) :
    (((Finset.univ.prod a) ^ d : Real) : Complex) ^ s =
      Finset.univ.prod (fun i : Fin n => (a i : Complex) ^ ((d : Complex) * s)) := by
  let z := (d : Complex) * s
  have hA : 0 <= Finset.univ.prod a := Finset.prod_nonneg (fun i _ => (ha i).le)
  have hPow : (((Finset.univ.prod a) ^ d : Real) : Complex) ^ s =
      ((Finset.univ.prod a : Real) : Complex) ^ z := by
    rw [<- Real.rpow_natCast (Finset.univ.prod a) d,
      <- Complex.cpow_mul_ofReal_nonneg hA, Complex.ofReal_natCast]
  rw [hPow]
  have hProduct (t : Finset (Fin n)) :
      ((t.prod a : Real) : Complex) ^ z = t.prod (fun i => (a i : Complex) ^ z) := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hit ih =>
      rw [Finset.prod_insert hit, Finset.prod_insert hit, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (ha i).le (Finset.prod_nonneg (fun j _ => (ha j).le)), ih]
  exact hProduct Finset.univ

section MatrixKernel

variable {F : Type*} [RCLike F] {n : Nat}

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "N" => valuationUpperUnitriangularSubgroup F n

/-- The Gaussian test with the normalized determinant power and a matrix coefficient. -/
noncomputable def archMatrixGaussianZetaDensity
    (d : Nat) (b : Real) (s : Complex) (R : M) (coefficient : Complex) : Complex :=
  (Real.exp (-b * archFrobeniusSq R) : Complex) *
    ((norm R.det ^ d : Real) : Complex) ^ (s + ((n : Complex) - 1) / 2) * coefficient

private theorem archMatrixGaussianZetaDensity_chart
    (d : Nat) (b : Real) (s : Complex) (z : Fin n -> Complex)
    (a : Fin n -> Real) (ha : forall i, 0 < a i) (u : N) (Q : Matrix.unitaryGroup (Fin n) F) :
    let coeff := Finset.univ.prod (fun i : Fin n =>
      (a i : Complex) ^ ((d : Complex) * z i +
        (d : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2))
    archMatrixGaussianZetaDensity d b s
        ((Matrix.diagonal (fun i => (a i : F)) * u.val.val.val) * Q.val) coeff =
      Finset.univ.prod (fun i : Fin n =>
        (a i : Complex) ^ ((d : Complex) * (s + z i) + ((d * (n - (i.val + 1)) : Nat) : Complex)) *
          (Real.exp (-b * a i ^ (2 : Nat)) : Complex)) *
        (archUnipotentScaledKernel F (fun x => Real.exp (-b * norm x ^ (2 : Nat))) n a u : Complex) := by
  let shift := s + ((n : Complex) - 1) / 2
  let v (i : Fin n) := (d : Complex) * z i +
    (d : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2
  let D (i : Fin n) : Complex := (a i : Complex) ^ ((d : Complex) * shift)
  let V (i : Fin n) : Complex := (a i : Complex) ^ (v i)
  let B (i : Fin n) : Complex := (Real.exp (-b * a i ^ (2 : Nat)) : Complex)
  let A (i : Fin n) : Complex :=
    (a i : Complex) ^ ((d : Complex) * (s + z i) + ((d * (n - (i.val + 1)) : Nat) : Complex)) * B i
  let U : Complex :=
    (archUnipotentScaledKernel F (fun x => Real.exp (-b * norm x ^ (2 : Nat))) n a u : Complex)
  unfold archMatrixGaussianZetaDensity
  rw [norm_det_diagonal_unitriangular_unitary a ha u Q,
    archProductDeterminantCpow n d a ha,
    archMatrixGaussian_diagonal_unitriangular_unitary b a u Q,
    Complex.ofReal_mul, Complex.ofReal_prod]
  change ((Finset.univ.prod B * U) * Finset.univ.prod D) * Finset.univ.prod V =
    Finset.univ.prod A * U
  have hRad : Finset.univ.prod B * (Finset.univ.prod D * Finset.univ.prod V) = Finset.univ.prod A := by
    rw [<- Finset.prod_mul_distrib, <- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    change B i * ((a i : Complex) ^ ((d : Complex) * shift) * (a i : Complex) ^ (v i)) = _
    have hNonzero : Not ((a i : Complex) = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt (ha i))
    rw [<- Complex.cpow_add _ _ hNonzero]
    have hZ := archSphericalRowExponent n d i s (z i)
    change (d : Complex) * shift + v i = _ at hZ
    rw [hZ]
    exact mul_comm _ _
  calc
    _ = (Finset.univ.prod B * (Finset.univ.prod D * Finset.univ.prod V)) * U := by ac_rfl
    _ = _ := by rw [hRad]

end MatrixKernel

open MeasureTheory

section LocalSphericalIntegral

variable (F : Type*) [RCLike F] [ProperSpace F] [SecondCountableTopology F]
  [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
  [SigmaFinite (volume : Measure F)] (n : Nat)

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "G" => Units M
local notation "P" => positiveDiagonalSubgroup F n
local notation "N" => valuationUpperUnitriangularSubgroup F n
local notation "T" => positiveUpperTriangularMatrixSubgroup F n
local notation "K" => Matrix.unitaryGroup (Fin n) F
local notation "Y" => (Fin n -> Real)

local instance sphericalLocalUnipotentMS : MeasurableSpace N := borel N
local instance sphericalLocalUnipotentBorel : BorelSpace N := BorelSpace.mk rfl

/-- The normalized spherical section has a convergent Gaussian zeta integral.
Its value is a positive constant independent of the Mellin variable times the Gamma product. -/
theorem exists_pos_archSphericalLocalIntegral
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace T] [BorelSpace T]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace K] [BorelSpace K]
    (mu : Measure G) [mu.IsHaarMeasure] [mu.InnerRegular]
    (muK : Measure K) [muK.IsHaarMeasure] [IsProbabilityMeasure muK]
    (b : Real) (hb : 0 < b) (z : Fin n -> Complex) (v : G -> Complex)
    (hv : forall (r : Y) (_ : forall i, 0 < r i) (u : N) (q : K) (g : G),
      g.val = ((Matrix.diagonal (fun i => (r i : F)) * u.val.val.val) * q.val) ->
      v g = Finset.univ.prod (fun i : Fin n =>
        (r i : Complex) ^ ((Module.finrank Real F : Complex) * z i +
          (Module.finrank Real F : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2))) :
    exists C : Real, And (0 < C)
      (forall (s : Complex) (_ : forall i, 0 < (s + z i).re),
        let d := Module.finrank Real F
        let f (g : G) := archMatrixGaussianZetaDensity d b s g.val (v g)
        And (Integrable f mu)
          (integral mu f = (C : Complex) *
            Finset.univ.prod (fun i : Fin n => HSMul.hSMul (Inv.inv (2 : Real))
              ((1 / (b : Complex)) ^ ((d : Complex) * (s + z i) / 2) *
                Complex.Gamma ((d : Complex) * (s + z i) / 2))))) := by
  let d := Module.finrank Real F
  let m (i : Fin n) := n - (i.val + 1)
  let cBase := Real.rpow (Real.pi / b) ((d : Real) / 2)
  let C := Finset.univ.prod (fun i : Fin n => cBase ^ (m i))
  let muN := valuationUnitriangularProductMeasure F volume n
  let _ : SecondCountableTopology N := archUnipotent_secondCountable F n
  let _ : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> F))
  have hK : Topology.IsEmbedding (fun k : K => k.val) := Topology.IsEmbedding.subtypeVal
  let _ : SecondCountableTopology K := hK.secondCountableTopology
  let _ : SigmaFinite muN := sigmaFinite_valuationUnitriangularProductMeasure F volume n
  let _ : muN.IsHaarMeasure := isHaarMeasure_archUnipotentProduct F volume n
  choose E hE hScale using exists_pos_smul_map_exponentialIwasawaHaar F n mu muN muK
  choose c hc using hScale
  have hcR : 0 < (c : Real) := by exact_mod_cast hc.1
  have hBase : 0 < cBase := Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _
  have hC : 0 < C := Finset.prod_pos (fun i _ => pow_pos hBase (m i))
  refine Exists.intro ((c : Real) * C) (And.intro (mul_pos hcR hC) ?_)
  intro s hs
  let w (i : Fin n) : Complex := (d : Complex) * (s + z i)
  have hd : 0 < (d : Real) := by
    have hdNat : 0 < Module.finrank Real F := Module.finrank_pos
    exact_mod_cast hdNat
  have hw (i : Fin n) : 0 < (w i).re := by
    change 0 < ((d : Complex) * (s + z i)).re
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      using mul_pos hd (hs i)
  let a (x : Y) (i : Fin n) := Real.exp (x i)
  let D (p : Prod Y N) : Complex :=
    Finset.univ.prod (fun i : Fin n => (a p.1 i : Complex) ^ (w i + ((d * m i : Nat) : Complex)) *
      (Real.exp (-b * (a p.1 i) ^ (2 : Nat)) : Complex)) *
      (archUnipotentScaledKernel F (fun x => Real.exp (-b * norm x ^ (2 : Nat))) n (a p.1) p.2 : Complex)
  let f (g : G) := archMatrixGaussianZetaDensity d b s g.val (v g)
  let nu := (volume : Measure Y).prod muN
  let base := nu.prod muK
  have hD := integrable_integral_archSphericalGaussian F b hb n w hw
  have hInt : Integrable D nu := hD.1
  have hF (p : Prod (Prod Y N) K) : f (E p) = D p.1 := by
    have ha (i : Fin n) : 0 < a p.1.1 i := Real.exp_pos _
    have hvp := hv (a p.1.1) ha p.1.2 (Inv.inv p.2) (E p) (hE p)
    unfold f
    rw [hvp, hE]
    exact archMatrixGaussianZetaDensity_chart d b s z (a p.1.1) ha p.1.2 (Inv.inv p.2)
  have hProd : Integrable (fun p : Prod (Prod Y N) K => D p.1) base :=
    hInt.comp_fst muK
  have hPull : Integrable (fun p : Prod (Prod Y N) K => f (E p)) base := by
    simp_rw [hF]
    exact hProd
  have hPush : MeasurePreserving E base (Measure.map E base) :=
    { measurable := E.continuous.measurable, map_eq := rfl }
  have hMapped : Integrable f (Measure.map E base) :=
    (hPush.integrable_comp_emb E.measurableEmbedding).mp hPull
  have hIntMu : Integrable f mu := by
    rw [hc.2]
    exact hMapped.smul_measure_nnreal
  change And (Integrable f mu) _
  refine And.intro hIntMu ?_
  have hProb : integral base (fun p : Prod (Prod Y N) K => D p.1) = integral nu D := by
    rw [integral_prod _ hProd]
    simp [integral_const, measureReal_def]
  have hDiag : integral nu D =
      (C : Complex) * Finset.univ.prod (fun i : Fin n => HSMul.hSMul (Inv.inv (2 : Real))
        ((1 / (b : Complex)) ^ (w i / 2) * Complex.Gamma (w i / 2))) := by
    have hCast : (C : Complex) = Finset.univ.prod (fun i : Fin n => (cBase : Complex) ^ (m i)) := by
      unfold C
      rw [Complex.ofReal_prod]
      simp only [Complex.ofReal_pow]
    rw [hCast]
    exact hD.2
  change integral mu f = _
  rw [hc.2, integral_smul_nnreal_measure, <- hPush.integral_comp E.measurableEmbedding]
  have hFun : (fun p : Prod (Prod Y N) K => f (E p)) =
      (fun p : Prod (Prod Y N) K => D p.1) := funext hF
  rw [hFun, hProb, hDiag]
  change HSMul.hSMul (c : Real) (_ : Complex) = _
  rw [Complex.real_smul, Complex.ofReal_mul, mul_assoc]

end LocalSphericalIntegral


section

variable {F : Type*} [RCLike F] {n : Nat}

local notation "M" => Matrix (Fin n) (Fin n) F

private theorem archFrobeniusSq_star (A : M) :
    archFrobeniusSq (star A) = archFrobeniusSq A := by
  unfold archFrobeniusSq
  simp_rw [Matrix.star_apply, RCLike.star_def, RCLike.norm_conj]
  rw [Finset.sum_comm]

private theorem archFrobeniusSq_unitary_mul (Q : Matrix.unitaryGroup (Fin n) F) (A : M) :
    archFrobeniusSq (Q.val * A) = archFrobeniusSq A := by
  rw [<- archFrobeniusSq_star (Q.val * A), star_mul]
  change archFrobeniusSq (star A * (Inv.inv Q).val) = _
  rw [archFrobeniusSq_mul_unitary, archFrobeniusSq_star]

private theorem norm_det_unitary_mul (Q : Matrix.unitaryGroup (Fin n) F) (A : M) :
    norm ((Q.val * A : M).det) = norm A.det := by
  rw [Matrix.det_mul, norm_mul, norm_det_archUnitary, one_mul]

private theorem continuous_unitary_toUnits :
    Continuous (fun Q : Matrix.unitaryGroup (Fin n) F => Unitary.toUnits Q) := by
  rw [Units.isInducing_embedProduct.continuous_iff]
  change Continuous (fun Q : Matrix.unitaryGroup (Fin n) F =>
    Prod.mk Q.val (MulOpposite.op (star Q.val)))
  have hs : Continuous (fun A : M => star A) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun A : M => star (A j i))
    rw [RCLike.star_def]
    exact RCLike.continuous_conj.comp ((continuous_apply i).comp (continuous_apply j))
  exact continuous_subtype_val.prodMk
    (MulOpposite.opHomeomorph.continuous.comp (hs.comp continuous_subtype_val))

end


private theorem integrable_integral_weighted_leftAverage
    {G K : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace K]
    (mu : Measure G) [mu.IsMulLeftInvariant] [SFinite mu]
    (nu : Measure K) [IsProbabilityMeasure nu]
    (b : K -> G)
    (hm : Measurable (fun p : Prod K G => b p.1 * p.2)) (w v : G -> Complex)
    (hw : forall k x, w (b k * x) = w x)
    (hf : Integrable (fun g => w g * v g) mu) :
    let a (g : G) : Complex := integral nu (fun k => v (b k * g))
    And (Integrable (fun g => w g * a g) mu)
      (integral mu (fun g => w g * a g) = integral mu (fun g => w g * v g)) := by
  let f (g : G) := w g * v g
  let a (g : G) := integral nu (fun k => v (b k * g))
  let X (p : Prod K G) := w p.2 * v (b p.1 * p.2)
  let J (p : Prod K G) : Prod K G := Prod.mk p.1 (b p.1 * p.2)
  have hJ : MeasurePreserving J (nu.prod mu) (nu.prod mu) :=
    (MeasurePreserving.id nu).skew_product hm
      (Filter.Eventually.of_forall (fun k => map_mul_left_eq_self mu (b k)))
  have hRel : Function.comp (fun p : Prod K G => f p.2) J = X := by
    funext p
    change w (b p.1 * p.2) * v (b p.1 * p.2) = w p.2 * v (b p.1 * p.2)
    rw [hw]
  have hX : Integrable X (nu.prod mu) := by
    rw [<- hRel]
    exact hJ.integrable_comp_of_integrable (hf.comp_snd nu)
  have hG (g : G) : integral nu (fun k => X (Prod.mk k g)) = w g * a g := by
    change integral nu (fun k => w g * v (b k * g)) = _
    rw [integral_const_mul]
  have hK (k : K) : integral mu (fun g => X (Prod.mk k g)) = integral mu f := by
    calc
      _ = integral mu (fun g => f (b k * g)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun g => by
          change w g * v (b k * g) = w (b k * g) * v (b k * g)
          rw [hw])
      _ = _ := (measurePreserving_mul_left mu (b k)).integral_comp
        (MeasurableEquiv.mulLeft (b k)).measurableEmbedding f
  have hi : Integrable (fun g => w g * a g) mu := by
    simpa only [hG] using hX.integral_prod_right
  refine And.intro hi ?_
  change integral mu (fun g => w g * a g) = integral mu f
  calc
    _ = integral mu (fun g => integral nu (fun k => X (Prod.mk k g))) := by
      simp_rw [hG]
    _ = integral nu (fun k => integral mu (fun g => X (Prod.mk k g))) :=
      (integral_integral_swap (f := fun k g => X (Prod.mk k g)) hX).symm
    _ = integral nu (fun _ : K => integral mu f) := by
      simp_rw [hK]
    _ = _ := by simp [integral_const, measureReal_def]



open MeasureTheory

section AveragedSphericalIntegral

variable (F : Type*) [RCLike F] [ProperSpace F] [SecondCountableTopology F]
  [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
  [SigmaFinite (volume : Measure F)] (n : Nat)

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "G" => Units M
local notation "P" => positiveDiagonalSubgroup F n
local notation "N" => valuationUpperUnitriangularSubgroup F n
local notation "T" => positiveUpperTriangularMatrixSubgroup F n
local notation "K" => Matrix.unitaryGroup (Fin n) F
local notation "Y" => (Fin n -> Real)

/-- Averaging the normalized section over the unitary group gives the same
absolutely convergent local zeta formula for the spherical coefficient. -/
theorem exists_pos_archSphericalLocalIntegral_average
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace T] [BorelSpace T]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace K] [BorelSpace K]
    (mu : Measure G) [mu.IsHaarMeasure] [mu.InnerRegular] [SFinite mu]
    (muK : Measure K) [muK.IsHaarMeasure] [IsProbabilityMeasure muK]
    (b : Real) (hb : 0 < b) (z : Fin n -> Complex) (v : G -> Complex)
    (hv : forall (r : Y) (_ : forall i, 0 < r i) (u : N) (q : K) (g : G),
      g.val = ((Matrix.diagonal (fun i => (r i : F)) * u.val.val.val) * q.val) ->
      v g = Finset.univ.prod (fun i : Fin n =>
        (r i : Complex) ^ ((Module.finrank Real F : Complex) * z i +
          (Module.finrank Real F : Complex) * ((n : Complex) - 1 - 2 * (i.val : Complex)) / 2))) :
    exists C : Real, And (0 < C)
      (forall (s : Complex) (_ : forall i, 0 < (s + z i).re),
        let d := Module.finrank Real F
        let coeff (g : G) := integral muK (fun q : K => v (Unitary.toUnits q * g))
        let f (g : G) := archMatrixGaussianZetaDensity d b s g.val (coeff g)
        And (Integrable f mu)
          (integral mu f = (C : Complex) *
            Finset.univ.prod (fun i : Fin n => HSMul.hSMul (Inv.inv (2 : Real))
              ((1 / (b : Complex)) ^ ((d : Complex) * (s + z i) / 2) *
                Complex.Gamma ((d : Complex) * (s + z i) / 2))))) := by
  choose C hC h using exists_pos_archSphericalLocalIntegral F n mu muK b hb z v hv
  refine Exists.intro C (And.intro hC ?_)
  intro s hs
  let d := Module.finrank Real F
  let W (g : G) := archMatrixGaussianZetaDensity d b s g.val 1
  let coeff (g : G) := integral muK (fun q : K => v (Unitary.toUnits q * g))
  have hS := h s hs
  have hSplit (k : G -> Complex) :
      (fun g : G => W g * k g) =
        (fun g : G => archMatrixGaussianZetaDensity d b s g.val (k g)) := by
    funext g
    simp only [W, archMatrixGaussianZetaDensity, mul_one]
  have hW (q : K) (g : G) : W (Unitary.toUnits q * g) = W g := by
    change archMatrixGaussianZetaDensity d b s (q.val * g.val) 1 =
      archMatrixGaussianZetaDensity d b s g.val 1
    unfold archMatrixGaussianZetaDensity
    rw [archFrobeniusSq_unitary_mul, norm_det_unitary_mul]
  let _ : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n -> Fin n -> F))
  let op : Homeomorph M (MulOpposite M) := MulOpposite.opHomeomorph
  let _ : SecondCountableTopology (MulOpposite M) := op.symm.isEmbedding.secondCountableTopology
  have hG : Topology.IsEmbedding (Units.embedProduct M) := Units.isEmbedding_embedProduct
  let _ : SecondCountableTopology G := hG.secondCountableTopology
  have hK : Topology.IsEmbedding (fun q : K => q.val) := Topology.IsEmbedding.subtypeVal
  let _ : SecondCountableTopology K := hK.secondCountableTopology
  have hB : Continuous (fun q : K => Unitary.toUnits q) := continuous_unitary_toUnits
  have hMeas : Measurable (fun p : Prod K G => Unitary.toUnits p.1 * p.2) :=
    ((hB.comp continuous_fst).mul continuous_snd).measurable
  have hV : Integrable (fun g => W g * v g) mu := by
    rw [hSplit v]
    exact hS.1
  have hA := integrable_integral_weighted_leftAverage mu muK
    (fun q : K => Unitary.toUnits q) hMeas W v hW hV
  change And (Integrable (fun g : G => archMatrixGaussianZetaDensity d b s g.val (coeff g)) mu) _
  constructor
  . rw [<- hSplit coeff]
    exact hA.1
  . change integral mu (fun g : G => archMatrixGaussianZetaDensity d b s g.val (coeff g)) = _
    rw [<- hSplit coeff, hA.2, hSplit v]
    exact hS.2

end AveragedSphericalIntegral

/-- The real radial factor at $b=pi$ is one half of the standard real Gamma factor. -/
theorem sphericalRealRadialFactor (z : Complex) :
    HSMul.hSMul (Inv.inv (2 : Real))
      ((1 / (Real.pi : Complex)) ^ (z / 2) * Complex.Gamma (z / 2)) =
      (1 / 2 : Complex) * DedekindZeta.LReal z := by
  have hArg : Not ((Real.pi : Complex).arg = Real.pi) := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact ne_of_lt Real.pi_pos
  rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat,
    one_div (Real.pi : Complex), Complex.inv_cpow _ _ hArg, <- Complex.cpow_neg]
  rw [DedekindZeta.LReal, neg_div]
  rw [one_div (2 : Complex)]

/-- The complex radial factor at $b=2pi$ is one quarter of the standard complex Gamma factor. -/
theorem sphericalComplexRadialFactor (z : Complex) :
    HSMul.hSMul (Inv.inv (2 : Real))
      ((1 / ((2 * Real.pi : Real) : Complex)) ^ ((2 * z) / 2) * Complex.Gamma ((2 * z) / 2)) =
      (1 / 4 : Complex) * DedekindZeta.LComplex z := by
  let b := 2 * Real.pi
  have hb : 0 < b := mul_pos two_pos Real.pi_pos
  have hArg : Not ((b : Complex).arg = Real.pi) := by
    rw [Complex.arg_ofReal_of_nonneg hb.le]
    exact ne_of_lt Real.pi_pos
  have hz : (2 * z) / 2 = z := by ring
  change HSMul.hSMul (Inv.inv (2 : Real))
    ((1 / (b : Complex)) ^ ((2 * z) / 2) * Complex.Gamma ((2 * z) / 2)) = _
  rw [hz, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat,
    one_div (b : Complex), Complex.inv_cpow _ _ hArg, <- Complex.cpow_neg]
  have hbC : (b : Complex) = 2 * (Real.pi : Complex) := by
    simp only [b, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [hbC, DedekindZeta.LComplex]
  ring

end Robin1984.GRH
