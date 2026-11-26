import DedekindZeta.Theta
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.Tactic.Ring
import Robin1984.GRH.SchwartzGaussian

/-!
## Provenance

- Classification: **Standard mathematical formalization**.
- Mathematical source: The archimedean Gaussian in the Godement-Jacquet zeta integral.
- Formalization note: Realizes its product over the infinite places as a Schwartz function in the global Minkowski matrix coordinates.
- PROVENANCE-END
-/

/-!
# The archimedean matrix Gaussian as a Schwartz test

The Euclidean Gaussian on the vectorized Minkowski matrix space is a
Schwartz function. Its pullback to archimedean adelic matrices is the
product of the real and complex Gaussians with their local norm weights.
-/

set_option autoImplicit false

open NumberField
open scoped Classical RealInnerProductSpace

noncomputable section

namespace Robin1984.GRH

section AdelicMatrix

variable (K : Type*) [Field K] [NumberField K] (n : Nat)

local notation "Ix" => Prod (Fin n) (Fin n)
local notation "Arch" => PiLp 2 (fun _ : Ix => DedekindZeta.Theta.minkowskiSpace K)

/-- The Gaussian Schwartz test on the Minkowski matrix coordinates used in
the global Godement-Jacquet zeta integral. -/
def archMinkowskiMatrixGaussian : SchwartzMap Arch Complex :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    (schwartzExp_of_negativeQuadratic
      ((Function.HasTemperateGrowth.const (-Real.pi)).mul
        (Function.hasTemperateGrowth_norm_sq Arch)) Real.pi_pos (fun _ => le_rfl))

/-- In the Euclidean matrix coordinates the test is the Gaussian of the
squared norm. -/
theorem archMinkowskiMatrixGaussian_apply (x : Arch) :
    archMinkowskiMatrixGaussian K n x = (Real.exp (-Real.pi * norm x ^ 2) : Complex) := by
  rfl

private theorem norm_sq_archMinkowski (z : Arch) :
    norm z ^ 2 = Finset.univ.sum (fun i : Ix => norm (z i) ^ 2) := by
  classical
  rw [<- real_inner_self_eq_norm_sq, PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => real_inner_self_eq_norm_sq _)

/-- The Minkowski Gaussian separates over infinite places. The exponent is
weighted by one at real places and two at complex places. -/
theorem archMinkowskiMatrixGaussian_factor
    (X : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) :
    archMinkowskiMatrixGaussian K n
        (WithLp.toLp 2 (fun i : Ix => DedekindZeta.Theta.toMinkowski K
          (InfiniteAdeleRing.ringEquiv_mixedSpace K (X.vec i)))) =
      Finset.univ.prod (fun w : InfinitePlace K =>
        (Real.exp (-(InfinitePlace.mult w : Real) * Real.pi *
          (Finset.univ.sum (fun i : Ix => NumberField.mixedEmbedding.normAtPlace w
            (InfiniteAdeleRing.ringEquiv_mixedSpace K (X.vec i)) ^ 2))) : Complex)) := by
  classical
  rw [archMinkowskiMatrixGaussian_apply,
    norm_sq_archMinkowski, <- Complex.ofReal_prod, <- Real.exp_sum]
  congr 2
  simp only [DedekindZeta.Theta.norm_toMinkowski_sq]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun i _ => ?_))
  ring

end AdelicMatrix

end Robin1984.GRH
