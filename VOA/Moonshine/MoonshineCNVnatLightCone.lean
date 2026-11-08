import VOA.Moonshine.MoonshineCNTensorLightConeKernels
import VOA.Moonshine.MoonshineCNTensorConformal
import VOA.Moonshine.AutVnat

/-! # The concrete light-cone decomposition on the moonshine tensor sector

This specializes the tensor splitting to the existing V♮ Virasoro modes.
It is a decomposition of actual ranges and kernels; the graded string
module, form, and physical quotient still require their separate constructions.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster
open scoped TensorProduct

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem nearVirasoroNegative_comm (W : NearVOA V) (i j : ℕ) :
    nearVirasoroMode W (-(i + 1 : ℤ)) * nearVirasoroMode W (-(j + 1 : ℤ)) -
      nearVirasoroMode W (-(j + 1 : ℤ)) * nearVirasoroMode W (-(i + 1 : ℤ)) =
      ((j : ℂ) - i) • nearVirasoroMode W (-((i + j + 1 : ℕ) + 1 : ℤ)) := by
  have h := W.virasoro (-(i + 1 : ℤ)) (-(j + 1 : ℤ))
  rw [if_neg (by omega), add_zero] at h
  have hi : -(i + 1 : ℤ) + -(j + 1 : ℤ) + 1 = -((i + j + 1 : ℕ) + 1 : ℤ) + 1 := by
    omega
  have hc : ((-(i + 1 : ℤ) : ℤ) : ℂ) - ((-(j + 1 : ℤ) : ℤ) : ℂ) = (j : ℂ) - i := by
    push_cast
    ring
  simpa only [nearVirasoroMode, Ring.lie_def, hi, hc] using h

/-- The negative modes are the sum of the existing matter and hyperbolic modes. -/
def vnatHypNegative (κ ell : ℂ) (j : ℕ) : Module.End ℂ (Vnat ⊗[ℂ] hypFock) :=
  hypTensorNegative (fun j => nearVirasoroMode VnatVOA.toNearVOA (-(j + 1 : ℤ))) κ ell j

/-- No unestablished form, representation, or splitting datum is assumed. -/
theorem vnatHypTensor_lightConeSplit (κ ell : ℂ) (h : κ ≠ 0 ∨ ell ≠ 0) :
    ∃ a : Fin 2, IsCompl (⨆ j : ℕ, LinearMap.range (vnatHypNegative κ ell j))
      (⨅ j : ℕ, LinearMap.ker
        ((hypOscillator a (if a = 0 then κ else ell) (j + 1 : ℤ)).lTensor Vnat)) :=
  hypTensor_lightConeSplit_nonzero _ (nearVirasoroNegative_comm VnatVOA.toNearVOA) κ ell h

end VOA.Moonshine.ConwayNorton
