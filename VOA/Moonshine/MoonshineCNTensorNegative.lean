import VOA.Moonshine.MoonshineCNHyperbolicLightCone
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Genuine negative modes on a tensor sector

Polynomial coordinates take values in the arbitrary matter module. No basis,
grading, form, or finite-dimensionality of that module is required here.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped TensorProduct BigOperators

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

def hypTensorCoordinates : (V ⊗[ℂ] hypFock) ≃ₗ[ℂ] ((ℕ × Fin 2) →₀ ℕ) →₀ V :=
  TensorProduct.equivFinsuppOfBasisRight (basisMonomials (ℕ × Fin 2) ℂ)

@[simp] theorem hypTensorCoordinates_tmul (v : V) (p : hypFock)
    (e : (ℕ × Fin 2) →₀ ℕ) :
    hypTensorCoordinates (v ⊗ₜ[ℂ] p) e = coeff e p • v := by
  rw [hypTensorCoordinates, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  rfl

@[simp] theorem hypTensorCoordinates_monomial (v : V) (e : (ℕ × Fin 2) →₀ ℕ) :
    hypTensorCoordinates (v ⊗ₜ[ℂ] monomial e 1) = Finsupp.single e v := by
  ext t
  simp only [hypTensorCoordinates_tmul, coeff_monomial]
  by_cases h : e = t
  · subst t; simp
  · simp [h, Ne.symm h]

@[simp] theorem hypTensorCoordinates_symm_single (v : V) (e : (ℕ × Fin 2) →₀ ℕ) :
    (hypTensorCoordinates (V := V)).symm (Finsupp.single e v) =
      v ⊗ₜ[ℂ] monomial e 1 := by
  apply hypTensorCoordinates.injective
  simp

theorem hypTensor_expansion (x : V ⊗[ℂ] hypFock) :
    x = ∑ e ∈ (hypTensorCoordinates x).support,
      hypTensorCoordinates x e ⊗ₜ[ℂ] monomial e 1 := by
  conv_lhs => rw [← hypTensorCoordinates.symm_apply_apply x]
  rw [hypTensorCoordinates, TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  rfl

def hypTensorSupported (s : Set ((ℕ × Fin 2) →₀ ℕ)) : Submodule ℂ (V ⊗[ℂ] hypFock) :=
  (Finsupp.supported V ℂ s).comap hypTensorCoordinates.toLinearMap

theorem hypTensorSupported_mem (s : Set ((ℕ × Fin 2) →₀ ℕ)) (x : V ⊗[ℂ] hypFock) :
    x ∈ hypTensorSupported s ↔ ∀ e, hypTensorCoordinates x e ≠ 0 → e ∈ s := by
  change (∀ e ∈ (hypTensorCoordinates x).support, e ∈ s) ↔ _
  simp only [Finsupp.mem_support_iff]

theorem hypTensorSupported_tmul (s : Set ((ℕ × Fin 2) →₀ ℕ)) (v : V) (p : hypFock)
    (hp : ∀ e, coeff e p ≠ 0 → e ∈ s) : v ⊗ₜ[ℂ] p ∈ hypTensorSupported s := by
  rw [hypTensorSupported_mem]
  intro e he
  apply hp e
  intro hz
  simp [hz] at he

theorem hypTensorSupported_mono {s t : Set ((ℕ × Fin 2) →₀ ℕ)} (h : s ⊆ t) :
    hypTensorSupported (V := V) s ≤ hypTensorSupported t := by
  intro x hx
  rw [hypTensorSupported_mem] at hx ⊢
  exact fun e he => h (hx e he)

theorem hypTensorSupported_induction (s : Set ((ℕ × Fin 2) →₀ ℕ))
    (U : Submodule ℂ (V ⊗[ℂ] hypFock))
    (h : ∀ e ∈ s, ∀ v : V, v ⊗ₜ[ℂ] monomial e 1 ∈ U) :
    hypTensorSupported s ≤ U := by
  intro x hx
  rw [hypTensor_expansion x]
  apply Submodule.sum_mem
  intro e he
  exact h e ((hypTensorSupported_mem s x).mp hx e (Finsupp.mem_support_iff.mp he)) _

def hypTensorFiltered (d w : ℕ) : Submodule ℂ (V ⊗[ℂ] hypFock) :=
  hypTensorSupported {e | Finsupp.weight hypBCountWeight e < d ∨
    (Finsupp.weight hypBCountWeight e = d ∧ Finsupp.weight hypBLevelWeight e < w)}

theorem hypTensorFiltered_tmul (d w : ℕ) (v : V) (p : hypFock)
    (hp : p ∈ hypBFiltered d w) : v ⊗ₜ[ℂ] p ∈ hypTensorFiltered d w :=
  hypTensorSupported_tmul _ v p ((hypBFiltered_mem d w p).mp hp)

theorem hypTensorFiltered_mono {d w D W : ℕ} (h : d < D ∨ (d = D ∧ w ≤ W)) :
    hypTensorFiltered (V := V) d w ≤ hypTensorFiltered D W := by
  apply hypTensorSupported_mono
  intro e he
  change _ < _ ∨ (_ = _ ∧ _ < _) at he ⊢
  omega

/-- Index `j` denotes the genuine tensor mode with integer index `-(j+1)`. -/
def hypTensorNegative (D : ℕ → Module.End ℂ V) (κ ell : ℂ) (j : ℕ) :
    Module.End ℂ (V ⊗[ℂ] hypFock) :=
  (D j).rTensor hypFock + (hypSugawara κ ell (-(j + 1 : ℤ))).lTensor V

@[simp] theorem hypTensorNegative_tmul (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (j : ℕ) (v : V) (p : hypFock) :
    hypTensorNegative D κ ell j (v ⊗ₜ[ℂ] p) =
      D j v ⊗ₜ[ℂ] p + v ⊗ₜ[ℂ] hypSugawara κ ell (-(j + 1 : ℤ)) p := by
  simp [hypTensorNegative]

theorem hypTensorNegative_comm (D : ℕ → Module.End ℂ V)
    (hD : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (κ ell : ℂ) (i j : ℕ) :
    hypTensorNegative D κ ell i * hypTensorNegative D κ ell j -
      hypTensorNegative D κ ell j * hypTensorNegative D κ ell i =
      ((j : ℂ) - i) • hypTensorNegative D κ ell (i + j + 1) := by
  apply TensorProduct.ext'
  intro v p
  have hv := LinearMap.congr_fun (hD i j) v
  have hp := LinearMap.congr_fun (hypSugawara_negative_comm κ ell i j) p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hv hp ⊢
  simp only [hypTensorNegative_tmul, map_add]
  have hvt := congrArg (fun z => z ⊗ₜ[ℂ] p) hv
  have hpt := congrArg (fun z => v ⊗ₜ[ℂ] z) hp
  simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub,
    TensorProduct.tmul_smul, ← TensorProduct.smul_tmul'] at hvt hpt
  rw [smul_add]
  rw [← hvt, ← hpt]
  abel

end VOA.Moonshine.ConwayNorton
