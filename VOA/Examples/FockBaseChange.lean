/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.LiDelta
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Base change of operators from `Fock` to `FockW`  (Route 1, step 1)

Li's conjugation identity does not typecheck as usually written, because `Δ : Fock → FockW`
maps between *different* spaces.  The honest statement lives entirely on `FockW`:

  `deltaSubW λ ∘ Y_W(u,z₀) ∘ deltaSubW (-λ) = Y_W (Δ(λ, z+z₀) u, z₀)`

so `Y` must first be transported to `FockW`.  Since
`MvPolynomial.scalarRTensorAlgEquiv : Fock ⊗[ℂ] ℂ[w] ≃ₐ[ℂ] FockW`, an operator on `Fock`
transports as `T ↦ e ∘ (T ⊗ id) ∘ e⁻¹`.

## What is here

`fockWEquiv` (the identification), `bcEnd` (the operator base change), and the facts that make
it usable as a ring map on operators: `bcEnd_one`, `bcEnd_comp`, `bcEnd_add`, `bcEnd_smul`.

## Status

Proved, axiom-clean.  **Not** here: `Y_W` itself — the transport of `YN` along `bcEnd`,
including its field/mode API — and then the conjugation identity.
-/

namespace VOA.Heisenberg

open MvPolynomial
open scoped TensorProduct

/-- `FockW ≅ Fock ⊗[ℂ] ℂ[w]`. -/
noncomputable def fockWEquiv : Fock ⊗[ℂ] Polynomial ℂ ≃ₐ[ℂ] FockW :=
  MvPolynomial.scalarRTensorAlgEquiv

/-- **Base change of an operator** from `Fock` to `FockW`: act on the `Fock` factor. -/
noncomputable def bcEnd (T : Module.End ℂ Fock) : Module.End ℂ FockW :=
  fockWEquiv.toLinearEquiv.conj (LinearMap.rTensor (Polynomial ℂ) T)

/-- Base change preserves composition. -/
theorem bcEnd_comp (T S : Module.End ℂ Fock) :
    bcEnd (T * S) = bcEnd T * bcEnd S := by
  unfold bcEnd
  rw [show (T * S) = T ∘ₗ S from rfl, LinearMap.rTensor_comp]
  ext x
  simp [LinearEquiv.conj_apply]

/-- Base change is unital. -/
theorem bcEnd_one : bcEnd 1 = 1 := by
  unfold bcEnd
  rw [show (1 : Module.End ℂ Fock) = LinearMap.id from rfl, LinearMap.rTensor_id]
  ext x
  simp [LinearEquiv.conj_apply]

/-- Base change is `ℂ`-linear in the operator. -/
theorem bcEnd_add (T S : Module.End ℂ Fock) : bcEnd (T + S) = bcEnd T + bcEnd S := by
  unfold bcEnd
  rw [LinearMap.rTensor_add]
  ext x
  simp [LinearEquiv.conj_apply]

theorem bcEnd_smul (c : ℂ) (T : Module.End ℂ Fock) : bcEnd (c • T) = c • bcEnd T := by
  unfold bcEnd
  rw [LinearMap.rTensor_smul]
  ext x
  simp [LinearEquiv.conj_apply]

/-! ## The transported vertex operator `Y_W`

`Y_W u` is `Y u` acting on the `Fock` factor of `FockW`.  Its field property transports because
`e⁻¹ x` is a finite sum of pure tensors and each `Y u n` truncates on the `Fock` component. -/

/-- **The base-changed vertex operator**, on states from `Fock`. -/
noncomputable def YW (k : ℂ) : Fock →ₗ[ℂ] FormalDist (Module.End ℂ FockW) where
  toFun u := fun n => bcEnd (Y k u n)
  map_add' u v := by
    funext n
    show bcEnd (Y k (u + v) n) = bcEnd (Y k u n) + bcEnd (Y k v n)
    rw [map_add]
    exact bcEnd_add _ _
  map_smul' c u := by
    funext n
    show bcEnd (Y k (c • u) n) = c • bcEnd (Y k u n)
    rw [map_smul]
    exact bcEnd_smul _ _

@[simp] theorem YW_apply (k : ℂ) (u : Fock) (n : ℤ) :
    YW k u n = bcEnd (Y k u n) := rfl

/-- **`bcEnd` transports the field property.**  Given `x : FockW`, pull back along `fockWEquiv`
and induct over the tensor product: a pure tensor `p ⊗ q` truncates at `p`'s bound, and a sum
truncates at the minimum of the two. -/
theorem bcEnd_isField {a : FormalDist (Module.End ℂ Fock)} (ha : IsField a) :
    IsField (fun n => bcEnd (a n)) := by
  intro x
  -- reduce to the tensor side
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ n : ℤ, n < B →
      LinearMap.rTensor (Polynomial ℂ) (a n) (fockWEquiv.toLinearEquiv.symm x) = 0 := by
    induction (fockWEquiv.toLinearEquiv.symm x) using TensorProduct.induction_on with
    | zero => exact ⟨0, fun n _ => by simp⟩
    | tmul p q =>
        obtain ⟨B, hB⟩ := ha p
        exact ⟨B, fun n hn => by
          rw [LinearMap.rTensor_tmul, hB n hn, TensorProduct.zero_tmul]⟩
    | add y z hy hz =>
        obtain ⟨B1, h1⟩ := hy
        obtain ⟨B2, h2⟩ := hz
        exact ⟨min B1 B2, fun n hn => by
          rw [map_add, h1 n (lt_of_lt_of_le hn (min_le_left _ _)),
            h2 n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]⟩
  refine ⟨B, fun n hn => ?_⟩
  show bcEnd (a n) x = 0
  unfold bcEnd
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hB n hn]
  exact map_zero _

theorem YW_isField (k : ℂ) (u : Fock) : IsField (YW k u) :=
  bcEnd_isField (Y_isField k u)

/-! ## Extending `Y_W` to states in `FockW`

The right-hand side of Li's identity is `Y_W (Δ(λ, z+z₀) u, z₀)`, and `Δ(λ,·)u` lands in
`FockW`.  So `Y_W` must accept states from `FockW`, not just from `Fock`.  Via
`fockWEquiv : Fock ⊗[ℂ] ℂ[w] ≅ FockW`, a `ℂ[w]`-linear map out of `FockW` is exactly a
`ℂ`-linear map out of `Fock` with values in a `ℂ[w]`-module — so the extension is
`TensorProduct.lift` of `u ⊗ q ↦ q • Y_W u`. -/

/-- Multiplication by `q : ℂ[w]` on `FockW`, as a `ℂ`-linear endomorphism.  `ℂ[w]` is the
coefficient ring of `FockW = MvPolynomial ℕ ℂ[w]`, so this is scalar multiplication. -/
noncomputable def smulW (q : Polynomial ℂ) : Module.End ℂ FockW where
  toFun x := q • x
  map_add' := smul_add q
  map_smul' c x := by
    simp only [RingHom.id_apply]
    exact smul_comm q c x

@[simp] theorem smulW_apply (q : Polynomial ℂ) (x : FockW) : smulW q x = q • x := rfl

theorem smulW_add (q r : Polynomial ℂ) : smulW (q + r) = smulW q + smulW r := by
  ext x; simp [add_smul]

theorem smulW_smul (c : ℂ) (q : Polynomial ℂ) : smulW (c • q) = c • smulW q := by
  ext x; simp [smul_assoc]

/-- **`Y_W` extended to `FockW`-states**, as a `ℂ`-bilinear pairing on the tensor factors:
`u ⊗ q ↦ q · Y_W u`. -/
noncomputable def YWtensor (k : ℂ) :
    Fock ⊗[ℂ] Polynomial ℂ →ₗ[ℂ] FormalDist (Module.End ℂ FockW) :=
  TensorProduct.lift
    { toFun := fun u =>
        { toFun := fun q => fun n => smulW q * YW k u n
          map_add' := fun q r => by
            funext n
            show smulW (q + r) * YW k u n = smulW q * YW k u n + smulW r * YW k u n
            rw [smulW_add, add_mul]
          map_smul' := fun c q => by
            funext n
            show smulW (c • q) * YW k u n = c • (smulW q * YW k u n)
            rw [smulW_smul, smul_mul_assoc] }
      map_add' := fun u v => by
        refine LinearMap.ext (fun q => ?_)
        funext n
        show smulW q * YW k (u + v) n = smulW q * YW k u n + smulW q * YW k v n
        have h : YW k (u + v) n = YW k u n + YW k v n := by rw [map_add]; rfl
        rw [h, mul_add]
      map_smul' := fun c u => by
        refine LinearMap.ext (fun q => ?_)
        funext n
        show smulW q * YW k (c • u) n = c • (smulW q * YW k u n)
        have h : YW k (c • u) n = c • YW k u n := by rw [map_smul]; rfl
        rw [h, mul_smul_comm] }

/-- **`Y_W` on all of `FockW`** — the operator the right-hand side of Li's identity needs. -/
noncomputable def YWfull (k : ℂ) : FockW →ₗ[ℂ] FormalDist (Module.End ℂ FockW) :=
  (YWtensor k).comp fockWEquiv.toLinearEquiv.symm.toLinearMap

end VOA.Heisenberg
