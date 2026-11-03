/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCoordinates

/-! Exact coordinate transport of the two actual factor actions. -/
namespace VOA.DeligneAudit.D4Two

open VOA.DeligneAudit.D1TensorG VOA.DeligneAudit.SectorLoop

noncomputable section

variable {n : ℕ}

abbrev SiteVector (n : ℕ) := SiteIndex n → ℂ
abbrev TwoVector (n : ℕ) := PairIndex n → ℂ

/-- Transport an actual site operator to its standard coordinates. -/
def siteAction (A : Module.End ℂ (D1SiteG.Space n)) : Module.End ℂ (SiteVector n) :=
  (siteCoordinates n).toLinearMap ∘ₗ A ∘ₗ (siteCoordinates n).symm.toLinearMap

@[simp] theorem siteAction_apply (A : Module.End ℂ (D1SiteG.Space n)) (v : SiteVector n) :
    siteAction A v = siteCoordinates n (A ((siteCoordinates n).symm v)) := rfl

@[simp] theorem siteAction_coordinates (A : Module.End ℂ (D1SiteG.Space n))
    (u : D1SiteG.Space n) :
    siteAction A (siteCoordinates n u) = siteCoordinates n (A u) := by
  simp [siteAction]

/-- Apply a coordinate operator to the first tensor coordinate. -/
def leftAction (A : Module.End ℂ (SiteVector n)) : Module.End ℂ (TwoVector n) where
  toFun v p := A (fun i => v (i, p.2)) p.1
  map_add' u v := by
    funext p
    change A ((fun i => u (i, p.2)) + (fun i => v (i, p.2))) p.1 = _
    rw [map_add]
    rfl
  map_smul' z v := by
    funext p
    change A (z • (fun i => v (i, p.2))) p.1 = _
    rw [map_smul]
    rfl

/-- Apply a coordinate operator to the second tensor coordinate. -/
def rightAction (A : Module.End ℂ (SiteVector n)) : Module.End ℂ (TwoVector n) where
  toFun v p := A (fun i => v (p.1, i)) p.2
  map_add' u v := by
    funext p
    change A ((fun i => u (p.1, i)) + (fun i => v (p.1, i))) p.2 = _
    rw [map_add]
    rfl
  map_smul' z v := by
    funext p
    change A (z • (fun i => v (p.1, i))) p.2 = _
    rw [map_smul]
    rfl

private theorem tensor_linear_ext {U : Type*} [AddCommGroup U] [Module ℂ U]
    (L M : D1TensorG.Space n 2 →ₗ[ℂ] U)
    (h : ∀ u : Fin 2 → D1SiteG.Space n,
      L (PiTensorProduct.tprod ℂ u) = M (PiTensorProduct.tprod ℂ u)) : L = M := by
  apply PiTensorProduct.ext
  ext u
  exact h u

/-- The left factor formula holds for every actual tensor, by the tensor universal property. -/
theorem coordinates_local_left (A : Module.End ℂ (D1SiteG.Space n))
    (v : D1TensorG.Space n 2) :
    coordinates n (localOp (0 : Fin 2) A v) =
      leftAction (siteAction A) (coordinates n v) := by
  have h : (coordinates n).toLinearMap ∘ₗ localOp (0 : Fin 2) A =
      leftAction (siteAction A) ∘ₗ (coordinates n).toLinearMap := by
    apply tensor_linear_ext
    intro u
    funext p
    change coordinates n (localOp (0 : Fin 2) A (PiTensorProduct.tprod ℂ u)) p =
      siteAction A (fun i => coordinates n (PiTensorProduct.tprod ℂ u) (i, p.2)) p.1
    simp_rw [localOp_tprod, coordinates_tprod]
    rw [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    change siteCoordinates n (A (u 0)) p.1 * siteCoordinates n (u 1) p.2 =
      siteAction A (fun i => siteCoordinates n (u 0) i * siteCoordinates n (u 1) p.2) p.1
    have he : (fun i => siteCoordinates n (u 0) i * siteCoordinates n (u 1) p.2) =
        siteCoordinates n (u 1) p.2 • siteCoordinates n (u 0) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [he, map_smul, siteAction_coordinates]
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  exact LinearMap.congr_fun h v

/-- The right factor formula holds for every actual tensor. -/
theorem coordinates_local_right (A : Module.End ℂ (D1SiteG.Space n))
    (v : D1TensorG.Space n 2) :
    coordinates n (localOp (1 : Fin 2) A v) =
      rightAction (siteAction A) (coordinates n v) := by
  have h : (coordinates n).toLinearMap ∘ₗ localOp (1 : Fin 2) A =
      rightAction (siteAction A) ∘ₗ (coordinates n).toLinearMap := by
    apply tensor_linear_ext
    intro u
    funext p
    change coordinates n (localOp (1 : Fin 2) A (PiTensorProduct.tprod ℂ u)) p =
      siteAction A (fun i => coordinates n (PiTensorProduct.tprod ℂ u) (p.1, i)) p.2
    simp_rw [localOp_tprod, coordinates_tprod]
    rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), Function.update_self]
    change siteCoordinates n (u 0) p.1 * siteCoordinates n (A (u 1)) p.2 =
      siteAction A (fun i => siteCoordinates n (u 0) p.1 * siteCoordinates n (u 1) i) p.2
    have he : (fun i => siteCoordinates n (u 0) p.1 * siteCoordinates n (u 1) i) =
        siteCoordinates n (u 0) p.1 • siteCoordinates n (u 1) := rfl
    rw [he, map_smul, siteAction_coordinates]
    rfl
  exact LinearMap.congr_fun h v

/-- The exact zero-mode coadjoint matrix used by the finite integer certificates. -/
theorem siteAction_zero_inl (f : Fin n → Fin n → Fin n → ℂ) (c i : Fin n)
    (v : SiteVector n) :
    siteAction (D1SiteG.zeroOp f c) v (Sum.inl i) =
      -∑ j : Fin n, f c i j * v (Sum.inl j) := by
  simp [siteAction, D1SiteG.zeroOp_apply, D1SiteG.coOp_apply, DeligneSector.slotA, siteCoordinates]

@[simp] theorem siteAction_zero_inr (f : Fin n → Fin n → Fin n → ℂ) (c : Fin n)
    (v : SiteVector n) : siteAction (D1SiteG.zeroOp f c) v (Sum.inr ()) = 0 := rfl

@[simp] theorem siteAction_one_inl (c i : Fin n) (v : SiteVector n) :
    siteAction (D1SiteG.oneOp c) v (Sum.inl i) = 0 := rfl

@[simp] theorem siteAction_one_inr (c : Fin n) (v : SiteVector n) :
    siteAction (D1SiteG.oneOp c) v (Sum.inr ()) = v (Sum.inl c) := rfl

end
end VOA.DeligneAudit.D4Two

#print axioms VOA.DeligneAudit.D4Two.coordinates_local_left
#print axioms VOA.DeligneAudit.D4Two.coordinates_local_right
#print axioms VOA.DeligneAudit.D4Two.siteAction_zero_inl
