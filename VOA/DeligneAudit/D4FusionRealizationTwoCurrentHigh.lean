/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCurrent
import Mathlib.Tactic.Module

/-! Every high mode in the actual two-jet model is generated linearly by
modes two and three. This supplies the endpoint for finite span stability. -/
namespace VOA.DeligneAudit.D4Two

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorLoop

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ)

theorem coordinateOp_high (c : Fin n) (k : ℕ) (hk : 2 ≤ k) :
    coordinateOp f c k = ((3 : ℂ) - (k : ℂ)) • coordinateOp f c 2 +
      ((k : ℂ) - 2) • coordinateOp f c 3 := by
  rcases k with _ | _ | k
  · omega
  · omega
  · simp only [coordinateOp, zero_add]
    module

variable (hJ : JacobiCoord f) (hskew : ∀ a b c, f a b c = -f b a c)

/-- This is equality of the actual current endomorphisms, not an identity
assumed for an abstract matrix model. -/
theorem current_high (c : Fin n) (k : ℕ) (hk : 2 ≤ k) :
    (D1TensorG.rep f hJ hskew twoPoints).op c k =
      ((3 : ℂ) - (k : ℂ)) • (D1TensorG.rep f hJ hskew twoPoints).op c 2 +
      ((k : ℂ) - 2) • (D1TensorG.rep f hJ hskew twoPoints).op c 3 := by
  apply LinearMap.ext
  intro v
  apply coordinates_injective n
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    coordinates_current_two]
  exact congrArg (fun a : Module.End ℂ (TwoVector n) => a (coordinates n v))
    (coordinateOp_high f c k hk)

end
end VOA.DeligneAudit.D4Two

#print axioms VOA.DeligneAudit.D4Two.current_high
