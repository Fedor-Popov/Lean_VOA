/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.GradedUnitarity

/-!
# Transport of positive sesquilinear forms

This file gives the small functoriality package needed to transfer graded positivity through an
injective complex-linear realization, such as an inverse Drinfeld--Sokolov map.  It is deliberately
independent of vertex-operator-algebra structure: only a linear map, a submodule, and the
repository's `SesqForm` and `IsPosOn` are used.
-/

namespace VOA

namespace SesqForm

variable {E F G : Type*}
variable [AddCommGroup E] [Module ℂ E]
variable [AddCommGroup F] [Module ℂ F]
variable [AddCommGroup G] [Module ℂ G]

/-- Pull a sesquilinear form back along a complex-linear map in both slots. -/
def pullback (h : SesqForm F) (iota : E →ₗ[ℂ] F) : SesqForm E where
  toFun x y := h (iota x) (iota y)
  add_left x x' y := by rw [map_add, h.add_left]
  smul_left a x y := by rw [map_smul, h.smul_left]
  add_right x y y' := by rw [map_add, h.add_right]
  smul_right a x y := by rw [map_smul, h.smul_right]

@[simp] theorem pullback_apply (h : SesqForm F) (iota : E →ₗ[ℂ] F) (x y : E) :
    h.pullback iota x y = h (iota x) (iota y) := rfl

/-- Pullback is contravariantly functorial under composition of linear maps. -/
theorem pullback_comp (h : SesqForm G) (j : F →ₗ[ℂ] G) (iota : E →ₗ[ℂ] F) :
    (h.pullback j).pullback iota = h.pullback (j.comp iota) := by
  rfl

/-- Pullback commutes with the sign twist used in graded unitarity. -/
theorem pullback_signedForm (h : SesqForm F) (iota : E →ₗ[ℂ] F) (p : ℕ) :
    (signedForm h p).pullback iota = signedForm (h.pullback iota) p := by
  rfl

/-- Positivity on the image submodule pulls back through an injective linear map. -/
theorem isPosOn_pullback {h : SesqForm F} {iota : E →ₗ[ℂ] F}
    (hiota : Function.Injective iota) {S : Submodule ℂ E}
    (hpos : IsPosOn h (S.map iota)) :
    IsPosOn (h.pullback iota) S := by
  intro x hx hx0
  have hix : iota x ∈ S.map iota := ⟨x, hx, rfl⟩
  have hix0 : iota x ≠ 0 := by
    intro hzero
    apply hx0
    apply hiota
    simpa using hzero
  obtain ⟨r, hr, hdiag⟩ := hpos (iota x) hix hix0
  exact ⟨r, hr, hdiag⟩

/-- Compatibility wrapper for a source form presented as the exact pullback of an ambient form.
This is the form normally used by realization and inverse-DS arguments. -/
theorem isPosOn_of_eq_pullback {hE : SesqForm E} {hF : SesqForm F}
    {iota : E →ₗ[ℂ] F} (hiota : Function.Injective iota)
    (hcompat : hE = hF.pullback iota) {S : Submodule ℂ E}
    (hpos : IsPosOn hF (S.map iota)) :
    IsPosOn hE S := by
  rw [hcompat]
  exact isPosOn_pullback hiota hpos

/-- The signed compatibility statement follows without a separate calculation. -/
theorem signedForm_eq_pullback {hE : SesqForm E} {hF : SesqForm F}
    {iota : E →ₗ[ℂ] F} (hcompat : hE = hF.pullback iota) (p : ℕ) :
    signedForm hE p = (signedForm hF p).pullback iota := by
  rw [hcompat, pullback_signedForm]

/-- Signed positivity transports through the same injective realization. -/
theorem isPosOn_signedForm_of_eq_pullback {hE : SesqForm E} {hF : SesqForm F}
    {iota : E →ₗ[ℂ] F} (hiota : Function.Injective iota)
    (hcompat : hE = hF.pullback iota) {S : Submodule ℂ E} (p : ℕ)
    (hpos : IsPosOn (signedForm hF p) (S.map iota)) :
    IsPosOn (signedForm hE p) S :=
  isPosOn_of_eq_pullback hiota (signedForm_eq_pullback hcompat p) hpos

end SesqForm

end VOA
