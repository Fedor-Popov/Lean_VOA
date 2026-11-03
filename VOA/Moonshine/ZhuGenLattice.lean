/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.ZhuGenV0

/-!
# The charged ground-state step of `V0LowerSpanned`  (Moonshine step M8g, R-gen)

For `x_β = e^β + e^{-β}` (`frameX0P β`) in `V_Λ⁺`:

* `frameX0P_smul_zero_of_form_neg_one`: if `⟨α,β⟩ = -1` then
  `x_α₍₀₎x_β = ε(α,β)·x_{α+β}` (the two cross terms `e^{±α}₍₀₎e^{∓β}` vanish, and
  `ε(-α,-β) = ε(α,β)`);
* `frameX0P_smul_neg_one_of_form_zero`: if `⟨α,β⟩ = 0` then
  `x_α₍₋₁₎x_β = ε(α,β)·(x_{α+β} + x_{α-β})`.

Consequently, for `α, β ∈ Λ₀ \ 0` (`V₀⁺`):

* `x0_mem_span_lowerProd_of_form_neg_one`: `⟨α,β⟩ = -1 ⇒ x_{α+β} ∈ span (lowerProd V0P n)`,
  `n = ½|α+β|²` — a ground state of charge `α+β` is a weight-raising product of two lower-weight
  ground states;
* `x0_add_mem_span_lowerProd_of_form_zero`: `⟨α,β⟩ = 0 ⇒ x_{α+β} + x_{α-β} ∈ span (lowerProd V0P n)`.

These are the only products that can produce ground states (a Fock-dressed source gives a
Fock-excited result), so the ground-state part of `V0LowerSpanned` is exactly a statement about the
lattice `Λ₀` (`GroundLattice`); that lattice statement is **not** proved here (it is proved in
`GroundLattice.lean`).

## Status
`sorry`-free; no project axiom.  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SigmaExist

open VOA VOA.Moonshine VOA.Moonshine.ZhuGen LatGen IntegralLattice HeisenbergN
open Submodule

/-! ## §1  Products of charged vacua -/

/-- `e^a₍ₙ₎e^c = ε(a,c)·e^{a+c}` when `-n-1-⟨a,c⟩ = 0`. -/
theorem e_smul_e_of_eq (a c : leech.carrier) {n : ℤ} (hn : -n - 1 - leech.form a c = 0) :
    leechVOA.smul (latChargeGen leech a) n (latChargeGen leech c)
      = latticeCocycle leech a c • latChargeGen leech (a + c) := by
  have h := leechVOA_smul_latChargeGen_state a c n (vacuumN (rank leech))
  change leechVOA.smul _ n (latStateGen leech (vacuumN (rank leech)) c) = _
  rw [h, hn,
    EEVec_vacuum, if_pos le_rfl, show ((0 : ℤ)).toNat = 0 from rfl, vSchur_zero]
  rfl

/-- `e^a₍ₙ₎e^c = 0` when `-n-1-⟨a,c⟩ < 0`. -/
theorem e_smul_e_of_lt (a c : leech.carrier) {n : ℤ} (hn : -n - 1 - leech.form a c < 0) :
    leechVOA.smul (latChargeGen leech a) n (latChargeGen leech c) = 0 :=
  leechVOA_smul_latChargeGen_eq_zero a c (by omega)

theorem frameX0P_coe (β : leech.carrier) :
    ((frameX0P β : VPlus) : LatModuleGen leech) = latChargeGen leech β + latChargeGen leech (-β) :=
  rfl

/-- `⟨α,β⟩ = -1 ⇒ x_α₍₀₎x_β = ε(α,β)·x_{α+β}`. -/
theorem frameX0P_smul_zero_of_form_neg_one {α β : leech.carrier} (h : leech.form α β = -1) :
    leechVOAPlus.smul (frameX0P α) 0 (frameX0P β) = latticeCocycle leech α β • frameX0P (α + β) := by
  apply Subtype.ext
  rw [plus_smul_coe, frameX0P_coe, frameX0P_coe, Submodule.coe_smul, frameX0P_coe,
    PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_add_right,
    e_smul_e_of_eq α β (by omega),
    e_smul_e_of_lt α (-β) (by rw [leech_form_neg_right]; omega),
    e_smul_e_of_lt (-α) β (by rw [leech_form_neg_left]; omega),
    e_smul_e_of_eq (-α) (-β) (by rw [leech_form_neg_left, leech_form_neg_right]; omega),
    latticeCocycle_neg_neg, show -α + -β = -(α + β) by abel]
  simp only [add_zero, zero_add, smul_add]

/-- `⟨α,β⟩ = 0 ⇒ x_α₍₋₁₎x_β = ε(α,β)·(x_{α+β} + x_{α-β})`. -/
theorem frameX0P_smul_neg_one_of_form_zero {α β : leech.carrier} (h : leech.form α β = 0) :
    leechVOAPlus.smul (frameX0P α) (-1) (frameX0P β)
      = latticeCocycle leech α β • (frameX0P (α + β) + frameX0P (α - β)) := by
  apply Subtype.ext
  rw [plus_smul_coe, frameX0P_coe, frameX0P_coe, Submodule.coe_smul, Submodule.coe_add,
    frameX0P_coe, frameX0P_coe,
    PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_add_right,
    e_smul_e_of_eq α β (by omega),
    e_smul_e_of_eq α (-β) (by rw [leech_form_neg_right]; omega),
    e_smul_e_of_eq (-α) β (by rw [leech_form_neg_left]; omega),
    e_smul_e_of_eq (-α) (-β) (by rw [leech_form_neg_left, leech_form_neg_right]; omega),
    latticeCocycle_neg_neg, latticeCocycle_neg_left, latticeCocycle_neg_right,
    show -α + -β = -(α + β) by abel, show -α + β = -(α - β) by abel, show α + -β = α - β by abel]
  simp only [smul_add]
  abel

/-! ## §2  In `V₀⁺` -/

theorem frameX0P_mem_frameSector_zero {β : leech.carrier} (hβ : β ∈ lambda0) :
    frameX0P β ∈ frameSector 0 := by
  rw [mem_frameSector_zero_iff]
  intro α hα
  change coordEα leech α (latChargeGen leech β + latChargeGen leech (-β)) = 0
  rw [map_add, coordEα_latChargeGen, coordEα_latChargeGen,
    if_neg (by rintro rfl; exact hα hβ), if_neg (by rintro rfl; exact hα (lambda0.neg_mem hβ)),
    add_zero]

/-- `x_β` as an element of `V₀⁺` (`β ∈ Λ₀`). -/
noncomputable def x0 {β : leech.carrier} (hβ : β ∈ lambda0) : V0Sub.carrier :=
  ⟨frameX0P β, by rw [V0Sub_carrier]; exact frameX0P_mem_frameSector_zero hβ⟩

theorem x0_mem_grading {β : leech.carrier} (hβ : β ∈ lambda0) :
    x0 hβ ∈ V0P.grading (LatGen.halfNorm leech β) := InvForm.frameX0P_mem_grading β

theorem V0P_smul_coe (u : V0Sub.carrier) (n : ℤ) (v : V0Sub.carrier) :
    ((V0P.smul u n v : V0Sub.carrier) : VPlus) = leechVOAPlus.smul u n v := rfl

theorem two_mul_halfNorm (β : leech.carrier) : 2 * LatGen.halfNorm leech β = leech.form β β := by
  obtain ⟨k, hk⟩ := leech_even β
  simp only [LatGen.halfNorm, hk]; omega

theorem form_ge_four {v : leech.carrier} (hv : v ≠ 0) : 4 ≤ leech.form v v := by
  have hpos := leech_posDef v hv
  obtain ⟨k, hk⟩ := leech_even v
  have h2 := leech_no_roots v
  omega

theorem form_add_self (α β : leech.carrier) :
    leech.form (α + β) (α + β) = leech.form α α + 2 * leech.form α β + leech.form β β := by
  have hs : leech.form β α = leech.form α β := IntegralLattice.form_symm leech β α
  simp only [map_add, LinearMap.add_apply, hs]; ring

theorem form_sub_self (α β : leech.carrier) :
    leech.form (α - β) (α - β) = leech.form α α - 2 * leech.form α β + leech.form β β := by
  rw [sub_eq_add_neg, form_add_self, leech_form_neg_right, leech_form_neg_left,
    leech_form_neg_right, neg_neg]; ring

/-- **Ground-state step, `⟨α,β⟩ = -1`.** -/
theorem x0_mem_span_lowerProd_of_form_neg_one {α β : leech.carrier} (hα : α ∈ lambda0)
    (hβ : β ∈ lambda0) (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (h : leech.form α β = -1) :
    x0 (lambda0.add_mem hα hβ) ∈ span ℂ (lowerProd V0P (LatGen.halfNorm leech (α + β))) := by
  have h4α := form_ge_four hα0
  have h4β := form_ge_four hβ0
  have e1 := two_mul_halfNorm α
  have e2 := two_mul_halfNorm β
  have e3 := two_mul_halfNorm (α + β)
  rw [form_add_self, h] at e3
  have hmem : V0P.smul (x0 hα) 0 (x0 hβ) ∈ lowerProd V0P (LatGen.halfNorm leech (α + β)) :=
    ⟨LatGen.halfNorm leech α, LatGen.halfNorm leech β, 0, by omega, by omega, le_rfl, by omega,
      x0 hα, x0_mem_grading hα, x0 hβ, x0_mem_grading hβ, rfl⟩
  have heq : V0P.smul (x0 hα) 0 (x0 hβ) = latticeCocycle leech α β • x0 (lambda0.add_mem hα hβ) := by
    apply Subtype.ext
    rw [V0P_smul_coe]
    exact frameX0P_smul_zero_of_form_neg_one h
  have hsp := subset_span (R := ℂ) hmem
  rw [heq] at hsp
  have := smul_mem _ (latticeCocycle leech α β) hsp
  rwa [smul_smul, latticeCocycle_sq, one_smul] at this

/-- **Ground-state step, `⟨α,β⟩ = 0`.** -/
theorem x0_add_mem_span_lowerProd_of_form_zero {α β : leech.carrier} (hα : α ∈ lambda0)
    (hβ : β ∈ lambda0) (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (h : leech.form α β = 0) :
    x0 (lambda0.add_mem hα hβ) + x0 (lambda0.sub_mem hα hβ)
      ∈ span ℂ (lowerProd V0P (LatGen.halfNorm leech (α + β))) := by
  have h4α := form_ge_four hα0
  have h4β := form_ge_four hβ0
  have e1 := two_mul_halfNorm α
  have e2 := two_mul_halfNorm β
  have e3 := two_mul_halfNorm (α + β)
  rw [form_add_self, h] at e3
  have hmem : V0P.smul (x0 hα) (-1) (x0 hβ) ∈ lowerProd V0P (LatGen.halfNorm leech (α + β)) :=
    ⟨LatGen.halfNorm leech α, LatGen.halfNorm leech β, -1, by omega, by omega, by norm_num, by omega,
      x0 hα, x0_mem_grading hα, x0 hβ, x0_mem_grading hβ, rfl⟩
  have heq : V0P.smul (x0 hα) (-1) (x0 hβ)
      = latticeCocycle leech α β • (x0 (lambda0.add_mem hα hβ) + x0 (lambda0.sub_mem hα hβ)) := by
    apply Subtype.ext
    rw [V0P_smul_coe]
    exact frameX0P_smul_neg_one_of_form_zero h
  have hsp := subset_span (R := ℂ) hmem
  rw [heq] at hsp
  have := smul_mem _ (latticeCocycle leech α β) hsp
  rwa [smul_smul, latticeCocycle_sq, one_smul] at this

end VOA.Moonshine.SigmaExist
