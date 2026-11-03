/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FrameSectors
import VOA.Moonshine.CyclicVacuumTrick

/-!
# The untwisted frame sectors are cyclic `V₀⁺`-modules  (Moonshine step M8f, untwisted half)

Recall (`Moonshine/FrameSectors.lean`) `V_Λ⁺ = V₀⁺ ⊕ V₃⁺`, `V₀⁺ = frameSector 0` (θ-fixed states with
momenta in `Λ₀ = ker β`), `V₃⁺ = frameSector 1` (θ-fixed states with momenta in `Λ \ Λ₀`), and
`V_i·V_j ⊆ V_{i+j}` (`frameSector_smul_mem`).  We prove that each is a **cyclic** `V₀⁺`-module:

* `cyclic_V0` — with `x₀ = 𝟙`: `span {u₍ₙ₎𝟙 | u ∈ V₀⁺} = V₀⁺` (trivial: `u = u₍₋₁₎𝟙`);
* `cyclic_V3` — with `x₀ = e^β + e^{-β}` for any `β ∈ Λ \ Λ₀`:
  `span {u₍ₙ₎x₀ | u ∈ V₀⁺, n ∈ ℤ} = V₃⁺`.

## The proof of `cyclic_V3` (no Fock-space bookkeeping)

Let `N = ⟨β,β⟩ > 0` (`N` even).  From the lattice vertex operator
`Y(e^α,z)e^γ = ε(α,γ) z^{⟨α,γ⟩} E⁻(-α,z) e^{α+γ}` (`Yeαvec_tmul`, `EEVec_vacuum`):

* `e^{±β}₍ⱼ₎ e^{±β} = 0` for `j ≥ -N`;
* `e^{±β}₍ⱼ₎ e^{∓β} = 0` for `j ≥ N`, and `e^{±β}₍N₋₁₎ e^{∓β} = ε(±β,∓β)·𝟙`.

Hence `x₀₍N₋₁₎x₀ = (ε(β,-β) + ε(-β,β))·𝟙 = 2ε(β,-β)·𝟙 ≠ 0` (the cocycle commutator is
`(-1)^{⟨β,-β⟩} = 1`, `latticeCocycle_swap_sign`), and `x₀₍ⱼ₎x₀ = 0` for `j ≥ N`.  The general vacuum
trick `VertexOperatorAlgebra.mem_span_iterate_of_vacuum` (Borcherds identity) then writes every
`v ∈ V₃⁺` as a combination of `(v₍ᵢ₎x₀)₍ⱼ₎x₀`, and `v₍ᵢ₎x₀ ∈ V₃⁺·V₃⁺ ⊆ V₀⁺`.  The reverse inclusion is
`V₀⁺·V₃⁺ ⊆ V₃⁺`.  This avoids DGM's Virasoro-field argument entirely: cyclicity (not
irreducibility) only needs one vector pairing to the vacuum.

## Main results
* `Moonshine.leechVOA_Y_latChargeGen`, `leechVOA_smul_latChargeGen_eq_zero`,
  `leechVOA_smul_latChargeGen_neg` — the three lattice inputs.
* `Moonshine.exists_not_mem_lambda0` — `Λ₀ ≠ Λ`.
* `Moonshine.frameX0`, `frameX0_mem_frameSector_one`, `frameX0_smul_top`, `frameX0_smul_above`.
* `Moonshine.cyclic_V0`, `Moonshine.cyclic_V3`, and the explicit-vector form
  `Moonshine.span_smul_frameX0`.

## Status
`sorry`-free; `#print axioms cyclic_V3 = [propext, Classical.choice, Quot.sound]` (no `VOA.pbw`).
Unconditional.  **Not done:** irreducibility of `V₃⁺` (FLM / DGM Prop. 7.1 — every nonzero vector is
cyclic; it would need a nondegenerate invariant form on `V₃⁺` to produce, for each nonzero `x`, a
partner `y` with `y₍ₖ₎x ∈ ℂ^×𝟙`); the twisted sectors `T₀⁺`, `T₃⁺` (they need M8a); the closure of
the span under further `V₀⁺`-modes is not stated (not needed: the span is already all of `V₃⁺`).
Imported by the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine

open LatGen IntegralLattice HeisenbergN

/-! ## §1  Lattice inputs in `V_Λ` -/

theorem leech_form_neg_left (a b : leech.carrier) : leech.form (-a) b = -leech.form a b :=
  LinearMap.map_neg₂ _ _ _

theorem leech_form_neg_right (a b : leech.carrier) : leech.form a (-b) = -leech.form a b :=
  map_neg _ _

theorem leechVOA_Y_latChargeGen (α : leech.carrier) :
    leechVOA.Y (latChargeGen leech α) = Yeαvec leech α := by
  have hw := YfullGen_word leech leech_even leech_posDef [] α
  rw [wordStateLatGen_nil, YwordLatGen_nil] at hw
  exact hw

/-- `e^α₍ₙ₎ e^γ = 0` for `n ≥ -⟨α,γ⟩`. -/
theorem leechVOA_smul_latChargeGen_eq_zero (α γ : leech.carrier) {n : ℤ}
    (hn : -leech.form α γ ≤ n) :
    leechVOA.smul (latChargeGen leech α) n (latChargeGen leech γ) = 0 := by
  rw [PreVertexAlgebra.smul_def, leechVOA_Y_latChargeGen, mode_apply]
  rw [show latChargeGen leech γ = latStateGen leech (vacuumN (rank leech)) γ from rfl, Yeαvec_tmul]
  have h : EEVec leech α (-n - 1 - leech.form α γ) (vacuumN (rank leech)) = 0 := by
    rw [EEVec_vacuum, if_neg (by omega)]
  rw [h, latStateGen, TensorProduct.zero_tmul, smul_zero]

/-- `e^α₍⟨α,α⟩₋₁₎ e^{-α} = ε(α,-α)·𝟙`. -/
theorem leechVOA_smul_latChargeGen_neg (α : leech.carrier) :
    leechVOA.smul (latChargeGen leech α) (leech.form α α - 1) (latChargeGen leech (-α))
      = latticeCocycle leech α (-α) • latVacuumGen leech := by
  rw [PreVertexAlgebra.smul_def, leechVOA_Y_latChargeGen, mode_apply]
  rw [show latChargeGen leech (-α) = latStateGen leech (vacuumN (rank leech)) (-α) from rfl,
    Yeαvec_tmul]
  have h0 : -(leech.form α α - 1) - 1 - leech.form α (-α) = 0 := by
    rw [leech_form_neg_right]; ring
  rw [h0, EEVec_vacuum, if_pos le_rfl, show (0 : ℤ).toNat = 0 from rfl, vSchur_zero,
    add_neg_cancel]
  rfl

/-- `Λ₀ ≠ Λ`. -/
theorem exists_not_mem_lambda0 : ∃ β : leech.carrier, β ∉ lambda0 := by
  by_contra h
  push Not at h
  have htop : lambda0 = ⊤ := eq_top_iff.mpr (fun x _ => h x)
  have hc := card_quotient_lambda0
  rw [htop] at hc
  simp at hc

/-! ## §2  The cyclic vector `x₀ = e^β + e^{-β}` -/

/-- The candidate cyclic vector `e^β + e^{-β}` of `V₃⁺`. -/
noncomputable def frameX0 (β : leech.carrier) : LatModuleGen leech :=
  latChargeGen leech β + latChargeGen leech (-β)

theorem frameX0_mem_plus (β : leech.carrier) :
    frameX0 β ∈ (orbifold (Subgroup.zpowers leechTheta)).carrier := by
  rw [mem_leechVOAPlus_iff, frameX0, map_add, thetaLat_latChargeGen, thetaLat_latChargeGen,
    neg_neg, add_comm]

/-- `x₀` as an element of `V_Λ⁺`. -/
noncomputable def frameX0P (β : leech.carrier) : VPlus := ⟨frameX0 β, frameX0_mem_plus β⟩

open Classical in
theorem coordEα_latChargeGen (α γ : leech.carrier) :
    coordEα leech α (latChargeGen leech γ) = if α = γ then vacuumN (rank leech) else 0 :=
  coordEα_apply leech α γ _

theorem frameX0_mem_frameSector_one {β : leech.carrier} (hβ : β ∉ lambda0) :
    frameX0P β ∈ frameSector 1 := by
  rw [mem_frameSector_one_iff]
  intro α hα
  have h1 : α ≠ β := fun h => hβ (h ▸ hα)
  have h2 : α ≠ -β := fun h => hβ (by rw [← neg_neg β, ← h]; exact lambda0.neg_mem hα)
  change coordEα leech α (frameX0 β) = 0
  rw [frameX0, map_add, coordEα_latChargeGen, coordEα_latChargeGen, if_neg h1, if_neg h2,
    add_zero]

/-- `x₀₍ⱼ₎x₀ = 0` for `j ≥ ⟨β,β⟩`. -/
theorem frameX0_smul_above (β : leech.carrier) {j : ℤ} (hj : leech.form β β ≤ j) :
    leechVOA.smul (frameX0 β) j (frameX0 β) = 0 := by
  have hpos : 0 ≤ leech.form β β := by
    by_cases h : β = 0
    · rw [h]; simp
    · exact (leech_posDef β h).le
  rw [frameX0, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_add_right,
    leechVOA_smul_latChargeGen_eq_zero β β (by omega),
    leechVOA_smul_latChargeGen_eq_zero β (-β) (by rw [leech_form_neg_right]; omega),
    leechVOA_smul_latChargeGen_eq_zero (-β) β (by rw [leech_form_neg_left]; omega),
    leechVOA_smul_latChargeGen_eq_zero (-β) (-β)
      (by rw [leech_form_neg_left, leech_form_neg_right, neg_neg]; omega)]
  simp

/-- `x₀₍⟨β,β⟩₋₁₎x₀ = (ε(β,-β) + ε(-β,β))·𝟙`. -/
theorem frameX0_smul_top {β : leech.carrier} (hβ : β ≠ 0) :
    leechVOA.smul (frameX0 β) (leech.form β β - 1) (frameX0 β)
      = (latticeCocycle leech β (-β) + latticeCocycle leech (-β) β) • latVacuumGen leech := by
  have hpos : 0 < leech.form β β := leech_posDef β hβ
  have hn := leechVOA_smul_latChargeGen_neg (-β)
  rw [neg_neg, leech_form_neg_left, leech_form_neg_right, neg_neg] at hn
  rw [frameX0, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_add_right,
    leechVOA_smul_latChargeGen_eq_zero β β (by omega), leechVOA_smul_latChargeGen_neg β, hn,
    leechVOA_smul_latChargeGen_eq_zero (-β) (-β)
      (by rw [leech_form_neg_left, leech_form_neg_right, neg_neg]; omega), add_smul]
  simp

/-- The pairing scalar `ε(β,-β) + ε(-β,β) = 2ε(-β,β)` is non-zero. -/
theorem frameX0_scalar_ne_zero (β : leech.carrier) :
    latticeCocycle leech β (-β) + latticeCocycle leech (-β) β ≠ 0 := by
  have hsw := latticeCocycle_swap_sign leech leech_even β (-β)
  have hev : Even (leech.form β (-β)) := by
    obtain ⟨k, hk⟩ := leech_even β
    exact ⟨-k, by rw [leech_form_neg_right, hk]; ring⟩
  rw [hev.neg_one_zpow, one_mul] at hsw
  rw [hsw, ← two_mul]
  have hsq := latticeCocycle_sq leech (-β) β
  intro h
  rcases mul_eq_zero.mp h with h | h
  · norm_num at h
  · rw [h, mul_zero] at hsq; exact zero_ne_one hsq

/-! ## §3  Cyclicity -/

theorem plus_smul_coe (u : VPlus) (n : ℤ) (v : VPlus) :
    ((leechVOAPlus.smul u n v : VPlus) : LatModuleGen leech) = leechVOA.smul u n v := rfl

theorem plus_vacuum_coe :
    ((leechVOAPlus.vacuum : VPlus) : LatModuleGen leech) = latVacuumGen leech := rfl

theorem vacuum_mem_frameSector_zero : leechVOAPlus.vacuum ∈ frameSector 0 := by
  rw [← V0Sub_carrier]; exact V0Sub.vacuum_mem

/-- **`V₀⁺` is cyclic over itself**, generated by `𝟙`. -/
theorem cyclic_V0 : ∃ x₀ ∈ frameSector 0,
    Submodule.span ℂ {y | ∃ u ∈ frameSector 0, ∃ n : ℤ, y = leechVOAPlus.smul u n x₀}
      = frameSector 0 := by
  refine ⟨leechVOAPlus.vacuum, vacuum_mem_frameSector_zero, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro y ⟨u, hu, n, rfl⟩
    have := frameSector_smul_mem hu vacuum_mem_frameSector_zero n
    rwa [add_zero] at this
  · intro v hv
    refine Submodule.subset_span ⟨v, hv, -1, ?_⟩
    exact (PreVertexAlgebra.smul_vacuum_neg_one _ v).symm

/-- **`V₃⁺` is a cyclic `V₀⁺`-module**, generated by `x₀ = e^β + e^{-β}` for any `β ∈ Λ \ Λ₀`. -/
theorem span_smul_frameX0 {β : leech.carrier} (hβ : β ∉ lambda0) :
    Submodule.span ℂ {y | ∃ u ∈ frameSector 0, ∃ n : ℤ, y = leechVOAPlus.smul u n (frameX0P β)}
      = frameSector 1 := by
  have hX := frameX0_mem_frameSector_one hβ
  have hβ0 : β ≠ 0 := fun h => hβ (h ▸ lambda0.zero_mem)
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro y ⟨u, hu, n, rfl⟩
    have := frameSector_smul_mem hu hX n
    rwa [zero_add] at this
  · intro v hv
    have hk : leechVOAPlus.smul (frameX0P β) (leech.form β β - 1) (frameX0P β)
        = (latticeCocycle leech β (-β) + latticeCocycle leech (-β) β) • leechVOAPlus.vacuum :=
      Subtype.ext (by rw [plus_smul_coe, Submodule.coe_smul, plus_vacuum_coe]; exact frameX0_smul_top hβ0)
    have hk' : ∀ j : ℤ, leech.form β β - 1 < j →
        leechVOAPlus.smul (frameX0P β) j (frameX0P β) = 0 := fun j hj =>
      Subtype.ext (by rw [plus_smul_coe]; exact frameX0_smul_above β (by omega))
    have hmem := VertexOperatorAlgebra.mem_span_iterate_of_vacuum leechVOAPlus
      (frameX0_scalar_ne_zero β) hk hk' v
    refine Submodule.span_mono ?_ hmem
    rintro y ⟨i, j, rfl⟩
    have hvi := frameSector_smul_mem hv hX i
    rw [show (1 : ZMod 2) + 1 = 0 from rfl] at hvi
    exact ⟨_, hvi, j, rfl⟩

/-- **M8f, untwisted half: `V₃⁺` is a cyclic `V₀⁺`-module.** -/
theorem cyclic_V3 : ∃ x₀ ∈ frameSector 1,
    Submodule.span ℂ {y | ∃ u ∈ frameSector 0, ∃ n : ℤ, y = leechVOAPlus.smul u n x₀}
      = frameSector 1 := by
  obtain ⟨β, hβ⟩ := exists_not_mem_lambda0
  exact ⟨frameX0P β, frameX0_mem_frameSector_one hβ, span_smul_frameX0 hβ⟩

end VOA.Moonshine
