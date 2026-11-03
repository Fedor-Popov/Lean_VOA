/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenOppLocal

/-!
# Lattice reconstruction inputs (general even positive-definite `L`)

The generating-field/field-property inputs the operator-first reconstruction
(`Reconstruction.reconstruct`) consumes, for the general even positive-definite lattice VOA
`V_L = FockN(rank L) ⊗ ℂ_ε{L}`.  The cross-charge lift of A₁'s `LatticeWordFields`.

Banked here:
* `Yeαvec_isField` — the charge-`α` lattice vertex operator `Y(e^α,z)` is a field (lower-truncated
  on every basis state `p ⊗ e^β` by the boson dressing `EEVec_isField`, shifted by `⟨α,β⟩`).

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice)

/-- **The charged lattice vertex operator is a field** (`IsField (Yeαvec L α)`): on `p ⊗ e^β` the
cocycle-twisted sector shift `t ↦ t - ⟨α,β⟩` lower-truncates via `EEVec_isField`; the bound over a
general tensor is the min across its finitely many lattice sectors.  Cross-charge lift of A₁'s
`Yemα_isField`. -/
theorem Yeαvec_isField (α : L.carrier) : IsField (Yeαvec L α) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => (Yeαvec L α n).map_zero⟩
  | add x y hx hy =>
      obtain ⟨Bx, hBx⟩ := hx
      obtain ⟨By, hBy⟩ := hy
      refine ⟨min Bx By, fun n hn => ?_⟩
      rw [map_add (Yeαvec L α n) x y, hBx n (lt_of_lt_of_le hn (min_le_left _ _)),
        hBy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => exact ⟨0, fun n _ => by erw [TensorProduct.tmul_zero]; exact (Yeαvec L α n).map_zero⟩
      | add g1 g2 h1 h2 =>
          obtain ⟨B1, hB1⟩ := h1
          obtain ⟨B2, hB2⟩ := h2
          refine ⟨min B1 B2, fun n hn => ?_⟩
          erw [TensorProduct.tmul_add]
          simp only [map_add]
          rw [hB1 n (lt_of_lt_of_le hn (min_le_left _ _)),
            hB2 n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
      | single β a =>
          obtain ⟨Bp, hBp⟩ := EEVec_isField L α p
          refine ⟨Bp + L.form α β, fun n hn => ?_⟩
          rw [(Finsupp.smul_single_one β a).symm,
            show (Finsupp.single β (1 : ℂ) : L.carrier →₀ ℂ) = eGen L β from rfl]
          erw [TensorProduct.tmul_smul, map_smul,
            show p ⊗ₜ[ℂ] eGen L β = latStateGen L p β from rfl, Yeαvec_tmul,
            hBp (n - L.form α β) (by omega), latStateGen, TensorProduct.zero_tmul,
            smul_zero]

end VOA.LatGen
