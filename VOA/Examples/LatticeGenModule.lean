/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Foundations.LatticeAlgebraTwisted
import VOA.Examples.HeisenbergNVertex

/-!
# The general lattice VOA module `V_L = FockN(rank L) ⊗ ℂ_ε{L}`  (FLM Ch. 8; Gannon §5.2.2)

The state space of the lattice VOA for an arbitrary even positive-definite lattice `L`, generalizing
the `A₁` module `LatModule = FockN 1 ⊗ ℂ{ℤ}` (`Examples.LatticeA1`) to rank `= L.rank`.  The charge
factor is the group algebra `ℂ{L} = L.carrier →₀ ℂ` **as a vector space**; the FLM cocycle `ε`
(`Foundations.LatticeCocycle` / `Foundations.LatticeAlgebraTwisted`) enters only in the *operators*
`Y(e^α)`, not the module structure.

This file defines the module type and its distinguished vectors (vacuum, charged states); the
grading, vertex operators, locality and reconstruction are built in the other `LatticeGen*`
modules.

## References
* Frenkel–Lepowsky–Meurman, *Vertex Operator Algebras and the Monster*, Ch. 8; Gannon §5.2.2.
-/

namespace VOA.LatGen

open scoped TensorProduct
open VOA VOA.IntegralLattice

variable (L : IntegralLattice)

/-- The **general lattice VOA module** `V_L = FockN(rank L) ⊗_ℂ ℂ{L}` (FLM Ch. 8).  The rank-`L.rank`
free-boson Fock space tensored with the (vector space underlying the) lattice group algebra. -/
noncomputable abbrev LatModuleGen : Type :=
  HeisenbergN.FockN (rank L) ⊗[ℂ] (L.carrier →₀ ℂ)

/-- The charge-`α` basis vector `e^α ∈ ℂ{L}`. -/
noncomputable def eGen (α : L.carrier) : L.carrier →₀ ℂ := Finsupp.single α 1

/-- The lattice state `p ⊗ e^α` (boson state `p` in charge sector `α`). -/
noncomputable def latStateGen (p : HeisenbergN.FockN (rank L)) (α : L.carrier) : LatModuleGen L :=
  p ⊗ₜ[ℂ] eGen L α

/-- The **vacuum** `|0⟩ = 𝟙_boson ⊗ e^0`. -/
noncomputable def latVacuumGen : LatModuleGen L :=
  latStateGen L (HeisenbergN.vacuumN (rank L)) 0

/-- The **charged vacuum** `e^α = 𝟙_boson ⊗ e^α` (the lowest state of the charge-`α` sector,
conformal weight `½⟨α,α⟩`). -/
noncomputable def latChargeGen (α : L.carrier) : LatModuleGen L :=
  latStateGen L (HeisenbergN.vacuumN (rank L)) α

@[simp] theorem latChargeGen_zero : latChargeGen L 0 = latVacuumGen L := rfl

/-- `latStateGen` is additive in the boson slot. -/
theorem latStateGen_add_boson (p q : HeisenbergN.FockN (rank L)) (α : L.carrier) :
    latStateGen L (p + q) α = latStateGen L p α + latStateGen L q α := by
  simp only [latStateGen, TensorProduct.add_tmul]

/-- `latStateGen` is `ℂ`-linear in the boson slot. -/
theorem latStateGen_smul_boson (c : ℂ) (p : HeisenbergN.FockN (rank L)) (α : L.carrier) :
    latStateGen L (c • p) α = c • latStateGen L p α := by
  rw [latStateGen, latStateGen, TensorProduct.smul_tmul']

/-- The charged states `latStateGen p α` (over all `p, α`) **span** `V_L`: the tensor product of the
spanning boson states with the `e^α`-basis of `ℂ{L}` (`TensorProduct.span_tmul_eq_top`), the
generating family for the operator-first reconstruction. -/
theorem latStateGen_span :
    Submodule.span ℂ (Set.range (fun q : HeisenbergN.FockN (rank L) × L.carrier =>
      latStateGen L q.1 q.2)) = ⊤ := by
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top ℂ (HeisenbergN.FockN (rank L)) (L.carrier →₀ ℂ),
    Submodule.span_le]
  rintro _ ⟨p, g, rfl⟩
  -- every simple tensor p ⊗ g is a finite ℂ-combination of p ⊗ e^α (e^α the Finsupp basis)
  induction g using Finsupp.induction_linear with
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add g₁ g₂ h₁ h₂ =>
      rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h₁ h₂
  | single α c =>
      rw [show (Finsupp.single α c : L.carrier →₀ ℂ) = c • eGen L α from by
            rw [eGen, Finsupp.smul_single, smul_eq_mul, mul_one], TensorProduct.tmul_smul]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨⟨p, α⟩, rfl⟩)

end VOA.LatGen
