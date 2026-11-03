/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.VerlindeReduction
import VOA.Huang.FusionC2
import VOA.Huang.FusionUnit

/-!
# The Verlinde input with the library's own fusion rules

`VerlindeInput` (`Huang/VerlindeReduction.lean`) quantifies the fusion matrix existentially
(`∃ N : ι → ι → ι → ℕ`).  Huang's theorem says more: the matrix is the matrix of **fusion rules**,
`N_ab^c = dim` of the space of intertwining operators of type `(M_c / M_a M_b)`.  This file states
that sharper form against the library's FHL intertwiners (`Huang/Intertwining.lean`),

* `HuangVerlindeFusionInput` — for a nice `V` and Zhu's `ρ(S)` on a complete irredundant family
  with vacuum label `v0`: `S₀ₓ ≠ 0`, `S₀ₐ = Sₐ₀`, and
  `S_ax S_bx = S₀ₓ Σ_c N_ab^c S_cx` with `N_ab^c = fusionRule (M_a) (M_b) (M_c)`;

and proves

* `verlindeInput_of_fusion : HuangVerlindeFusionInput → VerlindeInput` (take `N := fusionRule`);
* `finiteDimensional_fusion` — under `ModuleC2Input`, every intertwiner space among the
  family is finite-dimensional, so the `N_ab^c` in `HuangVerlindeFusionInput` are true dimensions
  (`fusionRule = finrank` is not the junk value of an infinite-dimensional space);
* `lwOf` — a family member as a lowest-weight module (its conformal weight is a lowest weight);
* `famFusion_vac` — the **unit row** `N_{0b}^c = δ_bc` of the family's fusion rules
  (unconditional: from `Huang/FusionUnit.lean` and irredundancy), and its consistency with the
  Verlinde identity, `verlinde_vac_row` (the `a = 0` instance holds for *any* matrix `S`).

`HuangVerlindeFusionInput` is the Verlinde endpoint; it is TRUE by Huang (2008), *Vertex operator
algebras and the Verlinde
conjecture*, Commun. Contemp. Math. 10, 103–154 (the Verlinde formula `N_a S = S D_a`, together
with `S₀ₓ ≠ 0` and the symmetry of `S`, all proved there), for intertwiners in the sense of
Frenkel–Huang–Lepowsky, which is the
library's `IsIntertwiningOperator`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.VerlindeFusion

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.VerlindeReduction
  VOA.Huang.FusionTop VOA.Huang.FusionC2

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- A member of a modular-data family, as a bundled lowest-weight module. -/
def lwOf {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι) (i : ι) :
    LWModule W where
  carrier := (D.Mfam i).carrier
  isMod := (D.Mfam i).isMod
  h := D.h i
  isLow := (D.hasWeight i).2
  realized := (D.hasWeight i).1

theorem lwOf_irreducible {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)
    (i : ι) : (lwOf D i).IsIrreducibleLW :=
  (D.Mfam i).irreducible

/-- The fusion rule `N_ab^c` of a modular-data family: the dimension of the space of FHL
intertwining operators of type `(M_c / M_a M_b)`. -/
noncomputable def famFusion {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)
    (a b c : ι) : ℕ :=
  fusionRule (D.Mfam a).isMod (D.Mfam b).isMod (D.Mfam c).isMod

/-- **The fusion rules of a nice VOA are honest dimensions** (conditional on `ModuleC2Input`):
every intertwiner space among the family is finite-dimensional. -/
theorem finiteDimensional_fusion (hIn : ModuleC2Input.{u}) (hV : Nice W) {ι : Type w} [Fintype ι]
    [DecidableEq ι] (D : VOA.ModularData W ι) (a b c : ι) :
    FiniteDimensional ℂ
      (intertwiningSpace (D.Mfam a).isMod (D.Mfam b).isMod (D.Mfam c).isMod) :=
  finiteDimensional_intertwiningSpace_nice (P₁ := lwOf D a) (P₂ := lwOf D b) (P₃ := lwOf D c)
    hIn hV (lwOf_irreducible D a) (lwOf_irreducible D b) (lwOf_irreducible D c)

/-- **The unit row of the fusion rules**: `N_{0b}^c = δ_{bc}` for an irredundant family whose
member `v0` is the adjoint module.  Unconditional. -/
theorem famFusion_vac {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)
    (hirr : Irredundant D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (b c : ι) :
    famFusion D v0 b c = if b = c then 1 else 0 := by
  classical
  obtain ⟨e⟩ := hv0
  have h := FusionUnit.fusionRule_adjoint_eq (P₂ := lwOf D b) (P₃ := lwOf D c)
    (lwOf_irreducible D b) (lwOf_irreducible D c)
  change fusionRule (adjointModule W) (D.Mfam b).isMod (D.Mfam c).isMod
    = if Nonempty (ModuleEquiv W (D.Mfam b).isMod (D.Mfam c).isMod) then 1 else 0 at h
  rw [famFusion, FusionUnit.fusionRule_congr_left e, h]
  by_cases hbc : b = c
  · subst hbc
    rw [if_pos ⟨ModuleEquiv.refl _⟩, if_pos rfl]
  · rw [if_neg hbc, if_neg]
    exact fun h => hbc (hirr b c h)

/-- The `a = v0` instance of the Verlinde identity with the true fusion rules holds for every
matrix `S` (a consistency check of `HuangVerlindeFusionInput` against `famFusion_vac`). -/
theorem verlinde_vac_row {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)
    (hirr : Irredundant D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (S : ι → ι → ℂ)
    (b x : ι) : S v0 x * S b x = S v0 x * ∑ c, (famFusion D v0 b c : ℂ) * S c x := by
  congr 1
  simp [famFusion_vac D hirr v0 hv0]

/-- **Huang's Verlinde theorem with the true fusion rules.**  For a nice VOA, Zhu's `ρ(S)` on a
complete irredundant family with vacuum label `v0` has nonvanishing vacuum row, symmetric vacuum
row/column, and is diagonalised by the fusion matrices `N_ab^c = famFusion D a b c`:
`S_ax S_bx = S₀ₓ Σ_c N_ab^c S_cx`.

*Source.* Y.-Z. Huang, Commun. Contemp. Math. 10 (2008) 103–154, main theorem: the Verlinde
formula `N_{ab}^c = Σ_x S_ax S_bx (S⁻¹)_xc / S₀ₓ` (equivalently `N_a S = S D_a`), with `S₀ₓ ≠ 0`
and `S` symmetric, all proved there (theorem numbers not re-checked for this docstring).
The intertwiners there are those of Frenkel–Huang–Lepowsky, i.e.
the library's `IsIntertwiningOperator`, and `N_ab^c` is finite for nice `V`
(`finiteDimensional_fusion`, given `ModuleC2Input`), so `famFusion` is the true dimension. -/
def HuangVerlindeFusionInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        (∀ x, D.repS v0 x ≠ 0) ∧ (∀ a, D.repS v0 a = D.repS a v0) ∧
        ∀ a b x, D.repS a x * D.repS b x
          = D.repS v0 x * ∑ c, (famFusion D a b c : ℂ) * D.repS c x

/-- `HuangVerlindeFusionInput ⟹ VerlindeInput` (the fusion matrix is the witness). -/
theorem verlindeInput_of_fusion (h : HuangVerlindeFusionInput.{u, w}) :
    VerlindeInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0
  obtain ⟨h1, h2, h3⟩ := h 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  exact ⟨h1, h2, ⟨famFusion D, h3⟩⟩

end VOA.Huang.VerlindeFusion
