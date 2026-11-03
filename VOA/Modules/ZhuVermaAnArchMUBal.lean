/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUBalancedPiece
import Mathlib.Algebra.DirectSum.Module

/-!
# The `A(𝒱)`-balanced generalized-Verma carrier `MUBal W U = ⨁ₙ MUPieceBal W U n`

`ZhuVermaAnArchMUBalancedPiece` built the `A(𝒱)`-balanced level-`n` piece
`MUPieceBal W U n = A_{n,0}(𝒱) ⊗_{A(𝒱)} U`.  This file assembles the graded carrier

  `MUBal W U = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U`

— the bimodule-balanced replacement of the ℂ-tensor carrier `MU W U` (`ZhuVermaAnArchMU`),
whose bottom is the genuine Dong–Jiang `M(U)(0) ≅ U` (`muPieceBal0EquivU`) rather than the strictly
larger ℂ-tensor `A(𝒱) ⊗_ℂ U`.  The graded structure mirrors `MU` exactly.

## Contents (axiom-clean, pbw-free)

* **`MUBal W U := ⨁ n, MUPieceBal W U n`** — the balanced graded carrier, with the canonical
  `DirectSum` `AddCommGroup`/`Module ℂ`.
* **`MUBal.incl`/`MUBal.proj`** — the level-`n` inclusion/projection (`proj_incl_same`/`proj_incl_ne`).
* **`MUBal.deg n := range (MUBal.incl … n)`** — the `ℕ`-grading `MUBal = ⊕ₙ MUBal(n)`.
* **`MUBal.isInternal_deg`** — the grading is a genuine internal direct-sum decomposition
  (`DirectSum.IsInternal`), mirroring `MU.isInternal_deg`.

`#print axioms` on every headline term is `[propext, Classical.choice, Quot.sound]`.  pbw-free.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Thm 4.13; Dong–Li–Mason III §4; Gannon §5.3.2.
Cross-ref `ZhuVermaAnArchMU` (the ℂ-tensor analogue `MU`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The balanced graded carrier `MUBal W U = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U` -/

/-- **The `A(𝒱)`-balanced Dong–Jiang induced-module carrier** `MUBal W U = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U`
(bimodule balancing; DJ Construction B / Thm 4.13).  The `ℕ`-grading is the level `n`; the bottom (`n = 0`) is the
genuine `M(U)(0) ≅ U`.  Carries the canonical `DirectSum` `AddCommGroup`/`Module ℂ`. -/
abbrev MUBal (W : VertexOperatorAlgebra 𝒱) (U : AMod W) : Type u :=
  ⨁ n : ℕ, MUPieceBal W U n

/-- The canonical inclusion of the balanced level-`n` piece into `MUBal W U`. -/
noncomputable def MUBal.incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MUPieceBal W U n →ₗ[ℂ] MUBal W U :=
  DirectSum.lof ℂ ℕ (MUPieceBal W U) n

/-- The canonical projection of `MUBal W U` onto the balanced level-`n` piece. -/
noncomputable def MUBal.proj (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MUBal W U →ₗ[ℂ] MUPieceBal W U n :=
  DirectSum.component ℂ ℕ (MUPieceBal W U) n

@[simp] theorem MUBal.proj_incl_same (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    (x : MUPieceBal W U n) : MUBal.proj W U n (MUBal.incl W U n x) = x :=
  DirectSum.component.lof_self ℂ n x

theorem MUBal.proj_incl_ne (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {n k : ℕ} (h : n ≠ k)
    (x : MUPieceBal W U k) : MUBal.proj W U n (MUBal.incl W U k x) = 0 := by
  rw [MUBal.proj, MUBal.incl, DirectSum.component.of]
  exact dif_neg (Ne.symm h)

/-! ## The `ℕ`-grading of `MUBal W U` is an internal direct sum -/

/-- The balanced level-`n` graded subspace of `MUBal W U`: the range of `MUBal.incl … n`.
This is the DJ grading `M(U) = ⊕ₙ M(U)(n)` on the balanced carrier. -/
noncomputable def MUBal.deg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    Submodule ℂ (MUBal W U) := LinearMap.range (MUBal.incl W U n)

/-- **The `ℕ`-grading of `MUBal W U` is a genuine internal direct-sum decomposition.**
The DJ statement `M(U) = ⊕ₙ M(U)(n)` (`DirectSum.IsInternal`) on the `A(𝒱)`-balanced carrier,
mirroring `MU.isInternal_deg`. -/
theorem MUBal.isInternal_deg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    DirectSum.IsInternal (MUBal.deg W U) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hproj_sup : ∀ (n : ℕ) (z : MUBal W U),
      z ∈ (⨆ (j : ℕ) (_ : j ≠ n), MUBal.deg W U j) → MUBal.proj W U n z = 0 := by
    intro n z hz
    refine Submodule.iSup_induction _ (motive := fun w => MUBal.proj W U n w = 0) hz
      ?_ (map_zero _) (fun a b ha hb => by simp only [map_add, ha, hb, add_zero])
    intro j z hjz
    refine Submodule.iSup_induction _ (motive := fun w => MUBal.proj W U n w = 0) hjz
      ?_ (map_zero _) (fun a b ha hb => by simp only [map_add, ha, hb, add_zero])
    intro hjn w hw
    obtain ⟨v, rfl⟩ := hw
    exact MUBal.proj_incl_ne W U (Ne.symm hjn) v
  constructor
  · refine iSupIndep_def.mpr (fun n => ?_)
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    rintro x ⟨⟨y, rfl⟩, hxsup⟩
    rw [Submodule.mem_bot]
    have h0 : MUBal.proj W U n (MUBal.incl W U n y) = 0 := hproj_sup n _ hxsup
    rw [MUBal.proj_incl_same] at h0
    rw [h0, map_zero]
  · rw [eq_top_iff]
    intro x _
    refine DirectSum.induction_on x (Submodule.zero_mem _) ?_
      (fun a b ha hb => Submodule.add_mem _ ha hb)
    intro n y
    exact Submodule.mem_iSup_of_mem n ⟨y, rfl⟩

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
