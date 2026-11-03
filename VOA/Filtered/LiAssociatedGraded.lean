/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.FiniteAssociatedGraded
import VOA.Modularity.LiFiltration
import VOA.Modularity.BuhlSpanningData

/-!
# Li filtration slices and exact layers

This file keeps the Li filtration instantiation deliberately small:

* the adjoint Li filtration `liFiltration`;
* its fixed-weight slices `liWeightPiece`;
* the exact layer `liWeightLayer` obtained via `Submodule.Layer`;
* a few immediate facts: monotonicity, the degree-zero slice under the exact
  lowest-weight-generation hypothesis, vanishing above weight, and finite-rank
  additivity both layerwise and after telescoping.

No associated-graded multiplication is defined here.
-/

namespace VOA

open scoped BigOperators
open Module (finrank)

universe u

section LiAssociatedGraded

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The adjoint Li filtration on the VOA itself. -/
def liFiltration (W : VertexOperatorAlgebra 𝒱) (p : ℕ) : Submodule ℂ 𝒱 :=
  Gfil (adjointModule W).toWeakModule ({W.vacuum} : Set 𝒱) (p : ℤ)

/-- The fixed-weight slice of the Li filtration. -/
def liWeightPiece (W : VertexOperatorAlgebra 𝒱) (p N : ℕ) : Submodule ℂ 𝒱 :=
  liFiltration W p ⊓ W.grading N

/-- The degree-zero Li slice is the full weight space. Lowest-weight generation of the adjoint
module by the vacuum holds for every VOA (`lwGenerated_adjoint`: `u = u₍₋₁₎𝟙`), so it is not a
hypothesis; an earlier version carried it as the redundant hypothesis `hLW` (register entry 54). -/
theorem liWeightPiece_zero_eq_grading (W : VertexOperatorAlgebra 𝒱) (N : ℕ) :
    liWeightPiece W 0 N = W.grading N := by
  change Gfil (adjointWeakModule W) ({W.vacuum} : Set 𝒱) 0 ⊓ W.grading N = W.grading N
  rw [lwGenerated_adjoint W, top_inf_eq]

/-- The fixed-weight Li slices are decreasing in the filtration index. -/
theorem liWeightPiece_antitone (W : VertexOperatorAlgebra 𝒱) (N : ℕ) {p q : ℕ} (hpq : p ≤ q) :
    liWeightPiece W q N ≤ liWeightPiece W p N := by
  dsimp [liWeightPiece, liFiltration]
  exact inf_le_inf_right _ (Gfil_antitone (adjointWeakModule W) ({W.vacuum} : Set 𝒱)
    (by exact_mod_cast hpq))

/-- The exact layer between consecutive fixed-weight Li slices. -/
abbrev liWeightLayer (W : VertexOperatorAlgebra 𝒱) (p N : ℕ) : Type _ :=
  Submodule.Layer (P := liWeightPiece W p N) (Q := liWeightPiece W (p + 1) N)
    (liWeightPiece_antitone (W := W) (N := N) (Nat.le_succ p))

/-- A fixed-weight Li slice is finite-dimensional because it sits inside one graded piece. -/
theorem liWeightPiece_finiteDimensional (W : VertexOperatorAlgebra 𝒱) (p N : ℕ) :
    FiniteDimensional ℂ (liWeightPiece W p N) := by
  haveI : FiniteDimensional ℂ (W.grading N) := W.finrank N
  exact Submodule.finiteDimensional_of_le (S₁ := liWeightPiece W p N)
    (S₂ := W.grading N) (inf_le_right : liWeightPiece W p N ≤ W.grading N)

/-- Above the weight, the Li filtration misses the fixed weight space. -/
theorem liWeightPiece_eq_bot_of_lt (W : VertexOperatorAlgebra 𝒱) {p N : ℕ} (h : N < p) :
    liWeightPiece W p N = ⊥ := by
  have hB : ∀ w ∈ ({W.vacuum} : Set 𝒱), ∃ d₀ : ℕ, w ∈ (adjointModule W).weight (0 + d₀) := by
    intro w hw
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    refine ⟨0, ?_⟩
    have hvac : W.vacuum ∈ adjWeight W ((0 : ℤ) : ℂ) := by
      have hcast : adjWeight W ((0 : ℤ) : ℂ) = W.grading 0 := adjWeight_cast W 0
      exact hcast.symm ▸ (W.vacuum_mem_grading_zero : W.vacuum ∈ W.grading 0)
    simpa [adjointModule] using hvac
  have hbot := Gfil_inf_weight_eq_bot (adjointModule W) ({W.vacuum} : Set 𝒱) 0 hB
    (p := p) (d := N) h
  dsimp [adjointModule] at hbot
  have hzeroN : (0 : ℂ) + (N : ℂ) = (N : ℂ) := by ring
  rw [hzeroN] at hbot
  have hNcast : ((N : ℕ) : ℂ) = ((N : ℤ) : ℂ) := by norm_num
  rw [hNcast] at hbot
  rw [adjWeight_cast W N] at hbot
  simpa [liWeightPiece, liFiltration, adjointModule] using hbot

/-- The exact layer between consecutive fixed-weight Li pieces is finite-dimensional and has the
expected rank additivity. -/
theorem liWeightLayer_finrank_add_finrank (W : VertexOperatorAlgebra 𝒱) (p N : ℕ) :
    Module.finrank ℂ (liWeightLayer W p N) +
      Module.finrank ℂ (liWeightPiece W (p + 1) N) =
      Module.finrank ℂ (liWeightPiece W p N) := by
  haveI : FiniteDimensional ℂ (liWeightPiece W p N) :=
    liWeightPiece_finiteDimensional W p N
  simpa [liWeightLayer] using
    (Submodule.Layer.finrank_layer_add_finrank
      (P := liWeightPiece W p N) (Q := liWeightPiece W (p + 1) N)
      (h := liWeightPiece_antitone W N (Nat.le_succ p)))

/-- The finite telescope through filtration indices `0, ..., m - 1`.  This version does not use
lowest-weight generation or bottom vanishing, and records the surviving degree-`m` slice. -/
theorem sum_liWeightLayer_finrank_add_finrank (W : VertexOperatorAlgebra 𝒱) (N m : ℕ) :
    (∑ p ∈ Finset.range m, Module.finrank ℂ (liWeightLayer W p N)) +
      Module.finrank ℂ (liWeightPiece W m N) =
      Module.finrank ℂ (liWeightPiece W 0 N) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hstep := liWeightLayer_finrank_add_finrank W m N
      omega

/-- In fixed conformal weight `N`, the exact Li layers in degrees `0, ..., N` exhaust the full
weight space.  The upper endpoint uses fixed-weight vanishing, the lower endpoint
`liWeightPiece_zero_eq_grading`.  No lowest-weight-generation hypothesis is needed (an earlier
version carried the redundant `hLW`; register entry 54). -/
theorem sum_liWeightLayer_finrank_eq_grading (W : VertexOperatorAlgebra 𝒱) (N : ℕ) :
    (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (liWeightLayer W p N)) =
      Module.finrank ℂ (W.grading N) := by
  have htel := sum_liWeightLayer_finrank_add_finrank W N (N + 1)
  rw [liWeightPiece_eq_bot_of_lt W (Nat.lt_succ_self N), finrank_bot, add_zero,
    liWeightPiece_zero_eq_grading W N] at htel
  exact htel

end LiAssociatedGraded

end VOA
