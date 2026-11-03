/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.BetaGammaInstance
import VOA.Core.SuperAutomorphism
import VOA.Modularity.GammaThetaStatement

/-!
# Reducing beta--gamma C2 detectors to creation words

The beta--gamma creation states `stWordBG l` span the full Fock space.  Since every vertex-algebra
mode is bilinear, a linear detector annihilates every `(-2)` product as soon as it annihilates the
products of two creation words.  This file packages that span argument independently of any
particular detector.

In particular, the second theorem upgrades the word-pair check directly to containment of the
super `C₂` subspace in the detector's kernel.  It does not assert that a particular detector
satisfies the word-pair hypothesis.
-/

namespace VOA.BGInst

open VOA
open VOA.BetaGamma
open VOA.GammaThetaStmt

noncomputable section

variable {M : Type*} [AddCommMonoid M] [Module ℂ M]

/-- A linear detector annihilates every beta--gamma `(-2)` product if it annihilates the products
of all pairs of creation words. -/
theorem linearMap_smul_neg_two_eq_zero_of_words (D : Fock →ₗ[ℂ] M)
    (hword : ∀ l₁ l₂ : BGWord,
      D (bgSVOA.smul (stWordBG l₁) (-2) (stWordBG l₂)) = 0)
    (u v : Fock) : D (bgSVOA.smul u (-2) v) = 0 := by
  have hright : ∀ (l₁ : BGWord) (v : Fock),
      D (bgSVOA.smul (stWordBG l₁) (-2) v) = 0 := by
    intro l₁ v
    have hv : v ∈ Submodule.span ℂ (Set.range stWordBG) := by
      rw [stWordBG_span]
      exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun v _ => D (bgSVOA.smul (stWordBG l₁) (-2) v) = 0)
      ?_ ?_ ?_ ?_ hv
    · intro x hx
      obtain ⟨l₂, rfl⟩ := hx
      exact hword l₁ l₂
    · have hz := bgSVOA.smul_smul_right (stWordBG l₁) (0 : ℂ) (-2) (1 : Fock)
      simpa using congrArg D hz
    · intro x y _ _ hx hy
      simp only [SuperVertexAlgebra.smul_add_right, map_add, hx, hy, add_zero]
    · intro c x _ hx
      simp only [SuperVertexAlgebra.smul_smul_right, map_smul, hx, smul_zero]
  have hu : u ∈ Submodule.span ℂ (Set.range stWordBG) := by
    rw [stWordBG_span]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun u _ => D (bgSVOA.smul u (-2) v) = 0)
    ?_ ?_ ?_ ?_ hu
  · intro x hx
    obtain ⟨l₁, rfl⟩ := hx
    exact hright l₁ v
  · have hz := bgSVOA.smul_smul_left (0 : ℂ) (1 : Fock) (-2) v
    simpa using congrArg D hz
  · intro x y _ _ hx hy
    simp only [SuperVertexAlgebra.smul_add_left, map_add, hx, hy, add_zero]
  · intro c x _ hx
    simp only [SuperVertexAlgebra.smul_smul_left, map_smul, hx, smul_zero]

/-- Word-pair annihilation is enough to put the entire super `C₂` subspace in a detector's
kernel. -/
theorem superO₂_le_ker_of_linearMap_word_pairs (D : Fock →ₗ[ℂ] M)
    (hword : ∀ l₁ l₂ : BGWord,
      D (bgSVOA.smul (stWordBG l₁) (-2) (stWordBG l₂)) = 0) :
    superO₂ bgSVOA ≤ LinearMap.ker D := by
  rw [superO₂, Submodule.span_le]
  intro x hx
  obtain ⟨u, v, rfl⟩ := hx
  change D (bgSVOA.smul u (-2) v) = 0
  exact linearMap_smul_neg_two_eq_zero_of_words D hword u v

end

end VOA.BGInst
