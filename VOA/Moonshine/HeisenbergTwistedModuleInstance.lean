/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.HeisenbergTwistedModuleProductFormula
import VOA.Moonshine.HeisenbergTwistedModuleL0

/-!
# The `σ`-twisted module of the rank-`r` Heisenberg VOA  (Moonshine step M6a, Heisenberg part)

`heisTwistedModule r : TwistedModule (sigma1 r) 2 (FockT r)` — the twisted Fock space
`S[θ] = FockT r` is a `σ`-twisted module, in the sense of `Modularity/Twisted.lean`, for the level-one rank-`r` Heisenberg VOA
`heisVOA1 r` and its involution `σ = sigma1 r`.  The data:

* `YM := YT r`, the concrete twisted vertex operator of `HeisenbergTwistedModuleVertex`
  (generators ↦ the half-integer moded twisted Heisenberg fields);
* `vacuum_YM`, `truncation`, `support` — `YT_vacuum`, `YT_truncation`, `YT_support`;
* `jacobi` — `twistedJacobi_YT` (`HeisenbergTwistedModuleProductFormula`);
* `weight := weightC r`, the `L₀`-eigenspace decomposition `weightT r` of
  `TwistedHeisenberg.lean` transported from `ℚ` to `ℂ`; `L0_weight` is `YT_omega_two`
  (`Y^T(ω)₍₁₎ = L0T r`, with the `r/16` of the twisted vacuum); every weight space is
  finite-dimensional, and weights are bounded below by `r/16`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
This is the Heisenberg part of M6 only: the lattice twisted module `V_Λ^T = S[θ] ⊗ T` (the
`T`-factor and the twisted vertex operators of `e^α`) is not constructed here.
-/

namespace VOA

namespace Moonshine

open MvPolynomial TwistedHeisenberg HeisenbergN TwistedReduction
open Module (End)

variable (r : ℕ)

/-! ## The complex weight decomposition -/

/-- The `L₀`-eigenspace of `S[θ]` of eigenvalue `α ∈ ℂ`. -/
noncomputable def weightC (α : ℂ) : Submodule ℂ (FockT r) :=
  ⨆ (d : ℕ) (_ : ((levelT r d : ℚ) : ℂ) = α), gradingT r d

theorem levelC_injective : Function.Injective fun d : ℕ => ((levelT r d : ℚ) : ℂ) :=
  fun _ _ h => levelT_injective r (Rat.cast_injective h)

theorem weightC_level (d : ℕ) : weightC r ((levelT r d : ℚ) : ℂ) = gradingT r d := by
  apply le_antisymm
  · refine iSup₂_le fun e he => ?_
    rw [levelC_injective r he]
  · exact le_iSup₂_of_le d rfl le_rfl

theorem weightC_eq_bot {α : ℂ} (hα : ∀ d : ℕ, ((levelT r d : ℚ) : ℂ) ≠ α) : weightC r α = ⊥ := by
  rw [weightC, eq_bot_iff]
  exact iSup₂_le fun d hd => absurd hd (hα d)

theorem weightC_isInternal : DirectSum.IsInternal (weightC r) := by
  have hA := gradingT_isInternal r
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [← iSupIndep_ne_bot]
    have hex : ∀ α : {α : ℂ // weightC r α ≠ ⊥}, ∃ d : ℕ, ((levelT r d : ℚ) : ℂ) = α.1 := by
      rintro ⟨α, hα⟩
      by_contra h
      push Not at h
      exact hα (weightC_eq_bot r h)
    choose g hg using hex
    have hginj : Function.Injective g := by
      intro a b h
      exact Subtype.ext (by rw [← hg a, ← hg b, h])
    have hcomp : (fun α : {α : ℂ // weightC r α ≠ ⊥} => weightC r α.1) = gradingT r ∘ g := by
      funext α
      simp only [Function.comp_apply]
      rw [← weightC_level, hg α]
    rw [hcomp]
    exact hA.submodule_iSupIndep.comp hginj
  · rw [eq_top_iff, ← hA.submodule_iSup_eq_top]
    exact iSup_le fun d => (weightC_level r d) ▸ le_iSup (weightC r) ((levelT r d : ℚ) : ℂ)

theorem weightC_finiteDimensional (α : ℂ) : FiniteDimensional ℂ (weightC r α) := by
  by_cases h : ∃ d : ℕ, ((levelT r d : ℚ) : ℂ) = α
  · obtain ⟨d, rfl⟩ := h
    rw [weightC_level]
    infer_instance
  · push Not at h
    rw [weightC_eq_bot r h]
    infer_instance

theorem YT_omega_two_weightC {α : ℂ} {x : FockT r} (hx : x ∈ weightC r α) :
    YT r (heisVOA1 r).conformalVector 2 x = α • x := by
  rw [YT_omega_two]
  by_cases h : ∃ d : ℕ, ((levelT r d : ℚ) : ℂ) = α
  · obtain ⟨d, rfl⟩ := h
    rw [weightC_level] at hx
    exact L0T_of_mem_gradingT hx
  · push Not at h
    rw [weightC_eq_bot r h, Submodule.mem_bot] at hx
    rw [hx, map_zero, smul_zero]

theorem weightC_boundedBelow :
    ∃ B : ℝ, ∀ α : ℂ, weightC r α ≠ ⊥ → B ≤ α.re := by
  refine ⟨(r : ℝ) / 16, fun α hα => ?_⟩
  by_contra hlt
  apply hα
  refine weightC_eq_bot r fun d hd => hlt ?_
  rw [← hd, Complex.ratCast_re, levelT]
  push_cast
  have : (0 : ℝ) ≤ d := d.cast_nonneg
  linarith

/-! ## The twisted module -/

/-- **The twisted Heisenberg module.**  `S[θ] = FockT r`, with the concrete twisted vertex
operator `YT r`, is a `σ`-twisted module of order `2` for the level-one rank-`r` Heisenberg
VOA `heisVOA1 r`. -/
noncomputable def heisTwistedModule : TwistedModule (sigma1 r) 2 (FockT r) where
  YM := YT r
  vacuum_YM k := by
    change YT r (vacuumN r) k = _
    rw [YT_vacuum]
    push_cast
    rfl
  truncation := YT_truncation r
  support := fun j u hu k hk => YT_support r j u hu k hk
  jacobi := twistedJacobi_YT r
  weight := weightC r
  isInternal := weightC_isInternal r
  L0_weight := fun α x hx => YT_omega_two_weightC r hx
  finrank := weightC_finiteDimensional r
  boundedBelow := weightC_boundedBelow r

@[simp] theorem heisTwistedModule_YM : (heisTwistedModule r).YM = YT r := rfl

@[simp] theorem heisTwistedModule_weight : (heisTwistedModule r).weight = weightC r := rfl

end Moonshine

end VOA
