/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorGraded
import VOA.Modules.LogTensorTargets
import VOA.Classification.COne.PlusFiniteLengthCyclic
import VOA.Classification.COne.ABDWeakAdmissibleEigenCyclic

/-!
# Graded bookkeeping for logarithmic modules (stage T1d, part 1)

Elementary tools on a `LogVModule` `N`, used by the finiteness theorem for logarithmic fusion
rules (`LogTensorFinMain`):

* `LogFin.proj N α` — the projection `M → M_[α] ⊆ M` of the grading decomposition, with
  `proj_of_mem` (identity on `M_[α]`), `proj_of_mem_ne` (zero on `M_[β]`, `β ≠ α`),
  `proj_mem`, and `eq_zero_of_proj` (a vector with all components zero is zero);
* `LogFin.mode_mem_weight` — a homogeneous mode `u₍ₚ₎`, `u ∈ V_(d)`, maps `M_[α]` to
  `M_[α + d − p − 1]`;
* `LogFin.weight_eq_bot_of_re_lt` — below the global lower bound the graded pieces vanish;
* `LogFin.c2Part N α` — the degree-`α` part of `C₂(M)`: the span of `u₍ℓ₎ w` with `u ∈ V_(d)`,
  `d ≥ 0`, `ℓ ≤ −2`, `w ∈ M_[α − (d − ℓ − 1)]`;
* `LogFin.modeAlg_mem_of_modeStable` — a mode-stable subspace is stable under the mode algebra.

No `sorry`, no new axioms.
-/

namespace VOA.LogTensor.LogFin

open Module (End)
open VOA.Classification.COne

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M] (N : LogVModule W M)

/-- The linear equivalence `⊕_α M_[α] ≃ M` of the grading. -/
noncomputable def gradEquiv : (DirectSum ℂ fun α : ℂ => N.weight α) ≃ₗ[ℂ] M :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap N.weight) N.isInternal

/-- The projection onto the generalized weight space `M_[α]`, viewed inside `M`. -/
noncomputable def proj (α : ℂ) : M →ₗ[ℂ] M :=
  (N.weight α).subtype ∘ₗ DirectSum.component ℂ ℂ (fun β : ℂ => N.weight β) α ∘ₗ
    (gradEquiv N).symm.toLinearMap

theorem proj_mem (α : ℂ) (y : M) : proj N α y ∈ N.weight α := by
  simp only [proj, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
  exact Subtype.property _

theorem gradEquiv_symm_of_mem {α : ℂ} {y : M} (hy : y ∈ N.weight α) :
    (gradEquiv N).symm y = DirectSum.of (fun β : ℂ => N.weight β) α ⟨y, hy⟩ := by
  apply (gradEquiv N).injective
  rw [LinearEquiv.apply_symm_apply]
  change y = DirectSum.coeLinearMap N.weight (DirectSum.lof ℂ ℂ (fun β => N.weight β) α ⟨y, hy⟩)
  rw [DirectSum.coeLinearMap_lof]

theorem proj_of_mem {α : ℂ} {y : M} (hy : y ∈ N.weight α) : proj N α y = y := by
  classical
  simp only [proj, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    gradEquiv_symm_of_mem N hy, Submodule.coe_subtype]
  rw [show DirectSum.of (fun β : ℂ => N.weight β) α ⟨y, hy⟩ =
    DirectSum.lof ℂ ℂ (fun β : ℂ => N.weight β) α ⟨y, hy⟩ from rfl, DirectSum.component.lof_self]

theorem proj_of_mem_ne {α β : ℂ} {y : M} (hy : y ∈ N.weight β) (h : β ≠ α) :
    proj N α y = 0 := by
  classical
  simp only [proj, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    gradEquiv_symm_of_mem N hy, Submodule.coe_subtype]
  rw [show DirectSum.of (fun β : ℂ => N.weight β) β ⟨y, hy⟩ =
    DirectSum.lof ℂ ℂ (fun β : ℂ => N.weight β) β ⟨y, hy⟩ from rfl,
    DirectSum.component.of]
  simp [h]

theorem eq_zero_of_proj {y : M} (h : ∀ α, proj N α y = 0) : y = 0 := by
  classical
  have h0 : (gradEquiv N).symm y = 0 := by
    ext α
    have := h α
    simp only [proj, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Submodule.coe_subtype] at this
    simpa [DirectSum.component] using this
  have := congrArg (gradEquiv N) h0
  rwa [LinearEquiv.apply_symm_apply, map_zero] at this

theorem eq_of_proj {y z : M} (h : ∀ α, proj N α y = proj N α z) : y = z := by
  rw [← sub_eq_zero]
  exact eq_zero_of_proj N (fun α => by rw [map_sub, h, sub_self])

theorem iSup_weight_eq_top : (⨆ α, N.weight α) = ⊤ := by
  classical
  exact N.isInternal.submodule_iSup_eq_top

/-- Every vector is a finite sum of homogeneous vectors (an induction principle). -/
theorem induction_on {C : M → Prop} (y : M) (hmem : ∀ α, ∀ x ∈ N.weight α, C x)
    (hzero : C 0) (hadd : ∀ x z, C x → C z → C (x + z)) : C y := by
  have hy : y ∈ ⨆ α, N.weight α := by rw [iSup_weight_eq_top]; trivial
  exact Submodule.iSup_induction _ (motive := C) hy hmem hzero hadd

/-- Homogeneous modes shift generalized weights by the integer mode degree. -/
theorem mode_mem_weight {d : ℤ} {u : 𝒱} (hu : u ∈ W.grading d) (p : ℤ) {α : ℂ} {w : M}
    (hw : w ∈ N.weight α) :
    mode (N.YM u) p w ∈ N.weight (α + ((d - p - 1 : ℤ) : ℂ)) := by
  rw [N.weight_eq_maxGenEigenspace] at hw ⊢
  exact ABDWeakAdmissible.mode_mem_maxGenEigenspace N.toWeakModule hu p hw

/-- A global lower bound for the weights. -/
theorem exists_lower_bound : ∃ B : ℝ, ∀ α : ℂ, α.re < B → N.weight α = ⊥ := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  exact ⟨B, fun α hα => by
    by_contra h
    exact absurd (hB α h) (not_le.mpr hα)⟩

theorem eq_zero_of_mem_bot {α : ℂ} {y : M} (h : N.weight α = ⊥) (hy : y ∈ N.weight α) :
    y = 0 := by
  rw [h] at hy
  exact (Submodule.mem_bot ℂ).mp hy

/-- The degree-`α` part of `C₂(M)`: spanned by `u₍ℓ₎ w`, `u ∈ V_(d)`, `d ≥ 0`, `ℓ ≤ −2`,
`w ∈ M_[α − (d − ℓ − 1)]`. -/
def c2Part (α : ℂ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (d ℓ : ℤ) (u : 𝒱) (w : M), u ∈ W.grading d ∧ 0 ≤ d ∧ ℓ ≤ -2 ∧
    w ∈ N.weight (α - ((d - ℓ - 1 : ℤ) : ℂ)) ∧ y = mode (N.YM u) ℓ w}

/-- A mode-stable subspace is stable under the whole mode algebra. -/
theorem modeAlg_mem_of_modeStable {P : Submodule ℂ M} (hP : ModeStable N.toWeakModule P)
    {f : End ℂ M} (hf : f ∈ modeAlg N.toWeakModule) : ∀ y ∈ P, f y ∈ P := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨u, n, rfl⟩ := hf
    intro y hy
    exact hP u n y hy
  | algebraMap c =>
    intro y hy
    rw [Module.algebraMap_end_apply]
    exact P.smul_mem c hy
  | add f g _ _ hf hg => intro y hy; exact P.add_mem (hf y hy) (hg y hy)
  | mul f g _ _ hf hg => intro y hy; exact hf _ (hg y hy)

/-- The `ℂ`-span of a mode-algebra submodule is mode-stable. -/
theorem modeStable_restrictScalars (P : Submodule (modeAlg N.toWeakModule) M) :
    ModeStable N.toWeakModule (P.restrictScalars ℂ) := by
  intro u m y hy
  exact P.smul_mem (⟨mode (N.YM u) m, Algebra.subset_adjoin ⟨u, m, rfl⟩⟩ :
    modeAlg N.toWeakModule) hy

end VOA.LogTensor.LogFin
