/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangFullFockWard
import VOA.Examples.InverseDSLeeYangIntertwinerDescent

/-!
# Concrete mode-generated descent for the Lee--Yang Fock field

The full Fock-space Ward identity reduces preservation of a mode-generated source null
submodule to preservation of its generators.  We apply that reduction to the explicit
level-four Lee--Yang source singular vector.

This gives two endpoints.  First, descent to any proposed simple target quotient is equivalent
to the single explicit family saying that every Fock-field coefficient of the source singular
vector belongs to the target null submodule.  Second, taking the target null submodule generated
by those coefficient images produces an unconditional canonical quotient screening field.

Identifying these Fock quotients with the simple Lee--Yang vacuum and weight `-1/5` modules is a
separate representation-theoretic statement; it is not hidden in the construction below.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangConcreteDescent

open Module (End)
open ScreeningLowering
open LeeYangIntertwinerDescent
open LeeYangFockExponential LeeYangFockVirasoro LeeYangFullFockWard

noncomputable section

universe u v

variable {Source : Type u} {Target : Type v}
variable [AddCommGroup Source] [Module ℂ Source]
variable [AddCommGroup Target] [Module ℂ Target]

/-! ## Mode closures -/

/-- Apply a word of modes, with the head acting last-added and hence outermost. -/
def applyModeWord (Lop : ℤ → End ℂ Source) : List ℤ → Source →ₗ[ℂ] Source
  | [] => LinearMap.id
  | m :: w => (Lop m).comp (applyModeWord Lop w)

@[simp] theorem applyModeWord_nil (Lop : ℤ → End ℂ Source) (x : Source) :
    applyModeWord Lop [] x = x := rfl

@[simp] theorem applyModeWord_cons (Lop : ℤ → End ℂ Source)
    (m : ℤ) (w : List ℤ) (x : Source) :
    applyModeWord Lop (m :: w) x = Lop m (applyModeWord Lop w x) := rfl

/-- The linear span of all mode words applied to a seed submodule. -/
def modeClosure (Lop : ℤ → End ℂ Source) (seed : Submodule ℂ Source) :
    Submodule ℂ Source :=
  Submodule.span ℂ {x | ∃ w : List ℤ, ∃ y ∈ seed, x = applyModeWord Lop w y}

theorem seed_le_modeClosure (Lop : ℤ → End ℂ Source) (seed : Submodule ℂ Source) :
    seed ≤ modeClosure Lop seed := by
  intro x hx
  apply Submodule.subset_span
  exact ⟨[], x, hx, rfl⟩

/-- A mode closure is invariant under every mode by construction. -/
theorem modeClosure_preserves (Lop : ℤ → End ℂ Source) (seed : Submodule ℂ Source) :
    ModeFamilyPreserves (modeClosure Lop seed) Lop := by
  intro m x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, y, hy, rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨m :: w, y, hy, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ a hx

/-! ## Ward propagation from null generators -/

/-- Ward rewrites a field coefficient applied after a source mode in terms of one target-mode
image and one shifted coefficient. -/
theorem field_apply_sourceMode
    (sourceL : ℤ → End ℂ Source) (targetL : ℤ → End ℂ Target)
    (I : FormalDist (Source →ₗ[ℂ] Target))
    (hWard : K85VirasoroIntertwinerWard sourceL targetL I)
    (m t : ℤ) (x : Source) :
    I t (sourceL m x) = targetL m (I t x) -
      (((t - 2 * m : ℤ) : ℂ) / 2 +
        ((m + 1 : ℤ) : ℂ) * k85ScreeningVirWeight) • I (t - 2 * m) x := by
  have h := LinearMap.congr_fun (hWard m t) x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] at h
  apply (eq_sub_iff_add_eq).2
  rw [add_comm]
  exact ((sub_eq_iff_eq_add).1 h).symm

/-- If every coefficient maps the seed into an invariant target submodule, Ward propagates this
to every source mode word. -/
theorem field_applyModeWord_mem
    (sourceL : ℤ → End ℂ Source) (targetL : ℤ → End ℂ Target)
    (I : FormalDist (Source →ₗ[ℂ] Target))
    (hWard : K85VirasoroIntertwinerWard sourceL targetL I)
    (T : Submodule ℂ Target) (hT : ModeFamilyPreserves T targetL)
    (seed : Submodule ℂ Source)
    (hseed : ∀ t y, y ∈ seed → I t y ∈ T) :
    ∀ w : List ℤ, ∀ t y, y ∈ seed → I t (applyModeWord sourceL w y) ∈ T := by
  intro w
  induction w with
  | nil =>
      intro t y hy
      exact hseed t y hy
  | cons m w ih =>
      intro t y hy
      rw [applyModeWord_cons, field_apply_sourceMode sourceL targetL I hWard]
      exact Submodule.sub_mem T
        (hT m _ (ih t y hy))
        (Submodule.smul_mem T _ (ih (t - 2 * m) y hy))

/-- Generator preservation is enough for coefficientwise preservation of the entire mode
closure. -/
theorem fieldRespects_modeClosure
    (sourceL : ℤ → End ℂ Source) (targetL : ℤ → End ℂ Target)
    (I : FormalDist (Source →ₗ[ℂ] Target))
    (hWard : K85VirasoroIntertwinerWard sourceL targetL I)
    (T : Submodule ℂ Target) (hT : ModeFamilyPreserves T targetL)
    (seed : Submodule ℂ Source)
    (hseed : ∀ t y, y ∈ seed → I t y ∈ T) :
    FieldRespectsNullSubmodules (modeClosure sourceL seed) T I := by
  intro t x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, y, hy, rfl⟩ := hx
      exact field_applyModeWord_mem sourceL targetL I hWard T hT seed hseed w t y hy
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ a hx

/-- For a mode-generated null submodule, the full coefficientwise descent condition is exactly
its restriction to the chosen seed submodule. -/
theorem fieldRespects_modeClosure_iff
    (sourceL : ℤ → End ℂ Source) (targetL : ℤ → End ℂ Target)
    (I : FormalDist (Source →ₗ[ℂ] Target))
    (hWard : K85VirasoroIntertwinerWard sourceL targetL I)
    (T : Submodule ℂ Target) (hT : ModeFamilyPreserves T targetL)
    (seed : Submodule ℂ Source) :
    FieldRespectsNullSubmodules (modeClosure sourceL seed) T I ↔
      ∀ t y, y ∈ seed → I t y ∈ T := by
  constructor
  · intro h t y hy
    exact h t y (seed_le_modeClosure sourceL seed hy)
  · exact fieldRespects_modeClosure sourceL targetL I hWard T hT seed

/-! ## The explicit Lee--Yang singular generator -/

/-- The level-four Lee--Yang singular expression inside the source Feigin--Fuchs Fock carrier. -/
def k85SourceSingular : LeeYangFock :=
  (5 : ℂ) • k85SourceL (-2) (k85SourceL (-2) (HeisenbergN.vacuumN 1)) +
    (-3 : ℂ) • k85SourceL (-4) (HeisenbergN.vacuumN 1)

/-- The Fock source null submodule generated by the level-four singular expression. -/
def k85SourceNull : Submodule ℂ LeeYangFock :=
  modeClosure k85SourceL (ℂ ∙ k85SourceSingular)

theorem k85SourceNull_preserves : ModeFamilyPreserves k85SourceNull k85SourceL :=
  modeClosure_preserves k85SourceL (ℂ ∙ k85SourceSingular)

/-- Exact simple-target descent gate: all coefficients preserve the source null closure if and
only if their values on the single level-four singular generator lie in the target null
submodule. -/
theorem k85FockField_respects_sourceNull_iff
    (T : Submodule ℂ LeeYangFock) (hT : ModeFamilyPreserves T k85TargetL) :
    FieldRespectsNullSubmodules k85SourceNull T k85FockField ↔
      ∀ t : ℤ, k85FockField t k85SourceSingular ∈ T := by
  rw [k85SourceNull,
    fieldRespects_modeClosure_iff k85SourceL k85TargetL k85FockField
      k85FockVirasoroScreeningFieldData.ward T hT]
  constructor
  · intro h t
    exact h t k85SourceSingular (Submodule.mem_span_singleton_self _)
  · intro h t y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul]
    exact Submodule.smul_mem T a (h t)

/-! ## An unconditional canonical target quotient -/

/-- The seed made of all coefficient images of the source singular vector. -/
def k85TargetImageSeed : Submodule ℂ LeeYangFock :=
  Submodule.span ℂ {y | ∃ t : ℤ, y = k85FockField t k85SourceSingular}

/-- The target null submodule generated by those images under all target Virasoro modes. -/
def k85TargetImageNull : Submodule ℂ LeeYangFock :=
  modeClosure k85TargetL k85TargetImageSeed

theorem k85TargetImageNull_preserves :
    ModeFamilyPreserves k85TargetImageNull k85TargetL :=
  modeClosure_preserves k85TargetL k85TargetImageSeed

theorem k85FockField_singular_mem_targetImageNull (t : ℤ) :
    k85FockField t k85SourceSingular ∈ k85TargetImageNull := by
  apply seed_le_modeClosure k85TargetL k85TargetImageSeed
  apply Submodule.subset_span
  exact ⟨t, rfl⟩

theorem k85FockField_respects_canonicalNulls :
    FieldRespectsNullSubmodules k85SourceNull k85TargetImageNull k85FockField :=
  (k85FockField_respects_sourceNull_iff k85TargetImageNull
    k85TargetImageNull_preserves).2 k85FockField_singular_mem_targetImageNull

/-- Fully concrete descent data for the source-singular quotient and the canonical target-image
quotient. -/
noncomputable def k85CanonicalDescentData :
    K85ScreeningDescentData k85FockVirasoroScreeningFieldData where
  sourceNull := k85SourceNull
  targetNull := k85TargetImageNull
  sourceMode_preserves := k85SourceNull_preserves
  targetMode_preserves := k85TargetImageNull_preserves
  field_preserves := k85FockField_respects_canonicalNulls

/-- An unconditional screening-field interface on the two canonical Fock quotients. -/
noncomputable def k85CanonicalQuotientScreeningFieldData :
    K85VirasoroScreeningFieldData
      (Vir := LeeYangFock ⧸ k85SourceNull)
      (ShiftedVir := LeeYangFock ⧸ k85TargetImageNull) :=
  k85CanonicalDescentData.toQuotientScreeningFieldData

end
end LeeYangConcreteDescent
end InverseDS
end VOA
