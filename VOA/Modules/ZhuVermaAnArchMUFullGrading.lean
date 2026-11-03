/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUFullActionU

/-!
# The `ℕ`-grading of DJ's full-ideal induced module `M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗ U`

`ZhuVermaAnArchMUFull` names the carrier `MUFull W U = ⨁ₙ MUPieceFull W U n` together with the
level inclusion/projection `MUFull.incl`/`MUFull.proj`.  This file supplies the grading API that the
`OrdVModule` upgrade consumes — the mirror, on Dong–Jiang's GENUINE (full) ideal, of the prime-ideal
API `MU.deg`/`MU.isInternal_deg` (`ZhuVermaAnArchMU`):

* `MUFull.proj_incl_same` / `MUFull.proj_incl_ne` — the level projections are orthogonal idempotents;
* `MUFull.deg W U n` — the level-`n` graded subspace of `M(U)` (the range of `incl n`);
* `MUFull.isInternal_deg` — `M(U) = ⊕ₙ M(U)(n)` is a genuine internal direct-sum decomposition
  (DJ §4: `M(U)` is `ℤ₊`-graded with `M(U)(n) = A_{n,0}(𝒱) ⊗ U`);
* `MUFull.bottomIncl` / `MUFull.proj0` — the bottom (`n = 0`) layer `A_{0,0}(𝒱) ⊗ U`.

This is the ideal-agnostic half of `M(U)`'s graded structure: nothing here depends on which of the
two ideals (`Onm`, `OnmFull`) is used, so the proofs are the `MU` proofs verbatim on the full-ideal
carrier.  The `𝒱`-action layer is `oFullU` (`ZhuVermaAnArchMUFullActionU`); the module Jacobi
(DJ Thm 4.10 / Gannon 5.3.1b) is NOT closed here.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (`M(U) = ⊕_{n∈ℤ₊} A_{n,m}(V)⊗_{A_m(V)}U`, `M(U)(n) = A_{n,m}(V)⊗U`);
Gannon §5.3.2; `ZhuVermaAnArchMU` (`MU.deg`, `MU.isInternal_deg` — the prime-ideal template),
`ZhuVermaAnArchMUFull` (`MUFull`, `MUFull.incl`, `MUFull.proj`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped TensorProduct DirectSum

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The level projections are orthogonal idempotents. -/

@[simp] theorem MUFull.proj_incl_same (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    (x : MUPieceFull W U n) : MUFull.proj W U n (MUFull.incl W U n x) = x :=
  DirectSum.component.lof_self ℂ n x

theorem MUFull.proj_incl_ne (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {n k : ℕ} (h : n ≠ k)
    (x : MUPieceFull W U k) : MUFull.proj W U n (MUFull.incl W U k x) = 0 := by
  rw [MUFull.proj, MUFull.incl, DirectSum.component.of]
  exact dif_neg (Ne.symm h)

/-! ## The bottom (`n = 0`) layer `M(U)(0) = A_{0,0}(𝒱) ⊗ U`. -/

/-- The bottom-layer embedding `A_{0,0}(𝒱) ⊗ U = M(U)(0) ↪ M(U)` on DJ's genuine (full) ideal. -/
noncomputable def MUFull.bottomIncl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    MUPieceFull W U 0 →ₗ[ℂ] MUFull W U := MUFull.incl W U 0

/-- The bottom-layer projection `M(U) ↠ M(U)(0) = A_{0,0}(𝒱) ⊗ U`. -/
noncomputable def MUFull.proj0 (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    MUFull W U →ₗ[ℂ] MUPieceFull W U 0 := MUFull.proj W U 0

@[simp] theorem MUFull.proj0_bottomIncl (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (x : MUPieceFull W U 0) : MUFull.proj0 W U (MUFull.bottomIncl W U x) = x :=
  MUFull.proj_incl_same W U 0 x

/-! ## The `ℕ`-grading of `M(U)` is an internal direct sum. -/

/-- The level-`n` graded subspace of `M(U)` on DJ's genuine ideal: the range of `MUFull.incl … n`.
This is DJ's grading `M(U) = ⊕ₙ M(U)(n)`, `M(U)(n) = A_{n,0}(𝒱) ⊗ U`. -/
noncomputable def MUFull.deg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    Submodule ℂ (MUFull W U) := LinearMap.range (MUFull.incl W U n)

theorem MUFull.incl_mem_deg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    (x : MUPieceFull W U n) : MUFull.incl W U n x ∈ MUFull.deg W U n := ⟨x, rfl⟩

/-- **The `ℕ`-grading of `M(U)` is a genuine internal direct-sum decomposition** (DJ §4: `M(U)` is
`ℤ₊`-graded).  The full-ideal mirror of `MU.isInternal_deg`; the graded structure from which the
`OrdVModule` bounded-below / finite-dimensionality data is read off. -/
theorem MUFull.isInternal_deg (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    DirectSum.IsInternal (MUFull.deg W U) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hproj_sup : ∀ (n : ℕ) (z : MUFull W U),
      z ∈ (⨆ (j : ℕ) (_ : j ≠ n), MUFull.deg W U j) → MUFull.proj W U n z = 0 := by
    intro n z hz
    refine Submodule.iSup_induction _ (motive := fun w => MUFull.proj W U n w = 0) hz
      ?_ (map_zero _) (fun a b ha hb => by simp only [map_add, ha, hb, add_zero])
    intro j z hjz
    refine Submodule.iSup_induction _ (motive := fun w => MUFull.proj W U n w = 0) hjz
      ?_ (map_zero _) (fun a b ha hb => by simp only [map_add, ha, hb, add_zero])
    intro hjn w hw
    obtain ⟨v, rfl⟩ := hw
    exact MUFull.proj_incl_ne W U (Ne.symm hjn) v
  constructor
  · refine iSupIndep_def.mpr (fun n => ?_)
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    rintro x ⟨⟨y, rfl⟩, hxsup⟩
    rw [Submodule.mem_bot]
    have h0 : MUFull.proj W U n (MUFull.incl W U n y) = 0 := hproj_sup n _ hxsup
    rw [MUFull.proj_incl_same] at h0
    rw [h0, map_zero]
  · rw [eq_top_iff]
    intro x _
    refine DirectSum.induction_on x (Submodule.zero_mem _) ?_
      (fun a b ha hb => Submodule.add_mem _ ha hb)
    intro n y
    exact Submodule.mem_iSup_of_mem n ⟨y, rfl⟩

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.MUFull.deg
  #print axioms VOA.MUFull.isInternal_deg
-/
