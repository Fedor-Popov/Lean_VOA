/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbSpanGlue

/-! # OrbOcta: graded descent with any finite seed family gives finite conformal towers

`OrbSpan.dongJiangVirasoroSpan_of_gradedDescent` is specific to the Dong--Jiang seeds
`𝟙, u, v, u₍ₙ₎u`. This file proves the seed-agnostic version for an arbitrary VOA:

`conformalTowerSpan_of_gradedDescent`: if every weight space lies in
`O₂ + span (range s) + Σ_{m ≥ 1} L(-m) W_{N-m}` for a finite family `s`, then the conformal
towers of the classes of `s` span `A₂(W) = W/C₂(W)` (`OrbC2b.ConformalTowerSpan W`).

`conformalTowerSpan_of_primary`: the same from a Virasoro primary decomposition and a
primary reduction.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbOcta
open VOA VertexOperatorAlgebra OrbC2b OrbC2c OrbSpan
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- **Graded induction with finitely many seeds.** -/
theorem conformalTowerSpan_of_gradedDescent {ι : Type*} [Finite ι] (s : ι → V)
    (h : GradedDescent W (Set.range s)) : ConformalTowerSpan W := by
  let f : ι → A₂ W := fun i => mk₂ W (s i)
  apply conformalTowerSpan_of_towerSpan_eq_top W f
  let S : Submodule ℂ V := (towerSpan W f).comap (mk₂ W)
  have hT : Submodule.span ℂ (Set.range s) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change mk₂ W (s i) ∈ towerSpan W f
    exact Submodule.subset_span ⟨(i, 0), by simp [f]⟩
  have hO : O₂ W ≤ S := by
    intro x hx
    change mk₂ W x ∈ towerSpan W f
    rw [(mk₂_eq_zero_iff W).mpr hx]
    exact Submodule.zero_mem _
  have hL : ∀ (m : ℕ) (y : V), y ∈ S → W.L (-(m : ℤ) - 1) y ∈ S := fun m y hy =>
    mk₂_virWord_mem W f y hy [m]
  have hnat : ∀ N : ℕ, W.grading (N : ℤ) ≤ S := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      refine le_trans (h N) (sup_le (sup_le hO hT) ?_)
      apply Submodule.span_le.mpr
      rintro x ⟨m, y, hy, rfl⟩
      apply hL
      by_cases hneg : (N : ℤ) - m - 1 < 0
      · rw [W.positivity _ hneg, Submodule.mem_bot] at hy
        rw [hy]; exact Submodule.zero_mem _
      · have hk : (N : ℤ) - m - 1 = ((N - m - 1 : ℕ) : ℤ) := by omega
        rw [hk] at hy
        exact ih (N - m - 1) (by omega) hy
  have hall : ∀ N : ℤ, W.grading N ≤ S := by
    intro N
    by_cases hN : N < 0
    · rw [W.positivity N hN]; exact bot_le
    · have := hnat N.toNat
      rwa [Int.toNat_of_nonneg (by omega)] at this
  have hS : S = ⊤ := by
    apply top_unique
    rw [← W.isInternal.submodule_iSup_eq_top]
    exact iSup_le hall
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := mk₂_surjective W y
  have hx : x ∈ S := by rw [hS]; trivial
  exact hx

/-- **Primary form.** -/
theorem conformalTowerSpan_of_primary {ι : Type*} [Finite ι] (s : ι → V)
    (hD : VirPrimaryDecomp W) (hG : PrimaryC2Reduction W (Set.range s)) :
    ConformalTowerSpan W :=
  conformalTowerSpan_of_gradedDescent W s (gradedDescent_of_primary W _ hD hG)

end VOA.Classification.COne.OrbOcta
