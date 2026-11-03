/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.MoonshineCorollary
import VOA.Modularity.TraceIndependence

/-!
# `TraceSpanning` reduces to the single matrix `S`

`Modularity.BlockSpanning` proves Zhu's modularity for every `A ∈ SL₂(ℤ)` from `TraceSpanning`
and `TraceIndependent`, and already has the three structural ingredients of `TraceSpanning`:

* the cocycle `autFactor_mul` and hence the **product law** `realisesLaw_mul`,
* `realisesLaw_one`,
* the **`T`-law `realisesLaw_T`, unconditionally** (`ρ(T)` diagonal, `= e^{2πi(hᵢ−c/24)}`).

The set `{A | ∃ ρ_A, RealisesLaw A ρ_A}` is therefore a **submonoid** of `SL₂(ℤ)` containing `T`.
This file shows that `S` and `T` generate `SL₂(ℤ)` as a *monoid* — not merely as a group — so
that submonoid is everything as soon as it contains `S`:

  `traceSpanning_of_S : (∃ ρ_S, RealisesLaw … S ρ_S) → TraceSpanning Mfam h`.

Monoid (rather than group) generation is what is needed, because closure under **inverses** is
not available: inverting the law at `A` would require `ρ_A` to be invertible, which is a
*consequence* of `TraceIndependent`, not an input.  Fortunately both generators have inverses
that are already *words* in `S` and `T`:

  `S⁻¹ = S³`  (from `S² = −1`, so `S⁴ = 1`),
  `T⁻¹ = (ST)⁵ S`  (from `(ST)³ = −1`, so `(ST)⁶ = 1`, whence `(ST)⁵·S·T = (ST)⁶ = 1`).

## Contents

* `S_pow_four`, `ST_pow_six`, `S_inv_eq`, `T_inv_eq` — the two relations and the inverse words.
* `submonoid_closure_S_T_eq_top` — `S` and `T` generate `SL₂(ℤ)` as a **monoid**.
* **`traceSpanning_of_S`** — the structural reduction.
* `zhu_modularity_of_S` — Zhu's law for every `A`, from the `S`-law alone (plus the
  `TraceIndependent` inputs already discharged in `Modularity.TraceIndependence`).

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Residual: the `S`-law itself (Zhu Thms 5.3.1–5.3.3).
-/

namespace VOA

open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `S` and `T` generate `SL₂(ℤ)` as a monoid -/

/-- `(−1)² = 1` in `SL₂(ℤ)`. -/
theorem neg_one_sq_SL2Z : (-1 : SL(2, ℤ)) ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `S⁴ = 1`. -/
theorem S_pow_four : ModularGroup.S ^ 4 = 1 := by
  have h2 : ModularGroup.S ^ 2 = (-1 : SL(2, ℤ)) := by
    rw [pow_two]; exact S_mul_S
  calc ModularGroup.S ^ 4 = (ModularGroup.S ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (-1 : SL(2, ℤ)) ^ 2 := by rw [h2]
    _ = 1 := neg_one_sq_SL2Z

/-- `(ST)⁶ = 1`. -/
theorem ST_pow_six : (ModularGroup.S * ModularGroup.T) ^ 6 = 1 := by
  calc (ModularGroup.S * ModularGroup.T) ^ 6
      = ((ModularGroup.S * ModularGroup.T) ^ 3) ^ 2 := by rw [← pow_mul]
    _ = (-1 : SL(2, ℤ)) ^ 2 := by rw [S_mul_T_pow_three]
    _ = 1 := neg_one_sq_SL2Z

/-- `S⁻¹ = S³` — a *word* in `S`. -/
theorem S_inv_eq : ModularGroup.S⁻¹ = ModularGroup.S ^ 3 := by
  refine inv_eq_of_mul_eq_one_right ?_
  calc ModularGroup.S * ModularGroup.S ^ 3 = ModularGroup.S ^ 4 := by
        rw [← pow_succ']
    _ = 1 := S_pow_four

/-- `T⁻¹ = (ST)⁵ S` — a *word* in `S` and `T`. -/
theorem T_inv_eq :
    ModularGroup.T⁻¹ = (ModularGroup.S * ModularGroup.T) ^ 5 * ModularGroup.S := by
  refine inv_eq_of_mul_eq_one_left ?_
  calc (ModularGroup.S * ModularGroup.T) ^ 5 * ModularGroup.S * ModularGroup.T
      = (ModularGroup.S * ModularGroup.T) ^ 5 * (ModularGroup.S * ModularGroup.T) := by
        rw [mul_assoc]
    _ = (ModularGroup.S * ModularGroup.T) ^ 6 := by rw [← pow_succ]
    _ = 1 := ST_pow_six

/-- **`S` and `T` generate `SL₂(ℤ)` as a MONOID.**  Mathlib gives group generation
(`SpecialLinearGroup.SL2Z_generators`); the upgrade is `Subgroup.closure_toSubmonoid` together
with the fact that both inverses are words (`S_inv_eq`, `T_inv_eq`). -/
theorem submonoid_closure_S_T_eq_top :
    Submonoid.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) = ⊤ := by
  rw [eq_top_iff]
  intro A _
  have hgrp : A ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top A
  have hsub : A ∈ (Subgroup.closure ({ModularGroup.S, ModularGroup.T} :
      Set SL(2, ℤ))).toSubmonoid := hgrp
  rw [Subgroup.closure_toSubmonoid] at hsub
  refine Submonoid.closure_le.mpr ?_ hsub
  have hSmem : ModularGroup.S ∈ Submonoid.closure ({ModularGroup.S, ModularGroup.T} :
      Set SL(2, ℤ)) := Submonoid.subset_closure (by simp)
  have hTmem : ModularGroup.T ∈ Submonoid.closure ({ModularGroup.S, ModularGroup.T} :
      Set SL(2, ℤ)) := Submonoid.subset_closure (by simp)
  rintro y (hy | hy)
  · exact Submonoid.subset_closure hy
  · rw [Set.mem_inv] at hy
    have hy' : y = ModularGroup.S⁻¹ ∨ y = ModularGroup.T⁻¹ := by
      rcases hy with hy | hy
      · exact Or.inl (by rw [← hy, inv_inv])
      · exact Or.inr (by rw [← hy, inv_inv])
    rcases hy' with rfl | rfl
    · rw [S_inv_eq]
      exact Submonoid.pow_mem _ hSmem 3
    · rw [T_inv_eq]
      exact Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mul_mem _ hSmem hTmem) 5) hSmem

/-! ## The reduction -/

section Reduce

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}
variable (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **`TraceSpanning` from the `S`-law alone.**

The set of matrices realising Zhu's transformation law is a submonoid (`realisesLaw_one`,
`realisesLaw_mul`), it contains `T` unconditionally (`realisesLaw_T`), and `S`, `T` generate
`SL₂(ℤ)` as a monoid.  So `TraceSpanning` — the last mathematical input to Zhu's modularity
theorem — is equivalent to the single statement that *some* matrix realises the law at `S`. -/
theorem traceSpanning_of_S (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hS : ∃ ρS : ι → ι → ℂ, RealisesLaw Mfam h ModularGroup.S ρS) :
    TraceSpanning Mfam h := by
  intro A
  have hA : A ∈ Submonoid.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [submonoid_closure_S_T_eq_top]; exact Submonoid.mem_top A
  show ∃ ρA : ι → ι → ℂ, RealisesLaw Mfam h A ρA
  induction hA using Submonoid.closure_induction with
  | mem x hx =>
      rcases hx with rfl | hx
      · exact hS
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨_, realisesLaw_T Mfam h hcw⟩
  | one => exact ⟨_, realisesLaw_one Mfam h⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨ρx, hx⟩ := ihx
      obtain ⟨ρy, hy⟩ := ihy
      exact ⟨_, realisesLaw_mul Mfam h hx hy⟩

/-- **Zhu's modularity from the `S`-law.**  Combining `traceSpanning_of_S` with the
independence already discharged in `Modularity.TraceIndependence`. -/
theorem zhu_modularity_of_S (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hinj : Function.Injective (tEigen W h)) (hnz : TraceNonvanishing Mfam h)
    (hS : ∃ ρS : ι → ι → ℂ, RealisesLaw Mfam h ModularGroup.S ρS) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h (traceSpanning_of_S Mfam h hcw hS)
        (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnz) hcw) :=
  zhu_modularity_of_spanning Mfam h (traceSpanning_of_S Mfam h hcw hS)
    (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnz) hcw

end Reduce

end VOA
