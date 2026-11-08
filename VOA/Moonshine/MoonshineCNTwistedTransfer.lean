import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Transfer of weighted counts along linear isomorphisms of coordinate spaces

On `X →₀ ℂ` a function `κ : X → ℂ` gives the diagonal operator `e_x ↦ κ(x) e_x`
(`finsuppDiag`).  If a linear isomorphism `Ψ : (X →₀ ℂ) ≃ (Y →₀ ℂ)` intertwines a family of
diagonal operators `κX j` and `κY j` (`j : J`), then `Ψ e_x` is supported on the points with the
same labels `j ↦ κ j`, so the label fibres have the same cardinality, and every weighted count over
a union of label fibres agrees on both sides (`sum_eq_sum_of_diag_equiv`).

This is how traces of an automorphism on graded pieces are compared below: the automorphism and two
torus elements recording the bidegree are the diagonal operators.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open Finsupp Finset

/-- The diagonal operator `e_x ↦ κ(x) e_x`. -/
def finsuppDiag {X : Type*} (κ : X → ℂ) : (X →₀ ℂ) →ₗ[ℂ] (X →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun x => Finsupp.single x (κ x)

theorem finsuppDiag_single {X : Type*} (κ : X → ℂ) (x : X) (a : ℂ) :
    finsuppDiag κ (single x a) = single x (κ x * a) := by
  simp [finsuppDiag, Finsupp.smul_single, mul_comm]

theorem finsuppDiag_apply {X : Type*} (κ : X → ℂ) (v : X →₀ ℂ) (y : X) :
    finsuppDiag κ v y = κ y * v y := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw, mul_add]
  | single x a =>
      rw [finsuppDiag_single]
      by_cases h : x = y
      · subst h; simp
      · rw [Finsupp.single_eq_of_ne' h, Finsupp.single_eq_of_ne' h, mul_zero]

variable {X Y : Type*}

/-- Intertwining a diagonal operator forces `Ψ e_x` to vanish off the matching eigenvalue. -/
theorem apply_single_eq_zero_of_diag {Ψ : (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ)} {κX : X → ℂ} {κY : Y → ℂ}
    (h : ∀ v, Ψ (finsuppDiag κX v) = finsuppDiag κY (Ψ v)) (x : X) (y : Y)
    (hxy : κY y ≠ κX x) : Ψ (single x 1) y = 0 := by
  have h1 := congrArg (fun v => v y) (h (single x 1))
  simp only [finsuppDiag_single, finsuppDiag_apply, mul_one] at h1
  rw [show single x (κX x) = κX x • single x (1 : ℂ) by simp, map_smul,
    Finsupp.smul_apply, smul_eq_mul] at h1
  have h2 : (κX x - κY y) * Ψ (single x 1) y = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3).symm hxy
  · exact h3

/-- An injective map sending each `e_x` (`x ∈ S`) into the span of `T` forces `|S| ≤ |T|`. -/
theorem card_le_of_injective_support (Ψ : (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ))
    (hΨ : Function.Injective Ψ) (S : Finset X) (T : Finset Y)
    (hsupp : ∀ x ∈ S, ∀ y, Ψ (single x 1) y ≠ 0 → y ∈ T) : S.card ≤ T.card := by
  classical
  let V := Finsupp.supported ℂ ℂ (T : Set Y)
  have hmem : ∀ x : S, Ψ (single (x : X) 1) ∈ V := by
    intro x
    rw [Finsupp.mem_supported]
    intro y hy
    exact hsupp x x.2 y (Finsupp.mem_support_iff.mp hy)
  let fam : S → V := fun x => ⟨Ψ (single (x : X) 1), hmem x⟩
  have hli0 : LinearIndependent ℂ (fun x : S => single (x : X) (1 : ℂ)) :=
    (Finsupp.linearIndependent_single_one ℂ X).comp _ Subtype.val_injective
  have hli1 : LinearIndependent ℂ (Ψ ∘ fun x : S => single (x : X) (1 : ℂ)) :=
    hli0.map' Ψ (LinearMap.ker_eq_bot.mpr hΨ)
  have hli : LinearIndependent ℂ fam := by
    apply LinearIndependent.of_comp V.subtype
    exact hli1
  haveI : FiniteDimensional ℂ V :=
    LinearEquiv.finiteDimensional (Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ)
      (T : Set Y)).symm
  have h := LinearIndependent.fintype_card_le_finrank hli
  rw [Fintype.card_coe] at h
  refine h.trans (le_of_eq ?_)
  rw [(Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ) (T : Set Y)).finrank_eq,
    Module.finrank_finsupp_self]
  simp

variable {J : Type*}

/-- A linear isomorphism intertwining a family of diagonal operators preserves the cardinality of
each fibre of the labels `x ↦ (j ↦ κ j x)`. -/
theorem card_fiber_eq_of_diag_equiv (Ψ : (X →₀ ℂ) ≃ₗ[ℂ] (Y →₀ ℂ)) (κX : J → X → ℂ)
    (κY : J → Y → ℂ) (h : ∀ j v, Ψ (finsuppDiag (κX j) v) = finsuppDiag (κY j) (Ψ v))
    (σ : J → ℂ) (S : Finset X) (T : Finset Y) (hS : ∀ x, x ∈ S ↔ ∀ j, κX j x = σ j)
    (hT : ∀ y, y ∈ T ↔ ∀ j, κY j y = σ j) : S.card = T.card := by
  have h' : ∀ j v, Ψ.symm (finsuppDiag (κY j) v) = finsuppDiag (κX j) (Ψ.symm v) := by
    intro j v
    apply Ψ.injective
    rw [LinearEquiv.apply_symm_apply, h, LinearEquiv.apply_symm_apply]
  apply le_antisymm
  · refine card_le_of_injective_support Ψ.toLinearMap Ψ.injective S T fun x hx y hy => ?_
    rw [hT]
    intro j
    rw [← (hS x).mp hx j]
    by_contra hne
    exact hy (apply_single_eq_zero_of_diag (Ψ := Ψ.toLinearMap) (h j) x y hne)
  · refine card_le_of_injective_support Ψ.symm.toLinearMap Ψ.symm.injective T S
      fun y hy x hx => ?_
    rw [hS]
    intro j
    rw [← (hT y).mp hy j]
    by_contra hne
    exact hx (apply_single_eq_zero_of_diag (Ψ := Ψ.symm.toLinearMap) (h' j) y x hne)

/-- **Transfer of weighted counts.**  If `Ψ` intertwines the diagonal operators `κX j` and
`κY j`, then for every set `P` of labels the counts weighted by `κ j₀` over the points whose label
lies in `P` agree. -/
theorem sum_eq_sum_of_diag_equiv (Ψ : (X →₀ ℂ) ≃ₗ[ℂ] (Y →₀ ℂ))
    (κX : J → X → ℂ) (κY : J → Y → ℂ)
    (h : ∀ j v, Ψ (finsuppDiag (κX j) v) = finsuppDiag (κY j) (Ψ v))
    (P : (J → ℂ) → Prop) (S : Finset X) (T : Finset Y)
    (hS : ∀ x, x ∈ S ↔ P fun j => κX j x) (hT : ∀ y, y ∈ T ↔ P fun j => κY j y) (j₀ : J) :
    ∑ x ∈ S, κX j₀ x = ∑ y ∈ T, κY j₀ y := by
  classical
  set ℓX : X → J → ℂ := fun x j => κX j x
  set ℓY : Y → J → ℂ := fun y j => κY j y
  set Λ := S.image ℓX ∪ T.image ℓY
  have hX : ∑ x ∈ S, κX j₀ x = ∑ σ ∈ Λ, ∑ x ∈ S.filter (fun x => ℓX x = σ), κX j₀ x :=
    (sum_fiberwise_of_maps_to (fun x hx => mem_union_left _ (mem_image_of_mem ℓX hx)) _).symm
  have hY : ∑ y ∈ T, κY j₀ y = ∑ σ ∈ Λ, ∑ y ∈ T.filter (fun y => ℓY y = σ), κY j₀ y :=
    (sum_fiberwise_of_maps_to (fun y hy => mem_union_right _ (mem_image_of_mem ℓY hy)) _).symm
  rw [hX, hY]
  refine sum_congr rfl fun σ _ => ?_
  have hXc : ∑ x ∈ S.filter (fun x => ℓX x = σ), κX j₀ x =
      ∑ x ∈ S.filter (fun x => ℓX x = σ), σ j₀ :=
    sum_congr rfl fun x hx => by rw [← (mem_filter.mp hx).2]
  have hYc : ∑ y ∈ T.filter (fun y => ℓY y = σ), κY j₀ y =
      ∑ y ∈ T.filter (fun y => ℓY y = σ), σ j₀ :=
    sum_congr rfl fun y hy => by rw [← (mem_filter.mp hy).2]
  rw [hXc, hYc, sum_const, sum_const]
  congr 1
  by_cases hP : P σ
  · refine card_fiber_eq_of_diag_equiv Ψ κX κY h σ _ _ (fun x => ?_) (fun y => ?_)
    · rw [mem_filter, hS, funext_iff]
      constructor
      · exact fun h => h.2
      · intro h'
        have : ℓX x = σ := funext h'
        refine ⟨?_, h'⟩
        have hl : (fun j => κX j x) = σ := this
        rw [hl]
        exact hP
    · rw [mem_filter, hT, funext_iff]
      constructor
      · exact fun h => h.2
      · intro h'
        have : ℓY y = σ := funext h'
        refine ⟨?_, h'⟩
        have hl : (fun j => κY j y) = σ := this
        rw [hl]
        exact hP
  · rw [filter_eq_empty_iff.mpr fun x hx hxσ => hP (by rw [← hxσ]; exact (hS x).mp hx),
      filter_eq_empty_iff.mpr fun y hy hyσ => hP (by rw [← hyσ]; exact (hT y).mp hy),
      card_empty, card_empty]

end VOA.Moonshine.ConwayNorton
