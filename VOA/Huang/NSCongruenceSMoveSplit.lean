/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSCongruenceCyclotomic

/-!
# Splitting the `S` move along the orbit

`MixedSMoveOrbit` (the `S` step of the mixed indicators at every primitive row) is derived from
three named sub-statements:

* `MixedPositiveSMove` — rows `(m,l)` with `m > 0` and `l ≠ 0` (only positive-degree rotation
  traces occur, on both sides, up to the dual probe for `l < 0`);
* `MixedBaseSMove` — the single row `(1,0)`, whose target `(0,-1)` is the closed-rotation
  (zero-degree) indicator;
* `MixedChargeSymmetry` — equivariance at the central element `S² = -1`, i.e.
  `ν_{-m,-l} = ν_{m,l} ∘ (C ⊗ C)`.

All three are true consequences of Ng–Schauenburg Theorem 5.4 (they are instances of
equivariance).  None is proved here.
-/

noncomputable section
set_option linter.unusedSectionVars false

namespace VOA.Huang.NSCongruence

open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg
open scoped MatrixGroups

universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- **Sub-residual (positive-degree S move).**  The `S` step at every primitive row `(m,l)` with
`m > 0` and `l ≠ 0`. -/
def MixedPositiveSMove (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ →
    ∀ (a : F.Label) (m l : ℤ), 0 < m → l ≠ 0 → IsCoprime m l →
      ∀ z : F.Label × F.Label → ℂ,
        mixedRow F a l (-m) z = mixedRow F a m l (mixedRepresentation ρ ModularGroup.S⁻¹ z)

open Classical in
/-- **Sub-residual (base row).**  The `S` step at the row `(1,0)`: the zero-degree indicator
`ν_{0,-1}` is the `S⁻¹`-transform of the fusion row `ν_{1,0}`. -/
def MixedBaseSMove (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ →
    ∀ (a : F.Label) (z : F.Label × F.Label → ℂ),
      mixedRow F a 0 (-1) z = mixedRow F a 1 0 (mixedRepresentation ρ ModularGroup.S⁻¹ z)

open Classical in
/-- **Sub-residual (charge symmetry).**  Equivariance at the central element `S²`. -/
def MixedChargeSymmetry (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ →
    ∀ (a : F.Label) (m l : ℤ) (z : F.Label × F.Label → ℂ),
      mixedRow F a (-m) (-l) z = mixedRow F a m l (mixedRepresentation ρ (ModularGroup.S ^ 2) z)

open Classical in
/-- **The `S` move along the orbit from the three sub-statements.** -/
theorem SMoveOrbit_of_split (F : SphericalFusion C) (M : Modular F)
    (hP : MixedPositiveSMove F M) (hB : MixedBaseSMove F M) (hC : MixedChargeSymmetry F M) :
    MixedSMoveOrbit F M := by
  intro ρ hr a γ z
  set σ := mixedRepresentation ρ with hσ
  have g1 : (ModularGroup.S⁻¹ * ModularGroup.S⁻¹ : SL(2, ℤ)) = ModularGroup.S ^ 2 := by decide
  have g2 : (ModularGroup.S⁻¹ * ModularGroup.S ^ 2 : SL(2, ℤ)) =
      ModularGroup.S ^ 2 * ModularGroup.S⁻¹ := by decide
  have hSS : ∀ w, σ ModularGroup.S⁻¹ (σ ModularGroup.S⁻¹ w) = σ (ModularGroup.S ^ 2) w := by
    intro w
    rw [← LinearEquiv.mul_apply, ← map_mul, g1]
  have hc2 : ∀ w, σ ModularGroup.S⁻¹ (σ (ModularGroup.S ^ 2) w) =
      σ (ModularGroup.S ^ 2) (σ ModularGroup.S⁻¹ w) := by
    intro w
    rw [← LinearEquiv.mul_apply, ← map_mul, g2, map_mul, LinearEquiv.mul_apply]
  -- negation transfers the S move
  have hneg : ∀ m l, (∀ w, mixedRow F a l (-m) w = mixedRow F a m l (σ ModularGroup.S⁻¹ w)) →
      ∀ w, mixedRow F a (-l) (-(-m)) w = mixedRow F a (-m) (-l) (σ ModularGroup.S⁻¹ w) := by
    intro m l h w
    have e1 := hC ρ hr a l (-m) w
    rw [e1, h, hC ρ hr a m l, hc2]
  -- positive first index
  have hpos : ∀ m l, 0 < m → IsCoprime m l →
      ∀ w, mixedRow F a l (-m) w = mixedRow F a m l (σ ModularGroup.S⁻¹ w) := by
    intro m l hm hml
    by_cases hl : l = 0
    · subst hl
      have hm1 : m = 1 := by
        have hu := isCoprime_zero_right.mp hml
        rcases Int.isUnit_iff.mp hu with h | h <;> omega
      subst hm1
      exact hB ρ hr a
    · exact hP ρ hr a m l hm hl hml
  -- the zero row `(0,-1)`
  have hzero : ∀ w, mixedRow F a (-1) (-0) w = mixedRow F a 0 (-1) (σ ModularGroup.S⁻¹ w) := by
    intro w
    rw [hB ρ hr a, hSS]
    simpa using hC ρ hr a 1 0 w
  have hall : ∀ m l, IsCoprime m l →
      ∀ w, mixedRow F a l (-m) w = mixedRow F a m l (σ ModularGroup.S⁻¹ w) := by
    intro m l hml
    rcases lt_trichotomy 0 m with hm | hm | hm
    · exact hpos m l hm hml
    · subst hm
      have hl : l = 1 ∨ l = -1 := Int.isUnit_iff.mp (isCoprime_zero_left.mp hml)
      rcases hl with rfl | rfl
      · intro w
        have := hneg 0 (-1) hzero w
        simpa using this
      · intro w
        simpa using hzero w
    · intro w
      have hml' : IsCoprime (-m) (-l) := by
        rw [IsCoprime.neg_neg_iff]; exact hml
      have := hneg (-m) (-l) (hpos (-m) (-l) (by omega) hml') w
      simpa using this
  have hcop : IsCoprime (rowAction 1 0 γ).1 (rowAction 1 0 γ).2 := by
    rw [rowAction_one_zero]
    refine ⟨γ 1 1, -γ 1 0, ?_⟩
    have h := γ.property
    rw [Matrix.det_fin_two] at h
    simp only
    linarith
  exact hall _ _ hcop z

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge

open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence

universe u v w

/-- The finest current residual contract: positive-degree S move, base row, charge symmetry,
and cyclotomic mixed S entries, for every modular category. -/
def NSMixedSplitResidualsAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F),
    MixedPositiveSMove F M ∧ MixedBaseSMove F M ∧ MixedChargeSymmetry F M ∧
      MixedSCyclotomic F M

/-- **The kernel half of NS 6.8 from the split residuals.** -/
theorem nsProjectiveKernelAll_of_splitResiduals (h : NSMixedSplitResidualsAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} := by
  apply nsProjectiveKernelAll_of_SResiduals
  intro C _ _ _ _ _ _ _ _ _ _ F M
  obtain ⟨hP, hB, hC, hc⟩ := h C F M
  exact ⟨SMoveOrbit_of_split F M hP hB hC, hc⟩

end VOA.Huang.DLNBridge
