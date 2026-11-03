/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.CardyPositivity

/-!
# `IModData` from three inputs, with the character-level positivity proved

`Huang/ZhuModData.lean` reduces `IModData` to `ZhuPBWBottomInput`, `DLMRationalWeightsInput` and
`HuangSPositivityInput`. `Huang/CardyPositivity.lean` proves that the vacuum column of `ρ(S)` is
real and non-negative from the characters alone, given real `c` and real conformal weights. This
file uses it to weaken the categorical input:

* `DLMRationalityInput` — `c` and every conformal weight are rational (DLM 2000 Thm 11.3; it states
  both);
* `HuangSInput` — only `S₀₀ ≠ 0`, `S₀ₐ = Sₐ₀`, `d_a ≥ 1` and `‖S_ab‖ ≤ S₀₀ d_a d_b`. Reality and
  positivity of `S₀₀` and reality of `d_a` are **proved** (`huangSPositivityInput_of`).

## Main result

* `iModData_of_reduced_inputs` : `ZhuPBWBottomInput`, `DLMRationalityInput`, `HuangSInput` ⟹
  `IModData`. `#print axioms`: Lean's three.
* `iModData_of_reduced_pbw_inputs` : the PBW input discharged by `VOA.pbw`.
-/

open Complex

noncomputable section

namespace VOA.Huang.IModDataReduced

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.CardyPositivity

universe u w

/-- **Rationality of the central charge and of the conformal weights** of a strongly rational VOA
(Dong–Li–Mason, CMP 214 (2000), Thm 11.3; Anderson–Moore 1988). -/
def DLMRationalityInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    StronglyRational W → (∃ q : ℚ, (q : ℂ) = W.centralCharge) ∧
      ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M),
        N.IsIrreducible → ∀ h : ℂ, HasConformalWeight N h → ∃ q : ℚ, (q : ℂ) = h

theorem dlmRationalWeightsInput_of (hRat : DLMRationalityInput.{u}) :
    DLMRationalWeightsInput.{u} :=
  fun 𝒱 _ _ W hSR => (hRat 𝒱 W hSR).2

/-- The part of the `S`-matrix positivity package that needs Huang's modular tensor category. -/
structure HuangSData {ι : Type w} (S : ι → ι → ℂ) (v0 : ι) : Prop where
  vac_ne_zero : S v0 v0 ≠ 0
  symm_vac : ∀ a, S v0 a = S a v0
  qdim_ge_one : ∀ a, 1 ≤ qdimOf S v0 a
  bound : ∀ a b, ‖S a b‖ ≤ (S v0 v0).re * qdimOf S v0 a * qdimOf S v0 b

/-- **Huang's input, reduced.** For a nice VOA, Zhu's `ρ(S)` on a complete irredundant family has
`S₀₀ ≠ 0`, a symmetric vacuum row/column, `d_a ≥ 1` and Gannon's bound.

*Source.* Huang (2008): `Rep V` is modular, `ρ(S)` is symmetric and `S_{a0}/S_{00}` is the
categorical dimension, nonzero; pseudo-unitarity identifies categorical with Frobenius–Perron
dimensions, so `d_a ≥ 1` (ENO 2005); Gannon (2005) (4.2a) / GR (2.35) for the bound. -/
def HuangSInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        HuangSData D.repS v0

/-- **The full positivity package from the reduced Huang input**, the reality/positivity of
the vacuum column being supplied by `vacColumn_mem_K`. -/
theorem huangSPositivityInput_of (hRat : DLMRationalityInput.{u})
    (hS : HuangSInput.{u, w}) : HuangSPositivityInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0
  have hH := hS 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  obtain ⟨⟨qc, hqc⟩, hqh⟩ := hRat 𝒱 W hNice.1
  have hc : W.centralCharge.im = 0 := by rw [← hqc]; simp
  have hreal : ∀ i, (D.h i).im = 0 := by
    intro i
    obtain ⟨q, hq⟩ := hqh _ (D.Mfam i).isMod (D.Mfam i).irreducible _ (D.hasWeight i)
    rw [← hq]; simp
  have hK := fun a => vacColumn_mem_K hNice D hZ hirr v0 hv0 hreal hc a
  have h00 := hK v0
  have hpos : 0 < (D.repS v0 v0).re := by
    refine lt_of_le_of_ne h00.2 (fun h => hH.vac_ne_zero ?_)
    exact Complex.ext h.symm h00.1
  refine
    { vac_real := h00.1
      vac_pos := hpos
      symm_vac := hH.symm_vac
      qdim_real := fun a => ?_
      qdim_ge_one := hH.qdim_ge_one
      bound := hH.bound }
  have ea : D.repS a v0 = ((D.repS a v0).re : ℂ) := Complex.ext (by simp) (by simp [(hK a).1])
  have e0 : D.repS v0 v0 = ((D.repS v0 v0).re : ℂ) := Complex.ext (by simp) (by simp [h00.1])
  rw [ea, e0, ← Complex.ofReal_div]
  simp

/-- **`IModData` from three inputs**: the PBW datum, DLM rationality of `c` and `h`, and the
reduced Huang input. -/
theorem iModData_of_reduced_inputs (hPBW : ZhuPBWBottomInput.{u})
    (hRat : DLMRationalityInput.{u}) (hS : HuangSInput.{u, u + 1}) : IModData.{u} :=
  iModData_of_inputs hPBW (dlmRationalWeightsInput_of hRat) (huangSPositivityInput_of hRat hS)

/-- The same with the PBW datum supplied by the theorem `VOA.pbw`. -/
theorem iModData_of_reduced_pbw_inputs (hRat : DLMRationalityInput.{u})
    (hS : HuangSInput.{u, u + 1}) : IModData.{u} :=
  iModData_of_reduced_inputs zhuPBWBottomInput_of_pbw hRat hS

end VOA.Huang.IModDataReduced
