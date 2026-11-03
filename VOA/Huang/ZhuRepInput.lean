/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.ZhuRepModel

/-!
# DLN Theorem 3.10(ii): Zhu's representation is a modular representation of `Rep V`

`zhuModularRepresentationInput_holds : DLNBridge.ZhuModularRepresentationInput.{u, 0, 0}`.

For a nice `V`, modular data `D` and any Zhu datum `D'` on the labels of `D`, the witness is the
canonical small model of `Rep V` (`canonicalModel`), with

* the Ng–Schauenburg spherical fusion structure `modelSphericalFusion` (pivotal `j = θ u`),
* the modular structure `modelModular`,
* the identity relabelling `e = Equiv.refl D.ι`,
* `a = S₀₀` and `b = e^{-2πi c/24}` (`modularTEntry V 0`):

`ρ(S)_{ij} = S₀₀ · S^{NS}_{ij}` and `ρ(T)_{ii} = e^{-2πic/24} · θ_i`, `ρ(T)_{ij} = 0` for `i ≠ j`.

Convention check (flagged in the task): the natural category `Rep V` (no reversed braiding) works;
the dual on the first index of the NS (1.6) matrix is absorbed by `S_{σa,b} = conj S_{ab}`
(`exists_charge_star`), which is proved, not assumed.

Universe remark: the Prop is universe-polymorphic in the category; it is proved here at
`Type 0`/`Category.{0}` (the canonical model is small).  That is the instance consumed by
`DLNBridge.dln_inputs_of_NS_twist` with `NSProjectiveCongruenceAll.{0, 0}`
(`dln_inputs_of_NS_lifting_twist`).
-/

noncomputable section

namespace VOA.Huang.ZhuRep

open CategoryTheory MonoidalCategory Limits
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.TensorCat.RepPackaging
  VOA.Huang.HuangRigid VOA.Huang.HuangModularity VOA.Huang.NgSchauenburg VOA.Huang.SPinning
  VOA.Huang.DLNBridge

universe u

/-- The three identities of DLN 3.10(ii) for the explicit model `modelSphericalFusion`,
`modelModular`, with `a = S₀₀`, `b = e^{-2πic/24}` and the identity relabelling. -/
theorem zhu_rep_model {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
    (hV : Nice V) (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
    [RightRigidCategory (canonicalModel hV D hD).C] (D' : VOA.ModularData V D.ι)
    (hZD : IsZhuDatum D hD D') :
    (∀ i j, D'.rep ModularGroup.S i j =
      (D.S00 : ℂ) * categoricalS (modelSphericalFusion hV D hD) i j) ∧
    (∀ i, D'.rep ModularGroup.T i i =
      modularTEntry V (0 : ℂ) * (modelModular hV D hD).twistScalar i) ∧
    (∀ i j, i ≠ j → D'.rep ModularGroup.T i j = 0) := by
  obtain ⟨hM, hh, hZ⟩ := hZD
  obtain ⟨Pr⟩ := ZhuModData.zhuPBWBottomInput_of_pbw 𝒱 V
  have htr : ∀ (a : D.ι) (v : 𝒱) (τ : UpperHalfPlane),
      traceFun D'.Mfam D'.h a v τ = D.trace a v τ := by
    intro a v τ
    rw [hM, hh]
    rfl
  have hSeq : D.S = D'.repS := S_eq_repS Pr hV.1.c2Cofinite D hD D' hZ htr
  obtain ⟨σ, hσ, hvac, -, hstar⟩ := exists_charge_star hV D hD
  refine ⟨fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · rw [D'.rep_S, Matrix.of_apply, ← hSeq]
    exact S_eq_S00_mul_categoricalS hV D hD σ hσ hvac hstar i j
  · rw [D'.rep_T, Matrix.of_apply, twistScalar_model, hh]
    simp only [VOA.modularRepT, if_true, hOf]
    rw [modularTEntry_eq]
    simp only [twistOf]
    ring
  · rw [D'.rep_T, Matrix.of_apply, hh]
    exact VOA.modularRepT_off_diag V (hOf D) hij

/-- **DLN Theorem 3.10(ii), proved**: Zhu's `ρ(S)`, `ρ(T)` are nonzero multiples of the
Ng–Schauenburg categorical `S` and twist matrix of the modular tensor category `Rep V`. -/
theorem zhuModularRepresentationInput_holds : ZhuModularRepresentationInput.{u, 0, 0} := by
  intro 𝒱 _ _ V hV D hD D' hZD
  obtain ⟨r⟩ := huangRigidityInput_holds 𝒱 V hV D hD
  letI := r
  have hS0 : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
  have hb0 : modularTEntry V (0 : ℂ) ≠ 0 := modularTEntry_ne_zero _
  obtain ⟨hS, hT, hT'⟩ := zhu_rep_model hV D hD D' hZD
  exact ⟨(canonicalModel hV D hD).C, inferInstance, inferInstance, r, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    modelSphericalFusion hV D hD, modelModular hV D hD, Equiv.refl D.ι, Units.mk0 _ hS0,
    Units.mk0 _ hb0, hS, hT, hT'⟩

/-- Projective congruence of Zhu's representation from Ng–Schauenburg 6.8 alone
(DLN 3.10 is proved). -/
theorem zhuProjectiveCongruence_of_NS' (hNS : NSProjectiveCongruenceAll.{0, 0}) :
    ZhuProjectiveCongruenceInput.{u} :=
  zhuProjectiveCongruence_of_NS hNS zhuModularRepresentationInput_holds

/-- **Both classification inputs from three contracts**: Ng–Schauenburg 6.8, DLN 2.3
(`MatrixDLNLifting`) and the scaled Galois twist law (`ZhuGaloisTwistInput`). -/
theorem dln_inputs_of_NS_lifting_twist (hNS : NSProjectiveCongruenceAll.{0, 0})
    (hlift : MatrixDLNLifting) (hT : ZhuGaloisTwistInput.{u}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_NS_twist hNS zhuModularRepresentationInput_holds hlift hT

end VOA.Huang.ZhuRep
