/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangRigidAssembly
import VOA.Huang.HuangModularityTrace
import VOA.Huang.HuangModularityZhu

/-!
# Huang's modularity input: reduction to the dimension clause and the symmetry of `S`

`HuangRigid.HuangModularityInput` has three clauses for the canonical model and its (unique) twist
pivotal structure `modelPivotal`: `SMatchInput` (`S_ab = S₀₀ S̃_ab` or `S₀₀ conj S̃_ab`),
`QDimMatchInput` (`dim M_a = d_a`), `QDimTensorInput` (`dim(M_a ⊗ M_b) = d_a d_b`).
This file proves:

* `fusionN_eq` — the categorical multiplicities of any structural model are the VOA fusion rules,
  `N_{ij}^c = fusionRule(M_i, M_j; M_c)`;
* `qDimTensorInput_of_qDimMatch` — `QDimMatchInput → QDimTensorInput`, for EVERY pivotal
  structure (trace additivity `qdim_tensor_eq_sum` + `Σ_c N_ab^c d_c = d_a d_b`, the vacuum
  column of `D.S`);
* `sMatchInput_of_qDimMatch` — `QDimMatchInput` and the symmetry `S_ab = S_ba` give
  `SMatchInput` (in the orientation `S_ab = S₀₀ conj S̃_ab`): the categorical balancing formula
  `S̃_ab T_a T_b = Σ_c N_ab^c T_c dim X_c` (`sTilde_mul_T`) against the identity
  `S₀₀ Σ_c N_ab^c T_c⁻¹ d_c = T_a⁻¹ T_b⁻¹ S_ab` (`balancing_S`, from Huang's Theorem 5.2 and
  `TSTST = S` in Zhu's representation);
* `qDimMatchInput_of_sMatch` — conversely `SMatchInput → QDimMatchInput` (`S̃_{a,vac} = dim X_a`);
* `huangModularityInput_of_qdim : HuangQDimInput → SSymmetricInput → HuangModularityInput`
  and `huangRepInput_of_qdim`, with the converse `huangQDimInput_of_modularity`.

Both named inputs are proved downstream: `SSymmetricInput` in `HuangModularitySymm`
(`sSymmetricInput_holds`, Huang's Theorem 5.6) and `HuangQDimInput` in `HuangModularityQDim`
(`huangQDimInput_holds`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HuangModularity

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Module VOA
  VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.TensorCat.BraidRibbon
  VOA.Huang.TensorCat.RepPackaging VOA.Huang.Tannakian VOA.Huang.HuangRigid
  VOA.Huang.FusionProduct VOA.Huang.SPinning

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

section Model

variable (hW : Nice W) (M : StructuralModel W) (D : VOA.Classification.COne.ModularData W)
  (hD : D.IsModularData) [RightRigidCategory M.C]

include hW in
/-- **The categorical multiplicities are the VOA fusion rules.** -/
theorem fusionN_eq (i j c : D.ι) :
    FusionCategory.N (F := M.fusion D hD) i j c = fus D i j c := by
  letI F := M.fusion D hD
  letI := monoidalCategoryOfStronglyRational_pbw M.F M.stronglyRational
  letI := M.monoidalFunctor
  change mult (F.simple i ⊗ F.simple j) c = _
  rw [mult_eq_finrank_hom_to]
  let e1 : (F.simple i ⊗ F.simple j ⟶ F.simple c) ≃ₗ[ℂ]
      (M.E.functor.obj (F.simple i ⊗ F.simple j) ⟶ M.E.functor.obj (F.simple c)) :=
    LinearEquiv.ofBijective (M.E.functor.mapLinearMap ℂ)
      ⟨M.E.functor.map_injective, M.E.functor.map_surjective⟩
  let e2 : (M.E.functor.obj (F.simple i ⊗ F.simple j) ⟶ M.E.functor.obj (F.simple c)) ≃ₗ[ℂ]
      (tensorObj M.F (Ordinary.of (D.module i)) (Ordinary.of (D.module j)) ⟶
        Ordinary.of (D.module c)) := Linear.homCongr ℂ
    ((Functor.Monoidal.μIso M.E.functor (F.simple i) (F.simple j)).symm ≪≫
      (modelSimpleIso M.E D i ⊗ᵢ modelSimpleIso M.E D j)) (modelSimpleIso M.E D c)
  let e3 : (tensorObj M.F (Ordinary.of (D.module i)) (Ordinary.of (D.module j)) ⟶
        Ordinary.of (D.module c)) ≃ₗ[ℂ]
      IntertwiningOperator (D.module i) (D.module j) (D.module c) := homEquiv ((M.F (Ordinary.of (D.module i)) (Ordinary.of (D.module j))).universal
    (D.carrier c) (D.module c))
  rw [e1.finrank_eq, e2.finrank_eq]
  exact e3.finrank_eq

include hW hD in
/-- **Dimension multiplicativity from the dimension clause**, for any pivotal structure. -/
theorem qDimTensorInput_of_qDimMatch (P : PivotalStructure M.C) (hq : M.QDimMatchInput D P) :
    M.QDimTensorInput D P := by
  letI F := M.fusion D hD
  intro a b
  have h := qdim_tensor_eq_sum P a b
  change P.qdim (F.simple a ⊗ F.simple b) = _
  rw [h]
  simp_rw [fusionN_eq hW M D hD]
  have hq' : ∀ c, P.qdim (F.simple c) = (D.d c : ℂ) := hq
  simp_rw [hq']
  exact sum_fusion_d hW D hD a b

theorem star_twistOf (x : ℝ) : star (twistOf (x : ℂ)) = (twistOf (x : ℂ))⁻¹ := by
  simp only [twistOf]
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

include hW in
/-- **The `S`-matrix clause from the dimension clause and the symmetry of `S`**, in the
orientation `S_ab = S₀₀ conj S̃_ab`. -/
theorem sMatchInput_of_qDimMatch (P : PivotalStructure M.C) (hdual : M.RibbonDualInput)
    (hq : M.QDimMatchInput D P) (hsym : ∀ a b, D.S a b = D.S b a) :
    M.SMatchInput D hD (M.ribbon P hdual) := by
  letI F := M.fusion D hD
  intro a b
  right
  set R := M.ribbon P hdual
  have hT : ∀ x, R.T x = twistOf (D.h x : ℂ) := fun x => M.ribbon_T D hD P hdual x
  have hq' : ∀ c, R.qdim (F.simple c) = (D.d c : ℂ) := hq
  have hcat := sTilde_mul_T R a b
  simp_rw [fusionN_eq hW M D hD, hT, hq'] at hcat
  have hc := congrArg star hcat
  simp only [star_mul', star_sum, star_natCast, Complex.star_def, Complex.conj_ofReal] at hc
  simp only [← Complex.star_def] at hc
  have hh : ∀ x : D.ι, star (twistOf ((D.h x : ℚ) : ℂ)) = (twistOf ((D.h x : ℚ) : ℂ))⁻¹ := by
    intro x
    have := star_twistOf ((D.h x : ℚ) : ℝ)
    simpa using this
  simp only [hh] at hc
  have hb := balancing_S hW D hD hsym a b
  have hc' : star (R.sTilde a b) * ((twistOf ((D.h a : ℚ) : ℂ))⁻¹ * (twistOf ((D.h b : ℚ) : ℂ))⁻¹)
      = ∑ c : D.ι, (fus D a b c : ℂ) * ((twistOf ((D.h c : ℚ) : ℂ))⁻¹ * (D.d c : ℂ)) := hc
  rw [← hc'] at hb
  have hta : twistOf ((D.h a : ℚ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have htb : twistOf ((D.h b : ℚ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have : (twistOf ((D.h a : ℚ) : ℂ))⁻¹ * (twistOf ((D.h b : ℚ) : ℂ))⁻¹ *
      ((D.S00 : ℂ) * star (R.sTilde a b)) =
      (twistOf ((D.h a : ℚ) : ℂ))⁻¹ * (twistOf ((D.h b : ℚ) : ℂ))⁻¹ * D.S a b := by
    rw [← hb]; ring
  exact (mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hta) (inv_ne_zero htb)) this).symm

include hW in
/-- **The dimension clause from the `S`-matrix clause**: `S̃_{a,vac} = dim X_a`. -/
theorem qDimMatchInput_of_sMatch (P : PivotalStructure M.C) (hdual : M.RibbonDualInput)
    (hS : M.SMatchInput D hD (M.ribbon P hdual)) : M.QDimMatchInput D P := by
  letI F := M.fusion D hD
  intro a
  set R := M.ribbon P hdual
  -- `S̃_{a,vac} T_a T_vac = Σ_c N_{a,vac}^c T_c dim X_c = T_a dim X_a`
  have hcat := sTilde_mul_T R a D.vac
  simp_rw [fusionN_eq hW M D hD] at hcat
  obtain ⟨-, hunit, -⟩ := zhu_facts hW D hD
  simp only [hunit, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hcat
  have hT0 : R.T D.vac = 1 := by
    rw [M.ribbon_T D hD P hdual, hD.h_vac]; simp
  have hTa : R.T a ≠ 0 := RibbonStructure.T_ne_zero R a
  rw [hT0, mul_one] at hcat
  have hs : R.sTilde a D.vac = R.qdim (F.simple a) := mul_right_cancel₀ hTa (by rw [hcat]; ring)
  have hS0 : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
  have hv := hD.S_vac_right a
  change P.qdim (F.simple a) = _
  change R.qdim (F.simple a) = _
  rcases hS a D.vac with h | h
  · rw [hv, ← hs] at *
    exact (mul_left_cancel₀ hS0 h).symm
  · rw [hv] at h
    have h' := (mul_left_cancel₀ hS0 h).symm
    rw [hs] at h'
    rw [← star_star (R.qdim (F.simple a)), h', Complex.star_def, Complex.conj_ofReal]

end Model

/-! ## The two named residuals and the assembly -/

/-- **Huang's dimension theorem for the twist pivotal structure**: for the canonical model, every
right-dual choice, and the twist pivotal structure `modelPivotal`,
`dim M_a = d_a = S_{a,vac}/S_{vac,vac}` (Huang, *Rigidity and modularity of vertex tensor
categories*, CCM 10 (2008); equivalently `SMatchInput` at `b = vac`, `qDimMatchInput_of_sMatch`).
proved: `HuangModularityQDim.huangQDimInput_holds`. -/
def HuangQDimInput : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)
    (hW : Nice W) (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
    (r : RightRigidCategory (canonicalModel hW D hD).C),
    letI := r
    (canonicalModel hW D hD).QDimMatchInput D (modelPivotal (canonicalModel hW D hD))

/-- **Symmetry of the modular `S`-matrix** (Huang, *Vertex operator algebras and the Verlinde
conjecture*, CCM 10 (2008), Theorem 5.6; Zhu's `ρ(S)` on the irreducibles of a nice VOA).
Non-vacuous: it constrains `D.S`, which is pinned by `IsModularData.S_pinned`. Proved:
`HuangModularitySymm.sSymmetricInput_holds`. -/
def SSymmetricInput : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)
    (_hW : Nice W) (D : VOA.Classification.COne.ModularData W) (_hD : D.IsModularData)
    (a b : D.ι), D.S a b = D.S b a

/-- **Huang's modularity input from the dimension clause and the symmetry of `S`.** -/
theorem huangModularityInput_of_qdim (hq : HuangQDimInput.{u}) (hs : SSymmetricInput.{u}) :
    HuangModularityInput.{u} := by
  intro V _ _ W hW D hD r
  letI := r
  have hq' := hq V W hW D hD r
  refine ⟨?_, hq', ?_⟩
  · exact sMatchInput_of_qDimMatch hW _ D hD _ _ hq' (hs V W hW D hD)
  · exact qDimTensorInput_of_qDimMatch hW _ D hD _ hq'

/-- The converse: the dimension clause is part of `HuangModularityInput`. -/
theorem huangQDimInput_of_modularity (h : HuangModularityInput.{u}) : HuangQDimInput.{u} :=
  fun V _ _ W hW D hD r => (h V W hW D hD r).2.1

/-- **`HuangRepInput` from the two named residuals.** -/
theorem huangRepInput_of_qdim (hq : HuangQDimInput.{u}) (hs : SSymmetricInput.{u}) :
    HuangRepInput.{u} :=
  huangRepInput_of_modularity (huangModularityInput_of_qdim hq hs)

end VOA.Huang.HuangModularity
