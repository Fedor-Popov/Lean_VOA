/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.DLNBridge

/-!
# The categorical half of the DLN bridge

`DLNBridge.ZhuProjectiveCongruenceInput` (projective congruence of Zhu's representation) is
reduced here to two independent contracts:

* `NSProjectiveCongruenceAll` — Ng–Schauenburg's Theorem 6.8 for every modular category in the
  abstract Ng–Schauenburg formalization (`NgSchauenburg.ProjectiveCongruenceTheorem`);
* `ZhuModularRepresentationInput` — DLN Theorem 3.10(ii): Zhu's representation `ρ_V` is a
  modular representation of the modular tensor category of `V`, i.e. after a relabelling
  `e : F.Label ≃ D.ι` one has `ρ_V(S) = a · S_cat` and `ρ_V(T) = b · diag(θ)` for some nonzero
  scalars `a, b`, with `S_cat` the Ng–Schauenburg (1.6) matrix `NgSchauenburg.categoricalS`.

The transport of a matrix representation to the linear-equivalence representations used by the
Ng–Schauenburg files (`matrixRepToLinear`) is constructed and proved here.

Source for the bridge Prop: Dong–Lin–Ng, arXiv:1201.6644v7, Theorem 3.10 (with Huang's
Theorem 3.9 = Huang 2008, Thm 4.1, for the modular tensor category `C_V`).  It is a TRUE
published statement; it is quantified existentially over the modular category, so universe
parameters may be chosen freely (a small skeletal model of `C_V` exists).
-/

noncomputable section

namespace VOA.Huang.DLNBridge

open CategoryTheory MonoidalCategory Limits
open VOA VOA.Classification.COne VOA.Huang.DLN VOA.Huang.NgSchauenburg CongruenceSubgroup

universe u v w

/-! ## Transport of matrix representations -/

section Transport

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A matrix representation, acting on column vectors. -/
def matrixRepToLinear (g : SL2Z →* Matrix κ κ ℂ) : SL2Z →* ((κ → ℂ) ≃ₗ[ℂ] (κ → ℂ)) where
  toFun γ :=
    { toFun := fun z => (g γ).mulVec z
      map_add' := fun z z' => Matrix.mulVec_add _ _ _
      map_smul' := fun c z => by simp [Matrix.mulVec_smul]
      invFun := fun z => (g γ⁻¹).mulVec z
      left_inv := fun z => by
        simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
      right_inv := fun z => by
        simp only [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one,
          Matrix.one_mulVec] }
  map_one' := by
    ext z i
    simp
  map_mul' γ δ := by
    ext z i
    simp [Matrix.mulVec_mulVec]

theorem matrixRepToLinear_apply (g : SL2Z →* Matrix κ κ ℂ) (γ : SL2Z) (z : κ → ℂ) (i : κ) :
    matrixRepToLinear g γ z i = ∑ j, g γ i j * z j := rfl

/-- Scalar action of the transported representation forces a scalar matrix. -/
theorem matrix_eq_smul_of_linear (g : SL2Z →* Matrix κ κ ℂ) (γ : SL2Z) (c : ℂ)
    (h : ∀ z, matrixRepToLinear g γ z = c • z) : g γ = c • (1 : Matrix κ κ ℂ) := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [matrixRepToLinear_apply] at this
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul] at this
  rw [this]
  simp [Matrix.one_apply]

/-- Reindexing a matrix representation along `e : κ ≃ ι`. -/
def reindexRep {ι : Type*} [Fintype ι] [DecidableEq ι] (e : κ ≃ ι) (g : SL2Z →* Matrix ι ι ℂ) :
    SL2Z →* Matrix κ κ ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ e.symm).toAlgHom.toRingHom.toMonoidHom.comp g

theorem reindexRep_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (e : κ ≃ ι)
    (g : SL2Z →* Matrix ι ι ℂ) (γ : SL2Z) (i j : κ) :
    reindexRep e g γ i j = g γ (e i) (e j) := by
  simp [reindexRep, Matrix.reindexAlgEquiv_apply]

end Transport

/-! ## The contracts -/

/-- **Ng–Schauenburg Theorem 6.8 for every modular category** (in the abstract NS
formalization; `ProjectiveCongruenceTheorem` is the faithful transcription). -/
def NSProjectiveCongruenceAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F), ProjectiveCongruenceTheorem F M

/-- **DLN Theorem 3.10(ii): Zhu's representation is a modular representation of `C_V`.**
There is a modular category (in the Ng–Schauenburg formalization) whose simple labels are
identified with `D.ι` so that Zhu's `ρ(S)` and `ρ(T)` are nonzero multiples of the categorical
`S` (NS convention (1.6)) and the twist matrix. -/
def ZhuModularRepresentationInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
      (D' : VOA.ModularData V D.ι), IsZhuDatum D hD D' →
      ∃ (C : Type w) (_ : Category.{v} C) (_ : MonoidalCategory C) (_ : RightRigidCategory C)
        (_ : Preadditive C) (_ : Linear ℂ C) (_ : MonoidalPreadditive C)
        (_ : MonoidalLinear ℂ C) (_ : HasKernels C) (_ : HasFiniteBiproducts C)
        (_ : BraidedCategory C) (F : SphericalFusion C) (M : Modular F)
        (e : F.Label ≃ D.ι) (a b : ℂˣ),
        (∀ i j, D'.rep ModularGroup.S (e i) (e j) = (a : ℂ) * categoricalS F i j) ∧
        (∀ i, D'.rep ModularGroup.T (e i) (e i) = (b : ℂ) * M.twistScalar i) ∧
        (∀ i j, i ≠ j → D'.rep ModularGroup.T (e i) (e j) = 0)

/-- **Projective congruence of Zhu's representation from NS 6.8 and DLN 3.10.** -/
theorem zhuProjectiveCongruence_of_NS (hNS : NSProjectiveCongruenceAll.{v, w})
    (hB : ZhuModularRepresentationInput.{u, v, w}) : ZhuProjectiveCongruenceInput.{u} := by
  intro 𝒱 _ _ V hV D hD D' hZD
  obtain ⟨C, _, _, _, _, _, _, _, _, _, _, F, M, e, a, b, hS, hT, hT'⟩ := hB 𝒱 V hV D hD D' hZD
  classical
  let ρ := matrixRepToLinear (reindexRep e D'.rep)
  have hmod : IsModularRepresentation F M ρ := by
    refine ⟨a, b, fun z i => ?_, fun z i => ?_⟩
    · change matrixRepToLinear (reindexRep e D'.rep) ModularGroup.S z i = _
      rw [matrixRepToLinear_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [reindexRep_apply, hS, mul_assoc]
    · change matrixRepToLinear (reindexRep e D'.rep) ModularGroup.T z i = _
      rw [matrixRepToLinear_apply, Finset.sum_eq_single i]
      · rw [reindexRep_apply, hT]
      · intro j _ hji
        rw [reindexRep_apply, hT' i j (Ne.symm hji), zero_mul]
      · simp
  obtain ⟨hpos, hall⟩ := hNS C F M
  obtain ⟨hproj, -⟩ := hall ρ hmod
  refine ⟨fsExponent F, hpos, fun γ hγ => ?_⟩
  obtain ⟨c, hc⟩ := hproj γ ((NSFinish.inPrincipalCongruence_iff _ γ).mpr hγ)
  refine ⟨(c : ℂ), ?_⟩
  have hm := matrix_eq_smul_of_linear (reindexRep e D'.rep) γ c hc
  ext i j
  have := congrFun (congrFun hm (e.symm i)) (e.symm j)
  rw [reindexRep_apply] at this
  simp only [Equiv.apply_symm_apply] at this
  rw [this]
  simp [Matrix.one_apply]

/-- **Both classification inputs from NS 6.8, DLN 3.10, DLN 2.3 and DLN II(iv).** -/
theorem dln_inputs_of_NS (hNS : NSProjectiveCongruenceAll.{v, w})
    (hB : ZhuModularRepresentationInput.{u, v, w}) (hlift : MatrixDLNLifting)
    (hW : ZhuGaloisWordInput.{u}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_contracts (zhuProjectiveCongruence_of_NS hNS hB) hlift hW

end VOA.Huang.DLNBridge
