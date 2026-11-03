/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.ZhuRepInput

/-!
# The Galois twist law for Zhu's representation, reduced to modular categories

`DLNBridge.ZhuGaloisTwistInput` (the Coste–Gannon signed-row law together with the
square-Galois twist law up to a scalar) is a theorem about the modular tensor category `Rep V`:
Dong–Lin–Ng prove the twist half categorically (DLN 2015, Lemma 4.2, §5, via generalized
Frobenius–Schur indicators), not from the congruence property of `ρ_V`.  With DLN 3.10(ii)
proved (`zhuModularRepresentationInput_holds`), we reduce it to the VOA-free statement
`NSGaloisTwistAll` about an arbitrary modular category in the Ng–Schauenburg formalization and
an arbitrary linear representation `ρ` of `SL(2, ℤ)` with `ρ(S) = a S_cat`, `ρ(T) = b diag(θ)`.

* `zhuGaloisTwistInput_of_NS : NSGaloisTwistAll.{0, 0} → ZhuGaloisTwistInput`;
* `dln_inputs_of_categorical : NSProjectiveCongruenceAll.{0, 0} → MatrixDLNLifting →
  NSGaloisTwistAll.{0, 0} → DLNCongruenceInput ∧ GaloisSymmetryNontrivialInput` — all three
  remaining contracts are VOA-free.

**Truth of `NSGaloisTwistAll`** (literature, not machine-checked).  For `ρ` as above,
`ρ(S)⁴ = 1` and `S_cat² = dim(C) · C` force `ρ(S)² = ±C`; the Galois conjugates of the fusion
characters `S_{ij}/S_{0j}` are fusion characters, and `ρ(S)_{0j} = a d_j` with
`Σ_i s_{ij} s_{ij*} = ±1` gives `σ(s_{0j}) = ± s_{0,π j}`; with the symmetry of `S_cat` this is
the signed-row law `σ(s) = G s = s G⁻¹`.  The twist law `θ_{π i} = σ²(θ_i)` is DLN Theorem II(iii)
(their Lemma 4.2); writing `t = b θ` it becomes `G t = β t^{x²} G` with `β = b^{1 - x²}`.  The
hypothesis `ρ(T)^N = 1` gives `b^N = 1` (as `θ_𝟙 = 1`), hence `θ^N = 1` and `σ(t) = t^x`
for `σ` extending `ζ_N ↦ ζ_N^x`.
-/

noncomputable section

namespace VOA.Huang.ZhuRep

open CategoryTheory MonoidalCategory Limits
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.TensorCat.RepPackaging
  VOA.Huang.HuangRigid VOA.Huang.HuangModularity VOA.Huang.NgSchauenburg
  VOA.Huang.DLNBridge VOA.Huang.DLN VOA.Huang.NSFinish

universe u v w

open Classical in
/-- **DLN Theorem II(ii)–(iii) with Coste–Gannon, for an abstract modular category**: for every
linear representation `ρ` of `SL(2, ℤ)` on the simple labels with `ρ(S) = a S_cat`,
`ρ(T) = b diag(θ)` and `ρ(T)^N = 1`, and every `x y` with `x y ≡ 1 (mod N)`, there are a field
automorphism `σ` of `ℂ` acting as `ζ ↦ ζ^x` on the eigenvalues of `ρ(T)` and a signed
permutation matrix `G` with `σ(s) = G s`, `σ(s) G = s` and `G t = β t^{x²} G` for some scalar
`β`.  VOA-free; TRUE (DLN 2015 Lemma 4.2 / Theorem II(iii); see the module docstring). -/
def NSGaloisTwistAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F) (ρ : SL2Z →* Matrix F.Label F.Label ℂ) (a b : ℂˣ),
    (∀ i j, ρ ModularGroup.S i j = (a : ℂ) * categoricalS F i j) →
    (∀ i, ρ ModularGroup.T i i = (b : ℂ) * M.twistScalar i) →
    (∀ i j, i ≠ j → ρ ModularGroup.T i j = 0) →
    ∀ N : ℕ, 0 < N → ρ ModularGroup.T ^ N = 1 → ∀ x y : ℤ, x * y ≡ 1 [ZMOD N] →
      ∃ (σ : ℂ ≃+* ℂ) (G : Matrix F.Label F.Label ℂ), IsSignedPermutation G ∧
        mapσ σ (ρ ModularGroup.S) = G * ρ ModularGroup.S ∧
        mapσ σ (ρ ModularGroup.S) * G = ρ ModularGroup.S ∧
        mapσ σ (ρ ModularGroup.T) = ρ (ModularGroup.T ^ x) ∧
        ∃ β : ℂ, G * ρ ModularGroup.T = β • (ρ (ModularGroup.T ^ (x * x)) * G)

/-- `A ^ n = 1` does not depend on the decidable-equality instance. -/
theorem matrix_pow_eq_one_of_inst {κ : Type*} [Fintype κ] (i1 i2 : DecidableEq κ)
    (A : Matrix κ κ ℂ) (n : ℕ) (h : letI := i1; A ^ n = 1) : letI := i2; A ^ n = 1 := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  exact h

/-- **The Galois twist law for Zhu's representation from the categorical statement**,
through the proved DLN 3.10(ii) model. -/
theorem zhuGaloisTwistInput_of_NS (h : NSGaloisTwistAll.{0, 0}) : ZhuGaloisTwistInput.{u} := by
  intro 𝒱 _ _ V hV D hD D' hZD N hN x y hxy
  obtain ⟨r⟩ := huangRigidityInput_holds 𝒱 V hV D hD
  letI := r
  have hS0 : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
  have hb0 : modularTEntry V (0 : ℂ) ≠ 0 := modularTEntry_ne_zero _
  obtain ⟨hS, hT, hT'⟩ := zhu_rep_model hV D hD D' hZD
  have hTN := zhu_T_pow_eq_one_of_level D hD D' hZD hN
  classical
  let ρ' : SL2Z →* Matrix (modelSphericalFusion hV D hD).Label
      (modelSphericalFusion hV D hD).Label ℂ :=
    { toFun := fun γ => D'.rep γ
      map_one' := by convert D'.rep.map_one
      map_mul' := fun γ δ => D'.rep.map_mul γ δ }
  obtain ⟨σ, G, hG, h1, h2, h3, β, h4⟩ := h (canonicalModel hV D hD).C
    (modelSphericalFusion hV D hD) (modelModular hV D hD) ρ' (Units.mk0 _ hS0)
    (Units.mk0 _ hb0) hS hT hT' N hN.1 (matrix_pow_eq_one_of_inst _ _ _ N hTN) x y hxy
  exact ⟨σ, G, by convert hG, h1, h2, h3, β, h4⟩

/-- **Both classification inputs from three VOA-free contracts**: Ng–Schauenburg 6.8
(`NSProjectiveCongruenceAll`), DLN 2.3 (`MatrixDLNLifting`) and the categorical Galois twist law
(`NSGaloisTwistAll`). -/
theorem dln_inputs_of_categorical (hNS : NSProjectiveCongruenceAll.{0, 0})
    (hlift : MatrixDLNLifting) (hG : NSGaloisTwistAll.{0, 0}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_NS_lifting_twist hNS hlift (zhuGaloisTwistInput_of_NS hG)

end VOA.Huang.ZhuRep
