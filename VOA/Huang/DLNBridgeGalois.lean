/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.DLNBridgeCategorical
import VOA.Huang.NSFinishGalois

/-!
# The Galois word for Zhu's representation from the (scaled) square-Galois twist law

`DLNBridge.ZhuGaloisWordInput` (DLN Theorem II(iv) for `ρ_V`) is derived here from the congruence
property and the weaker, normalization-free contract `ZhuGaloisTwistInput`: some automorphism
`σ` of `ℂ` acting as `ζ ↦ ζ^a` on the `T`-eigenvalues, with a signed permutation matrix `G`,
satisfies the Coste–Gannon law `σ(s) = G s = s G⁻¹` and the twist law `G t = β · t^{a²} G` for
**some** scalar `β`.  The scalar is eliminated by `NSFinish.galoisWord_of_scaledTwist`
(DLN §4.3).
-/

noncomputable section

namespace VOA.Huang.DLNBridge

open VOA VOA.Classification.COne VOA.Huang.DLN VOA.Huang.DLNAlg VOA.Huang.NSFinish
  VOA.Huang.HuangModularity

universe u v w

/-- A signed permutation matrix is fixed by every ring automorphism. -/
theorem mapσ_signedPermutation {κ : Type*} [Fintype κ] [DecidableEq κ] {G : Matrix κ κ ℂ}
    (hG : IsSignedPermutation G) (σ : ℂ ≃+* ℂ) : mapσ σ G = G := by
  obtain ⟨π, ε, hε, hGe⟩ := hG
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.coe_toRingHom, hGe]
  split_ifs
  · rcases hε a with h | h <;> simp [h]
  · simp

/-- **The square-Galois twist law for Zhu's representation, up to a scalar** (DLN 2015,
Corollary 4.4 / Theorem II(iii) via Theorem 3.10; Coste–Gannon for the signed-row half).
For every level `N` and `a b ≡ 1 (mod N)` there are an automorphism `σ` of `ℂ` with
`σ(ρ T) = ρ(T^a)` and a signed permutation matrix `G` with `σ(s) = G s`, `σ(s) G = s` and
`G t = β · t^{a²} G` for some scalar `β`.  (DLN prove it with `β = 1`; the scalar is allowed
so that the contract only needs the twist law up to the normalization of `ρ`.)  Existence of
`σ` uses the standard extension of `ζ_N ↦ ζ_N^a` from `ℚ(ζ_N)` to `ℂ`. -/
def ZhuGaloisTwistInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
      (D' : VOA.ModularData V D.ι), IsZhuDatum D hD D' →
      ∀ N : ℕ, D.IsLevel N → ∀ a b : ℤ, a * b ≡ 1 [ZMOD N] →
        ∃ (σ : ℂ ≃+* ℂ) (G : Matrix D.ι D.ι ℂ), IsSignedPermutation G ∧
          mapσ σ (D'.rep ModularGroup.S) = G * D'.rep ModularGroup.S ∧
          mapσ σ (D'.rep ModularGroup.S) * G = D'.rep ModularGroup.S ∧
          mapσ σ (D'.rep ModularGroup.T) = D'.rep (ModularGroup.T ^ a) ∧
          ∃ β : ℂ, G * D'.rep ModularGroup.T = β • (D'.rep (ModularGroup.T ^ (a * a)) * G)

/-- **The DLN Galois word from congruence and the scaled twist law.** -/
theorem zhuGaloisWord_of_twist (hC : ZhuCongruenceInput.{u}) (hT : ZhuGaloisTwistInput.{u}) :
    ZhuGaloisWordInput.{u} := by
  intro 𝒱 _ _ V hV D hD D' hZD N hN a b hab
  have hk := kernel_at_level hC hV D hD D' hZD hN
  obtain ⟨σ, G, hG, hrow, hcol, hTa, β, htw⟩ := hT 𝒱 V hV D hD D' hZD N hN a b hab
  have h := (galoisWord_of_scaledTwist D'.rep hk hab σ G (mapσ_signedPermutation hG σ) hrow
    hcol hTa β htw).1
  rw [← h]
  exact hG

/-- **`DLNCongruenceInput` and `GaloisSymmetryNontrivialInput` from four contracts**:
Ng–Schauenburg 6.8 (`NSProjectiveCongruenceAll`), DLN 3.10 (`ZhuModularRepresentationInput`),
DLN 2.3 (`MatrixDLNLifting`) and the scaled twist law (`ZhuGaloisTwistInput`).  The exact level
(DLN Lemma A.1) and the scalar elimination (DLN §4.3) are proved. -/
theorem dln_inputs_of_NS_twist (hNS : NSProjectiveCongruenceAll.{v, w})
    (hB : ZhuModularRepresentationInput.{u, v, w}) (hlift : MatrixDLNLifting)
    (hT : ZhuGaloisTwistInput.{u}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} := by
  have hC := zhuCongruence_of_projective (zhuProjectiveCongruence_of_NS hNS hB) hlift
  exact ⟨dlnCongruenceInput_of_zhuCongruence hC,
    galoisSymmetryNontrivialInput_of_word hC (zhuGaloisWord_of_twist hC hT)⟩

end VOA.Huang.DLNBridge
