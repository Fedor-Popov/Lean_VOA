/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.Inputs

/-!
# `ICongruenceGalois` split into its two published theorems

`ICongruenceGalois` (`Classification/COne/Inputs.lean`) bundles two different theorems:

* `DLNCongruenceInput` — Dong–Lin–Ng, *Congruence property in conformal field theory*, Algebra &
  Number Theory 9 (2015), Theorem I: the characters are `Γ(N)`-invariant for every level `N`;
* `GaloisSymmetryNontrivialInput` — the Galois symmetry `ρ(γ_ℓ)` = signed permutation
  (Coste–Gannon 1994; DLN 2015 via Ng–Schauenburg 2010), asked for **only for `ℓ ≢ ±1 (mod N)`**.

The cases `ℓ ≡ ±1 (mod N)` of the Galois symmetry are *proved* here from the congruence property
(`galoisCase_pm_one`): then `±γ ∈ Γ(N)` and `π = id`, `ε = 1`. In particular, at the levels
`N ∈ {1, 2, 3, 4, 6}` (where `(ℤ/N)ˣ = {±1}`) the Galois symmetry is a consequence of congruence.

## Main results

* `iCongruenceGalois_of_split` : `DLNCongruenceInput → GaloisSymmetryNontrivialInput →
  ICongruenceGalois`;
* `dlnCongruenceInput_of_iCongruenceGalois`, `galoisSymmetryNontrivialInput_of_iCongruenceGalois`:
  the converse, so the split is exact (no strength is lost or added).
-/

open Complex

noncomputable section

namespace VOA.Huang.CongruenceGaloisSplit

open VOA VOA.Classification.COne

universe u

/-- **Congruence property** (Dong–Lin–Ng 2015, Theorem I: `ker ρ_V ⊇ Γ(n)`, `n` the order of
`ρ_V(T)`; every level is a multiple of `n`). For nice `V` with modular data `D` and any level
`N` of `D`, every character is `Γ(N)`-invariant. -/
def DLNCongruenceInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ D : VOA.Classification.COne.ModularData V, D.IsModularData → ∀ N : ℕ, D.IsLevel N →
      ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ a (τ : ℂ), 0 < τ.im →
        D.ch a (mobius γ τ) = D.ch a τ

/-- The Galois-symmetry clause of `ModularData.GaloisSymmetric` for one `ℓ` and one `γ`. -/
def GaloisCase {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
    (D : VOA.Classification.COne.ModularData V) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Prop :=
  ∃ (π : D.ι ≃ D.ι) (ε : D.ι → ℂ), (∀ a, ε a = 1 ∨ ε a = -1) ∧
    ∀ a (τ : ℂ), 0 < τ.im → D.ch a (mobius γ τ) = ε a * D.ch (π a) τ

/-- **Galois symmetry for nontrivial `ℓ`** (Coste–Gannon 1994; Dong–Lin–Ng 2015, via
Ng–Schauenburg 2010 and Huang's MTC): for `ℓ` invertible modulo the level `N` with
`ℓ ≢ ±1 (mod N)` and `γ ≡ diag(ℓ, ℓ⁻¹) (mod N)`, `ρ(γ)` acts on characters as a signed
permutation. Strictly weaker than `∀ N, D.GaloisSymmetric N`. -/
def GaloisSymmetryNontrivialInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ D : VOA.Classification.COne.ModularData V, D.IsModularData → ∀ N : ℕ, D.IsLevel N →
      ∀ ℓ ℓ' : ℤ, ℓ * ℓ' ≡ 1 [ZMOD N] → ¬ ℓ ≡ 1 [ZMOD N] → ¬ ℓ ≡ -1 [ZMOD N] →
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ 0 0 ≡ ℓ [ZMOD N] → γ 1 1 ≡ ℓ' [ZMOD N] → γ 0 1 ≡ 0 [ZMOD N] → γ 1 0 ≡ 0 [ZMOD N] →
        GaloisCase D γ

/-- `-γ` acts on `ℂ` like `γ`. -/
theorem mobius_neg (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℂ) :
    mobius (-γ) τ = mobius γ τ := by
  simp only [mobius, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
  rw [show -(γ 0 0 : ℂ) * τ + -(γ 0 1 : ℂ) = -((γ 0 0 : ℂ) * τ + γ 0 1) by ring,
    show -(γ 1 0 : ℂ) * τ + -(γ 1 1 : ℂ) = -((γ 1 0 : ℂ) * τ + γ 1 1) by ring, neg_div_neg_eq]

theorem intCast_zmod_eq {N : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD N]) : (a : ZMod N) = b :=
  (ZMod.intCast_eq_intCast_iff a b N).2 h

/-- **The trivial Galois cases follow from congruence.** If the characters are
`Γ(N)`-invariant, then for `ℓ ≡ ±1 (mod N)` every `γ ≡ diag(ℓ, ℓ⁻¹)` acts trivially. -/
theorem galoisCase_pm_one {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {V : VertexOperatorAlgebra 𝒱} (D : VOA.Classification.COne.ModularData V) (N : ℕ)
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ a (τ : ℂ), 0 < τ.im →
      D.ch a (mobius γ τ) = D.ch a τ)
    (ℓ ℓ' : ℤ) (hℓℓ' : ℓ * ℓ' ≡ 1 [ZMOD N]) (hpm : ℓ ≡ 1 [ZMOD N] ∨ ℓ ≡ -1 [ZMOD N])
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h00 : γ 0 0 ≡ ℓ [ZMOD N]) (h11 : γ 1 1 ≡ ℓ' [ZMOD N]) (h01 : γ 0 1 ≡ 0 [ZMOD N])
    (h10 : γ 1 0 ≡ 0 [ZMOD N]) : GaloisCase D γ := by
  refine ⟨Equiv.refl _, fun _ => 1, fun _ => Or.inl rfl, fun a τ hτ => ?_⟩
  simp only [Equiv.refl_apply, one_mul]
  have e00 := intCast_zmod_eq h00
  have e11 := intCast_zmod_eq h11
  have e01 := intCast_zmod_eq h01
  have e10 := intCast_zmod_eq h10
  have ell := intCast_zmod_eq hℓℓ'
  push_cast at e00 e11 e01 e10 ell
  rcases hpm with h1 | h1
  · have el := intCast_zmod_eq h1
    push_cast at el
    have el' : (ℓ' : ZMod N) = 1 := by rw [el, one_mul] at ell; exact ell
    apply hΓ γ _ a τ hτ
    rw [CongruenceSubgroup.Gamma_mem]
    exact ⟨by rw [e00, el], e01, e10, by rw [e11, el']⟩
  · have el := intCast_zmod_eq h1
    push_cast at el
    have el' : (ℓ' : ZMod N) = -1 := by
      rw [el, neg_one_mul] at ell; rw [← neg_neg (ℓ' : ZMod N), ell]
    rw [← mobius_neg]
    apply hΓ (-γ) _ a τ hτ
    rw [CongruenceSubgroup.Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    exact ⟨by rw [e00, el, neg_neg], by rw [e01, neg_zero], by rw [e10, neg_zero],
      by rw [e11, el', neg_neg]⟩

/-- **`ICongruenceGalois` from its two halves**, the Galois half needed only for
`ℓ ≢ ±1 (mod N)`. -/
theorem iCongruenceGalois_of_split (hC : DLNCongruenceInput.{u})
    (hG : GaloisSymmetryNontrivialInput.{u}) : ICongruenceGalois.{u} := by
  intro 𝒱 _ _ V hV D hD N hN
  have hΓ := hC 𝒱 V hV D hD N hN
  refine ⟨hΓ, fun ℓ ℓ' hℓℓ' γ h00 h11 h01 h10 => ?_⟩
  by_cases hp : ℓ ≡ 1 [ZMOD N]
  · exact galoisCase_pm_one D N hΓ ℓ ℓ' hℓℓ' (Or.inl hp) γ h00 h11 h01 h10
  by_cases hm : ℓ ≡ -1 [ZMOD N]
  · exact galoisCase_pm_one D N hΓ ℓ ℓ' hℓℓ' (Or.inr hm) γ h00 h11 h01 h10
  exact hG 𝒱 V hV D hD N hN ℓ ℓ' hℓℓ' hp hm γ h00 h11 h01 h10

/-- The split loses nothing: `ICongruenceGalois` gives back the congruence half. -/
theorem dlnCongruenceInput_of_iCongruenceGalois (h : ICongruenceGalois.{u}) :
    DLNCongruenceInput.{u} :=
  fun 𝒱 _ _ V hV D hD N hN => (h 𝒱 V hV D hD N hN).1

/-- … and the Galois half. -/
theorem galoisSymmetryNontrivialInput_of_iCongruenceGalois (h : ICongruenceGalois.{u}) :
    GaloisSymmetryNontrivialInput.{u} :=
  fun 𝒱 _ _ V hV D hD N hN ℓ ℓ' hℓℓ' _ _ γ h00 h11 h01 h10 =>
    (h 𝒱 V hV D hD N hN).2 ℓ ℓ' hℓℓ' γ h00 h11 h01 h10

end VOA.Huang.CongruenceGaloisSplit
