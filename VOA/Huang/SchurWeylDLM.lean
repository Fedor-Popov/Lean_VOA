/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.DistinctResiduals
import Mathlib.RepresentationTheory.Character

/-!
# Dong–Li–Mason Schur–Weyl duality for finite orbifolds

For a simple VOA `W` and a finite group `G ≤ Aut W`,

  `W = ⊕_{λ ∈ Irr G} E_λ ⊗ W_λ`,  `W_λ = Hom_G(E_λ, W)`,

with every `W_λ` a nonzero irreducible `W^G`-module and the `W_λ` pairwise inequivalent
(C. Dong, H. Li, G. Mason, *Compact automorphism groups of vertex operator algebras*, IMRN 1996,
no. 18, 913–921, main theorem — stated there for compact `G`, finite `G` included; for finite `G`
also Dong–Mason, *On quantum Galois theory*, Duke Math. J. 86 (1997), and Dong–Yamskulna,
Math. Z. 241 (2002), for the twisted generalization.  Theorem numbers not re-checked here).

## The statement

* `multSpace G σ : Submodule ℂ (E →ₗ[ℂ] 𝒱)` — `Hom_G(E, W)`, DLM's `W_λ` (a `G`-map from a
  finite-dimensional `E` lands in finitely many weights, so this is the algebraic
  `⊕_n Hom_G(E, W_n)`);
* `modeOp_comp_mem` — `W^G` acts on it by `φ ↦ u₍ₙ₎ ∘ φ` (`u ∈ W^G` commutes with `G`);
* `ModeStable` — a `W^G`-submodule;
* `DLMSchurWeyl : Prop` — for simple `W`, finite `G`, irreducible `σ`: (occurs) `multSpace ≠ ⊥`;
  (irreducible) every mode-stable `P ≤ multSpace` is `⊥` or everything; (inequivalent) for
  `σ ≇ σ'` irreducible, every linear map `multSpace σ → multSpace σ'` commuting with all `W^G`-modes
  is `0`.  These are exactly DLM's three clauses (for irreducible modules, "non-isomorphic" is
  equivalent to "no nonzero homomorphism").

## What is proved (unconditionally)

* `multSpaceTrivialEquiv`, `multSpaceTrivialEquiv_mode` — the trivial isotypic multiplicity module
  is `W^G` itself, with its adjoint action;
* `multSpace_trivial_ne_bot` — the trivial representation occurs (clause "occurs" for `λ = 1`);
* `gradedRep`, `intertwiningToMultSpace` (injective) — `Hom_G(E, W_n) ↪ Hom_G(E, W)`;
* `finrank_intertwining_grading` — **Molien's multiplicity formula**
  `dim Hom_G(E, W_n) = |G|⁻¹ Σ_g tr(g | W_n) χ_E(g⁻¹)`, generalizing `card_mul_finrank_orbifold`.

## The content of DLM — proved downstream

`dlmSchurWeyl_holds : DLMSchurWeyl` is proved in `SchurWeylDLMProof.lean` (with
`SchurWeylDLMProofDensity.lean`, `SchurWeylDLMProofOccurs.lean`): "occurs" via Dedekind's lemma for
the automorphisms of a simple VOA (`aut_sum_eq_zero_imp`), irreducibility and inequivalence via
Jacobson density for the mode algebra, Li's single-mode spanning lemma and averaging over `G`.
`SchurWeylDLMProofFinGen.lean` derives that `𝒱` is a finitely generated `W^G`-module.

(`multSpace`, `modeOp_comp_mem`, `ModeStable`, `intertwiningToMultSpace` accept `E` in any universe
— needed for the regular representation `ℂ^G`, `G ≤ Aut W : Type u`; `DLMSchurWeyl` itself still
quantifies over `E E' : Type`.)

## Is it needed by `ITannakian`?  No.

`ITannakian`'s consumer needs `V ≅ W^Γ` and `dim W_n`.  In `TannakianInterface.lean` both come
from the Huang–Kirillov–Lepowsky correspondence applied to the regular algebra, once
`Fun(G)^G = ℂ` is checked (`sum_leftTranslHom`); DLM is the converse statement and is not used.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.SchurWeyl

open VOA VOA.Classification.COne Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- `G ≤ Aut W` acting on the whole space `𝒱`. -/
def autRep (G : Subgroup (Aut W)) : Representation ℂ G 𝒱 where
  toFun g := (g : Aut W).toLinearEquiv.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem autRep_apply (G : Subgroup (Aut W)) (g : G) (v : 𝒱) :
    autRep G g v = (g : Aut W) v := rfl

/-- The mode `u₍ₙ₎` as a linear endomorphism of `𝒱`. -/
def modeOp (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (n : ℤ) : 𝒱 →ₗ[ℂ] 𝒱 :=
  VOA.mode (W.Y u) n

theorem modeOp_apply (u : 𝒱) (n : ℤ) (v : 𝒱) : modeOp W u n v = W.smul u n v := rfl

/-- The **multiplicity space** `Hom_G(E, W)` of a `G`-representation `E` in `W` (DLM's `V_λ`). -/
def multSpace (G : Subgroup (Aut W)) {E : Type*} [AddCommGroup E] [Module ℂ E]
    (σ : Representation ℂ G E) : Submodule ℂ (E →ₗ[ℂ] 𝒱) where
  carrier := {φ | ∀ (g : G) (x : E), (g : Aut W) (φ x) = φ (σ g x)}
  add_mem' {φ ψ} hφ hψ g x := by
    simp only [LinearMap.add_apply]
    rw [← hφ g x, ← hψ g x]
    exact map_add (g : Aut W).toLinearEquiv _ _
  zero_mem' g x := by
    simp only [LinearMap.zero_apply]
    exact map_zero (g : Aut W).toLinearEquiv
  smul_mem' c {φ} hφ g x := by
    simp only [LinearMap.smul_apply]
    rw [← hφ g x]
    exact map_smul (g : Aut W).toLinearEquiv _ _

/-- The orbifold `W^G` **acts on the multiplicity spaces** by post-composition with its modes:
for `u ∈ W^G`, `u₍ₙ₎` commutes with `G`, so `u₍ₙ₎ ∘ φ` is again `G`-equivariant. -/
theorem modeOp_comp_mem (G : Subgroup (Aut W)) {E : Type*} [AddCommGroup E] [Module ℂ E]
    (σ : Representation ℂ G E) {u : 𝒱} (hu : u ∈ (orbifold G).carrier) (n : ℤ)
    {φ : E →ₗ[ℂ] 𝒱} (hφ : φ ∈ multSpace G σ) : (modeOp W u n).comp φ ∈ multSpace G σ := by
  intro g x
  simp only [LinearMap.comp_apply, modeOp_apply]
  rw [Aut.map_smul, hu g g.2, hφ g x]

/-- A subspace of `Hom(E, W)` stable under all modes of `W^G`. -/
def ModeStable (G : Subgroup (Aut W)) {E : Type*} [AddCommGroup E] [Module ℂ E]
    (P : Submodule ℂ (E →ₗ[ℂ] 𝒱)) : Prop :=
  ∀ u ∈ (orbifold G).carrier, ∀ (n : ℤ), ∀ φ ∈ P, (modeOp W u n).comp φ ∈ P

theorem modeStable_multSpace (G : Subgroup (Aut W)) {E : Type*} [AddCommGroup E] [Module ℂ E]
    (σ : Representation ℂ G E) : ModeStable G (multSpace G σ) :=
  fun _ hu n _ hφ => modeOp_comp_mem G σ hu n hφ

/-- **Dong–Li–Mason Schur–Weyl duality (finite groups)** — see the module docstring for the
source and for why the three clauses are DLM's.  Proved: `dlmSchurWeyl_holds`
(`SchurWeylDLMProof.lean`); not used by `ITannakian`. -/
def DLMSchurWeyl : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)
    (G : Subgroup (Aut W)), W.IsSimple → Finite G →
    ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
      (σ : Representation ℂ G E), σ.IsIrreducible →
      multSpace G σ ≠ ⊥ ∧
      (∀ P : Submodule ℂ (E →ₗ[ℂ] 𝒱), P ≤ multSpace G σ → ModeStable G P →
        P = ⊥ ∨ P = multSpace G σ) ∧
      (∀ (E' : Type) [AddCommGroup E'] [Module ℂ E'] [FiniteDimensional ℂ E']
        (σ' : Representation ℂ G E'), σ'.IsIrreducible → IsEmpty (σ.Equiv σ') →
        ∀ T : multSpace G σ →ₗ[ℂ] multSpace G σ',
          (∀ u (hu : u ∈ (orbifold G).carrier) (n : ℤ) (φ : multSpace G σ),
            (T ⟨(modeOp W u n).comp φ, modeOp_comp_mem G σ hu n φ.2⟩ : E' →ₗ[ℂ] 𝒱) =
              (modeOp W u n).comp (T φ : E' →ₗ[ℂ] 𝒱)) → T = 0)

/-! ## What is proved: the trivial isotypic part, and the Molien multiplicity formula -/

/-- The **trivial multiplicity space is the orbifold**: `Hom_G(ℂ, W) ≃ W^G`, `φ ↦ φ(1)`. -/
def multSpaceTrivialEquiv (G : Subgroup (Aut W)) :
    multSpace G (Representation.trivial ℂ G ℂ) ≃ₗ[ℂ] (orbifold G).carrier where
  toFun φ := ⟨(φ : ℂ →ₗ[ℂ] 𝒱) 1, fun g hg => φ.2 ⟨g, hg⟩ 1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨LinearMap.toSpanSingleton ℂ 𝒱 (v : 𝒱), fun g c => by
    simp only [LinearMap.toSpanSingleton_apply, Representation.trivial_apply]
    rw [← Aut.coe_toLinearEquiv, map_smul, Aut.coe_toLinearEquiv, v.2 g g.2]⟩
  left_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext_ring
    simp
  right_inv v := by
    apply Subtype.ext
    simp

/-- The equivalence intertwines the `W^G`-actions: `(u₍ₙ₎ ∘ φ)(1) = u₍ₙ₎ φ(1)`. -/
theorem multSpaceTrivialEquiv_mode (G : Subgroup (Aut W)) {u : 𝒱} (hu : u ∈ (orbifold G).carrier)
    (n : ℤ) (φ : multSpace G (Representation.trivial ℂ G ℂ)) :
    ((multSpaceTrivialEquiv G ⟨(modeOp W u n).comp φ, modeOp_comp_mem G _ hu n φ.2⟩ :
        (orbifold G).carrier) : 𝒱) = W.smul u n ((multSpaceTrivialEquiv G φ : (orbifold G).carrier) : 𝒱) :=
  rfl

/-- **The trivial representation occurs** in a simple `W` (the vacuum). -/
theorem multSpace_trivial_ne_bot (G : Subgroup (Aut W)) (hW : W.IsSimple) :
    multSpace G (Representation.trivial ℂ G ℂ) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  let v : (orbifold G).carrier := ⟨W.vacuum, fun g _ => g.map_vacuum⟩
  refine ⟨((multSpaceTrivialEquiv G).symm v : ℂ →ₗ[ℂ] 𝒱), ((multSpaceTrivialEquiv G).symm v).2, ?_⟩
  intro h0
  have h1 := congrArg (fun φ : ℂ →ₗ[ℂ] 𝒱 => φ 1) h0
  simp only [LinearMap.zero_apply] at h1
  exact hW.vacuum_ne_zero (by simpa [multSpaceTrivialEquiv, v] using h1)

/-- The weight-`n` piece `W_n` as a representation of `G`. -/
def gradedRep (G : Subgroup (Aut W)) (n : ℤ) : Representation ℂ G (W.grading n) :=
  (autRes W n).comp G.subtype

/-- An intertwiner `E → W_n` is an element of the multiplicity space (`W_n ⊆ W`). -/
def intertwiningToMultSpace (G : Subgroup (Aut W)) (n : ℤ) {E : Type*} [AddCommGroup E]
    [Module ℂ E] (σ : Representation ℂ G E) :
    Representation.IntertwiningMap σ (gradedRep G n) →ₗ[ℂ] multSpace G σ where
  toFun f := ⟨(W.grading n).subtype.comp f.toLinearMap, fun g x => by
    have h := congrArg (fun m => ((m x : W.grading n) : 𝒱)) (f.isIntertwining' g)
    simp only [LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [h]
    rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem intertwiningToMultSpace_injective (G : Subgroup (Aut W)) (n : ℤ) {E : Type*}
    [AddCommGroup E] [Module ℂ E] (σ : Representation ℂ G E) :
    Function.Injective (intertwiningToMultSpace G n σ) := by
  intro f f' h
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun φ : multSpace G σ => (φ : E →ₗ[ℂ] 𝒱) x) h

/-- **The Molien multiplicity formula**: the multiplicity of a finite-dimensional
representation `E` in the weight-`n` space is
`dim Hom_G(E, W_n) = |G|⁻¹ Σ_g tr(g | W_n) · χ_E(g⁻¹)`.  For `E` trivial this is
`card_mul_finrank_orbifold`. -/
theorem finrank_intertwining_grading (G : Subgroup (Aut W)) [Fintype G] (n : ℤ)
    [FiniteDimensional ℂ (W.grading n)] {E : Type} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (σ : Representation ℂ G E) :
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, LinearMap.trace ℂ _ (autRes W n g) * σ.character g⁻¹ =
      finrank ℂ (Representation.IntertwiningMap σ (gradedRep G n)) := by
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ (gradedRep G n)

end VOA.Huang.SchurWeyl
