/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLRationalSeparable
import VOA.Huang.HuangModularityDim

/-!
# The twist-pivotal dimension of a self-dual object through a symmetric self-duality

Monoidal category theory only.

* `exactPairingOfZig` — the two zig-zag identities `Zig₁ c p`, `Zig₂ c p` make `(c, p)` an
  `ExactPairing A A`;
* `twistPivotal_trL_id_selfDual` — for the twist pivotal structure of a natural twist `θ`,
  if `θ_A = 1` and `β_{A,A} ≫ p = p`, then `tr(𝟙_A) = c ≫ p` (`twistPivotal_trL_id`);
* `twistPivotal_trL_id_frobenius` — for a commutative algebra `A` with trivial twist and a
  Frobenius copairing `c` of `p = μ ≫ q` (only `Zig₁ c p` is assumed), `tr(𝟙_A) = c ≫ μ ≫ q`.

No `sorry`, no new axioms.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLRational

open CategoryTheory MonoidalCategory BraidedCategory Category VOA.Huang.TensorCat
  VOA.Huang.HuangRigid VOA.Huang.HuangModularity

universe v u

section Pairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C}

/-- The zig-zags `Zig₁`, `Zig₂` make `(c, p)` an exact pairing of `A` with itself. -/
@[implicit_reducible]
def exactPairingOfZig {c : 𝟙_ C ⟶ A ⊗ A} {p : A ⊗ A ⟶ 𝟙_ C} (h₁ : Zig₁ c p)
    (h₂ : Zig₂ c p) : ExactPairing A A where
  coevaluation' := c
  evaluation' := p
  coevaluation_evaluation' := by
    unfold Zig₂ at h₂
    rw [← cancel_epi (ρ_ A).inv, ← cancel_mono (λ_ A).hom]
    simpa [Category.assoc] using h₂
  evaluation_coevaluation' := by
    unfold Zig₁ at h₁
    rw [← cancel_epi (λ_ A).inv, ← cancel_mono (ρ_ A).hom]
    simpa [Category.assoc] using h₁

end Pairing

section Trace

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C] {θ : ∀ X : C, X ≅ X}

/-- **The twist-pivotal dimension through a symmetric self-duality.** -/
theorem twistPivotal_trL_id_selfDual
    (hθ : ∀ {X Y : C} (f : X ⟶ Y), f ≫ (θ Y).hom = (θ X).hom ≫ f) {A : C}
    {c : 𝟙_ C ⟶ A ⊗ A} {p : A ⊗ A ⟶ 𝟙_ C} (h₁ : Zig₁ c p) (h₂ : Zig₂ c p)
    (htw : (θ A).hom = 𝟙 A) (hp : (β_ A A).hom ≫ p = p) :
    (twistPivotal hθ).trL (𝟙 A) = c ≫ p := by
  rw [twistPivotal_trL_id hθ A A (exactPairingOfZig h₁ h₂)]
  change c ≫ ((θ A).hom ▷ A) ≫ (β_ A A).hom ≫ p = c ≫ p
  rw [htw, id_whiskerRight, id_comp, hp]

/-- **The twist-pivotal dimension of a commutative Frobenius algebra with trivial twist**:
`tr(𝟙_A) = c ≫ μ ≫ q` for any `c` with `Zig₁ c (μ ≫ q)`. -/
theorem twistPivotal_trL_id_frobenius
    (hθ : ∀ {X Y : C} (f : X ⟶ Y), f ≫ (θ Y).hom = (θ X).hom ≫ f) {A : C} [MonObj A]
    [IsCommMonObj A] {q : A ⟶ 𝟙_ C} {c : 𝟙_ C ⟶ A ⊗ A} (h₁ : Zig₁ c (MonObj.mul ≫ q))
    (htw : (θ A).hom = 𝟙 A) :
    (twistPivotal hθ).trL (𝟙 A) = c ≫ MonObj.mul ≫ q := by
  have hp : (β_ A A).hom ≫ MonObj.mul ≫ q = MonObj.mul ≫ q := by
    rw [← assoc, IsCommMonObj.mul_comm]
  exact twistPivotal_trL_id_selfDual hθ h₁ (isCentral_of_frobenius h₁).1 htw hp

end Trace

end VOA.Huang.HKLRational
