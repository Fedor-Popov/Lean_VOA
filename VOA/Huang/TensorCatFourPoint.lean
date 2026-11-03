import VOA.Huang.TensorCatCoherence
import VOA.Huang.AssocConverseUniqueness

/-! # The proved analytic four-point comparison, distinct from the module associator

Both directions of the library's associativity theorem identify the simultaneous
function spaces for irreducible external modules. This does not yet identify
those spaces with the represented ordinary-module intertwiner spaces used by
Reassociation, nor does it assert five-point coherence.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.AssocTarget VOA.Huang.AssocConverse
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {P₁ P₂ P₃ P₄ : LWModule W}

/-- Both associativity directions give equality of the actual analytic function spaces. -/
theorem fourPointSpans_eq (h : AssociativityBoth W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) :
    iterateSpan P₁ P₂ P₃ P₄ = productSpan P₁ P₂ P₃ P₄ :=
  le_antisymm (span_le_of_associativityConverse h.2 P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄)
    (productSpan_le_iterateSpan h.1 i₁ i₂ i₃ i₄)

/-- Canonical comparison on analytic functions: it preserves every test-data value. -/
def fourPointEquiv (h : AssociativityBoth W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) :
    iterateSpan P₁ P₂ P₃ P₄ ≃ₗ[ℂ] productSpan P₁ P₂ P₃ P₄ :=
  LinearEquiv.ofEq _ _ (fourPointSpans_eq h i₁ i₂ i₃ i₄)

@[simp] theorem fourPointEquiv_apply (h : AssociativityBoth W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (f : iterateSpan P₁ P₂ P₃ P₄) (d : TestData P₁ P₂ P₃ P₄) :
    (fourPointEquiv h i₁ i₂ i₃ i₄ f).val d = f.val d := rfl

/-- Strong rationality supplies the analytic comparison (PBW datum from the theorem `VOA.pbw`).
This is an equivalence of four-point function spaces, not a module associator. -/
def fourPointEquiv_pbw (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) :
    iterateSpan P₁ P₂ P₃ P₄ ≃ₗ[ℂ] productSpan P₁ P₂ P₃ P₄ :=
  fourPointEquiv (associativityBoth_of_stronglyRational_pbw hV) i₁ i₂ i₃ i₄

end VOA.Huang.TensorCat
