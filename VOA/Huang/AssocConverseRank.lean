/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocConverseSpan
import VOA.Huang.BraidingSkewJacobi

/-!
# A dimension squeeze for inverse associativity

Forward associativity alone gives `dim Products ≤ dim Iterates`. It does not imply
surjectivity. There is, however, a noncircular dimension route: use the same forward
inclusion with the first and third inputs reversed, together with skew-symmetry of
the individual fusion rules. Only a lower bound for products and an upper bound
for iterates are needed. No associativity identity for fusion coefficients is assumed.

The two bounds below are named residuals, intended for a complete irredundant finite
family of irreducibles. The implication is proved for any family satisfying the bounds;
this file does not prove either bound or the unconditional converse.
-/

namespace VOA.Huang.AssocConverse

open VOA VOA.Huang.AssocTarget Module
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {ι : Type v} [Fintype ι]

/-- Dimension of the formal space of product channels over the chosen family. -/
noncomputable def productMultiplicity (R : ι → LWModule W) (P₁ P₂ P₃ P₄ : LWModule W) : ℕ :=
  ∑ j, fusionRule P₁.isMod (R j).isMod P₄.isMod *
    fusionRule P₂.isMod P₃.isMod (R j).isMod

/-- Dimension of the formal space of iterate channels over the chosen family. -/
noncomputable def iterateMultiplicity (R : ι → LWModule W) (P₁ P₂ P₃ P₄ : LWModule W) : ℕ :=
  ∑ j, fusionRule (R j).isMod P₃.isMod P₄.isMod *
    fusionRule P₁.isMod P₂.isMod (R j).isMod

/-- Input reversal exchanges the two *formal* multiplicities, by skew-symmetry only. -/
theorem productMultiplicity_reverse (R : ι → LWModule W) (P₁ P₂ P₃ P₄ : LWModule W) :
    productMultiplicity R P₃ P₂ P₁ P₄ = iterateMultiplicity R P₁ P₂ P₃ P₄ := by
  unfold productMultiplicity iterateMultiplicity
  apply Finset.sum_congr rfl
  intro j _
  rw [VOA.Huang.BraidingSkew.fusionRule_swap (R j).isMod P₃.isMod P₄.isMod,
    VOA.Huang.BraidingSkew.fusionRule_swap P₁.isMod P₂.isMod (R j).isMod]

/-- Independence of product channels supplies this lower bound. For strongly rational `W`
and a finite irredundant irreducible family it is a true target; completeness is unnecessary. -/
def ProductDimensionLowerBound (R : ι → LWModule W) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW →
      productMultiplicity R P₁ P₂ P₃ P₄ ≤ finrank ℂ (productSpan P₁ P₂ P₃ P₄)

/-- Spanning by a complete finite irreducible family supplies this upper bound. Finiteness
is included explicitly so that `finrank` is never its infinite-dimensional default value. -/
def IterateDimensionUpperBound (R : ι → LWModule W) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW →
      FiniteDimensional ℂ (iterateSpan P₁ P₂ P₃ P₄) ∧
      finrank ℂ (iterateSpan P₁ P₂ P₃ P₄) ≤ iterateMultiplicity R P₁ P₂ P₃ P₄

/-- Forward inclusions in two input orders squeeze the dimensions in the required direction.
The proof uses no fusion-ring associativity. -/
theorem iterateSpan_finrank_le_productSpan (hassoc : AssociativityInput W)
    (R : ι → LWModule W) (hlower : ProductDimensionLowerBound R)
    (hupper : IterateDimensionUpperBound R)
    {P₁ P₂ P₃ P₄ : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) :
    finrank ℂ (iterateSpan P₁ P₂ P₃ P₄) ≤ finrank ℂ (productSpan P₁ P₂ P₃ P₄) := by
  have hu := hupper P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄
  have hr := hupper P₃ P₂ P₁ P₄ i₃ i₂ i₁ i₄
  letI := hr.1
  calc
    finrank ℂ (iterateSpan P₁ P₂ P₃ P₄)
        ≤ iterateMultiplicity R P₁ P₂ P₃ P₄ := hu.2
    _ = productMultiplicity R P₃ P₂ P₁ P₄ := (productMultiplicity_reverse R _ _ _ _).symm
    _ ≤ finrank ℂ (productSpan P₃ P₂ P₁ P₄) := hlower _ _ _ _ i₃ i₂ i₁ i₄
    _ ≤ finrank ℂ (iterateSpan P₃ P₂ P₁ P₄) :=
      Submodule.finrank_mono (productSpan_le_iterateSpan hassoc i₃ i₂ i₁ i₄)
    _ ≤ iterateMultiplicity R P₃ P₂ P₁ P₄ := hr.2
    _ = productMultiplicity R P₁ P₂ P₃ P₄ := (productMultiplicity_reverse R _ _ _ _).symm
    _ ≤ finrank ℂ (productSpan P₁ P₂ P₃ P₄) := hlower _ _ _ _ i₁ i₂ i₃ i₄

/-- A sufficient algebraic route from forward to inverse associativity. Both remaining
dimension bounds refer to the actual simultaneous matrix-coefficient spaces. -/
theorem associativityConverse_of_dimension_bounds (hassoc : AssociativityInput W)
    (R : ι → LWModule W) (hlower : ProductDimensionLowerBound R)
    (hupper : IterateDimensionUpperBound R) : AssociativityConverse W := by
  apply associativityConverse_of_span_le
  intro P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄
  letI := (hupper P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄).1
  have heq := Submodule.eq_of_le_of_finrank_le
    (productSpan_le_iterateSpan hassoc i₁ i₂ i₃ i₄)
    (iterateSpan_finrank_le_productSpan hassoc R hlower hupper i₁ i₂ i₃ i₄)
  exact heq.ge

/-- The numerical associativity identity is an output of the same argument, not an input. -/
theorem fusion_associativity_of_dimension_bounds (hassoc : AssociativityInput W)
    (R : ι → LWModule W) (hlower : ProductDimensionLowerBound R)
    (hupper : IterateDimensionUpperBound R)
    {P₁ P₂ P₃ P₄ : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) :
    productMultiplicity R P₁ P₂ P₃ P₄ = iterateMultiplicity R P₁ P₂ P₃ P₄ := by
  have hle : ∀ (A B C D : LWModule W), A.IsIrreducibleLW → B.IsIrreducibleLW →
      C.IsIrreducibleLW → D.IsIrreducibleLW →
      productMultiplicity R A B C D ≤ iterateMultiplicity R A B C D := by
    intro A B C D iA iB iC iD
    letI := (hupper A B C D iA iB iC iD).1
    exact (hlower A B C D iA iB iC iD).trans
      ((Submodule.finrank_mono (productSpan_le_iterateSpan hassoc iA iB iC iD)).trans
        (hupper A B C D iA iB iC iD).2)
  apply le_antisymm (hle P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄)
  simpa only [productMultiplicity_reverse R P₁ P₂ P₃ P₄,
    ← productMultiplicity_reverse R P₃ P₂ P₁ P₄] using hle P₃ P₂ P₁ P₄ i₃ i₂ i₁ i₄

end VOA.Huang.AssocConverse
