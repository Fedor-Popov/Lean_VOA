import VOA.Huang.GenusTwoPointSepCoordinateWard

/-!
# From square-bracket collection to Huang's minus-two trace descent

This is a conditional consumer, with two independent obligations: the actual
coordinate conjugation and the square-bracket Ward identities. The latter are
predicates on a supplied bilinear function; they are not asserted for a single
rectangular mode coefficient. Kernel normalizations and both orientations are
retained. In particular the Weierstrass factor in mode m has weight m+2.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne QEquation
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {F : Type*} [AddCommGroup F] [Module ℂ F]

/-- Pointwise normalization of Zhu kernels to Huang's coordinate. -/
def huangScaledKernels (c : Kernels ℂ) : Kernels ℂ where
  G k := Complex.exp (logTwoPiI * (2 * (k : ℂ) + 4)) * c.G k
  Pleft m := Complex.exp (logTwoPiI * ((m : ℂ) + 2)) * c.Pleft m
  Pright m := Complex.exp (logTwoPiI * ((m : ℂ) + 2)) * c.Pright m

/-- Bilinear precomposition with the actual U(1), not an unspecified equivalence. -/
def huangModifyPair (P₁ P₂ : LWModule W) (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F) :
    P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F :=
  S.compl₁₂ (huangU P₁ 0).toLinearMap (huangU P₂ 0).toLinearMap

@[simp] theorem huangModifyPair_apply (P₁ P₂ : LWModule W)
    (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F) (x : P₁.carrier) (y : P₂.carrier) :
    huangModifyPair P₁ P₂ S x y = S (huangU P₁ 0 x) (huangU P₂ 0 y) := rfl

/-- The square-mode cutoff, expressed on the actual module square modes. -/
def SquareTailBound (P₁ P₂ : LWModule W) (a : V) (x : P₁.carrier) (y : P₂.carrier)
    (K : ℕ) : Prop := ∀ m : ℤ, K ≤ m →
  SquareModule.sqMode P₁.isMod m a x = 0 ∧ SquareModule.sqMode P₂.isMod m a y = 0

/-- The remaining collected identity in Zhu's normalized coordinate. -/
def SquareLeftWard (P₁ P₂ : LWModule W) (c : Kernels ℂ)
    (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F) : Prop :=
  ∀ a x y, ∃ K, SquareTailBound P₁ P₂ a x y K ∧
    S (SquareModule.sqMode P₁.isMod (-2) a x) y +
      (∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : ℂ) * c.G k) •
        S (SquareModule.sqMode P₁.isMod (2 * (k + 1)) a x) y) +
      (∑ m ∈ Finset.range K, ((-1 : ℂ) ^ m * (m + 1) * c.Pleft m) •
        S x (SquareModule.sqMode P₂.isMod m a y)) = 0

/-- Exchanging labels also exchanges the oriented elliptic kernels. -/
def reverseKernels (c : Kernels ℂ) : Kernels ℂ := ⟨c.G, c.Pright, c.Pleft⟩

/-- The opposite square-bracket obligation. -/
def SquareRightWard (P₁ P₂ : LWModule W) (c : Kernels ℂ)
    (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F) : Prop :=
  SquareLeftWard P₂ P₁ (reverseKernels c) S.flip

private theorem scaled_mode (m : ℤ) :
    Complex.exp (logTwoPiI * ((m : ℂ) + 2)) * huangModeScale m =
      Complex.exp logTwoPiI := by
  rw [huangModeScale, ← Complex.exp_add]
  congr 1
  ring

/-- A coordinate law carries a genuine square-mode cutoff to a plain-mode cutoff. -/
theorem tailBound_of_square (P₁ P₂ : LWModule W)
    (h₁ : NormalizedSquareConjugation P₁) (h₂ : NormalizedSquareConjugation P₂)
    (a : V) (x : P₁.carrier) (y : P₂.carrier) (K : ℕ)
    (hK : SquareTailBound P₁ P₂ (huangStateU W a) (huangU P₁ 0 x) (huangU P₂ 0 y) K) :
    TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y K := by
  intro m hm
  constructor
  · apply (huangU P₁ 0).injective
    rw [map_zero, huangU_mode_of_squareConjugation P₁ h₁, (hK m hm).1, smul_zero]
  · apply (huangU P₂ 0).injective
    rw [map_zero, huangU_mode_of_squareConjugation P₂ h₂, (hK m hm).2, smul_zero]

/-- The normalization-sensitive left Ward implication. Neither hypothesis is
silently discharged by the scalar coordinate construction. -/
theorem collectedLeftWard_of_square (P₁ P₂ : LWModule W)
    (h₁ : NormalizedSquareConjugation P₁) (h₂ : NormalizedSquareConjugation P₂)
    (c : Kernels ℂ) (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F)
    (hS : SquareLeftWard P₁ P₂ c S) :
    CollectedLeftWard P₁.isMod.toWeakModule P₂.isMod.toWeakModule
      (huangScaledKernels c) (huangModifyPair P₁ P₂ S) := by
  intro a x y
  obtain ⟨K, hK, h⟩ := hS (huangStateU W a) (huangU P₁ 0 x) (huangU P₂ 0 y)
  refine ⟨K, tailBound_of_square P₁ P₂ h₁ h₂ a x y K hK, ?_⟩
  have he (k : ℕ) :
      (((2 * k + 3 : ℕ) : ℂ) * (huangScaledKernels c).G k) *
        huangModeScale (2 * (k + 1)) =
      Complex.exp logTwoPiI * (((2 * k + 3 : ℕ) : ℂ) * c.G k) := by
    have hs := scaled_mode (2 * (k + 1))
    push_cast at hs
    have hex : (2 : ℂ) * (k + 1) + 2 = 2 * k + 4 := by ring
    rw [hex] at hs
    dsimp [huangScaledKernels]
    linear_combination ((2 * k + 3 : ℕ) : ℂ) * c.G k * hs
  have hp (m : ℕ) :
      ((-1 : ℂ) ^ m * (m + 1) * (huangScaledKernels c).Pleft m) * huangModeScale m =
      Complex.exp logTwoPiI * ((-1 : ℂ) ^ m * (m + 1) * c.Pleft m) := by
    have hs := scaled_mode m
    dsimp [huangScaledKernels]
    push_cast at hs
    linear_combination (-1 : ℂ) ^ m * (m + 1) * c.Pleft m * hs
  have hneg : huangModeScale (-2) = Complex.exp logTwoPiI := by
    unfold huangModeScale
    congr 1
    norm_num
  simp only [huangModifyPair_apply, huangU_mode_of_squareConjugation P₁ h₁,
    huangU_mode_of_squareConjugation P₂ h₂, map_smul, LinearMap.smul_apply,
    smul_smul, he, hp, hneg]
  simp only [mul_smul, ← Finset.smul_sum, ← smul_add]
  simp only [mul_smul] at h
  rw [h, smul_zero]

/-- Right collection is not dropped: it is the left calculation with both
insertions and the two oriented kernels exchanged. -/
theorem collectedRightWard_of_square (P₁ P₂ : LWModule W)
    (h₁ : NormalizedSquareConjugation P₁) (h₂ : NormalizedSquareConjugation P₂)
    (c : Kernels ℂ) (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F)
    (hS : SquareRightWard P₁ P₂ c S) :
    CollectedRightWard P₁.isMod.toWeakModule P₂.isMod.toWeakModule
      (huangScaledKernels c) (huangModifyPair P₁ P₂ S) := by
  intro a x y
  obtain ⟨K, hK, h⟩ := collectedLeftWard_of_square P₂ P₁ h₂ h₁
    (reverseKernels c) S.flip hS a y x
  exact ⟨K, fun m hm => ⟨(hK m hm).2, (hK m hm).1⟩, h⟩

/-- The exact pre-existing descent interface, with the normalized-coordinate
and collection obligations visible. This theorem does not assert them for a trace. -/
theorem traceDescent_of_squareWard (P₁ P₂ : LWModule W)
    (h₁ : NormalizedSquareConjugation P₁) (h₂ : NormalizedSquareConjugation P₂)
    (c : Kernels ℂ) (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F)
    (hL : SquareLeftWard P₁ P₂ c S) (hR : SquareRightWard P₁ P₂ c S) :
    TraceDescent P₁.isMod.toWeakModule P₂.isMod.toWeakModule (huangScaledKernels c)
      (tensorTrace (R := ℂ) (huangModifyPair P₁ P₂ S)) :=
  traceDescent_of_collected _ _ _ _
    (collectedLeftWard_of_square P₁ P₂ h₁ h₂ c S hL)
    (collectedRightWard_of_square P₁ P₂ h₁ h₂ c S hR)

end VOA.Huang.GenusTwoPoint.Separate
