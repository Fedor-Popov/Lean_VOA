import VOA.DeligneAudit.SL4TRadicalMultiplicityAction
import VOA.DeligneAudit.SL4TCore
import VOA.DeligneAudit.SL4TGrassmannianFinite
import Mathlib.RingTheory.TensorProduct.Basic

/-!
The three-Grassmannian source for a merged radical multiplicity space.
The source and its binomial dimension bound are proved here. The surjective,
power-sum-equivariant presentation is an explicit residual proposition, not a theorem.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open scoped TensorProduct

/-- The three independent Grassmannian alphabets at arbitrary dominant labels. -/
abbrev RadicalGrassmannianRing (a b c : ℕ) (d : Fin 3 → ℕ) :=
  H (d 0) a ⊗[ℂ] (H (d 1) b ⊗[ℂ] H (d 2) c)

/-- Power sums in the elementary-generator presentation of a Grassmannian ring. -/
def grassmannianPowerSum (d M s : ℕ) : H d M :=
  powerSumOfCoeff d (fun j => (-1) ^ j * eClass d (M - d) j) s

/-- The three power sums embedded into the tensor product of Grassmannian rings. -/
def radicalGrassmannianPowerSum (a b c : ℕ) (d : Fin 3 → ℕ) (j : Fin 3)
    (s : ℕ) : RadicalGrassmannianRing a b c d :=
  match j with
  | 0 => grassmannianPowerSum (d 0) a s ⊗ₜ[ℂ] (1 ⊗ₜ[ℂ] 1)
  | 1 => 1 ⊗ₜ[ℂ] (grassmannianPowerSum (d 1) b s ⊗ₜ[ℂ] 1)
  | 2 => 1 ⊗ₜ[ℂ] (1 ⊗ₜ[ℂ] grassmannianPowerSum (d 2) c s)

/-- The three-Grassmannian source is finite with the expected binomial upper bound. -/
theorem radicalGrassmannianRing_finite_rank_le (a b c : ℕ) (d : Fin 3 → ℕ)
    (h₀ : d 0 ≤ a) (h₁ : d 1 ≤ b) (h₂ : d 2 ≤ c) :
    FiniteDimensional ℂ (RadicalGrassmannianRing a b c d) ∧
      Module.finrank ℂ (RadicalGrassmannianRing a b c d) ≤
        a.choose (d 0) * b.choose (d 1) * c.choose (d 2) := by
  obtain ⟨hf₀, hr₀⟩ := H_finite_rank_le (d 0) a h₀
  obtain ⟨hf₁, hr₁⟩ := H_finite_rank_le (d 1) b h₁
  obtain ⟨hf₂, hr₂⟩ := H_finite_rank_le (d 2) c h₂
  letI := hf₀
  letI := hf₁
  letI := hf₂
  refine ⟨inferInstance, ?_⟩
  simp only [RadicalGrassmannianRing, Module.finrank_tensorProduct]
  rw [mul_assoc]
  exact Nat.mul_le_mul hr₀ (Nat.mul_le_mul hr₁ hr₂)

/-- The unresolved Grassmannian presentation of the actual merged multiplicity space. -/
def RadicalGrassmannianPresentation {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : SectorWeyl.CurrentModule A3Sector.bracketTable V) (w : V)
    (a b c : ℕ) (h : A3Sector.LocalWeylRel ρ w (A3Sector.weightABC a b c))
    (d : Fin 3 → ℕ) : Prop :=
  ∃ π : RadicalGrassmannianRing a b c d →ₗ[ℂ] radicalCountMultiplicity ρ w d,
    Function.Surjective π ∧
      ∀ j s, 0 < s → ∀ φ,
        radicalAlphabetQuotCurrent ρ w a b c h d j s (π φ :
          V ⧸ higherRadicalCountClosure ρ w d) =
            (π (radicalGrassmannianPowerSum a b c d j s * φ) :
              V ⧸ higherRadicalCountClosure ρ w d)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianRing_finite_rank_le
