import VOA.DeligneAudit.LeviKeyFiltrationSurj

/-! A Levi step with finite key spaces and a bounded local Weyl quotient at each key. -/

namespace VOA.DeligneAudit.LeviTypeA

noncomputable section

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

open LeviKeyFiltration

/-- The finite-key Levi estimate. `hsurj` is supplied by the local Weyl
quotient at a key; `hKS` is the box multiplicity estimate. -/
theorem levi_step_bound
    (n : ℕ) (F S : ℕ → Submodule K M)
    (C : Submodule K M → Submodule K M) (L g : ℕ → ℕ)
    (hzero : F 0 = ⊥) (htop : F n = ⊤)
    (hstage : ∀ i < n, F (i + 1) = F i ⊔ C (S i))
    (hSfinite : ∀ i < n, FiniteDimensional K (S i))
    (hsurj : ∀ i < n,
      ∃ φ : (Fin (L i) → KeyQuot F S i) →ₗ[K] StepQuot F i,
        Function.Surjective φ)
    (hKS : ∀ i < n, Module.finrank K (KeyQuot F S i) ≤ g i) :
    FiniteDimensional K M ∧
      Module.finrank K M ≤ ∑ i ∈ Finset.range n, L i * g i := by
  have hmono (i : ℕ) (hi : i < n) : F i ≤ F (i + 1) := by
    rw [hstage i hi]
    exact le_sup_left
  have hfinite (i : ℕ) (hi : i < n) : FiniteDimensional K (StepQuot F i) := by
    letI : FiniteDimensional K (S i) := hSfinite i hi
    obtain ⟨φ, hφ⟩ := hsurj i hi
    exact FiniteDimensional.of_surjective φ hφ
  have hM : FiniteDimensional K M :=
    finite_of_finite_steps n F hzero htop hmono hfinite
  refine ⟨hM, ?_⟩
  calc
    Module.finrank K M ≤
        ∑ i ∈ Finset.range n, L i * Module.finrank K (KeyQuot F S i) :=
      key_filtered_generated_bound n F S C L hzero htop hstage hSfinite hsurj
    _ ≤ ∑ i ∈ Finset.range n, L i * g i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (hKS i (Finset.mem_range.mp hi))

end
end VOA.DeligneAudit.LeviTypeA

#print axioms VOA.DeligneAudit.LeviTypeA.levi_step_bound
