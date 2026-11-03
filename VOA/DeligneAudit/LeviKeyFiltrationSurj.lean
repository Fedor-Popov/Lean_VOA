import VOA.DeligneAudit.LeviKeyFiltrationFinite

/-! A quotient-of-copies interface for local Weyl layer estimates. -/

namespace VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A surjection from `d i` copies of each independent key generator supplies
both finiteness and the numerical step bound in Theorem R. -/
theorem key_filtered_weyl_bound_of_surjections
    (n : ℕ) (F S : ℕ → Submodule K M) (d : ℕ → ℕ)
    (hzero : F 0 = ⊥) (htop : F n = ⊤)
    (hmono : ∀ i < n, F i ≤ F (i + 1))
    (hSfinite : ∀ i < n, FiniteDimensional K (S i))
    (hsurj : ∀ i < n,
      ∃ φ : (Fin (d i) → KeyQuot F S i) →ₗ[K] StepQuot F i,
        Function.Surjective φ) :
    Module.finrank K M ≤
      ∑ i ∈ Finset.range n, d i * Module.finrank K (KeyQuot F S i) := by
  have hfinite (i : ℕ) (hi : i < n) : FiniteDimensional K (StepQuot F i) := by
    letI : FiniteDimensional K (S i) := hSfinite i hi
    obtain ⟨φ, hφ⟩ := hsurj i hi
    exact FiniteDimensional.of_surjective φ hφ
  have hstep (i : ℕ) (hi : i < n) :
      Module.finrank K (StepQuot F i) ≤
        d i * Module.finrank K (KeyQuot F S i) := by
    letI : FiniteDimensional K (S i) := hSfinite i hi
    obtain ⟨φ, hφ⟩ := hsurj i hi
    calc
      Module.finrank K (StepQuot F i) ≤
          Module.finrank K (Fin (d i) → KeyQuot F S i) :=
        LinearMap.finrank_le_finrank_of_surjective hφ
      _ = ∑ _j : Fin (d i), Module.finrank K (KeyQuot F S i) :=
        Module.finrank_pi_fintype K
      _ = d i * Module.finrank K (KeyQuot F S i) := by simp
  exact key_filtered_weyl_bound_of_finite_steps n F S d hzero htop hmono
    hfinite hstep

/-- The same bound when each stage is generated from its key space by an
abstract closure operation, such as the Levi current-algebra action. -/
theorem key_filtered_generated_bound
    (n : ℕ) (F S : ℕ → Submodule K M) (C : Submodule K M → Submodule K M)
    (d : ℕ → ℕ) (hzero : F 0 = ⊥) (htop : F n = ⊤)
    (hstage : ∀ i < n, F (i + 1) = F i ⊔ C (S i))
    (hSfinite : ∀ i < n, FiniteDimensional K (S i))
    (hsurj : ∀ i < n,
      ∃ φ : (Fin (d i) → KeyQuot F S i) →ₗ[K] StepQuot F i,
        Function.Surjective φ) :
    Module.finrank K M ≤
      ∑ i ∈ Finset.range n, d i * Module.finrank K (KeyQuot F S i) := by
  apply key_filtered_weyl_bound_of_surjections n F S d hzero htop
  · intro i hi
    rw [hstage i hi]
    exact le_sup_left
  · exact hSfinite
  · exact hsurj

end
end VOA.DeligneAudit.LeviKeyFiltration

#print axioms VOA.DeligneAudit.LeviKeyFiltration.key_filtered_weyl_bound_of_surjections
#print axioms VOA.DeligneAudit.LeviKeyFiltration.key_filtered_generated_bound
