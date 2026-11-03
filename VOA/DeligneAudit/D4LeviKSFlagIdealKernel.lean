import VOA.DeligneAudit.D4LeviKSRzMaximalIdeal

/-! The three maximal complete-homogeneous families lie in the target kernel. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

/-- The span of degree-indexed multiples of the three maximal Garland
    generators. The coefficient may be any separately symmetric polynomial. -/
noncomputable def ksFlagMaximalRelationSpan
    (m a b c d : ℕ) : Submodule ℂ (pairTargetSymmetric a b c) :=
  Submodule.span ℂ {T |
    (∃ s r : ℕ, ∃ U : pairTargetSymmetric a b c,
      1 ≤ c ∧ m + 1 ≤ c + s ∧ s + r = d ∧
        T = U * rzFullHSymm a b c s) ∨
    (∃ s r : ℕ, ∃ U : pairTargetSymmetric a b c,
      1 ≤ b ∧ m + 1 ≤ c + b + s ∧ s + r = d ∧
        T = U * ryMixedTarget a b c s) ∨
    (∃ s r : ℕ, ∃ U : pairTargetSymmetric a b c,
      1 ≤ a + b ∧ m + 1 ≤ c + a + b + s ∧ s + r = d ∧
        T = U * rxMixedTarget a b c s)}

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ksFlagMaximalRelationSpan_le_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c d) :
    ksFlagMaximalRelationSpan m a b c d ≤
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c d h hi hkey)).ker := by
  apply Submodule.span_le.mpr
  intro T hT
  rcases hT with ⟨s, r, U, hc, hks, hdeg, rfl⟩ |
    ⟨s, r, U, hb, hks, hdeg, rfl⟩ |
    ⟨s, r, U, hx, hks, hdeg, rfl⟩
  · have hkey' : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c (s + r) := by
      rw [hdeg]
      exact hkey
    simpa [hdeg] using rzFullHSymm_mul_shifted_mem_ker
      ρ w m i a b c s r h hc hks hi hkey' U
  · have hkey' : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c (s + r) := by
      rw [hdeg]
      exact hkey
    simpa [hdeg] using ry_gen_maximal_mul_shifted_mem_ker
      ρ w m i a b c s r h hb hks hi hkey' U
  · have hkey' : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c (s + r) := by
      rw [hdeg]
      exact hkey
    simpa [hdeg] using rx_gen_maximal_mul_shifted_mem_ker
      ρ w m i a b c s r h hx hks hi hkey' U

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksFlagMaximalRelationSpan_le_ker
