import VOA.DeligneAudit.D4LeviKSFlagIdealKernel
import VOA.DeligneAudit.D4LeviKSBoxCountKey

/-! The flag ideal is the whole ring when the three block sizes exceed `m`. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

theorem rzFullHSymm_zero (a b c : ℕ) : rzFullHSymm a b c 0 = 1 := by
  apply Subtype.ext
  simp [rzFullHSymm, hsymm_zero]

theorem ryMixedTarget_zero (a b c : ℕ) : ryMixedTarget a b c 0 = 1 := by
  apply Subtype.ext
  simp [ryMixedTarget_polynomial, hsymm_zero]

theorem rxMixedTarget_zero (a b c : ℕ) : rxMixedTarget a b c 0 = 1 := by
  apply Subtype.ext
  simp [rxMixedTarget_polynomial, hsymm_zero]

/-- An overfull flag has the unit among its maximal Garland relations. -/
theorem ksFlagMaximalRelationSpan_eq_top_of_overfull
    (m a b c d : ℕ) (hover : m < a + b + c) :
    ksFlagMaximalRelationSpan m a b c d = ⊤ := by
  apply top_unique
  intro T _
  apply Submodule.subset_span
  by_cases hx : 1 ≤ a + b
  · exact Or.inr (Or.inr ⟨0, d, T, hx, by omega, by simp,
      by simp [rxMixedTarget_zero]⟩)
  · by_cases hb : 1 ≤ b
    · exact Or.inr (Or.inl ⟨0, d, T, hb, by omega, by simp,
        by simp [ryMixedTarget_zero]⟩)
    · have hc : 1 ≤ c := by omega
      exact Or.inl ⟨0, d, T, hc, by omega, by simp,
        by simp [rzFullHSymm_zero]⟩

/-- The box spanning inclusion in the overfull case needs no box vectors. -/
theorem ksFlagBoxSpan_of_overfull
    (m a b c d : ℕ) (hover : m < a + b + c)
    (B : Finset (pairTargetSymmetric a b c))
    (T : pairTargetSymmetric a b c) :
    T ∈ Submodule.span ℂ (B : Set (pairTargetSymmetric a b c)) ⊔
      ksFlagMaximalRelationSpan m a b c d := by
  rw [ksFlagMaximalRelationSpan_eq_top_of_overfull m a b c d hover]
  simp

/-- The maximal relation span is stable under every symmetric target multiplier. -/
theorem ksFlagMaximalRelationSpan_mul_mem
    (m a b c d : ℕ) (U T : pairTargetSymmetric a b c)
    (hT : T ∈ ksFlagMaximalRelationSpan m a b c d) :
    U * T ∈ ksFlagMaximalRelationSpan m a b c d := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
      apply Submodule.subset_span
      rcases hT with ⟨s, r, W, hc, hs, hd, rfl⟩ |
        ⟨s, r, W, hb, hs, hd, rfl⟩ |
        ⟨s, r, W, hx, hs, hd, rfl⟩
      · exact Or.inl ⟨s, r, U * W, hc, hs, hd, by simp [mul_assoc]⟩
      · exact Or.inr (Or.inl ⟨s, r, U * W, hb, hs, hd,
          by simp [mul_assoc]⟩)
      · exact Or.inr (Or.inr ⟨s, r, U * W, hx, hs, hd,
          by simp [mul_assoc]⟩)
  | zero => simp
  | add T W hT hW ihT ihW =>
      simpa only [mul_add] using
        (ksFlagMaximalRelationSpan m a b c d).add_mem ihT ihW
  | smul r T hT ih =>
      simpa only [mul_smul_comm] using
        (ksFlagMaximalRelationSpan m a b c d).smul_mem r ih

/-- Increasing the final degree retains every maximal relation. -/
theorem ksFlagMaximalRelationSpan_mono_degree
    (m a b c d e : ℕ) (hde : d ≤ e) :
    ksFlagMaximalRelationSpan m a b c d ≤
      ksFlagMaximalRelationSpan m a b c e := by
  apply Submodule.span_le.mpr
  intro T hT
  apply Submodule.subset_span
  rcases hT with ⟨s, r, U, hc, hs, hd, hT⟩ |
    ⟨s, r, U, hb, hs, hd, hT⟩ |
    ⟨s, r, U, hx, hs, hd, hT⟩
  · exact Or.inl ⟨s, e - s, U, hc, hs, by omega, hT⟩
  · exact Or.inr (Or.inl ⟨s, e - s, U, hb, hs, by omega, hT⟩)
  · exact Or.inr (Or.inr ⟨s, e - s, U, hx, hs, by omega, hT⟩)

theorem ksBoxCount_pairFinalKey_zero_of_overfull
    (m a b c d : ℕ) (hover : m < a + b + c) :
    ksBoxCount m (pairFinalKey a b c d) = 0 := by
  simp [ksBoxCount, pairFinalKey, show ¬a + b + c ≤ m by omega]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The target quotient map vanishes at an overfull flag key. -/
theorem pairTargetQuotientEvaluation_eq_zero_of_overfull
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c d)
    (hover : m < a + b + c) :
    pairTargetQuotientEvaluation ρ w m i a b c
      (pairKernelPrefix_of_sat ρ w m i a b c d h hi hkey) = 0 := by
  apply LinearMap.ext
  intro T
  have hker := ksFlagMaximalRelationSpan_le_ker ρ w m i a b c d h hi hkey
  rw [ksFlagMaximalRelationSpan_eq_top_of_overfull m a b c d hover] at hker
  exact (LinearMap.mem_ker.mp (hker (Submodule.mem_top)))

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzFullHSymm_zero
#print axioms VOA.DeligneAudit.D4Levi.ryMixedTarget_zero
#print axioms VOA.DeligneAudit.D4Levi.rxMixedTarget_zero
#print axioms VOA.DeligneAudit.D4Levi.ksFlagMaximalRelationSpan_eq_top_of_overfull
#print axioms VOA.DeligneAudit.D4Levi.ksFlagBoxSpan_of_overfull
#print axioms VOA.DeligneAudit.D4Levi.ksFlagMaximalRelationSpan_mul_mem
#print axioms VOA.DeligneAudit.D4Levi.ksFlagMaximalRelationSpan_mono_degree
#print axioms VOA.DeligneAudit.D4Levi.ksBoxCount_pairFinalKey_zero_of_overfull
#print axioms VOA.DeligneAudit.D4Levi.pairTargetQuotientEvaluation_eq_zero_of_overfull
