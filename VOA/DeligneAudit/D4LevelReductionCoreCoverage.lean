import VOA.DeligneAudit.D4LevelCoreConvertedAudit
import VOA.DeligneAudit.D4LevelBoundsAdjointAudit

/-! Exhaustive coverage of the nonnegative vector-node grades by the core and boundary bounds. -/

namespace VOA.DeligneAudit.D4LevelReduction

/-- A nonnegative grade with even level difference and nonnegative counts has a bottom triple. -/
theorem levelIndex_bottomTriple (m : ℕ) (κ p : ℤ) (hκ : 0 ≤ κ)
    (hparity : (p - κ) % 2 = 0) (ha : κ ≤ p) (hc : p + κ ≤ 2 * (m : ℤ)) :
    ∃ a b c : ℕ, a + b + c = m ∧ (b : ℤ) = κ ∧ 2 * (a : ℤ) + b = p := by
  let a := ((p - κ) / 2).toNat
  let b := κ.toNat
  let c := m - a - b
  have haCast : (a : ℤ) = (p - κ) / 2 := Int.toNat_of_nonneg (by omega)
  have hbCast : (b : ℤ) = κ := Int.toNat_of_nonneg hκ
  refine ⟨a, b, c, ?_, hbCast, ?_⟩
  · dsimp [c]
    omega
  · omega

/-- Interior core bounds and the proved boundaries cover every level of a nonnegative grade. -/
theorem levelTruncationBound_of_nonnegative_coreBounds
    (h : ∀ a b c : ℕ, 1 ≤ a → 1 ≤ c → TruncatedCoreRankBound a b c)
    (m : ℕ) (κ p : ℤ) (hκ : 0 ≤ κ) : LevelTruncationBound m κ p := by
  by_cases houtside : (κ, p) ∉ levelIndices m
  · exact levelTruncationBound_of_empty m κ p (Or.inl houtside)
  by_cases hodd : (p - κ) % 2 ≠ 0
  · exact levelTruncationBound_of_empty m κ p (Or.inr (Or.inl hodd))
  by_cases hadjoint : p < κ
  · exact levelTruncationBound_of_empty m κ p (Or.inr (Or.inr (Or.inl hadjoint)))
  by_cases hcentral : 2 * (m : ℤ) < p + κ
  · exact levelTruncationBound_of_empty m κ p (Or.inr (Or.inr (Or.inr hcentral)))
  obtain ⟨a, b, c, hm, hb, hp⟩ :=
    levelIndex_bottomTriple m κ p hκ (by omega) (by omega) (by omega)
  by_cases ha : a = 0
  · have hlevel : p = κ := by simp_all
    rw [hlevel]
    exact levelTruncationBound_of_zero_adjoint m κ
  by_cases hc : c = 0
  · have hedge := levelTruncationBound_adjoint_edge a b
    have hab : a + b = m := by omega
    rwa [hab, hp, hb] at hedge
  have hinterior := levelTruncationBound_of_truncatedCoreRank a b c
    (h a b c (by omega) (by omega))
  rwa [hm, hp, hb] at hinterior

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.levelIndex_bottomTriple
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_nonnegative_coreBounds
