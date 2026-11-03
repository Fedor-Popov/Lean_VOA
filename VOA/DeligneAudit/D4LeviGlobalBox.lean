import VOA.DeligneAudit.D4LeviCountCutoff
import VOA.DeligneAudit.D4LeviFiniteBox

/-! One finite radical key box for every source multiplicity. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

theorem keyCount_wordKey (j : Fin 6) (l : List (Fin 6 × ℕ)) :
    keyCount j (wordKey l) = l.countP (fun p => p.1 = j) := by
  fin_cases j <;> simp [keyCount, wordKey] <;> rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem keyLayer_eq_bot_of_count
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (j : Fin 6)
    (hj : rootWeight m j < keyCount j k) :
    keyLayer ρ w k = ⊥ := by
  rw [keyLayer, eq_bot_iff, Submodule.span_le]
  intro z hz
  obtain ⟨l, hk, rfl⟩ := hz
  have hc : rootWeight m j < l.countP (fun p => p.1 = j) := by
    simpa [← keyCount_wordKey j l, hk] using hj
  rw [radicalWord_zero_of_count ρ w m h j l hc]
  exact Submodule.zero_mem _

theorem keyDepth_le_of_nonzero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hk : keyLayer ρ w k ≠ ⊥) :
    keyDepth k ≤ 6 * m := by
  have he : k.e ≤ 0 := by
    by_contra hn
    exact hk (keyLayer_eq_bot_of_count ρ w m h k 0 (by
      simp [rootWeight, keyCount]; omega))
  have hx : k.x ≤ m := by
    by_contra hn
    exact hk (keyLayer_eq_bot_of_count ρ w m h k 1 (by
      simp [rootWeight, keyCount]; omega))
  have hu : k.u ≤ m := by
    by_contra hn
    exact hk (keyLayer_eq_bot_of_count ρ w m h k 2 (by
      simp [rootWeight, keyCount]; omega))
  have hup : k.up ≤ m := by
    by_contra hn
    exact hk (keyLayer_eq_bot_of_count ρ w m h k 3 (by
      simp [rootWeight, keyCount]; omega))
  have hy : k.y ≤ m := by
    by_contra hn
    exact hk (keyLayer_eq_bot_of_count ρ w m h k 4 (by
      simp [rootWeight, keyCount]; omega))
  have hz : k.z ≤ 2 * m := by
    by_contra hn
    exact hk (keyLayer_eq_bot_of_count ρ w m h k 5 (by
      simp [rootWeight, keyCount]; omega))
  dsimp [keyDepth]
  omega

theorem keyLayer_eq_bot_of_depth_gt
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hk : 6 * m < keyDepth k) :
    keyLayer ρ w k = ⊥ := by
  by_contra hn
  exact (Nat.not_le_of_gt hk) (keyDepth_le_of_nonzero ρ w m h k hn)

/-- Every nonzero exact key layer lies in this one all-depth box. -/
theorem keyBox_contains_nonzero_global
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hk : keyLayer ρ w k ≠ ⊥) :
    k ∈ keyBox (6 * m) (2 * m * (6 * m)) := by
  exact keyBox_contains_nonzero_at_depth ρ w m h (6 * m) k
    (keyDepth_le_of_nonzero ρ w m h k hk) hk

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyCount_wordKey
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_eq_bot_of_count
#print axioms VOA.DeligneAudit.D4Levi.keyDepth_le_of_nonzero
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_eq_bot_of_depth_gt
#print axioms VOA.DeligneAudit.D4Levi.keyBox_contains_nonzero_global
