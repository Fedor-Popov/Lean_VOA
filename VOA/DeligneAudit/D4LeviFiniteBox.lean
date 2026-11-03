import VOA.DeligneAudit.D4LeviRaiseTable

/-! A finite search box at every bounded radical depth. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- Every nonzero layer at depth at most `n` lies in an explicit finite box. -/
theorem keyBox_contains_nonzero_at_depth
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (n : ℕ) (k : RadicalKey) (hdepth : keyDepth k ≤ n)
    (hk : keyLayer ρ w k ≠ ⊥) :
    k ∈ keyBox n (2 * m * n) := by
  have hdegree : k.degree ≤ 2 * m * keyDepth k := by
    by_contra hn
    exact hk (keyLayer_eq_bot_of_degree_gt ρ w m h k (by omega))
  have hdegree' : k.degree ≤ 2 * m * n :=
    hdegree.trans (Nat.mul_le_mul_left (2 * m) hdepth)
  apply mem_keyBox n (2 * m * n) k <;>
    dsimp [keyDepth] at hdepth <;> omega

/-- A key outside the bounded-depth box has zero layer or excessive depth. -/
theorem keyLayer_eq_bot_or_depth_gt
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (n : ℕ) (k : RadicalKey) (hk : k ∉ keyBox n (2 * m * n)) :
    keyLayer ρ w k = ⊥ ∨ n < keyDepth k := by
  by_cases hd : keyDepth k ≤ n
  · left
    by_contra hnonzero
    exact hk (keyBox_contains_nonzero_at_depth ρ w m h n k hd hnonzero)
  · right
    omega

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyBox_contains_nonzero_at_depth
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_eq_bot_or_depth_gt
