import Mathlib

/-! A finite key filtration and its dimension bound. -/

namespace VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The key space modulo contributions generated at earlier filtration stages. -/
abbrev KeyQuot (F : ℕ → Submodule K M) (S : ℕ → Submodule K M) (i : ℕ) : Type _ :=
  S i ⧸ (F i).comap (S i).subtype

/-- The new layer at key `i`, modulo all preceding keys. -/
abbrev StepQuot (F : ℕ → Submodule K M) (i : ℕ) : Type _ :=
  F (i + 1) ⧸ (F i).comap (F (i + 1)).subtype

/-- Theorem R with the local Weyl quotient estimate as an explicit hypothesis.
The keys are numbered in filtration order. -/
theorem key_filtered_weyl_bound [FiniteDimensional K M]
    (n : ℕ) (F S : ℕ → Submodule K M) (d : ℕ → ℕ)
    (hzero : F 0 = ⊥) (htop : F n = ⊤)
    (hmono : ∀ i < n, F i ≤ F (i + 1))
    (hstep : ∀ i < n,
      Module.finrank K (StepQuot F i) ≤ d i * Module.finrank K (KeyQuot F S i)) :
    Module.finrank K M ≤
      ∑ i ∈ Finset.range n, d i * Module.finrank K (KeyQuot F S i) := by
  have hrank (i : ℕ) (hi : i < n) :
      Module.finrank K (F (i + 1)) ≤
        Module.finrank K (F i) +
          d i * Module.finrank K (KeyQuot F S i) := by
    let T : Submodule K (F (i + 1)) := (F i).comap (F (i + 1)).subtype
    have heq : Module.finrank K (F i) = Module.finrank K T := by
      rw [← Submodule.finrank_map_subtype_eq]
      have hm : T.map (F (i + 1)).subtype = F i := by
        simpa [T, inf_eq_right.mpr (hmono i hi)] using
          (Submodule.map_comap_subtype (p := F (i + 1)) (p' := F i))
      rw [hm]
    calc
      Module.finrank K (F (i + 1)) =
          Module.finrank K (StepQuot F i) + Module.finrank K T :=
        (T.finrank_quotient_add_finrank).symm
      _ ≤ d i * Module.finrank K (KeyQuot F S i) +
          Module.finrank K (F i) :=
        Nat.add_le_add (hstep i hi) (le_of_eq heq.symm)
      _ = _ := Nat.add_comm _ _
  have hprefix (j : ℕ) (hj : j ≤ n) :
      Module.finrank K (F j) ≤
        ∑ i ∈ Finset.range j, d i * Module.finrank K (KeyQuot F S i) := by
    induction j with
    | zero => simp [hzero]
    | succ j ih =>
      rw [Finset.sum_range_succ]
      exact (hrank j (by omega)).trans (Nat.add_le_add_right (ih (by omega)) _)
  have h := hprefix n le_rfl
  rw [htop] at h
  simpa only [finrank_top] using h

end
end VOA.DeligneAudit.LeviKeyFiltration

#print axioms VOA.DeligneAudit.LeviKeyFiltration.key_filtered_weyl_bound
