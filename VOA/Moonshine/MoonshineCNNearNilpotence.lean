import VOA.Moonshine.MoonshineCNNearGoddard

/-! Charge-sector lower bounds imply local nilpotence of the actual `L₁`.
No bound on the total grading, or finite-dimensionality, is required. -/

namespace VOA.NearVOA

open Module (End)

variable {H : Type*} [AddCommGroup H] [Module ℂ H] (V : NearVOA H)

theorem virasoroMode_mem_weight {N : ℤ} {u : H} (hu : u ∈ V.grading N) (n : ℤ) :
    V.L n u ∈ V.grading (N - n) := by
  simpa only [L_def, show 2 + N - (n + 1) - 1 = N - n by ring] using
    V.grading_mode V.conformalVector V.conformal_mem u hu (n + 1)

theorem virasoroOne_pow_mem_weight {N : ℤ} {u : H} (hu : u ∈ V.grading N) (k : ℕ) :
    (V.L 1 ^ k) u ∈ V.grading (N - (k : ℤ)) := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      simpa only [Nat.cast_succ, sub_add_eq_sub_sub] using V.virasoroMode_mem_weight ih 1

theorem virasoroOne_pow_mem_stable (S : Submodule ℂ H)
    (hS : ∀ u ∈ S, V.L 1 u ∈ S) {u : H} (hu : u ∈ S) (k : ℕ) :
    (V.L 1 ^ k) u ∈ S := by
  induction k with
  | zero => simpa using hu
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hS _ ih

/-- The cutoff counts level above the sector ground energy, including negative energies. -/
theorem virasoroOne_pow_zero_of_lower_bound (S : Submodule ℂ H) (E : ℤ)
    (hS : ∀ u ∈ S, V.L 1 u ∈ S)
    (hE : ∀ N : ℤ, N < E → S ⊓ V.grading N = ⊥)
    {N : ℤ} {u : H} (hu : u ∈ V.grading N) (hSu : u ∈ S)
    (k : ℕ) (hk : (N - E).toNat < k) : (V.L 1 ^ k) u = 0 := by
  have hmem : (V.L 1 ^ k) u ∈ S ⊓ V.grading (N - (k : ℤ)) :=
    ⟨V.virasoroOne_pow_mem_stable S hS hSu k, V.virasoroOne_pow_mem_weight hu k⟩
  rw [hE _ (by omega), Submodule.mem_bot] at hmem
  exact hmem

/-- Vectors killed by some power form a submodule; sums use a common larger cutoff. -/
def virasoroOneNilpotentStates : Submodule ℂ H where
  carrier := {u | ∃ k : ℕ, (V.L 1 ^ k) u = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro u v ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨max k l, by rw [map_add,
      Module.End.pow_map_zero_of_le (le_max_left k l) hk,
      Module.End.pow_map_zero_of_le (le_max_right k l) hl, add_zero]⟩
  smul_mem' := by
    rintro c u ⟨k, hk⟩
    exact ⟨k, by rw [map_smul, hk, smul_zero]⟩

/-- A sectorwise lower bound gives local nilpotence on all finite sums of homogeneous states. -/
theorem virasoroOne_locallyNilpotent_of_weight_sectors {ι : Type*}
    (S : ι → Submodule ℂ H) (E : ι → ℤ)
    (hS : ∀ α u, u ∈ S α → V.L 1 u ∈ S α)
    (hE : ∀ α N, N < E α → S α ⊓ V.grading N = ⊥)
    (hspan : (⨆ α, ⨆ N, S α ⊓ V.grading N) = ⊤) (u : H) :
    ∃ k : ℕ, (V.L 1 ^ k) u = 0 := by
  have htop : V.virasoroOneNilpotentStates = ⊤ := by
    apply top_unique
    rw [← hspan]
    refine iSup_le fun α => iSup_le fun N => ?_
    intro v hv
    exact ⟨(N - E α).toNat + 1,
      V.virasoroOne_pow_zero_of_lower_bound (S α) (E α) (hS α) (hE α)
        hv.2 hv.1 _ (Nat.lt_succ_self _)⟩
  change u ∈ V.virasoroOneNilpotentStates
  rw [htop]
  trivial

end VOA.NearVOA
