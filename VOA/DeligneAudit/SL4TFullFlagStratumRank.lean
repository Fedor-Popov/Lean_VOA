import VOA.DeligneAudit.SL4TStratumConfigurationSymmetry

/-! # The configuration bound for every truncated full-flag stratum -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The full-alphabet boundary of the refined configuration bound. -/
theorem fullFlagStratumRankBound_univ (B k j : ℕ) (hk : 2 * k ≤ B) :
    Module.finrank ℂ (FullFlagStratumRing B (B - k) j Finset.univ) ≤
      Nat.card (FullFlagStratumConfiguration B k j Finset.univ) := by
  by_cases hj : j ≤ k
  · exact fullFlagStratumRankBound_univ_of_le B k j hk hj
  · rw [Nat.card_congr
      (fullFlagStratumConfiguration_allEquiv B k j Finset.univ (by omega))]
    exact (fullFlagStratum_finrank_le_fullFlag B (B - k) j Finset.univ).trans
      (fullFlag_finrank_le_configurations B k hk)

/-- Every proper selected subset can be relabeled to avoid the first position. -/
theorem selectedPositions_delete_first (B : ℕ) (Y : Finset (Fin (B + 1)))
    (hY : Y ≠ Finset.univ) :
    ∃ (e : Equiv.Perm (Fin (B + 1))) (Z : Finset (Fin B)),
      Y.map e.toEmbedding = Z.map (Fin.succEmb B) := by
  classical
  have hex : ∃ a, a ∉ Y := by
    by_contra hn
    apply hY
    apply Finset.eq_univ_iff_forall.mpr
    intro a
    by_contra ha
    exact hn ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  let e : Equiv.Perm (Fin (B + 1)) := Equiv.swap 0 a
  let W := Y.map e.toEmbedding
  have hzero : (0 : Fin (B + 1)) ∉ W := by
    simpa only [W, Finset.mem_map_equiv, e, Equiv.swap_apply_left] using ha
  let Z : Finset (Fin B) := Finset.univ.filter fun i => i.succ ∈ W
  refine ⟨e, Z, ?_⟩
  change W = Z.map (Fin.succEmb B)
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [hzero]
  · simp [Z]

/-- The dimension of each full-flag stratum is bounded by its labeled configurations. -/
theorem fullFlagStratum_finrank_le (B k j : ℕ) (Y : Finset (Fin B)) (hk : 2 * k ≤ B) :
    Module.finrank ℂ (FullFlagStratumRing B (B - k) j Y) ≤
      Nat.card (FullFlagStratumConfiguration B k j Y) := by
  classical
  induction B generalizing k j with
  | zero =>
      have hY : Y = Finset.univ := by ext i; exact Fin.elim0 i
      subst Y
      exact fullFlagStratumRankBound_univ 0 k j hk
  | succ B ih =>
      by_cases hY : Y = Finset.univ
      · subst Y
        exact fullFlagStratumRankBound_univ (B + 1) k j hk
      obtain ⟨e, Z, he⟩ := selectedPositions_delete_first B Y hY
      rw [← fullFlagStratum_finrank_relabel (B + 1) (B + 1 - k) j Y e,
        Nat.card_congr (fullFlagStratumConfiguration_relabel (B + 1) k j Y e), he,
        fullFlagStratumConfiguration_card_recursion B k j Z hk]
      let N := B + 1 - k
      have hN : 0 < N := by dsimp [N]; omega
      have hlen : B + 1 = N + k := by dsimp [N]; omega
      have hkN : k ≤ N := by dsimp [N]; omega
      have h := fullFlagStratum_finrank_recursion B N k j Z hN hlen hkN
      apply h.trans
      apply Nat.add_le_add
      · by_cases hk0 : k = 0
        · simp only [hk0, zero_mul, le_refl]
        · have hn : N = B - (k - 1) := by dsimp [N]; omega
          rw [hn]
          exact Nat.mul_le_mul_left k (ih (k - 1) j Z (by omega))
      · by_cases hvalid : 2 * k ≤ B
        · have hn : N - 1 = B - k := by dsimp [N]; omega
          rw [hn]
          exact Nat.mul_le_mul_left (N - k) (ih k j Z hvalid)
        · have hn : N - k = 0 := by dsimp [N]; omega
          change (N - k) * _ ≤ (N - k) * _
          rw [hn, zero_mul, zero_mul]

/-- The stratum-refined full-flag bound holds for every admissible number of paired sites. -/
theorem fullFlagStratumRankBound : FullFlagStratumRankBound :=
  fullFlagStratum_finrank_le

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumRankBound_univ
#print axioms VOA.DeligneAudit.SL4T.selectedPositions_delete_first
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finrank_le
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumRankBound
