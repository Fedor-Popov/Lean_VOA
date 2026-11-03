import VOA.DeligneAudit.SL4TStratumRankRecursion

/-! # Relabeling and boundary cases of the full-flag strata -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Imposing a stratum never increases the dimension of the full flag. -/
theorem fullFlagStratum_finrank_le_fullFlag (B N j : ℕ) (Y : Finset (Fin B)) :
    Module.finrank ℂ (FullFlagStratumRing B N j Y) ≤
      Module.finrank ℂ (FullFlagRing B N) := by
  letI := fullFlag_finite B N
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := (Ideal.Quotient.factorₐ ℂ
      (show fullFlagTruncationIdeal B N ≤
        fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j from
          le_sup_left)).toLinearMap)
    (Ideal.Quotient.factor_surjective le_sup_left)

/-- A unit top minor makes the stratum quotient zero. -/
theorem fullFlagStratum_finrank_zero_of_cutoff (B N j : ℕ) (Y : Finset (Fin B))
    (h : N + j ≤ Y.card) : Module.finrank ℂ (FullFlagStratumRing B N j Y) = 0 := by
  have hlen : (fullFlagSubalphabet Y).length = Y.card := by
    simp only [fullFlagSubalphabet, List.length_map, Finset.length_toList]
  have ht := remainderTopIdeal_eq_top (fullFlagSubalphabet Y) N j
    (by omega) (by omega)
  change Module.finrank ℂ (MvPolynomial (Fin B) ℂ ⧸
    (fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j)) = 0
  rw [ht, sup_top_eq]
  exact Module.finrank_zero_of_subsingleton

/-- One direction of invariance of stratum dimension under relabeling the positions. -/
theorem fullFlagStratum_finrank_relabel_le (B N j : ℕ) (Y : Finset (Fin B))
    (e : Equiv.Perm (Fin B)) :
    Module.finrank ℂ (FullFlagStratumRing B N j (Y.map e.toEmbedding)) ≤
      Module.finrank ℂ (FullFlagStratumRing B N j Y) := by
  let Z := Y.map e.toEmbedding
  let z := fullFlagStratumRoot B N j Z
  let x : Fin B → FullFlagStratumRing B N j Z := z ∘ e
  apply fullFlagStratum_rank_le_of_relations B N j Y x
  · rw [alphabetElementary_perm (e.ofFn_comp_perm z)]
    exact fullFlagStratum_elementary _ _ _ _
  · intro a
    exact fullFlagStratumRoot_pow _ _ _ _ (e a)
  · intro cols
    exact (remainderTopMinor_perm (selectedAlphabet_map_perm Y e.toEmbedding z)
      N j cols).symm.trans (fullFlagStratum_minor_zero _ _ _ _ cols)
  · intro a
    obtain ⟨p, hp⟩ := Ideal.Quotient.mkₐ_surjective ℂ
      (fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Z) N j) a
    refine ⟨MvPolynomial.rename e.symm p, ?_⟩
    rw [MvPolynomial.aeval_rename]
    have hx : x ∘ e.symm = z := by ext b; simp [x]
    rw [hx, fullFlagStratum_aeval]
    exact hp

/-- The stratum dimension depends only on the selected positions up to permutation. -/
theorem fullFlagStratum_finrank_relabel (B N j : ℕ) (Y : Finset (Fin B))
    (e : Equiv.Perm (Fin B)) :
    Module.finrank ℂ (FullFlagStratumRing B N j (Y.map e.toEmbedding)) =
      Module.finrank ℂ (FullFlagStratumRing B N j Y) := by
  apply le_antisymm (fullFlagStratum_finrank_relabel_le B N j Y e)
  have h := fullFlagStratum_finrank_relabel_le B N j (Y.map e.toEmbedding) e.symm
  have hY : (Y.map e.toEmbedding).map e.symm.toEmbedding = Y := by
    ext a
    simp
  rwa [hY] at h

/-- The refined recursion can peel a root in any chosen ordering of the positions. -/
theorem fullFlagStratum_finrank_recursion_relabel (B N k j : ℕ)
    (Y : Finset (Fin B)) (e : Equiv.Perm (Fin (B + 1)))
    (hN : 0 < N) (hlen : B + 1 = N + k) (hk : k ≤ N) :
    Module.finrank ℂ
        (FullFlagStratumRing (B + 1) N j ((Y.map (Fin.succEmb B)).map e.toEmbedding)) ≤
      k * Module.finrank ℂ (FullFlagStratumRing B N j Y) +
        (N - k) * Module.finrank ℂ (FullFlagStratumRing B (N - 1) j Y) := by
  rw [fullFlagStratum_finrank_relabel]
  exact fullFlagStratum_finrank_recursion B N k j Y hN hlen hk

/-- The full alphabet contains every doubled site. -/
theorem fullFlagDoublesIn_univ (B k : ℕ) (hk : 2 * k ≤ B)
    (f : FullFlagConfiguration B k) : fullFlagDoublesIn Finset.univ f = k := by
  classical
  simp only [fullFlagDoublesIn, Finset.mem_univ, implies_true, and_true,
    Fin.card_filter_val_lt]
  exact min_eq_right (by omega)

/-- Below the number of doubled sites the full-alphabet stratum has no configurations. -/
theorem fullFlagStratumConfiguration_univ_card_zero (B k j : ℕ)
    (hk : 2 * k ≤ B) (hj : j ≤ k) :
    Nat.card (FullFlagStratumConfiguration B k j Finset.univ) = 0 := by
  have hempty : IsEmpty (FullFlagStratumConfiguration B k j Finset.univ) :=
    ⟨fun f => by
      have h := f.property
      rw [fullFlagDoublesIn_univ B k hk] at h
      omega⟩
  letI := hempty
  simp

/-- Above the number of doubled sites the full-alphabet condition excludes no configuration. -/
def fullFlagStratumConfiguration_univ_equiv (B k j : ℕ)
    (hk : 2 * k ≤ B) (hj : k < j) :
    FullFlagStratumConfiguration B k j Finset.univ ≃ FullFlagConfiguration B k :=
  Equiv.subtypeUnivEquiv (fun f => by rwa [fullFlagDoublesIn_univ B k hk])

/-- The zero full-alphabet strata satisfy the requested dimension bound. -/
theorem fullFlagStratumRankBound_univ_of_le (B k j : ℕ)
    (hk : 2 * k ≤ B) (hj : j ≤ k) :
    Module.finrank ℂ (FullFlagStratumRing B (B - k) j Finset.univ) ≤
      Nat.card (FullFlagStratumConfiguration B k j Finset.univ) := by
  rw [fullFlagStratum_finrank_zero_of_cutoff B (B - k) j Finset.univ (by simp; omega)]
  exact Nat.zero_le _

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finrank_le_fullFlag
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finrank_zero_of_cutoff
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finrank_relabel_le
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finrank_relabel
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finrank_recursion_relabel
#print axioms VOA.DeligneAudit.SL4T.fullFlagDoublesIn_univ
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumConfiguration_univ_card_zero
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumConfiguration_univ_equiv
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumRankBound_univ_of_le
