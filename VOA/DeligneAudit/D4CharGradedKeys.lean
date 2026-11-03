import VOA.DeligneAudit.D4CharGradedReduction

/-! Exact-degree key orbits and the finite graded PBW decomposition for L1. -/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl UnivG DeligneSector.D4 D4Levi

noncomputable section

local notation "deg" => SectorGraded.wordDeg

theorem graded_key_word_degree (l : List (Fin 28 × ℕ)) (r : List (Fin 6 × ℕ)) :
    deg (l ++ r.map fun p => (radicalColour p.1, p.2)) = deg l + (wordKey r).degree := by
  simp [SectorGraded.wordDeg, wordKey, List.map_map]
  rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem keyLayer_le_exact_degree (ρ : CurrentModule D4sector.f V) (w : V)
    (k : RadicalKey) : keyLayer ρ w k ≤ cycDeg ρ w k.degree := by
  apply Submodule.span_le.mpr
  rintro v ⟨r, hk, rfl⟩
  refine Submodule.subset_span ⟨r.map (fun p => (radicalColour p.1, p.2)), ?_, rfl⟩
  have hd := graded_key_word_degree [] r
  simpa only [List.nil_append, SectorGraded.wordDeg, List.map_nil, List.sum_nil,
    zero_add, hk] using hd

/-- The part of a key orbit with exact total degree N, including the radical seed degree. -/
def gradedKeyOrbit (ρ : CurrentModule D4sector.f V) (w : V) (k : RadicalKey)
    (N : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ l : List (Fin 28 × ℕ), ∃ r : List (Fin 6 × ℕ),
    l.Forall (fun p => IsLevi p.1) ∧ wordKey r = k ∧ deg l + k.degree = N ∧
      z = wordOp ρ (l ++ r.map fun p => (radicalColour p.1, p.2)) w}

theorem gradedKeyOrbit_le (ρ : CurrentModule D4sector.f V) (w : V)
    (k : RadicalKey) (N : ℕ) :
    gradedKeyOrbit ρ w k N ≤ cycDeg ρ w N ⊓ keyOrbit ρ w k := by
  apply Submodule.span_le.mpr
  rintro v ⟨l, r, hl, hk, hd, rfl⟩
  constructor
  · refine Submodule.subset_span ⟨l ++ r.map (fun p => (radicalColour p.1, p.2)), ?_, rfl⟩
    exact (graded_key_word_degree l r).trans (by simpa only [hk] using hd)
  · exact Submodule.subset_span ⟨l, r, hl, hk, rfl⟩

/-- Keys above the requested degree contribute no vectors, even before taking a quotient. -/
theorem gradedKeyOrbit_eq_bot_of_lt (ρ : CurrentModule D4sector.f V) (w : V)
    (k : RadicalKey) (N : ℕ) (hN : N < k.degree) : gradedKeyOrbit ρ w k N = ⊥ := by
  apply eq_bot_iff.mpr
  apply Submodule.span_le.mpr
  rintro v ⟨l, r, hl, hk, hd, hv⟩
  omega

/-- Degree projection of each old ungraded orbit is its explicit exact-degree span. -/
theorem projUG_keyOrbit (R : RelSpec 28) (k : RadicalKey) (N : ℕ) :
    (keyOrbit (univRepG D4sector.f R) (wUG D4sector.f R) k).map
      (projUG D4sector.f R N) =
        gradedKeyOrbit (univRepG D4sector.f R) (wUG D4sector.f R) k N := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro v ⟨l, r, hl, hk, rfl⟩
    change projUG D4sector.f R N
      (wordOp (univRepG D4sector.f R)
        (l ++ r.map fun p => (radicalColour p.1, p.2)) (wUG D4sector.f R)) ∈
      gradedKeyOrbit (univRepG D4sector.f R) (wUG D4sector.f R) k N
    rw [wordOp_univG, projUG_mk]
    split_ifs with hd
    · rw [← wordOp_univG]
      refine Submodule.subset_span ⟨l, r, hl, hk, ?_, rfl⟩
      have hh := (graded_key_word_degree l r).symm.trans hd
      simpa only [hk] using hh
    · exact Submodule.zero_mem _
  · intro v hv
    have hh := gradedKeyOrbit_le (univRepG D4sector.f R) (wUG D4sector.f R) k N hv
    exact ⟨v, hh.2, projUG_cyc D4sector.f R N hh.1⟩

/-- The exact-degree span equals intersection with the grading on the universal module. -/
theorem gradedKeyOrbit_eq_inf (R : RelSpec 28) (k : RadicalKey) (N : ℕ) :
    gradedKeyOrbit (univRepG D4sector.f R) (wUG D4sector.f R) k N =
      cycDeg (univRepG D4sector.f R) (wUG D4sector.f R) N ⊓
        keyOrbit (univRepG D4sector.f R) (wUG D4sector.f R) k := by
  apply le_antisymm (gradedKeyOrbit_le _ _ _ _)
  intro v hv
  rw [← projUG_keyOrbit]
  exact ⟨v, hv.2, projUG_cyc D4sector.f R N hv.1⟩

theorem projUG_cyclic (R : RelSpec 28) (N : ℕ) :
    (cycSubG (univRepG D4sector.f R) (wUG D4sector.f R)).map
      (projUG D4sector.f R N) = cycDeg (univRepG D4sector.f R) (wUG D4sector.f R) N := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro v ⟨l, rfl⟩
    change projUG D4sector.f R N
      (wordOp (univRepG D4sector.f R) l (wUG D4sector.f R)) ∈
      cycDeg (univRepG D4sector.f R) (wUG D4sector.f R) N
    rw [wordOp_univG, projUG_mk]
    split_ifs with hd
    · rw [← wordOp_univG]
      exact Submodule.subset_span ⟨l, hd, rfl⟩
    · exact Submodule.zero_mem _
  · intro v hv
    exact ⟨v, d4_cycDeg_le_cyclic _ _ _ hv, projUG_cyc D4sector.f R N hv⟩

/-- The finite key box from the total-rank bound also spans every exact degree. -/
theorem d4_universal_degree_eq_keys (n N : ℕ) :
    cycDeg (univRepG D4sector.f (ravFam D4sector n 0))
      (wUG D4sector.f (ravFam D4sector n 0)) N =
      ⨆ i : Fin (globalKeyBox n).card,
        gradedKeyOrbit (univRepG D4sector.f (ravFam D4sector n 0))
          (wUG D4sector.f (ravFam D4sector n 0)) (keyEnum n i) N := by
  have hh := congrArg (fun S => S.map (projUG D4sector.f (ravFam D4sector n 0) N))
    (keyPrefix_top (univRepG D4sector.f (ravFam D4sector n 0))
      (wUG D4sector.f (ravFam D4sector n 0)) n
      (univG_sat D4sector.f (ravFam D4sector n 0)))
  dsimp only at hh
  rw [projUG_cyclic] at hh
  simpa [keyPrefix, Submodule.map_iSup, projUG_keyOrbit] using hh.symm

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.graded_key_word_degree
#print axioms VOA.DeligneAudit.D4Char.keyLayer_le_exact_degree
#print axioms VOA.DeligneAudit.D4Char.gradedKeyOrbit_le
#print axioms VOA.DeligneAudit.D4Char.gradedKeyOrbit_eq_bot_of_lt
#print axioms VOA.DeligneAudit.D4Char.projUG_keyOrbit
#print axioms VOA.DeligneAudit.D4Char.gradedKeyOrbit_eq_inf
#print axioms VOA.DeligneAudit.D4Char.projUG_cyclic
#print axioms VOA.DeligneAudit.D4Char.d4_universal_degree_eq_keys
