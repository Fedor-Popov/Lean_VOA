import VOA.DeligneAudit.D4LevelReductionAdjointFiltration

/-! The all-m adjoint boundary bound from the finite homogeneous multiplicity filtration. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Successive quotient images have the same dimension as imposing both relations together. -/
theorem quotientImage_twice_finrank (S H T : Submodule ℂ V) :
    Module.finrank ℂ ((S.map T.mkQ).map (H.map T.mkQ).mkQ) =
      Module.finrank ℂ (S.map (H ⊔ T).mkQ) := by
  have hfirst := SL4T.submodule_finrank_sup_eq (S.map T.mkQ) (H.map T.mkQ)
  have hsecond := SL4T.submodule_finrank_sup_eq (S ⊔ H) T
  have hthird := SL4T.submodule_finrank_sup_eq H T
  have hfourth := SL4T.submodule_finrank_sup_eq S (H ⊔ T)
  rw [← Submodule.map_sup] at hfirst
  rw [sup_assoc] at hsecond
  omega

variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The adjoint boundary coinvariants satisfy the binomial mixed-label estimate. -/
theorem adjointEdge_coinvariants_rank_le (a b : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b) 0)) :
    Module.finrank ℂ (TruncatedLevelPiece ρ w (a + b) b (2 * (a : ℤ) + b)) ≤
      (a + b).choose a * 15 ^ a * 6 ^ b := by
  classical
  let E := levelFiltration ρ w (a + b) b (2 * (a : ℤ) + b)
  let T := currentTail ρ E {c | IsLevi c} (a + b)
  let S := fun d => (keyOrbit ρ w (adjointLetterKey a d)).map T.mkQ
  let H := fun d => (adjointHigherDegree ρ w a d).map T.mkQ
  let degrees := Finset.range (2 * (a + b) * a + 1)
  have hedge : E = ⨆ d : ℕ, keyOrbit ρ w (adjointLetterKey a d) := by
    have he := adjointEdge_eq_iSup_keyOrbit ρ w (a + b) a h
    convert he using 1 <;> simp [E, Nat.cast_add] <;> ring
  have hfinite : E = ⨆ d ∈ degrees, keyOrbit ρ w (adjointLetterKey a d) := by
    rw [hedge]
    apply le_antisymm
    · apply iSup_le
      intro d
      by_cases hd : d ∈ degrees
      · exact le_iSup_of_le d (le_iSup_of_le hd le_rfl)
      · rw [adjointOrbit_eq_bot_of_degree_gt ρ w (a + b) a d h (by
          simpa only [degrees, Finset.mem_range, not_lt, Nat.add_one_le_iff] using hd)]
        exact bot_le
    · exact iSup_le fun d => iSup_le fun _ =>
        le_iSup (fun e : ℕ => keyOrbit ρ w (adjointLetterKey a e)) d
  have hT : ∀ c r, IsLevi c → T ≤ T.comap (ρ.op c r) :=
    currentTail_stable_of_leviInvariant ρ E (a + b)
      (levelFiltration_stable ρ w (a + b) b (2 * (a : ℤ) + b))
  have hH : ∀ d ∈ degrees,
      H d ≤ ⨆ e ∈ degrees, ⨆ (_ : -(e : ℤ) < -(d : ℤ)), S e := by
    intro d _
    have hh := Submodule.map_mono (f := T.mkQ)
      (adjointHigherDegree_le_finite ρ w (a + b) a d h)
    simp only [Submodule.map_iSup] at hh
    apply hh.trans
    apply iSup_le
    intro e
    apply iSup_le
    intro he
    apply iSup_le
    intro hde
    exact le_iSup_of_le e (le_iSup_of_le he
      (le_iSup_of_le (by omega : -(e : ℤ) < -(d : ℤ)) le_rfl))
  have hstep (d : ℕ) : Module.finrank ℂ ((S d).map (H d).mkQ) ≤
      (15 ^ a * 6 ^ b) * (adjointGradedBox (a + b) a d).card := by
    rw [quotientImage_twice_finrank]
    exact adjointOrbit_quotient_rank_le ρ w a b d h T hT le_rfl
  have htotal := SL4T.finiteFiltration_finrank_le S H (fun d => -(d : ℤ))
    (fun d => (15 ^ a * 6 ^ b) * (adjointGradedBox (a + b) a d).card)
    degrees hH (fun d _ => hstep d)
  have hspan : (⨆ d ∈ degrees, S d) = E.map T.mkQ := by
    simp only [S, ← Submodule.map_iSup, ← hfinite]
  rw [hspan, ← Finset.mul_sum] at htotal
  have hbound := htotal.trans (Nat.mul_le_mul_left _
    (adjointGradedBox_sum_le (a + b) a (by omega) degrees))
  have hnext : levelFiltration ρ w (a + b) b (2 * (a : ℤ) + b + 1) = ⊥ := by
    apply levelFiltration_eq_bot_above_adjoint_edge
    push_cast
    omega
  change Module.finrank ℂ
    (E ⧸ (levelFiltration ρ w (a + b) b (2 * (a : ℤ) + b + 1) ⊔ T).comap
      E.subtype) ≤ _
  rw [hnext, bot_sup_eq, ksKey_quot_finrank_eq_image]
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hbound

/-- Every level with zero central count satisfies the required truncation bound. -/
theorem levelTruncationBound_adjoint_edge (a b : ℕ) :
    LevelTruncationBound (a + b) b (2 * (a : ℤ) + b) := by
  have h := d4_all_weight_rank (demazureCurrent (a + b)) (demazureGenerator (a + b))
    (a + b) (univG_sat D4sector.f (ravFam D4sector (a + b) 0))
  rw [d4_univ_cyclic] at h
  haveI : FiniteDimensional ℂ (⊤ : Submodule ℂ (DemazureModule (a + b))) := h.1
  haveI : FiniteDimensional ℂ (DemazureModule (a + b)) :=
    FiniteDimensional.of_surjective (⊤ : Submodule ℂ (DemazureModule (a + b))).subtype
      (fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩)
  rw [levelTruncationBound_adjoint_edge_iff]
  exact adjointEdge_coinvariants_rank_le (demazureCurrent (a + b))
    (demazureGenerator (a + b)) a b (univG_sat D4sector.f (ravFam D4sector (a + b) 0))

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.quotientImage_twice_finrank
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointEdge_coinvariants_rank_le
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_adjoint_edge
