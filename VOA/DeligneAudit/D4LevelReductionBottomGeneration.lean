import VOA.DeligneAudit.D4LevelReductionThreeColourGeneration

/-! Bottom cyclic generation of every nonnegative Levi level, before truncation. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

/-- Every three-colour word has the positional shape prescribed by its three counts. -/
theorem threeColourWord_hasShape (l : List (Fin 6 × ℕ))
    (hl : ∀ t ∈ l, t.1 = 1 ∨ t.1 = 4 ∨ t.1 = 5) :
    HasWordShape (threeColourModeShape (wordKey l).x (wordKey l).y (wordKey l).z) l := by
  classical
  apply hasWordShape_of_colourPerm
  apply List.perm_iff_count.mpr
  intro i
  rw [ksWord_colour_count]
  have hz (k : Fin 6) (hk : k ≠ 1 ∧ k ≠ 4 ∧ k ≠ 5) :
      l.countP (fun t => t.1 = k) = 0 := by
    apply List.countP_eq_zero.mpr
    intro t ht
    rcases hl t ht with he | he | he <;> simp [he, Ne.symm hk.1, Ne.symm hk.2.1,
      Ne.symm hk.2.2]
  conv_rhs =>
    simp only [List.count, List.countP_map, ksCountP_sum, List.map_map, Function.comp_def,
      Finset.sum_map_toList]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  fin_cases i <;> simp [threeColourModeShape, wordKey, Fintype.card_fin]
  all_goals try simp only [← Nat.card_eq_fintype_card, Nat.card_fin]
  all_goals try rfl
  all_goals
    intro j r hj
    rcases hl (j, r) hj with he | he | he <;> simp_all

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Arbitrary modes and arbitrary middle counts are generated from the bottom zero-mode vector. -/
theorem threeColourWord_mem_bottomOrbit (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (l : List (Fin 6 × ℕ))
    (hl : ∀ t ∈ l, t.1 = 1 ∨ t.1 = 4 ∨ t.1 = 5) :
    radicalWord ρ w l ∈
      keyVectorOrbit ρ (bottomVector ρ w (wordKey l).x ((wordKey l).y + (wordKey l).z)) := by
  obtain ⟨d, hd⟩ := threeColourWord_hasShape l hl
  rw [radicalWord_perm ρ w hd]
  have hh := threeColour_evaluation_mem ρ w m h
    (wordKey l).x (wordKey l).y (wordKey l).z (∏ i, X i ^ d i)
  rwa [xyzEvaluation_prod_X_pow] at hh

/-- The bottom reductive orbit stays in its prescribed level filtration term. -/
theorem bottomOrbit_le_levelFiltration (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0)) :
    keyVectorOrbit ρ (bottomVector ρ w a c) ≤
      levelFiltration ρ w (a + b + c) b (2 * a + b) := by
  rw [keyVectorOrbit, Submodule.span_le]
  rintro v ⟨l, hl, rfl⟩
  induction l with
  | nil =>
      exact levelMultiplicitySpan_le_filtration ρ w (a + b + c) h b (2 * a + b)
        (bottomVector_mem_multiplicity ρ w a b c)
  | cons q l ih =>
      simp only [List.forall_cons] at hl
      exact levelFiltration_stable ρ w (a + b + c) b (2 * a + b) q.1 q.2 hl.1 (ih hl.2)

/-- Each level is the bottom cyclic orbit plus the next filtration term. -/
theorem levelFiltration_eq_bottomOrbit_sup_next (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0)) :
    levelFiltration ρ w (a + b + c) b (2 * a + b) =
      keyVectorOrbit ρ (bottomVector ρ w a c) ⊔
        levelFiltration ρ w (a + b + c) b (2 * a + b + 1) := by
  apply le_antisymm
  · apply levelFiltration_le_of_threeColour ρ w (a + b + c) h b (2 * a + b)
    · exact leviInvariant_sup ρ _ _
        (fun e r he v hv => keyVectorOrbit_inv ρ _ e r he hv)
        (levelFiltration_stable ρ w (a + b + c) b (2 * a + b + 1))
    · exact le_sup_right
    · intro l hl hg hp
      have hcounts : (wordKey l).e = 0 ∧ (wordKey l).u = 0 ∧ (wordKey l).up = 0 := by
        have hz (i : Fin 6) (hi : i ≠ 1 ∧ i ≠ 4 ∧ i ≠ 5) :
            l.countP (fun t => t.1 = i) = 0 := by
          apply List.countP_eq_zero.mpr
          intro t ht
          rcases hl t ht with he | he | he <;>
            simp [he, Ne.symm hi.1, Ne.symm hi.2.1, Ne.symm hi.2.2]
        exact ⟨hz 0 (by decide), hz 2 (by decide), hz 3 (by decide)⟩
      have hx : (wordKey l).x = a := by
        simp only [keyAlphaGrade, keyLeviLevel, keyDepth, Nat.cast_add,
          hcounts.1, hcounts.2.1, hcounts.2.2, Nat.cast_zero] at hg hp
        omega
      have hc : (wordKey l).y + (wordKey l).z = c := by
        simp only [keyAlphaGrade, keyDepth, Nat.cast_add, hcounts.1,
          hcounts.2.1, hcounts.2.2, hx, Nat.cast_zero] at hg
        omega
      have hv := threeColourWord_mem_bottomOrbit ρ w (a + b + c) h l hl
      rw [hx, hc] at hv
      exact Submodule.mem_sup_left hv
  · exact sup_le (bottomOrbit_le_levelFiltration ρ w a b c h)
      (levelFiltration_antitone ρ w (a + b + c) b (by omega))

/-- The same generation equality uses only the semisimple Levi current algebra. -/
theorem levelFiltration_eq_bottomCyclic_sup_next (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0)) :
    levelFiltration ρ w (a + b + c) b (2 * a + b) =
      cycSubG (leviCurrent ρ) (bottomVector ρ w a c) ⊔
        levelFiltration ρ w (a + b + c) b (2 * a + b + 1) := by
  rw [levelFiltration_eq_bottomOrbit_sup_next ρ w a b c h,
    bottomVector_reductiveOrbit_eq_cyclic ρ w (a + b + c) a c h]

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.threeColourWord_hasShape
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColourWord_mem_bottomOrbit
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomOrbit_le_levelFiltration
#print axioms VOA.DeligneAudit.D4LevelReduction.levelFiltration_eq_bottomOrbit_sup_next
#print axioms VOA.DeligneAudit.D4LevelReduction.levelFiltration_eq_bottomCyclic_sup_next
