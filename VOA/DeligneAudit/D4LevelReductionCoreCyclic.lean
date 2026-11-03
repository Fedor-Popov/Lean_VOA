import VOA.DeligneAudit.D4LevelReductionBottomGeneration

/-! Cyclicity of the universal level piece and the remaining converted-relation interface. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Restricting the semisimple action to a level commutes with every current word. -/
theorem levelLeviCurrent_word_coe (m : ℕ) (κ p : ℤ) (l : List (Fin 15 × ℕ))
    (v : levelFiltration ρ w m κ p) :
    (wordOp (levelLeviCurrent ρ w m κ p) l v).val =
      wordOp (leviCurrent ρ) l (v : V) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
      change (leviCurrent ρ).op q.1 q.2 (wordOp (levelLeviCurrent ρ w m κ p) l v).val = _
      rw [ih]
      rfl

/-- The bottom cyclic orbit maps into the cyclic orbit of its image in level coinvariants. -/
theorem bottomCyclic_image_mem (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0))
    {v : V} (hv : v ∈ cycSubG (leviCurrent ρ) (bottomVector ρ w a c)) :
    ∀ hf, levelCoinvariantMap ρ w (a + b + c) b (2 * a + b) ⟨v, hf⟩ ∈
      cycSubG (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b))
        (bottomCartanToLevel ρ w a b c h
          ⟨bottomVector ρ w a c, Submodule.subset_span ⟨[], rfl⟩⟩) := by
  let v₀ : levelFiltration ρ w (a + b + c) b (2 * a + b) :=
    bottomCartanLift ρ w a b c h
      ⟨bottomVector ρ w a c, Submodule.subset_span ⟨[], rfl⟩⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      intro hf
      have he : (⟨wordOp (leviCurrent ρ) l (bottomVector ρ w a c), hf⟩ :
          levelFiltration ρ w (a + b + c) b (2 * a + b)) =
          wordOp (levelLeviCurrent ρ w (a + b + c) b (2 * a + b)) l v₀ := by
        apply Subtype.ext
        exact (levelLeviCurrent_word_coe ρ w _ _ _ l v₀).symm
      rw [he, ← levelCoinvariantMap_word]
      exact wordOp_mem_cycSubG _ _ l
  | zero => intro hf; exact Submodule.zero_mem _
  | add x y hx hy hx' hy' =>
      intro hf
      have hle : cycSubG (leviCurrent ρ) (bottomVector ρ w a c) ≤
          levelFiltration ρ w (a + b + c) b (2 * a + b) := by
        rw [← bottomVector_reductiveOrbit_eq_cyclic ρ w (a + b + c) a c h]
        exact bottomOrbit_le_levelFiltration ρ w a b c h
      exact Submodule.add_mem _ (hx' (hle hx)) (hy' (hle hy))
  | smul z v hv hv' =>
      intro hf
      have hle : cycSubG (leviCurrent ρ) (bottomVector ρ w a c) ≤
          levelFiltration ρ w (a + b + c) b (2 * a + b) := by
        rw [← bottomVector_reductiveOrbit_eq_cyclic ρ w (a + b + c) a c h]
        exact bottomOrbit_le_levelFiltration ρ w a b c h
      exact Submodule.smul_mem _ z (hv' (hle hv))

/-- Every truncated level is cyclic on the zero-mode bottom vector. -/
theorem levelCoinvariant_bottom_cyclic (a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector (a + b + c) 0)) :
    cycSubG (levelCoinvariantCurrent ρ w (a + b + c) b (2 * a + b))
      (bottomCartanToLevel ρ w a b c h
        ⟨bottomVector ρ w a c, Submodule.subset_span ⟨[], rfl⟩⟩) = ⊤ := by
  apply top_unique
  intro v _
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
      have hv := (levelFiltration_eq_bottomCyclic_sup_next ρ w a b c h).le v.property
      obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.mp hv
      have hule : cycSubG (leviCurrent ρ) (bottomVector ρ w a c) ≤
          levelFiltration ρ w (a + b + c) b (2 * a + b) := by
        rw [← bottomVector_reductiveOrbit_eq_cyclic ρ w (a + b + c) a c h]
        exact bottomOrbit_le_levelFiltration ρ w a b c h
      have htf := levelFiltration_antitone ρ w (a + b + c) b
        (show (2 * a + b : ℤ) ≤ 2 * a + b + 1 by omega) ht
      have he : v = (⟨u, hule hu⟩ : levelFiltration ρ w (a + b + c) b (2 * a + b)) +
          ⟨t, htf⟩ := Subtype.ext hut.symm
      change levelCoinvariantMap ρ w (a + b + c) b (2 * a + b) v ∈ _
      rw [he, map_add]
      have hz : levelCoinvariantMap ρ w (a + b + c) b (2 * a + b) ⟨t, htf⟩ = 0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact Submodule.mem_sup_left ht
      rw [hz, add_zero]
      exact bottomCyclic_image_mem ρ w a b c h hu _

/-- The universal core piece is cyclic for all nonnegative bottom labels. -/
theorem universalCoreBottom_cyclic (a b c : ℕ) :
    cycSubG (universalCoreCurrent a b c) (universalCoreBottom a b c) = ⊤ :=
  levelCoinvariant_bottom_cyclic _ _ a b c
    (univG_sat D4sector.f (ravFam D4sector (a + b + c) 0))

/-- The nonempty raising window is the only missing part of the universal core presentation. -/
theorem universalCorePresentation_of_raisingWindow (a b c : ℕ)
    (hwindow : ∀ j, 1 ≤ j → j ≤ c →
      (coreRaisingIdeal a b c j).restrictScalars ℂ ≤
        LinearMap.ker (coreRaisingEvaluation (universalCoreCurrent a b c) a b c
          (universalCoreEvaluation a b c) j)) : UniversalCorePresentation a b c :=
  universalCorePresentation_of_raisingWindow_and_cyclic a b c hwindow
    (universalCoreBottom_cyclic a b c)

/-- Given the converted relations, the core rank estimate implies the corresponding level bound. -/
theorem levelTruncationBound_of_coreRank_raisingWindow (a b c : ℕ)
    (hbound : TruncatedCoreRankBound a b c)
    (hwindow : ∀ j, 1 ≤ j → j ≤ c →
      (coreRaisingIdeal a b c j).restrictScalars ℂ ≤
        LinearMap.ker (coreRaisingEvaluation (universalCoreCurrent a b c) a b c
          (universalCoreEvaluation a b c) j)) :
    LevelTruncationBound (a + b + c) b (2 * a + b) :=
  levelTruncationBound_of_corePresentation a b c hbound
    (universalCorePresentation_of_raisingWindow a b c hwindow)

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.levelLeviCurrent_word_coe
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCyclic_image_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.levelCoinvariant_bottom_cyclic
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreBottom_cyclic
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCorePresentation_of_raisingWindow
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_coreRank_raisingWindow
