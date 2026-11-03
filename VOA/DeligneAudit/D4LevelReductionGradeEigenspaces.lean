import VOA.DeligneAudit.D4LevelReductionGradeOperator

/-! The Demazure grade images are the intrinsic eigenspaces of the truncated module. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The vector-node layers span every saturated cyclic Demazure module. -/
theorem alphaLayer_spans (m : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    (⨆ κ : ℤ, alphaLayer ρ w m κ) = cycSubG ρ w := by
  apply le_antisymm
  · apply iSup_le
    intro κ
    rw [alphaLayer_eq_levelSup]
    exact iSup_le fun i => iSup_le fun _ => levelFiltration_le_cyclic ρ w m h i.1 i.2
  · rw [← levelFiltration_spans ρ w m h]
    exact iSup_le fun i => iSup_le fun _ =>
      (levelFiltration_le_alphaLayer ρ w m i.1 i.2).trans (le_iSup _ i.1)

/-- Universal maps carry each key orbit onto the corresponding target key orbit. -/
theorem demazure_keyOrbit_map (m : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) :
    (keyOrbit (demazureCurrent m) (demazureGenerator m) k).map (univMapG h) =
      keyOrbit ρ w k := by
  rw [keyOrbit, keyOrbit, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨u, ⟨l, r, hl, hk, rfl⟩, rfl⟩
    exact ⟨l, r, hl, hk, univMapG_wordOp h _⟩
  · rintro ⟨l, r, hl, hk, rfl⟩
    exact ⟨_, ⟨l, r, hl, hk, rfl⟩, univMapG_wordOp h _⟩

/-- The canonical quotient preserves the complete radical grade layers. -/
theorem truncatedGradeImage_eq_alphaLayer (m : ℕ) (hm : 1 ≤ m) (κ : ℤ) :
    truncatedGradeImage m hm κ =
      alphaLayer (univRepG D4sector.f (lwSpec D4sector m))
        (wUG D4sector.f (lwSpec D4sector m)) m κ := by
  unfold truncatedGradeImage alphaLayer
  simp only [Submodule.map_iSup]
  congr! 4
  exact demazure_keyOrbit_map _ _ m (truncatedGenerator_demazure_sat m hm) _

/-- The intrinsic vector-node grade eigenspace in the universal truncated module. -/
noncomputable def truncatedGradeSpace (m : ℕ) (κ : ℤ) :
    Submodule ℂ (TruncatedModule m) :=
  Module.End.eigenspace
    (doubledGradeCartan (univRepG D4sector.f (lwSpec D4sector m))) (2 * (κ : ℂ))

/-- Distinct integer grades give distinct coweight eigenvalues. -/
theorem doubledGrade_cast_injective : Function.Injective (fun κ : ℤ => 2 * (κ : ℂ)) := by
  intro a b hab
  have he : (a : ℂ) = (b : ℂ) := mul_left_cancel₀ (by norm_num) hab
  exact_mod_cast he

/-- The intrinsic grade eigenspaces form an independent family. -/
theorem truncatedGradeSpace_independent (m : ℕ) : iSupIndep (truncatedGradeSpace m) :=
  (Module.End.eigenspaces_iSupIndep _).comp doubledGrade_cast_injective

/-- The images of the Demazure grades span the truncated module. -/
theorem truncatedGradeImage_spans (m : ℕ) (hm : 1 ≤ m) :
    (⨆ κ : ℤ, truncatedGradeImage m hm κ) = ⊤ := by
  simp only [truncatedGradeImage, ← Submodule.map_iSup,
    alphaLayer_spans _ _ m (univG_sat D4sector.f (ravFam D4sector m 0)),
    d4_univ_cyclic, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (demazureToTruncated_surjective m hm)

/-- The Demazure grade image is exactly the intrinsic grade eigenspace. -/
theorem truncatedGradeImage_eq_eigenspace (m : ℕ) (hm : 1 ≤ m) (κ : ℤ) :
    truncatedGradeImage m hm κ = truncatedGradeSpace m κ := by
  have hle : truncatedGradeImage m hm ≤ truncatedGradeSpace m := by
    intro j
    rw [truncatedGradeImage_eq_alphaLayer]
    exact alphaLayer_le_gradeEigenspace _ _ m (truncatedGenerator_demazure_sat m hm) j
  exact congrFun ((truncatedGradeSpace_independent m).le_iff_eq_of_iSup_eq_top
    (truncatedGradeImage_spans m hm) |>.mp hle) κ

/-- The intrinsic coweight eigenspaces span the universal truncated module. -/
theorem truncatedGradeSpace_spans (m : ℕ) (hm : 1 ≤ m) :
    (⨆ κ : ℤ, truncatedGradeSpace m κ) = ⊤ := by
  simp only [← truncatedGradeImage_eq_eigenspace m hm]
  exact truncatedGradeImage_spans m hm

/-- The truncated module is the internal direct sum of its coweight eigenspaces. -/
theorem truncatedGradeSpace_isInternal (m : ℕ) (hm : 1 ≤ m) :
    DirectSum.IsInternal (truncatedGradeSpace m) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (truncatedGradeSpace_independent m) (truncatedGradeSpace_spans m hm)

/-- Each intrinsic grade satisfies the right-exact level rank estimate. -/
theorem truncatedGradeSpace_rank_le_levelSum (m : ℕ) (hm : 1 ≤ m) (κ : ℤ) :
    Module.finrank ℂ (truncatedGradeSpace m κ) ≤
      ∑ i ∈ gradeLevelIndices m κ, Module.finrank ℂ (UniversalLevelPiece m i.1 i.2) := by
  rw [← truncatedGradeImage_eq_eigenspace m hm]
  exact truncatedGradeImage_rank_le_levelSum m hm κ

/-- The existing radical count cutoff gives finite grade support before using symmetry. -/
theorem alphaLayer_eq_bot_of_grade_outside (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ : ℤ)
    (hκ : κ < -5 * (m : ℤ) ∨ (m : ℤ) < κ) : alphaLayer ρ w m κ = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro k
  apply iSup_le
  intro _
  apply iSup_le
  intro hk
  by_cases hz : keyLayer ρ w k = ⊥
  · rw [keyOrbit_eq_bot_of_keyLayer_bot ρ w k hz]
  have hd := keyDepth_le_of_nonzero ρ w m h k hz
  simp only [keyAlphaGrade] at hk
  omega

/-- A finite interval contains all intrinsic grades, without any reflection assumption. -/
theorem truncatedGradeSpace_eq_bot_of_grade_outside (m : ℕ) (hm : 1 ≤ m) (κ : ℤ)
    (hκ : κ < -5 * (m : ℤ) ∨ (m : ℤ) < κ) : truncatedGradeSpace m κ = ⊥ := by
  rw [← truncatedGradeImage_eq_eigenspace m hm, truncatedGradeImage_eq_alphaLayer]
  exact alphaLayer_eq_bot_of_grade_outside _ _ m
    (truncatedGenerator_demazure_sat m hm) κ hκ

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.alphaLayer_spans
#print axioms VOA.DeligneAudit.D4LevelReduction.demazure_keyOrbit_map
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_independent
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeImage_eq_eigenspace
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_spans
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_isInternal
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_rank_le_levelSum
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_eq_bot_of_grade_outside
