import VOA.DeligneAudit.D4LevelReductionFiltration
import VOA.DeligneAudit.SL4TFiniteFiltrationRank

/-! Right exactness bounds for the D4 Levi-level coinvariants. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V W : Type} [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Relations killed by a linear map give an upper bound for its image dimension. -/
theorem linearImage_finrank_le_quotient [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] W) (S R : Submodule ℂ V) (hR : R ≤ LinearMap.ker f) :
    Module.finrank ℂ (S.map f) ≤ Module.finrank ℂ (S ⧸ R.comap S.subtype) := by
  have hker : R.comap S.subtype ≤ LinearMap.ker (f.comp S.subtype) := by
    intro v hv
    exact hR hv
  let g := (R.comap S.subtype).liftQ (f.comp S.subtype) hker
  have hrange : LinearMap.range g = S.map f := by
    dsimp [g]
    rw [Submodule.range_liftQ, LinearMap.range_comp, Submodule.range_subtype]
  rw [← hrange]
  exact g.finrank_range_le

/-- Passing to a larger ambient subspace enlarges the current image. -/
theorem currentTail_mono_subspace (ρ : CurrentModule D4sector.f V)
    (colours : Set (Fin 28)) (N : ℕ) {S T : Submodule ℂ V} (hST : S ≤ T) :
    currentTail ρ S colours N ≤ currentTail ρ T colours N := by
  apply Submodule.span_mono
  rintro z ⟨c, hc, r, hr, v, hv, rfl⟩
  exact ⟨c, hc, r, hr, v, hST hv, rfl⟩

/-- The image of a level in the global coinvariants is a quotient of its own coinvariants. -/
theorem truncatedLevel_image_rank_le [FiniteDimensional ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ p : ℤ) :
    let G := leviCurrentTail ρ w m
    let S := levelFiltration ρ w m κ p
    let H := levelFiltration ρ w m κ (p + 1)
    Module.finrank ℂ ((S.map G.mkQ).map (H.map G.mkQ).mkQ) ≤
      Module.finrank ℂ (TruncatedLevelPiece ρ w m κ p) := by
  dsimp only
  let G := leviCurrentTail ρ w m
  let S := levelFiltration ρ w m κ p
  let H := levelFiltration ρ w m κ (p + 1)
  let T := currentTail ρ S {c | IsLevi c} m
  let f := (H.map G.mkQ).mkQ.comp G.mkQ
  have hTG : T ≤ G := currentTail_mono_subspace ρ _ m
    (levelFiltration_le_cyclic ρ w m h κ p)
  have hker : H ⊔ T ≤ LinearMap.ker f := by
    apply sup_le
    · intro v hv
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨v, hv, rfl⟩
    · intro v hv
      change (H.map G.mkQ).mkQ (G.mkQ v) = 0
      have hz : G.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (hTG hv)
      rw [hz, map_zero]
  have hb := linearImage_finrank_le_quotient f S (H ⊔ T) hker
  rw [← Submodule.map_comp]
  exact hb

/-- Summing the level coinvariants bounds the cyclic module's Levi coinvariants. -/
theorem levelTruncation_finrank_le [FiniteDimensional ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    Module.finrank ℂ
      (cycSubG ρ w ⧸ (leviCurrentTail ρ w m).comap (cycSubG ρ w).subtype) ≤
      ∑ i ∈ levelIndices m, Module.finrank ℂ (TruncatedLevelPiece ρ w m i.1 i.2) := by
  classical
  let G := leviCurrentTail ρ w m
  let S := fun i : ℤ × ℤ => (levelFiltration ρ w m i.1 i.2).map G.mkQ
  let H := fun i : ℤ × ℤ => (levelFiltration ρ w m i.1 (i.2 + 1)).map G.mkQ
  have hH : ∀ i ∈ levelIndices m,
      H i ≤ ⨆ j ∈ levelIndices m, ⨆ (_ : -j.2 < -i.2), S j := by
    intro i _
    have hh := Submodule.map_mono (f := G.mkQ)
      (levelFiltration_next_le ρ w m i.1 i.2)
    simp only [Submodule.map_iSup] at hh
    apply hh.trans
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    apply iSup_le
    intro hp
    exact le_iSup_of_le j (le_iSup_of_le hj
      (le_iSup_of_le (by omega : -j.2 < -i.2) le_rfl))
  have hb := SL4T.finiteFiltration_finrank_le S H (fun i => -i.2)
    (fun i => Module.finrank ℂ (TruncatedLevelPiece ρ w m i.1 i.2))
    (levelIndices m) hH (fun i _ => truncatedLevel_image_rank_le ρ w m h i.1 i.2)
  have hspan : (⨆ i ∈ levelIndices m, S i) = (cycSubG ρ w).map G.mkQ := by
    dsimp [S]
    simp only [← Submodule.map_iSup, levelFiltration_spans ρ w m h]
  rw [hspan] at hb
  rw [ksKey_quot_finrank_eq_image]
  exact hb

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.linearImage_finrank_le_quotient
#print axioms VOA.DeligneAudit.D4LevelReduction.currentTail_mono_subspace
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedLevel_image_rank_le
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncation_finrank_le
