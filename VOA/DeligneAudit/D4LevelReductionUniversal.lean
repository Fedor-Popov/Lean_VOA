import VOA.DeligneAudit.D4LevelReductionRank
import VOA.DeligneAudit.SL4TMixedLabelUniversal

/-! The actual universal truncated D4 module is bounded by the Levi-level coinvariants. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

noncomputable section

abbrev DemazureModule (m : ℕ) := UModG D4sector.f (ravFam D4sector m 0)

abbrev demazureCurrent (m : ℕ) := univRepG D4sector.f (ravFam D4sector m 0)

abbrev demazureGenerator (m : ℕ) := wUG D4sector.f (ravFam D4sector m 0)

abbrev TruncatedModule (m : ℕ) := UModG D4sector.f (lwSpec D4sector m)

/-- The universal truncated generator satisfies the parent Demazure presentation. -/
theorem truncatedGenerator_demazure_sat (m : ℕ) (hm : 1 ≤ m) :
    Sat D4sector.f (univRepG D4sector.f (lwSpec D4sector m))
      (wUG D4sector.f (lwSpec D4sector m)) (ravFam D4sector m 0) := by
  have hw := (localWeylRelG_iff D4sector _ _ m).mpr
    (univG_sat D4sector.f (lwSpec D4sector m))
  exact ((localWeylRelG_iff_demazure_trunc hm).mp hw).1

/-- The canonical map from the level-one module to the target truncated module. -/
def demazureToTruncated (m : ℕ) (hm : 1 ≤ m) :
    DemazureModule m →ₗ[ℂ] TruncatedModule m :=
  univMapG (truncatedGenerator_demazure_sat m hm)

theorem demazureToTruncated_surjective (m : ℕ) (hm : 1 ≤ m) :
    Function.Surjective (demazureToTruncated m hm) := by
  apply LinearMap.range_eq_top.mp
  rw [demazureToTruncated, SL4T.presentedCurrent_map_range, SL4T.presentedCurrent_cyclic]

/-- High full-current images vanish under the canonical truncation map. -/
theorem fullCurrentTail_le_truncation_kernel (m : ℕ) (hm : 1 ≤ m) :
    fullCurrentTail (demazureCurrent m) (demazureGenerator m) m ≤
      LinearMap.ker (demazureToTruncated m hm) := by
  let ρ := demazureCurrent m
  let w := demazureGenerator m
  let f := demazureToTruncated m hm
  have hw := (localWeylRelG_iff D4sector _ _ m).mpr
    (univG_sat D4sector.f (lwSpec D4sector m))
  rw [fullCurrentTail, currentTail, Submodule.span_le]
  rintro z ⟨c, _, r, hr, v, hv, rfl⟩
  change f (ρ.op c r v) = 0
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      change univMapG (truncatedGenerator_demazure_sat m hm)
        (wordOp ρ ((c, r) :: l) w) = 0
      rw [univMapG_wordOp]
      exact D4FusionContact.localWeyl_high_kills_word hm hw l c r hr
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul a x _ hx => simp [map_smul, hx]

/-- The cut-down gives a surjection from the Levi coinvariants onto the target module. -/
theorem truncatedModule_rank_le_leviCoinvariants (m : ℕ) (hm : 1 ≤ m) :
    FiniteDimensional ℂ (TruncatedModule m) ∧
      Module.finrank ℂ (TruncatedModule m) ≤
        Module.finrank ℂ (DemazureModule m ⧸
          leviCurrentTail (demazureCurrent m) (demazureGenerator m) m) := by
  haveI : FiniteDimensional ℂ (DemazureModule m) := (d4_demazureUnivRank m hm).1
  let G := leviCurrentTail (demazureCurrent m) (demazureGenerator m) m
  have hker : G ≤ LinearMap.ker (demazureToTruncated m hm) := by
    dsimp only [G, demazureCurrent, demazureGenerator]
    rw [← fullCurrentTail_eq_leviCurrentTail _ _ m m hm le_rfl
      (univG_sat D4sector.f (ravFam D4sector m 0))]
    exact fullCurrentTail_le_truncation_kernel m hm
  let f := G.liftQ (demazureToTruncated m hm) hker
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨u, rfl⟩ := demazureToTruncated_surjective m hm v
    exact ⟨G.mkQ u, rfl⟩
  exact ⟨Module.Finite.of_surjective f hf, LinearMap.finrank_le_finrank_of_surjective hf⟩

/-- The level coinvariant of the universal parent module. -/
abbrev UniversalLevelPiece (m : ℕ) (κ p : ℤ) :=
  TruncatedLevelPiece (demazureCurrent m) (demazureGenerator m) m κ p

/-- For all positive multiplicities, the target rank is bounded by the level coinvariants. -/
theorem truncatedModule_rank_le_levelSum (m : ℕ) (hm : 1 ≤ m) :
    FiniteDimensional ℂ (TruncatedModule m) ∧
      Module.finrank ℂ (TruncatedModule m) ≤
        ∑ i ∈ levelIndices m, Module.finrank ℂ (UniversalLevelPiece m i.1 i.2) := by
  haveI : FiniteDimensional ℂ (DemazureModule m) := (d4_demazureUnivRank m hm).1
  have hbase := truncatedModule_rank_le_leviCoinvariants m hm
  have hlevels := levelTruncation_finrank_le (demazureCurrent m) (demazureGenerator m) m
    (univG_sat D4sector.f (ravFam D4sector m 0))
  rw [ksKey_quot_finrank_eq_image, d4_univ_cyclic, Submodule.map_top,
    Submodule.range_mkQ, finrank_top] at hlevels
  exact ⟨hbase.1, hbase.2.trans hlevels⟩

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGenerator_demazure_sat
#print axioms VOA.DeligneAudit.D4LevelReduction.demazureToTruncated_surjective
#print axioms VOA.DeligneAudit.D4LevelReduction.fullCurrentTail_le_truncation_kernel
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedModule_rank_le_leviCoinvariants
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedModule_rank_le_levelSum
