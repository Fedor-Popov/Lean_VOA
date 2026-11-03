import VOA.DeligneAudit.SL4TMixedLabelModule

/-! Equivalence of the universal truncated rank assertion and its cyclic-module formulation. -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

noncomputable section

/-- The universal map has precisely the cyclic submodule as its image. -/
theorem presentedCurrent_map_range {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : CurrentModule f V} {w : V} {R : RelSpec n} (h : Sat f ρ w R) :
    LinearMap.range (univMapG h) = cycSubG ρ w := by
  rw [← Submodule.map_top, ← presentedCurrent_cyclic f R, cycSubG, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨x, ⟨l, rfl⟩, rfl⟩
    exact ⟨l, (univMapG_wordOp h l).symm⟩
  · rintro ⟨l, rfl⟩
    exact ⟨_, ⟨l, rfl⟩, univMapG_wordOp h l⟩

/-- Finite universal presentations bound every cyclic module satisfying their relations. -/
theorem presentedCurrent_cyclic_rank_le {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : CurrentModule f V} {w : V} {R : RelSpec n} (h : Sat f ρ w R)
    [FiniteDimensional ℂ (UModG f R)] :
    FiniteDimensional ℂ (cycSubG ρ w) ∧
      Module.finrank ℂ (cycSubG ρ w) ≤ Module.finrank ℂ (UModG f R) := by
  rw [← presentedCurrent_map_range h]
  exact ⟨inferInstance, (univMapG h).finrank_range_le⟩

/-- The precise bound on all cyclic current modules is equivalent to the universal target. -/
theorem mixedLabelTruncatedRank_iff_cyclic : MixedLabelTruncatedRank ↔
    ∀ (a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule A3Sector.bracketTable V) (w : V),
      A3Sector.LocalWeylRel ρ w (A3Sector.weightABC a b a) →
      (∀ x s, a + b ≤ s → ρ.op x s w = 0) →
      FiniteDimensional ℂ (cycSubG ρ w) ∧
        Module.finrank ℂ (cycSubG ρ w) ≤ 15 ^ a * 6 ^ b := by
  constructor
  · intro h a b V _ _ ρ w hw ht
    obtain ⟨hf, hr⟩ := h a b
    letI := hf
    have hs := (truncatedWeylSpec_sat_iff ρ w (A3Sector.weightABC a b a)
      (a + b)).mpr ⟨hw, ht⟩
    obtain ⟨hfc, hrc⟩ := presentedCurrent_cyclic_rank_le hs
    exact ⟨hfc, hrc.trans hr⟩
  · intro h a b
    let R := truncatedWeylSpec (A3Sector.weightABC a b a) (a + b)
    have hs := (truncatedWeylSpec_sat_iff _ _ _ _).mp
      (univG_sat A3Sector.bracketTable R)
    obtain ⟨_, hr⟩ := h a b _ (univRepG A3Sector.bracketTable R)
      (wUG A3Sector.bracketTable R) hs.1 hs.2
    rw [presentedCurrent_cyclic, finrank_top] at hr
    exact ⟨(mixedLabelModule_finite_and_local_bound a b).1, hr⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.presentedCurrent_map_range
#print axioms VOA.DeligneAudit.SL4T.presentedCurrent_cyclic_rank_le
#print axioms VOA.DeligneAudit.SL4T.mixedLabelTruncatedRank_iff_cyclic
