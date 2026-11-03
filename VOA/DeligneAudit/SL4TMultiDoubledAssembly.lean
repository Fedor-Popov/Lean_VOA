import VOA.DeligneAudit.SL4TMultiDoubledOrbit
import VOA.DeligneAudit.SL4TDoubledSiteRankReduction

/-! Levi assembly of the multi-doubled rank estimate from concrete coefficient flags. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector VOA.DeligneAudit.UnivG

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The nested Levi indices inject into the valid blocks of the multi-doubled word catalog. -/
theorem multiDoubledSiteNestedBlockBound_sum_le (B k : ℕ) (hk : 2 * k ≤ B) :
    (∑ d ∈ radicalSupportedCounts 0 B 0,
      ∑ e ∈ mixedSecondSupportedCounts 0 B d,
        multiDoubledSiteBlockBound B k (mixedLabelBlockParams 0 B d e.1 e.2)) ≤
          20 ^ k * 6 ^ (B - 2 * k) := by
  classical
  rw [← multiDoubledSiteBlockBound_sum_all_valid B k hk]
  let t := (radicalSupportedCounts 0 B 0).sigma (mixedSecondSupportedCounts 0 B)
  have hs : (∑ x ∈ t, multiDoubledSiteBlockBound B k (mixedCountIndexParams 0 B x)) =
      ∑ q ∈ t.image (mixedCountIndexParams 0 B), multiDoubledSiteBlockBound B k q := by
    rw [Finset.sum_image (mixedCountIndexParams_injective 0 B).injOn]
  have he : (∑ d ∈ radicalSupportedCounts 0 B 0,
      ∑ e ∈ mixedSecondSupportedCounts 0 B d,
        multiDoubledSiteBlockBound B k (mixedLabelBlockParams 0 B d e.1 e.2)) =
      ∑ x ∈ t, multiDoubledSiteBlockBound B k (mixedCountIndexParams 0 B x) := by
    rw [Finset.sum_sigma]
    rfl
  rw [he, hs]
  apply Finset.sum_le_sum_of_subset
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  exact mixedCountIndexParams_mem_valid 0 B x hx

set_option synthInstance.maxHeartbeats 100000 in
-- Both actual Levi filtrations use nested quotient coefficient algebras.
/-- Quotient subspace flags suffice for the multi-doubled bound on every finite cyclic module. -/
theorem multiDoubledSiteCyclic_rank_le_of_flags [FiniteDimensional ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V) (B k : ℕ) (hk : 2 * k ≤ B)
    (hN : 0 < B - k)
    (h : LocalWeylRel ρ w (weightABC 0 B 0))
    (ht : ∀ i s v, B - k ≤ s → ρ.op i s v = 0)
    (hflags : ∀ q ∈ mixedValidBlocks 0 B, MultiDoubledSiteCoefficientFlag B k q) :
    Module.finrank ℂ (cycSubG ρ w) ≤ 20 ^ k * 6 ^ (B - 2 * k) := by
  apply le_trans (radicalCountFiltration_rank_le ρ w 0 B 0 h
    (fun d => ∑ e ∈ mixedSecondSupportedCounts 0 B d,
      multiDoubledSiteBlockBound B k (mixedLabelBlockParams 0 B d e.1 e.2)) ?_)
    (multiDoubledSiteNestedBlockBound_sum_le B k hk)
  intro d hd
  rw [radicalCountClosure_map_eq_secondCounts ρ w 0 B 0 h d]
  apply secondLeviFiltration_rank_le_of_orbit_bounds ρ w 0 B h d
    ((mem_radicalSupportedCounts 0 B 0 d).mp hd) (multiDoubledSiteBlockBound B k)
  intro e₁ e₂ hv
  exact (multiDoubledSiteSecondLeviOrbit_bound_of_flag ρ w B k hN h ht d e₁ e₂ hv
    (hflags _ ((mem_mixedValidBlocks 0 B _).mpr ⟨hv, rfl, rfl⟩))).2

/-- The universal multi-doubled rank bound is reduced to the power-sum-stable coefficient flags. -/
theorem truncatedWeyl_sl4_multiDoubledSite_rank_le_of_flags (B k : ℕ) (hk : 2 * k ≤ B)
    (hflags : ∀ q ∈ mixedValidBlocks 0 B, MultiDoubledSiteCoefficientFlag B k q) :
    FiniteDimensional ℂ (TruncatedLabelModule 0 B 0 (B - k)) ∧
      Module.finrank ℂ (TruncatedLabelModule 0 B 0 (B - k)) ≤ 20 ^ k * 6 ^ (B - 2 * k) := by
  by_cases hk0 : k = 0
  · subst k
    simpa using truncatedLabelModule_finite_and_local_bound 0 B 0 B
  let R := truncatedWeylSpec (weightABC 0 B 0) (B - k)
  let ρ := univRepG bracketTable R
  let w := wUG bracketTable R
  have hw := (truncatedWeylSpec_sat_iff ρ w _ _).mp (univG_sat bracketTable R)
  haveI : FiniteDimensional ℂ (TruncatedLabelModule 0 B 0 (B - k)) :=
    (truncatedLabelModule_finite_and_local_bound 0 B 0 (B - k)).1
  have ht : ∀ i s v, B - k ≤ s → ρ.op i s v = 0 := by
    intro i s v hs
    exact truncatedLabelModule_current_zero 0 B 0 (B - k) i s hs v
  have hb := multiDoubledSiteCyclic_rank_le_of_flags ρ w B k hk (by omega) hw.1 ht hflags
  rw [presentedCurrent_cyclic, finrank_top] at hb
  exact ⟨inferInstance, hb⟩


end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteNestedBlockBound_sum_le
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCyclic_rank_le_of_flags
#print axioms VOA.DeligneAudit.SL4T.truncatedWeyl_sl4_multiDoubledSite_rank_le_of_flags
