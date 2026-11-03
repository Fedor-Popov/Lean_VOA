import VOA.DeligneAudit.SL4TDoubledSiteOrbit
import VOA.DeligneAudit.SL4TMixedLabelRank

/-! Reduction of the universal doubled-site rank bound to the quotient spanning filtrations. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector VOA.DeligneAudit.UnivG

variable {V : Type} [AddCommGroup V] [Module ℂ V]

set_option synthInstance.maxHeartbeats 100000 in
-- The count filtration uses two quotient stages over the Grassmannian coefficient algebra.
/-- Arbitrary bounds on the supported last-root orbits sum along the second Levi filtration. -/
theorem secondLeviFiltration_rank_le_of_orbit_bounds [FiniteDimensional ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V) (a b : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b a)) (d : Fin 3 → ℕ)
    (hd : d 0 ≤ a ∧ d 1 ≤ b ∧ d 2 ≤ a) (cost : MixedParams → ℕ)
    (hbound : ∀ e₁ e₂, MixedValid (mixedLabelBlockParams a b d e₁ e₂) →
      Module.finrank ℂ (secondLeviOrbit (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b a h d) e₁ e₂) ≤
          cost (mixedLabelBlockParams a b d e₁ e₂)) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w a b a h d
    Module.finrank ℂ ↥(⨆ e : ℕ × ℕ,
      a2LeviClosure Q (secondLeviCountLayer Q β e.1 e.2)) ≤
        ∑ e ∈ mixedSecondSupportedCounts a b d, cost (mixedLabelBlockParams a b d e.1 e.2) := by
  classical
  let Q := radicalCountQuotCurrent ρ w d
  let β := radicalGrassmannianAmbientEvaluation ρ w a b a h d
  let p := (a3KeyLabelInt b a 0 ⟨d 0, d 1, d 2, 0⟩).toNat
  let q := (a3KeyLabelInt b a 1 ⟨d 0, d 1, d 2, 0⟩).toNat
  let S := fun e : ℕ × ℕ => a2LeviClosure Q (secondLeviCountLayer Q β e.1 e.2)
  let N := fun e : ℕ × ℕ => higherSecondLeviCountClosure Q β e.1 e.2
  let t := (Finset.range (p + 1)) ×ˢ (Finset.range (q + 1))
  let c := fun e : ℕ × ℕ => if e ∈ t then cost (mixedLabelBlockParams a b d e.1 e.2) else 0
  have hm : ∀ j, 0 ≤ a3KeyLabelInt b a j ⟨d 0, d 1, d 2, 0⟩ := by
    intro j
    fin_cases j <;> simp [a3KeyLabelInt] <;> omega
  have hb := finiteFiberFiltration_finrank_le S N secondLeviCountFiber
    (fun e => -(e.1 : ℤ)) c t
    (fun i => Finset.mem_antidiagonal.mpr rfl)
    (fun i j hj => by
      have he := Finset.mem_antidiagonal.mp hj
      simp only [secondLeviCountFiber, he])
    (higherSecondLeviCountClosure_le_fiber Q β)
    (fun e => by
      by_cases he : e ∈ t
      · have he' := he
        simp only [t, Finset.mem_product, Finset.mem_range] at he'
        have hv := mixedLabelBlockParams_valid a b d hd e.1 e.2
          (by rw [← Int.toNat_of_nonneg (hm 0)]; exact_mod_cast (by omega : e.1 ≤ p))
          (by rw [← Int.toNat_of_nonneg (hm 1)]; exact_mod_cast (by omega : e.2 ≤ q))
        rw [show (S e).map (N e).mkQ = secondLeviOrbit Q β e.1 e.2 from
          secondLeviClosure_map_eq_orbit Q β e.1 e.2
            (radicalSecondLeviMultiplicity_otherCartan ρ w a b h d (hm 0) e.1 e.2)]
        simpa only [c, if_pos he] using hbound e.1 e.2 hv
      · have he' : p < e.1 ∨ q < e.2 := by
          simp only [t, Finset.mem_product, Finset.mem_range] at he
          omega
        rw [show (S e).map (N e).mkQ = ⊥ from
          radicalSecondLeviClosure_map_zero ρ w a b h d hm e.1 e.2 he']
        simp [c, he])
    (fun e he => by simp [c, he])
  simpa only [c, Finset.sum_ite_mem, Finset.inter_self] using hb

/-- The nested Levi indices inject into the valid blocks of the doubled-site catalog. -/
theorem doubledSiteNestedBlockBound_sum_le (B : ℕ) (hB : 2 ≤ B) :
    (∑ d ∈ radicalSupportedCounts 0 B 0,
      ∑ e ∈ mixedSecondSupportedCounts 0 B d,
        doubledSiteBlockBound B (mixedLabelBlockParams 0 B d e.1 e.2)) ≤
          20 * 6 ^ (B - 2) := by
  classical
  rw [← doubledSiteBlockBound_sum_all_valid B hB]
  let t := (radicalSupportedCounts 0 B 0).sigma (mixedSecondSupportedCounts 0 B)
  have hs : (∑ x ∈ t, doubledSiteBlockBound B (mixedCountIndexParams 0 B x)) =
      ∑ q ∈ t.image (mixedCountIndexParams 0 B), doubledSiteBlockBound B q := by
    rw [Finset.sum_image (mixedCountIndexParams_injective 0 B).injOn]
  have he : (∑ d ∈ radicalSupportedCounts 0 B 0,
      ∑ e ∈ mixedSecondSupportedCounts 0 B d,
        doubledSiteBlockBound B (mixedLabelBlockParams 0 B d e.1 e.2)) =
      ∑ x ∈ t, doubledSiteBlockBound B (mixedCountIndexParams 0 B x) := by
    rw [Finset.sum_sigma]
    rfl
  rw [he, hs]
  apply Finset.sum_le_sum_of_subset
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  exact mixedCountIndexParams_mem_valid 0 B x hx

set_option synthInstance.maxHeartbeats 100000 in
-- Both actual Levi filtrations use nested quotient coefficient algebras.
/-- Quotient spanning flags suffice for the doubled-site bound on every finite cyclic module. -/
theorem doubledSiteCyclic_rank_le_of_flags [FiniteDimensional ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V) (B : ℕ) (hB : 2 ≤ B)
    (h : LocalWeylRel ρ w (weightABC 0 B 0))
    (ht : ∀ i s v, B - 1 ≤ s → ρ.op i s v = 0)
    (hflags : ∀ q ∈ mixedValidBlocks 0 B, DoubledSiteSpanningFiltration B q) :
    Module.finrank ℂ (cycSubG ρ w) ≤ 20 * 6 ^ (B - 2) := by
  apply le_trans (radicalCountFiltration_rank_le ρ w 0 B 0 h
    (fun d => ∑ e ∈ mixedSecondSupportedCounts 0 B d,
      doubledSiteBlockBound B (mixedLabelBlockParams 0 B d e.1 e.2)) ?_)
    (doubledSiteNestedBlockBound_sum_le B hB)
  intro d hd
  rw [radicalCountClosure_map_eq_secondCounts ρ w 0 B 0 h d]
  apply secondLeviFiltration_rank_le_of_orbit_bounds ρ w 0 B h d
    ((mem_radicalSupportedCounts 0 B 0 d).mp hd) (doubledSiteBlockBound B)
  intro e₁ e₂ hv
  exact (doubledSiteSecondLeviOrbit_bound_of_chain ρ w B hB h ht d e₁ e₂ hv
    (hflags _ ((mem_mixedValidBlocks 0 B _).mpr ⟨hv, rfl, rfl⟩))).2

/-- The universal doubled-site rank bound is reduced to the pure ring spanning flags. -/
theorem truncatedWeyl_sl4_doubledSite_rank_le_of_flags (B : ℕ) (hB : 2 ≤ B)
    (hflags : ∀ q ∈ mixedValidBlocks 0 B, DoubledSiteSpanningFiltration B q) :
    FiniteDimensional ℂ (DoubledSiteModule B) ∧
      Module.finrank ℂ (DoubledSiteModule B) ≤ 20 * 6 ^ (B - 2) := by
  let R := truncatedWeylSpec (weightABC 0 B 0) (B - 1)
  let ρ := univRepG bracketTable R
  let w := wUG bracketTable R
  have hw := (truncatedWeylSpec_sat_iff ρ w _ _).mp (univG_sat bracketTable R)
  haveI : FiniteDimensional ℂ (DoubledSiteModule B) :=
    (truncatedLabelModule_finite_and_local_bound 0 B 0 (B - 1)).1
  have ht : ∀ i s v, B - 1 ≤ s → ρ.op i s v = 0 := by
    intro i s v hs
    exact truncatedLabelModule_current_zero 0 B 0 (B - 1) i s hs v
  have hb := doubledSiteCyclic_rank_le_of_flags ρ w B hB hw.1 ht hflags
  rw [presentedCurrent_cyclic, finrank_top] at hb
  exact ⟨inferInstance, hb⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviFiltration_rank_le_of_orbit_bounds
#print axioms VOA.DeligneAudit.SL4T.doubledSiteNestedBlockBound_sum_le
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCyclic_rank_le_of_flags
#print axioms VOA.DeligneAudit.SL4T.truncatedWeyl_sl4_doubledSite_rank_le_of_flags
