import VOA.DeligneAudit.D4LeviKSCorrectedCountSum
import VOA.DeligneAudit.D4LeviKSConditionalUniv

/-! Conditional rank assembly with the corrected rectangle count. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The key filtration and the multinomial count turn the per-key KS bound
into the rank bound for every saturated cyclic D4 module. -/
theorem d4_rank_of_corrected_key_box_bounds
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hkey : ∀ i : Fin (globalKeyBox m).card,
      Module.finrank ℂ
        (keyLayer ρ w (keyEnum m i) ⧸
          (keyPrefix ρ w m i.val).comap
            (keyLayer ρ w (keyEnum m i)).subtype) ≤
        ksCorrectedBoxCount m (keyEnum m i)) :
    FiniteDimensional ℂ (cycSubG ρ w) ∧
      Module.finrank ℂ (cycSubG ρ w) ≤ 29 ^ m := by
  obtain ⟨hfd, hrank⟩ := d4_all_weight_finite_and_raw_sum ρ w m h
  refine ⟨hfd, hrank.trans ?_⟩
  calc
    (∑ i : Fin (globalKeyBox m).card,
      keyOrbitLength m (keyEnum m i) *
        Module.finrank ℂ
          (keyLayer ρ w (keyEnum m i) ⧸
            (keyPrefix ρ w m i.val).comap
              (keyLayer ρ w (keyEnum m i)).subtype)) ≤
      ∑ i : Fin (globalKeyBox m).card,
        keyOrbitLength m (keyEnum m i) * ksCorrectedBoxCount m (keyEnum m i) := by
          exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hkey i)
    _ ≤ 29 ^ m := ksCorrectedBoxCount_enum_sum m

/-- The remaining key-quotient estimate is sufficient for the actual
universal rank statement, uniformly in `m`. -/
theorem d4_demazureUnivRank_of_corrected_key_box_bounds
    (hkey : ∀ m, 1 ≤ m → ∀ i : Fin (globalKeyBox m).card,
      Module.finrank ℂ
        (keyLayer (univRepG D4sector.f (ravFam D4sector m 0))
            (wUG D4sector.f (ravFam D4sector m 0)) (keyEnum m i) ⧸
          (keyPrefix (univRepG D4sector.f (ravFam D4sector m 0))
              (wUG D4sector.f (ravFam D4sector m 0)) m i.val).comap
            (keyLayer (univRepG D4sector.f (ravFam D4sector m 0))
              (wUG D4sector.f (ravFam D4sector m 0)) (keyEnum m i)).subtype) ≤
        ksCorrectedBoxCount m (keyEnum m i)) :
    DemazureUnivRank := by
  intro m hm
  let R := ravFam D4sector m 0
  let ρ := univRepG D4sector.f R
  let w := wUG D4sector.f R
  have h := d4_rank_of_corrected_key_box_bounds ρ w m
    (univG_sat D4sector.f R) (hkey m hm)
  have hc : cycSubG ρ w = ⊤ := d4_univ_cyclic m
  rw [hc] at h
  haveI : FiniteDimensional ℂ (⊤ : Submodule ℂ (UModG D4sector.f R)) := h.1
  haveI : FiniteDimensional ℂ (UModG D4sector.f R) :=
    FiniteDimensional.of_surjective
      (⊤ : Submodule ℂ (UModG D4sector.f R)).subtype
      (fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩)
  exact ⟨inferInstance, by simpa only [finrank_top] using h.2⟩

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.d4_rank_of_corrected_key_box_bounds
#print axioms VOA.DeligneAudit.D4Levi.d4_demazureUnivRank_of_corrected_key_box_bounds
