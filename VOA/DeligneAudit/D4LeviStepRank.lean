import VOA.DeligneAudit.D4LeviHigherPrefix
import VOA.DeligneAudit.LeviTypeA3StepQuotRank

/-! The quotient of each ordered prefix step has its key orbit bound. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

noncomputable def keyOrbitLength (m : ℕ) (k : RadicalKey) : ℕ :=
  if ∃ i : Fin 3, keyLabel m i k < 0 then 0
  else 4 ^ keyWeight m k 0 * 6 ^ keyWeight m k 1 *
    4 ^ keyWeight m k 2

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem keyPrefix_step_rank
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : ℕ) (hi : i < (globalKeyBox m).card) :
    let k := keyEnum m ⟨i, hi⟩
    let F := keyPrefix ρ w m i
    let S := keyLayer ρ w k
    let T := keyPrefix ρ w m (i + 1)
    FiniteDimensional ℂ (T ⧸ F.comap T.subtype) ∧
      Module.finrank ℂ (T ⧸ F.comap T.subtype) ≤
        keyOrbitLength m k * Module.finrank ℂ (S ⧸ F.comap S.subtype) := by
  let k := keyEnum m ⟨i, hi⟩
  let F := keyPrefix ρ w m i
  let S := keyLayer ρ w k
  let T := keyPrefix ρ w m (i + 1)
  let L := keyOrbitLength m k * Module.finrank ℂ (S ⧸ F.comap S.subtype)
  have hF : F = higherOrbit ρ w m k := keyPrefix_eq_higher ρ w m h i hi
  have horbit : FiniteDimensional ℂ ((keyOrbit ρ w k).map F.mkQ) ∧
      Module.finrank ℂ ((keyOrbit ρ w k).map F.mkQ) ≤ L := by
    dsimp only [L]
    rw [hF]
    by_cases hneg : ∃ j : Fin 3, keyLabel m j k < 0
    · rw [keyOrbit_map_bot_of_non_dominant ρ w m h k hneg]
      constructor
      · infer_instance
      · simp [keyOrbitLength, hneg]
    · have hdom : ∀ j : Fin 3, 0 ≤ keyLabel m j k := by
        intro j
        exact le_of_not_gt (fun hj => hneg ⟨j, hj⟩)
      simpa [S, keyOrbitLength, hneg] using
        key_orbit_rank ρ w m h k hdom
  have hT : T = F ⊔ ⨆ _ : Fin 1, keyOrbit ρ w k := by
    change keyPrefix ρ w m (i + 1) =
      keyPrefix ρ w m i ⊔ ⨆ _ : Fin 1, keyOrbit ρ w k
    rw [keyPrefix_step ρ w m i hi]
    rw [iSup_unique]
  have hh := VOA.DeligneAudit.A3Sector.a3_step_quot_rank_of_orbits
    F T 1 L (fun _ : Fin 1 => keyOrbit ρ w k) hT
    (fun _ => horbit.1) (fun _ => horbit.2)
  simpa [L, F, T, S, k] using hh

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyPrefix_step_rank
