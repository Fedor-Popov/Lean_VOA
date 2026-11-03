import VOA.DeligneAudit.D4LeviCountCutoff

/-! Source relations for the D4 key multiplicity argument. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The `E` letter kills every radical word, in every mode. -/
theorem radicalWord_zero_of_E
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (l : List (Fin 6 × ℕ))
    (he : 0 < l.countP (fun p => p.1 = 0)) :
    radicalWord ρ w l = 0 := by
  apply radicalWord_zero_of_count ρ w m h 0 l
  simpa [rootWeight] using he

/-- Every exact key containing an `E` has zero source layer. -/
theorem keyLayer_eq_bot_of_E
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (he : 0 < k.e) : keyLayer ρ w k = ⊥ := by
  rw [keyLayer, eq_bot_iff, Submodule.span_le]
  intro v hv
  obtain ⟨l, hk, rfl⟩ := hv
  have hcount : 0 < l.countP (fun p => p.1 = 0) := by
    simpa [← hk, wordKey] using he
  rw [radicalWord_zero_of_E ρ w m h l hcount]
  exact Submodule.zero_mem _

/-- The Garland current relation for each of the six radical roots. -/
theorem radical_garland_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (j : Fin 6) (k s : ℕ) (hk : 1 ≤ k)
    (hs : rootWeight m j + 1 ≤ k + s) :
    (PowerSeries.coeff s
      (VOA.DeligneAudit.Garland.Fs (rootF ρ j) ^ k)) w = 0 := by
  exact VOA.DeligneAudit.Garland.garland
    (rootEF_comm ρ j) (rootHF_comm ρ j)
    (rootF_comm ρ j) (rootE_source_zero ρ w m h j)
    (fun r => rootH_source_pos_zero ρ w m h j (r + 1) (by omega))
    k hk (rootF_source_nil ρ w m h j) s hs

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.radicalWord_zero_of_E
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_eq_bot_of_E
#print axioms VOA.DeligneAudit.D4Levi.radical_garland_zero
