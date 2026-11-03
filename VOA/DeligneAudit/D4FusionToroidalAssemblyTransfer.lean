import VOA.DeligneAudit.D4FusionToroidalAssemblyZero

/-! The first high-mode quotient surjects onto the local-Weyl universal module. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

private def localSat (m : ℕ) (hm : 1 ≤ m) :
    Sat D4sector.f (univRepG D4sector.f (lwSpec D4sector m))
      (wUG D4sector.f (lwSpec D4sector m)) (ravFam D4sector m 0) :=
  ((localWeylRelG_iff_demazure_trunc
    (ρ := univRepG D4sector.f (lwSpec D4sector m))
    (w := wUG D4sector.f (lwSpec D4sector m)) hm).mp
    (univ_localWeylRelG D4sector m)).1

private def localMap (m : ℕ) (hm : 1 ≤ m) :
    UModG D4sector.f (ravFam D4sector m 0) →ₗ[ℂ]
      UModG D4sector.f (lwSpec D4sector m) :=
  univMapG (localSat m hm)

theorem localMap_surjective (m : ℕ) (hm : 1 ≤ m) :
    Function.Surjective (localMap m hm) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← D4FusionContact.Polynomial.universal_word_span D4sector.f
      (lwSpec D4sector m),
    Submodule.span_le]
  rintro x ⟨l, rfl⟩
  exact ⟨wordOp (univRepG D4sector.f (ravFam D4sector m 0)) l
    (wUG D4sector.f (ravFam D4sector m 0)),
    univMapG_wordOp (localSat m hm) l⟩

theorem localMap_kills_TU (m : ℕ) (hm : 1 ≤ m) :
    FusionToroidal.TU D4sector.f (ravFam D4sector m 0) m 1 ≤
      LinearMap.ker (localMap m hm) := by
  rw [FusionToroidal.TU, FusionToroidal.Tfree, Submodule.map_span,
    Submodule.span_le]
  rintro x ⟨v, ⟨l, hl, rfl⟩, rfl⟩
  change localMap m hm ((Jrel D4sector.f (ravFam D4sector m 0)).mkQ (sw l)) = 0
  have hne : l.filter (fun x => m ≤ x.2) ≠ [] := by
    intro he
    simp [FusionToroidal.tmWeight, he] at hl
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
  simp only [List.mem_filter] at hx
  have hz := wordOp_eq_zero_of_mem _ (D4FusionContact.contact_truncIdeal m)
    (D4FusionContact.localWeyl_high_kills hm
      (univ_localWeylRelG D4sector m)) l ⟨x, hx.1, of_decide_eq_true hx.2⟩
  have hw := univMapG_wordOp (localSat m hm) l
  rw [wordOp_univG] at hw
  exact hw.trans hz

/-- The universal map factors through the first high-mode quotient. -/
def truncToLocal (m : ℕ) (hm : 1 ≤ m) :
    FusionToroidal.truncMod D4sector.f (ravFam D4sector m 0) m →ₗ[ℂ]
      UModG D4sector.f (lwSpec D4sector m) :=
  (FusionToroidal.TU D4sector.f (ravFam D4sector m 0) m 1).liftQ
    (localMap m hm) (localMap_kills_TU m hm)

theorem truncToLocal_surjective (m : ℕ) (hm : 1 ≤ m) :
    Function.Surjective (truncToLocal m hm) := by
  intro y
  obtain ⟨x, rfl⟩ := localMap_surjective m hm y
  exact ⟨_, Submodule.liftQ_apply _ _ _⟩

theorem local_rank_le_trunc (m : ℕ) (hm : 1 ≤ m)
    [FiniteDimensional ℂ
      (FusionToroidal.truncMod D4sector.f (ravFam D4sector m 0) m)] :
    FiniteDimensional ℂ (UModG D4sector.f (lwSpec D4sector m)) ∧
      Module.finrank ℂ (UModG D4sector.f (lwSpec D4sector m)) ≤
        Module.finrank ℂ
          (FusionToroidal.truncMod D4sector.f (ravFam D4sector m 0) m) := by
  have hs := truncToLocal_surjective m hm
  exact ⟨Module.Finite.of_surjective _ hs,
    LinearMap.finrank_le_finrank_of_surjective hs⟩

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.localMap_kills_TU
#print axioms VOA.DeligneAudit.Toroidal.truncToLocal_surjective
#print axioms VOA.DeligneAudit.Toroidal.local_rank_le_trunc
