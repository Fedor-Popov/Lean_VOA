import VOA.DeligneAudit.D4LeviKSConditionalFinal
import VOA.DeligneAudit.D4FusionTruncatedWeylRank

/-! The universal Demazure endpoint conditional only on the per-key box bound. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

theorem d4_univ_cyclic (m : ℕ) :
    cycSubG (univRepG D4sector.f (ravFam D4sector m 0))
      (wUG D4sector.f (ravFam D4sector m 0)) = ⊤ := by
  let R := ravFam D4sector m 0
  let F := D4sector.f
  have hall : ∀ y : FreeW D4sector.n,
      Submodule.Quotient.mk y ∈ cycSubG (univRepG F R) (wUG F R) := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y z hy hz =>
        exact (cycSubG (univRepG F R) (wUG F R)).add_mem hy hz
    | single l c =>
        have hsingle : Finsupp.single l c = c • UnivG.sw l := by
          simp [UnivG.sw]
        rw [hsingle, Submodule.Quotient.mk_smul]
        rw [← wordOp_univG F R l]
        exact (cycSubG (univRepG F R) (wUG F R)).smul_mem c
          (wordOp_mem_cycSubG (univRepG F R) (wUG F R) l)
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (Jrel F R) x
  exact hall y

/-- The remaining key-quotient estimate is sufficient for the actual
universal rank statement, uniformly in `m`. -/
theorem d4_demazureUnivRank_of_key_box_bounds
    (hkey : ∀ m, 1 ≤ m → ∀ i : Fin (globalKeyBox m).card,
      Module.finrank ℂ
        (keyLayer (univRepG D4sector.f (ravFam D4sector m 0))
            (wUG D4sector.f (ravFam D4sector m 0)) (keyEnum m i) ⧸
          (keyPrefix (univRepG D4sector.f (ravFam D4sector m 0))
              (wUG D4sector.f (ravFam D4sector m 0)) m i.val).comap
            (keyLayer (univRepG D4sector.f (ravFam D4sector m 0))
              (wUG D4sector.f (ravFam D4sector m 0)) (keyEnum m i)).subtype) ≤
        ksBoxCount m (keyEnum m i)) :
    DemazureUnivRank := by
  intro m hm
  let R := ravFam D4sector m 0
  let ρ := univRepG D4sector.f R
  let w := wUG D4sector.f R
  have h := d4_rank_of_key_box_bounds ρ w m
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

#print axioms VOA.DeligneAudit.D4Levi.d4_univ_cyclic
#print axioms VOA.DeligneAudit.D4Levi.d4_demazureUnivRank_of_key_box_bounds
