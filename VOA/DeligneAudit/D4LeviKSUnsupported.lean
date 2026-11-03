import VOA.DeligneAudit.D4LeviKSLemma0StepProof
import VOA.DeligneAudit.D4LeviKSBoxCountClass

/-! Unsupported D4 key layers with a non-XYZ radical letter vanish in the quotient. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- An exact XYZ word cannot have a key recording E, U, or U′. -/
theorem xyzSpan_eq_bot_of_excluded (k : RadicalKey)
    (he : k.e ≠ 0 ∨ k.u ≠ 0 ∨ k.up ≠ 0) :
    xyzSpan ρ w k = ⊥ := by
  apply le_antisymm ?_ bot_le
  rw [xyzSpan, Submodule.span_le]
  rintro v ⟨l, hk, hE, hU, hUp, rfl⟩
  have he0 : k.e = 0 := by simpa [← hk, wordKey] using hE
  have hu0 : k.u = 0 := by simpa [← hk, wordKey] using hU
  have hup0 : k.up = 0 := by simpa [← hk, wordKey] using hUp
  rcases he with h | h | h <;> contradiction

/-- Lemma 0 removes every key containing a non-XYZ radical letter. -/
theorem keyLayer_le_prefix_of_excluded
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : ℕ) (hi : i < (globalKeyBox m).card)
    (he : (keyEnum m ⟨i, hi⟩).e ≠ 0 ∨
      (keyEnum m ⟨i, hi⟩).u ≠ 0 ∨
        (keyEnum m ⟨i, hi⟩).up ≠ 0) :
    keyLayer ρ w (keyEnum m ⟨i, hi⟩) ≤ keyPrefix ρ w m i := by
  calc
    keyLayer ρ w (keyEnum m ⟨i, hi⟩) ≤
        xyzSpan ρ w (keyEnum m ⟨i, hi⟩) ⊔ keyPrefix ρ w m i :=
      keyLayer_le_xyzSpan_sup_prefix ρ w m h i hi
    _ = keyPrefix ρ w m i := by
      rw [xyzSpan_eq_bot_of_excluded ρ w _ he, bot_sup_eq]

/-- The excluded-key contribution to the raw rank sum is zero. -/
theorem keyQuot_finrank_zero_of_excluded
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : ℕ) (hi : i < (globalKeyBox m).card)
    (he : (keyEnum m ⟨i, hi⟩).e ≠ 0 ∨
      (keyEnum m ⟨i, hi⟩).u ≠ 0 ∨
        (keyEnum m ⟨i, hi⟩).up ≠ 0) :
    Module.finrank ℂ
      (keyLayer ρ w (keyEnum m ⟨i, hi⟩) ⧸
        (keyPrefix ρ w m i).comap
          (keyLayer ρ w (keyEnum m ⟨i, hi⟩)).subtype) = 0 := by
  have htop : (keyPrefix ρ w m i).comap
      (keyLayer ρ w (keyEnum m ⟨i, hi⟩)).subtype = ⊤ := by
    apply top_unique
    intro x hx
    exact keyLayer_le_prefix_of_excluded ρ w m h i hi he x.property
  rw [htop]
  haveI : Subsingleton
      (keyLayer ρ w (keyEnum m ⟨i, hi⟩) ⧸
        (⊤ : Submodule ℂ (keyLayer ρ w (keyEnum m ⟨i, hi⟩)))) :=
    (Submodule.Quotient.subsingleton_iff).mpr rfl
  exact Module.finrank_zero_iff.mpr inferInstance

/-- An XYZ key with more Y than X has a negative first Levi label. -/
theorem keyOrbitLength_zero_of_xyz_y_gt_x (k : RadicalKey)
    (hu : k.u = 0) (hup : k.up = 0) (hxy : k.x < k.y) :
    keyOrbitLength m k = 0 := by
  unfold keyOrbitLength
  rw [if_pos]
  refine ⟨0, ?_⟩
  simp [keyLabel, hu, hup]
  omega

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyzSpan_eq_bot_of_excluded
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_le_prefix_of_excluded
#print axioms VOA.DeligneAudit.D4Levi.keyQuot_finrank_zero_of_excluded
#print axioms VOA.DeligneAudit.D4Levi.keyOrbitLength_zero_of_xyz_y_gt_x
